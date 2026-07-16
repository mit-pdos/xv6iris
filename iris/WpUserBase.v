(* WpUserBase.v -- frames, the Löb theorem, the fetch/step engines, and shared helpers.
   Split from the monolithic WpUserExec.v; all lemmas close over the
   single parameter bundle [uctx] (see WpUserBase).                      *)
(* WpUserExec.v -- the user-execution theorem: the loop frames and the
   Löb skeleton.

   [user_frame] is the loop invariant P of [wp_user_loop]: an ARBITRARY
   user machine -- existential GPRs, pc, trap CSRs, TLB (consistent with
   the page-table spec) -- over the loop-constant configuration (the
   [user_cfg] cells, the page-table ownership [upt_inv], the persistent
   user code bytes, and the writable user data bytes).

   [user_trap_frame] is Tr: the same machine handed to the kernel
   re-entry continuation -- Supervisor privilege, pc at stvec's direct
   base, trap CSRs written (existential here; refined per-cause by the
   USTEP cases that produce it).

   [wp_user_exec] is the Löb capstone: one USTEP obligation -- a single
   machine step from [user_frame] re-establishes [user_frame] (retire)
   or produces [user_trap_frame] (trap), with both continuations under a
   later -- runs arbitrary user code forever.  The USTEP obligation is
   discharged case by case in the companion files (fetch trichotomy x
   decode totality x execute families); the proven instances so far are
   the wp_user_ecall / wp_user_fetch_pagefault vertical slices.        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall UmodeWalk.
Require Import UptInv WpUserLoop.
Local Open Scope Z_scope.
Import Defs.

(* The loop-constant parameter bundle: boot configuration, the page table,
   the user memory image, and the pure boot-config facts.  ONE record so
   every lemma in the split files closes over a single argument [U].     *)
Record uctx := {
  stvec_v : mword 64; mie_v : mword 64; midl_v : mword 64;
  medl_v : mword 64; mip_v : mword 64;
  meip : mword 1; seip : mword 1;
  satp0 : mword 64;
  root : mword 44;
  slots : gmap (mword 64) (mword 64);
  spec : gmap (mword 27) uwalk_info;
  pmpcfg0 : type_of_register pmpcfg_n;
  pmpaddr00 : type_of_register pmpaddr_n;
  code : gmap Arch.pa (bv 8);
  data : gset Arch.pa;
  dq : dfrac; dqc : dfrac;
  Hmm : and_vec mie_v (not_vec midl_v) = zeros' 64;
  Hs0 : and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v midl_v) = zeros' 64;
  Hsatpmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4);
  Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
            = (mword_of_int 0 : mword 16);
  Hroot : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root;
  Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct;
  Hdel_ecall : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true;
  Hdel_fetchpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true;
  Hdel_loadpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Load_Page_Fault tt)))) = true;
  Hdel_samopf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_SAMO_Page_Fault tt)))) = true;
  Hdel_illegal : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true;
  Hdel_break : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true;
  Hdel_fetch_addr_align : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Fetch_Addr_Align tt)))) = true;
  HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR;
  Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false;
  HpmpX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true;
  HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true;
  HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true;
  Hpmp_cov : (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z;
  Hpter : forall regions, pma_allows_all regions -> pma_allows_pte_read regions;
  Hspec : upt_spec root slots spec
}.

Section WpUserBase.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (stvec_v U).
  Local Notation mie_v := (mie_v U).
  Local Notation midl_v := (midl_v U).
  Local Notation medl_v := (medl_v U).
  Local Notation mip_v := (mip_v U).
  Local Notation meip := (meip U).
  Local Notation seip := (seip U).
  Local Notation satp0 := (satp0 U).
  Local Notation root := (root U).
  Local Notation slots := (slots U).
  Local Notation spec := (spec U).
  Local Notation pmpcfg0 := (pmpcfg0 U).
  Local Notation pmpaddr00 := (pmpaddr00 U).
  Local Notation code := (code U).
  Local Notation data := (data U).
  Local Notation dq := (dq U).
  Local Notation dqc := (dqc U).
  Local Notation Hmm := (Hmm U).
  Local Notation Hs0 := (Hs0 U).
  Local Notation Hsatpmode := (Hsatpmode U).
  Local Notation Hasid := (Hasid U).
  Local Notation Hroot := (Hroot U).
  Local Notation Htvd := (Htvd U).
  Local Notation Hdel_ecall := (Hdel_ecall U).
  Local Notation Hdel_fetchpf := (Hdel_fetchpf U).
  Local Notation Hdel_loadpf := (Hdel_loadpf U).
  Local Notation Hdel_samopf := (Hdel_samopf U).
  Local Notation Hdel_illegal := (Hdel_illegal U).
  Local Notation Hdel_break := (Hdel_break U).
  Local Notation HpmpA := (HpmpA U).
  Local Notation Hpmp_ord := (Hpmp_ord U).
  Local Notation HpmpX := (HpmpX U).
  Local Notation HpmpR := (HpmpR U).
  Local Notation HpmpW := (HpmpW U).
  Local Notation Hpmp_cov := (Hpmp_cov U).
  Local Notation Hpter := (Hpter U).
  Local Notation Hspec := (Hspec U).


  (* ------------------------------------------------------------------ *)
  (* The frames                                                          *)
  (* ------------------------------------------------------------------ *)

  (* the loop-constant config cells (fraction [dqc]: never written) *)
  Definition user_cfg : iProp Σ :=
    (stvec ↦ᵣ{ dqc } stvec_v ∗
     mie ↦ᵣ{ dqc } mie_v ∗
     mideleg ↦ᵣ{ dqc } midl_v ∗
     medeleg ↦ᵣ{ dqc } medl_v ∗
     mip ↦ᵣ{ dqc } mip_v ∗
     sig_meip ↦ᵣ{ dqc } meip ∗
     sig_seip ↦ᵣ{ dqc } seip ∗
     satp ↦ᵣ{ dqc } satp0 ∗
     menvcfg ↦ᵣ{ dqc } MENVCFG_S ∗
     senvcfg ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     mstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     sstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 32) ∗
     pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 ∗
     pmpaddr_n ↦ᵣ{ dqc } pmpaddr00)%I.


  (* the user memory image: persistent code bytes + owned data bytes
     (contents existential -- stores retarget them freely) *)
  Definition user_code : iProp Σ :=
    ([∗ map] a ↦ b ∈ code, a ↦ₘ□ b)%I.

  Definition user_data : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8), ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₘ b)%I.


  Global Instance user_code_persistent : Persistent user_code.
  Proof. apply _. Qed.

  (* P: an arbitrary user machine over the constant config.  Everything
     an instruction can change is existential: GPRs, pc, the trap CSRs
     (traps leave the loop, but the OLD values are unconstrained on
     entry), mstatus (SXL pinned), and the TLB (walk fills change it,

     [upt_tlb_ok] survives by upt_tlb_ok_fill). *)
  Definition user_frame : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v va : mword 64)
       (g : gmap regidx (mword 64))
       (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      ⌜_get_Mstatus_SXL ms_v = 'b"10"⌝ ∗
      ⌜upt_tlb_ok spec tlbvec⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ User ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      tlb ↦ᵣ tlbvec ∗
      pc_is va ∗
      gpr_file g ∗
      upt_inv root slots spec ∗
      user_code ∗
      user_data ∗
      user_cfg)%I.

  (* Tr: the machine handed to the kernel re-entry continuation.  The
     trap CSR VALUES are existential at this level; the USTEP cases that
     produce Tr know the exact cause/tval/sepc and can be consumed
     directly when a caller needs them -- this frame is the join point

     the Löb loop needs. *)
  Definition user_trap_frame : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v : mword 64)
       (g : gmap regidx (mword 64))
       (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      ⌜upt_tlb_ok spec tlbvec⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ Supervisor ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      tlb ↦ᵣ tlbvec ∗
      pc_is (stvec_base stvec_v) ∗
      gpr_file g ∗
      upt_inv root slots spec ∗
      user_code ∗
      user_data ∗
      user_cfg)%I.

  (* ------------------------------------------------------------------ *)
  (* The USTEP obligation and the capstone                               *)
  (* ------------------------------------------------------------------ *)

  (* one machine step from the user frame: retire back into the frame,
     or trap into the kernel re-entry frame -- both under a later, as

     the step engines provide *)
  Definition user_step_obligation E (Φ : mval -> iProp Σ) : iProp Σ :=
    (□ (user_frame -∗
        ▷ ((user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
           (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}))%I.


  (* the user-execution theorem, given the per-step case analysis *)
  Theorem wp_user_exec E (Φ : mval -> iProp Σ) :
    user_step_obligation E Φ -∗
    user_frame -∗
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros "#Hstep HP Htr".
    iApply (wp_user_loop with "Hstep HP Htr").
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The U-mode RETIRE engine (TLB-hit, 4-byte, integer families): the    *)
  (* user analog of InstrBytes' [wp_instr].  Fetch goes through the Sv39  *)
  (* hit path at the stored walk entry; decode is a per-word hypothesis   *)
  (* at the concrete [dstateU] (the shape [decode_total_u] instances      *)
  (* provide); the caller supplies ONE execute fact (RETIRE_SUCCESS) at   *)
  (* nextPC := va + 4 and gets the ticked PC back under a later.  FP is   *)
  (* excluded structurally: mstatus.FS = Off in U makes every FP          *)
  (* instruction trap, so the retire engine never sees one.               *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_instr_u_hit
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ tlbvec -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the leaf facts, transported onto the stored TLB entry *)
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- the instruction bytes + RAM-ness of the user code page ---- *)
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* ---- pure facts: fetch, decode, dispatch at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- the caller's execute fact ---- *)
    iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
            (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
            with "[$Hreg $Hmem $Hdev]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.


  Lemma wp_instr_u_hit_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ tlbvec -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the leaf facts, transported onto the stored TLB entry *)
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- the instruction bytes + RAM-ness of the user code page ---- *)
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* ---- pure facts: fetch, decode, dispatch at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- the caller's execute fact ---- *)
    iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
            (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
            with "Htlbc Hupt [$Hreg $Hmem $Hdev]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The U-mode COMPRESSED retire engine (TLB-hit, RVC, ExecuteAs).       *)
  (* Every retiring compressed instruction executes as [ExecuteAs] of its *)
  (* base expansion (UmodeFetchC §5), so the caller supplies the pure     *)
  (* expansion fact and ONE execute fact about the BASE instruction at    *)
  (* nextPC := va + 2 -- the whole existing execute-lemma layer reuses.   *)
  (* The fetch has two modes: at a 4-aligned pc the Ziccif branch reads a *)
  (* full 4-byte window whose LOW HALF is the instruction; at pc == 2     *)
  (* (mod 4) a single 2-byte fetch runs (Zca keeps bit 1 legal).          *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_instr_c_hit
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii ii_b : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry (mode-independent part) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (* the two fetch modes *)
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion *)
    (forall s : mstate, exec (execute ii) s = Some (ExecuteAs ii_b, s)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii_b) (set_reg σ nextPC (add_vec_int va 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ tlbvec -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def Hmode HisRVC Hdec Hexp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    (* ---- width-independent pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HZca : exec (currentlyEnabled Ext_Zca) σ = Some (true, σ)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa. exact HmisaC. }
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- mode split: build the F_RVC fetch fact ---- *)
    destruct Hmode as
      [ (w4 & Hval & Hpaal & Hcw & Hh_eq)
      | (Hb0 & Hb1 & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, F_RVC is the low half *)
      iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte w4 j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
        iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ region
                 Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ Hnc ltac:(lia))
                 (within_sig_false pa 4 σ Hns ltac:(lia))
                 (within_htif_false pa 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv).
        rewrite <- Hh_eq. exact HisRVC. }
      (* ---- the caller's execute fact ---- *)
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "[$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
    - (* pc == 2 (mod 4): single 2-byte fetch *)
      iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 1%nat ltac:(lia)) with "Hcode") as "Hb1".
        iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 2) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ region
                 Lpc Hb0 Hb1 Hval4 HmisaC' Htr HA' Hord' Hrange' HX' Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ Hnc ltac:(lia))
                 (within_sig_false pa 2 σ Hns ltac:(lia))
                 (within_htif_false pa 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv HisRVC). }
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "[$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  Lemma wp_instr_c_hit_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii ii_b : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry (mode-independent part) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (* the two fetch modes *)
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    (* the pure expansion *)
    (forall s : mstate, exec (execute ii) s = Some (ExecuteAs ii_b, s)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ tlbvec -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii_b) (set_reg σ nextPC (add_vec_int va 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def Hmode HisRVC Hdec Hexp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    (* ---- width-independent pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HZca : exec (currentlyEnabled Ext_Zca) σ = Some (true, σ)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa. exact HmisaC. }
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- mode split: build the F_RVC fetch fact ---- *)
    destruct Hmode as
      [ (w4 & Hval & Hpaal & Hcw & Hh_eq)
      | (Hb0 & Hb1 & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, F_RVC is the low half *)
      iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte w4 j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
        iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ region
                 Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ Hnc ltac:(lia))
                 (within_sig_false pa 4 σ Hns ltac:(lia))
                 (within_htif_false pa 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv).
        rewrite <- Hh_eq. exact HisRVC. }
      (* ---- the caller's execute fact ---- *)
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "Htlbc Hupt [$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
    - (* pc == 2 (mod 4): single 2-byte fetch *)
      iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 1%nat ltac:(lia)) with "Hcode") as "Hb1".
        iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 2) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ region
                 Lpc Hb0 Hb1 Hval4 HmisaC' Htr HA' Hord' Hrange' HX' Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ Hnc ltac:(lia))
                 (within_sig_false pa 2 σ Hns ltac:(lia))
                 (within_htif_false pa 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv HisRVC). }
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "Htlbc Hupt [$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_exec h ii ii_b va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact Hexec. }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.



  Lemma wp_instr_c_hit_direct
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (h : mword 16) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* fetch-hit facts *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    (* va / pa geometry (mode-independent part) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (* the two fetch modes *)
    ((exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
     \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
         neq_vec (access_vec_dec va 1) ('b"0") = true /\
         is_aligned_vaddr (Virtaddr va) 4 = false /\
         is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
         (forall j : nat, (j < 2)%nat ->
            code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte h j)))) ->
    isRVC h = true ->
    (* decode at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = tlbvec
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ tlbvec -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def Hmode HisRVC Hdec.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    (* ---- width-independent pure facts at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HZca : exec (currentlyEnabled Ext_Zca) σ = Some (true, σ)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa. exact HmisaC. }
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- mode split: build the F_RVC fetch fact ---- *)
    destruct Hmode as
      [ (w4 & Hval & Hpaal & Hcw & Hh_eq)
      | (Hb0 & Hb1 & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, F_RVC is the low half *)
      iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte w4 j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
        iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ region
                 Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ Hnc ltac:(lia))
                 (within_sig_false pa 4 σ Hns ltac:(lia))
                 (within_htif_false pa 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv).
        rewrite <- Hh_eq. exact HisRVC. }
      (* ---- the caller's execute fact ---- *)
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "[$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { exact (exec_hart_active_progress_RVC_direct_gen User σ σ s_exec h ii va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca Hexec I). }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
    - (* pc == 2 (mod 4): single 2-byte fetch *)
      iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
        iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      iAssert (⌜addr_is_ram (pa_add pa 1)⌝)%I as %Hram1.
      { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                     (Hcw 1%nat ltac:(lia)) with "Hcode") as "Hb1".
        iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro. exact Hr1. }
      pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
      destruct (Hpma_all pa 2) as (region & Hpmam & Hpmax & _ & _ & _).
      assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ region
                 Lpc Hb0 Hb1 Hval4 HmisaC' Htr HA' Hord' Hrange' HX' Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ Hnc ltac:(lia))
                 (within_sig_false pa 2 σ Hns ltac:(lia))
                 (within_htif_false pa 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv HisRVC). }
      iMod ("H" $! σ Lpc (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')
              (conj Lpriv (conj Lms (conj Lsatp (conj Ltlb (conj Lpmpc Lpmpa)))))
              with "[$Hreg $Hmem $Hdev]")
        as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
      iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
      { exact (exec_hart_active_progress_RVC_direct_gen User σ σ s_exec h ii va
                 RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca Hexec I). }
      iModIntro.
      iExists (zero_extend' 32 h), s_exec.
      iSplitR; [iPureIntro; exact Hha |].
      rewrite Lpc_exec.
      iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc'").
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.


  (* decode-state agreement survives a nextPC write (nextPC is outside
     the decode read set D_u) *)
  Lemma agree_u_set_nextPC (s : mstate) (v : mword 64) :
    agree_on D_u s dstateU ->
    agree_on D_u (set_reg s nextPC v) dstateU.
  Proof.
    intros H r Hr.
    pose proof Hr as Hr'.
    unfold D_u in Hr'.
    unfold set_reg; cbn [sregs].
    repeat (apply orb_true_elim in Hr' as [Hr'|Hr']);
      apply register_beq_eq in Hr'; subst r;
      (rewrite irrelevant_register_set; [ exact (H _ Hr) | vm_compute; reflexivity ]).
  Qed.

  (* Zicfilp is disabled at the user decode state (mseccfg.MLPE = 0,
     menvcfg.LPE = 0): transported by the read-frame bridge, like the

     per-word decode facts *)
  Lemma exec_cE_zicfilp_false_u (s : mstate) :
    agree_on D_u s dstateU ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
  Proof.
    intros Hag.
    apply (decode_state_bridge D_u _ dstateU);
      [ exact Hag | vm_compute; reflexivity | vm_compute; reflexivity ].
  Qed.


  (* decode-state agreement also survives a tlb write *)
  Lemma agree_u_set_tlb (s : mstate) (v : vec (option TLB_Entry) (2 ^ 6)) :
    agree_on D_u s dstateU ->
    agree_on D_u (set_reg s tlb v) dstateU.
  Proof.
    intros H r Hr.
    pose proof Hr as Hr'.
    unfold D_u in Hr'.
    unfold set_reg; cbn [sregs].
    repeat (apply orb_true_elim in Hr' as [Hr'|Hr']);
      apply register_beq_eq in Hr'; subst r;
      (rewrite irrelevant_register_set; [ exact (H _ Hr) | vm_compute; reflexivity ]).
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The U-mode RETIRE engine, TLB-MISS twin: the fetch walks the owned   *)
  (* page table (empty hash slot), FILLS the TLB with the walk entry, and *)
  (* proceeds exactly as the hit engine from the filled state.  The       *)
  (* continuation gets the tlb cell back at the FILLED vector, with       *)
  (* [upt_tlb_ok] re-established by [upt_tlb_ok_fill].                    *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_instr_u_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some ie ->
    (* the lookup MISSES: the hash slot is empty, or holds a non-matching
       (colliding) entry *)
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                    (Some (upt_entry vpn ie))) -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          upt_inv root slots spec -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hvec Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- the three PTE reads off the owned slots ---- *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HA' Hord' HR' Hcov' Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    (* ---- pure facts: the walk-filling translate + fetch at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    set (tlbvec' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (upt_entry vpn ie))).
    set (σ' := set_reg σ tlb tlbvec').
    assert (Htr : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
                    = Some (Ok (Physaddr (u_walk_pa (uw_pte0 ie) va),
                                PBMT_PMA, init_ext_ptw), σ')).
    { destruct Hvec as [Hvec | (ent' & Hvec & Hnm)].
      - exact (exec_translateAddr_fetch_walk_u vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def).
      - exact (exec_translateAddr_fetch_walk_u_nomatch ent' vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec Hnm HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def). }
    (* ---- fetch through the FILLED state σ' ---- *)
    set (pa := u_walk_pa (uw_pte0 ie) va) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    (* σ' pins: everything except tlb is untouched *)
    assert (LpmpcX : register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0)
      by (unfold σ'; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00)
      by (unfold σ'; lk; exact Lpmpa).
    assert (LpmaX : register_lookup pma_regions σ'.(sregs) = pmar0)
      by (unfold σ'; lk; exact Lpma).
    assert (LhtifX : register_lookup htif_tohost_base σ'.(sregs) = None)
      by (unfold σ'; lk; exact Lhtif).
    assert (LprivX : register_lookup cur_privilege σ'.(sregs) = User)
      by (unfold σ'; lk; exact Lpriv).
    assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
      by (unfold σ'; lk; exact Lelp).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite LpmpaX.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ' region
                  Lpc Hval Htr
                  ltac:(rewrite LpmpcX; exact HpmpA)
                  ltac:(rewrite LpmpaX; exact Hpmp_ord)
                  Hrange'
                  ltac:(rewrite LpmpcX; exact HpmpX)
                  ltac:(rewrite LpmaX; exact Hpmam)
                  Hpaal Hpmax
                  (within_clint_false pa 4 σ' Hnc ltac:(lia))
                  (within_sig_false pa 4 σ' Hns ltac:(lia))
                  (within_htif_false pa 4 σ' LhtifX)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf LprivX HnotRVC) as Hfetch.
    (* decode at σ' (agreement survives the tlb fill) *)
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagX.
    pose proof (Hdec σ' HagX) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite LelpX; exact Help_np).
    assert (LpcX : register_lookup PC σ'.(sregs) = va)
      by (unfold σ'; lk; exact Lpc).
    (* ---- ghost tlb fill, then the caller's execute fact at σ' ---- *)
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod ("H" $! σ' LpcX HagX with "[Hreg Hmem Hdev]") as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    { unfold σ', set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ' s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad LpcX).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Htlbc Hpc' Hupt").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

  (* ================================================================= *)
  (* Combined fetch-MISS engine WITH the data callback (tlb+upt threaded  *)
  (* into the execute step so a memory arm can walk+fill the DATA EA).    *)
  (* Miss twin of wp_instr_u_hit_data / data twin of wp_instr_u_miss.     *)
  (* ================================================================= *)
  Lemma wp_instr_u_miss_data
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (ii : instruction) (ms_v : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some ie ->
    (* the lookup MISSES: the hash slot is empty, or holds a non-matching
       (colliding) entry *)
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    tlb ↦ᵣ tlbvec -∗
    PC ↦ᵣ va -∗
    user_code -∗
    upt_inv root slots spec -∗
    user_cfg -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (Hag : agree_on D_u σ dstateU)
       (Hpins : register_lookup cur_privilege σ.(sregs) = User
             /\ register_lookup mstatus σ.(sregs) = ms_v
             /\ register_lookup satp σ.(sregs) = satp0
             /\ register_lookup tlb σ.(sregs) = vec_update_dec tlbvec
                                                  (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))
             /\ register_lookup pmpcfg_n σ.(sregs) = pmpcfg0
             /\ register_lookup pmpaddr_n σ.(sregs) = pmpaddr00),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute ii) (set_reg σ nextPC (add_vec_int va 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          cur_privilege ↦ᵣ User -∗
          mstatus ↦ᵣ ms_v -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          user_cfg -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hsome Hvec Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Htlbc Hpc #Hcode Hupt Hcfg H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    destruct (Hspec vpn ie Hsome) as (Hsl2 & Hsl1 & Hsl0 & Hwf).
    destruct Hwf as (H2i & H2nl & H1i & H1nl & H0i & H0nl & H0N & Hglob & Hpbmt0).
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    (* ---- the three PTE reads off the owned slots ---- *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HA' Hord' HR' Hcov' Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(Hrd2 & Hrd1 & Hrd0 & _).
    (* ---- pure facts: the walk-filling translate + fetch at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    set (tlbvec' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                      (Some (upt_entry vpn ie))).
    set (σ' := set_reg σ tlb tlbvec').
    assert (Htr : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
                    = Some (Ok (Physaddr (u_walk_pa (uw_pte0 ie) va),
                                PBMT_PMA, init_ext_ptw), σ')).
    { destruct Hvec as [Hvec | (ent' & Hvec & Hnm)].
      - exact (exec_translateAddr_fetch_walk_u vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def).
      - exact (exec_translateAddr_fetch_walk_u_nomatch ent' vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 H2i H2nl H1i H1nl H0i H0nl (fun s0 => Hchk0 false false s0) H0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec Hnm HupdN
                 Hrd2 Hrd1 Hrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def). }
    (* ---- fetch through the FILLED state σ' ---- *)
    set (pa := u_walk_pa (uw_pte0 ie) va) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    (* σ' pins: everything except tlb is untouched *)
    assert (LpmpcX : register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0)
      by (unfold σ'; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00)
      by (unfold σ'; lk; exact Lpmpa).
    assert (LpmaX : register_lookup pma_regions σ'.(sregs) = pmar0)
      by (unfold σ'; lk; exact Lpma).
    assert (LhtifX : register_lookup htif_tohost_base σ'.(sregs) = None)
      by (unfold σ'; lk; exact Lhtif).
    assert (LprivX : register_lookup cur_privilege σ'.(sregs) = User)
      by (unfold σ'; lk; exact Lpriv).
    assert (LelpX : register_lookup elp σ'.(sregs) = elp0)
      by (unfold σ'; lk; exact Lelp).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite LpmpaX.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ' region
                  Lpc Hval Htr
                  ltac:(rewrite LpmpcX; exact HpmpA)
                  ltac:(rewrite LpmpaX; exact Hpmp_ord)
                  Hrange'
                  ltac:(rewrite LpmpcX; exact HpmpX)
                  ltac:(rewrite LpmaX; exact Hpmam)
                  Hpaal Hpmax
                  (within_clint_false pa 4 σ' Hnc ltac:(lia))
                  (within_sig_false pa 4 σ' Hns ltac:(lia))
                  (within_htif_false pa 4 σ' LhtifX)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf LprivX HnotRVC) as Hfetch.
    (* decode at σ' (agreement survives the tlb fill) *)
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagX.
    pose proof (Hdec σ' HagX) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite LelpX; exact Help_np).
    assert (LpcX : register_lookup PC σ'.(sregs) = va)
      by (unfold σ'; lk; exact Lpc).
    assert (HpinsX : register_lookup cur_privilege σ'.(sregs) = User
                  /\ register_lookup mstatus σ'.(sregs) = ms_v
                  /\ register_lookup satp σ'.(sregs) = satp0
                  /\ register_lookup tlb σ'.(sregs) = tlbvec'
                  /\ register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0
                  /\ register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00).
    { split; [ exact LprivX
      | split; [ unfold σ'; lk; exact Lms
      | split; [ unfold σ'; lk; exact Lsatp
      | split; [ unfold σ', set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity
      | split; [ exact LpmpcX | exact LpmpaX ]]]]]. }
    (* ---- ghost tlb fill, then the caller's execute fact at σ' ---- *)
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod ("H" $! σ' LpcX HagX HpinsX with "Htlbc Hupt [Hreg Hmem Hdev]") as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    { unfold σ', set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* ---- the whole retiring step ---- *)
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { apply (exec_hart_active_progress_base_gen User σ σ' s_exec w ii va
               RETIRE_SUCCESS Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad LpcX).
      - exact Hexec.
      - exact I. }
    iModIntro.
    iExists (zero_extend' 32 w), s_exec.
    iSplitR; [iPureIntro; exact Hha |].
    rewrite Lpc_exec.
    iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hpc'").
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.


End WpUserBase.
