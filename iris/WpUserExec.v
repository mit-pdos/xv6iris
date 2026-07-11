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
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr.
Require Import SmodeCore WpIntrCore.
Require Import UmodeTrap UmodeFetch UmodeStep UmodeEcall UmodeFetchFault UmodeWalk.
Require Import UptInv WpUserLoop.
Local Open Scope Z_scope.
Import Defs.

Section WpUserExec.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* Loop-constant parameters: the boot configuration, the page table,   *)
  (* and the user memory image.                                          *)
  (* ------------------------------------------------------------------ *)
  Context (stvec_v mie_v midl_v medl_v mip_v : mword 64).
  Context (meip seip : mword 1).
  Context (satp0 : mword 64).
  Context (root : mword 44).
  Context (slots : gmap (mword 64) (mword 64)).
  Context (spec : gmap (mword 27) uwalk_info).
  Context (pmpcfg0 : type_of_register pmpcfg_n).
  Context (pmpaddr00 : type_of_register pmpaddr_n).
  (* user code bytes: immutable, hence persistent ([↦ₘ□]) *)
  Context (code : gmap Arch.pa (bv 8)).
  (* user data byte addresses: owned writable, contents existential *)
  Context (data : gset Arch.pa).
  Context {dq dqc : dfrac}.

  (* ---- pure boot-config hypotheses (loop-constant) ---- *)
  (* no interrupt can become pending in U-mode *)
  Hypothesis Hmm : and_vec mie_v (not_vec midl_v) = zeros' 64.
  Hypothesis Hs0 :
    and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v midl_v) = zeros' 64.
  (* satp: Sv39, asid 0, rooted at [root] *)
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid :
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16).
  Hypothesis Hroot :
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
  (* stvec: direct mode *)
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  (* every synchronous U-mode cause the loop can raise is delegated *)
  Hypothesis Hdel_ecall : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true.
  Hypothesis Hdel_fetchpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true.
  Hypothesis Hdel_loadpf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Load_Page_Fault tt)))) = true.
  Hypothesis Hdel_samopf : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_SAMO_Page_Fault tt)))) = true.
  Hypothesis Hdel_illegal : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true.
  Hypothesis Hdel_break : bit_to_bool (access_vec_dec medl_v
    (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true.
  (* PMP entry 0: an RWX TOR entry covering all of RAM *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false.
  Hypothesis HpmpX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true.
  Hypothesis Hpmp_cov : (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z.
  (* the boot PMA list supports PTE reads everywhere (concrete-list fact) *)
  Hypothesis Hpter : forall regions, pma_allows_all regions -> pma_allows_pte_read regions.
  (* the slot map describes the page table rooted at [root] *)
  Hypothesis Hspec : upt_spec root slots spec.

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

End WpUserExec.
