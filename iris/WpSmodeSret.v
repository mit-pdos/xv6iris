(* WpSmodeSret.v -- K2: wp_sret_gpr, the SRET endpoint WP on the new
   [instr] / [wp_instr_s_config] layer (the S-mode mirror of WpGprMretNew's
   [wp_mret_gpr] recipe).

   SRET writes mstatus (SIE<-SPIE, SPIE<-1, SPP<-0, MPRV<-0, SPELP<-0),
   cur_privilege (<- SPP-decoded newpriv; for xv6's kernelvec SPP=1 so
   newpriv = Supervisor, taken as the premise [sret_newpriv mstatus0 =
   Supervisor]) and elp -- cells [smode_config] bundles -- so it sits on the
   raw-cell [wp_instr_s_config] engine with the mstatus VALUE explicit.

   The elp write: SRET sets elp := (if lpe then SPELP else NO_LP_EXPECTED).
   elp is pinned PERSISTENTLY by [hw_config] (elp ↦ᵣ□ elp0, elp0 ≠
   LP_EXPECTED, hence = NO_LP_EXPECTED), so the WP requires menvcfg.LPE = 0
   (get_xLPE Supervisor reads menvcfg) forcing lpe = false, making the
   physical write VALUE-PRESERVING -- absorbed by [reg_interp_set_same]
   with no ghost update (same trick as wp_mret_gpr).

   The execute reduction [exec_execute_SRET_menv] is the archived
   WpGprSret.v reduction with the un-dischargeable [forall sz, get_xLPE ..]
   premise replaced by the menvcfg-pinned per-state form (the same repair
   wp_mret_gpr applied to MRET): get_xLPE is read at ONE intermediate state
   of the tower, where menvcfg is untouched by the preceding set_regs. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprMret WpGprMretNew.
Require Import SmodeCore WpSmodeGpr.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* The SRET post-execute CSR tower, as functions of the initial mstatus / *)
(* sepc (names as in the archived WpKvSret.v).                            *)
(* ===================================================================== *)
Definition sret_ms1 (ms0 : mword 64) := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
Definition sret_ms2 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms1 ms0) 5 5 ('b"1").
Definition sret_newpriv (ms0 : mword 64) : Privilege :=
  if eq_vec (_get_Mstatus_SPP (sret_ms2 ms0)) ('b"1") then Supervisor else User.
Definition sret_ms3 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms2 ms0) 8 8 ('b"0").
Definition sret_ms4 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms3 ms0) 17 17 ('b"0").
Definition sret_ms5 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms4 ms0) 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
Definition sret_tgt (sepc0 : mword 64) := update_vec_dec sepc0 0 ('b"0").

(* ===================================================================== *)
(* exec_execute_SRET_menv -- the SRET reduction (archived WpGprSret.v)    *)
(* with the get_xLPE premise pinned by the menvcfg VALUE: it is read at   *)
(* one intermediate state [s6] of the tower, where menvcfg is untouched.  *)
(* ===================================================================== *)
Section ExecSRET.
  Context (s : mstate) (lpe : bool) (menvcfg0 : mword 64).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 5 5 ('b"1").
  Let newpriv : Privilege := if eq_vec (_get_Mstatus_SPP ms2) ('b"1") then Supervisor else User.
  Let ms3 := update_subrange_vec_dec ms2 8 8 ('b"0").
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_SPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := update_vec_dec (register_lookup sepc s.(sregs)) 0 ('b"0").
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HTSR : eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis Hlpe : forall sz : mstate,
      register_lookup menvcfg sz.(sregs) = menvcfg0 ->
      exec (get_xLPE newpriv) sz = Some (lpe, sz).

  Lemma exec_execute_SRET_menv : exec (execute (SRET tt)) s = Some (RETIRE_SUCCESS, sF).
  Proof using All.
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    (* read cur_privilege = Supervisor; reduce the sret_illegal guard to false *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. cbn match.
    assert (Harm1 : exec (Defs.bind (currentlyEnabled Ext_S)
                          (fun w1 : bool => returnM (Riscv.rv64d.not w1))) s = Some (false, s)).
    { rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS.
      cbn [Riscv.rv64d.not negb]. apply exec_returnM. }
    assert (Hguard : exec (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                            (fun w1 : bool => returnM (Riscv.rv64d.not w1)))
                          (Defs.bind (Defs.read_reg mstatus)
                            (fun w2 : mword 64 => returnM (eq_vec (_get_Mstatus_TSR w2) ('b"1"))))) s
                    = Some (false, s)).
    { unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ Harm1). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite HTSR. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hguard). cbn match.
    change (ext_check_xret_priv Supervisor) with true. cbn [Riscv.rv64d.not negb]. cbn match.
    (* prev_priv read *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    (* read mstatus (w7), read mstatus (w8) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    (* write mstatus ms1 (bit1 := SPIE) *)
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms1 s)).
    (* read mstatus (w9 = ms1); write mstatus ms2 (bit5 := 1) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms2 s1)).
    (* read mstatus (w10 = ms2); newpriv from SPP; write cur_privilege newpriv *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege newpriv s2)).
    (* read mstatus (w12 = ms2); write mstatus ms3 (bit8 SPP := 0) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set; [subst s2; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms3 s3)).
    (* read cur_privilege (w13 = newpriv); guard newpriv<>Machine -> then branch *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set; [subst s3; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    assert (Hnpm : generic_neq newpriv Machine = true)
      by (unfold newpriv; destruct (eq_vec (_get_Mstatus_SPP ms2) ('b"1")); reflexivity).
    rewrite Hnpm. cbn match.
    (* read mstatus (w14 = ms3); write mstatus ms4 (bit17 MPRV := 0) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms4 s4)).
    (* zicfilp sRET branch: read mstatus(ms4) x2, write mstatus ms5 (bit23), elp *)
    set (s6 := set_reg s5 mstatus ms5).
    set (s7 := set_reg s6 elp elpv).
    assert (HL6 : register_lookup menvcfg s6.(sregs) = menvcfg0).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Hmenv. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12)) s5
               = Some (tt, s7))).
        2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s5)).
            replace (register_lookup cur_privilege s5.(sregs)) with newpriv
              by (subst s5 s4 s3; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite register_lookup_set; reflexivity).
            unfold zicfilp_restore_elp_on_xret. cbn match.
            rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind (Defs.read_reg mstatus)
                     (fun w0 : mword 64 => Defs.bind (Defs.read_reg mstatus)
                        (fun w1 : mword 64 => Defs.bind0
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 23 23
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_SPELP w0))))) s5
                   = Some (_get_Mstatus_SPELP ms4, s6))).
            2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms5 s5)).
                apply exec_returnm. }
            rewrite (exec_bind_Some _ _ _ _ _ (Hlpe s6 HL6)).
            rewrite (exec_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    (* TAIL: callback / print(false) / prepare_xret Supervisor = sepc / set_next_pc *)
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Supervisor)) s7 = Some (tgt, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7))).
        2:{ rewrite (exec_bind0_Some _ _ _ _ _
              (_ : exec (long_csr_write_callback "mstatus" "mstatush" ms5) s7 = Some (tt, s7))).
            2:{ apply exec_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_returnm. }
        (* prepare_xret_target Supervisor = read sepc >>= align_pc = tgt *)
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s7)).
        replace (register_lookup sepc s7.(sregs)) with (register_lookup sepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_bind_Some _ _ _ _ _
          (_ : exec (currentlyEnabled Ext_Zca) s7 = Some (true, s7))).
        2:{ apply exec_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Hmc. }
        cbn match. apply exec_returnM. }
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_set_next_pc tgt s7)).
    apply exec_returnm.
  Qed.
End ExecSRET.

(* ===================================================================== *)
(* wp_sret_gpr -- the SRET endpoint WP.  Raw unbundled S-cells at full    *)
(* ownership with the mstatus VALUE explicit; premises pin the decode of  *)
(* SPP to Supervisor and force lpe = false (menvcfg.LPE = 0 + the         *)
(* persistent elp pinning).  The continuation receives the RAW post-SRET  *)
(* cells: privilege Supervisor, mstatus [sret_ms5 mstatus0], pc at the    *)
(* bit0-cleared sepc target; everything else (incl. the GPR file and      *)
(* sepc) unchanged.                                                       *)
(* ===================================================================== *)
Section WpSretGpr.
  Context `{!riscvGS Σ}.


  (* ------------------------------------------------------------------- *)
  (* UNIFIED: wp_sret_gpr over the TLB/page-table consistency invariant.  *)
  (* No slot facts: the fetch either hits the identity entry or walks the *)
  (* owned PTE and fills slot 5 (preserving the invariant).  SRET itself  *)
  (* never touches the TLB, so the invariant round-trips unchanged.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sret_gpr (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (* fetch: page-table geometry (SRET is a 4-byte F_Base) *)
    kv_fetch_geom pc ->
    kv_fetch_geom (add_vec_int pc 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    (* the walk's PTE read *)
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* SRET-specific premises *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    tlb_inv root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (SRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pmpaddr_n ↦ᵣ pmpaddr00 -∗
      tlb_inv root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom Hgeom2 Hpmp
             Hpmpp Hpteregion Halignp HTSR Hsup Hlpe0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hsepc
       [Hpc Hnpc] Hfile Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    assert (Hxlpe : forall sz : mstate,
              register_lookup menvcfg sz.(sregs) = menvcfg0 ->
              exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (false, sz)).
    { intros sz Hm. rewrite Hsup. apply exec_get_xLPE_S. rewrite Hm. exact Hlpe0. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (SRET tt)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE Hgeom (fun _ => Hgeom2) Hpmp
              Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    (* tick nextPC := pc+4 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lsepc_pc : register_lookup sepc s_pc.(sregs) = sepc0)
      by (unfold s_pc; tmig; exact Lsepc).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the SRET execute reduction at s_pc, with lpe = false *)
    pose proof (exec_execute_SRET_menv s_pc false menvcfg0
                  Lpriv_pc
                  ltac:(rewrite Lmisa_pc; exact HmisaS)
                  ltac:(rewrite Lms_pc; exact HTSR)
                  ltac:(rewrite Lmisa_pc; exact HmisaC)
                  Lmenv_pc
                  ltac:(intros sz Hm;
                        pose proof (Hxlpe sz Hm) as Hx;
                        unfold sret_newpriv, sret_ms2, sret_ms1 in Hx;
                        rewrite Lms_pc; exact Hx)) as HexecC0.
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 mstatus0)) mstatus (sret_ms2 mstatus0))
                           cur_privilege Supervisor) mstatus (sret_ms3 mstatus0)) mstatus (sret_ms4 mstatus0))
                  mstatus (sret_ms5 mstatus0)) elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (sret_tgt sepc0)).
    assert (HexecC : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite HexecC0. unfold sX.
      rewrite !Lms_pc Lsepc_pc.
      unfold sret_newpriv, sret_ms2, sret_ms1 in Hsup.
      unfold sret_ms1, sret_ms2, sret_ms3, sret_ms4, sret_ms5, sret_tgt.
      rewrite Hsup. reflexivity. }
    (* mirror the physical set_regs on the ghost cells *)
    iMod (reg_update _ mstatus _ (sret_ms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (sret_ms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (sret_ms5 mstatus0) (register_set mstatus (sret_ms4 mstatus0)
                (register_set mstatus (sret_ms3 mstatus0) (register_set cur_privilege Supervisor
                  (register_set mstatus (sret_ms2 mstatus0) (register_set mstatus (sret_ms1 mstatus0)
                    (register_set nextPC (add_vec_int pc 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (sret_tgt sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists sX.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold sX, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC sX.(sregs) = sret_tgt sepc0)
      by (unfold sX, set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes] Hsepc
                          [$Hpc' $Hnpc] Hfile").
    iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
              with "Hsatp Htlb Hpbytes").
  Qed.

End WpSretGpr.
