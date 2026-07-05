(* WpGprMretNew.v -- the MRET endpoint WP on the NEW [instr]/[wp_instr_config]
   layer.  MRET writes mstatus, cur_privilege and elp -- cells that live in
   (or, for elp, are persistently pinned by) the ambient config -- so it takes
   the UNBUNDLED config premises with the mstatus VALUE explicit (the target
   privilege is decoded from mstatus.MPP, which an opaque [mmode_config] would
   hide).  A chain arriving here with the opaque bundle first applies
   [mmode_config_unbundle]; the boot chain knows the concrete mstatus value
   from [wp_csrw_mstatus_gpr]'s raw-cell continuation plus the
   [mstatus_legalized_*] preservation lemmas (WpGprCsrwC.v).

   The elp write: MRET sets elp := (if lpe then MPELP else NO_LP_EXPECTED).
   In this development elp is pinned PERSISTENTLY by [hw_config] (elp ↦ᵣ□
   elp0 with elp0 ≠ LP_EXPECTED, hence elp0 = NO_LP_EXPECTED on a 1-bit
   register), so the WP requires lpe = false (xv6: Zicfilp's xLPE is off) and
   the physical write is VALUE-PRESERVING -- absorbed by [reg_interp_set_same]
   with no ghost update.

   Execute reduction: reuses [exec_execute_MRET] (WpGprMret.v) and the clean
   post-state values [cms1..cms5]/[ctgt] (WpGprMretWp.v) wholesale. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Require Import WpGpr.
Require Import InstrBytes.
Require Import WpGprMret WpGprMretWp.

(* A 1-bit vector that is not LP_EXPECTED ('b"1") is NO_LP_EXPECTED ('b"0"). *)
Lemma mword1_not_lp (x : mword 1) :
  eq_vec x (landing_pad_bits_backwards LP_EXPECTED) = false ->
  x = landing_pad_bits_backwards NO_LP_EXPECTED.
Proof.
  intro H.
  change (landing_pad_bits_backwards LP_EXPECTED) with ('b"1" : mword 1) in H.
  change (landing_pad_bits_backwards NO_LP_EXPECTED) with ('b"0" : mword 1).
  apply bv_eq.
  replace (bv_unsigned ('b"0" : mword 1)) with 0 by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ x) as Hr.
  replace (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2 in Hr
    by (vm_compute; reflexivity).
  destruct (decide (bv_unsigned x = 1)) as [He|Hne]; [| lia].
  exfalso.
  assert (Hx1 : x = ('b"1" : mword 1)).
  { apply bv_eq. rewrite He. vm_compute. reflexivity. }
  rewrite Hx1 in H. vm_compute in H. discriminate H.
Qed.

(* Same-value physical register write: if the register already holds [v], the
   ghost register bridge is preserved by [register_set r v] with NO ghost
   update -- the agreement map is untouched.  This absorbs MRET's elp write
   (elp is persistently pinned, so no full-ownership cell exists to update). *)
Lemma reg_interp_set_same `{!riscvGS Σ} `{CpuId} (rs : regstate) (r : register)
    (v : type_of_register r) :
  register_lookup r rs = v ->
  reg_interp rs -∗ reg_interp (register_set r v rs).
Proof.
  iIntros (Hlk) "Hi". iDestruct "Hi" as (mp) "[Hm %Hag]".
  iExists mp. iFrame "Hm". iPureIntro.
  intros k dv Hk.
  destruct (decide (k = r)) as [->|Hne].
  - rewrite (Hag r dv Hk) register_lookup_set Hlk. reflexivity.
  - rewrite (Hag k dv Hk)
      (irrelevant_register_set k r rs v (register_beq_false k r Hne)).
    reflexivity.
Qed.

(* get_xLPE at Supervisor reads the menvcfg REGISTER; with menvcfg's value
   pinned by a points-to (and its LPE bit clear) the read reduces per-state.
   This replaces the old un-dischargeable [forall sz, exec (get_xLPE ..) ..]
   premise: the WP below derives the fact at the exact intermediate state the
   MRET reduction reads it (menvcfg is untouched by the preceding set_regs). *)
Lemma exec_get_xLPE_S (sz : mstate) :
  _get_MEnvcfg_LPE (register_lookup menvcfg sz.(sregs)) = ('b"0") ->
  exec (get_xLPE Supervisor) sz = Some (false, sz).
Proof.
  intro HL.
  unfold get_xLPE. destruct (Defs.Zwf_guarded _).
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb 2 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl sz)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg sz)).
  rewrite HL.
  replace (bool_bit_backwards ('b"0")) with false by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Section WpMretGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* wp_mret_gpr: the new-layer MRET WP.  Unbundled config premises with the
     mstatus value [ms_cur] explicit; premises mirror [wp_mret]'s execute
     tower: the decoded MPP target [newpriv] (for xv6: Supervisor, from
     [mstatus_legalized_MPP] on the csrw'd value), newpriv ≠ Machine, and the
     xLPE-off fact (lpe = false, forced by the persistent elp pinning).
     The continuation receives the RAW post-MRET cells: privilege [newpriv],
     mstatus [cms5 ms_cur], pc at the aligned mepc target [ctgt mepc0]; pmpcfg,
     mepc and the GPR file are unchanged. *)
  Lemma wp_mret_gpr E (Φ : mval -> iProp Σ) (pc : mword 64)
      (newpriv : Privilege)
      (ms_cur mepc0 menvcfg1 : mword 64)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms_cur) ('b"1") = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms_cur -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    menvcfg ↦ᵣ menvcfg1 -∗
    pc_is pc -∗
    gpr_file m -∗
    mepc ↦ᵣ mepc0 -∗
    instr pc false (MRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ newpriv -∗
      mstatus ↦ᵣ cms5 ms_cur -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      menvcfg ↦ᵣ menvcfg1 -∗
      pc_is (ctgt mepc0) -∗
      gpr_file m -∗
      mepc ↦ᵣ mepc0 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp HmIE Hnp Hsup Hlpe0)
      "#Hhw #Hinv Hhs Hpriv Hms Hpmpc Hmenv [Hpc Hnpc] Hfile Hmepc Hinstr Hcont".
    assert (Hnpm : generic_neq newpriv Machine = true)
      by (rewrite Hsup; vm_compute; reflexivity).
    iApply (wp_instr_config E Φ pc false (MRET tt) pmpcfg0 ms_cur HN Hpmp HmIE
              with "Hhw Hinv Hhs Hpriv Hms Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid    with "Hreg Hmepc")  as %Lmepc.
    iDestruct (reg_valid    with "Hreg Hmenv")  as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    (* tick nextPC := pc+4 (the fetch-advance the execute obligation is stated at) *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    (* transfer the σ-level lookups to s_pc *)
    assert (LprivP : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (LmsP : register_lookup mstatus s_pc.(sregs) = ms_cur)
      by (unfold s_pc; tmig; exact Lms).
    assert (LmepcP : register_lookup mepc s_pc.(sregs) = mepc0)
      by (unfold s_pc; tmig; exact Lmepc).
    assert (HmuP : eq_vec (_get_Misa_U (register_lookup misa s_pc.(sregs))) ('b"1") = true)
      by (unfold s_pc; tmig; rewrite Lmisa; exact HmisaU).
    assert (HmcP : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true)
      by (unfold s_pc; tmig; rewrite Lmisa; exact HmisaC).
    assert (HnpP : privLevel_bits_forwards
              (_get_Mstatus_MPP (update_subrange_vec_dec
                 (update_subrange_vec_dec (register_lookup mstatus s_pc.(sregs)) 3 3
                    (_get_Mstatus_MPIE (register_lookup mstatus s_pc.(sregs)))) 7 7 ('b"1")),
               ('b"0")) = returnM newpriv)
      by (rewrite LmsP; exact Hnp).
    (* the MRET execute reduction, with the post-state phrased on the OWNED
       values (cms1..cms5 / ctgt) *)
    (* the per-state get_xLPE fact, at whatever intermediate state the MRET
       reduction reads it: menvcfg is preserved by the preceding set_regs. *)
    assert (Hxlpe : forall sz, register_lookup menvcfg sz.(sregs) = menvcfg1 ->
              exec (get_xLPE newpriv) sz = Some (false, sz)).
    { intros sz Hm. rewrite Hsup. apply exec_get_xLPE_S. rewrite Hm. exact Hlpe0. }
    pose proof (fun HL => exec_execute_MRET s_pc newpriv false
                    LprivP HmuP HmcP HnpP Hnpm (Hxlpe _ HL)) as HexecC0.
    match type of HexecC0 with ?A -> _ => assert (HLmenv : A) end.
    { unfold s_pc, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Lmenv. }
    specialize (HexecC0 HLmenv).
    assert (HexecC : exec (execute (MRET tt)) s_pc
            = Some (RETIRE_SUCCESS,
                set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg s_pc mstatus (cms1 ms_cur)) mstatus (cms2 ms_cur))
                  cur_privilege newpriv) mstatus (cms3 ms_cur)) mstatus (cms4 ms_cur))
                  mstatus (cms5 ms_cur))
                  elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (ctgt mepc0))).
    { rewrite LmsP LmepcP in HexecC0. exact HexecC0. }
    (* mirror the physical set_regs on the ghost cells *)
    iMod (reg_update _ mstatus _ (cms1 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms2 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ newpriv with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (cms3 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms4 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms5 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    (* elp: value-preserving physical write, no ghost update *)
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (cms5 ms_cur) (register_set mstatus (cms4 ms_cur)
                (register_set mstatus (cms3 ms_cur) (register_set cur_privilege newpriv
                  (register_set mstatus (cms2 ms_cur) (register_set mstatus (cms1 ms_cur)
                    (register_set nextPC (add_vec_int pc 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (ctgt mepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg s_pc mstatus (cms1 ms_cur)) mstatus (cms2 ms_cur))
              cur_privilege newpriv) mstatus (cms3 ms_cur)) mstatus (cms4 ms_cur))
              mstatus (cms5 ms_cur))
              elp (landing_pad_bits_backwards NO_LP_EXPECTED))
              nextPC (ctgt mepc0)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
               (set_reg s_pc mstatus (cms1 ms_cur)) mstatus (cms2 ms_cur))
               cur_privilege newpriv) mstatus (cms3 ms_cur)) mstatus (cms4 ms_cur))
               mstatus (cms5 ms_cur))
               elp (landing_pad_bits_backwards NO_LP_EXPECTED))
               nextPC (ctgt mepc0)).(sregs)
             = ctgt mepc0)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hpmpc Hmenv [$Hpc' $Hnpc] Hfile Hmepc").
  Qed.

End WpMretGpr.
