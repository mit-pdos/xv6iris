(* WpSFrames.v -- the S-mode BUNDLE ⇄ FRAMES bridge.

   [InstrBytes.mm_frames_intro] / [_elim] is the M-mode twin, and this is the
   same job one mode over: it is the ONLY place the S-mode resource algebra is
   touched.  Above it, everything speaks in frames ([HartSFrame.s_rs] and its
   footprint); below it, everything speaks in the kernel's bundles.

   FOUR OWNERS, and between them they cover the tower exactly:

     [sconf]                 cur_privilege (Supervisor), mstatus, mie,
                             mideleg, menvcfg -- and [hw_config] with the
                             pinned misa / mseccfg / pma_regions / htif /
                             elp / senvcfg inside it
     [pc_is]                 PC, nextPC, minstret, minstret_increment,
                             mcountinhibit, minstretcfg, mcycle, mtime, mip
     [KptShare.tlb_res_pt]   satp and tlb -- the two cells M-mode does not
                             have -- plus [pmp_config] (pmpcfg_n, pmpaddr_n)
     [hart_state ↦ᵣ]         handed in separately, as the M-mode twin does

   WHAT COMES BACK OUT UNUSED is as important as what goes in: the mstatus
   SIE ghost and [sret_tie], [tlb_snap_ok], [kpt_inv] and [minstret_inv] are
   not cells and cannot ride in a frame, so they are returned to the caller
   untouched.  [tlb_snap_ok] is what a later TLB HIT needs (it says the entry
   found is legitimate for the installed tree) and [kpt_inv] is what a MISS
   needs (it supplies the PTE reads), so both must survive the round trip
   rather than be consumed here. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv.
Require Import HartSwp HartLift HartSpan HartSpanChar HartSFrame.
Require Import HartMCycle.
Require Import SmodeCore.
Require Import InstrBytes IntrDefs KptShare SmodePte.
Local Open Scope Z_scope.

Section sframes.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma s_frames_intro (pc : mword 64) (root_ppn : mword 44) :
    hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf -∗ pc_is pc -∗
    tlb_res_pt root_ppn -∗
    hw_config ∗ minstret_inv ∗
    ∃ (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv : type_of_register tlb),
      (* the facts the walk and the dispatch will ask for, at the SAME values
         the tower carries -- so no consumer reconciles two sets of
         existentials, exactly as [mm_frames_intro] arranges it *)
      ⌜ sconf_ms_facts mst0 ⌝ ∗
      ⌜ and_vec MIE_S (not_vec mdv0) = zeros' 64 ⌝ ∗
      ⌜ menv0 = MENVCFG_S ⌝ ∗
      ⌜ eq_vec (_get_MEnvcfg_PBMTE menv0) ('b"0") = true ⌝ ∗
      ⌜ misa0 = MISA_C ⌝ ∗
      ⌜ pma_allows_all pmar0 ⌝ ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16
          (satp_to_asid (autocast (T := mword) satp0 : mword 64))
        = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword)
          (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      (* the frames *)
      hreg_frame (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
        s_Drw ∗
      hreg_frame_ro (s_Df (DfracOwn 1))
        (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
           mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv) s_Dro ∗
      (* ...and everything that is NOT a cell, back untouched *)
      ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗
      sret_tie mst0 ∗
      tlb_snap_ok tlbv ∗
      kpt_inv root_ppn.
  Proof.
    iIntros "Hhs Hsc Hpc Htlb".
    iDestruct "Hsc" as "(#Hhw & #Hmi_inv & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mst0) "(Hmstatus & Hsie & Hsret & %Hmsf)".
    iDestruct "Hmie" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenv" as (menv0)
      "(Hmenvc & %HPBMTE & %HPMM & %HLPE & %HFIOM & %Hmenvval)".
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr)".
    iDestruct "Hmr" as (ms bmi mc micfg) "(Hms & Hmi & #Hmc & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
    iDestruct "Htlb" as (satp0 tlbv)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlbc & Hsnap & Hpmp & Hkpt)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
        %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
        %Hmisaval & %Hsecval & _)".
    iFrame "Hhw Hmi_inv".
    iExists ms, bmi, cy, ti, ip, mst0, mc, micfg, misa0, mseccfg0,
            (mword_of_int 0 : mword 64), pmar0, elp0, satp0, mdv0, menv0,
            pcfg, paddr, tlbv.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip Htlbc".
    - rewrite s_rw_split.
      rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
        s_rs_tlb. iFrame.
    - iSplitL "Hpriv Hmstatus Hhs Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenvc".
      + rewrite s_ro_split.
        rewrite s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
          s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp
          s_rs_senv s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
        iFrame "Hpriv Hmstatus Hhs Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenvc".
        by iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv".
      + iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ...and back.  [InstrBytes.mm_frames_elim]'s twin.  The non-cell       *)
  (* resources come back IN (they never rode in the frames), and the two    *)
  (* files may differ: the fetch may have filled the TLB, so [tlbv'] is a   *)
  (* fresh parameter and it is [tlb_snap_ok tlbv'] the caller owes -- which *)
  (* is precisely what the fill's own rule must re-establish.               *)
  (* ------------------------------------------------------------------ *)
  Lemma s_frames_elim (npc : mword 64) (root_ppn : mword 44)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv : type_of_register tlb) :
    sconf_ms_facts mst0 ->
    and_vec MIE_S (not_vec mdv0) = zeros' 64 ->
    menv0 = MENVCFG_S ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    autocast (T := mword)
      (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    hw_config -∗ minstret_inv -∗
    hreg_frame (s_rs npc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
      s_Drw -∗
    hreg_frame_ro (s_Df (DfracOwn 1))
      (s_rs npc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv) s_Dro -∗
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) -∗
    sret_tie mst0 -∗
    tlb_snap_ok tlbv -∗
    kpt_inv root_ppn -∗
    hart_state ↦ᵣ HART_ACTIVE tt ∗ sconf ∗ pc_is npc ∗ tlb_res_pt root_ppn.
  Proof.
    intros Hmsf Hmm Hmenvval Hmode Hasid Hppn HA Hord HX HW HR Hcov.
    iIntros "#Hhw #Hmi_inv Hrw Hro Hsie Hsret Hsnap Hkpt".
    rewrite s_rw_split s_ro_split.
    rewrite s_rs_PC s_rs_nPC s_rs_ms s_rs_mi s_rs_cy s_rs_ti s_rs_ip
      s_rs_tlb.
    rewrite s_rs_priv s_rs_mst s_rs_hart s_rs_pcfg s_rs_paddr s_rs_mc
      s_rs_micfg s_rs_misa s_rs_sec s_rs_pma s_rs_htif s_rs_elp s_rs_senv
      s_rs_satp s_rs_mie s_rs_mdl s_rs_menv.
    iDestruct "Hrw" as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc)".
    iDestruct "Hro" as "(Hpriv & Hmst & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg &
                         #Hmisa & #Hsec & #Hpma & #Hhtif & #Help & #Hsenv &
                         Hsatp & Hmie & Hmdl & Hmenvc)".
    iFrame "Hhs".
    iSplitL "Hpriv Hmst Hsie Hsret Hmie Hmdl Hmenvc".
    { iFrame "Hhw Hmi_inv Hpriv".
      iSplitL "Hmst Hsie Hsret".
      { iExists mst0. by iFrame "Hmst Hsie Hsret". }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. by iFrame "Hmie Hmdl". }
      iExists menv0. iFrame "Hmenvc". subst menv0.
      iPureIntro. split_and!; vm_compute; reflexivity. }
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
    { iFrame "HPC HnPC".
      iSplitL "Hms Hmi".
      { iExists ms, bmi, mc, micfg. by iFrame "Hms Hmi Hmc Hmicfg". }
      iExists cy, ti, ip. by iFrame. }
    iExists satp0, tlbv. iFrame "Hsatp Htlbc Hsnap Hkpt".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iExists pcfg, paddr. by iFrame "Hpcfg Hpaddr".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The two tower transports the cycle rule consumes, [InstrBytes]'s      *)
  (* [mm_tick_agree] / [mm_pre_agree] one for one.  Each is ONE            *)
  (* [s_rs_agree] application, so the 25-way set reasoning is paid here     *)
  (* rather than inside the wrapper's arms.                                *)
  (* ------------------------------------------------------------------ *)

  (* the tail: [wrap_post] commits nextPC into PC and sets minstret, then the
     tick moves mcycle/mtime/mip -- which is exactly what the [∖ tk_clock3]
     in the incoming agreement leaves unpinned *)
  Lemma s_tick_agree (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) (tlbv : type_of_register tlb)
      (mi : mword 64) (rs : regstate) :
    reg_agree_on ((s_Drw ∪ s_Dro) ∖ tk_clock3) rs
      (wrap_post (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                    mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) mi) ->
    reg_agree_on (s_Drw ∪ s_Dro) rs
      (s_rs npc npc mi bmi
         (register_lookup (R_bitvector_64 mcycle) rs)
         (register_lookup (R_bitvector_64 mtime) rs)
         (register_lookup (R_bitvector_64 mip) rs)
         mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
         satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    intros Hag. apply s_rs_agree.
    all: try reflexivity.
    all: (etransitivity;
          [ apply Hag; rewrite /s_Drw /s_Dro /tk_clock3; set_solver | ]).
    all: try (by rewrite wrap_post_PC s_rs_nPC).
    all: try (by rewrite wrap_post_ms).
    all: rewrite wrap_post_other;
      [| vm_compute; reflexivity | vm_compute; reflexivity ].
    all: by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
              ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.

  (* the head: [wrap_pre] overwrites minstret_increment and nothing else *)
  Lemma s_pre_agree (pc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) (tlbv : type_of_register tlb) :
    reg_agree_on (s_Drw ∪ s_Dro)
      (wrap_pre (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv))
      (s_rs pc pc ms
         (minstret_inc_flag mc micfg Supervisor)
         cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
         satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    apply s_rs_agree.
    all: try (rewrite wrap_pre_mi;
              by rewrite s_rs_mc s_rs_micfg s_rs_priv).
    all: try (rewrite wrap_pre_other; [| vm_compute; reflexivity ]).
    all: by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_cy ?s_rs_ti ?s_rs_ip
              ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
              ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec
              ?s_rs_pma ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp
              ?s_rs_mie ?s_rs_mdl ?s_rs_menv.
  Qed.


  (* ==================================================================== *)
  (* s_cycle -- THE S-MODE INSTANCE of [swp_exec_step_decode_execute].      *)
  (*                                                                      *)
  (* [WpInstr.mm_cycle]'s twin, and its header predicted exactly this: the *)
  (* S-mode wrapper writes its own thirty-line twin of THAT rule and reuses *)
  (* the generic one unchanged.  So it does.  Everything about the cycle    *)
  (* -- boundary, interrupt check, minstret, tick, PC commit -- is in the  *)
  (* generic rule, which knows nothing about privilege regimes; all this   *)
  (* adds is the two bundle<->frame bridges above.                         *)
  (* ==================================================================== *)
  Local Ltac srs :=
    by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
       ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
       ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
       ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
       ?s_rs_menv.

  Lemma s_cycle (pc npc : mword 64) (root_ppn : mword 44) (Psi : iProp Σ)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv tlbv' : type_of_register tlb) :
    sconf_ms_facts mst0 ->
    and_vec MIE_S (not_vec mdv0) = zeros' 64 ->
    menv0 = MENVCFG_S ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    autocast (T := mword)
      (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    hw_config -∗ minstret_inv -∗
    hreg_frame (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
      s_Drw -∗
    hreg_frame_ro (s_Df (DfracOwn 1))
      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv) s_Dro -∗
    (* the body, at the prelude's file: the flag the prelude wrote, computed
       AT SUPERVISOR -- which is only sayable because [minstret_inc_flag]
       takes the privilege *)
    (hreg_frame (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
                   cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                   pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv) s_Drw -∗
     hreg_frame_ro (s_Df (DfracOwn 1))
       (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
          cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
          pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv) s_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ w : mword 32,
            ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
            hreg_frame (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor)
                          cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
                          senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv')
              s_Drw ∗
            hreg_frame_ro (s_Df (DfracOwn 1))
              (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor)
                 cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv') s_Dro ∗ Psi)) -∗
    (* what the bridge could not carry, back in for the rebuild *)
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) -∗
    sret_tie mst0 -∗
    tlb_snap_ok tlbv' -∗
    kpt_inv root_ppn -∗
    ▷ (hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf -∗ pc_is npc -∗
       tlb_res_pt root_ppn -∗ Psi -∗ WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmsf Hmm Hmenvval Hmode Hasid Hppn HA Hord HX HW HR Hcov.
    iIntros "#Hhw #Hmi_inv Hrw Hro Hbody Hsie Hsret Hsnap Hkpt Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (swp_exec_step_decode_execute s_Drw s_Dro (s_Df (DfracOwn 1))
              (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
              (s_rs pc pc ms (minstret_inc_flag mc micfg Supervisor)
                 cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
              (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor)
                 cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv') Psi
              s_disj s_w_cy s_w_ti s_w_ip s_in_priv s_in_hart s_in_mc
              s_in_micfg s_w_mi s_in_mi s_w_ms s_in_ms s_w_PC s_in_PC
              s_in_nPC ltac:(srs) ltac:(srs) ltac:(srs)
              (s_pre_agree pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv)
              with "Hcert Hrw Hro Hbody [Hcont Hsie Hsret Hsnap Hkpt]").
    iNext. iIntros (rs3) "%Hag Hrw Hro HPsi".
    destruct Hag as (mi & Hag).
    pose proof (s_tick_agree pc npc ms (minstret_inc_flag mc micfg Supervisor)
                  cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0
                  pmar0 elp0 satp0 MIE_S mdv0 menv0 tlbv' mi rs3 Hag) as Hag'.
    iDestruct (s_rw_ext _ _ Hag' with "Hrw") as "Hrw".
    iDestruct (s_ro_ext (DfracOwn 1) _ _ Hag' with "Hro") as "Hro".
    iDestruct (s_frames_elim npc root_ppn mi
                 (minstret_inc_flag mc micfg Supervisor) _ _ _ mst0 mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mdv0 menv0 pcfg paddr
                 tlbv' Hmsf Hmm Hmenvval Hmode Hasid Hppn HA Hord HX HW HR
                 Hcov with "Hhw Hmi_inv Hrw Hro Hsie Hsret Hsnap Hkpt")
      as "(Hhs & Hsc & Hpc & Htlb)".
    iApply ("Hcont" with "Hhs Hsc Hpc Htlb HPsi").
  Qed.


End sframes.
