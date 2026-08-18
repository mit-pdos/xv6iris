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
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv.
Require Import HartSwp HartLift HartSpan HartSpanChar HartSFrame.
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

End sframes.
