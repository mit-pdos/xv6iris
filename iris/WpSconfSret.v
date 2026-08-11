(* WpSconfSret.v -- [wp_sret_s_sconf], the SIE-ENABLING sret leaf at the
   sconf altitude: the last instruction of kernelvec, and the only one in the
   tree that turns interrupts back on by RESTORING a saved bit rather than by
   writing a known one.

   WHY IT IS A SEPARATE LEAF, NOT AN INSTANCE OF
   [WpSmodePtCtl.wp_sret_gpr_r].
   That one is the raw-cell endpoint: it hands the caller mstatus / privilege /
   sepc / the GPR file back as individual cells and knows nothing about the SIE
   choreography.  Everything this file adds is the choreography -- the four
   ghost pieces the flip has to move, the invariant re-seal, the tie's SPP bit
   changing value, the trap CSRs going back into the arm, and the ARM-DEPENDENT
   stack reserve being handed back.  That is exactly the difference between the
   raw csrsi leaf and [WpSconfCsr.wp_csrsi_sstatus_x0_s_sconf], and this leaf
   is the sret twin of THAT one: same premise set, same four-piece flip, same
   index discipline.  Read them side by side.

   THE THREE THINGS THAT ARE NOT IN THE csrsi TWIN.

   (1) THE NEW SIE VALUE IS NOT A LITERAL.  [csrsi sstatus,2] sets bit 1, so
   its leaf can prove SIE = '1' from bit theory alone.  SRET assigns
   SIE := SPIE, so the '1' has to come from somewhere -- and it comes from the
   caller's [sret_bits] TRAVELLING HALF, pinned at ('1','1').  Agreement with
   [sconf]'s stationary tie ([IntrDefs.sconf_at_sret]) turns that into a fact
   about the live mstatus, whatever the funnel's [∃ ms] happens to name it, and
   [IntrDefs.sret_sconf_flip] carries it through the SRET tower.  This is the
   step that CLOSES the round trip: no bit theory here knows that this SPIE is
   the one the trap saved; the identification is the caller's, carried by that
   half.  The same half is what pins SPP = '1', hence
   [sret_newpriv ms = Supervisor] -- so the privilege write is
   value-preserving and no separate premise is needed.

   (2) THE TIE ACTUALLY MOVES.  Every SIE flip so far left SPP and SPIE alone,
   so [IntrDefs.sret_tie_congr] merely re-expressed the tie at the new mstatus
   with no ghost update.  SRET writes SPP := 0, so here the tie's VALUE changes
   and both halves must be updated together ([IntrDefs.sret_bits_update]) --
   which is only possible because the caller handed the travelling half over.
   The updated copy at ('0','1') goes into [sie_arm true]'s existential, where
   the next trap will find it.

   (3) THE pc MOVES.  The post is at [ret_pc sepc0], not [pc + 4]; a caller
   that restored an aligned epc rewrites it away with its own
   [ret_pc ep = ep].

   THE INDEX DISCIPLINE IS THE ENABLING ONE, and here it is not an accounting
   convention but the literal truth about the stack.  Pre index
   [trap_res true + n], post index [n] at the enabled arm: the handler is
   holding its own now-dead frame reserve ([kv_frame_slots] slots) on top of
   the [n] the interrupted code owned, and it hands back exactly the [n],
   because [sie_cap]'s enabled arm re-reserves the frame for the NEXT trap.
   Both sides are [kv_frame_slots + n] after the carve, so the stack conjunct
   is untouched -- [iExact] closes it with no arithmetic, exactly as in the
   csrsi twin.

   THE ARM INDEX IS PINNED TO [false].  A trap handler runs with SIE = 0 by
   construction (that is what taking the trap did), so there is no [b] to
   generalize over and no impossible-arm branch to refute -- one of the seven
   leaves that went the same way in the [b := false] slice. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpMmodeLeafBase.
Require Import MstatusBits.
(* [exec_execute_SRET_menv] -- the SRET reduction with the get_xLPE premise
   pinned by the menvcfg VALUE, which is what [sconf] gives us. *)
Require Import WpSmodeSret.
Require Import IntrDefs WpSmodeIntr.
Import Defs.
Local Open Scope Z_scope.

Section WpSconfSret.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {p : mword 64}.

  Lemma wp_sret_s_sconf
      (pc : mword 64)
      (m : regfile) (n : nat) (sepc0 : mword 64) :
    sie_cap_gpr m (trap_res true + n)%nat false p -∗
    (* THE TRAVELLING TIE, at the values a trap taken from S-mode with
       interrupts enabled left behind.  This is what makes the sret's SIE
       land on '1' and its privilege land on Supervisor -- see (1) above. *)
    sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
    intr_count 1 true -∗
    (* the trap CSRs: sepc at the NAMED value the handler restored (the sret
       reads it), the other two at whatever this hart's trap left. *)
    sepc ↦ᵣ sepc0 -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    cpu_cells 0 true p -∗
    cpu_claim p -∗
    pc_is pc -∗
    instr pc false (SRET tt) -∗
    ( sie_cap_gpr m n true p -∗
      pc_is (ret_pc sepc0) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hmir Hcnt Hsepc Hscausex Hstvalx Hcells Hclm Hpc Hinstr Hcont".
    iDestruct "Hcnt" as "[Htok Hhx]".
    iApply (wp_instr_s_sconf m (trap_res true + n)%nat false pc false (SRET tt)
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %Hpbmte & %Hpmm & %Hlpeb & %Hfiom & %Hmenvval)".
    subst menvcfg0.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    (* ---- THE TWO sret BITS, read off the bundle by ghost agreement.  The
         funnel's [∃ ms] named the live mstatus [ms0]; the travelling half is
         about the same two fields, so this is where ('1','1') becomes a fact
         about [ms0]. ---- *)
    iDestruct (sret_bits_agree _ _ _ _ with "Hspp Hmir") as %[Hspp0 Hspie0].
    destruct (sret_sconf_flip ms0 Hmsf Hspie0) as (Hsie' & Hsppf & Hspief & Hmsf').
    (* re-state the stationary tie at the LITERALS, so the joint update below
       has something to match -- see [IntrDefs.sret_tie_vals] for why this is a
       lemma and not a rewrite. *)
    iDestruct (sret_tie_vals ms0 _ _ Hspp0 Hspie0 with "Hspp") as "Hspp".
    (* SPP = '1' decodes the privilege to Supervisor, so the cur_privilege
       write is value-preserving and needs no premise of its own. *)
    assert (Hsup : sret_newpriv ms0 = Supervisor).
    { unfold sret_newpriv. rewrite sret_ms2_SPP Hspp0. vm_compute. reflexivity. }
    assert (Hlpe0 : _get_MEnvcfg_LPE MENVCFG_S = ('b"0"))
      by (apply bv_eq; vm_compute; reflexivity).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hsepc") as %Lsepc.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    (* tick nextPC := pc+4 (SRET is a 4-byte instruction) *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_spc : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lsepc_spc : register_lookup sepc s_pc.(sregs) = sepc0)
      by (unfold s_pc; tmig; exact Lsepc).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* ---- the SRET execute reduction at [s_pc], with lpe = false ---- *)
    assert (Hxlpe : forall sz : mstate,
              register_lookup menvcfg sz.(sregs) = MENVCFG_S ->
              exec (get_xLPE (sret_newpriv ms0)) sz = Some (false, sz)).
    { intros sz Hm. rewrite Hsup. apply exec_get_xLPE_S. rewrite Hm. exact Hlpe0. }
    pose proof (exec_execute_SRET_menv s_pc false MENVCFG_S
                  Lpriv_spc
                  ltac:(rewrite Lmisa_spc; exact HmisaS)
                  ltac:(rewrite Lms_spc;
                        exact (proj1 (proj2 (proj2 (proj2 Hmsf)))))
                  ltac:(rewrite Lmisa_spc; exact HmisaC)
                  Lmenv_spc
                  ltac:(intros sz Hm;
                        pose proof (Hxlpe sz Hm) as Hx;
                        unfold sret_newpriv, sret_ms2, sret_ms1 in Hx;
                        rewrite Lms_spc; exact Hx)) as HexecC0.
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 ms0)) mstatus (sret_ms2 ms0))
                           cur_privilege Supervisor) mstatus (sret_ms3 ms0)) mstatus (sret_ms4 ms0))
                  mstatus (sret_ms5 ms0)) elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (ret_pc sepc0)).
    assert (HexecC : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite HexecC0. unfold sX.
      rewrite !Lms_spc Lsepc_spc.
      unfold sret_newpriv, sret_ms2, sret_ms1 in Hsup.
      unfold sret_ms1, sret_ms2, sret_ms3, sret_ms4, sret_ms5, ret_pc.
      rewrite Hsup. reflexivity. }
    (* ---- THE FOUR-PIECE FLIP.  Identical to the csrsi restore: the bundle's
         tied half, the capability eighth (the whole of [sie_arm false]), the
         count eighth the caller brought, and the invariant quarter. ---- *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hhx" as (handler) "[#Hintr #Hspec]".
    iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
    iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & _)".
    iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi") as "(Hhalf & Hqcap & Hqcnt & Hqi)".
    iMod ("Hclose" with "[Hqi Hstv]") as "_".
    { iNext. iExists ('b"1" : mword 1). iFrame "Hqi Hstv".
      iModIntro. iIntros "%Hb". iExact "Hspec". }
    (* ---- THE TIE MOVES: ('1','1') -> ('0','1') on BOTH halves at once. ---- *)
    iMod (sret_bits_update ('b"1") ('b"1") ('b"1") ('b"1") ('b"0") ('b"1")
            with "Hspp Hmir") as "[Hspp Hmir]".
    (* ---- mirror the physical set_regs on the ghost cells ---- *)
    iMod (reg_update _ mstatus _ (sret_ms1 ms0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms2 ms0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (sret_ms3 ms0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms4 ms0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (sret_ms5 ms0) with "Hreg Hms") as "[Hreg Hms]".
    (* elp's write is VALUE-PRESERVING ([hw_config] pins it persistently at
       NO_LP_EXPECTED), so it is absorbed with no ghost update. *)
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (sret_ms5 ms0) (register_set mstatus (sret_ms4 ms0)
                (register_set mstatus (sret_ms3 ms0) (register_set cur_privilege Supervisor
                  (register_set mstatus (sret_ms2 ms0) (register_set mstatus (sret_ms1 ms0)
                    (register_set nextPC (add_vec_int pc 4) σ.(sregs))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat tmig. rewrite Lelp Help0. reflexivity. }
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (ret_pc sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists sX.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact HexecC. }
    iSplitL "Hreg Hmem".
    { unfold sX, s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC sX.(sregs) = ret_pc sepc0)
      by (unfold sX; rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite -Hsie') in "Hhalf".
    (* the new tie sits at exactly the two constants SRET wrote *)
    iAssert (sret_tie (sret_ms5 ms0)) with "[Hspp]" as "Hspp".
    { rewrite /sret_tie Hsppf Hspief. iExact "Hspp". }
    (* ... and the arm holds the travelling half at an EXISTENTIAL value, so
       pack the three named cells before rebuilding the capability. *)
    iAssert (∃ v : mword 64, sepc ↦ᵣ v)%I with "[Hsepc]" as "Hsepcx".
    { iExists sepc0. iExact "Hsepc". }
    iAssert (∃ a b : mword 1, sret_bits a b)%I with "[Hmir]" as "Hsppc".
    { iExists ('b"0"), ('b"1"). iExact "Hmir". }
    (* ---- rebuild the ENABLED capability.  The carve is identical on both
         sides -- [trap_res false + (trap_res true + n)] going in,
         [trap_res true + n] coming out, both [kv_frame_slots + n] by
         conversion -- so [iExact] closes the stack with no arithmetic. ---- *)
    iAssert (sie_cap m n true p)
      with "[Hqcap Hqcnt Hsepcx Hscausex Hstvalx Hsppc Hclm Hstk Htr Hcells]" as "Hcap".
    { iSplitL "Hstk". { iExact "Hstk". }
      iFrame "Htr".
      iFrame "Hqcap Hsepcx Hscausex Hstvalx Hsppc Hclm".
      iSplitR "Hcells Hqcnt".
      { iExists handler. iSplit; [iPureIntro; exact Htvd |].
        iSplit; [iPureIntro; exact Hsb |]. iExact "Hinv_i". }
      (* [cpu_hart 0 true p] -- the cells the caller handed in, plus the count
         eighth the flip just produced at '1'. *)
      iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists (sret_ms5 ms0). iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf'. }
      iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
      split; [exact Hpbmte |]. split; [exact Hpmm |]. split; [exact Hlpeb |].
      split; [exact Hfiom | reflexivity]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

End WpSconfSret.
