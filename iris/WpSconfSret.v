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
Require Import InstrBytes.
Require Import SmodeCore WpMmodeLeafBase.
Require Import MstatusBits.
(* [exec_execute_SRET_menv] -- the SRET reduction with the get_xLPE premise
   pinned by the menvcfg VALUE, which is what [sconf] gives us. *)
(* [wp_next_off_intro] -- this leaf is pinned to [b = false], so the funnel's
   hart-generic callback is discharged by wp_next's own introduction rule.
   (The dead-import sweep removed WpNext while the leaf did not yet consume
   the funnel through [wp_next]; it does now.) *)
Require Import WpNext.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
(* the SRET execute walk at the node layer (sweep D) and the S-mode CSR
   frame kit it shares with the rest of the sconf tier *)
Require Import WpSmodePtEngine HartSCsr HartSwp HartMFrame HartLift HartSpan
        HartSpanChar HartRegNode HartMCycle HartGoodb WpDecodeBridge.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

Section WpSconfSret.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {p : mword 64}.

  Context {kt : ktier}.
  Lemma wp_sret_s_sconf
      (pc : mword 64)
      (m : regfile) (n : nat) (sepc0 : mword 64) :
    sie_cap_gpr kt m (trap_res true + n)%nat false p -∗
    (* THE TRAVELLING TIE, at the values a trap taken from S-mode with
       interrupts enabled left behind.  This is what makes the sret's SIE
       land on '1' and its privilege land on Supervisor -- see (1) above. *)
    sret_bits ('b"1" : mword 1) ('b"1" : mword 1) -∗
    intr_count 1 true -∗
    (* the trap CSRs: sepc at the NAMED value the handler restored (the sret
       reads it), the other two at whatever this hart's trap left.  They are
       threaded PIECEWISE rather than as the folded [trap_csrs], because sepc
       is pinned -- so [intr_res], the bundle's fifth member, is its own
       premise here.  It is the slot [intr_handler_avail] used to occupy,
       inside [intr_count 1 true]; the difference that matters is that the
       contract now arrives ATTACHED to the very stvec cell this sret's flip
       re-forms, so the two cannot be about different vectors. *)
    sepc ↦ᵣ sepc0 -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    intr_res kt -∗
    (* THE KPT RECEIPT, [trap_csrs]' sixth member (IntrDefs §6b), piecewise
       here like the rest.  This leaf RE-ENABLES interrupts, so it is exactly
       the place that has to show the kernel table is installed -- the arm it
       builds carries the receipt, and nothing can reach [b = true] without
       one.  A caller has it from its own [intr_off], which is where the
       matching csrci put it. *)
    kpt_on cpu_id -∗
    (* ∅, NOT a threaded set: sret re-enables interrupts, and the enabled arm
       carries [lks = ∅] ([CpuOwn.cpu_own_on]).  So "you may only turn
       interrupts back on holding no spinlock" is enforced HERE, at the one
       instruction that does it. *)
    cpu_priv 0 true p ∅ -∗
    cpu_claim p -∗
    pc_is pc -∗
    instr pc false (SRET tt) -∗
    ( sie_cap_gpr kt m n true p -∗
      pc_is (ret_pc sepc0) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hmir Htok Hsepc Hscausex Hstvalx Hhx Hkptr Hcells Hclm Hpc
             Hinstr Hcont".
    (* THE ARM MOVES, [false] in and [true] out -- the generalized obligation's
       second index -- and the landing mstatus is NAMED ([sret_ms5 ms0]), which
       is the other half of the same generalization. *)
    iApply (wp_instr_s_sconf m (trap_res true + n)%nat false true pc false
              (SRET tt)
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = ret_pc sepc0⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝)%I
              with "Hcg Hpc Hinstr
                    [Hmir Htok Hsepc Hscausex Hstvalx Hhx Hkptr Hcells Hclm
                     Hcont]").
    (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic callback
       is discharged at the ambient hart and nothing is renamed. *)
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      pose proof (mword1_not_lp elp0 Help_np) as Help0. subst elp0.
      (* ---- THE TWO sret BITS, read off the bundle by ghost agreement.  The
           obligation's [∃ ms] named the live mstatus [ms0]; the travelling
           half is about the same two fields, so this is where ('1','1')
           becomes a fact about [ms0]. ---- *)
      iDestruct (sret_bits_agree _ _ _ _ with "Hspp Hmir") as %[Hspp0 Hspie0].
      destruct (sret_sconf_flip ms0 Hmsf Hspie0)
        as (Hsie' & Hsppf & Hspief & Hmsf').
      (* re-state the stationary tie at the LITERALS, so the joint update below
         has something to match -- [IntrDefs.sret_tie_vals]. *)
      iDestruct (sret_tie_vals ms0 _ _ Hspp0 Hspie0 with "Hspp") as "Hspp".
      (* SPP = '1' decodes the privilege to Supervisor, so the cur_privilege
         write is value-preserving and needs no premise of its own. *)
      assert (Hsup : sret_newpriv ms0 = Supervisor).
      { unfold sret_newpriv. rewrite sret_ms2_SPP Hspp0. vm_compute. reflexivity. }
      assert (Hlpe0 : _get_MEnvcfg_LPE MENVCFG_S = ('b"0"))
        by (apply bv_eq; vm_compute; reflexivity).
      pose proof Hmsf as (_ & _ & _ & HTSR & _).
      iDestruct (sret_frames_in ms0 Supervisor (add_vec_int pc 4) MENVCFG_S
                   sepc0 with "Hms Hpriv HnPC Hmisa Hmenv Hsepc") as "[Hrw Hro]".
      (* ---- THE FOUR-PIECE FLIP happens in the swp's POST, where the new
           mstatus is already installed; the ghost updates are [bupd]s, and
           [HartSwp.swp_fupd_post] is what lets them run there. ---- *)
      iApply swp_fupd_post.
      iApply (swp_mono with
                "[Hcap Hmir Htok Hhalf Hspp Hhx Hkptr Hscausex Hstvalx Hcells
                  Hclm Hmie Hmdl HPC Hresv Hfile] [Hrw Hro]");
        [| iApply (swp_execute_SRET_S ms0 (add_vec_int pc 4) MENVCFG_S sepc0
                     HTSR Hsup Hlpe0 with "Hcert Help Hrw Hro") ].
      iIntros (e) "(-> & Hrw & Hro)".
      iDestruct (sret_frames_out (sret_ms5 ms0) Supervisor (ret_pc sepc0)
                   MENVCFG_S sepc0 with "[$Hrw $Hro]")
        as "(Hms & Hpriv & HnPC & _ & Hmenv & Hsepc)".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iEval (rewrite /intr_res) in "Hhx".
      iDestruct "Hhx" as (handler vb) "(%Htvd & %Hsb & Hqi & Hstv & #Hspec)".
      iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi")
        as "(Hhalf & Hqcap & Hqcnt & Hqi)".
      iDestruct (intr_res_intro handler _ Htvd Hsb with "Hqi Hstv Hspec")
        as "Hintr".
      (* ---- THE TIE MOVES: ('1','1') -> ('0','1') on BOTH halves at once. *)
      iMod (sret_bits_update ('b"1") ('b"1") ('b"1") ('b"1") ('b"0") ('b"1")
              with "Hspp Hmir") as "[Hspp Hmir]".
      iModIntro.
      iEval (rewrite -Hsie') in "Hhalf".
      (* the new tie sits at exactly the two constants SRET wrote *)
      iAssert (sret_tie (sret_ms5 ms0)) with "[Hspp]" as "Hspp".
      { rewrite /sret_tie Hsppf Hspief. iExact "Hspp". }
      (* the arm holds the travelling half and sepc at EXISTENTIAL values *)
      iAssert (∃ v : mword 64, sepc ↦ᵣ v)%I with "[Hsepc]" as "Hsepcx".
      { iExists sepc0. iExact "Hsepc". }
      iAssert (∃ a b : mword 1, sret_bits a b)%I with "[Hmir]" as "Hsppc".
      { iExists ('b"0"), ('b"1"). iExact "Hmir". }
      iSplitR; [done|].
      iExists (ret_pc sepc0), (sret_ms5 ms0), m, n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        iPureIntro. split; [exact Hmsf' | exact Hmm]. }
      (* ---- rebuild the ENABLED capability.  The carve is identical on both
           sides -- [trap_res false + (trap_res true + n)] going in,
           [trap_res true + n] coming out, both [kv_frame_slots + n] by
           conversion -- so [iExact] closes the stack with no arithmetic. *)
      iSplitL "Hqcap Hqcnt Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm
               Hstk Htr Hcells".
      { iSplitL "Hstk". { iExact "Hstk". }
        iFrame "Htr Hwit".
        iFrame "Hqcap Hintr Hkptr Hsepcx Hscausex Hstvalx Hsppc Hclm".
        iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
      iSplitL "Hfile". { iExact "Hfile". }
      iSplitR; [done|]. iSplitR; [done|]. done.
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" with "Hcg' Hpc'").
  Qed.

End WpSconfSret.
