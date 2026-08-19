(* WpSmodePtFetch.v -- THE FETCH TRANSLATION A REGIME-GENERIC LEAF PAYS.

   [SmodeCorePt]'s five S-mode wrappers take the fetch translation as a
   premise, spelled [spt_fetch_tr], and hand it straight up to their caller.
   [SmodeCorePt.spt_tr_obl_of_regime] produces the underlying [spt_tr_obl]
   -- but at a NAMED tower, and its first premise is [misa0 = MISA_C], while
   [spt_fetch_tr] ∀-quantifies misa and every other tower component a caller
   cannot name.  So the producer does not apply from outside the box.

   IT APPLIES FROM INSIDE, and that is the whole of this file.  The box's own
   body hands the caller [hreg_frame_ro (s_Df_mix dq) (srs tv) s_Dro], whose
   misa and pma_regions cells sit at [DfracDiscarded], and [hw_config] pins
   both -- so two [InstrBytes.reg_pointsto_agree]s under the box turn the
   ∀-bound components into the literals the producer and the regime's own
   side condition want.

   Everything else is now a FIELD of [s_regime] (the swp fold, SRegime.v):
   [sr_adm_of_pin] turns the text datum's tier pin into the regime's
   admissibility, and [sr_swp_side_ok] turns the pure config facts a leaf
   already carries into the regime's side condition.  So this lemma's premise
   list is pure config -- no regime-specific fact at all -- which is what
   makes a leaf stated over [forall (R : s_regime)] able to discharge it. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile WpGpr InstrBytes MinstretInv.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame WpDecodeBridge.
Require Import WpSmodePtEngine.
Require Import Ktier CommonWalk.
Require Import HartMCycle WpSFrames.
Require Import SmodeCore SRegime KptShare SmodeCorePt.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* the walk's reference footprint: exactly the two cells [sr_swp_side_ok]
   asks the caller to have declared (mstatus for SXL, satp for the mode) *)
Definition spf_Db (r : register) : bool :=
  orb (register_beq r (mstatus : register)) (register_beq r (satp : register)).

Lemma spf_Db_in (r : register) : spf_Db r = true -> r ∈ s_Drw ∪ s_Dro.
Proof.
  unfold spf_Db. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact s_in_mst | exact s_in_satp].
Qed.

Lemma spf_Db_mst : spf_Db mstatus = true.
Proof. unfold spf_Db. vm_compute. reflexivity. Qed.

Lemma spf_Db_satp : spf_Db satp = true.
Proof. unfold spf_Db. vm_compute. reflexivity. Qed.

Lemma spf_leafchk_in (r : register) : D_leafchk r = true -> r ∈ s_Drw ∪ s_Dro.
Proof.
  unfold D_leafchk. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact s_in_misa | exact s_in_menv].
Qed.

(* the same two at ANY conforming write set -- what the Bare arm's fetch
   producer needs.  [s_frame_ok] is exactly the contract that makes them
   hold: [sf_in_mst] / [sf_in_satp] / [sf_in_misa] / [sf_in_menv]. *)
Lemma spf_Db_in_D (SD : gset register) (HSD : s_frame_ok SD) (r : register) :
  spf_Db r = true -> r ∈ SD ∪ s_Dro.
Proof.
  unfold spf_Db. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact (sf_in_mst SD HSD) | exact (sf_in_satp SD HSD)].
Qed.

Lemma spf_leafchk_in_D (SD : gset register) (HSD : s_frame_ok SD)
    (r : register) :
  D_leafchk r = true -> r ∈ SD ∪ s_Dro.
Proof.
  unfold D_leafchk. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact (sf_in_misa SD HSD) | exact (sf_in_menv SD HSD)].
Qed.

Section SPtFetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma spt_fetch_tr_of_regime (R : s_regime) (dq : dfrac)
      (pc mst0 satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    hw_config -∗
    spt_fetch_tr (s_Df_mix dq) (sr_swp_res_at R satp0) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok.
    iIntros "#Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /spt_fetch_tr.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    rewrite /spt_tr_obl.
    iModIntro.
    iIntros (va ppn tv rr) "%Hlt %Hpin #Hat Hfrag HRes Hrw Hro".
    (* THE TWO FACTS THE ∀ HID, read off the frame the box was handed and the
       persistent pins [hw_config] carries. *)
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (spt_tr_obl_of_regime R (s_Df_mix dq) spf_Db pc ms bmi cy ti ip
                 mst0 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0
                 satp0 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV spf_Db_in
                 spf_leafchk_in spf_Db_mst spf_Db_satp Hsatpok Hpmpok
                 (pma_all_ram Hpma) with "Hcert") as "#Hobl".
    iApply ("Hobl" $! va ppn tv rr with "[%] [%] Hat Hfrag HRes Hrw Hro");
      [ exact Hlt | exact Hpin ].
  Qed.

  (* THE BARE ARM'S FETCH PRODUCER.  [spt_fetch_tr_of_regime] above pays
     [sr_swp_side_ok], whose [tlb ∈ Drw] the Bare write set cannot meet; this
     one takes the arm's own side-condition INTRODUCTION instead -- exactly
     the conjunct [SRegime.sr_slot_acc]'s Bare disjunct hands out -- plus the
     satp fact it comes with. *)
  Lemma spt_fetch_tr_of_regime_b (R : s_regime) (dq : dfrac)
      (pc mst0 satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    bare_satp_ok satp0 ->
    (forall (acc : MemoryAccessType mem_payload)
            (va : SailStdpp.Values.mword 64)
            (ppn : SailStdpp.Values.mword 44) (kp : kperm)
            (Db : register -> bool) (Drw Dro : gset register)
            (rs : regstate) (dst : mstate),
       s_acc_ok acc ->
       bare_satp_ok (register_lookup satp rs) ->
       eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs)) ('b"1")
         = false ->
       sr_swp_side R acc va ppn kp Db Drw Dro rs dst) ->
    hw_config -∗
    spt_fetch_tr_b (s_Df_mix dq) (sr_swp_res_at R satp0) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok Hbare Hbside.
    iIntros "#Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /spt_fetch_tr_b.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    iModIntro.
    iIntros (va ppn tv rr) "%Hlt %Hpin #Hat Hfrag HRes Hrw Hro".
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (spt_tr_obl_of_regime_D s_Drwb s_frame_ok_Drwb R (s_Df_mix dq)
                 spf_Db pc ms bmi cy ti ip mst0 pcfg paddr mc micfg MISA_C
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
                 eq_refl Hmenv HSXL HMPRV
                 (spf_Db_in_D s_Drwb s_frame_ok_Drwb)
                 (spf_leafchk_in_D s_Drwb s_frame_ok_Drwb)
                 spf_Db_mst spf_Db_satp Hsatpok Hpmpok (pma_all_ram Hpma)
                 ltac:(intros va0 ppn0 tv0;
                       apply (Hbside (InstructionFetch tt) va0 ppn0 KP_rx
                                spf_Db s_Drwb s_Dro _ _);
                       [ left; reflexivity
                       | rewrite s_rs_satp; exact Hbare
                       | rewrite s_rs_mst; exact HMPRV ])
                 with "Hcert") as "#Hobl".
    iApply ("Hobl" $! va ppn tv rr with "[%] [%] Hat Hfrag HRes Hrw Hro");
      [ exact Hlt | exact Hpin ].
  Qed.

End SPtFetch.


(* ===================================================================== *)
(* §2  THE DATA-SIDE TRANSLATION, at the leaf's own footprint.            *)
(*                                                                       *)
(* [HartSMem]'s LOAD/STORE engines take the translation as an obligation   *)
(* whose shape is [SRegime.sr_swp_translate]'s conclusion verbatim -- so    *)
(* this is that field, at [sda_Drw]/[sda_Dro] and with every premise        *)
(* discharged off the tower.  The reference state is THIS HART'S OWN FILE,  *)
(* which is what makes the two agreement premises [reflexivity], and the    *)
(* regime's two remaining obligations come from the fold's producer fields  *)
(* ([sr_adm_of_pin], [sr_swp_side_ok]).  Nothing here names a regime.       *)
(* ===================================================================== *)
Lemma spf_Db_in_sda (r : register) : spf_Db r = true -> r ∈ sda_Drw ∪ sda_Dro.
Proof.
  unfold spf_Db. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact sda_in_mst | exact sda_in_satp].
Qed.

Lemma spf_leafchk_in_sda (r : register) :
  D_leafchk r = true -> r ∈ sda_Drw ∪ sda_Dro.
Proof.
  unfold D_leafchk. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact sda_in_misa | exact sda_in_menv].
Qed.

(* both at an ARBITRARY data write set: every register either set mentions
   lives in [sda_Dro], so the generalization is free. *)
Lemma spf_Db_in_sda_D (D : gset register) (r : register) :
  spf_Db r = true -> r ∈ D ∪ sda_Dro.
Proof.
  unfold spf_Db. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact (sda_in_mst_D D) | exact (sda_in_satp_D D)].
Qed.

Lemma spf_leafchk_in_sda_D (D : gset register) (r : register) :
  D_leafchk r = true -> r ∈ D ∪ sda_Dro.
Proof.
  unfold D_leafchk. intros Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
    [exact (sda_in_misa_D D) | exact (sda_in_menv_D D)].
Qed.

Section SPtData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE TIER SPLIT, [SRegime.sr_absorb_ktier]'s at the swp layer.  At KT0 the
     datum's own pin IS the identity claim, [sr_adm_of_pin] takes it and the
     plain [sr_swp_translate] runs; at KT1 there is no pin at all,
     [KtierLe KT1 kt] forces kt = KT1 so the hart's witness IS [sr_kwit], and
     the WITNESSED field runs instead.  Both arms have the same premise list
     apart from that one conjunct, and both land on the same post, so no leaf
     above ever sees the split. *)
  Lemma sda_translate_D (R : s_regime) (SD : gset register) (kt kt' : ktier) `{Hle : !KtierLe kt' kt}
      (dq : dfrac) (acc : MemoryAccessType mem_payload) (kp : kperm)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb)
      (va : SailStdpp.Values.mword 64) (ppn : SailStdpp.Values.mword 44)
      (rr : option resv) :
    s_acc_ok acc ->
    kperm_allows kp acc ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_ram pmar0 ->
    (uint va < 274877906944)%Z ->
    ktier_pin kt' ppn va ->
    SD ## sda_Dro ->
    (* the regime's side condition as a PREMISE.  [sr_swp_side_ok] demands
       [tlb ∈ Drw] -- it is the introduction a WALKING leaf calls -- and the
       Bare instantiation ([SD := sda_Drwb], the EMPTY set) cannot pay it.
       [sda_translate] below is this at [sda_Drw], with the generic
       introduction supplying it. *)
    sr_swp_side R acc va ppn kp spf_Db SD sda_Dro
      (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv)
      (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∅ dev0_state) ->
    sr_ktier_wit R kt -∗
    kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
    sr_swp_res R (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) -∗
    hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) SD -∗
    hreg_frame_ro (sda_Df dq)
      (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr (pa_of ppn va), PBMT_PMA,
                                init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv \/
                    exists tv, rsf = register_set tlb tv
                                 (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr
                                    tlbv) ⌝ ∗
                  hreg_frame rsf SD ∗
                  hreg_frame_ro (sda_Df dq) rsf sda_Dro ∗
                  sr_swp_res R rsf ∗ resv_any cpu_id).
  Proof.
    intros Hacc Hallow Hmenv HSXL HMPRV Hsok Hpmp Hpma Hlt Hpin Hdisj Hside.
    assert (Heff : exec (effectivePrivilege acc
                     (register_lookup mstatus
                        (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv)
                           ∅ dev0_state).(sregs)) Supervisor)
                     (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∅
                        dev0_state)
                   = Some (Supervisor, _))
      by (apply s_eff_exec; cbn [sregs]; rewrite sda_rs_mst; exact HMPRV).
    assert (Heffg : goodb spf_Db (effectivePrivilege acc
                      (register_lookup mstatus
                         (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv)
                            ∅ dev0_state).(sregs)) Supervisor)
                      (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∅
                         dev0_state) = true)
      by (apply s_eff_goodb; cbn [sregs]; rewrite sda_rs_mst; exact HMPRV).
    destruct kt' as [|].
    - (* KT0: the datum's pin IS the identity claim *)
      iIntros "_".
      iApply (sr_swp_translate R acc SD sda_Dro (sda_Df dq)
                (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv)
                (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∅
                   dev0_state)
                spf_Db va (pa_of ppn va) ppn kp rr
                Hdisj Hacc Hallow
                (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_satp_D SD) (sda_in_pma_D SD)
                (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                (spf_Db_in_sda_D SD) (fun r _ => eq_refl)
                (spf_leafchk_in_sda_D SD) (fun r _ => eq_refl)
                (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _) eq_refl
                ltac:(cbn [sregs]; apply sda_rs_misa)
                ltac:(cbn [sregs]; rewrite sda_rs_menv; exact Hmenv)
                ltac:(rewrite sda_rs_mst; exact HSXL)
                Heff Heffg
                (s_acc_ssa_exec acc _ Hacc) (s_acc_ssa_goodb acc spf_Db _ Hacc)
                (lo_canonical va Hlt) eq_refl
                (sr_adm_of_pin R va ppn Hpin) Hside).
    - (* KT1: no pin; the hart's witness carries admissibility *)
      destruct (ktier_le_cases _ _ Hle) as [Heq | [Hbad _]]; [| discriminate Hbad].
      rewrite -Heq. iIntros "Hw".
      iApply (sr_swp_translate_wit R acc SD sda_Dro (sda_Df dq)
                (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv)
                (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∅
                   dev0_state)
                spf_Db va (pa_of ppn va) ppn kp rr
                Hdisj Hacc Hallow
                (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_satp_D SD) (sda_in_pma_D SD)
                (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                (spf_Db_in_sda_D SD) (fun r _ => eq_refl)
                (spf_leafchk_in_sda_D SD) (fun r _ => eq_refl)
                (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _) eq_refl
                ltac:(cbn [sregs]; apply sda_rs_misa)
                ltac:(cbn [sregs]; rewrite sda_rs_menv; exact Hmenv)
                ltac:(rewrite sda_rs_mst; exact HSXL)
                Heff Heffg
                (s_acc_ssa_exec acc _ Hacc) (s_acc_ssa_goodb acc spf_Db _ Hacc)
                (lo_canonical va Hlt) eq_refl Hside
                with "Hw").
  Qed.

  (* THE KPT PINNING, and the only place [sr_swp_side_ok]'s [tlb ∈ Drw]
     premise is paid on the data side: at [sda_Drw] the cell IS the write set.
     Every existing caller means this one. *)
  Lemma sda_translate (R : s_regime) (kt kt' : ktier) `{Hle : !KtierLe kt' kt}
      (dq : dfrac) (acc : MemoryAccessType mem_payload) (kp : kperm)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb)
      (va : SailStdpp.Values.mword 64) (ppn : SailStdpp.Values.mword 44)
      (rr : option resv) :
    s_acc_ok acc ->
    kperm_allows kp acc ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_ram pmar0 ->
    (uint va < 274877906944)%Z ->
    ktier_pin kt' ppn va ->
    sr_ktier_wit R kt -∗
    kmap_at (svpn_of va) ppn kp -∗ gen_cert -∗ resv_frag cpu_id rr -∗
    sr_swp_res R (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) -∗
    hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drw -∗
    hreg_frame_ro (sda_Df dq)
      (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr (pa_of ppn va), PBMT_PMA,
                                init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv \/
                    exists tv, rsf = register_set tlb tv
                                 (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr
                                    tlbv) ⌝ ∗
                  hreg_frame rsf sda_Drw ∗
                  hreg_frame_ro (sda_Df dq) rsf sda_Dro ∗
                  sr_swp_res R rsf ∗ resv_any cpu_id).
  Proof.
    intros Hacc Hallow Hmenv HSXL HMPRV Hsok Hpmp Hpma Hlt Hpin.
    iApply (sda_translate_D R sda_Drw kt kt' dq acc kp mst0 menv0 satp0 pmar0
              pcfg paddr tlbv va ppn rr Hacc Hallow Hmenv HSXL HMPRV Hsok
              Hpmp Hpma Hlt Hpin sda_disj).
    apply (sr_swp_side_ok R acc va ppn kp spf_Db sda_Drw sda_Dro _ _ Hacc);
      [ rewrite sda_rs_satp; exact Hsok
      | rewrite sda_rs_pcfg sda_rs_paddr; exact Hpmp
      | rewrite sda_rs_pma; exact Hpma
      | rewrite sda_rs_mst; exact HMPRV
      | exact spf_Db_mst | exact spf_Db_satp
      | cbn [sregs]; rewrite sda_rs_mst; exact HSXL
      | cbn [sregs]; reflexivity
      | rewrite /sda_Drw; set_solver ].
  Qed.


  (* ==================================================================== *)
  (* THE PT TIER'S DATA-SIDE SLOT ACCESSOR, AT GENERIC [R].                *)
  (*                                                                      *)
  (* [WpIntrInv.sda_slot_acc] is this at [strans_regime] and it exists for *)
  (* the same reason: pre-port a leaf never saw the translation slot's     *)
  (* cells at all -- it passed [sr_inv R] FOLDED and the walk's TLB write  *)
  (* was absorbed BELOW it.  Handing the cells up is what made the Bare    *)
  (* arm fund a tlb cell, and that is what buried kvminithart's flush.     *)
  (*                                                                      *)
  (* So this takes the slot FOLDED, opens whichever arm is live through    *)
  (* the record's own [sr_slot_acc], and hands the leaf an ABSTRACT write  *)
  (* set with its frames, the regime residue, and the SIDE CONDITION       *)
  (* ALREADY DISCHARGED at that set -- which is the one thing a leaf       *)
  (* cannot produce, since [sr_swp_side_ok] demands [tlb ∈ Drw] and the    *)
  (* Bare arm's set is empty.  The leaf then runs [sda_translate_D] at the *)
  (* abstract set and never learns which arm it is on.                     *)
  (* ==================================================================== *)
  Definition sda_side_at (R : s_regime) (SD : gset register)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) : Prop :=
    forall (acc : MemoryAccessType mem_payload) (kp : kperm)
           (va : SailStdpp.Values.mword 64)
           (ppn : SailStdpp.Values.mword 44) (tv : type_of_register tlb),
      s_acc_ok acc ->
      sr_swp_side R acc va ppn kp spf_Db SD sda_Dro
        (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv)
        (MState (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv) ∅ dev0_state).

  Lemma sda_slot_acc_R (R : s_regime) (dq : dfrac)
      (mst0 menv0 : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    pma_allows_ram pmar0 ->
    reg_pointsto mstatus dq mst0 -∗
    reg_pointsto cur_privilege dq Supervisor -∗
    reg_pointsto menvcfg dq menv0 -∗
    reg_pointsto pma_regions DfracDiscarded pmar0 -∗
    reg_pointsto htif_tohost_base DfracDiscarded None -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    sr_inv R -∗
    ∃ (SD : gset register) (satp0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (tlbv : type_of_register tlb),
      ⌜ SD ## sda_Dro ⌝ ∗ ⌜ SD ⊆ sda_Drw ⌝ ∗ ⌜ sr_swp_satp_ok R satp0 ⌝ ∗
      ⌜ pmp_ent0_ok pcfg paddr ⌝ ∗
      ⌜ sda_side_at R SD mst0 menv0 satp0 pmar0 pcfg paddr ⌝ ∗
      hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) SD ∗
      hreg_frame_ro (sda_Df dq)
        (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro ∗
      sr_swp_res R (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) ∗
      (∀ tv' : type_of_register tlb,
         hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv') SD -∗
         hreg_frame_ro (sda_Df dq)
           (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv') sda_Dro -∗
         sr_swp_res R (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv') -∗
         reg_pointsto mstatus dq mst0 ∗
         reg_pointsto cur_privilege dq Supervisor ∗
         reg_pointsto menvcfg dq menv0 ∗
         reg_pointsto pma_regions DfracDiscarded pmar0 ∗
         reg_pointsto htif_tohost_base DfracDiscarded None ∗
         reg_pointsto misa DfracDiscarded MISA_C ∗ sr_inv R).
  Proof.
    intros Hmenv HSXL HMPRV Hpma.
    iIntros "Hms Hpriv Hmenv Hpma Hhtif Hmisa Hinv".
    iDestruct (sr_slot_acc R with "Hinv") as (satp0 pcfg paddr tlbv)
      "(%Hsok & %Hpok & Hsatp & Hpcfg & Hpaddr & Hres & [Harm | Harm])".
    - (* ---- THE WALKING ARM: the cell is the frame's ---- *)
      iDestruct "Harm" as "(Htlb & _ & Hcl)".
      iExists sda_Drw, satp0, pcfg, paddr, tlbv.
      iSplitR; [iPureIntro; exact sda_disj |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; exact Hsok |].
      iSplitR; [iPureIntro; exact Hpok |].
      iSplitR.
      { iPureIntro. intros acc kp va ppn tv Hacc.
        apply (sr_swp_side_ok R acc va ppn kp spf_Db sda_Drw sda_Dro _ _ Hacc);
          [ rewrite sda_rs_satp; exact Hsok
          | rewrite sda_rs_pcfg sda_rs_paddr; exact Hpok
          | rewrite sda_rs_pma; exact Hpma
          | rewrite sda_rs_mst; exact HMPRV
          | exact spf_Db_mst | exact spf_Db_satp
          | cbn [sregs]; rewrite sda_rs_mst; exact HSXL
          | cbn [sregs]; reflexivity
          | exact sda_w_tlb ]. }
      iDestruct (sda_frames_in dq mst0 menv0 satp0 pmar0 pcfg paddr tlbv
                   with "Htlb Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      iFrame "Hrw Hro".
      iSplitL "Hres".
      { rewrite -sr_swp_res_agree sda_rs_satp sda_rs_tlb. iExact "Hres". }
      iIntros (tv') "Hrw Hro Hres".
      iDestruct (sda_frames_out dq mst0 menv0 satp0 pmar0 pcfg paddr tv'
                   with "[$Hrw $Hro]")
        as "(Htlb & Hms & Hpriv & Hmenv & Hsatp & Hpma & Hpcfg & Hpaddr &
             Hhtif & Hmisa)".
      iFrame "Hms Hpriv Hmenv Hpma Hhtif Hmisa".
      iEval (rewrite -sr_swp_res_agree sda_rs_satp sda_rs_tlb) in "Hres".
      iApply ("Hcl" $! tv' with "Hsatp Hpcfg Hpaddr Htlb Hres").
    - (* ---- THE BARE ARM: no cell, and the side condition comes with it -- *)
      iDestruct "Harm" as "(%Hbare & %Hside & Hcl)".
      iExists sda_Drwb, satp0, pcfg, paddr, tlbv.
      iSplitR; [iPureIntro; exact sda_disj_b |].
      iSplitR; [iPureIntro; exact (empty_subseteq sda_Drw) |].
      iSplitR; [iPureIntro; exact Hsok |].
      iSplitR; [iPureIntro; exact Hpok |].
      iSplitR.
      { iPureIntro. intros acc kp va ppn tv Hacc.
        apply (Hside acc va ppn kp spf_Db sda_Drwb sda_Dro _ _ Hacc);
          [ rewrite sda_rs_satp; exact Hbare
          | rewrite sda_rs_mst; exact HMPRV ]. }
      iDestruct (sda_frames_in_b dq mst0 menv0 satp0 pmar0 pcfg paddr tlbv
                   with "Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      iFrame "Hrw Hro".
      iSplitL "Hres".
      { rewrite -sr_swp_res_agree sda_rs_satp sda_rs_tlb. iExact "Hres". }
      iIntros (tv') "Hrw Hro Hres".
      iDestruct (sda_frames_out_b dq mst0 menv0 satp0 pmar0 pcfg paddr tv'
                   with "[$Hrw $Hro]")
        as "(Hms & Hpriv & Hmenv & Hsatp & Hpma & Hpcfg & Hpaddr &
             Hhtif & Hmisa)".
      iFrame "Hms Hpriv Hmenv Hpma Hhtif Hmisa".
      iEval (rewrite -sr_swp_res_agree sda_rs_satp sda_rs_tlb) in "Hres".
      iApply ("Hcl" $! tv' with "Hsatp Hpcfg Hpaddr Hres").
  Qed.


End SPtData.


(* ===================================================================== *)
(* §3  THE FOLDED INSTRUCTION ENGINE.                                     *)
(*                                                                       *)
(* [SmodeCorePt.wp_instr_s_config_sr] hands its leaf the translation      *)
(* slot's FOUR CELLS (satp / pmpcfg_n / pmpaddr_n / tlb) plus the         *)
(* regime residue.  That is the port's own artifact -- pre-port           *)
(* ([git show main:iris/SmodeCorePt.v]) the leaf took [sr_inv R] FOLDED   *)
(* and the walk's TLB write was absorbed BELOW it -- and it is what       *)
(* forces the Bare arm to fund a [tlb] cell it cannot have, since         *)
(* [translateAddr]'s [Bare] case is a bare [returnR] that never consults  *)
(* the TLB.  This engine restores the pre-port boundary: the leaf takes   *)
(* and returns [sr_inv R], and the engine case-splits on                  *)
(* [SRegime.sr_slot_acc]'s arm ITSELF, running two branches that are      *)
(* CONCRETE in the write set ([s_Drw] / [s_Drwb]) -- §3 of               *)
(* claude-notes/projects/kvminithart-tlb-lane.md forbids any other shape. *)
(*                                                                       *)
(* THREE THINGS IT IS NOT.  It is not a wrapper over the two cell-handout *)
(* engines: those pin the LANDING satp/PMP to the entry values, which a   *)
(* folded slot cannot witness, so the landing satp/pmpcfg/pmpaddr go      *)
(* EXISTENTIAL here (strictly more general -- a leaf that MOVES satp is   *)
(* expressible).  It does not take the fetch translation as a premise:    *)
(* the producer is arm-specific ([spt_fetch_tr_of_regime] /               *)
(* [spt_fetch_tr_of_regime_b]) and a regime-generic leaf has no way to    *)
(* know its arm, so the engine produces it.  And it does not live in      *)
(* [SmodeCorePt.v]: that producer needs [spf_Db] / [spf_Db_in] from this  *)
(* file's head, so this file is the lowest place it can sit -- which is   *)
(* still below every leaf.                                                *)
(* ===================================================================== *)
Section SPtFolded.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- THE CLOSER, AS A RIDER ----------------------------------------
     The slot is opened at the TOP (the fetch's frame needs its cells),
     re-folded INSIDE the body so the leaf is handed [sr_inv R], re-opened
     after the leaf (the frames must go back at the write set the cycle
     fixed), and re-sealed in the CONTINUATION -- which is on the far side
     of the tick.  Nothing at the far end can rebuild the closer, so it has
     to ride, and the only place it can ride is the cycle's post-file
     rider.  [WpSmodeIntr.off_close] is the same shape one tier up: keyed
     on the landing file, so the continuation can name what it pins. *)
  Definition sr_close_at (R : s_regime) (rs2 : regstate) : iProp Σ :=
    (∀ tv' : type_of_register tlb,
       satp ↦ᵣ register_lookup satp rs2 -∗
       pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs2 -∗
       pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs2 -∗
       tlb ↦ᵣ tv' -∗
       sr_swp_res_at R (register_lookup satp rs2) tv' -∗ sr_inv R)%I.

  (* the Bare branch's rider, and the one piece the Bare branch is not a
     mechanical [_b] substitution of.  It carries NO tlb cell and it is
     PINNED at the landing file's own tlb slot rather than ∀ over it: a
     frame at [s_Drwb] cannot have moved the cell, so there is no other
     value to serve.  The pinning is also what absorbs a leaf that FLIPPED
     THE ARM -- the re-open after the leaf is [sr_slot_acc] (there is no
     receipt at Bare), and BOTH of its disjuncts inhabit this: the walking
     one by PARKING its tlb cell inside the closer, the Bare one directly. *)
  Definition sr_close_at_b (R : s_regime) (rs2 : regstate) : iProp Σ :=
    (satp ↦ᵣ register_lookup satp rs2 -∗
     pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs2 -∗
     pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs2 -∗
     sr_swp_res_at R (register_lookup satp rs2) (register_lookup tlb rs2) -∗
     sr_inv R)%I.

  Lemma wp_instr_s_config_folded (R : s_regime)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (* THE LEAF'S OBLIGATION, with the slot FOLDED -- pre-port's boundary
       verbatim.  Gone from it against [wp_instr_s_config_sr]'s: the
       [∀ satp0 pcfg paddr tv'] binder, [⌜sr_swp_satp_ok R satp0⌝],
       [⌜pmp_ent0_ok pcfg paddr⌝], the four cells and the residue.  A leaf
       that needs any of them takes them from [sda_slot_acc_R] instead --
       which also hands it the arm's translation SIDE CONDITION, the one
       thing a regime-generic leaf cannot produce for itself. *)
    (cur_privilege ↦ᵣ{ dq } Supervisor -∗
     mstatus ↦ᵣ{ dq } mstatus0 -∗
     mie ↦ᵣ{ dq } mie_v -∗
     mideleg ↦ᵣ{ dq } mdv0 -∗
     menvcfg ↦ᵣ{ dq } menvcfg0 -∗
     sr_inv R -∗
     clock_res -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
     resv_any cpu_id -∗
     swp (execute i)
       (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                 cur_privilege ↦ᵣ{ dq } Supervisor ∗
                 mie ↦ᵣ{ dq } mie1 ∗
                 menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                 sr_inv R ∗ clock_res ∗
                 (∃ ms1 mdv1 npc : mword 64,
                    mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                    (R_bitvector_64 PC) ↦ᵣ pc ∗
                    (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                 resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         sr_inv R -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval.
    iIntros "#Hhw #Hminv Hhs Hpriv Hmst Hmie Hmdl Hmenv Hinv Hpc Hinstr Hex
             Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (sr_slot_acc R with "Hinv") as (satp0 pcfg paddr tlbv)
      "(%Hsatpok & %Hpmpok & Hsatp & Hpcfg & Hpaddr & HRes & [Harm | Harm])".
    - (* ================= THE WALKING ARM, at [s_Drw] ================= *)
      iDestruct "Harm" as "(Htlbc & #Hwit & Hcl)".
      pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct (spt_frames_intro dq pc mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg
                   paddr tlbv
                   with "Hhw Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                         Htlbc Hpc") as "[Hfrag Hfr]".
      iDestruct "Hfr" as (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0
                          elp0) "(%Hmisaval & %Hpmaall & %Helpnp & Hrw & Hro)".
      (* THE ENGINE PRODUCES THE FETCH TRANSLATION.  A leaf cannot: at the
         Bare arm it would have to be [spt_tr_obl_D s_Drwb], and nothing a
         regime-generic leaf holds tells it which arm it is on. *)
      iPoseProof (spt_fetch_tr_of_regime R dq pc mstatus0 satp0 mie_v mdv0
                    menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                    with "Hhw") as "#Htr".
      iPoseProof ("Htr" $! ms (minstret_inc_flag mc micfg Supervisor) cy ti ip
                    mc micfg misa0 mseccfg0 senv0 pmar0 elp0) as "#Htr0".
      iApply (spt_cycle (s_Df_mix dq) pc
                (fun rs2 => (sr_swp_res R rs2 ∗ sr_close_at R rs2
                             ∗ resv_any cpu_id
                             ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                  (register_lookup mstatus rs2)
                                  (register_lookup mideleg rs2))%I)
                (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 satp1 : mword 64)
                              (pcfg1 : type_of_register pmpcfg_n)
                              (paddr1 : type_of_register pmpaddr_n)
                              (tv : type_of_register tlb),
                   rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                ms bmi cy ti ip mstatus0 mc micfg misa0 mseccfg0 senv0 pmar0
                elp0 satp0 mie_v mdv0 menvcfg0 pcfg paddr tlbv
                ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 &
                                  pcfg1 & paddr1 & tv & ->); apply s_rs_hart)
                ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 &
                                  pcfg1 & paddr1 & tv & ->); apply s_rs_mi)
                with "Hcert Hfrag Hrw Hro [Hex HRes Hinstr Hcl] [Hcont]").
      2:{ (* ---- the continuation: RE-SEAL, off the rider ---- *)
          iNext. iIntros (rs3 rs2 mi)
            "[%HQ %Hag] Hrw Hro (HRes & Hclose & Hfrag & HRl)".
          destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 & pcfg1 &
                          paddr1 & tv & ->).
          iEval (rewrite -sr_swp_res_agree s_rs_satp s_rs_tlb) in "HRes".
          iEval (rewrite /sr_close_at s_rs_satp s_rs_pcfg s_rs_paddr)
            in "Hclose".
          iEval (rewrite s_rs_nPC s_rs_mst s_rs_mdl) in "HRl".
          pose proof (s_tick_agree pc npc ms
                        (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                        pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                        satp1 mie1 mdv1 menvcfg1 tv mi rs3 Hag) as Hag'.
          iDestruct (s_rw_ext _ _ Hag' with "Hrw") as "Hrw".
          iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hag' with "Hro") as "Hro".
          iDestruct (spt_frames_elim dq npc mi
                       (minstret_inc_flag mc micfg Supervisor) _ _ _ mc micfg
                       misa0 mseccfg0 senv0 pmar0 elp0 ms1 satp1 mie1 mdv1
                       menvcfg1 pcfg1 paddr1 tv with "Hfrag Hrw Hro")
            as "(Hhs & Hpriv & Hmst & Hmie & Hmdl & Hmenv & Hsatp & Hpcfg &
                 Hpaddr & Htlbc & Hpc)".
          iApply ("Hcont" $! npc ms1 mdv1 with
                    "Hhs Hpriv Hmst Hmie Hmdl Hmenv
                     [Hsatp Hpcfg Hpaddr Htlbc HRes Hclose] Hpc HRl").
          iApply ("Hclose" $! tv with "Hsatp Hpcfg Hpaddr Htlbc HRes"). }
      (* ---- the body ---- *)
      iIntros "Hfrag Hrw Hro".
      iApply (swp_mono with "[] [-]");
        [| iApply (spt_run_hart_active_instr_S (s_Df_mix dq) pc ms
                     (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                     pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                     mie_v mdv0 menvcfg0 (sr_swp_res_at R satp0) tlbv is_rvc i
                     (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 satp1 : mword 64)
                                   (pcfg1 : type_of_register pmpcfg_n)
                                   (paddr1 : type_of_register pmpaddr_n)
                                   (tv : type_of_register tlb),
                        rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                     (fun rs2 => (sr_swp_res R rs2 ∗ sr_close_at R rs2
                                  ∗ resv_any cpu_id
                                  ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                       (register_lookup mstatus rs2)
                                       (register_lookup mideleg rs2))%I)
                     emp%I (fun _ _ => False%I)
                     Hmisaval Hmenvval Helpnp (pma_all_ram Hpmaall)
                     HA Hord HX Hcov
                     with "Hcert Hinstr [] Hfrag HRes Hrw Hro [] Htr0
                           [Hex Hcl]") ].
      + iIntros (st) "[Hi | Hr]".
        * iDestruct "Hi" as (ii pr) "(_ & Hf)". iDestruct "Hf" as %[].
        * iDestruct "Hr" as (w) "(-> & Hr)".
          iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HPsi)".
          iExists rs2. iSplitR; [done|]. iFrame.
      + done.
      + iApply (spt_dispatch_none (s_Df_mix dq) pc ms
                  (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                  pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                  mie_v mdv0 menvcfg0 (sr_swp_res_at R satp0) tlbv emp%I
                  (fun _ _ => False%I) Hmisaval HSIE Hmm with "Hcert").
      + (* THE LEAF, at the file the fetch landed on *)
        iIntros (tv') "_ HRes' Hany Hrw Hro".
        pose proof (s_npc_agree pc pc
                      (add_vec_int pc (if is_rvc then 2 else 4)) ms
                      (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                      pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                      mie_v mdv0 menvcfg0 tv') as Hnp.
        iDestruct (s_rw_ext _ _ Hnp with "Hrw") as "Hrw".
        iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hnp with "Hro") as "Hro".
        iDestruct (spt_frames_open dq pc
                     (add_vec_int pc (if is_rvc then 2 else 4)) ms
                     (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                     pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                     mie_v mdv0 menvcfg0 tv' with "Hrw Hro")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc & Hpriv & Hmst
               & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg & #Hmisa & #Hsec & #Hpma
               & #Hhtif & #Help & #Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
        iAssert clock_res with "[Hcy Hti Hip]" as "Hclk".
        { iExists cy, ti, ip. iFrame "Hcy Hti Hip". }
        (* RE-FOLD: the leaf is handed the slot, not its cells *)
        iDestruct ("Hcl" $! tv' with "Hsatp Hpcfg Hpaddr Htlbc HRes'")
          as "Hinv".
        iApply (swp_mono with "[Hms Hmi Hhs] [-]");
          [| iApply ("Hex" with "Hpriv Hmst Hmie Hmdl Hmenv Hinv Hclk HPC HnPC
                       Hany") ].
        iIntros (e) "(-> & Hpriv & Hmie & Hmenv & Hinv & Hclk & Hcfg & Hany)".
        (* RE-OPEN: the frames must go back at the write set the cycle fixed,
           and the leaf may have MOVED the slot (a satp switch does).  The
           walking arm's persistent receipt is what says the arm survived. *)
        iDestruct (sr_slot_reopen R with "Hwit Hinv")
          as (satp1 pcfg1 paddr1 tv2)
          "(%Hsatpok1 & %Hpmpok1 & Hsatp & Hpcfg & Hpaddr & Htlbc & HRes' &
            Hcl2)".
        iDestruct "Hclk" as (cy1 ti1 ip1) "(Hcy & Hti & Hip)".
        iDestruct "Hcfg" as (ms1 mdv1 npc) "(Hmst & Hmdl & HPC & HnPC & HRl)".
        iSplitR; [done|].
        iExists (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv2).
        iSplitR;
          [ iPureIntro;
            by exists npc, ms1, mdv1, cy1, ti1, ip1, satp1, pcfg1, paddr1,
                      tv2 |].
        iDestruct (spt_frames_close dq pc npc ms
                     (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                     pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                     satp1 mie1 mdv1 menvcfg1 tv2
                     with "[HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs
                            Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenv]")
          as "[Hrw Hro]".
        { iFrame "HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs Hpcfg
                  Hpaddr Hsatp Hmie Hmdl Hmenv".
          by iFrame "Hmc Hmicfg Hmisa Hsec Hpma Hhtif Help Hsenv". }
        iFrame "Hrw Hro".
        iSplitL "HRes'".
        { rewrite -sr_swp_res_agree s_rs_satp s_rs_tlb. iExact "HRes'". }
        iSplitL "Hcl2".
        { rewrite /sr_close_at s_rs_satp s_rs_pcfg s_rs_paddr. iExact "Hcl2". }
        iFrame "Hany".
        rewrite s_rs_nPC s_rs_mst s_rs_mdl. iExact "HRl".
    - (* ================== THE BARE ARM, at [s_Drwb] ================== *)
      iDestruct "Harm" as "(%Hbare & %Hside & Hcl)".
      pose proof Hpmpok as (HA & Hord & HX & HW & HR & Hcov).
      iDestruct (spt_frames_intro_b dq pc mstatus0 mie_v mdv0 menvcfg0 satp0
                   pcfg paddr tlbv
                   with "Hhw Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                         Hpc") as "[Hfrag Hfr]".
      iDestruct "Hfr" as (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0
                          elp0) "(%Hmisaval & %Hpmaall & %Helpnp & Hrw & Hro)".
      iPoseProof (spt_fetch_tr_of_regime_b R dq pc mstatus0 satp0 mie_v mdv0
                    menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                    Hbare Hside with "Hhw") as "#Htr".
      iPoseProof ("Htr" $! ms (minstret_inc_flag mc micfg Supervisor) cy ti ip
                    mc micfg misa0 mseccfg0 senv0 pmar0 elp0) as "#Htr0".
      iApply (spt_cycle_b (s_Df_mix dq) pc
                (fun rs2 => (sr_swp_res R rs2 ∗ sr_close_at_b R rs2
                             ∗ resv_any cpu_id
                             ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                  (register_lookup mstatus rs2)
                                  (register_lookup mideleg rs2))%I)
                (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 satp1 : mword 64)
                              (pcfg1 : type_of_register pmpcfg_n)
                              (paddr1 : type_of_register pmpaddr_n)
                              (tv : type_of_register tlb),
                   rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                ms bmi cy ti ip mstatus0 mc micfg misa0 mseccfg0 senv0 pmar0
                elp0 satp0 mie_v mdv0 menvcfg0 pcfg paddr tlbv
                ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 &
                                  pcfg1 & paddr1 & tv & ->); apply s_rs_hart)
                ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 &
                                  pcfg1 & paddr1 & tv & ->); apply s_rs_mi)
                with "Hcert Hfrag Hrw Hro [Hex HRes Hinstr Hcl] [Hcont]").
      2:{ (* ---- the continuation ---- *)
          iNext. iIntros (rs3 rs2 mi)
            "[%HQ %Hag] Hrw Hro (HRes & Hclose & Hfrag & HRl)".
          destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & satp1 & pcfg1 &
                          paddr1 & tv & ->).
          iEval (rewrite -sr_swp_res_agree s_rs_satp s_rs_tlb) in "HRes".
          iEval (rewrite /sr_close_at_b s_rs_satp s_rs_pcfg s_rs_paddr
                   s_rs_tlb) in "Hclose".
          iEval (rewrite s_rs_nPC s_rs_mst s_rs_mdl) in "HRl".
          pose proof (s_tick_agree_b pc npc ms
                        (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                        pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                        satp1 mie1 mdv1 menvcfg1 tv mi rs3 Hag) as Hag'.
          iDestruct (s_rw_ext_D s_Drwb _ _ (s_agree_narrow_b _ _ Hag')
                       with "Hrw") as "Hrw".
          iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hag' with "Hro") as "Hro".
          (* AT THE LANDING FILE'S OWN TLB SLOT: [s_tick_agree_b] cannot name
             the value the cycle started with ([s_Drwb ∪ s_Dro] has no tlb in
             it), and naming [tv] here is the 3^N tower bomb. *)
          iDestruct (spt_frames_elim_b dq npc mi
                       (minstret_inc_flag mc micfg Supervisor) _ _ _ mc micfg
                       misa0 mseccfg0 senv0 pmar0 elp0 ms1 satp1 mie1 mdv1
                       menvcfg1 pcfg1 paddr1 (register_lookup tlb rs3)
                       with "Hfrag Hrw Hro")
            as "(Hhs & Hpriv & Hmst & Hmie & Hmdl & Hmenv & Hsatp & Hpcfg &
                 Hpaddr & Hpc)".
          iApply ("Hcont" $! npc ms1 mdv1 with
                    "Hhs Hpriv Hmst Hmie Hmdl Hmenv
                     [Hsatp Hpcfg Hpaddr HRes Hclose] Hpc HRl").
          iApply ("Hclose" with "Hsatp Hpcfg Hpaddr HRes"). }
      (* ---- the body ---- *)
      iIntros "Hfrag Hrw Hro".
      iApply (swp_mono with "[] [-]");
        [| iApply (spt_run_hart_active_instr_S_b (s_Df_mix dq) pc ms
                     (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                     pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                     mie_v mdv0 menvcfg0 (sr_swp_res_at R satp0) tlbv is_rvc i
                     (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 satp1 : mword 64)
                                   (pcfg1 : type_of_register pmpcfg_n)
                                   (paddr1 : type_of_register pmpaddr_n)
                                   (tv : type_of_register tlb),
                        rs2 = s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                     (fun rs2 => (sr_swp_res R rs2 ∗ sr_close_at_b R rs2
                                  ∗ resv_any cpu_id
                                  ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                       (register_lookup mstatus rs2)
                                       (register_lookup mideleg rs2))%I)
                     emp%I (fun _ _ => False%I)
                     Hmisaval Hmenvval Helpnp (pma_all_ram Hpmaall)
                     HA Hord HX Hcov
                     with "Hcert Hinstr [] Hfrag HRes Hrw Hro [] Htr0
                           [Hex Hcl]") ].
      + iIntros (st) "[Hi | Hr]".
        * iDestruct "Hi" as (ii pr) "(_ & Hf)". iDestruct "Hf" as %[].
        * iDestruct "Hr" as (w) "(-> & Hr)".
          iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HPsi)".
          iExists rs2. iSplitR; [done|]. iFrame.
      + done.
      + iApply (spt_dispatch_none_D s_Drwb s_frame_ok_Drwb (s_Df_mix dq) pc ms
                  (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                  pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                  mie_v mdv0 menvcfg0 (sr_swp_res_at R satp0) tlbv emp%I
                  (fun _ _ => False%I) Hmisaval HSIE Hmm with "Hcert").
      + (* THE LEAF *)
        iIntros (tv') "_ HRes' Hany Hrw Hro".
        pose proof (s_npc_agree pc pc
                      (add_vec_int pc (if is_rvc then 2 else 4)) ms
                      (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                      pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                      mie_v mdv0 menvcfg0 tv') as Hnp.
        iDestruct (s_rw_ext_D s_Drwb _ _ (s_agree_narrow_b _ _ Hnp)
                     with "Hrw") as "Hrw".
        iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hnp with "Hro") as "Hro".
        iDestruct (spt_frames_open_b dq pc
                     (add_vec_int pc (if is_rvc then 2 else 4)) ms
                     (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                     pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                     mie_v mdv0 menvcfg0 tv' with "Hrw Hro")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Hpriv & Hmst
               & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg & #Hmisa & #Hsec & #Hpma
               & #Hhtif & #Help & #Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
        iAssert clock_res with "[Hcy Hti Hip]" as "Hclk".
        { iExists cy, ti, ip. iFrame "Hcy Hti Hip". }
        iDestruct ("Hcl" $! tv' with "Hsatp Hpcfg Hpaddr HRes'") as "Hinv".
        iApply (swp_mono with "[Hms Hmi Hhs] [-]");
          [| iApply ("Hex" with "Hpriv Hmst Hmie Hmdl Hmenv Hinv Hclk HPC HnPC
                       Hany") ].
        iIntros (e) "(-> & Hpriv & Hmie & Hmenv & Hinv & Hclk & Hcfg & Hany)".
        (* RE-OPEN with [sr_slot_acc], not [sr_slot_reopen]: there is no
           receipt at Bare, and the leaf MAY HAVE FLIPPED THE ARM.  Both
           disjuncts serve [sr_close_at_b] -- the walking one by PARKING its
           tlb cell inside the closer. *)
        iDestruct (sr_slot_acc R with "Hinv") as (satp1 pcfg1 paddr1 tv2)
          "(%Hsatpok1 & %Hpmpok1 & Hsatp & Hpcfg & Hpaddr & HRes' & Harm)".
        iAssert (sr_swp_res_at R satp1 tv2 -∗
                 satp ↦ᵣ satp1 -∗ pmpcfg_n ↦ᵣ pcfg1 -∗ pmpaddr_n ↦ᵣ paddr1 -∗
                 sr_inv R)%I with "[Harm]" as "Hcl2".
        { iDestruct "Harm" as "[(Htlbc & _ & Hcl2) | (_ & _ & Hcl2)]".
          - iIntros "HRes'' Hsatp Hpcfg Hpaddr".
            iApply ("Hcl2" $! tv2 with "Hsatp Hpcfg Hpaddr Htlbc HRes''").
          - iIntros "HRes'' Hsatp Hpcfg Hpaddr".
            iApply ("Hcl2" $! tv2 with "Hsatp Hpcfg Hpaddr HRes''"). }
        iDestruct "Hclk" as (cy1 ti1 ip1) "(Hcy & Hti & Hip)".
        iDestruct "Hcfg" as (ms1 mdv1 npc) "(Hmst & Hmdl & HPC & HnPC & HRl)".
        iSplitR; [done|].
        iExists (s_rs pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv2).
        iSplitR;
          [ iPureIntro;
            by exists npc, ms1, mdv1, cy1, ti1, ip1, satp1, pcfg1, paddr1,
                      tv2 |].
        iDestruct (spt_frames_close_b dq pc npc ms
                     (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                     pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                     satp1 mie1 mdv1 menvcfg1 tv2
                     with "[HPC HnPC Hms Hmi Hcy Hti Hip Hpriv Hmst Hhs
                            Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenv]")
          as "[Hrw Hro]".
        { iFrame "HPC HnPC Hms Hmi Hcy Hti Hip Hpriv Hmst Hhs Hpcfg
                  Hpaddr Hsatp Hmie Hmdl Hmenv".
          by iFrame "Hmc Hmicfg Hmisa Hsec Hpma Hhtif Help Hsenv". }
        iFrame "Hrw Hro".
        iSplitL "HRes'".
        { rewrite -sr_swp_res_agree s_rs_satp s_rs_tlb. iExact "HRes'". }
        iSplitL "Hcl2".
        { rewrite /sr_close_at_b s_rs_satp s_rs_pcfg s_rs_paddr s_rs_tlb.
          iIntros "Hsatp Hpcfg Hpaddr HRes''".
          iApply ("Hcl2" with "HRes'' Hsatp Hpcfg Hpaddr"). }
        iFrame "Hany".
        rewrite s_rs_nPC s_rs_mst s_rs_mdl. iExact "HRl".
  Qed.

End SPtFolded.
