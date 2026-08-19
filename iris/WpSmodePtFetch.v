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


End SPtData.
