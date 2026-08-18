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
  Context `{KTR : CurKtier}.

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
