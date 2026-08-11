(* WpSconfMem.v -- the SIE-AGNOSTIC data-leaf layer (interrupt-sweep
   stage 5): the [sconf]+[sie_cap] twins of the width-8 RVC LOAD/STORE
   exemplars (WpSmodePtLeaves.v's [wp_cld_s_pt]/[wp_csd_s_pt]), over the
   agnostic funnel [wp_instr_s_sconf].

   The data-side translation runs through the regime-blind absorption
   [sr_absorb strans_regime] INSIDE the funnel's σf-callback: the
   callback threads the FOLDED translation slot [strans_inv] (as "Htr")
   through [strans_regime] with NO skolem-root open, effective-address
   transform comes from [sr_transform strans_regime], and the post-
   translate PMP/PMA facts come from [sr_absorb]'s [pmp_grant_facts]
   conclusion (mirroring the R-generic `_r` data leaves).  The config
   facts (MPRV/SXL/MXR/PMM) come from [sconf]'s bundled fact sets
   instead of eight per-call premises.  Spec cleanups made in this pass:
     - the redundant [let ea := .. let a8 := ea let pa := a8] alias
       chain collapses to the single [let pa := ..];
     - ALL config premises are gone (SIE is decided by the ghost, the
       rest ride in [sconf_ms_facts]/the menvcfg conjunct);
     - the STORE needs no rd-premises at all (it writes no register,
       so [sie_cap] is not even retargeted); the LOAD keeps
       [uint rd <> 0] and [rd_ok rd] (the latter replaces the old
       [rd <> csp_rs1] IN THE SAME SLOT: it also rules out tp, which the
       register file pins -- HartTp.v).
   The address / stored-value operands are read with [rget m rs]
   (correct at tp too) and stay OUTSIDE the [wp_next] lambda as [let]s:
   they are words computed from the ENTRY map, at the hart we came from,
   while every resource inside the lambda is about the hart we resume on.
   The remaining WpSmodePtMem widths (4/1, base widths) follow this
   template mechanically.                                                *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import MinstretInv.
Require Import UserBits.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import SmodePte.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import WpSmodeMemGen.
Require Import MemAccessGen.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import KptGhost.   (* kptN: the accessor-mask premise below *)
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.


(* helper copies (Local in WpSmodePtMem.v). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
  Proof.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
  Qed.

Section WpSconfMem.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* c.ld rd, imm(rs1) -- width-8 RVC load.                               *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mulw (width : Z) (a : mword 64) : add_vec_int a (0 * width) = a.
  Proof. change (0 * width)%Z with 0%Z. apply avi0. Qed.

  Definition wordw_pointsto (width : Z) (a : Arch.pa) (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width), mem_pointsto (pa_add a j) dq (nth_byte w j))%I.

  Local Lemma write_bytes_1 (mm : _) (pa : Arch.pa) (v : bv 8) :
    write_bytes mm pa 1 v = <[pa := nth_byte v 0]> mm.
  Proof. unfold write_bytes. change (N.to_nat 1) with 1%nat. cbn [seq foldr]. rewrite pa_add_0. reflexivity. Qed.

  Local Lemma nth_byte0_id (v : bv 8) : nth_byte v 0 = v.
  Proof.
    apply bv_eq. rewrite nth_byte_unsigned.
    change (Z.of_N (8 * N.of_nat 0)) with 0%Z. rewrite Z.shiftr_0_r.
    apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ v) as Hr.
    unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 8)%Z with 256%Z in Hr. change (2 ^ 8)%Z with 256%Z. lia.
  Qed.

  (* claim-keyed generic window write (uniform-claims: replaces the old
     physical [wordw_pointsto_write]).  Given the base [KP_rw] claim of a
     non-straddling VA window it overwrites the ACTUAL translated physical
     bytes at [pa_of ppn a] in step with the heap.  Width-agnostic via
     [s_win_write]. *)
  Local Lemma wordw_pointsto_write_c (width : Z) (mm : _) (a : mword 64)
      (ppn : mword 44) (vold vnew : mword (8*width)) :
    0 < width ->
    (uint a < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec a 11 0) + width <= 4096)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ wordw_pointsto width a (DfracOwn 1) vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn a) (Z.to_N width) vnew) ∗
    wordw_pointsto width a (DfracOwn 1) vnew.
  Proof.
    intros Hw0 Hcan Hoff. iIntros "#Hk Hm Hw". rewrite /wordw_pointsto.
    iDestruct "Hw" as "(%Hal & Hb)".
    iMod (s_win_write a ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 (Z.to_nat width))
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hjw];
                  assert (Hjz : Z.of_nat j < width) by
                    (rewrite <- (Z2Nat.id width) by lia; apply Nat2Z.inj_lt; exact Hjw);
                  lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. iSplitL "Hm".
    - unfold write_bytes. replace (N.to_nat (Z.to_N width)) with (Z.to_nat width) by lia. iFrame "Hm".
    - iFrame "Hb". iPureIntro. exact Hal.
  Qed.

  (* claim-keyed single-byte write (width-1 store): writes at [pa_of ppn a]. *)
  Local Lemma mem_pointsto_write_c (mm : _) (a : mword 64)
      (ppn : mword 44) (vold vnew : bv 8) :
    (uint a < 274877906944)%Z ->
    kmap_at (svpn_of a) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn a) 1 vnew) ∗ a ↦ₘ (nth_byte vnew 0).
  Proof.
    intros Hcan. iIntros "#Hk Hm Hw".
    assert (Hoff0 : (bv_unsigned (subrange_vec_dec a 11 0) + Z.of_nat 0 < 4096)%Z).
    { change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r.
      pose proof (off_bound_div a 1 ltac:(lia) ltac:(exists 4096; lia)
        ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)) as H1.
      rewrite (uint_unsigned_n _) in H1. lia. }
    iAssert ([∗ list] j ∈ (cons 0%nat nil), (pa_add a j) ↦ₘ (nth_byte vold j))%I with "[Hw]" as "Hw'".
    { iEval (rewrite big_sepL_singleton pa_add_0 nth_byte0_id). iExact "Hw". }
    iMod (s_win_write a ppn (nth_byte vold) (nth_byte vnew) Hcan (cons 0%nat nil)
            ltac:(constructor; [exact Hoff0 | constructor])
            mm with "Hk Hm Hw'") as "[Hm Hb]".
    iModIntro. iSplitL "Hm".
    - replace (write_bytes mm (pa_of ppn a) 1 vnew)
        with (foldr (fun j acc => <[pa_add (pa_of ppn a) j := nth_byte vnew j]> acc) mm (cons 0%nat nil)).
      2:{ cbn [foldr]. rewrite write_bytes_1 pa_add_0. reflexivity. }
      iExact "Hm".
    - iDestruct "Hb" as "[Hb _]". rewrite pa_add_0. iExact "Hb".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The width/RVC-generic load in ATOMIC-UPDATE form: the cell need NOT   *)
  (* be owned by the caller across the step -- it is produced, and handed  *)
  (* back, inside the engine callback's own mask.  That is what lets a     *)
  (* lock leaf open [is_lock] around exactly this step (WpSconfLock.v);    *)
  (* [wp_load_s_sconf_gen] below is the trivial instance in which the      *)
  (* caller already owns the cell.                                         *)
  (* The loaded word [v] is quantified OUTSIDE the [wp_next] hart binder:  *)
  (* it is a word, not a hart-indexed resource, so a consumer introduces   *)
  (* it first ([iIntros (v CID1 Hs1) "..."]) and the engine discharges     *)
  (* both quantifiers in one [iApply ... $! v cpu_id].                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_load_s_sconf_au (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (ext : mword (8*width) -> mword 64)
      (Ψ : mword (8*width) -> iProp Σ) (Em : coPset) (b : bool) {dqm : dfrac} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (* the vmem level hands back the value itself now, not the split
       accumulator, so the caller's extension is just [extend_value] *)
    (forall v : mword (8*width), extend_value uns v = ext v) ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    (* the data translation is absorbed WITH THE ACCESSOR OPEN, so the
       shared kernel table's namespace must be inside the accessor's inner
       mask (claude-notes/completed/kpt-share.md).  Every supplier's [Em] is
       [⊤ ∖ ↑minstretN] minus device/lock namespaces, so [solve_ndisj]. *)
    ↑kptN ⊆ Em ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword (8*width),
       wordw_pointsto width pa dqm v ∗
       (wordw_pointsto width pa dqm v ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword (8*width),
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr (<[Regidx rd := regval_into_reg (ext v)]> m) n b p -∗
        pc_is (add_vec_int pc (if c then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hext pa Hrd Hrdok HkptEm.
    rdok_split Hrdok.
    set (wlast := (Z.to_nat width - 1)%nat).
    assert (Hwn : Z.of_nat wlast = width - 1) by (unfold wlast; rewrite Nat2Z.inj_sub; [ rewrite Z2Nat.id; lia | lia ]).
    assert (Hwlt : (wlast < Z.to_nat width)%nat) by (unfold wlast; lia).
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_instr_s_sconf m n b pc c
              (LOAD (imm, Regidx rs1, Regidx rd, uns, width))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* open the caller's atomic update: the cell, and how to give it back *)
    iMod "HAU" as (v) "[Hbw Hcl]".
    iEval (rewrite /wordw_pointsto) in "Hbw".
    iDestruct "Hbw" as "(%Hpalign & Hbytes)".
    assert (Halign : is_aligned_vaddr (Virtaddr pa) width = true) by exact Hpalign.
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa width Hw0 Hwdvd Halign) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hmd : rf_to_gmap (tp_pin m) !! Regidx rd = Some (tp_pin m !!! Regidx rd))
      by (apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if c then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if c then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform strans_regime (Load Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb strans_regime (Load Data) pa (pa_of ppn pa) ppn KP_rw s_pc _
            (or_intror (or_introl eq_refl)) I
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_load s_pc)
            Lpma_pc' Hid _ with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [exact HkptEm |].
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    assert (Hoff' : (bv_unsigned (subrange_vec_dec pa 11 0) + Z.of_nat (Z.to_nat width) <= 4096)%Z)
      by (rewrite Z2Nat.id; [ exact Hoff | lia ]).
    iDestruct (s_mem_chunk s_tr pa pa 0 (Z.to_nat width) (Z.to_nat width) (nth_byte v) ppn dqm
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff' Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf & Hram0 & Hraml & _).
    assert (Hbytesf_tr : forall j : nat, (N.of_nat j < Z.to_N width)%N ->
              s_tr.(mem) !! (pa_add (pa_of ppn pa) j) = Some (nth_byte v j)).
    { intros j Hj. apply Hbytesf. lia. }
    destruct (pma_all_ram Hpma_all (pa_of ppn pa) width
               (pma_access_ram_at (pa_of ppn pa) width wlast Hwn Hram0 Hraml
                  (pma_width_le width 8 Hw0 Hw8 eq_refl))) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + width <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat wlast < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. rewrite Hwn. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) wlast Hnw) as Heq.
      fold wlast in Hraml.
      destruct Hraml as [_ Hhil]. rewrite Heq in Hhil. rewrite Hwn in Hhil.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) width s_tr (addr_is_ram_not_in_clint _ Hram0) Hw0) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) width s_tr (addr_is_ram_not_in_sig _ Hram0) Hw0) as Hws.
    pose proof (within_htif_false (pa_of ppn pa) width s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Load Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, uns, width))) s_pc
                    = Some (RETIRE_SUCCESS,
                            set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (ext v)))).
    { rewrite <- (Hext v).
      pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) width Hw0 Huintw Hlo Hfit Hcov) as Hrange_ld.
      apply (exec_execute_LOAD_w_gpr_S_walk_pt width Hw0 Hw8 Hvw Hread_plain uns rs1 rd imm v region_ld s_pc s_tr (pa_of ppn pa) md0 Hrd
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               HA0 Hord0
               Hrange_ld HR
               ltac:(rewrite Lpma_tr; exact Hmatch_ld0)
               (pa_aligned_div ppn pa width Hw0 Hwdvd Halign)
               Hread_ld Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)
               Hbytesf_tr). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ext v))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (ext v)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap".
    (* hand the (unchanged) cell back and collect the caller's payload *)
    iAssert (wordw_pointsto width pa dqm v)%I with "[Hbytes]" as "Hbw".
    { rewrite /wordw_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign. }
    iMod ("Hcl" with "Hbw") as "HPsi".
    iModIntro.
    iExists (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ext v))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hload. }
    iSplitL "Hreg Hmem Hdev".
    { unfold set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_tr (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ext v))).(sregs)
             = add_vec_int pc (if c then 2 else 4)).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap m n b p) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx csp_rs1 ≠ Regidx rd) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (ext v)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; exact Hspne).
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg (ext v)]> m) n b Hsp with "Hcap") as "Hcap".
    iAssert (gpr_file (<[Regidx rd := regval_into_reg (ext v)]> (tp_pin m))) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; apply rf_to_gmap_dom | iExact "Hfmap"]. }
    (* the leaf's own write commutes with the tp pin *)
    tp_refold (rd_ok_tp _ Hrdok) "Hfile".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! v cpu_id with "[] Hcg [$Hpc' $Hnpc] HPsi").
    iPureIntro. done.
  Qed.

  (* The non-atomic instance: the caller owns the cell throughout.  Generic
     in BOTH the width and the extension flag [uns], so every RAM load leaf
     in the tree (lb/lbu/lh/lhu/lw/lwu/ld and the RVC twins) is one line off
     it.  [wp_load_s_sconf_gen] / [wp_load_s_sconf_ugen] below are its
     [uns = false] / [uns = true] restatements (WRAPPER RECIPE). *)
  Lemma wp_load_s_sconf_gen_u (width : Z) (c uns : bool) (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    (* the vmem level hands back the value itself now *)
    extend_value uns v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, uns, width)) -∗
    wordw_pointsto width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain Hlv pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_au width c uns pc rd rs1 imm m n
              (fun w => extend_value uns w)
              (fun w => (⌜w = v⌝ ∗ wordw_pointsto width pa dqm v)%I) (⊤ ∖ ↑minstretN) b
              Hw0 Hw8 Hvw Hwdvd Huintw Hread_plain (fun w => eq_refl) Hrd Hrdok
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [Hbytes]").
    { iModIntro. iExists v. iFrame "Hbytes". iIntros "Hb". iModIntro. by iFrame "Hb". }
    iIntros (w CID1 Hs1) "Hcg Hpc [-> Hbw]".
    iEval (rewrite Hlv) in "Hcg".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* the SIGNED restatement. *)
  Lemma wp_load_s_sconf_gen (width : Z) (c : bool) (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    extend_value false v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, false, width)) -∗
    wordw_pointsto width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_load_s_sconf_gen_u width c false pc rd rs1 imm m n v lv b (dqm := dqm)).
  Qed.

  (* The UNSIGNED restatement.  [wp_load_s_sconf_gen_u] is generic in the
     extension ([uns]), so the two differ in exactly that flag -- which is why
     the width-1 [lbu] and the width-4 [lwu] are one-line instances of THIS
     rather than two hand-rolled copies of the same 190-line argument. *)
  Lemma wp_load_s_sconf_ugen (width : Z) (c : bool) (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword (8*width)) (lv : mword 64) (b : bool) {dqm : dfrac} :
    0 < width -> width <= 8 ->
    (* the vmem level splits on a PAGE boundary now, which needs the width to
       be one of the four the ISA allows there *)
    vmem_width width ->
    (width | 4096) ->
    uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (w : mword (8*width)) s,
       dev_addr addr = false ->
       (forall j : nat, (N.of_nat j < Z.to_N width)%N ->
          s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
       exec (read_ram rv64d_types.Read_plain (Physaddr addr) width false) s
         = Some ((w, default_meta), s)) ->
    extend_value true v = lv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (LOAD (imm, Regidx rs1, Regidx rd, true, width)) -∗
    wordw_pointsto width pa dqm v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg lv]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa dqm v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_load_s_sconf_gen_u width c true pc rd rs1 imm m n v lv b (dqm := dqm)).
  Qed.


  Local Lemma run_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 1)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    run (read_ram rv64d_types.Read_plain (Physaddr addr) 1 false) s
      (w, default_meta) s.
  Proof.
    intros Hdev Hbytes. unfold read_ram. cbn match.
    apply (proj2 (run_bind _ _ _ _ _)). eexists _, s.
    split; [apply run_returnM_fwd|]. cbn beta zeta.
    apply (proj2 (run_bind _ _ _ _ _)). unfold Defs.sail_mem_read. cbn beta zeta.
    eexists _, s. split.
    - eapply run_MemRead_ram_intro; [exact Hdev|intros j Hj; exact (Hbytes j Hj)|apply run_returnM_fwd].
    - cbn match beta. apply run_returnM_fwd.
  Qed.

  Local Lemma exec_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < 1)%N ->
       s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (read_ram rv64d_types.Read_plain (Physaddr addr) 1 false) s = Some ((w, default_meta), s).
  Proof.
    intros Hdev Hbytes.
    apply (run_to_exec _ _ _ _ (run_read_ram_plain_1 addr w s Hdev Hbytes)).
    unfold read_ram. cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
    unfold Defs.sail_mem_read. cbn beta zeta. unfold Defs.bind. cbn [Interface.iMon_bind].
    rewrite exec_MemRead; last exact Hdev. cbn [Interface.ReadReq.pa]. case_match eqn:Hrb.
    - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
    - exfalso. refine (read_bytes_ne (mem s) addr (Z.to_N 1) w _ Hrb).
      intros j Hj. change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
      change (RiscvModelBytes.nth_byte w j) with (nth_byte w j). exact (Hbytes j Hj).
  Qed.

  Local Lemma data2_ext_1_unsigned (v : mword 8) :
    extend_value true v = zero_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.
  (* lbu rd, imm(rs1) -- the width-1 UNSIGNED load, as an instance of
     [wp_load_s_sconf_ugen].  [dqm]-parametric: the byte may be owned outright
     (a stack buffer) or held at [DfracDiscarded] (a read-only image byte out
     of [kernel_data], which is how printint reads the [digits] table). *)
  Lemma wp_lbu_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 8) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    pa ↦ₘ{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦ₘ{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbyte Hcont".
    iApply (wp_load_s_sconf_ugen 1 false pc rd rs1 imm m n v (zero_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_1 (data2_ext_1_unsigned v) Hrd Hrdok
              with "Hcg Hpc Hinstr [Hbyte] [-]").
    { rewrite /wordw_pointsto.
      iSplit; [iPureIntro; change (is_aligned_vaddr (Virtaddr pa) 1 = true);
               unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity | ].
      change (Z.to_nat 1) with 1%nat.
      rewrite big_sepL_singleton pa_add_0 nth_byte0_id. iExact "Hbyte". }
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iEval (rewrite /wordw_pointsto) in "Hbw".
    iDestruct "Hbw" as "(_ & Hbw)".
    iEval (change (Z.to_nat 1) with 1%nat;
           rewrite big_sepL_singleton pa_add_0 nth_byte0_id) in "Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  (* the loaded-value facts: extend_value of the generic data2 = the
     per-width value written to rd. *)
  Lemma data2_ext_8 (v : mword 64) :
    extend_value false v = v.
  Proof. unfold extend_value. apply sign_extend'_id. Qed.

  Lemma data2_ext_4 (v : mword 32) :
    extend_value false v = sign_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  Lemma data2_ext_4_unsigned (v : mword 32) :
    extend_value true v = zero_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  (* lwu rd, imm(rs1) -- the width-4 UNSIGNED load (printk's %u and %x read
     their [uint32] argument with it).  One line off [wp_load_s_sconf_ugen],
     exactly as [wp_lw_s_sconf] is off the signed twin. *)
  Lemma wp_lwu_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) -∗ pa ↦₄{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_ugen 4 false pc rd rs1 imm m n v (zero_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4_unsigned v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_cld_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 8 true pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_ld_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗ pa ↦₈{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 8 false pc rd rs1 imm m n v v b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (data2_ext_8 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_clw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 4 true pc rd rs1 imm m n v (sign_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_lw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 32) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗ pa ↦₄{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen 4 false pc rd rs1 imm m n v (sign_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (data2_ext_4 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.sd rs2, imm(rs1) -- width-8 RVC store.  No register write, so no   *)
  (* rd premises and no [sie_cap] retarget.                               *)
  (* ------------------------------------------------------------------- *)
  (* ------------------------------------------------------------------- *)
  (* The width/RVC-generic store in ATOMIC-UPDATE form (twin of           *)
  (* [wp_load_s_sconf_au]): the caller produces the cell inside the        *)
  (* engine callback's mask and takes the WRITTEN cell back there, so a    *)
  (* lock leaf can open [is_lock] around exactly this step.                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_store_s_sconf_au (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (sv : mword (8*width)) (Ψ : iProp Σ) (Em : coPset) (b : bool) :
    0 < width -> width <= 8 -> vmem_width width ->
    (width | 4096) -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    (* the vmem level writes the value itself now, not the split projection *)
    (autocast (T := mword) (subrange_vec_dec (rget m rs2) (width*8-1) 0)
     : mword (8*width)) = sv ->
    (* see [wp_load_s_sconf_au]: the absorb runs with the accessor open *)
    ↑kptN ⊆ Em ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword (8*width),
       wordw_pointsto width pa (DfracOwn 1) vold ∗
       (wordw_pointsto width pa (DfracOwn 1) sv ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv HkptEm pa.
    set (wlast := (Z.to_nat width - 1)%nat).
    assert (Hwn : Z.of_nat wlast = width - 1) by (unfold wlast; rewrite Nat2Z.inj_sub; [ rewrite Z2Nat.id; lia | lia ]).
    assert (Hwlt : (wlast < Z.to_nat width)%nat) by (unfold wlast; lia).
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_instr_s_sconf m n b pc c
              (STORE (imm, Regidx rs2, Regidx rs1, width))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* open the caller's atomic update: the cell, and how to give it back *)
    iMod "HAU" as (vold) "[Hbw Hcl]".
    iEval (rewrite /wordw_pointsto) in "Hbw".
    iDestruct "Hbw" as "(%Hpalign & Hbytes)".
    assert (Halign : is_aligned_vaddr (Virtaddr pa) width = true) by exact Hpalign.
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa width Hw0 Hwdvd Halign) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hms2 : rf_to_gmap (tp_pin m) !! Regidx rs2 = Some (tp_pin m !!! Regidx rs2))
      by (apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if c then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if c then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m !!! Regidx rs2) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform strans_regime (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb strans_regime (Store Data) pa (pa_of ppn pa) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' Hid _ with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [exact HkptEm |].
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    assert (Hoff' : (bv_unsigned (subrange_vec_dec pa 11 0) + Z.of_nat (Z.to_nat width) <= 4096)%Z)
      by (rewrite Z2Nat.id; [ exact Hoff | lia ]).
    iDestruct (s_mem_chunk s_tr pa pa 0 (Z.to_nat width) (Z.to_nat width) (nth_byte vold) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff' Hcan
                 with "Hmem Hk Hbytes") as %(_ & Hram0 & Hraml & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn pa) width
               (pma_access_ram_at (pa_of ppn pa) width wlast Hwn Hram0 Hraml
                  (pma_width_le width 8 Hw0 Hw8 eq_refl))) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + width <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat wlast < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. rewrite Hwn. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) wlast Hnw) as Heq.
      fold wlast in Hraml.
      destruct Hraml as [_ Hhil]. rewrite Heq in Hhil. rewrite Hwn in Hhil.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) width s_tr (addr_is_ram_not_in_clint _ Hram0) Hw0) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) width s_tr (addr_is_ram_not_in_sig _ Hram0) Hw0) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn pa) width s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, width))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn pa) (Z.to_N width) sv)
                              s_tr.(mdev))).
    {
      pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) width Hw0 Huintw Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_w_gpr_S_walk_pt width Hw0 Hw8 Hvw Hwrite_plain rs2 rs1 imm region_st s_pc s_tr (pa_of ppn pa) md0
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign)
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               HA0 Hord0
               Hrange_st HW
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn pa width Hw0 Hwdvd Halign)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite Lv2 in H0.
      rewrite Hsv in H0.
      exact H0. }
    iMod (wordw_pointsto_write_c width s_tr.(mem) pa ppn vold sv Hw0 Hcan Hoff with "Hk Hmem [Hbytes]")
      as "[Hmem Hbytes]".
    { rewrite /wordw_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign. }
    (* hand the WRITTEN cell back and collect the caller's payload *)
    iMod ("Hcl" with "Hbytes") as "HPsi".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) (Z.to_N width) sv) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) (Z.to_N width) sv) s_tr.(mdev)).(sregs)
             = add_vec_int pc (if c then 2 else 4)).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap m n b p) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc] HPsi").
    iPureIntro. done.
  Qed.


  (* the non-atomic instance: the caller owns the cell throughout. *)
  Lemma wp_store_s_sconf_gen (width : Z) (c : bool) (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold sv : mword (8*width)) (b : bool) :
    0 < width -> width <= 8 -> vmem_width width ->
    (width | 4096) -> uint (to_bits 64 width) = width ->
    (forall (addr : mword 64) (data : mword (8*width)) s,
       dev_addr addr = false ->
       exec (write_ram rv64d_types.Write_plain (Physaddr addr) width data tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) data) s.(mdev))) ->
    (* the vmem level writes the value itself now, not the split projection *)
    (autocast (T := mword) (subrange_vec_dec (rget m rs2) (width*8-1) 0)
     : mword (8*width)) = sv ->
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc c (STORE (imm, Regidx rs2, Regidx rs1, width)) -∗
    wordw_pointsto width pa (DfracOwn 1) vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      wordw_pointsto width pa (DfracOwn 1) sv -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv pa.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_au width c pc rs2 rs1 imm m n sv
              (wordw_pointsto width pa (DfracOwn 1) sv) (⊤ ∖ ↑minstretN) b
              Hw0 Hw8 Hvw Hwdvd Huintw Hwrite_plain Hsv
              ltac:(solve_ndisj) with "Hcg Hpc Hinstr [Hbytes]").
    { iModIntro. iExists vold. iFrame "Hbytes". iIntros "Hb". by iModIntro. }
    iIntros (CID1 Hs1) "Hcg Hpc Hbw".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc Hbw").
    iPureIntro. exact Hs1.
  Qed.

  Lemma store_ext_8 (r : mword 64) :
    (autocast (T := mword) (subrange_vec_dec r (8*8-1) 0) : mword (8*8)) = r.
  Proof. apply (subrange_full_gen_cast 64 r ltac:(lia)). Qed.

  Lemma autocast_subrange32_id (d : mword 32) :
    autocast (T := mword) (subrange_vec_dec d (8*(0+1)*4-1) (8*0*4)) = d.
  Proof.
    change (8*(0+1)*4-1) with 31. change (8*0*4) with 0.
    unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
    apply bv_eq. rewrite autocast_id.
    unfold to_word_idx, to_word, get_word, MachineWord.slice.
    rewrite MachineWord.cast_idx_refl.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned.
  Qed.

  Lemma store_ext_4 (r : mword 64) :
    (autocast (T := mword) (subrange_vec_dec r (4*8-1) 0) : mword (8*4)) = trunc32 r.
  Proof. unfold trunc32. reflexivity. Qed.

  Lemma wp_csd_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := rget m rs2 in
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 8 true pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  Lemma wp_sd_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := rget m rs2 in
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗ pa ↦₈ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 8 false pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_csw_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (rget m rs2) in
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 2) -∗ pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 4 true pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  Lemma wp_sw_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 32) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc32 (rget m rs2) in
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗ pa ↦₄ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 4 false pc rs2 rs1 imm m n vold storeval b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* ld / sd -- the base-encoding width-8 pair: identical to the RVC      *)
  (* exemplars up to the fetch width (4-byte advance).                    *)
  (* ------------------------------------------------------------------- *)



  (* ------------------------------------------------------------------- *)
  (* c.lw / c.sw / lw / sw -- the width-4 quartet (lw sign-extends; the   *)
  (* stored word is trunc32 of rs2, definitionally the model's storeval). *)
  (* ------------------------------------------------------------------- *)










  (* ------------------------------------------------------------------- *)
  (* sb -- the width-1 RAM byte store (no alignment premise; the stored  *)
  (* byte is trunc8 of rs2, definitionally the model's storeval).        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma avi0_mul1 (a : mword 64) : add_vec_int a (0 * 1) = a.
  Proof. change (0 * 1)%Z with 0%Z. apply avi0. Qed.

  Local Lemma is_aligned_vaddr_1 (vaddr : virtaddr) : is_aligned_vaddr vaddr 1 = true.
  Proof. destruct vaddr as [addr]. unfold is_aligned_vaddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Local Lemma is_aligned_paddr_1 (paddr : physaddr) : is_aligned_paddr paddr 1 = true.
  Proof. destruct paddr as [addr]. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Definition trunc8 (w : mword 64) : mword 8 :=
    autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 1 8) 1) 0).

  (* the byte an [sb] writes when its source register was filled by an [lbu]:
     the store leaf truncates to 8 bits what the load leaf zero-extended to
     64.  Every byte-copy loop needs this (memmove, copyinstr), so it lives
     next to [trunc8] rather than in each proof. *)
  Lemma trunc8_zext8 (b : mword 8) : trunc8 (zero_extend' 64 b) = b.
  Proof.
    apply bv_eq. unfold trunc8. rewrite autocast_id.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    rewrite bv_extract_0_unsigned.
    cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
         MachineWord.MachineWord.zero_extend].
    rewrite bv_zero_extend_unsigned; [| vm_compute; discriminate].
    change (MachineWord.Z_idx 8) with 8%N.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  (* ...and the byte it writes when its source register is x0: copyinstr's
     [sb zero,0(a5)], the store that plants the string terminator. *)
  Lemma trunc8_zero : trunc8 (zero_reg : mword 64) = (mword_of_int 0 : mword 8).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma wp_sb_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 8) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc8 (rget m rs2) in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    pa ↦ₘ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦ₘ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbyte Hcont".
    iApply (wp_instr_s_sconf m n b pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 1))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    (* the byte's OWN claim + canonicality + region (refold to keep) *)
    iDestruct (mem_pointsto_acc with "Hbyte") as (ppn) "(#Hk & %Hcan & %Hram0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hbyte".
    destruct (pma_all_ram Hpma_all (pa_of ppn pa) 1
               (pma_access_ram_byte (pa_of ppn pa) Hram0)) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    assert (Hms2 : rf_to_gmap (tp_pin m) !! Regidx rs2 = Some (tp_pin m !!! Regidx rs2))
      by (apply rf_to_gmap_lookup).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 1 <= ram_base + ram_size)%Z)
      by (destruct Hram0 as [_ Hh]; unfold ram_base, ram_size in *; lia).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms2 with "Hfmap") as "[Hs2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (tp_pin m !!! Regidx rs2) s_pc with "Hreg Hs2c") as %Lv2.
    iDestruct ("Hfb2" with "Hs2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform strans_regime (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb strans_regime (Store Data) pa (pa_of ppn pa) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' Hid _ with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false (pa_of ppn pa) 1 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 1 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn pa) 1 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn pa) 1 storeval)
                              s_tr.(mdev))).
    { pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 1 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_1_gpr_S_walk_pt rs2 rs1 imm region_st s_pc s_tr (pa_of ppn pa)
                    Htea
                    ltac:(apply is_aligned_vaddr_1)
                    md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
                    ltac:(rewrite Lva subrange_id sign_extend'_id; exact Htr_pc)
                    Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                    HA0 Hord0
                    Hrange_st
                    HW
                    ltac:(rewrite Lpma_tr; exact Hmatch_st0)
                    Hwrite_st Hwc Hws Hwh
                    (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite Lv2 in H0.
      exact H0. }
    iMod (mem_pointsto_write_c s_tr.(mem) pa ppn vold storeval Hcan with "Hk Hmem Hbyte") as "[Hmem Hbyte]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 1 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 1 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite nth_byte0_id) in "Hbyte".
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap m n b p) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc] Hbyte").
    iPureIntro. done.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* c.ldsp / c.sdsp -- the sp-relative immediate forms, bridged onto     *)
  (* the c.ld / c.sd leaves by [sext9_12_64] (pure immediate rewrite).    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cldsp_s_sconf
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : regfile) (n : nat) (v : mword 64) (b : bool) {dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg v]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm pa Hrd Hrdok.
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_cld_s_sconf pc rd csp_rs1 imm m n v b (dqm:=dqm) Hrd Hrdok).
  Qed.

  (* THE SIDE CONDITION ARRIVES BY INSTANCE RESOLUTION, NOT AS A PREMISE.
     [rget m rs2] is a lookup in [tp_pin m], so the stored value as spelled
     here depends on the ambient hart at exactly one register, rs2 = tp.  Once
     the funnel's σ-callback moves inside [wp_next] the obligation arrives at
     the hart the trap returned TO, while this statement was elaborated at the
     hart we came FROM, and the two agree only away from tp.  This leaf has no
     [rd_ok]/[ops_ok] slot to widen -- a c.sdsp writes no register, so it has
     no pure premises at all -- and it is referenced ~640 times, so an ordinary
     premise would move every one of those call sites.  [IntrDefs.SrcOk] is
     that same side condition delivered as an IMPLICIT class argument: it
     occupies no positional slot, so no call site changes.

     THE STORED VALUE STAYS SPELLED [rget m rs2], at the ENTRY hart, and that
     is deliberate -- see this file's header.  The tempting alternative, making
     the statement literally hart-free as [m !!! Regidx rs2], was MEASURED and
     rejected: it breaks 99 consumer files, because a caller normalises the
     value it gets back with an [iEval (rgne)] / [rewrite H] whose LHS is a
     [rget], and those have nothing to match once the [rget] is gone.  So the
     class carries the side condition and the SPELLING does not move.

     LANDED AHEAD OF ITS CONSUMER, exactly as [IntrDefs.src_ok] was, and for
     the same reason: nothing here needs the reconciliation until the funnel's
     σ-callback moves inside [wp_next] and the obligation starts arriving at
     the rebound hart.  What the class buys is proved, not asserted -- see
     [IntrDefs.src_ok_rget_all] / [src_ok_rget_indep] -- and the point of
     landing it now is that adding it costs ZERO of this leaf's 672 references,
     so the funnel change is not entangled with a 672-site sweep. *)
  Lemma wp_csdsp_s_sconf
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5) `{!SrcOk rs2}
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let pa := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let storeval := rget m rs2 in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 2) -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm pa storeval.
    (* WHAT THE CLASS WILL DO HERE, recorded as a proved fact rather than a
       comment: the value this leaf promises is hart-independent, so the
       promise made at the entry hart is still the promise at the hart a trap
       returned to.  That is the ONE step the funnel change needs, and
       [SrcOk rs2] is its whole content.  It is stated and not yet used because
       today's σ-callback is still instantiated at the entry hart -- the
       reconciliation has no gap to close until [wp_instr_s_sconf]'s callback
       moves inside [wp_next].  (At a VARIABLE [rs2] this is not a conversion:
       the pin's [bool_decide] cannot reduce, so without the class there is no
       proof of it at all.) *)
    assert (Hsv_all : forall c : CpuId, rget (CID := c) m rs2 = storeval)
      by (intros c; exact (src_ok_rget_indep m rs2 c CID)).
    unfold pa.
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    exact (wp_csd_s_sconf pc rs2 csp_rs1 imm m n vold b).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* sd zero, imm(rs1) -- release's unconditional zero store.             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sd_zero_s_sconf
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 64) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := (zero_reg : mword 64) in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iDestruct (word_pointsto_aligned_p with "Hbytes") as %Hpalign4.
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 8 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf m n b pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    (* the word's OWN base claim + canonicality (peek byte 0 of its bytes) *)
    iDestruct (word_pointsto_bytes with "Hbytes") as "Hb".
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hb") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hb".
    pose proof (off_bound_div pa 8 ltac:(lia) ltac:(exists 512; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform strans_regime (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb strans_regime (Store Data) pa (pa_of ppn pa) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' Hid _ with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (s_mem_chunk s_tr pa pa 0 8 8 (nth_byte vold) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hb") as %(_ & Hram0 & Hram7 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn pa) 8
               (pma_access_ram (pa_of ppn pa) 8 7 Hram0 Hram7 (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 7 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (8 - 1)) with (pa_add (pa_of ppn pa) 7) in Hram7.
      destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 8 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 8 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn pa) 8 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn pa) 8 storeval)
                              s_tr.(mdev))).
    {
      pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_8_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr (pa_of ppn pa)
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               Hrange_st HW
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn pa 8 ltac:(lia) ltac:(exists 512; lia) Halign4)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iDestruct (word_pointsto_intro pa (DfracOwn 1) vold Hpalign4 with "Hb") as "Hbytes".
    iMod (word_pointsto_write_c s_tr.(mem) pa ppn vold storeval Hcan Hoff with "Hk Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 8 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 8 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap m n b p) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc] Hbytes").
    iPureIntro. done.
  Qed.

  (* c.sw x0 store (width-4 sibling of wp_sd_zero_s_sconf); moved here from
     ProofInitlock.v -- a store leaf belongs in the leaf file. *)
  Lemma wp_sw_zero_s_sconf
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (vold : bv 32) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := (mword_of_int 0 : mword 32) in
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf m n b pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : rf_to_gmap (tp_pin m) !! Regidx rs1 = Some (tp_pin m !!! Regidx rs1))
      by (apply rf_to_gmap_lookup).
    (* the word's OWN base claim + canonicality (peek byte 0, refold to keep) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & %Hid & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (tp_pin m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iDestruct (sr_transform strans_regime (Store Data)
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (sign_extend' 64 imm))
                 s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
    unshelve iMod (sr_absorb strans_regime (Store Data) pa (pa_of ppn pa) ppn KP_rw s_pc _
            (or_intror (or_intror (or_introl eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' Hid _ with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte vold) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(_ & Hram0 & Hram3 & Hkd).
    destruct (pma_all_ram Hpma_all (pa_of ppn pa) 4
               (pma_access_ram (pa_of ppn pa) 4 3 Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl)
                  eq_refl eq_refl)) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval)
                              s_tr.(mdev))).
    { pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
      pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr (pa_of ppn pa)
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA0 Hord0
               Hrange_st HW
               ltac:(rewrite Lpma_tr; exact Hmatch_st0)
               (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halign4)
               Hwrite_st Hwc Hws Hwh
               (addr_is_ram_not_dev _ Hram0)) as H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) vold Hpalign4 with "Hbytes") as "Hbytes".
    iMod (word4_pointsto_write_c s_tr.(mem) pa ppn vold storeval Hcan Hoff with "Hk Hmem Hbytes")
      as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw"; [ iExact "Hbytes" |].
    iAssert (sconf) with "[Hpriv Hms Hhalf Hspp Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf Hspp".
      { iExists ms0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap m n b p) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    iAssert (gpr_file (tp_pin m)) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc] Hbw").
    iPureIntro. done.
  Qed.


End WpSconfMem.
