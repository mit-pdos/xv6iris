(* VcGenS.v -- the S-MODE instantiation of the straight-line VCgen (VcGen.v).

   Same idea as the M-mode [wp_vc_block]: a deep-embedded symbolic executor
   whose successful run (checked by [vm_compute]) yields, through ONE
   generic Iris lemma, the WP of a whole straight-line block.  The
   differences from the M-mode version are dictated by the S-mode leaf WPs
   (wp_caddi_gpr_s_config / wp_caddi4spn_gpr_s_config / wp_csdsp_gpr_s_ram /
   wp_cldsp_gpr_s_ram):

     - the instruction alphabet [vop_s] mirrors the RVC SHAPES those leaves
       are stated for (c.addi / c.addi4spn / c.sdsp / c.ldsp -- exactly the
       prologue/epilogue instructions of the kernel's S-mode functions),
       with the immediate FORMS baked in so the leaf ASTs match up
       syntactically;
     - the fixed context threaded through every step is the S-mode machine
       configuration (Supervisor privilege, mstatus/mie/mideleg/menvcfg,
       the PMP TOR-covers-RAM geometry, and the [tlb_inv root_ppn]
       identity-translation invariant) instead of [mmode_config];
     - all loads/stores are sp-relative 8-byte accesses (that is all the
       S-mode RVC-shape leaves cover today).

   The symbolic state, heap, and register denotation are shared with
   VcGen.v ([vstate] / [vheap_own] / [vregs_den] / [sval]).  See
   WpMycpuVc.v / WpPopOffVc.v for this VCgen applied to mycpu() and
   pop_off(). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
Require Import WpGprAddi WpGprLogic WpGprLui WpGprLoad WpGprStore WpGprRvc.
Require Import WpEntryNew WpSpinNew SmodeCore WpSmodeGpr WpMemsetS WpPushOff WpPushOffMem.
Require Import VcGen.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The S-mode instruction alphabet.                                     *)
(* ====================================================================== *)

Inductive vop_s : Type :=
  | VScaddi (imm : mword 6) (rd : mword 5)                    (* c.addi rd, imm       *)
  | VScaddi4spn (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
                                                              (* addi rd, sp, nz*4    *)
  | VScsdsp (uimm : mword 6) (rs2 : mword 5)                  (* sd rs2, uimm*8(sp)   *)
  | VScldsp (uimm : mword 6) (rd : mword 5)                   (* ld rd, uimm*8(sp)    *)
  | VSclw (imm : mword 12) (rs1 rd : mword 5)                 (* lw rd, imm(rs1)      *)
  | VScsw (imm : mword 12) (rs2 rs1 : mword 5)                (* sw rs2, imm(rs1)     *)
  | VScaddiw (imm : mword 6) (rd : mword 5).                  (* c.addiw rd, imm      *)

(* the TARGET AST of each shape, exactly as the S-mode leaves state it. *)
Definition vop_s_ast (op : vop_s) : instruction :=
  match op with
  | VScaddi imm rd =>
      ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)
  | VScaddi4spn rdc nzimm rd =>
      ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)
  | VScsdsp uimm rs2 =>
      STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)
  | VScldsp uimm rd =>
      LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)
  | VSclw imm rs1 rd =>
      LOAD (imm, Regidx rs1, Regidx rd, false, 4)
  | VScsw imm rs2 rs1 =>
      STORE (imm, Regidx rs2, Regidx rs1, 4)
  | VScaddiw imm rd =>
      ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)
  end.

(* the sp-relative byte offset of a c.sdsp/c.ldsp (canonical Z). *)
Definition zoff6 (uimm : mword 6) : Z :=
  uint (zero_extend' 64 (concat_vec uimm ('b"000")) : mword 64).

(* ====================================================================== *)
(* 2. The symbolic executor (state shared with the M-mode VCgen).          *)
(*    All four shapes are RVC, so every step advances the pc by 2.         *)
(* ====================================================================== *)

Definition vc_step_s (st : vstate) (op : vop_s) : option vstate :=
  let pc' := st.(vpc) + 2 in
  match op with
  | VScaddi imm rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rd with
      | Some v =>
          if sval_is64 v then
            Some (VSt pc'
                    (<[Regidx rd := sval_addZ v (zimm12 (sign_extend' 12 imm))]>
                       st.(vregs))
                    st.(vheap) st.(vheap4))
          else None
      | None => None
      end
  | VScaddi4spn rdc nzimm rd =>
      if negb (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) then None else
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx csp_rs1 with
      | Some v =>
          if sval_is64 v then
            Some (VSt pc'
                    (<[Regidx rd := sval_addZ v (zimm12 (caddi4spn_imm nzimm))]>
                       st.(vregs))
                    st.(vheap) st.(vheap4))
          else None
      | None => None
      end
  | VScsdsp uimm rs2 =>
      match st.(vregs) !! Regidx csp_rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zoff6 uimm) in
          match vheap_find st.(vheap) a with
          | Some (i, _) =>
              Some (VSt pc' st.(vregs) (<[i := (a, v2)]> st.(vheap)) st.(vheap4))
          | None => None
          end
      | _, _ => None
      end
  | VScldsp uimm rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx csp_rs1 with
      | Some v1 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zoff6 uimm) in
          match vheap_find st.(vheap) a with
          | Some (_, v) =>
              Some (VSt pc' (<[Regidx rd := v]> st.(vregs)) st.(vheap) st.(vheap4))
          | None => None
          end
      | None => None
      end
  | VSclw imm rs1 rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rs1 with
      | Some v1 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zimm12 imm) in
          match vheap_find st.(vheap4) a with
          | Some (_, w) =>
              Some (VSt pc' (<[Regidx rd := S32 w]> st.(vregs)) st.(vheap) st.(vheap4))
          | None => None
          end
      | None => None
      end
  | VScsw imm rs2 rs1 =>
      match st.(vregs) !! Regidx rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zimm12 imm) in
          match vheap_find st.(vheap4) a with
          | Some (i, _) =>
              Some (VSt pc' st.(vregs) st.(vheap)
                        (<[i := (a, sval_trunc32 v2)]> st.(vheap4)))
          | None => None
          end
      | _, _ => None
      end
  | VScaddiw imm rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rd with
      | Some v =>
          Some (VSt pc'
                  (<[Regidx rd := S32 (sval32_addZ (sval_trunc32 v) (zimm32 imm))]>
                     st.(vregs))
                  st.(vheap) st.(vheap4))
      | None => None
      end
  end.

Fixpoint vc_block_s (st : vstate) (prog : list vop_s) : option vstate :=
  match prog with
  | nil => Some st
  | op :: rest =>
      match vc_step_s st op with
      | Some st1 => vc_block_s st1 rest
      | None => None
      end
  end.

(* ====================================================================== *)
(* Register AGREEMENT: the fast interface between a block's (PARTIAL)      *)
(* symbolic register map and the surrounding proof's abstract [gpr_file m].*)
(* A client seeds [vr] with just the registers the block touches or that   *)
(* it wants to observe across the block; [gpr_file m] is never rewritten.  *)
(* ====================================================================== *)
Definition gpr_matches (ρ : nat -> mword 64) (vr : gmap regidx sval)
    (m : gmap regidx (mword 64)) : Prop :=
  forall r sv, vr !! r = Some sv -> m !!! r = sval_den ρ sv.

Lemma gpr_matches_empty (ρ : nat -> mword 64) (m : gmap regidx (mword 64)) :
  gpr_matches ρ ∅ m.
Proof. intros r sv H. rewrite lookup_empty in H. discriminate. Qed.

(* seed one register (client-side, at block entry). *)
Lemma gpr_matches_ins (ρ : nat -> mword 64) (vr : gmap regidx sval)
    (m : gmap regidx (mword 64)) (r : regidx) (sv : sval) :
  m !!! r = sval_den ρ sv ->
  gpr_matches ρ vr m ->
  gpr_matches ρ (<[r := sv]> vr) m.
Proof.
  intros He Hm r' sv' H. destruct (decide (r' = r)) as [->|Hne].
  - rewrite lookup_insert in H. injection H as <-. exact He.
  - rewrite lookup_insert_ne in H;
      [exact (Hm _ _ H)|intro Heq; apply Hne; symmetry; exact Heq].
Qed.

(* a register write preserves agreement (engine-side, per step). *)
Lemma gpr_matches_insert (ρ : nat -> mword 64) (vr : gmap regidx sval)
    (m : gmap regidx (mword 64)) (r : regidx) (sv : sval) (w : mword 64) :
  w = sval_den ρ sv ->
  gpr_matches ρ vr m ->
  gpr_matches ρ (<[r := sv]> vr) (<[r := w]> m).
Proof.
  intros -> Hm r' sv' H. destruct (decide (r' = r)) as [->|Hne].
  - rewrite lookup_insert in H. injection H as <-. apply lookup_total_insert.
  - rewrite lookup_insert_ne in H;
      [|intro Heq; apply Hne; symmetry; exact Heq].
    rewrite lookup_total_insert_ne;
      [exact (Hm _ _ H)|intro Heq; apply Hne; symmetry; exact Heq].
Qed.

Section VcGenSIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* 4-byte (word) cells: the [word_pointsto] analogue for lw/sw.  Both   *)
  (* alignment forms travel with the ownership, exactly as ↦₈ does, so    *)
  (* the wrappers below need no per-address side conditions.              *)
  (* ------------------------------------------------------------------ *)
  Definition word4_pointsto (a : mword 64) (w : mword 32) : iProp Σ :=
    (⌜is_aligned_vaddr (Virtaddr a) 4 = true⌝ ∗
     ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ nth_byte w j)%I.

  (* wp_clw_s with the ten slot-geometry hypotheses DERIVED from the cell's
     RAM-ness + alignment (the [ram_*] lemmas), mirroring
     [wp_cldsp_gpr_s_ram]. *)
  Lemma wp_clw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    word4_pointsto ea v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) -∗
      word4_pointsto ea v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hval4 & %Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add ea 3)⌝)%I as %Hr3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint ea)%Z) by (destruct Hr0 as [H _]; exact H).
    assert (Hfit : (uint ea + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint ea + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hr0 as [_ Hh]. unfold ram_base, ram_size in Hh.
        change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add ea 3 Hnw) as Heq.
      destruct Hr3 as [_ Hhi3]. rewrite Heq in Hhi3.
      change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    iApply (wp_clw_s root_ppn E Φ pc rd rs1 imm (svpn_of ea) m v
              mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq) (dqm:=DfracOwn 1)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              Hval4 Hpal4
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbytes [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbytes".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile [Hbytes]").
    rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact (conj Hval4 Hpal4).
  Qed.

  (* wp_csw_s, same treatment.  The stored word is [trunc32 rs2]. *)
  Lemma wp_csw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    word4_pointsto ea vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      word4_pointsto ea (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hval4 & %Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add ea 3)⌝)%I as %Hr3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint ea)%Z) by (destruct Hr0 as [H _]; exact H).
    assert (Hfit : (uint ea + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint ea + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hr0 as [_ Hh]. unfold ram_base, ram_size in Hh.
        change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add ea 3 Hnw) as Heq.
      destruct Hr3 as [_ Hhi3]. rewrite Heq in Hhi3.
      change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    iApply (wp_csw_s root_ppn E Φ pc rs2 rs1 imm (svpn_of ea) m vold
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              Hval4 Hpal4
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbytes [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbytes".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile [Hbytes]").
    rewrite /word4_pointsto /trunc32. iFrame "Hbytes".
    iPureIntro. exact (conj Hval4 Hpal4).
  Qed.

  (* one fully-owned 4-byte points-to per word cell. *)
  Definition vheap4_own (ρ : nat -> mword 64) (h : list (sval * sval32)) : iProp Σ :=
    ([∗ list] c ∈ h, word4_pointsto (sval_den ρ c.1) (sval32_den ρ c.2))%I.

  (* the block's code: one RVC [instr] fact per entry, at consecutive pcs. *)
  Fixpoint block_instrs_s (pc : Z) (prog : list vop_s) : iProp Σ :=
    match prog with
    | nil => emp%I
    | op :: rest =>
        (instr (mword_of_int pc) true (vop_s_ast op) ∗
         block_instrs_s (pc + 2) rest)%I
    end.

  (* expose gpr_file's dom-completeness fact without consuming it. *)
  Lemma gpr_file_dom (m : gmap regidx (mword 64)) :
    gpr_file m -∗ ⌜ forall r : regidx, r ∈ dom m ⌝ ∗ gpr_file m.
  Proof.
    iIntros "[%Hdom Hmap]".
    iSplitR; [iPureIntro; exact Hdom|].
    iSplitR; [iPureIntro; exact Hdom|].
    iExact "Hmap".
  Qed.

  (* ================================================================== *)
  (* THE lemma: one successful symbolic run = one WP for the S-mode      *)
  (* block, under the standard S-mode machine configuration.             *)
  (* ================================================================== *)
  Lemma wp_vc_block_s_den (root_ppn : mword 44) (prog : list vop_s) E
      (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    vc_block_s st prog = Some st' ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file (vregs_den ρ st.(vregs)) -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file (vregs_den ρ st'.(vregs)) -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    revert st. induction prog as [|op rest IH]; intros st Hblk.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
               Hpc Hgpr _ Hheap Hheap4 Hcont".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                            Hpc Hgpr Hheap Hheap4").
    - cbn [vc_block_s] in Hblk.
      destruct (vc_step_s st op) as [st1|] eqn:Hstep;
        rewrite ?Hstep in Hblk; [|discriminate].
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
               Hpc Hgpr [Hi Hbi] Hheap Hheap4 Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                     |imm rs1 rd|imm rs2 rs1|imm rd]; simpl in Hstep.
      + (* VScaddi *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (vpc st)) rd imm
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx rd)
                             (sign_extend' 64 (sign_extend' 12 imm)))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx rd := sval_addZ v1 (zimm12 (sign_extend' 12 imm))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -(sval_den_add_imm ρ v1 (sign_extend' 12 imm) H64).
          apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi4spn *)
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (vpc st))
                  rdc nzimm rd (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrdc Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm nzimm)))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx rd := sval_addZ v1 (zimm12 (caddi4spn_imm nzimm))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -(sval_den_add_imm ρ v1 (caddi4spn_imm nzimm) H64).
          apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsdsp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64).
          rewrite (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rs2
                  (vregs_den ρ (vregs st)) (sval_den ρ vold)
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite (vregs_den_lookup ρ _ _ _ Hrs2) -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScldsp *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64).
          rewrite (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rd
                  (vregs_den ρ (vregs st)) (sval_den ρ vv)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq) (dqm:=DfracOwn 1)
                  HN Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Egpr : <[Regidx rd := regval_into_reg (sval_den ρ vv)]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := vv]> (vregs st))).
        { unfold regval_into_reg. apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSclw *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i w32]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64)
                  (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_clw_s_ram root_ppn E Φ (mword_of_int (vpc st)) rd rs1 imm
                  (vregs_den ρ (vregs st)) (sval32_den ρ w32)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
                  HN Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (sign_extend' 64 (sval32_den ρ w32))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := S32 w32]> (vregs st))).
        { unfold regval_into_reg. rewrite -vregs_den_insert.
          cbn [sval_den]. reflexivity. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsw *)
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i wold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64)
                  (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csw_s_ram root_ppn E Φ (mword_of_int (vpc st)) rs2 rs1 imm
                  (vregs_den ρ (vregs st)) (sval32_den ρ wold)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hsv : trunc32 (vregs_den ρ (vregs st) !!! Regidx rs2)
                      = sval32_den ρ (sval_trunc32 v2)).
        { rewrite sval_trunc32_den (vregs_den_lookup ρ _ _ _ Hrs2). reflexivity. }
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddiw *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (vpc st)) rd imm
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (vregs_den ρ (vregs st) !!! Regidx rd)
                                (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx rd := S32 (sval32_addZ (sval_trunc32 v1) (zimm32 imm))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -vregs_den_insert. cbn [sval_den].
          rewrite sval32_den_addZ.
          rewrite sval_trunc32_den.
          unfold zimm32. rewrite mword_of_int_uint32.
          rewrite -trunc32_add.
          rewrite trunc32_subrange. reflexivity. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
  Qed.


  (* ================================================================== *)
  (* THE lemma, agreement interface: the symbolic register map is        *)
  (* PARTIAL (only the block's touched/observed registers), and it is    *)
  (* related to the surrounding proof's abstract [gpr_file m] by the     *)
  (* pointwise [gpr_matches] fact -- [gpr_file] is never rewritten, and  *)
  (* the continuation receives the stepped file abstractly (∀ mf) with   *)
  (* the post-state agreement.  This is both the cheap-seams and the     *)
  (* cheap-vm_compute interface (small maps normalize in ~ms).           *)
  (* ================================================================== *)
  Lemma wp_vc_block_s (root_ppn : mword 44) (prog : list vop_s) E
      (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : gmap regidx (mword 64),
      ⌜ gpr_matches ρ st'.(vregs) mf ⌝ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE.
    revert st m. induction prog as [|op rest IH]; intros st m Hblk Hmatch.
    - (* empty block *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
               Hpc Hgpr _ Hheap Hheap4 Hcont".
      iApply ("Hcont" $! m with "[//] Hhs Hpriv Hms Hmie Hmdl Hmenv
                                 Htlbinv Hpc Hgpr Hheap Hheap4").
    - cbn [vc_block_s] in Hblk.
      destruct (vc_step_s st op) as [st1|] eqn:Hstep;
        rewrite ?Hstep in Hblk; [|discriminate].
      iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
               Hpc Hgpr [Hi Hbi] Hheap Hheap4 Hcont".
      destruct op as [imm rd|rdc nzimm rd|uimm rs2|uimm rd
                     |imm rs1 rd|imm rs2 rs1|imm rd]; simpl in Hstep.
      + (* VScaddi *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (vpc st)) rd imm m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (sign_extend' 12 imm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (sign_extend' 12 imm) H64).
          reflexivity. }
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi4spn *)
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (vpc st))
                  rdc nzimm rd m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrdc Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
                = sval_den ρ (sval_addZ v1 (zimm12 (caddi4spn_imm nzimm)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (caddi4spn_imm nzimm) H64).
          reflexivity. }
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsdsp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rs2
                  m (sval_den ρ vold)
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite Hm2 -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ _ Hblk Hmatch
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScldsp *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zoff6 uimm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zoff6 uimm))
                      = add_vec (m !!! Regidx csp_rs1)
                                (zero_extend' 64 (concat_vec uimm ('b"000")))).
        { unfold zoff6. rewrite (sval_den_add_off ρ v1 _ H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (vpc st)) uimm rd
                  m (sval_den ρ vv)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq) (dqm:=DfracOwn 1)
                  HN Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv)
          by reflexivity.
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSclw *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i w32]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_clw_s_ram root_ppn E Φ (mword_of_int (vpc st)) rd rs1 imm
                  m (sval32_den ρ w32)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
                  HN Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sign_extend' 64 (sval32_den ρ w32))
                       = sval_den ρ (S32 w32)) by reflexivity.
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsw *)
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap4 st) (sval_addZ v1 (zimm12 imm)))
          as [[i wold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap4_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap4")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_csw_s_ram root_ppn E Φ (mword_of_int (vpc st)) rs2 rs1 imm
                  m (sval32_den ρ wold)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hsv : trunc32 (m !!! Regidx rs2) = sval32_den ρ (sval_trunc32 v2)).
        { rewrite sval_trunc32_den Hm2. reflexivity. }
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iApply (IH _ _ Hblk Hmatch
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddiw *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (vpc st)) rd imm m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                  HN HSIE HMPRV HSXL Hmm HPBMTE Hrd0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (m !!! Regidx rd)
                                (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
                = sval_den ρ (S32 (sval32_addZ (sval_trunc32 v1) (zimm32 imm)))).
        { unfold regval_into_reg. rewrite Hm1.
          cbn [sval_den].
          rewrite sval32_den_addZ.
          rewrite sval_trunc32_den.
          unfold zimm32. rewrite mword_of_int_uint32.
          rewrite -trunc32_add.
          rewrite trunc32_subrange. reflexivity. }
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
  Qed.

End VcGenSIris.
