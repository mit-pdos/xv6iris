(* VcGenS.v -- the S-MODE instantiation of the straight-line VCgen (VcGen.v).

   Same idea as the M-mode [wp_vc_block]: a deep-embedded symbolic executor
   whose successful run (checked by [vm_compute]) yields, through ONE
   generic Iris lemma, the WP of a whole straight-line block.  The
   differences from the M-mode version are dictated by the S-mode leaf WPs
   (wp_caddi_gpr_s_config_pt / wp_caddi4spn_gpr_s_config_pt / wp_csdsp_gpr_s_pt /
   wp_cldsp_gpr_s_pt):

     - the instruction alphabet [vop_s] mirrors the RVC SHAPES those leaves
       are stated for (c.addi / c.addi4spn / c.sdsp / c.ldsp -- exactly the
       prologue/epilogue instructions of the kernel's S-mode functions),
       with the immediate FORMS baked in so the leaf ASTs match up
       syntactically;
     - the fixed context threaded through every step is the S-mode machine
       configuration (Supervisor privilege, mstatus/mie/mideleg/menvcfg,
       the PMP TOR-covers-RAM geometry, and the [tlb_res_pt root_ppn]
       identity-translation invariant) instead of [mmode_config];
     - all loads/stores are sp-relative 8-byte accesses (that is all the
       S-mode RVC-shape leaves cover today).

   The symbolic state, heap, and register denotation are shared with
   VcGen.v ([vstate] / [vheap_own] / [vregs_den] / [sval]).  See
   CodeMycpu.v / CodePopOff.v for this VCgen applied to mycpu() and
   pop_off(). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec WpGpr.
Require Import RegFile.
Require Import MinstretInv InstrBytes.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import VcGen.
Require Import KptShare.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype.
Require Import WpSmodePtMem WpSmodePtMemWrap.
From iris.base_logic.lib Require Import invariants.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
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
  | VScaddiw (imm : mword 6) (rd : mword 5)                   (* c.addiw rd, imm      *)
  | VSsd (rvc : bool) (imm : mword 12) (rs2 rs1 : mword 5)    (* [c.]sd rs2, imm(rs1) *)
  | VSld (rvc : bool) (imm : mword 12) (rs1 rd : mword 5)     (* [c.]ld rd, imm(rs1)  *)
  | VScaddi16sp (imm6 : mword 6).                             (* c.addi16sp sp, imm6  *)

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
  | VSsd _ imm rs2 rs1 =>
      STORE (imm, Regidx rs2, Regidx rs1, 8)
  | VSld _ imm rs1 rd =>
      LOAD (imm, Regidx rs1, Regidx rd, false, 8)
  | VScaddi16sp imm6 =>
      ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)
  end.

(* per-op fetch width: all the RVC shapes are 2 bytes; the base [sd]/[ld]
   general 8-byte accesses carry their own [rvc] flag (c.sd/c.ld -> 2, the
   full-width base sd/ld -> 4).  Used by [block_instrs_s] / [vc_step_s]. *)
Definition vop_s_rvc (op : vop_s) : bool :=
  match op with VSsd b _ _ _ => b | VSld b _ _ _ => b | _ => true end.
Definition vop_s_w (op : vop_s) : Z :=
  match op with
  | VSsd b _ _ _ => (if b then 2 else 4)
  | VSld b _ _ _ => (if b then 2 else 4)
  | _ => 2
  end.

(* the sp-relative byte offset of a c.sdsp/c.ldsp (canonical Z). *)
Definition zoff6 (uimm : mword 6) : Z :=
  uint (zero_extend' 64 (concat_vec uimm ('b"000")) : mword 64).

(* ====================================================================== *)
(* 2. The symbolic executor (state shared with the M-mode VCgen).          *)
(*    All four shapes are RVC, so every step advances the pc by 2.         *)
(* ====================================================================== *)

(* [is_tp r]: the executor's gate against a variable register operand being
   [tp] (x4, [HartTp.Rtp]).

   [tp] is PINNED to the hart (HartTp.v): a register-file resource held at
   hart [CID] owns [tp] at [cid_word_of cpu_id], so the value the hardware
   reads at x4 is [rget m 4], NOT [m !!! Regidx 4], and a write to x4 would
   falsify the pin outright.  [gpr_matches] below -- the executor's ONLY
   interface to a surrounding proof's register file -- relates the block's
   symbolic map to the PLAIN file [m], so at [r = tp] the symbolic value and
   the value the machine actually reads can disagree.  The executor
   therefore REJECTS every opcode whose variable register operand (source
   OR destination) is x4; [uint rd <> 0] was the only operand gate before
   the pin existed.

   This can only make the executor MORE conservative: a block that touches
   tp fails to run, it is never mis-run.  Downstream, [is_tp_false] is what
   feeds a tp-excluding leaf premise ([IntrDefs.rd_ok], or an [rget]-spelled
   value premise via [HartTp.rget_ne]).

   Spelled with [Z.eqb (uint _)] to match the neighbouring [uint rd <> 0]
   gate: that form is what survives the [simpl in Hstep] of every branch of
   the proofs below without unfolding. *)
Definition is_tp (r : mword 5) : bool := Z.eqb (uint r) 4.

(* [Regidx (mword_of_int 4 : mword 5)] IS [Regidx Rtp] (HartTp's [Rtp] is a
   notation for that literal), so this conclusion needs no bridge. *)
Lemma is_tp_false (r : mword 5) :
  is_tp r = false -> Regidx r <> Regidx (mword_of_int 4 : mword 5).
Proof.
  unfold is_tp. intros H Heq. apply Z.eqb_neq in H.
  injection Heq as Hr. subst r. apply H. vm_compute. reflexivity.
Qed.

Definition vc_step_s (st : vstate) (op : vop_s) : option vstate :=
  let pc' := st.(vpc) + vop_s_w op in
  match op with
  | VScaddi imm rd =>
      if is_tp rd then None else
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
      if is_tp rd then None else
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
      if is_tp rs2 then None else
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
      if is_tp rd then None else
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
      if orb (is_tp rd) (is_tp rs1) then None else
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
      if orb (is_tp rs1) (is_tp rs2) then None else
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
      if is_tp rd then None else
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rd with
      | Some v =>
          Some (VSt pc'
                  (<[Regidx rd := S32 (sval32_addZ (sval_trunc32 v) (zimm32 imm))]>
                     st.(vregs))
                  st.(vheap) st.(vheap4))
      | None => None
      end
  | VSsd _ imm rs2 rs1 =>
      if orb (is_tp rs1) (is_tp rs2) then None else
      match st.(vregs) !! Regidx rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zimm12 imm) in
          match vheap_find st.(vheap) a with
          | Some (i, _) =>
              Some (VSt pc' st.(vregs) (<[i := (a, v2)]> st.(vheap)) st.(vheap4))
          | None => None
          end
      | _, _ => None
      end
  | VSld _ imm rs1 rd =>
      if orb (is_tp rd) (is_tp rs1) then None else
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rs1 with
      | Some v1 =>
          if negb (sval_is64 v1) then None else
          let a := sval_addZ v1 (zimm12 imm) in
          match vheap_find st.(vheap) a with
          | Some (_, v) =>
              Some (VSt pc' (<[Regidx rd := v]> st.(vregs)) st.(vheap) st.(vheap4))
          | None => None
          end
      | None => None
      end
  | VScaddi16sp imm6 =>
      (* rd is always sp (x2 <> 0), so no rd-zero guard. *)
      match st.(vregs) !! Regidx csp_rs1 with
      | Some v =>
          if sval_is64 v then
            Some (VSt pc'
                    (<[Regidx csp_rs1 := sval_addZ v (zimm12 (caddi16sp_imm imm6))]>
                       st.(vregs))
                    st.(vheap) st.(vheap4))
          else None
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
    (m : regfile) : Prop :=
  forall r sv, vr !! r = Some sv -> m !!! r = sval_den ρ sv.

Lemma gpr_matches_empty (ρ : nat -> mword 64) (m : regfile) :
  gpr_matches ρ ∅ m.
Proof. intros r sv H. rewrite lookup_empty in H. discriminate. Qed.

(* seed one register (client-side, at block entry). *)
Lemma gpr_matches_ins (ρ : nat -> mword 64) (vr : gmap regidx sval)
    (m : regfile) (r : regidx) (sv : sval) :
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
    (m : regfile) (r : regidx) (sv : sval) (w : mword 64) :
  w = sval_den ρ sv ->
  gpr_matches ρ vr m ->
  gpr_matches ρ (<[r := sv]> vr) (<[r := w]> m).
Proof.
  intros -> Hm r' sv' H. destruct (decide (r' = r)) as [->|Hne].
  - rewrite lookup_insert in H. injection H as <-. apply upd_eq.
  - rewrite lookup_insert_ne in H;
      [|intro Heq; apply Hne; symmetry; exact Heq].
    rewrite upd_ne;
      [exact (Hm _ _ H)|congruence].
Qed.

Section VcGenSIris.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  (* the block's heap cells are frame slots, so they ride the accessing
     hart's regime -- see VcGen.v's [vheap_own]. *)
  Context `{KTR : !CurKtier}.

  (* ------------------------------------------------------------------ *)
  (* 4-byte (word) cells: the [word_pointsto] analogue for lw/sw.  Both   *)
  (* alignment forms travel with the ownership, exactly as ↦₈ does, so    *)
  (* the wrappers below need no per-address side conditions.              *)
  (* ------------------------------------------------------------------ *)
  (* [word4_pointsto] / [↦₄] is defined in RiscvPtsto (the 4-byte analogue of
     [↦₈]); it bundles the 4 byte points-to facts with the 4-byte alignment. *)

  (* [wp_clw_s_pt] / [wp_csw_s_pt] -- the 4-byte S-mode load/store leaves
     that DERIVE the slot geometry from the owning [ea ↦₄ v] -- now live in
     [WpPushOffMem] (imported above) so [wp_push_off] shares them. *)
  (* one fully-owned 4-byte points-to per word cell. *)
  Definition vheap4_own (ρ : nat -> mword 64) (h : list (sval * sval32)) : iProp Σ :=
    ([∗ list] c ∈ h, (sval_den ρ c.1) ↦₄ (sval32_den ρ c.2))%I.

  (* the block's code: one RVC [instr] fact per entry, at consecutive pcs. *)
  Fixpoint block_instrs_s (pc : Z) (prog : list vop_s) : iProp Σ :=
    match prog with
    | nil => emp%I
    | op :: rest =>
        (instr (mword_of_int pc) (vop_s_rvc op) (vop_s_ast op) ∗
         block_instrs_s (pc + vop_s_w op) rest)%I
    end.

  (* expose gpr_file's dom-completeness fact without consuming it. *)
  Lemma gpr_file_dom (m : regfile) :
    gpr_file m -∗ ⌜ forall r : regidx, r ∈ dom (rf_to_gmap m) ⌝ ∗ gpr_file m.
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
  Lemma wp_vc_block_s_den_r (R : s_regime) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* the block's heap cells ride the accessing hart's tier; at the shared
       kernel-table regime this witness is [emp] ([SRegime.sr_ktier_wit_kpt_share]). *)
    (⊢ sr_ktier_wit R KTR) ->
    vc_block_s st prog = Some st' ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file (vregs_den ρ st.(vregs)) -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file (vregs_den ρ st'.(vregs)) -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hwit.
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
                     |imm rs1 rd|imm rs2 rs1|imm rd
                     |rvc imm rs2 rs1|rvc imm rs1 rd|imm6]; simpl in Hstep.
      + (* VScaddi *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi_gpr_s_config_r R (mword_of_int (vpc st)) rd imm
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd0
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
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi4spn_gpr_s_config_r R (mword_of_int (vpc st))
                  rdc nzimm rd (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd0
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
        destruct (is_tp rs2) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_csdsp_gpr_s_r_t R KTR KTR (mword_of_int (vpc st)) uimm rs2
                  (vregs_den ρ (vregs st)) (sval_den ρ vold)
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite (vregs_den_lookup ρ _ _ _ Hrs2) -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScldsp *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_cldsp_gpr_s_r_t R KTR KTR (mword_of_int (vpc st)) uimm rd
                  (vregs_den ρ (vregs st)) (sval_den ρ vv)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
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
        destruct (orb (is_tp rd) (is_tp rs1)) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_clw_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                  (vregs_den ρ (vregs st)) (sval32_den ρ w32)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
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
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_csw_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                  (vregs_den ρ (vregs st)) (sval32_den ρ wold)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
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
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddiw_s_r R (mword_of_int (vpc st)) rd imm
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd0
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
      + (* VSsd : general-base 8-byte store (c.sd / base sd) *)
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Htp; [discriminate|].
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64)
                  (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        assert (Hsv : vregs_den ρ (vregs st) !!! Regidx rs2 = sval_den ρ v2)
          by (rewrite (vregs_den_lookup ρ _ _ _ Hrs2); reflexivity).
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        destruct rvc.
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_csd_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                    (vregs_den ρ (vregs st)) (sval_den ρ vold)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hsv -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                  Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_sd_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                    (vregs_den ρ (vregs st)) (sval_den ρ vold)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hsv -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                  Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSld : general-base 8-byte load (c.ld / base ld) *)
        destruct (orb (is_tp rd) (is_tp rs1)) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64)
                  (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        assert (Egpr : <[Regidx rd := regval_into_reg (sval_den ρ vv)]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := vv]> (vregs st)))
          by (unfold regval_into_reg; apply vregs_den_insert).
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        destruct rvc.
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_cld_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                    (vregs_den ρ (vregs st)) (sval_den ρ vv)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iEval (rewrite Egpr) in "Hgpr".
          iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                  Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_ld_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                    (vregs_den ρ (vregs st)) (sval_den ρ vv)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iEval (rewrite Egpr) in "Hgpr".
          iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                  Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi16sp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        iApply (wp_caddi16sp_gpr_s_config_r R (mword_of_int (vpc st)) imm6
                  (vregs_den ρ (vregs st))
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi16sp_imm imm6)))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ
                    (<[Regidx csp_rs1 := sval_addZ v1 (zimm12 (caddi16sp_imm imm6))]>
                       (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -(sval_den_add_imm ρ v1 (caddi16sp_imm imm6) H64).
          apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                                Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
    (* the [KtierLe KTR KTR] side conditions of the tier-generic leaves are
       shelved by [iApply]'s elaboration, not solved in place. *)
    Unshelve. all: apply _.
  Qed.

  Lemma wp_vc_block_s_den (root_ppn : mword 44) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    vc_block_s st prog = Some st' ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file (vregs_den ρ st.(vregs)) -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file (vregs_den ρ st'.(vregs)) -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (fun H1 H2 H3 H4 H5 H6 H7 H8 =>
             wp_vc_block_s_den_r (kpt_share_regime root_ppn) prog st st' ρ mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
               H1 H2 H3 H4 H5 H6 H7 H8 (sr_ktier_wit_kpt_share root_ppn KTR)).
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

  (* Untouched-register preservation: for registers absent from the
     symbolic map [vr], the concrete file [mf] still agrees with the
     block's original input [m0].  [vc_step_s] only ever ADDS a register
     to [vr] (writes) or leaves it unchanged (stores), so the domain grows
     monotonically and any register never entered into [vr] keeps its
     entry value from [m0]. *)
  Definition agree_off (vr : gmap regidx sval)
      (mf m0 : regfile) : Prop :=
    forall r, vr !! r = None -> mf !!! r = m0 !!! r.

  Lemma agree_off_step {vr : gmap regidx sval} {mf m0 : regfile}
      {r : regidx} {sv : sval} {w : mword 64} :
    agree_off vr mf m0 -> agree_off (<[r := sv]> vr) (<[r := w]> mf) m0.
  Proof.
    intros H r' Hr'. destruct (decide (r' = r)) as [->|Hne].
    - rewrite lookup_insert in Hr'. discriminate.
    - rewrite lookup_insert_ne in Hr'; [|congruence].
      rewrite upd_ne; [|congruence]. exact (H _ Hr').
  Qed.

  Lemma wp_vc_block_s_aux_r (R : s_regime) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m m0 : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* the block's heap cells ride the accessing hart's tier; at the shared
       kernel-table regime this witness is [emp] ([SRegime.sr_ktier_wit_kpt_share]). *)
    (⊢ sr_ktier_wit R KTR) ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    agree_off st.(vregs) m m0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m0 ⌝ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hwit.
    revert st m. induction prog as [|op rest IH]; intros st m Hblk Hmatch Hao.
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
                     |imm rs1 rd|imm rs2 rs1|imm rd
                     |rvc imm rs2 rs1|rvc imm rs1 rd|imm6]; simpl in Hstep.
      + (* VScaddi *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi_gpr_s_config_r R (mword_of_int (vpc st)) rd imm m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd0
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
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi4spn *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (regidx_eqb (creg2reg_idx rdc) (Regidx rd)) eqn:Hrdc0;
          [|discriminate].
        pose proof (regidx_eqb_eq _ _ Hrdc0) as Hrdc. cbn [negb] in Hstep.
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi4spn_gpr_s_config_r R (mword_of_int (vpc st))
                  rdc nzimm rd m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrdc Hrd0
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
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsdsp *)
        destruct (is_tp rs2) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_csdsp_gpr_s_r_t R KTR KTR (mword_of_int (vpc st)) uimm rs2
                  m (sval_den ρ vold)
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite Hm2 -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zoff6 uimm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ _ Hblk Hmatch Hao
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScldsp *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_cldsp_gpr_s_r_t R KTR KTR (mword_of_int (vpc st)) uimm rd
                  m (sval_den ρ vv)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv)
          by reflexivity.
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSclw *)
        destruct (orb (is_tp rd) (is_tp rs1)) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_clw_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                  m (sval32_den ρ w32)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        assert (Hval : regval_into_reg (sign_extend' 64 (sval32_den ρ w32))
                       = sval_den ρ (S32 w32)) by reflexivity.
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScsw *)
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Htp; [discriminate|].
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
        iPoseProof Hwit as "#Hwit".
        iApply (wp_csw_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                  m (sval32_den ρ wold)
                  mstatus0 mie_v mdv0 menvcfg0
                  (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                  with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi Hcell").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hsv : trunc32 (m !!! Regidx rs2) = sval32_den ρ (sval_trunc32 v2)).
        { rewrite sval_trunc32_den Hm2. reflexivity. }
        iEval (rewrite Hsv -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), sval_trunc32 v2)
                     with "[Hcell]") as "Hheap4"; [iExact "Hcell"|].
        iApply (IH _ _ Hblk Hmatch Hao
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddiw *)
        destruct (is_tp rd) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rd) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddiw_s_r R (mword_of_int (vpc st)) rd imm m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd0
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
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSsd : general-base 8-byte store (agreement interface) *)
        destruct (orb (is_tp rs1) (is_tp rs2)) eqn:Htp; [discriminate|].
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        pose proof (Hmatch _ _ Hrs2) as Hm2.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        destruct rvc.
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_csd_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                    m (sval_den ρ vold)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk Hmatch Hao
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                          Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_sd_s_r_t R KTR KTR (mword_of_int (vpc st)) rs2 rs1 imm
                    m (sval_den ρ vold)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite Hm2 -Hea) in "Hcell".
          iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
            as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk Hmatch Hao
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                          Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VSld : general-base 8-byte load (agreement interface) *)
        destruct (orb (is_tp rd) (is_tp rs1)) eqn:Htp; [discriminate|].
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; cbn [negb] in Hstep; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
        { rewrite (sval_den_add_imm ρ v1 imm H64) Hm1. reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        assert (Hval : regval_into_reg (sval_den ρ vv) = sval_den ρ vv) by reflexivity.
        destruct rvc.
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_cld_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                    m (sval_den ρ vv)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                          Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
        * iPoseProof Hwit as "#Hwit".
          iApply (wp_ld_s_r_t R KTR KTR (mword_of_int (vpc st)) rd rs1 imm
                    m (sval_den ρ vv)
                    mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=DfracOwn 1)
 Hrd0 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
                    with "Hwit Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hgpr Hi Hcell").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hcell".
          iEval (rewrite avi_mword) in "Hpc".
          iEval (rewrite -Hea) in "Hcell".
          iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
          iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                          Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
      + (* VScaddi16sp *)
        destruct (vregs st !! Regidx csp_rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (sval_is64 v1) eqn:H64; [|discriminate].
        injection Hstep as <-.
        pose proof (Hmatch _ _ Hrs1) as Hm1.
        iApply (wp_caddi16sp_gpr_s_config_r R (mword_of_int (vpc st)) imm6 m
                  mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                        Hpc Hgpr Hi").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Hval : regval_into_reg
                    (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))
                = sval_den ρ (sval_addZ v1 (zimm12 (caddi16sp_imm imm6)))).
        { unfold regval_into_reg.
          rewrite Hm1 (sval_den_add_imm ρ v1 (caddi16sp_imm imm6) H64).
          reflexivity. }
        iApply (IH _ _ Hblk (gpr_matches_insert _ _ _ _ _ _ Hval Hmatch) (agree_off_step Hao)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv
                        Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont").
  Qed.

  Lemma wp_vc_block_s_aux (root_ppn : mword 44) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m m0 : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    agree_off st.(vregs) m m0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m0 ⌝ -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (fun H1 H2 H3 H4 H5 H6 H7 H8 =>
             wp_vc_block_s_aux_r (kpt_share_regime root_ppn) prog st st' ρ m m0 mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
               H1 H2 H3 H4 H5 H6 H7 H8 (sr_ktier_wit_kpt_share root_ppn KTR)).
  Qed.

  (* Thin wrapper over [wp_vc_block_s_aux]: instantiate the auxiliary
     induction at [m0 := m], where the entry agreement [agree_off (vregs st)
     m m] is reflexive.  Same interface as before EXCEPT the continuation's
     pure fact now also carries [agree_off st'.(vregs) mf m] -- untouched
     registers keep their input values. *)
  Lemma wp_vc_block_s_r (R : s_regime) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    (⊢ sr_ktier_wit R KTR) ->
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m ⌝ -∗
      smode_config γ dq -∗
      sr_inv R -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwit Hblk Hmatch.
    iIntros "Hsm Htlbinv Hpc Hgpr Hbi Hheap Hheap4 Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_vc_block_s_aux_r R prog st st' ρ m m mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hwit Hblk Hmatch
              (fun r _ => eq_refl)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hbi Hheap Hheap4 [Hcont Hsie]").
    iIntros (mf) "%Hmf Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hheap Hheap4".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" $! mf with "[//] Hsm Htlbinv Hpc Hgpr Hheap Hheap4").
  Qed.

  Lemma wp_vc_block_s (root_ppn : mword 44) (prog : list vop_s)
      (st st' : vstate) (ρ : nat -> mword 64)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    vc_block_s st prog = Some st' ->
    gpr_matches ρ st.(vregs) m ->
    smode_config γ dq -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file m -∗
    block_instrs_s st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    vheap4_own ρ st.(vheap4) -∗
    ( ∀ mf : regfile,
      ⌜ gpr_matches ρ st'.(vregs) mf ∧ agree_off st'.(vregs) mf m ⌝ -∗
      smode_config γ dq -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file mf -∗
      vheap_own ρ st'.(vheap) -∗
      vheap4_own ρ st'.(vheap4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_vc_block_s_r (kpt_share_regime root_ppn) prog st st' ρ m γ (dq:=dq)
             (sr_ktier_wit_kpt_share root_ppn KTR)).
  Qed.

  (* ================================================================== *)
  (* Intra-block conditional branch.                                      *)
  (*                                                                      *)
  (* A [bne rs1,rs2,imm] (full 4-byte BTYPE) whose target [pc + sext imm] *)
  (* is another point within the surrounding straight-line region.  The   *)
  (* machine's actual register values decide the direction, so the caller *)
  (* is handed BOTH continuations, each with the decided comparison as a   *)
  (* pure fact:                                                            *)
  (*   - TAKEN (rs1 <> rs2): resume at [pc + sext imm];                    *)
  (*   - FALL  (rs1  = rs2): resume at [pc + 4].                           *)
  (* Compose with [wp_vc_block_s]/[wp_vc_block_s_den] to run each side's   *)
  (* straight-line segment; this is how the VCgen handles a forward branch *)
  (* such as [if (p->state == SLEEPING && p->chan == chan) ...] that skips *)
  (* ahead within one block and reconverges.  (The target [imm] may be     *)
  (* forward or backward, so the same lemma also covers the backward jump  *)
  (* the compiler emits for that [if] in wakeup.)                          *)
  (* ================================================================== *)
  (* ===== smode_config wrappers for the intra-block branch leaves ===== *)




  Lemma wp_bne_split_s_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( ⌜neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true⌝ -∗
      smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    ( ⌜neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false⌝ -∗
      smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrs1 Hrs2 Hal.
    iIntros "Hsm Htlbinv Hpc Hgpr Hinstr Htaken Hfall".
    destruct (neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2)) eqn:Hcmp.
    - iApply (wp_bne_taken_s_config_scfg_r R γ pc imm rs2 rs1 m (dq:=dq)
 Hrs1 Hrs2 Hcmp Hal
                with "Hsm Htlbinv Hpc Hgpr Hinstr").
      iIntros "Hsm Htlbinv Hpc Hgpr".
      iApply ("Htaken" with "[//] Hsm Htlbinv Hpc Hgpr").
    - iApply (wp_bne_fall_s_config_scfg_r R γ pc imm rs2 rs1 m (dq:=dq)
 Hrs1 Hrs2 Hcmp
                with "Hsm Htlbinv Hpc Hgpr Hinstr").
      iIntros "Hsm Htlbinv Hpc Hgpr".
      iApply ("Hfall" with "[//] Hsm Htlbinv Hpc Hgpr").
  Qed.

  Lemma wp_bne_split_s (root_ppn : mword 44)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( ⌜neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true⌝ -∗
      smode_config γ dq -∗ tlb_res_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    ( ⌜neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false⌝ -∗
      smode_config γ dq -∗ tlb_res_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_bne_split_s_r (kpt_share_regime root_ppn) pc imm rs2 rs1 m γ (dq:=dq)).
  Qed.

  Lemma wp_beq_split_s_r (R : s_regime)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( ⌜eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true⌝ -∗
      smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    ( ⌜eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false⌝ -∗
      smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrs1 Hrs2 Hal.
    iIntros "Hsm Htlbinv Hpc Hgpr Hinstr Htaken Hfall".
    destruct (eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2)) eqn:Hcmp.
    - iApply (wp_beq_taken_s_config_scfg_r R γ pc imm rs2 rs1 m (dq:=dq)
 Hrs1 Hrs2 Hcmp Hal
                with "Hsm Htlbinv Hpc Hgpr Hinstr").
      iIntros "Hsm Htlbinv Hpc Hgpr".
      iApply ("Htaken" with "[//] Hsm Htlbinv Hpc Hgpr").
    - iApply (wp_beq_fall_s_config_scfg_r R γ pc imm rs2 rs1 m (dq:=dq)
 Hrs1 Hrs2 Hcmp
                with "Hsm Htlbinv Hpc Hgpr Hinstr").
      iIntros "Hsm Htlbinv Hpc Hgpr".
      iApply ("Hfall" with "[//] Hsm Htlbinv Hpc Hgpr").
  Qed.

  Lemma wp_beq_split_s (root_ppn : mword 44)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (γ : gname) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( ⌜eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true⌝ -∗
      smode_config γ dq -∗ tlb_res_pt root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    ( ⌜eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false⌝ -∗
      smode_config γ dq -∗ tlb_res_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
    Proof.
    exact (wp_beq_split_s_r (kpt_share_regime root_ppn) pc imm rs2 rs1 m γ (dq:=dq)).
  Qed.

End VcGenSIris.
