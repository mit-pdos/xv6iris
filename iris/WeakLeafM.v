(** * WeakLeafM.v -- THE SC-SHAPED LEAF INTERFACE for the M-mode tier.

    WHY THIS FILE EXISTS.  Batch 2 gave every M-mode instruction shape a weak
    leaf ([WeakLeafItype.wwp_addi_leaf] & co.), and batch 4 built three whole
    functions on top of them.  The chains came out at ~3x their SC twins --
    and the measurement (recorded in weak-memory.md) says almost none of that
    is weak-memory content: ~15 of the ~25 lines an instruction costs are the
    UNBUNDLED DECODE INTERFACE, and exactly ONE is the view bump that weak
    memory actually owes.

    The SC side does not pay that tax because it packages "the text at [pc]
    decodes to AST [i]" into ONE persistent token, [InstrBytes.instr pc is_rvc
    i], minted once per instruction in a [Code*.v] file; an SC instruction is
    then a single [iApply].  The weak side HAS the twin already --
    [WeakFunnel.winstr], structurally near-verbatim -- and the funnel
    [wwp_instr] consumes it.  The batch-2 leaves simply did not: they take
    [winstr_bytes] plus four to six loose decode/alignment premises.

    So this file is not new theory.  It is the missing packaging layer:

      [winstr_m pc is_rvc i] -- [winstr] PLUS the reference-state decode
      facts the certificate half needs, which [winstr] alone does not carry.

    TWO OBSERVATIONS MAKE IT CHEAP.  (1) [winstr_bytes] already carries the
    2-alignment, [acc_wf] and RAM-membership facts, and [winstr] already
    carries [is_lpad] and the ∀-state decode -- five of the six scaffolding
    categories.  (2) EVERY call site in [WkTimerinit] and [WkStartNew] uses
    the SAME bridge instance, [D_m] / [D_none] / [dstateM], so those are not
    per-instruction data at all: fixed here, they take [agree_m_regs] and
    [D_m_mi] out of the interface entirely.  What is left -- [goodb0] at the
    reference state and the concrete decode there -- is what [wdec_ref]
    holds.

    The 4-alignment premise disappears too: a leaf's [al4] is definitionally
    [is_aligned_vaddr (Virtaddr pc) 4], so a wrapper instantiates it at that
    very term and passes [eq_refl].

    RESULT: a wrapper's statement is its SC twin's, plus [hart_ws cpu_id ws]
    and a [ws_le]-bound [ws'] in the continuation -- and a caller's
    per-instruction text is the SC text plus one [vwp_hold_mono].  See
    [wwp_lui] at the end for the worked shape. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WeakPmpEff WeakTickEff WeakFetchEff WeakFunnel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import ExecCommon.
Require Import InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WpDecode WpDecodeBridge.
Require Import WeakLeafUtypeShift.
Require Import WeakLeafItype.
Require Import WkEntryEff.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The two decode shapes, as plain [Prop]s over a [FetchResult].

    [wdec_all] is verbatim [winstr]'s own decode field -- the ∀-state shape,
    which is what the WP half consumes.  [wdec_ref] is the reference-state
    shape at the FIXED bridge instance, which is what the certificate
    ([exec_eff]) half consumes.  A decode file proves both per instruction
    and never mentions either again. *)

Section WeakLeafM.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition wdec_all (r : FetchResult) (i : instruction) : Prop :=
    forall t : mstate,
      priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
      eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
      eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
      register_lookup misa t.(sregs) = MISA_C ->
      cfg_ok t ->
      if fetch_is_rvc r
      then exists i0 : instruction,
             exec (decode_fetch r) t = Some (i0, t) /\
             is_lpad_instruction i0 = false /\
             (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
      else exec (decode_fetch r) t = Some (i, t).

  Definition wdec_ref (r : FetchResult) (i : instruction) : Prop :=
    goodb0 D_m (decode_fetch r) dstateM = true /\
    match r with
    | F_Base _ => exec (decode_fetch r) dstateM = Some (i, dstateM)
    | F_RVC _  =>
        exists i0 : instruction,
          exec (decode_fetch r) dstateM = Some (i0, dstateM) /\
          is_lpad_instruction i0 = false /\
          (forall s : mstate, goodb0 D_none (execute i0) s = true) /\
          (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
    | _ => False
    end.

  (* ==================================================================== *)
  (** ** 2. The token: [InstrBytes.instr]'s weak twin, at leaf altitude. *)

  Definition winstr_m (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) : iProp Σ :=
    (⌜is_lpad_instruction i = false⌝ ∗
     ∃ r : FetchResult,
       ⌜fetch_is_rvc r = is_rvc⌝ ∗
       winstr_bytes pc r ∗
       ⌜wdec_all r i⌝ ∗
       ⌜wdec_ref r i⌝)%I.

  Global Instance winstr_m_persistent pc is_rvc i :
    Persistent (winstr_m pc is_rvc i).
  Proof. rewrite /winstr_m. apply _. Qed.

  (** [WeakFunnel] exports the [acc_wf] projection of [winstr_bytes] but not
      the 2-alignment one, which every leaf asks for by name. *)
  Lemma winstr_bytes_aligned2 pc r :
    winstr_bytes pc r ⊢ ⌜is_aligned_vaddr (Virtaddr pc) 2 = true⌝.
  Proof. iIntros "(% & _)". by iPureIntro. Qed.

  (** It IS a [winstr] -- so anything already stated against the funnel's
      token keeps working, and nothing below [wwp_instr] needs to change. *)
  Lemma winstr_m_winstr pc is_rvc i :
    winstr_m pc is_rvc i ⊢ winstr pc is_rvc i.
  Proof.
    iIntros "(%Hlpad & %r & %Hrvc & #Hb & %Hall & _)".
    iApply (winstr_intro pc is_rvc i r Hlpad Hrvc Hall with "Hb").
  Qed.

  (* ==================================================================== *)
  (** ** 3. THE INTRODUCTION a decode file uses -- one per instruction.

      Premises are exactly the facts a [Code*Aux]/[Wk*Aux] file already
      proves per instruction: the window's alignment/[acc_wf]/RAM triple,
      the byte window itself, the landing-pad fact, and the two decode
      shapes.  Nothing else. *)
  Lemma winstr_m_of_text bs
      (pc : SailStdpp.Values.mword 64) (r : FetchResult)
      (w : SailStdpp.Values.mword 32) (i : instruction) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    acc_wf pc 4 ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
    (match r with
     | F_Base w' => w' = w /\ isRVC (subrange_vec_dec w 15 0) = false
     | F_RVC h   => subrange_vec_dec w 15 0 = h /\ isRVC h = true
     | _         => False
     end) ->
    is_lpad_instruction i = false ->
    wdec_all r i ->
    wdec_ref r i ->
    wkernel_text bs -∗
    ⌜forall j : nat, (j < 4)%nat -> bs !! pa_add pc j = Some (nth_byte w j)⌝ -∗
    winstr_m pc (fetch_is_rvc r) i.
  Proof.
    intros H2 Hacc Hram Hr Hlpad Hall Href. iIntros "#Ht %Hlk".
    iDestruct (winstr_bytes_of_text bs pc r w H2 Hacc Hram Hr with "Ht [%]")
      as "#Hb"; [exact Hlk|].
    rewrite /winstr_m. iSplitR; [by iPureIntro|].
    iExists r. iSplitR; [by iPureIntro|]. iFrame "Hb". by iSplitR; iPureIntro.
  Qed.

  (* ==================================================================== *)
  (** ** 4. The eliminators a WRAPPER uses.

      A wrapper knows [is_rvc] concretely, so it wants the token already
      resolved to the corresponding [FetchResult] constructor with both
      decode shapes in hand. *)

  Lemma winstr_m_rvc pc i :
    winstr_m pc true i -∗
    ∃ h : SailStdpp.Values.mword 16, ∃ i0 : instruction,
      ⌜is_lpad_instruction i = false⌝ ∗
      winstr_bytes pc (F_RVC h) ∗
      ⌜is_aligned_vaddr (Virtaddr pc) 2 = true⌝ ∗
      ⌜wdec_all (F_RVC h) i⌝ ∗
      ⌜goodb0 D_m (ext_decode_compressed h) dstateM = true⌝ ∗
      ⌜exec (ext_decode_compressed h) dstateM = Some (i0, dstateM)⌝ ∗
      ⌜is_lpad_instruction i0 = false⌝ ∗
      ⌜forall s : mstate, goodb0 D_none (execute i0) s = true⌝ ∗
      ⌜forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s)⌝.
  Proof.
    iIntros "(%Hlpad & %r & %Hrvc & #Hb & %Hall & %Href)".
    destruct r as [e | w | h | e];
      [discriminate Hrvc | discriminate Hrvc | | discriminate Hrvc].
    iDestruct "Hb" as "#Hb'".
    iDestruct (winstr_bytes_aligned2 with "Hb'") as %Hal2.
    destruct Href as (Hgood & i0 & Hdec & Hlp0 & Hg0 & Hexp).
    iExists h, i0. iFrame "Hb'". by repeat iSplitR; iPureIntro.
  Qed.

  Lemma winstr_m_base pc i :
    winstr_m pc false i -∗
    ∃ w : SailStdpp.Values.mword 32,
      winstr_bytes pc (F_Base w) ∗
      ⌜is_aligned_vaddr (Virtaddr pc) 2 = true⌝ ∗
      ⌜wdec_all (F_Base w) i⌝ ∗
      ⌜goodb0 D_m (ext_decode w) dstateM = true⌝ ∗
      ⌜exec (ext_decode w) dstateM = Some (i, dstateM)⌝.
  Proof.
    iIntros "(%Hlpad & %r & %Hrvc & #Hb & %Hall & %Href)".
    destruct r as [e | w | h | e];
      [destruct Href as (_ & []) | | discriminate Hrvc | destruct Href as (_ & [])].
    iDestruct "Hb" as "#Hb'".
    iDestruct (winstr_bytes_aligned2 with "Hb'") as %Hal2.
    destruct Href as (Hgood & Hdec).
    iExists w. iFrame "Hb'". by repeat iSplitR; iPureIntro.
  Qed.

  (* ==================================================================== *)
  (** ** 5. THE WORKED WRAPPER: [lui], is_rvc-generic.

      Compare [WpMmodeUtype.wp_lui_gpr]: same binders, same three premises
      (minus [kmap_static], which weak addresses do not need -- they are
      already physical), same resources with [instr] -> [winstr_m], same
      continuation with the [ws]/[ws_le] pair added. *)
  Lemma wwp_lui (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rd : mword 5) (imm : mword 20) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    destruct is_rvc.
    - iDestruct (winstr_m_rvc with "Hi") as
        (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
      iApply (wwp_lui_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
                pc h rd imm i0 m pc pmpcfg0 q D_m D_none dstateM ws
                Hgid Hpmp Hal2 eq_refl Hnz
                Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
                D_m_mi Hgood Hdec Hg0 Hexp
                with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
      iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
      iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
      iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
    - iDestruct (winstr_m_base with "Hi") as
        (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
      iApply (wwp_lui_leaf (is_aligned_vaddr (Virtaddr pc) 4)
                pc w rd imm m pc pmpcfg0 q D_m dstateM ws
                Hgid Hpmp Hal2 eq_refl Hnz
                Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
                D_m_mi Hgood Hdec
                with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
      iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
      iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
      iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** [addi], the same packaging.  Follows [wwp_lui] line for line — which
      is the point: the [winstr_m] layer is a TEMPLATE, and the remaining
      instructions differ only in the leaf names, the argument list and the
      post-state [gpr_file] expression. *)
  Lemma wwp_addi (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    destruct is_rvc.
    - iDestruct (winstr_m_rvc with "Hi") as
        (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
      iApply (wwp_addi_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
                pc h rs1 rd imm i0 m pc pmpcfg0 q D_m D_none dstateM ws
                Hgid Hpmp Hal2 eq_refl Hnz
                Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
                D_m_mi Hgood Hdec Hg0 Hexp
                with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
      iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
      iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
      iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
    - iDestruct (winstr_m_base with "Hi") as
        (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
      iApply (wwp_addi_leaf (is_aligned_vaddr (Virtaddr pc) 4)
                pc w rs1 rd imm m pc pmpcfg0 q D_m dstateM ws
                Hgid Hpmp Hal2 eq_refl Hnz
                Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
                D_m_mi Hgood Hdec
                with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
      iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
      iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
      iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

End WeakLeafM.
