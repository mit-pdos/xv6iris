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
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WeakPmpEff WeakTickEff WeakFetchEff WeakFunnel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv.
Require Import ExecCommon.
Require Import InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WpDecode WpDecodeBridge.
Require Import WeakLeafUtypeShift.
Require Import WeakLeafItype.
Require Import WeakLeafRtypeW.
Require Import WeakLeafCsrrM WeakLeafCsrrTime.
(* the CSR numbers the §7 statements name.  [WpGprCsrrA]/[WpGprCsrrB] are the
   SC-side homes of [csr_mcounteren] / [csr_menvcfg] / [csr_time]; note
   [WpGprCsrwA] defines two of those names AGAIN (same values, [mword_of_int]
   rather than [Ox]), so the import order here matters and this file must not
   pull the write-side one in. *)
Require Import WpGprCsrrA WpGprCsrrB.
Require Import WeakLeafCsrw2 WeakLeafStimecmp.
Require Import WeakLeafCsrw WeakLeafCsrw3 WeakLeafPmpcfg0 WeakLeafSdspOff.
Require Import WeakLeafJump WeakLeafMret WpGprMretWp.
Require Import WeakLeafTor WeakWord8.
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

  (* ==================================================================== *)
  (** ** 6. The rest of the register-only ALU family.

      WHY THESE ARE NOT [is_rvc]-GENERIC.  [lui] and [addi] above quantify
      over [is_rvc] because batch 2 proved BOTH encodings for them.  For the
      five below only one encoding was ever proven, because only one is ever
      reached: [c.or]/[c.add]/[c.slli]/[c.addiw] appear in [WkTimerinit] and
      [WkStartNew] exclusively compressed, and [ori] exclusively uncompressed.
      Stating a wrapper at a [bool] it cannot discharge would buy nothing and
      owe a leaf that does not exist, so each is stated at the encoding its
      leaf covers -- [winstr_m pc true] with a 2-bump, or [winstr_m pc false]
      with a 4-bump.  Adding the missing encoding later is a leaf-file job;
      the wrapper then generalises exactly as [wwp_lui] does. *)

  (** [c.or] -- [RTYPE … OR], compressed only. *)
  Lemma wwp_or_rvc (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_or_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs2 rs1 rd i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** [c.add] / [c.mv] -- [RTYPE … ADD], compressed only. *)
  Lemma wwp_add_rvc (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_add_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs2 rs1 rd i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** [c.slli] -- [SHIFTIOP … SLLI], compressed only. *)
  Lemma wwp_slli_rvc (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_slli_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rd shamt i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** [c.addiw] -- [ADDIW], compressed only. *)
  Lemma wwp_addiw_rvc (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (immv : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (sign_extend' 64
                    (subrange_vec_dec
                       (add_vec (m !!! Regidx rs1)
                          (sign_extend' 64 immv)) 31 0))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_addiw_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rd immv i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** [ori] -- [ITYPE … ORI], uncompressed only.  The one [F_Base] member of
      this batch, so the eliminator is [winstr_m_base] and the bump is 4. *)
  Lemma wwp_ori (pc : SailStdpp.Values.mword 64)
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
    winstr_m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (or_vec (m !!! Regidx rs1)
                                     (sign_extend' 64 imm))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_ori_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 rd imm m pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (* ==================================================================== *)
  (** ** 7. The CSR-read family.

      Wider than §6 only in resource slots: a CSR read names the CSR's own
      cell and the SINGLE destination GPR cell rather than the whole
      [gpr_file] (its SC twin does the same), so the wrapper passes two
      extra points-tos through.  The packaging itself is unchanged -- all
      four are [F_Base], so all four use [winstr_m_base]. *)

  (** [csrr rd, menvcfg] *)
  Lemma wwp_csrr_menvcfg (pc : mword 64) (rd : mword 5)
      (menvcfg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg menvcfg_in -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hcsr Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_menvcfg_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd menvcfg_in rd0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hcsr Hrd Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrd Hcsr Hhws HF"). exact Hle.
  Qed.

  (** [csrr rd, mcounteren] -- the one 32-bit CSR of the four, so the
      written-back value is [zero_extend' 64]. *)
  Lemma wwp_csrr_mcounteren (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mcounteren ↦ᵣ mcen_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (zero_extend' 64 mcen_in) -∗
      mcounteren ↦ᵣ mcen_in -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hcsr Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_mcounteren_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd mcen_in rd0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hcsr Hrd Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrd Hcsr Hhws HF"). exact Hle.
  Qed.

  (** [csrr rd, mhartid] *)
  Lemma wwp_csrr_mhartid (pc : mword 64) (rd : mword 5)
      (mhartid_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mhartid ↦ᵣ mhartid_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg mhartid_in -∗
      mhartid ↦ᵣ mhartid_in -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hcsr Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_mhartid_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd mhartid_in rd0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hcsr Hrd Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrd Hcsr Hhws HF"). exact Hle.
  Qed.

  (** [csrr rd, time] -- the odd one out: [time] is not a register the proof
      owns, so the leaf hands back a value it does not fix, and the
      wrapper's continuation quantifies over it exactly as the leaf's does. *)
  Lemma wwp_csrr_time (pc : mword 64) (rd : mword 5) (rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ (tv : mword 64) (ws' : wstate),
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg tv -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_time_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd rd0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrd Hb Hhws").
    iIntros (tv ws') "%Hle Hmm Hpcf Hpc Hrd Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! tv ws' with "[%] Hmm Hpcf Hpc Hrd Hhws HF"). exact Hle.
  Qed.

  (* ==================================================================== *)
  (** ** 8. The CSR-write family.

      A NAME COLLISION TO BE CAREFUL ABOUT, since it is silent.  Both
      CSR-number tables define [csr_menvcfg] and [csr_mcounteren] --
      [WpGprCsrrA]/[WpGprCsrrB] as [Ox"30A"] / [Ox"306"], [WpGprCsrwA] as
      [mword_of_int 0x30a] / [mword_of_int 0x306].  Same values, different
      terms.  §7 above needs the READ-side ones and this section needs the
      WRITE-side ones, so importing both would silently give one of the two
      sections the wrong constant and leave the [winstr_m] token failing to
      unify with its leaf for no visible reason.  Only the read-side table is
      imported; §8 spells the write-side numbers -- and [menvcfg_legalized] /
      [stimecmp_legalized], which live in the same modules -- QUALIFIED. *)

  (** [csrw menvcfg, rs1] *)
  Lemma wwp_csrw_menvcfg (pc : mword 64) (rs1 : mword 5)
      (menvcfg0 : type_of_register menvcfg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      menvcfg ↦ᵣ WpGprCsrwA.menvcfg_legalized menvcfg0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_menvcfg_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 menvcfg0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** [csrw mcounteren, rs1] *)
  Lemma wwp_csrw_mcounteren (pc : mword 64) (rs1 : mword 5)
      (mcounteren0 : type_of_register mcounteren) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_mcounteren_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 mcounteren0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** [csrw stimecmp, rs1] *)
  Lemma wwp_csrw_stimecmp (pc : mword 64) (rs1 : mword 5)
      (stimecmp0 : type_of_register stimecmp) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      stimecmp ↦ᵣ WpGprCsrwB.stimecmp_legalized stimecmp0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_stimecmp_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 rs1v pc stimecmp0 pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (* ==================================================================== *)
  (** ** 9. Control flow.

      The packaging is the same; what differs is only that the post-state
      pc is not [add_vec_int pc n].  [jal] lands at [pc + imm] and writes
      the return address, [c.jr] lands at [ret_pc rav] and writes nothing. *)

  (** [jal rd, imm] *)
  Lemma wwp_jal (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (rdv0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rdv0 -∗
    winstr_m pc false (JAL (imm, Regidx rd)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      R_bitvector_64 (gpr_of_Z (uint rd))
        ↦ᵣ (regval_into_reg (add_vec_int pc 4)) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz Htgt.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_jal_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd imm rdv0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz Htgt
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrd Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrd Hhws HF"). exact Hle.
  Qed.

  (** [c.jr ra] *)
  Lemma wwp_cjr_rvc (pc : mword 64) (ra : mword 5) (rav : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
    winstr_m pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (ret_pc rav) -∗
      R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hra #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_cjr_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h ra i0 rav pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hra Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hra Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hra Hhws HF"). exact Hle.
  Qed.

  (** ** 10. [mret] -- and why it is the last one this file can package.

      [mret] does not take [mmode_config]; it takes the five cells that
      bundle CONSTITUTES, because it changes one of them: [cur_privilege]
      goes from [Machine] to [Supervisor].  So the bundle cannot be
      reassembled on the way out, and the wrapper below is the [winstr_m]
      packaging ONLY -- it removes the fetch preamble like every other
      wrapper here and nothing else.

      This is also exactly the boundary the design notes put the view token
      at: [mret] is the M->S transition, so it is where [hart_view] should
      stop travelling inside an M-mode bundle and start travelling inside
      [sconf].  Until the port reaches S-mode there is nothing to hand it
      to, so §10 stops at layer A and [WeakLeafO] gives [mret] an [_o] but
      deliberately no [_run]. *)
  Lemma wwp_mret (pc : mword 64) (newpriv : Privilege)
      (ms_cur mepc0 menvcfg1 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (ws : wstate) (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms_cur) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms_cur) ('b"1") = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms_cur -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    menvcfg ↦ᵣ menvcfg1 -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_m pc false (MRET tt) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ newpriv -∗
      mstatus ↦ᵣ cms5 ms_cur -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      menvcfg ↦ᵣ menvcfg1 -∗
      mepc ↦ᵣ mepc0 -∗
      pc_is (ret_pc mepc0) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp HmIE Hmprv Hfwd Hnew Hlpe.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf [Hpc Hnpc] Hmenv Hmepc
             #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_mret_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w newpriv ms_cur mepc0 menvcfg1 pc pmpcfg0 D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl HmIE Hmprv Hfwd Hnew Hlpe
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Hmenv Hmepc Hb Hhws").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws'
              with "[%] Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc Hhws HF").
    exact Hle.
  Qed.

  (* ==================================================================== *)
  (** ** 11. The two memory instructions.

      These are the ones with real weak-memory content, and the packaging
      layer does NOT touch it: the fetch preamble comes off exactly as
      everywhere else, and the memory interface -- the [vwp_hold] in and
      out for the load, the released [T] and its coherence side condition
      for the store -- is passed through UNCHANGED.  That is deliberate:
      §11 is where a silent weakening would do damage, so it does nothing
      but repackage the fetch. *)

  (** [c.ld rd, imm(rs1)] under a TOR PMP region. *)
  Lemma wwp_ld8_tor_rvc (pc : mword 64) (rs1 rd : mword 5) (imm : mword 12)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rd0 : mword 64) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea dqv v) ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wpt8 ea dqv v) ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnzd Hea Hram.
    iIntros "Hmm Hpcf Hpad [Hpc Hnpc] Hrs Hrd #Hi Hhws Hpt Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_ld8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rd imm i0 ea v dqv q pmpcfg0 pmpaddrs rs1v rd0 pc
              D_m D_none dstateM ws
              Hgid Hpmp Htor Hal2 eq_refl Hnz1 Hnzd Hea Hram
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpad Hpc Hnpc Hrs Hrd Hb Hhws Hpt").
    iIntros (ws') "%Hle Hmm Hpcf Hpad Hpc Hrs Hrd Hhws Hpt".
    iApply ("Hcont" $! ws'
              with "[%] Hmm Hpcf Hpad Hpc Hrs Hrd Hhws Hpt"). exact Hle.
  Qed.

  (** [c.sd rs2, imm(rs1)] under a TOR PMP region -- the RELEASE store.

      The continuation keeps the leaf's [T] and its coherence side
      condition verbatim.  [T] is the whole point of the instruction: it is
      the timestamp at which the frame [R] becomes publishable, and the
      bound relates it to the POST-state view, so neither can be dropped
      without dropping what a lock release is for. *)
  Lemma wwp_sd8_tor_rvc (pc : mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rs2v : mword 64) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea (DfracOwn 1) vold) ws -∗
    vwp_hold R ws -∗
    ( ∀ (ws' : wstate) (T : nat),
      ⌜ws_le ws ws'⌝ -∗
      ⌜forall j : nat, (j < 8)%nat ->
         (T <= flr (ws_view ws') (acc_addr ea j))%nat⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wpt8 ea (DfracOwn 1) rs2v) ws' -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hnz1 Hnz2 Hea Hram.
    iIntros "Hmm Hpcf Hpad [Hpc Hnpc] Hrs1 Hrs2 #Hi Hhws Hpt HR Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_sd8_tor_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rs2 imm i0 ea vold R q pmpcfg0 pmpaddrs rs1v rs2v pc
              D_m D_none dstateM ws
              Hgid Hpmp Htor Hal2 eq_refl Hnz1 Hnz2 Hea Hram
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpad Hpc Hnpc Hrs1 Hrs2 Hb Hhws Hpt HR").
    iIntros (ws' T) "%Hle %HT Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hhws Hpt HR".
    iApply ("Hcont" $! ws' T
              with "[%] [%] Hmm Hpcf Hpad Hpc Hrs1 Hrs2 Hhws Hpt HR");
      [exact Hle | exact HT].
  Qed.

  (* ==================================================================== *)
  (** ** 12. THE [start()] FAMILIES -- everything §5-§11 did not already
      cover, so that the whole M-mode boot cone can be written on this
      interface.

      Three kinds appear here, and only the third is not a template fill:

      (a) plain register instructions ([c.and], [c.srli], [auipc]) and the
          non-TOR 8-byte store ([c.sdsp] under [pmp_all_off]) -- §6/§11
          verbatim with the leaf name and the post-state changed;

      (b) the CSRs that ride the bundle ([csrr sie], [csrw mepc] / [satp] /
          [medeleg] / [mideleg] / [sie] / [pmpaddr0]) -- §7/§8 verbatim;

      (c) THE THREE THAT DO NOT TAKE THE BUNDLE ([csrr mstatus],
          [csrw mstatus], [csrw pmpcfg0]).  Their leaves take the CELLS
          [mmode_config] is built from, at FULL ownership, because each
          reads or writes one of them -- so there is no [mmode_config] in
          the statement and no fraction to thread.  That is not an artifact
          of this layer: the SC chain ([WpStartNew]) opens the bundle at
          exactly these three sites too, which is why a wrapper hiding the
          unbundle/rebuild would be further from step-site parity, not
          closer.  [WeakLeafO] gives these three an [_o] and no [_run] for
          the same reason it gives [mret] one -- there is no bundle for the
          view token to ride in.

      The CSR-number collision §7 records applies again and more widely:
      [csr_mstatus] and [csr_sie] are each defined twice (read side
      [WpGprCsrrA]/[WpGprCsrrB], write side [WpGprCsrwA]/[WpGprCsrwB]) with
      the same value and different terms, so EVERY csr number below is
      written qualified. *)

  (** *** 12a. [c.and] -- [RTYPE … AND], compressed only. *)
  Lemma wwp_and_rvc (pc : SailStdpp.Values.mword 64)
      (rs2 rs1 rd : mword 5) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (and_vec (m !!! Regidx rs1)
                                     (m !!! Regidx rs2))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_and_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs2 rs1 rd i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** *** 12b. [c.srli] -- [SHIFTIOP … SRLI], compressed only. *)
  Lemma wwp_srli_rvc (pc : SailStdpp.Values.mword 64)
      (rs1 rd : mword 5) (shamt : mword 6) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    winstr_m pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_srli_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rd shamt i0 m pc pmpcfg0 q D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** *** 12c. [auipc] -- [UTYPE … AUIPC], base only. *)
  Lemma wwp_auipc (pc : SailStdpp.Values.mword 64)
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
    winstr_m pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
                  regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hfile #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_auipc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd imm m pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hfile Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hfile Hhws HF"). exact Hle.
  Qed.

  (** *** 12d. [c.sdsp] with NO PMP region -- the [pmp_all_off] twin of
      §11's TOR store.  Same release interface, different PMP premise. *)
  Lemma wwp_sd8_off_rvc (pc : mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rs2v : mword 64) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_m pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea (DfracOwn 1) vold) ws -∗
    vwp_hold R ws -∗
    ( ∀ (ws' : wstate) (T : nat),
      ⌜ws_le ws ws'⌝ -∗
      ⌜forall j : nat, (j < 8)%nat ->
         (T <= flr (ws_view ws') (acc_addr ea j))%nat⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wpt8 ea (DfracOwn 1) rs2v) ws' -∗
      monPred_at R (view_scl T) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz1 Hnz2 Hea Hram.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs1 Hrs2 #Hi Hhws Hpt HR Hcont".
    iDestruct (winstr_m_rvc with "Hi") as
      (h i0) "(_ & #Hb & %Hal2 & %Hall & %Hgood & %Hdec & %Hlp0 & %Hg0 & %Hexp)".
    iApply (wwp_sd8_off_rvc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc h rs1 rs2 imm i0 ea vold R q pmpcfg0 rs1v rs2v pc
              D_m D_none dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz1 Hnz2 Hea Hram
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec Hg0 Hexp
              with "Hmm Hpcf Hpc Hnpc Hrs1 Hrs2 Hb Hhws Hpt HR").
    iIntros (ws' T) "%Hle %HT Hmm Hpcf Hpc Hrs1 Hrs2 Hhws Hpt HR".
    iApply ("Hcont" $! ws' T
              with "[%] [%] Hmm Hpcf Hpc Hrs1 Hrs2 Hhws Hpt HR");
      [exact Hle | exact HT].
  Qed.

  (** *** 12e. [csrr rd, sie] -- reads [mie] through [mideleg]. *)
  Lemma wwp_csrr_sie (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
        regval_into_reg (lower_mie mie_in mideleg_in) -∗
      mie ↦ᵣ mie_in -∗
      mideleg ↦ᵣ mideleg_in -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hmie Hmdl Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_sie_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd mie_in mideleg_in rd0 pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hmie Hmdl Hrd Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrd Hmie Hmdl Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrd Hmie Hmdl Hhws HF").
    exact Hle.
  Qed.

  (** *** 12f. [csrw mepc, rs1] *)
  Lemma wwp_csrw_mepc (pc : mword 64) (rs1 : mword 5)
      (mepc0 : type_of_register mepc) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mepc, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mepc ↦ᵣ WpGprCsrwA.mepc_val rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_mepc_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 mepc0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** *** 12g. [csrw satp, rs1] *)
  Lemma wwp_csrw_satp (pc : mword 64) (rs1 : mword 5)
      (satp0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    satp ↦ᵣ satp0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      satp ↦ᵣ WpGprCsrwB.satp_legalized satp0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_satp_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 satp0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** *** 12h. [csrw medeleg, rs1] *)
  Lemma wwp_csrw_medeleg (pc : mword 64) (rs1 : mword 5)
      (medeleg0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    medeleg ↦ᵣ medeleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_medeleg, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_medeleg_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 medeleg0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** *** 12i. [csrw mideleg, rs1] *)
  Lemma wwp_csrw_mideleg (pc : mword 64) (rs1 : mword 5)
      (mideleg0 : type_of_register mideleg) (rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mideleg ↦ᵣ mideleg0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mideleg ↦ᵣ WpGprCsrwB.mideleg_legalized mideleg0 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hcsr #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_mideleg_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 mideleg0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hcsr Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hcsr Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hcsr Hhws HF"). exact Hle.
  Qed.

  (** *** 12j. [csrw sie, rs1] -- writes [mie] through [mideleg], which it
      also reads, so both cells appear. *)
  Lemma wwp_csrw_sie (pc : mword 64) (rs1 : mword 5)
      (mie0 mdl0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mdl0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      mie ↦ᵣ WpGprCsrwB.sie_new_mie mie0 mdl0 rs1v -∗
      mideleg ↦ᵣ mdl0 -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hmie Hmdl #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_sie_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 mie0 mdl0 rs1v pc pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hmie Hmdl Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hmie Hmdl Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hmie Hmdl Hhws HF").
    exact Hle.
  Qed.

  (** *** 12k. [csrw pmpaddr0, rs1] *)
  Lemma wwp_csrw_pmpaddr0 (pc : mword 64) (rs1 : mword 5) (rs1v : mword 64)
      (pmpaddr00 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) (ws : wstate)
      (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      pmpaddr_n ↦ᵣ WpGprCsrwB.pmp0_newaddr pmpcfg0 pmpaddr00 rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz.
    iIntros "Hmm Hpcf [Hpc Hnpc] Hrs Hpad #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_pmpaddr0_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 rs1v pc pmpaddr00 pmpcfg0 q D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hmm Hpcf Hpc Hnpc Hrs Hpad Hb Hhws").
    iIntros (ws') "%Hle Hmm Hpcf Hpc Hrs Hpad Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws' with "[%] Hmm Hpcf Hpc Hrs Hpad Hhws HF"). exact Hle.
  Qed.

  (** *** 12l. [csrr rd, mstatus] -- the first of the three CELL-based ones
      (see the section header). *)
  Lemma wwp_csrr_mstatus (pc : mword 64) (rd : mword 5) (ms0 rd0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (ws : wstate) (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_m pc false
      (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx rd, CSRRS)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ ms0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg ms0 -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf [Hpc Hnpc] Hrd #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrr_mstatus_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rd ms0 rd0 pc pmpcfg0 D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz HmIE Hmprv
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Hrd Hb Hhws").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrd Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws'
              with "[%] Hhs Hpriv Hms Hpcf Hpc Hrd Hhws HF"). exact Hle.
  Qed.

  (** *** 12m. [csrw mstatus, rs1].  Its leaf is the one instruction in the
      cone with NO [al4] parameter -- it is stated at 4-alignment only --
      so the wrapper takes that as a premise instead of instantiating it. *)
  Lemma wwp_csrw_mstatus (pc : mword 64) (rs1 : mword 5) (ms0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (ws : wstate) (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_mstatus, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ WpGprCsrwCommon.mstatus_legalized ms0 rs1v -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal4 Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf [Hpc Hnpc] Hrs #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_mstatus_leaf
              pc w rs1 ms0 rs1v pc pmpcfg0 D_m dstateM ws
              Hgid Hpmp Hal4 Hnz HmIE Hmprv
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Hrs Hb Hhws").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrs Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws'
              with "[%] Hhs Hpriv Hms Hpcf Hpc Hrs Hhws HF"). exact Hle.
  Qed.

  (** *** 12n. [csrw pmpcfg0, rs1] -- the third cell-based one: it writes
      the very register the PMP premise is about. *)
  Lemma wwp_csrw_pmpcfg0 (pc : mword 64) (rs1 : mword 5) (ms0 rs1v : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (ws : wstate) (F : vProp Σ) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_m pc false
      (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) -∗
    hart_ws cpu_id ws -∗
    vwp_hold F ws -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ ms0 -∗
      pmpcfg_n ↦ᵣ WpGprCsrwC.pmpcfg_written rs1v pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
      hart_ws cpu_id ws' -∗
      vwp_hold F ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hnz HmIE Hmprv.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hpcf [Hpc Hnpc] Hrs #Hi Hhws HF Hcont".
    iDestruct (winstr_m_base with "Hi") as
      (w) "(#Hb & %Hal2 & %Hall & %Hgood & %Hdec)".
    iApply (wwp_csrw_pmpcfg0_leaf (is_aligned_vaddr (Virtaddr pc) 4)
              pc w rs1 ms0 rs1v pc pmpcfg0 D_m dstateM ws
              Hgid Hpmp Hal2 eq_refl Hnz HmIE Hmprv
              Hall (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi Hgood Hdec
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Hrs Hb Hhws").
    iIntros (ws') "%Hle Hhs Hpriv Hms Hpcf Hpc Hrs Hhws".
    iDestruct (vwp_hold_mono _ ws ws' Hle with "HF") as "HF".
    iApply ("Hcont" $! ws'
              with "[%] Hhs Hpriv Hms Hpcf Hpc Hrs Hhws HF"). exact Hle.
  Qed.

End WeakLeafM.
