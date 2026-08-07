(** * WeakLeafRegOnly.v — the ALIGNMENT-GENERIC register-only leaf kit (M4)

    Every register-only M-mode instruction (the csrw family, the csrr
    family, MRET) is fetched either at a 4-aligned pc (ONE 4-byte read,
    [WeakFetchEff.wP_eff_of_leaf_base]) or at a 2-not-4-aligned pc (TWO
    2-byte reads, [WeakFetch2.wP_eff_of_leaf_base2]) — and [start()] /
    [timerinit()] use BOTH alignments for the SAME instruction shapes, so a
    per-alignment leaf pair would double every leaf in the sweep.  This file
    kills that axis once:

      §1  [regonly_es al4 pc] — the fetch-only trace, as a function of the
          alignment bit — with its [nowrite_trace] fact and the
          [wcert_nowrite]/[wQ_pure] certificate instance [wcert_regonly].
      §2  [wP_eff_of_leaf_regonly] — the UNION recipe: the premise lists of
          [_base] and [_base2] merged (the alignment premises become
          [2-aligned] + [4-aligned = al4]; the [misa.C] premise only the
          2-arm reads is required unconditionally — every caller has it from
          [WeakFunnel.wcfg_regs]), concluding at [regonly_es al4 pc].  A
          leaf states [al4] as a parameter and covers both call-site
          alignments with ONE lemma and no duplicated proof.
      §3  the CSR-WRITE CHECK KIT, csr-generic: the [exec_eff] mirrors of
          [WpGprCsrwCommon.exec_check_CSR_csrw_p] and the four
          [exec_check_CSR_result_csrw_*] dispatchers.  Together with
          [WeakLeafCsrw]'s [doCSR]/[execute_CSRReg] spine these make each
          further csrw leaf owe ONLY its own [write_CSR] mirror.

    No Iris here — [wP_eff] and [wstep_cert] are [Prop]s — so no [Σ]
    context and no proofmode. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrwCommon.
(* [set_lookup_ne] and the register-side peel helpers. *)
Require Import WeakLeafWin.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The fetch-only trace, as a function of the alignment bit *)

Definition regonly_es (al4 : bool) (pc : SailStdpp.Values.mword 64)
    : list weff :=
  if al4 then [WEread wak_plain pc 4]
  else [WEread wak_plain pc 2; WEread wak_plain (add_vec_int pc 2) 2].

Lemma nowrite_regonly (al4 : bool) (pc : SailStdpp.Values.mword 64) :
  nowrite_trace (regonly_es al4 pc).
Proof.
  destruct al4; [exact (nowrite_read1 wak_plain pc 4) | exact (nowrite_fetch2 pc)].
Qed.

(** The certificate every register-only leaf hands to the funnel. *)
Lemma wcert_regonly (al4 : bool) (cid : nat)
    (pc : SailStdpp.Values.mword 64) :
  wstep_cert cid pc (wP_eff (Some cid) (regonly_es al4 pc)) wQ_pure.
Proof. exact (wcert_nowrite cid pc (regonly_es al4 pc) (nowrite_regonly al4 pc)). Qed.

(* ====================================================================== *)
(** ** 2. THE UNION RECIPE

    [wP_eff_of_leaf_base]'s premise list with [_base2]'s two extras folded
    in: the alignment pair becomes [2-aligned = true] + [4-aligned = al4],
    and [misa.C] is required unconditionally (only the 2-arm reads it; every
    M-mode caller has it from [wcfg_regs]).  The [execute] premise (c) is
    the two recipes' common one, at [es_x := []] — a register-only
    instruction's own trace is empty, which is also why the conclusion can
    be [regonly_es al4 pc] with no [++ es_x] residue (an [if]-headed list
    does not reduce under [++] while [al4] is a variable). *)

Lemma wP_eff_of_leaf_regonly
    (al4 : bool) (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction)
    (D : register -> bool) (dst : mstate) :
  (* --- the window (porting guide §2, items 1-3) --- *)
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  (* --- the M-mode config tower: the SAME facts [wwp_instr] collects --- *)
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* --- (a) the text word, IN THE CONFINED MEMORY, at either alignment --- *)
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (* --- (b) the DECODE, exactly as the decode library states it --- *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (* --- (c) the [execute]'s own [exec_eff] fact, at the EMPTY trace --- *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, [])
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid) (regonly_es al4 pc) σ.
Proof.
  destruct al4;
    intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE
           Lelp Hal2 Hal4 Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad
           Hexec.
  - exact (wP_eff_of_leaf_base cid σ W pc w i [] D dst Hwf HW0 HWp Lpc Lpriv
             Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp Hal4 Hram Htext HnotRVC
             Hagree HDmi Hgood Hdec Hnlpad Hexec).
  - exact (wP_eff_of_leaf_base2 cid σ W pc w i [] D dst Hwf HW0 HWp Lpc Lpriv
             Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp Hal2 Hal4 Hram
             Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec).
Qed.

(* ====================================================================== *)
(** ** 3. THE CSR-WRITE CHECK KIT, csr-generic

    [WpGprCsrwCommon.exec_check_CSR_csrw_p] and its four
    [check_CSR_result] dispatchers, mirrored at [exec_eff] (all
    register-only: one [misa] read at most, trace [[]]).  Each further csrw
    leaf discharges its [check_CSR_result] obligation from ONE of these
    plus per-csr [vm_compute] side conditions, exactly as the SC leaves
    do. *)

Lemma exec_eff_check_CSR_csrw_p (p : Privilege) (csr : mword 12) s :
  exec_eff (check_CSR_priv csr p) s = Some (true, s, []) ->
  check_CSR_access csr CSRWrite = true ->
  exec_eff (is_CSR_accessible csr p CSRWrite) s = Some (true, s, []) ->
  exec_eff (stateen_allows_CSR_access csr p CSRWrite) s = Some (true, s, []) ->
  exec_eff (check_CSR csr p CSRWrite) s = Some (true, s, []).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec_eff (returnM (check_CSR_access csr CSRWrite) : M bool) s
               = Some (true, s, []))
    by (rewrite exec_eff_returnM; rewrite Hca; reflexivity).
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ HB). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_eff_check_CSR_result_csrw_p (p : Privilege) (csr : mword 12) s :
  exec_eff (check_CSR csr p CSRWrite) s = Some (true, s, []) ->
  exec_eff (check_CSR_result csr p CSRWrite) s = Some (CSR_Check_OK tt, s, []).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hcc). cbn match. apply exec_eff_returnM.
Qed.

(** pure-CSR ([is_CSR_accessible] = [returnM true]): mepc 0x341, … *)
Lemma exec_eff_check_CSR_result_csrw_pure (csr : mword 12) s :
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRWrite = true ->
  exec_eff (is_CSR_accessible csr Machine CSRWrite) s = Some (true, s, []) ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRWrite) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros. apply exec_eff_check_CSR_result_csrw_p.
  apply exec_eff_check_CSR_csrw_p; assumption.
Qed.

(** Ext_S-gated CSRs: medeleg 0x302, mideleg 0x303, sie 0x104, satp 0x180. *)
Lemma exec_eff_check_CSR_result_csrw_S (csr : mword 12) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRWrite = true ->
  is_CSR_accessible csr Machine CSRWrite = currentlyEnabled Ext_S ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRWrite) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HS Hpriv Hca Hacceq Hst.
  apply exec_eff_check_CSR_result_csrw_p.
  apply exec_eff_check_CSR_csrw_p; try assumption.
  rewrite Hacceq. rewrite (exec_eff_currentlyEnabled_S s). rewrite HS.
  reflexivity.
Qed.

(** U-gated CSRs whose accessibility conjoins a config predicate —
    menvcfg (0x30A). *)
Lemma exec_eff_check_CSR_result_csrw_U_and (csr : mword 12) (b : bool) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRWrite = true ->
  is_CSR_accessible csr Machine CSRWrite
    = Defs.and_boolM ((currentlyEnabled Ext_U) : M bool) (returnM b) ->
  b = true ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRWrite) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HU Hpriv Hca Hacceq Hb Hst.
  apply exec_eff_check_CSR_result_csrw_p.
  apply exec_eff_check_CSR_csrw_p; try assumption.
  rewrite Hacceq.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_currentlyEnabled_U s HU)).
  cbn match. rewrite Hb. apply exec_eff_returnM.
Qed.

Lemma exec_eff_check_CSR_result_csrw_U (csr : mword 12) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRWrite = true ->
  is_CSR_accessible csr Machine CSRWrite = currentlyEnabled Ext_U ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRWrite) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HU Hpriv Hca Hacceq Hst.
  apply exec_eff_check_CSR_result_csrw_p.
  apply exec_eff_check_CSR_csrw_p; try assumption.
  rewrite Hacceq. apply (exec_eff_currentlyEnabled_U s HU).
Qed.

(* ====================================================================== *)
(** ** 3b. The successor register frame for a ONE-CELL-writing instruction

    [WeakLeafCsrw.csrw_sexec_facts] generalized over the written register
    ([mstatus] there): the bookkeeping facts the recipes ask for alongside
    the run, for any instruction whose successor is
    [set_reg (set_reg (set_reg s0 mi b) nextPC npc) r v] with [r] none of
    the three frame registers. *)
Lemma csrw_sexec_facts_r (r : register) (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (v : type_of_register r) :
  register_beq hart_state r = false ->
  register_beq (R_bool minstret_increment) r = false ->
  register_beq nextPC r = false ->
  let s_exec :=
    set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
      r v in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = npc.
Proof.
  intros Hhs Hmi Hnpc. cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state r _ _ Hhs).
    by rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
               (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment) r _ _ Hmi).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite (set_lookup_ne nextPC r _ _ Hnpc).
    rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions wP_eff_of_leaf_regonly.
Print Assumptions wcert_regonly.
Print Assumptions exec_eff_check_CSR_result_csrw_U_and.
