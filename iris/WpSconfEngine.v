(* WpSconfEngine.v -- the S-MODE gpr-write ENGINES at the per-node layer,
   for the leaves whose written value is a FUNCTION OF THE SOURCE READS.

   WHY THIS FILE EXISTS.  [WpSmodeIntr.wp_gpr_write_s_sconf{,_base}]'s
   instruction obligation is HART-GENERIC -- it is [∀ CID, gen_cert -∗
   gpr_file (tp_pin m) -∗ swp (execute base) (... <[rd := wval]> (tp_pin m))]
   with [wval] fixed by the CALLER, at the caller's hart.  That is exactly
   right for a leaf whose value reads no caller-chosen register ([c.li],
   [lui]), and it is UNPROVABLE for one that does: the walk answers the read
   at the hart the σ-callback was instantiated at, while [wval] names the
   value at the entry hart, and the two differ at tp.  A leaf holding only
   [ops_ok b rd rsa rsb] cannot close that gap by itself -- [src_ok] is
   guarded on [b = true], and the guard that saves the [b = false] case is
   [WpNext.wp_next]'s, which the obligation does not carry.  (This is the
   "guarded route" IntrDefs' [SrcOk] note points at: a leaf whose caller has
   only [ops_ok] at a variable [b] belongs here and not on the class.)

   THE SHAPE THAT DISSOLVES IT.  Do not hand the obligation a value; hand it
   the FUNCTION.  The engines below take [f : mword 64 -> mword 64 -> mword 64]
   and a caller premise [f (rget m rsa) (rget m rsb) = wval], and their
   obligation is

     ∀ CID, gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base) (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
         gpr_file (<[Regidx rd := regval_into_reg
                       (f (tp_pin m !!! Regidx rsa)
                          (tp_pin m !!! Regidx rsb))]> (tp_pin m)))

   -- which mentions no hart-specific value at all and is, verbatim, what
   [WpMmodeSwpBase]'s node shapes ([swp_execute_rrw] / [_rw] / [_rw2] /
   [_rrw2] / [_pure_w]) conclude.  A converted leaf is therefore ONE [iApply]
   with no [swp_mono] and no rewriting.  The reconciliation between the two
   harts happens ONCE, here, out of [ops_ok] and the [wp_next] guard, by
   [IntrDefs.rget_next_ops_indep].

   A leaf reading NO caller-chosen register may still use these ([f] ignores
   its arguments) or stay on [WpSmodeIntr]'s value-shaped engines; both are
   proved from the same funnel.

   ADDITIVE: nothing here changes an existing statement.  The three engines
   that live in WpSconfAlu.v ([wp_gpr_write_s_sconf_base_pc], the two cap
   engines) are converted in place beside their leaves. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartSwp HartMFrame WpMmodeSwpBase.
Require Import HartLift HartSpan HartSpanChar HartRegNode HartMCycle WpMmodeJump ColdBoot.
Require Import IntrDefs WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* §2 BRANCHES.  A branch writes no GPR, so none of the engines above      *)
(* fits: what it does is read two registers, and -- if the comparison      *)
(* holds -- read PC and WRITE nextPC.  The model's own shape, printed      *)
(* rather than guessed (durable-notes' rule), is the notation below; the   *)
(* condition code is a parameter, so each of the six [bop]s is [eq_refl].  *)
(* ====================================================================== *)

Notation btype_body imm rs2 rs1 cmp :=
  (Defs.bind
     (Defs.bind (rX_bits (Regidx rs1))
        (fun a => Defs.bind (rX_bits (Regidx rs2))
                    (fun c => returnM (cmp a c))))
     (fun taken : bool =>
        if taken
        then Defs.bind (Defs.read_reg (R_bitvector_64 PC))
               (fun w => jump_to (add_vec w (sign_extend' 64 imm)))
        else returnM RETIRE_SUCCESS)).

(* the target's bit 0, spelled as the MODEL spells it (design §5 item 1(g):
   a hand-written [N_to_word 1 0] is convertible but not syntactically equal,
   and [rewrite]/[destruct .. eqn:] match syntactically) *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

(* ---- THE TWO-CELL FRAME the S-mode jump needs.  [WpMmodeJump]'s is FOUR
   cells and pins cur_privilege to Machine, which no S-mode leaf can supply;
   but [hfrun_jump_to_zca] itself only ever reads misa and only ever writes
   nextPC, so the privilege was never the jump's business.  This is that
   fact, framed. ---- *)
Definition sj_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition sj_Dro : gset register := {[ (misa : register) ]}.
Definition sj_Df : register -> dfrac := fun _ => DfracDiscarded.
Definition sj_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0 (register_set misa MISA_C init_regstate).

Lemma sj_disj : sj_Drw ## sj_Dro.
Proof. rewrite /sj_Drw /sj_Dro. set_solver. Qed.
Lemma sj_w_nPC : (R_bitvector_64 nextPC : register) ∈ sj_Drw.
Proof. rewrite /sj_Drw. set_solver. Qed.
Lemma sj_in_misa : (misa : register) ∈ sj_Drw ∪ sj_Dro.
Proof. rewrite /sj_Drw /sj_Dro. set_solver. Qed.

Lemma sj_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (sj_rs npc0) = npc0.
Proof. rewrite /sj_rs. by rewrite register_lookup_set. Qed.
Lemma sj_rs_misa npc0 : register_lookup misa (sj_rs npc0) = MISA_C.
Proof.
  rewrite /sj_rs.
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
  apply register_lookup_set.
Qed.

Lemma sj_set_agree (npc0 target : SailStdpp.Values.mword 64) :
  reg_agree_on (sj_Drw ∪ sj_Dro)
    (register_set (R_bitvector_64 nextPC) target (sj_rs npc0)) (sj_rs target).
Proof.
  intros r Hr. rewrite /sj_Drw /sj_Dro in Hr.
  apply elem_of_union in Hr as [Hr|Hr]; apply elem_of_singleton in Hr; subst r.
  - etransitivity; [apply register_lookup_set|]. symmetry. apply sj_rs_nPC.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply sj_rs_misa|]. symmetry. apply sj_rs_misa.
Qed.

Section HwMisa.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the ONE cell a jump needs out of the persistent config bundle *)
  Lemma hw_config_misa : hw_config -∗ misa ↦ᵣ□ MISA_C.
  Proof.
    iIntros "H". iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(Hmisa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hv & _)".
    rewrite Hv. iExact "Hmisa".
  Qed.
End HwMisa.

Section WpSconfBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sj_frames (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (sj_rs npc0) sj_Drw ∗
     hreg_frame_ro sj_Df (sj_rs npc0) sj_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sj_Drw /sj_Dro.
    rewrite !big_sepS_singleton.
    by rewrite sj_rs_nPC sj_rs_misa.
  Qed.

  (* THE S-MODE JUMP, at cells: nextPC written, misa read.  Privilege-free. *)
  Lemma swp_jump_to_s (target npc0 : SailStdpp.Values.mword 64) :
    eq_vec (access_vec_dec target 0) zerobit = true ->
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (jump_to target)
      (fun r => ⌜r = RETIRE_SUCCESS⌝ ∗
                (R_bitvector_64 nextPC) ↦ᵣ target ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    intros Halign. iIntros "#Hcert HnPC Hmisa".
    iAssert (hreg_frame (sj_rs npc0) sj_Drw ∗
             hreg_frame_ro sj_Df (sj_rs npc0) sj_Dro)%I with "[HnPC Hmisa]"
      as "[Hrw Hro]".
    { rewrite sj_frames. iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hfrun 6 sj_Drw sj_Dro sj_Df (sj_rs npc0)
                   (register_set (R_bitvector_64 nextPC) target (sj_rs npc0))
                   (jump_to target) RETIRE_SUCCESS sj_disj
                   (hfrun_jump_to_zca (sj_Drw ∪ sj_Dro) sj_Drw (sj_rs npc0)
                      target sj_in_misa sj_w_nPC Halign
                      ltac:(rewrite sj_rs_misa; vm_compute; reflexivity))
                   with "Hcert Hrw Hro") ].
    iIntros (r) "(-> & Hrw & Hro)".
    rewrite (hreg_frame_ext _ (sj_rs target) sj_Drw
               (reg_agree_l _ _ _ _ (sj_set_agree npc0 target))).
    rewrite (hreg_frame_ro_ext sj_Df _ (sj_rs target) sj_Dro
               (reg_agree_r _ _ _ _ (sj_set_agree npc0 target))).
    iSplitR; [done|]. rewrite -sj_frames. iFrame.
  Qed.

  (* the comparison half: two GPR reads at a symbolic index, so it peels at
     [swp_rX_file] like every other operand read in the sweep *)
  Lemma swp_btype_cmp (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    gen_cert -∗ gpr_file m -∗
    swp (Defs.bind (rX_bits (Regidx rs1))
           (fun a => Defs.bind (rX_bits (Regidx rs2))
                       (fun c => returnM (cmp a c))))
      (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗ gpr_file m).
  Proof.
    iIntros "#Hcert Hf".
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (v1) "[-> Hf]".
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v2) "[-> Hf]".
    iApply swp_ret. by iFrame.
  Qed.

  (* THE FALL-THROUGH ARM: the comparison is false, so the branch is two
     register reads and a [Ret] -- no cell of any kind is touched. *)
  Lemma swp_execute_BTYPE_fall (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    gen_cert -∗ gpr_file m -∗
    swp mo (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m).
  Proof.
    intros Hred Hcmp. iIntros "#Hcert Hf". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_btype_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply swp_ret. by iFrame.
  Qed.

  (* THE TAKEN ARM: the comparison holds, PC is read and nextPC written. *)
  Lemma swp_execute_BTYPE_taken (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult) (pc npc0 : SailStdpp.Values.mword 64)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp mo (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
              (R_bitvector_64 PC) ↦ᵣ pc ∗
              (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
              misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hred Hcmp Halign. iIntros "#Hcert Hf HPC HnPC Hmisa". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_btype_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w) "[-> HPC]".
    iApply (swp_mono with "[Hf HPC] [HnPC Hmisa]");
      [| iApply (swp_jump_to_s (add_vec pc (sign_extend' 64 imm)) npc0 Halign
                   with "Hcert HnPC Hmisa") ].
    iIntros (r) "(-> & HnPC & Hmisa)". iFrame. done.
  Qed.

End WpSconfBranch.

Section WpSconfEngine.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* [IntrDefs.tp_pin_sp] with the [rget] FOLDED, so a leaf reading sp can
     [rewrite] it: the engines' value premise is spelled [rget m rsa], and a
     leaf whose source is the concrete sp states its value at the plain map
     lookup.  The two are convertible; [rewrite] is syntactic. *)
  Lemma rget_sp (m : regfile) : rget m csp_rs1 = m !!! Regidx csp_rs1.
  Proof. exact (tp_pin_sp m). Qed.

  (* =================================================================== *)
  (* THE MASTER.  Encoding width [c] is a parameter; the capability moves  *)
  (* by a caller-supplied TRANSFORMER (so an sp-write is the same engine); *)
  (* and the PC cell the funnel lends is passed straight through to the    *)
  (* obligation (so AUIPC is the same engine too).  [ops_ok_sp] rather     *)
  (* than [ops_ok] -- rd MAY be sp here; the tp half and the whole read    *)
  (* side are identical.  Everything else in this file is an instance.     *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_gen
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (* THE INSTRUCTION'S OWN OBLIGATION, hart-generic and value-free: the walk
       reads whatever this hart's pin holds and writes [f] of it.  This is
       exactly what [WpMmodeSwpBase]'s node shapes conclude. *)
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    pose proof (ops_ok_sp_rd _ _ _ _ Hops) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc c base
              (fun npc m2 n2 => ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                                ⌜m2 = <[Regidx rd := regval_into_reg wval]> m⌝ ∗
                                ⌜n2 = n'⌝ ∗ P)%I
              with "Hcg Hpc Hinstr [Hex Hrecap Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART -- the statement never sees
       the rename, so callers naming this engine's hart keep working. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "Hex Hrecap".
    - (* the instruction *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      (* THE ONE RECONCILIATION, and the reason this engine exists: the walk
         answers the two source reads at the REBOUND hart, while [Hwval] names
         them at the entry hart.  At [b = true] [ops_ok] says neither source is
         tp; at [b = false] the guard [Hs] pins the hart outright. *)
      pose proof (rget_next_indep (CID := CID0) b p CID m rsa Hs
                    (ops_ok_sp_s1 _ _ _ _ Hops)) as Hra.
      pose proof (rget_next_indep (CID := CID0) b p CID m rsb Hs
                    (ops_ok_sp_s2 _ _ _ _ Hops)) as Hrb.
      assert (Hval : f (tp_pin (CID := CID) m !!! Regidx rsa)
                       (tp_pin (CID := CID) m !!! Regidx rsb) = wval)
        by (unfold rget in Hra, Hrb; rewrite Hra Hrb; exact Hwval).
      iDestruct ("Hrecap" $! CID with "Hcap") as "[Hcap HP]".
      iDestruct ("Hex" $! CID with "Hcert Hfile HPC") as "Hexx".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HnPC Hresv HP] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile & HPC)".
      iSplitR; [done|].
      iExists (add_vec_int pc (if c then 2 else 4)),
              (<[Regidx rd := regval_into_reg wval]> m), n'.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iSplitL "Hcap"; [ iExact "Hcap" |].
      iSplitL "Hfile".
      { iEval (rewrite Hval) in "Hfile".
        iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      iFrame "HP". done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc m2 n2) "Hcg' Hpc' (-> & -> & -> & HP)".
      iApply ("Hcont" $! CID with "[%] Hcg' HP Hpc'"). exact Hs.
  Qed.

  (* THE PC-FREE OBLIGATION, the shape 99 % of the leaves want: the cell is
     framed across the walk here instead of at every call site. *)
  Lemma wp_gpr_write_s_sconf_cap_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    iApply (wp_gpr_write_s_sconf_gen pc c rd rsa rsb base f wval m n n' P b
              Hrd Hops Hwval with "[Hex] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "Hcert Hf HPC".
    iApply (swp_mono (CID := CIDn) with "[HPC] [-]");
      [| iApply ("Hex" $! CIDn with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC".
  Qed.

  (* =================================================================== *)
  (* The ordinary (non-sp) engine: the capability is merely RETARGETED    *)
  (* across the write, which is what [rd_ok]'s sp conjunct buys.          *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_cap_val_w pc c rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the two width instances every leaf actually names *)
  Lemma wp_gpr_write_s_sconf_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc true rd rsa rsb base f wval m n b). Qed.

  Lemma wp_gpr_write_s_sconf_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc false rd rsa rsb base f wval m n b). Qed.

  (* the COMPRESSED cap engine -- the shape every sp-mover is built over *)
  Lemma wp_gpr_write_s_sconf_cap_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_gpr_write_s_sconf_cap_val_w pc true rd rsa rsb base f wval m n n' P b).
  Qed.

  (* THE PC-READING ENGINE (auipc): the funnel's own PC cell, lent to the
     obligation and taken back.  [f] ignores its arguments at every current
     call site -- the value is a function of [pc] -- but it is kept for
     uniformity with the rest of the family. *)
  Lemma wp_gpr_write_s_sconf_pc_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_gen pc false rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ================================================================== *)
  (* §3 THE TWO BRANCH FUNNELS.  A branch writes no GPR, so [sie_cap]    *)
  (* and the file pass through untouched and the only thing that moves   *)
  (* is nextPC (the taken arm).  The comparison premise is the ALL-HARTS *)
  (* form -- that is what a leaf's [SrcOk] classes buy it, and the       *)
  (* reason it is a premise here rather than a class is that the engine  *)
  (* has no register argument for a class to attach to.                  *)
  (* ================================================================== *)
  Lemma wp_btype_fall_s_sconf
      (pc : mword 64) (c : bool) (imm : mword 13) (rs2 rs1 : mword 5)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (m : regfile) (n : nat) (b : bool) :
    execute i = btype_body imm rs2 rs1 cmp ->
    (* THE COMPARISON, at whatever hart the funnel resumes on, and stated
       AGAINST THE FILE rather than purely: a branch on x0 reads index 0,
       whose value is [zero_reg] only because [gpr_file] says so
       ([WpGpr.gpr_file_x0]).  A leaf whose operands are ordinary registers
       supplies this from its own premise and its [SrcOk] classes and gives
       the file straight back. *)
    (∀ hh : CpuId, gpr_file (CID := hh) (tp_pin (CID := hh) m) -∗
       ⌜cmp (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false⌝ ∗
       gpr_file (CID := hh) (tp_pin (CID := hh) m)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c i -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hred) "Hcmp Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b pc c i
              (fun npc m2 n2 => ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                                ⌜m2 = m⌝ ∗ ⌜n2 = n⌝)%I
              with "Hcg Hpc Hinstr [Hcmp Hcont]").
    iNext. rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iDestruct ("Hcmp" $! CID with "Hfile") as "[%Hc0 Hfile]".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HPC HnPC Hresv] [Hfile]");
        [| iApply (swp_execute_BTYPE_fall (CID := CID) imm rs2 rs1
                     (tp_pin (CID := CID) m) (execute i) cmp Hred
                     Hc0 with "Hcert Hfile") ].
      iIntros (e) "[-> Hfile]". iSplitR; [done|].
      iExists (add_vec_int pc (if c then 2 else 4)), m, n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iFrame "Hcap Hfile". done.
    - iIntros (npc m2 n2) "Hcg' Hpc' (-> & -> & ->)".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  Lemma wp_btype_taken_s_sconf
      (pc : mword 64) (c : bool) (imm : mword 13) (rs2 rs1 : mword 5)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (m : regfile) (n : nat) (b : bool) :
    execute i = btype_body imm rs2 rs1 cmp ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
    (* the comparison, against the file -- see the fall-through engine *)
    (∀ hh : CpuId, gpr_file (CID := hh) (tp_pin (CID := hh) m) -∗
       ⌜cmp (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true⌝ ∗
       gpr_file (CID := hh) (tp_pin (CID := hh) m)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c i -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hred Hal0) "Hcmp Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b pc c i
              (fun npc m2 n2 => ⌜npc = add_vec pc (sign_extend' 64 imm)⌝ ∗
                                ⌜m2 = m⌝ ∗ ⌜n2 = n⌝)%I
              with "Hcg Hpc Hinstr [Hcmp Hcont]").
    iNext. rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iDestruct (hw_config_misa with "Hhw") as "#Hmisa".
      iDestruct ("Hcmp" $! CID with "Hfile") as "[%Hc0 Hfile]".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap Hresv] [Hfile HPC HnPC]");
        [| iApply (swp_execute_BTYPE_taken (CID := CID) imm rs2 rs1
                     (tp_pin (CID := CID) m) (execute i) pc
                     (add_vec_int pc (if c then 2 else 4)) cmp Hred
                     Hc0 Hal0 with "Hcert Hfile HPC HnPC Hmisa") ].
      iIntros (e) "(-> & Hfile & HPC & HnPC & _)". iSplitR; [done|].
      iExists (add_vec pc (sign_extend' 64 imm)), m, n.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hsc". { iFrame "Hhw Hminv Hsc". }
      iFrame "Hcap Hfile". done.
    - iIntros (npc m2 n2) "Hcg' Hpc' (-> & -> & ->)".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

End WpSconfEngine.
