(* ===================================================================== *)
(* UkBranch.v -- the CONDITIONAL-BRANCH leaves of the user-mode-ON-KERNEL *)
(* tier: WpUmodeBranch.v's leaves, stated against the kernel's U-mode     *)
(* bundle [UexecRet.uvb] with the table-re-binding continuation [ukc],    *)
(* over the UkStep.v engine (claude-notes/design/uk-engine.md).            *)
(*                                                                        *)
(* THE PORT IS A RE-THREAD AND NOTHING ELSE.  A branch touches no memory, *)
(* so nothing about the LAZY key -- the mapped sub-image, the permission  *)
(* projection, the transparent fault arm -- is visible here at all: the   *)
(* whole file rides [UkStep.wp_uk_retire[_later]] exactly as UkLeaf.v's   *)
(* 39 register-only leaves do.  The PURE half of WpUmodeBranch.v (the     *)
(* comparison function [uv_btaken], the value-precise execute fact        *)
(* [exec_execute_BTYPE_gpr_zca], its certificate twin and the pre-composed*)
(* [uv_btype_cert]) mentions no capability and is imported verbatim.      *)
(*                                                                        *)
(* The statements are WpUmodeBranch.v's with                              *)
(* [uv_cap_gpr C pt Ψ M m ∗ pc_is pc] read as [uvb C pt Rfd Rut sz π fdv cw M m pc]  *)
(* and [∀ CID0, uv_cap_gpr … M m -∗ pc_is pc' -∗ WP] read as              *)
(* [ukc π M sz fdv cw m pc']; the pure premises, the value convention and the       *)
(* proofs are unchanged.  The section carries the ambient table's guard   *)
(* ([loop_ok C pt], [perm_of (ud_um pt) sz = π]), which is what lets the  *)
(* retiring arm hand the bundle at THIS table to a continuation that      *)
(* accepts any table.                                                     *)
(*                                                                        *)
(* BOTH INTERFACES SURVIVE THE PORT, and for the reason WpUmodeBranch.v   *)
(* gives: [wp_uk_btype_later] / [wp_uk_btype_gen_later] /                 *)
(* [wp_uk_btype0_later] hand the step's own [▷] OUT, which is the only    *)
(* thing that lets a caller close an UNBOUNDED loop; the later-FREE       *)
(* restatements are what a bounded loop (echo's two) wants.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpGpr RegFile.
Require Import WpMmodeLeafBase.
Require Import WpDecodeBridge DecodeTotalU HartMemRun UserFrame.
Require UserTotalU.
Require Import UserPtTree UserExec.
Require Import WpUmodeStep WpUmodeBranch.
Require Import UserPerm UexecWp UexecRet UkStep.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

Section UkBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  (* A6.140: the loop borrows the running token out of [Rut pt] per step *)
  Hypothesis (HRut : forall pt' : uptd,
                       ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                                    (TsoCtx.own_context XI -∗ Rut pt')).

  (* RELOCATION DEBT: reads naturally beside [uv_next] in WpUmodeStep.v;
     kept here (as WpUmodeBranch.v keeps its own copy) so adding it does
     not rebuild the leaf tower. *)
  Local Lemma uk_next_bool (b : bool) (t d : mword 64) :
    uv_next (if b then Some t else None) d = (if b then t else d).
  Proof. destruct b; reflexivity. Qed.

  (* the x0 read, at an ARBITRARY zero index -- [UkStep.uvb_x0] pins it at
     the literal [mword_of_int 0] and the compressed branches need it at
     [WpMmodeLeafBase.cli_rs1].  Same proof, one binder wider. *)
  Local Lemma uvb_zero_at (r : mword 5) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) :
    uint r = 0 ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ⌜m !!! Regidx r = zero_reg⌝ ∗ uvb C pt Rfd Rut sz π fdv cw M m pc.
  Proof.
    intros Hr.
    rewrite /uvb /uvb_F.
    iIntros "(Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct (gpr_file_x0 m r Hr with "Hg") as "[%Hz Hg]".
    iSplitR; [ iPureIntro; exact Hz | ].
    iFrame "Hamb Hur Hpt Hfrag Hcfg Hg Hpc Hrut Hk";
      try (iPureIntro; exact Hsz).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The core.  Beyond [wp_uk_btype] it abstracts the three axes the       *)
  (* funnel already has -- the fetch width [is_rvc], the DECODED ast [i],  *)
  (* and the [ExecuteAs] redirect [o] -- so that the compressed branches   *)
  (* are instances rather than re-proofs.                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_btype_gen_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    uv_exp i o = BTYPE (imm, Regidx rs2, Regidx rs1, op) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ▷ ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hg1 Hexp Htaken Htgt Halign.
    iIntros "Hb Hcont".
    (* re-shape the continuation into the funnel's [uv_upd]/[uv_next] form *)
    iAssert (▷ ukc π M sz fdv cw (uv_upd m None)
               (uv_next (if taken then Some tgt else None)
                  (add_vec_int pc (if is_rvc then 2 else 4))))%I
      with "[Hcont]" as "Hcont".
    { iNext. rewrite uk_next_bool. iExact "Hcont". }
    iApply (wp_uk_retire_later C pt Rfd Rut π sz Hlo Hpm HRut M m pc fdv cw is_rvc i o
              (if taken then Some tgt else None) None
              Hui Hred Hlpad I Hg1
              ltac:(intros s_pc Lpc Lnpc Lcp Hag Hvals;
                    rewrite Hexp;
                    exact (uv_btype_cert M m pc is_rvc imm rs2 rs1 op taken tgt
                             Htaken Htgt Halign s_pc Lpc Lnpc Lcp Hag Hvals))
              with "Hb Hcont").
    intros s_pc Lpc _ _ Hag Hvals.
    rewrite Hexp.
    rewrite (exec_execute_BTYPE_gpr_zca imm rs2 rs1 op
               (m !!! Regidx rs1) (m !!! Regidx rs2) taken s_pc
               (Hvals rs1) (Hvals rs2) Htaken
               ltac:(intro Ht; rewrite Lpc; rewrite <- Htgt; exact (Halign Ht))
               (agree_u_zca s_pc Hag)).
    rewrite Lpc. rewrite <- Htgt. reflexivity.
  Qed.

  (* the later-FREE restatement, which is what the compressed instances and
     every bounded-loop caller take *)
  Lemma wp_uk_btype_gen (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    uv_exp i o = BTYPE (imm, Regidx rs2, Regidx rs1, op) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hg1 Hexp Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iApply (wp_uk_btype_gen_later M m pc fdv cw is_rvc i o imm rs2 rs1 op taken tgt
              Hui Hred Hlpad Hg1 Hexp Htaken Htgt Halign
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* beq / bne / blt / bge / bltu / bgeu -- ONE leaf.                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_btype (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    exact (wp_uk_btype_gen M m pc fdv cw false
             (BTYPE (imm, Regidx rs2, Regidx rs1, op)) None
             imm rs2 rs1 op taken tgt
             Hui (fun _ => I) eq_refl
             (uv_btype_cert M m pc false imm rs2 rs1 op taken tgt
                Htaken Htgt Halign)
             eq_refl Htaken Htgt Halign).
  Qed.

  (* ... and the same leaf handing the step's later OUT, which is what a
     caller closing an UNBOUNDED loop across this branch needs. *)
  Lemma wp_uk_btype_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ▷ ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    exact (wp_uk_btype_gen_later M m pc fdv cw false
             (BTYPE (imm, Regidx rs2, Regidx rs1, op)) None
             imm rs2 rs1 op taken tgt
             Hui (fun _ => I) eq_refl
             (uv_btype_cert M m pc false imm rs2 rs1 op taken tgt
                Htaken Htgt Halign)
             eq_refl Htaken Htgt Halign).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The BASE branch against x0 -- [beqz]/[bnez]/[bltz]/[bgez], which the  *)
  (* assembler emits as [BTYPE (imm, x0, rs1, op)].  The x0 read is the    *)
  (* one thing a pure premise cannot supply, so it is taken off the        *)
  (* bundle here ([UkStep.uvb_x0]) and the leaf's own premise talks about  *)
  (* [zero_reg].                                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_btype0_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ▷ ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iDestruct (uvb_x0 with "Hb") as "[%Hz Hb]".
    iApply (wp_uk_btype_later M m pc fdv cw imm (mword_of_int 0 : mword 5) rs1 op
              taken tgt Hui ltac:(rewrite Hz; exact Htaken) Htgt Halign
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_btype0 (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iApply (wp_uk_btype0_later M m pc fdv cw imm rs1 op taken tgt
              Hui Htaken Htgt Halign with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.beqz rs', imm -- the compressed branch-if-zero (echo's 0xcf91,      *)
  (* [c.beqz a5,+0x1c]).  It decodes to [C_BEQZ] and expands to            *)
  (*   BTYPE (sext13 (imm ++ 0), x0, rs, BEQ),                             *)
  (* so is_rvc = true and the second operand is x0, whose value comes off  *)
  (* the bundle.                                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cbeqz (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 8) (cr : mword 3) (rs : mword 5)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc true (C_BEQZ (imm, Cregidx cr)) ->
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = eq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iDestruct (uvb_zero_at cli_rs1 M m pc fdv cw ltac:(vm_compute; reflexivity)
                 with "Hb") as "[%Hz Hb]".
    iApply (wp_uk_btype_gen M m pc fdv cw true (C_BEQZ (imm, Cregidx cr))
              (Some (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")),
                            Regidx cli_rs1, Regidx rs, BEQ)))
              (sign_extend' 13 (concat_vec imm ('b"0"))) cli_rs1 rs BEQ taken tgt
              Hui
              ltac:(intro s;
                    rewrite (exec_execute_C_BEQZ imm (Cregidx cr) s);
                    rewrite Hcr; reflexivity)
              eq_refl
              (fun s _ _ _ _ _ =>
                 UserTotalU.goodmb_execute_C_BEQZ_U Du_r Du_w imm (Cregidx cr) s)
              eq_refl
              ltac:(cbn [uv_btaken]; rewrite Hz; exact Htaken)
              Htgt Halign
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs', imm -- the compressed branch-if-nonzero (echo's 0xff65,   *)
  (* [c.bnez a4,-0x8], the backward edge of a bounded loop).               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cbnez (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (imm : mword 8) (cr : mword 3) (rs : mword 5)
      (taken : bool) (tgt : mword 64) :
    uk_instr π M pc true (C_BNEZ (imm, Cregidx cr)) ->
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = neq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uvb C pt Rfd Rut sz π fdv cw M m pc -∗
    ukc π M sz fdv cw m (if taken then tgt else add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr Htaken Htgt Halign.
    iIntros "Hb Hcont".
    iDestruct (uvb_zero_at cli_rs1 M m pc fdv cw ltac:(vm_compute; reflexivity)
                 with "Hb") as "[%Hz Hb]".
    iApply (wp_uk_btype_gen M m pc fdv cw true (C_BNEZ (imm, Cregidx cr))
              (Some (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")),
                            Regidx cli_rs1, Regidx rs, BNE)))
              (sign_extend' 13 (concat_vec imm ('b"0"))) cli_rs1 rs BNE taken tgt
              Hui
              ltac:(intro s;
                    rewrite (exec_execute_C_BNEZ imm (Cregidx cr) s);
                    rewrite Hcr; reflexivity)
              eq_refl
              (fun s _ _ _ _ _ =>
                 UserTotalU.goodmb_execute_C_BNEZ Du_r Du_w imm (Cregidx cr) s)
              eq_refl
              ltac:(cbn [uv_btaken]; rewrite Hz; exact Htaken)
              Htgt Halign
              with "Hb Hcont").
  Qed.

End UkBranch.
