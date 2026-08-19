(* WpUmodeBranch.v -- the CONDITIONAL-BRANCH leaves of the VERIFIED
   user-execution tier (claude-notes/projects/user-verified.md,
   claude-notes/projects/user-echo.md).

   ONE GENERIC LEAF, NOT AN OP CROSS-PRODUCT.  The model's [execute_BTYPE]
   (Riscv.rv64d) is UNIFORM: whatever the branch op, it reads the two
   source registers with [rX_bits], compares them with an op-indexed
   predicate into a bool [taken], and then either reads PC and [jump_to]s
   [PC + sext imm] or falls through with [RETIRE_SUCCESS].  Nothing else
   varies.  So the whole family is captured by ONE pure comparison
   function [uv_btaken], ONE execute fact [exec_execute_BTYPE_gpr_zca]
   parameterised by the [taken] bool, and ONE leaf [wp_uv_btype] whose
   funnel arguments are

     jt := if taken then Some (pc + sext imm) else None,   wr := None.

   That is exactly what the retire funnel's OPTIONAL [jt] already
   expresses, so the taken and fall-through arms are the SAME instance of
   [wp_uv_retire] rather than two.  Contrast the S-mode tier's
   WpSmodePtBtype.v, which carries eight per-(op, taken/fall) lemmas: that
   6 x 2 cross-product is precisely what this file exists not to clone
   (claude-notes/durable-notes.md, "one general lemma over N special
   cases").

   BOTH INTERFACES ARE HERE, and which one a caller wants is decided by
   whether its loop is bounded.

     [wp_uv_btype_later] / [wp_uv_btype_gen_later] hand the step's own
     [|>] OUT, which is the only thing that lets a caller close an
     UNBOUNDED loop: an [iLoeb] IH is [|>]-guarded, and a later-free leaf
     can never strip it.  A branch-TAKEN edge is the back edge of a loop,
     so this is exactly the leaf that needs the general form -- the same
     role [wp_cbnez_taken_s] plays in the kernel tier
     (design/kernel-proofs.md).  Note that the later is exposed in BOTH
     arms, not only the taken one: [taken] is a parameter of one lemma
     here, not a case split into two, and a caller's [iNext] is harmless
     on the fall-through arm.

     [wp_uv_btype] / [wp_uv_btype_gen] / [wp_uv_cbeqz] / [wp_uv_cbnez] are
     the later-FREE restatements, which absorb it with their own [iNext].
     echo's two loops ([strlen], and [main]'s walk over argv) and every
     loop in sh are BOUNDED -- ordinary Rocq induction on a nat measure,
     no [iLoeb], no [|>] anywhere -- and those callers want this shape.

   init (claude-notes/projects/user-init.md) is the first program with a
   genuinely unbounded loop, and both of its back edges are base BTYPEs
   ([beq s1,a0] closing the restart loop, [bgez a0] closing the wait loop),
   which is why the later-exposing form is stated for the base leaf.

   The compressed instances are [wp_uv_cbeqz] / [wp_uv_cbnez] (echo's
   0xcf91 = c.beqz a5,+0x1c and 0xff65 = c.bnez a4,-0x8).  They are
   [ExecuteAs] redirects into a base BTYPE against x0, so they are derived
   from the same core -- see [wp_uv_btype_gen], which abstracts the three
   axes the funnel already has (is_rvc, the decoded AST, the redirect).

   VALUE CONVENTION (claude-notes/design/code-organization.md): every leaf
   takes [taken] and the jump target [tgt] as explicit binders with PURE
   hypotheses fixing them, so a call site's continuation mentions closed
   terms rather than comparisons of lookups. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep.
Require Import InstrBytes WpGpr RegFile.
Require Import ExecCommon WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap.
Require Import WpUmodeStep.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* The branch condition, as a pure function of the op and the two source   *)
(* VALUES.  One clause per constructor of [bop], transcribed from          *)
(* [execute_BTYPE]'s comparison prefix (Riscv.rv64d); the model's names    *)
(* [zopz0zI_s] / [zopz0zKzJ_s] / ... are Sail's manglings of < <= over     *)
(* signed / unsigned words.                                                *)
(* ---------------------------------------------------------------------- *)
Definition uv_btaken (op : bop) (v1 v2 : mword 64) : bool :=
  match op with
  | BEQ  => eq_vec v1 v2
  | BNE  => neq_vec v1 v2
  | BLT  => zopz0zI_s v1 v2
  | BGE  => zopz0zKzJ_s v1 v2
  | BLTU => zopz0zI_u v1 v2
  | BGEU => zopz0zKzJ_u v1 v2
  end.

(* ---------------------------------------------------------------------- *)
(* [exec_execute_BTYPE_gpr_zca] -- the value-precise execute fact for the   *)
(* WHOLE BTYPE family, in BOTH outcomes, as ONE lemma.                      *)
(*                                                                          *)
(* The two source premises are written in exactly the shape the retire      *)
(* funnel hands its leaves (the x0-aware [rX_bits] read, [WpGpr.            *)
(* exec_rX_bits_gpr]), so a leaf discharges them with the funnel's [Hvals]  *)
(* and nothing else.  The conclusion lands on the funnel's own post-state   *)
(* tower [uv_post s jt None] -- a branch never writes a register, and its   *)
(* only state effect is the OPTIONAL nextPC redirect, which is what makes   *)
(* the taken and fall-through arms one lemma instead of two.                *)
(*                                                                          *)
(* Alignment is required only when the branch is TAKEN (the fall-through    *)
(* arm never reaches [jump_to]'s assert), hence the hypothesis is guarded   *)
(* by [taken = true]; under Zca only bit 0 must be clear (see               *)
(* ExecCommon.exec_jump_to_zca), which is a decoder invariant at every real *)
(* call site.                                                               *)
(*                                                                          *)
(* RELOCATION DEBT: this is the value-precise strengthening of              *)
(* UserExecFacts.exec_execute_BTYPE_total (which only says the post state   *)
(* is one of the two) and belongs beside it; it is kept here so that adding *)
(* it does not rebuild the classification/totality tower.                   *)
(* ---------------------------------------------------------------------- *)
Lemma exec_execute_BTYPE_gpr_zca (imm : mword 13) (rs2 rs1 : mword 5)
    (op : bop) (v1 v2 : mword 64) (taken : bool) (s : mstate) :
  (if Z.eqb (uint rs1) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = v1 ->
  (if Z.eqb (uint rs2) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v2 ->
  taken = uv_btaken op v1 v2 ->
  (taken = true ->
   eq_vec (access_vec_dec
             (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0)
          ('b"0") = true) ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, op))) s
  = Some (RETIRE_SUCCESS,
          uv_post s
            (if taken
             then Some (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))
             else None)
            None).
Proof.
  intros Hv1 Hv2 Htaken Halign Hzca.
  (* the comparison prefix, once, for an arbitrary comparison [f] *)
  assert (Hcmp : forall f : mword 64 -> mword 64 -> bool,
            exec (Defs.bind (rX_bits (Regidx rs1))
                    (fun w1 => Defs.bind (rX_bits (Regidx rs2))
                       (fun w2 => returnM (f w1 w2)))) s
            = Some (f v1 v2, s)).
  { intro f.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)). cbn beta.
    rewrite Hv1. rewrite Hv2. apply exec_returnM. }
  change (execute (BTYPE (imm, Regidx rs2, Regidx rs1, op)))
    with (execute_BTYPE imm (Regidx rs2) (Regidx rs1) op).
  unfold execute_BTYPE.
  destruct op; cbn [uv_btaken] in Htaken;
    [ rewrite (exec_bind_Some _ _ _ _ _ (Hcmp eq_vec))
    | rewrite (exec_bind_Some _ _ _ _ _ (Hcmp neq_vec))
    | rewrite (exec_bind_Some _ _ _ _ _ (Hcmp zopz0zI_s))
    | rewrite (exec_bind_Some _ _ _ _ _ (Hcmp zopz0zKzJ_s))
    | rewrite (exec_bind_Some _ _ _ _ _ (Hcmp zopz0zI_u))
    | rewrite (exec_bind_Some _ _ _ _ _ (Hcmp zopz0zKzJ_u)) ].
  all: cbn beta; destruct taken; rewrite <- Htaken;
       cbn [uv_post uv_jmp uv_wr].
  all: try (apply exec_returnM).
  all: rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)); cbn beta;
       exact (exec_jump_to_zca _ s (Halign eq_refl) Hzca).
Qed.

Section WpUmodeBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* RELOCATION DEBT: reads naturally beside [uv_next] in WpUmodeStep.v;
     kept here so adding it does not rebuild the leaf tower. *)
  Local Lemma uv_next_bool (b : bool) (t d : mword 64) :
    uv_next (if b then Some t else None) d = (if b then t else d).
  Proof. destruct b; reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* The core.  Beyond [wp_uv_btype] it abstracts the three axes the       *)
  (* funnel already has -- the fetch width [is_rvc], the DECODED ast [i],  *)
  (* and the [ExecuteAs] redirect [o] -- so that the compressed branches,  *)
  (* which decode to [C_BEQZ]/[C_BNEZ] and expand to a base BTYPE against  *)
  (* x0, are instances rather than re-proofs.  Everything else (the        *)
  (* comparison, the target, the two arms) is shared verbatim.             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_btype_gen_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_exp i o = BTYPE (imm, Regidx rs2, Regidx rs1, op) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
         pc_is (CID := CID0)
           (if taken then tgt else add_vec_int pc (if is_rvc then 2 else 4)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hexp Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    (* re-shape the continuation into the funnel's [uv_upd]/[uv_next] form *)
    iAssert (▷ (∀ CID0 : CpuId,
                  uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m None) -∗
                  pc_is (CID := CID0)
                    (uv_next (if taken then Some tgt else None)
                       (add_vec_int pc (if is_rvc then 2 else 4))) -∗
                  WP (Loop : expr riscv_lang)))%I with "[Hcont]" as "Hcont".
    { iNext. rewrite uv_next_bool. iExact "Hcont". }
    iApply (wp_uv_retire_later C pt Ψ M m pc is_rvc i o
              (if taken then Some tgt else None) None
              Hui Hred Hlpad I with "Hcg Hpc Hcont").
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
  Lemma wp_uv_btype_gen (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_exp i o = BTYPE (imm, Regidx rs2, Regidx rs1, op) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0)
         (if taken then tgt else add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hexp Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_btype_gen_later Ψ M m pc is_rvc i o imm rs2 rs1 op taken tgt
              Hui Hred Hlpad Hexp Htaken Htgt Halign with "Hcg Hpc [Hcont]").
    iNext. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* beq / bne / blt / bge / bltu / bgeu -- ONE leaf.  The op is a         *)
  (* parameter, the outcome is the [taken] parameter, and the pure premise *)
  (* [taken = uv_btaken op ...] is what a call site discharges (by         *)
  (* [vm_compute] when both operands are closed, or by the surrounding     *)
  (* loop invariant when they are not).  Memory and the register file are  *)
  (* UNCHANGED -- a branch's only effect is on the pc.                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_btype (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    exact (wp_uv_btype_gen Ψ M m pc false
             (BTYPE (imm, Regidx rs2, Regidx rs1, op)) None
             imm rs2 rs1 op taken tgt
             Hui (fun _ => I) eq_refl eq_refl Htaken Htgt Halign).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ... and the same leaf handing the step's later OUT, which is what a   *)
  (* caller closing an UNBOUNDED loop across this branch needs.  init's    *)
  (* restart loop ([beq s1,a0] back to main+0x32) and its wait loop        *)
  (* ([bgez a0] back to main+0x44) are both closed with this.              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_btype_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
         pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 4) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    exact (wp_uv_btype_gen_later Ψ M m pc false
             (BTYPE (imm, Regidx rs2, Regidx rs1, op)) None
             imm rs2 rs1 op taken tgt
             Hui (fun _ => I) eq_refl eq_refl Htaken Htgt Halign).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The BASE branch against x0 -- [beqz]/[bnez]/[bltz]/[bgez], which the  *)
  (* assembler emits as [BTYPE (imm, x0, rs1, op)].  The x0 read is the    *)
  (* one thing a pure premise cannot supply, so it is taken off            *)
  (* [gpr_file] here ([WpGpr.gpr_file_x0]) exactly as the compressed       *)
  (* [wp_uv_cbeqz] does, and the leaf's own premise talks about            *)
  (* [zero_reg].  init has four of these (two closing its unbounded        *)
  (* loops), which is why they get a leaf rather than a per-site           *)
  (* [gpr_file_x0] dance.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_btype0_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
         pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 4) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 m (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hgpr") as "[%Hz Hgpr]".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hcap Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    iApply (wp_uv_btype_later Ψ M m pc imm (mword_of_int 0 : mword 5) rs1 op
              taken tgt Hui ltac:(rewrite Hz; exact Htaken) Htgt Halign
              with "Hcg Hpc Hcont").
  Qed.

  Lemma wp_uv_btype0 (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) ->
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_btype0_later Ψ M m pc imm rs1 op taken tgt
              Hui Htaken Htgt Halign with "Hcg Hpc [Hcont]").
    iNext. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.beqz rs', imm -- the compressed branch-if-zero (echo's 0xcf91,      *)
  (* [c.beqz a5,+0x1c]).  It decodes to [C_BEQZ] and expands               *)
  (* ([WpMmodeLeafBase.exec_execute_C_BEQZ]) to                            *)
  (*   BTYPE (sext13 (imm ++ 0), x0, rs, BEQ),                             *)
  (* so: is_rvc = true (the fall-through pc advances by TWO), the source    *)
  (* index is a COMPRESSED one -- the expanded index [rs] is a parameter    *)
  (* with the decoder's expansion as a pure premise, as in                  *)
  (* [wp_uv_caddi4spn] -- and the second operand is x0.  The x0 read is the *)
  (* one thing the pure premises cannot supply, so it is taken off          *)
  (* [gpr_file] here ([WpGpr.gpr_file_x0]) and the leaf's own premise talks *)
  (* about [zero_reg] directly.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cbeqz (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 8) (cr : mword 3) (rs : mword 5)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc true (C_BEQZ (imm, Cregidx cr)) ->
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = eq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 m cli_rs1 ltac:(vm_compute; reflexivity) with "Hgpr")
      as "[%Hz Hgpr]".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hcap Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    iApply (wp_uv_btype_gen Ψ M m pc true (C_BEQZ (imm, Cregidx cr))
              (Some (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")),
                            Regidx cli_rs1, Regidx rs, BEQ)))
              (sign_extend' 13 (concat_vec imm ('b"0"))) cli_rs1 rs BEQ taken tgt
              Hui
              ltac:(intro s;
                    rewrite (exec_execute_C_BEQZ imm (Cregidx cr) s);
                    rewrite Hcr; reflexivity)
              eq_refl eq_refl
              ltac:(cbn [uv_btaken]; rewrite Hz; exact Htaken)
              Htgt Halign
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs', imm -- the compressed branch-if-nonzero (echo's 0xff65,   *)
  (* [c.bnez a4,-0x8], the backward edge of a bounded loop).  Identical to *)
  (* [wp_uv_cbeqz] but for [BNE]; both are the same [wp_uv_btype_gen]      *)
  (* instance up to the op and the comparison.                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cbnez (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 8) (cr : mword 3) (rs : mword 5)
      (taken : bool) (tgt : mword 64) :
    uinstr pt M pc true (C_BNEZ (imm, Cregidx cr)) ->
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = neq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) (if taken then tgt else add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr Htaken Htgt Halign.
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 m cli_rs1 ltac:(vm_compute; reflexivity) with "Hgpr")
      as "[%Hz Hgpr]".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hcap Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    iApply (wp_uv_btype_gen Ψ M m pc true (C_BNEZ (imm, Cregidx cr))
              (Some (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")),
                            Regidx cli_rs1, Regidx rs, BNE)))
              (sign_extend' 13 (concat_vec imm ('b"0"))) cli_rs1 rs BNE taken tgt
              Hui
              ltac:(intro s;
                    rewrite (exec_execute_C_BNEZ imm (Cregidx cr) s);
                    rewrite Hcr; reflexivity)
              eq_refl eq_refl
              ltac:(cbn [uv_btaken]; rewrite Hz; exact Htaken)
              Htgt Halign
              with "Hcg Hpc Hcont").
  Qed.

End WpUmodeBranch.
