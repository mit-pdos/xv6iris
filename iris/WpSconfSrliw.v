(* WpSconfSrliw.v -- the ONE leaf the fs.c inode layer needs and the
   S-mode ALU layer did not have: [srliw rd, rs1, shamt].

   iupdate computes IBLOCK(inum, sb) as [srliw a5,a5,0x4] (an unsigned
   divide of a [uint] by IPB = 16) followed by [addw], and no other proved
   function in the tree steps a 32-bit SHIFT-RIGHT immediate -- [slliw] is
   in WpSconfAlu.v and [srli]/[srai] are the 64-bit SHIFTIOP forms in
   WpMmodeShiftiop.v, but the W right shift is absent from both.

   BOTH HALVES BELONG ONE FILE LOWER: [exec_execute_SHIFTIWOP_SRLIW{,_gpr}]
   beside their SLLIW twins in WpMmodeShiftiop.v, and [wp_srliw_s_sconf]
   beside [wp_slliw_s_sconf] in WpSconfAlu.v.  They are here instead only
   because both of those files sit near the BOTTOM of the build (editing
   either invalidates the whole downstream .vo tree, which cannot be
   rebuilt from a single-file check loop -- see claude-notes/durable-notes.md
   "Editing a file near the BOTTOM of the tree").  Merging this file into
   those two, on a build that can afford a full rebuild, is owed. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeShiftiop.
Require Import SmodeCore.
Require Import IntrDefs WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* ---- the exec bridge, verbatim the SLLIW one at the other branch of
   [execute_SHIFTIWOP]'s three-way match ---- *)
Lemma exec_execute_SHIFTIWOP_SRLIW (shamt : mword 5) (rs1 rd : regidx)
    (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64
          (shift_bits_right (subrange_vec_dec a 31 0 : mword 32) shamt)))
       s = Some (tt, s') ->
  exec (execute (SHIFTIWOP (shamt, rs1, rd, SRLIW))) s
  = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIWOP (shamt, rs1, rd, SRLIW)))
    with (execute_SHIFTIWOP shamt rs1 rd SRLIW).
  unfold execute_SHIFTIWOP. cbn match.
  rewrite (exec_bind_Some _ _ _ a s Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_srliw_val (rs1 : mword 5) (shamt : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (shift_bits_right (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32) shamt).

Lemma exec_execute_SHIFTIWOP_SRLIW_gpr (rs1 rd : mword 5) (shamt : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_srliw_val rs1 shamt s))).
Proof.
  unfold gpr_srliw_val, gpr_src.
  eapply exec_execute_SHIFTIWOP_SRLIW.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Section WpSconfSrliw.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  (* SRLIW: shift the source's low 32 bits RIGHT (logically) by a 5-bit
     shamt, sign-extend the 32-bit result back.  The [wp_slliw_s_sconf]
     twin, verbatim. *)
  Lemma wp_srliw_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sign_extend' 64 (shift_bits_right (subrange_vec_dec (rget m rs1) 31 0 : mword 32) shamt)
      = wval ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base Φ pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW)) wval m n b
              Hrd Hrdok _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIWOP_SRLIW_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srliw_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

End WpSconfSrliw.
