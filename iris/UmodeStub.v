(* UmodeStub.v -- THE xv6 SYSCALL STUB, once.
   (claude-notes/projects/user-verified.md is the tier.)

   Every entry in user/usys.S is the same three instructions

     <stub>+0  c.li  a7, N
     <stub>+2  ecall
     <stub>+6  c.jr  ra

   and they differ only in the address, the number, and WHICH arm of the
   process's protocol the [ecall] then has to be fed.  sh has eleven of
   them, init has eight, echo two, sync two.  So the shared HEAD (the [li]
   and the [ecall], ending at the protocol payload) and the shared TAIL
   (the [ret], for the arms that come back) are proved HERE, once,
   PROGRAM- AND PROTOCOL-GENERIC: the protocol [Ps] is a parameter the
   lemmas never inspect, and every closed side condition is a premise, so
   a stub is its arm plus two lines.

   This is the same factoring UmodeFrame.v does for the gcc 16-byte frame,
   and for the same reason -- and it replaces the [wp_sh_stub_head] /
   [wp_sh_stub_tail] pair that was [Local] to UProofShLib.v, which is
   where the shape was worked out. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi.
Require Import WpUmodeStep WpUmodeLeaf.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

Section UmodeStub.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* THE HEAD: [c.li a7,N] then [ecall], ending at the protocol payload    *)
  (* for number [N] with a7 already set.  [Ps] is never inspected.         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_stub_head (CIDp : CpuId) (Ps : usys_protocol Σ) (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :
    uinstr pt M (mword_of_int entry) true
      (C_LI (mword_of_int n : mword 6, Regidx a7_idx)) ->
    uinstr pt M (mword_of_int (entry + 2)) false (ECALL tt) ->
    (mword_of_int n : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int n : mword 6))) ->
    add_vec_int (mword_of_int entry : mword 64) 2 = mword_of_int (entry + 2) ->
    uint (mword_of_int n : mword 64) = n ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) (mword_of_int entry) -∗
    (uv_cap C pt Ps -∗
       Ps n (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
          (mword_of_int (entry + 2)) M) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui1 Hui2 Hwv Hpc2 Hn.
    iIntros "Hcg Hpc Harm".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgpr)".
    iAssert (uv_cap_gpr (CID := CIDp) C pt Ps M m) with "[Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    iApply (wp_uv_cli C pt Ps M m (mword_of_int entry)
              (mword_of_int n : mword 6) a7_idx (mword_of_int n : mword 64)
              Hui1 ltac:(vm_compute; discriminate) Hwv
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int n : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by reflexivity.
    iEval (rewrite Hnorm) in "Hcg".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Em1 : m1 !!! Regidx a7_idx = (mword_of_int n : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int n : mword 64)).
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = n) by (rewrite Em1; exact Hn).
    iApply (wp_uv_ecall C pt Ps M m1 (mword_of_int (entry + 2)) Hui2
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int (entry + 2)) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int (entry + 2))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hcg Hpc").
    rewrite Ha7.
    iApply ("Harm" with "Hcap").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TAIL: the [ret] every returning stub ends with.  The resume       *)
  (* bundle comes back at [entry+6] with a0 set; [ra] survives both        *)
  (* inserts, and the caller's 2-alignment premise makes [ret_pc] the      *)
  (* identity on it.  The image is a PARAMETER [M'] -- a syscall that       *)
  (* wrote the caller's buffer hands back a different one.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_stub_tail (CIDp : CpuId) (Ps : usys_protocol Σ) (entry n : Z)
      (M' : gmap Z (bv 8)) (m : regfile) (r : mword 64) :
    uinstr pt M' (mword_of_int (entry + 6)) true (C_JR (Regidx ra_idx)) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uv_cap C pt Ps -∗
    uv_run (CID := CIDp) C pt M'
      (<[Regidx a0_idx := r]> (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m))
      (mword_of_int (entry + 6)) -∗
    (∀ CID : CpuId,
       uv_cap_gpr (CID := CID) C pt Ps M'
         (<[Regidx a0_idx := r]> (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui3 Hret2.
    iIntros "#Hcap Hrun Hcont".
    set (m2 := <[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)).
    iDestruct (uv_run_cap_gpr (CID := CIDp) C pt Ps M' m2 (mword_of_int (entry + 6))
                 with "Hcap Hrun") as "[Hcg Hpc]".
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
                  (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int n : mword 64) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx) = ret_pc (m2 !!! Regidx ra_idx)).
    { rewrite Hra. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Ps M' m2 (mword_of_int (entry + 6))
              ra_idx (m !!! Regidx ra_idx)
              Hui3 ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 with "Hcg Hpc").
  Qed.

End UmodeStub.
