(* WpSwtchVc.v -- a whole-function WP for xv6's swtch(), via a small S-mode
   VCgen tailored to its instruction shapes.

   swtch (kernel/swtch.S) is a purely straight-line context switch:

       swtch:                          # a0 = old, a1 = new
         sd ra,0(a0)  ...  sd s11,104(a0)   # save 14 callee regs into *old
         ld ra,0(a1)  ...  ld s11,104(a1)   # load 14 callee regs from *new
         ret                                # jump to new->ra

   Two of the fourteen slots (s0,s1) compress to c.sd/c.ld (their registers and
   a0/a1 sit in x8..x15); the other twelve are full 4-byte sd/ld; the final
   [ret] is a c.ret (= jalr x0,0(x1)).  So the body is 28 general-base 8-byte
   loads/stores followed by a c.ret.

   The existing S-mode VCgen (VcGenS.v) only covers RVC value shapes and
   sp-relative 8-byte access; swtch needs general-base 8-byte sd/ld (both
   widths).  Rather than perturb [wp_vc_block_s_den] (used by mycpu/pop_off/
   kernelvec), this file grows a SELF-CONTAINED sibling VCgen -- reusing the
   shared symbolic machinery of VcGen.v (vstate / sval / vheap_own /
   vregs_den) -- whose two-constructor alphabet [swop] targets exactly the four
   leaf WPs of WpFreelistMem.v (wp_{sd,ld,csd,cld}_s_ram).

   [valid_context c] packages "the register set saved in the struct context at
   [c] admits a WP to run"; [wp_swtch] uses it to give swtch the natural
   context-switch spec: precondition [valid_context new]; the machine ends up
   running new's saved WP, handed [valid_context old] as its postcondition. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText.
Require Import SmodeCore.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SwtchCtx.
Require Import CodeSwtch.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* 1. Instruction DECODE facts for swtch's 29 instructions.                *)
(*    Base sd/ld: [swb_<word>]; compressed c.sd/c.ld: [swdc_<word>] +      *)
(*    clean ExecuteAs expansions [swx_<name>].  c.ret reuses podec/JR.     *)
(* ====================================================================== *)







(* ====================================================================== *)
(* 2. swtch's straight-line body as a program in the S-mode VCgen alphabet  *)
(*    [vop_s] (merged into VcGenS.v): 28 general-base 8-byte stores/loads    *)
(*    (VSsd/VSld).  Register indices: ra=1 sp=2 s0=8 s1=9 s2..s11=18..27,     *)
(*    a0=10 (old) a1=11 (new).                                              *)
(* ====================================================================== *)
Definition swtch_prog : list vop_s :=
  [ VSsd false (mword_of_int 0)   (mword_of_int 1)  (mword_of_int 10);
    VSsd false (mword_of_int 8)   (mword_of_int 2)  (mword_of_int 10);
    VSsd true  (mword_of_int 16)  (mword_of_int 8)  (mword_of_int 10);
    VSsd true  (mword_of_int 24)  (mword_of_int 9)  (mword_of_int 10);
    VSsd false (mword_of_int 32)  (mword_of_int 18) (mword_of_int 10);
    VSsd false (mword_of_int 40)  (mword_of_int 19) (mword_of_int 10);
    VSsd false (mword_of_int 48)  (mword_of_int 20) (mword_of_int 10);
    VSsd false (mword_of_int 56)  (mword_of_int 21) (mword_of_int 10);
    VSsd false (mword_of_int 64)  (mword_of_int 22) (mword_of_int 10);
    VSsd false (mword_of_int 72)  (mword_of_int 23) (mword_of_int 10);
    VSsd false (mword_of_int 80)  (mword_of_int 24) (mword_of_int 10);
    VSsd false (mword_of_int 88)  (mword_of_int 25) (mword_of_int 10);
    VSsd false (mword_of_int 96)  (mword_of_int 26) (mword_of_int 10);
    VSsd false (mword_of_int 104) (mword_of_int 27) (mword_of_int 10);
    VSld false (mword_of_int 0)   (mword_of_int 11) (mword_of_int 1);
    VSld false (mword_of_int 8)   (mword_of_int 11) (mword_of_int 2);
    VSld true  (mword_of_int 16)  (mword_of_int 11) (mword_of_int 8);
    VSld true  (mword_of_int 24)  (mword_of_int 11) (mword_of_int 9);
    VSld false (mword_of_int 32)  (mword_of_int 11) (mword_of_int 18);
    VSld false (mword_of_int 40)  (mword_of_int 11) (mword_of_int 19);
    VSld false (mword_of_int 48)  (mword_of_int 11) (mword_of_int 20);
    VSld false (mword_of_int 56)  (mword_of_int 11) (mword_of_int 21);
    VSld false (mword_of_int 64)  (mword_of_int 11) (mword_of_int 22);
    VSld false (mword_of_int 72)  (mword_of_int 11) (mword_of_int 23);
    VSld false (mword_of_int 80)  (mword_of_int 11) (mword_of_int 24);
    VSld false (mword_of_int 88)  (mword_of_int 11) (mword_of_int 25);
    VSld false (mword_of_int 96)  (mword_of_int 11) (mword_of_int 26);
    VSld false (mword_of_int 104) (mword_of_int 11) (mword_of_int 27) ].

(* struct-context field layout: field i (0..13) holds register [ctx_regs !! i]
   at byte offset 8*i -- ra sp s0 s1 s2 .. s11 ([ctx_regs] in SwtchCtx.v). *)
Definition ctx_regs_nat : list nat :=
  [ 1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27 ]%nat.

(* a struct-context-shaped segment of the symbolic 8-byte heap: base register
   [breg], one cell per value-register index in [ws], at offsets off, off+8,.... *)
Fixpoint seg_cells (breg : nat) (off : Z) (ws : list nat) : list (sval * sval) :=
  match ws with
  | [] => []
  | w :: rest => (SX breg off, SX w 0) :: seg_cells breg (off + 8) rest
  end.

(* initial heap: old's 14 cells (base a0 = SX 10) hold arbitrary values
   SX 46..59; new's 14 (base a1 = SX 11) hold the saved values SX 32..45. *)
Definition swtch_heap0 : list (sval * sval) :=
  seg_cells 10 0 [46;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.
(* post-block heap: old's cells now hold the current callee regs (ctx_regs_nat);
   new's cells are unchanged. *)
Definition swtch_heap1 : list (sval * sval) :=
  seg_cells 10 0 ctx_regs_nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.

(* post-block registers: ra sp s0..s11 now hold new's saved values SX 32..45,
   in struct-context field order; a0 = SX 10, a1 = SX 11 unchanged. *)
Definition swtch_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 27) := SX 45 0]>
  (<[Regidx (mword_of_int 26) := SX 44 0]>
  (<[Regidx (mword_of_int 25) := SX 43 0]>
  (<[Regidx (mword_of_int 24) := SX 42 0]>
  (<[Regidx (mword_of_int 23) := SX 41 0]>
  (<[Regidx (mword_of_int 22) := SX 40 0]>
  (<[Regidx (mword_of_int 21) := SX 39 0]>
  (<[Regidx (mword_of_int 20) := SX 38 0]>
  (<[Regidx (mword_of_int 19) := SX 37 0]>
  (<[Regidx (mword_of_int 18) := SX 36 0]>
  (<[Regidx (mword_of_int 9)  := SX 35 0]>
  (<[Regidx (mword_of_int 8)  := SX 34 0]>
  (<[Regidx (mword_of_int 2)  := SX 33 0]>
  (<[Regidx (mword_of_int 1)  := SX 32 0]> vregs_init))))))))))))).

Lemma swtch_run :
  vc_block_s (VSt KernelSyms.swtch vregs_init swtch_heap0 []) swtch_prog
  = Some (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Section WpSwtchVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.




  (* the 28-instruction body's code resource, extracted from kernel_text. *)
  Lemma swtch_code : kernel_text -∗ block_instrs_s KernelSyms.swtch swtch_prog.
  Proof.
    iIntros "#Ht".
    cbn [block_instrs_s swtch_prog vop_s_rvc vop_s_ast vop_s_w].
    iSplitR; [by iApply swi_00|].
    iSplitR; [by iApply swi_04|].
    iSplitR; [by iApply swi_08|].
    iSplitR; [by iApply swi_0a|].
    iSplitR; [by iApply swi_0c|].
    iSplitR; [by iApply swi_10|].
    iSplitR; [by iApply swi_14|].
    iSplitR; [by iApply swi_18|].
    iSplitR; [by iApply swi_1c|].
    iSplitR; [by iApply swi_20|].
    iSplitR; [by iApply swi_24|].
    iSplitR; [by iApply swi_28|].
    iSplitR; [by iApply swi_2c|].
    iSplitR; [by iApply swi_30|].
    iSplitR; [by iApply swi_34|].
    iSplitR; [by iApply swi_38|].
    iSplitR; [by iApply swi_3c|].
    iSplitR; [by iApply swi_3e|].
    iSplitR; [by iApply swi_40|].
    iSplitR; [by iApply swi_44|].
    iSplitR; [by iApply swi_48|].
    iSplitR; [by iApply swi_4c|].
    iSplitR; [by iApply swi_50|].
    iSplitR; [by iApply swi_54|].
    iSplitR; [by iApply swi_58|].
    iSplitR; [by iApply swi_5c|].
    iSplitR; [by iApply swi_60|].
    iSplitR; [by iApply swi_64|].
    done.
  Qed.

  (* [ctx_cells] / [callee_img] / [ret_pc] live in SwtchCtx.v. *)

  (* a heap segment's denotation IS the ctx-cell ownership of its values. *)
  Lemma seg_cells_ctx (rho : nat -> mword 64) (breg : nat) (c : mword 64)
      (off : Z) (ws : list nat) :
    rho breg = c ->
    ([∗ list] j ∈ seg_cells breg off ws, sval_den rho j.1 ↦₈ sval_den rho j.2)
    ⊣⊢ ctx_cells_at c off (map (fun w => rho w) ws).
  Proof.
    intro Hc. revert off. induction ws as [|w rest IH]; intro off.
    - reflexivity.
    - cbn [seg_cells map ctx_cells_at]. rewrite big_sepL_cons. cbn [fst snd].
      rewrite IH.
      assert (Ha : sval_den rho (SX breg off) = add_vec c (mword_of_int off))
        by (cbn [sval_den]; rewrite Hc; reflexivity).
      assert (Hv : sval_den rho (SX w 0) = rho w) by (apply sval_den_SX0).
      rewrite Ha Hv. reflexivity.
  Qed.

  (* a 14-element list equals its own [nth]-expansion. *)
  Lemma list14_nth (l : list (mword 64)) (d : mword 64) :
    length l = 14%nat ->
    [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d; nth 6 l d;
     nth 7 l d; nth 8 l d; nth 9 l d; nth 10 l d; nth 11 l d; nth 12 l d; nth 13 l d]
    = l.
  Proof.
    intro H.
    do 14 (destruct l as [|? l]; [simpl in H; lia|]).
    destruct l; [reflexivity | simpl in H; lia].
  Qed.

  (* [valid_context] and its fixpoint machinery live in SwtchCtx.v; the
     sconf-tier whole-function swtch spec lives in SpecSwtch.v /
     ProofSwtch.v. *)


End WpSwtchVc.

