(* ProofKernelvec.v -- the complete WP for xv6's kernelvec, the S-mode trap
   vector (kernelvec.S), as a sealed functor over its one callee's contract
   ([SpecKerneltrap.KERNELTRAP_RETURNS]).

     kernelvec:
       addi sp, sp, -256          # 1 instr : open the frame
       sd   ra, 0(sp)  ... sd t6, 240(sp)   # 17 c.sdsp : save the caller-saved
       call kerneltrap            # THE call (the assumed contract)
       ld   ra, 0(sp)  ... ld t6, 240(sp)   # 17 c.ldsp : restore them
       addi sp, sp, 256           # close the frame
       sret                       # back to the interrupted pc

   The pieces, bottom up:
   - [kv_cfg_split] / [kv_cfg_recombine]: the wp_start-style fraction
     choreography -- full raw cells <-> smode_config(1/2) + retained halves
     with the mstatus/mie/mideleg/menvcfg VALUES pinned outside the bundle.
   - [wp_kv_store_block_vc] / [wp_kv_load_block_vc]: the two 17-instruction
     straight-line runs, discharged through the block VCgen (VcGenS.v) rather
     than instruction by instruction.
   - [wp_kv_prologue]    : instrs #1..#19 (c.addi16sp fill-fetch, the 17
     c.sdsp saves incl. the data-walk fill, jal kerneltrap).
   - [wp_kv_epilogue]    : instrs #20..#38 (17 c.ldsp restores, c.addi16sp
     sp,+256, sret).
   - [wp_kernelvec]      : entry-to-SRET, gpr file FULLY PRESERVED (the loads
     restore the stores; -256/+256 cancels on sp).  Carries its mstatus /
     menvcfg parameters and their well-formedness premises explicitly.
   - [kernelvec_handler_spec] : THE public contract (SpecKernelvec.v) -- the
     cap that instantiates [wp_kernelvec] at MENVCFG_S and re-addresses
     kernelvec's 17 sparse save windows as [pa_stk] slots of the per-trap
     [intr_frame], so a trap into kernelvec returns idempotently to the
     interrupted pc with SIE re-enabled and the frame intact.  The SIE ghost
     kernelvec's WP consumes is a FRESH per-trap name [γk] (allocated here,
     tied to the trapped SIE=0 and discarded at the sret) -- the REAL [γ]'s
     pieces stay outside the handler run, untouched, so the live-bit tie is
     restored for free when SRET brings SIE back to 1.

   Only [Kerneltrap.kerneltrap_returns] + platform externs are assumed, and
   that one arrives through the functor parameter -- see LinkKerneltrap.v. *)
From Stdlib Require Import ZArith Bool FunctionalExtensionality.
From stdpp Require Import gmap finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase StackOwn.
Require Import SmodeCore KernelText CodeKernelvec.
Require Import HartTp CalleeSaved WpSconfSret.
Require Import WpLock FdSlots IrefSlots DiskPtsto WpUart SpecDevintr.
Require Import VcGen VcGenS.
Require Import KptShare.
Require Import WpSmodePtLeaves WpSmodePtCtl.
Require Import IntrDefs.
(* legalize_sie_clear_idem + have_nom_val: kept QUALIFIED (no Import) so the
   WpGprCsrwCommon/C namespaces don't shadow anything here. *)
Require WpGprCsrwCommon WpGprCsrwC.
Require Import SpecKerneltrap SpecKernelvec.
From Kernel Require KernelSyms.
Require Import KernelConsts.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

Module KernelvecProof (Kerneltrap : KERNELTRAP) : KERNELVEC.
(* ===================================================================== *)
(* Pure helpers.                                                          *)
(* ===================================================================== *)

(* regidx disequality: compare the uint of the 5-bit index. *)
Ltac kv_regne :=
  let H := fresh in
  intro H; apply (f_equal (fun r0 : regidx => uint (regidx_bits r0))) in H;
  vm_compute in H; discriminate H.

(* strip leading [<[k := v]>] inserts from a total-lookup / lookup goal,
   discharging the [k <> r] side conditions either structurally (both keys
   concrete) or from a [r <> k] disequality already in context.  Stops when
   the next insert's key IS the looked-up key. *)
Ltac kv_skipt :=
  repeat (rewrite upd_ne; [ | first [ kv_regne | congruence ] ]).
Ltac kv_skipl :=
  repeat (rewrite lookup_insert_ne; [ | first [ kv_regne | congruence ] ]).



(* the -256/+256 immediate cancellation of the two c.addi16sp. *)
Lemma kv_cancel :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* jal target / link-value arithmetic. *)
Lemma kv_jal_tgt :
  add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
          (sign_extend' 64 (mword_of_int KernelConsts.kernelvec_jal_imm : mword 21))
  = (mword_of_int (KernelSyms.kerneltrap) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_ra_val :
  add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) 4 = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_rvr :
  regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. reflexivity. Qed.

(* ---- JAL to a 2-byte-aligned target with the C extension enabled (the
   kerneltrap entry 0x800026a2 is NOT 4-aligned): copied from the archived
   WpKvJal.v -- the misalignment check (bit1 && not Zca) is false. ---- *)


(* sp after the prologue c.addi16sp (the value the whole frame is based on). *)
Definition kv_sp1 (m : regfile) : mword 64 :=
  regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm kv_imm1))).

(* the gpr file after instr #1 / after the jal (#19). *)
Definition kv_m1 (m : regfile) : regfile :=
  <[Regidx csp_rs1 := kv_sp1 m]> m.
Definition kv_m2 (m : regfile) : regfile :=
  <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64)]> (kv_m1 m).

(* The 18 registers kernelvec WRITES between entry and sret: sp + the 17
   saved/restored registers (⊇ kt_clobbered).  Key set of the final map_eq. *)
Definition kv_saved : gset regidx :=
  {[ Regidx csp_rs1;
     Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 3 : mword 5);
     Regidx (mword_of_int 5 : mword 5); Regidx (mword_of_int 6 : mword 5);
     Regidx (mword_of_int 7 : mword 5); Regidx (mword_of_int 10 : mword 5);
     Regidx (mword_of_int 11 : mword 5); Regidx (mword_of_int 12 : mword 5);
     Regidx (mword_of_int 13 : mword 5); Regidx (mword_of_int 14 : mword 5);
     Regidx (mword_of_int 15 : mword 5); Regidx (mword_of_int 16 : mword 5);
     Regidx (mword_of_int 17 : mword 5); Regidx (mword_of_int 28 : mword 5);
     Regidx (mword_of_int 29 : mword 5); Regidx (mword_of_int 30 : mword 5);
     Regidx (mword_of_int 31 : mword 5) ]}.

(* ===================================================================== *)
(* Block-VCgen support for the two 17-instruction straight-line runs      *)
(* (the register-save c.sdsp block and the register-restore c.ldsp block).*)
(* ===================================================================== *)
Definition kv_store_prog : list vop_s :=
  [ VScsdsp (mword_of_int 0) (mword_of_int 1);
    VScsdsp (mword_of_int 2) (mword_of_int 3);
    VScsdsp (mword_of_int 4) (mword_of_int 5);
    VScsdsp (mword_of_int 5) (mword_of_int 6);
    VScsdsp (mword_of_int 6) (mword_of_int 7);
    VScsdsp (mword_of_int 9) (mword_of_int 10);
    VScsdsp (mword_of_int 10) (mword_of_int 11);
    VScsdsp (mword_of_int 11) (mword_of_int 12);
    VScsdsp (mword_of_int 12) (mword_of_int 13);
    VScsdsp (mword_of_int 13) (mword_of_int 14);
    VScsdsp (mword_of_int 14) (mword_of_int 15);
    VScsdsp (mword_of_int 15) (mword_of_int 16);
    VScsdsp (mword_of_int 16) (mword_of_int 17);
    VScsdsp (mword_of_int 27) (mword_of_int 28);
    VScsdsp (mword_of_int 28) (mword_of_int 29);
    VScsdsp (mword_of_int 29) (mword_of_int 30);
    VScsdsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_load_prog : list vop_s :=
  [ VScldsp (mword_of_int 0) (mword_of_int 1);
    VScldsp (mword_of_int 2) (mword_of_int 3);
    VScldsp (mword_of_int 4) (mword_of_int 5);
    VScldsp (mword_of_int 5) (mword_of_int 6);
    VScldsp (mword_of_int 6) (mword_of_int 7);
    VScldsp (mword_of_int 9) (mword_of_int 10);
    VScldsp (mword_of_int 10) (mword_of_int 11);
    VScldsp (mword_of_int 11) (mword_of_int 12);
    VScldsp (mword_of_int 12) (mword_of_int 13);
    VScldsp (mword_of_int 13) (mword_of_int 14);
    VScldsp (mword_of_int 14) (mword_of_int 15);
    VScldsp (mword_of_int 15) (mword_of_int 16);
    VScldsp (mword_of_int 16) (mword_of_int 17);
    VScldsp (mword_of_int 27) (mword_of_int 28);
    VScldsp (mword_of_int 28) (mword_of_int 29);
    VScldsp (mword_of_int 29) (mword_of_int 30);
    VScldsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_store_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 1 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 3 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 5 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 6 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 7 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 10 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 11 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 12 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 13 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 14 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 15 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 16 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 17 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 28 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 29 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 30 0]>
  (<[Regidx (mword_of_int 31 : mword 5) := SX 31 0]> ∅))))))))))))))))).
Definition kv_store_heap0 : list (sval * sval) :=
  [ (SX 2 0, SX 33 0);
    (SX 2 16, SX 34 0);
    (SX 2 32, SX 35 0);
    (SX 2 40, SX 36 0);
    (SX 2 48, SX 37 0);
    (SX 2 72, SX 38 0);
    (SX 2 80, SX 39 0);
    (SX 2 88, SX 40 0);
    (SX 2 96, SX 41 0);
    (SX 2 104, SX 42 0);
    (SX 2 112, SX 43 0);
    (SX 2 120, SX 44 0);
    (SX 2 128, SX 45 0);
    (SX 2 216, SX 46 0);
    (SX 2 224, SX 47 0);
    (SX 2 232, SX 48 0);
    (SX 2 240, SX 49 0) ].
Definition kv_store_heap1 : list (sval * sval) :=
  [ (SX 2 0, SX 1 0);
    (SX 2 16, SX 3 0);
    (SX 2 32, SX 5 0);
    (SX 2 40, SX 6 0);
    (SX 2 48, SX 7 0);
    (SX 2 72, SX 10 0);
    (SX 2 80, SX 11 0);
    (SX 2 88, SX 12 0);
    (SX 2 96, SX 13 0);
    (SX 2 104, SX 14 0);
    (SX 2 112, SX 15 0);
    (SX 2 120, SX 16 0);
    (SX 2 128, SX 17 0);
    (SX 2 216, SX 28 0);
    (SX 2 224, SX 29 0);
    (SX 2 232, SX 30 0);
    (SX 2 240, SX 31 0) ].
Definition kv_load_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]> ∅.
Definition kv_load_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 31 : mword 5) := SX 49 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 48 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 47 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 46 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 45 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 44 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 43 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 42 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 41 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 40 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 39 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 38 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 37 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 36 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 35 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 34 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> kv_load_regs0)))))))))))))))).

(* concrete register file after the load block: 17 restores over [m], in the
   SAME nesting order as the epilogue target (innermost = x1, outermost = x31;
   csp/x2 is NOT written by the block).  [regval_into_reg] being the identity,
   the block's [wK] line up with the epilogue's [vK]. *)
Definition kv_load_result (m : regfile) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : mword 64) : regfile :=
  <[Regidx (mword_of_int 31 : mword 5) := w17]> (<[Regidx (mword_of_int 30 : mword 5) := w16]> (<[Regidx (mword_of_int 29 : mword 5) := w15]> (<[Regidx (mword_of_int 28 : mword 5) := w14]> (<[Regidx (mword_of_int 17 : mword 5) := w13]> (<[Regidx (mword_of_int 16 : mword 5) := w12]> (<[Regidx (mword_of_int 15 : mword 5) := w11]> (<[Regidx (mword_of_int 14 : mword 5) := w10]> (<[Regidx (mword_of_int 13 : mword 5) := w9]> (<[Regidx (mword_of_int 12 : mword 5) := w8]> (<[Regidx (mword_of_int 11 : mword 5) := w7]> (<[Regidx (mword_of_int 10 : mword 5) := w6]> (<[Regidx (mword_of_int 7 : mword 5) := w5]> (<[Regidx (mword_of_int 6 : mword 5) := w4]> (<[Regidx (mword_of_int 5 : mword 5) := w3]> (<[Regidx (mword_of_int 3 : mword 5) := w2]> (<[Regidx (mword_of_int 1 : mword 5) := w1]> m)))))))))))))))).

Lemma kv_store_run :
  vc_block_s (VSt (KernelSyms.kernelvec + 0x2) kv_store_regs0 kv_store_heap0 []) kv_store_prog
  = Some (VSt (KernelSyms.kernelvec + 0x24) kv_store_regs0 kv_store_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Lemma kv_load_run :
  vc_block_s (VSt (KernelSyms.kernelvec + 0x28) kv_load_regs0 kv_store_heap0 []) kv_load_prog
  = Some (VSt (KernelSyms.kernelvec + 0x4a) kv_load_regs1 kv_store_heap0 []).
Proof. vm_compute. reflexivity. Qed.

Section KernelvecCore.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* Congruence for [gpr_file]: two register files that agree on every
     register total-lookup hold the SAME resource (regfile is a total
     function, so pointwise agreement is functional extensionality).  The
     block lemmas use this to convert the abstract result map returned by
     [wp_vc_block_s] back to the surrounding proof's concrete register file. *)
  Lemma gpr_file_ext (m1 m2 : regfile) :
    (∀ r : regidx, m1 !!! r = m2 !!! r) ->
    gpr_file m1 -∗ gpr_file m2.
  Proof.
    iIntros (Hpt) "Hfile".
    assert (Heq : m1 = m2) by (apply functional_extensionality; intro r; exact (Hpt r)).
    rewrite -Heq. iExact "Hfile".
  Qed.

  Lemma kv_store_instrs :
    kernel_text -∗ block_instrs_s (KernelSyms.kernelvec + 0x2) kv_store_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_store_prog vop_s_ast].
    iSplitR; [by iApply kv_i2|].
    replace (KernelSyms.kernelvec + 0x2 + 2) with (KernelSyms.kernelvec + 0x4) by lia.
    iSplitR; [by iApply kv_i3|].
    replace (KernelSyms.kernelvec + 0x4 + 2) with (KernelSyms.kernelvec + 0x6) by lia.
    iSplitR; [by iApply kv_i4|].
    replace (KernelSyms.kernelvec + 0x6 + 2) with (KernelSyms.kernelvec + 0x8) by lia.
    iSplitR; [by iApply kv_i5|].
    replace (KernelSyms.kernelvec + 0x8 + 2) with (KernelSyms.kernelvec + 0xa) by lia.
    iSplitR; [by iApply kv_i6|].
    replace (KernelSyms.kernelvec + 0xa + 2) with (KernelSyms.kernelvec + 0xc) by lia.
    iSplitR; [by iApply kv_i7|].
    replace (KernelSyms.kernelvec + 0xc + 2) with (KernelSyms.kernelvec + 0xe) by lia.
    iSplitR; [by iApply kv_i8|].
    replace (KernelSyms.kernelvec + 0xe + 2) with (KernelSyms.kernelvec + 0x10) by lia.
    iSplitR; [by iApply kv_i9|].
    replace (KernelSyms.kernelvec + 0x10 + 2) with (KernelSyms.kernelvec + 0x12) by lia.
    iSplitR; [by iApply kv_i10|].
    replace (KernelSyms.kernelvec + 0x12 + 2) with (KernelSyms.kernelvec + 0x14) by lia.
    iSplitR; [by iApply kv_i11|].
    replace (KernelSyms.kernelvec + 0x14 + 2) with (KernelSyms.kernelvec + 0x16) by lia.
    iSplitR; [by iApply kv_i12|].
    replace (KernelSyms.kernelvec + 0x16 + 2) with (KernelSyms.kernelvec + 0x18) by lia.
    iSplitR; [by iApply kv_i13|].
    replace (KernelSyms.kernelvec + 0x18 + 2) with (KernelSyms.kernelvec + 0x1a) by lia.
    iSplitR; [by iApply kv_i14|].
    replace (KernelSyms.kernelvec + 0x1a + 2) with (KernelSyms.kernelvec + 0x1c) by lia.
    iSplitR; [by iApply kv_i15|].
    replace (KernelSyms.kernelvec + 0x1c + 2) with (KernelSyms.kernelvec + 0x1e) by lia.
    iSplitR; [by iApply kv_i16|].
    replace (KernelSyms.kernelvec + 0x1e + 2) with (KernelSyms.kernelvec + 0x20) by lia.
    iSplitR; [by iApply kv_i17|].
    replace (KernelSyms.kernelvec + 0x20 + 2) with (KernelSyms.kernelvec + 0x22) by lia.
    iSplitR; [by iApply kv_i18|].
    done.
  Qed.

  Lemma kv_load_instrs :
    kernel_text -∗ block_instrs_s (KernelSyms.kernelvec + 0x28) kv_load_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_load_prog vop_s_ast].
    iSplitR; [by iApply kv_i20|].
    replace (KernelSyms.kernelvec + 0x28 + 2) with (KernelSyms.kernelvec + 0x2a) by lia.
    iSplitR; [by iApply kv_i21|].
    replace (KernelSyms.kernelvec + 0x2a + 2) with (KernelSyms.kernelvec + 0x2c) by lia.
    iSplitR; [by iApply kv_i22|].
    replace (KernelSyms.kernelvec + 0x2c + 2) with (KernelSyms.kernelvec + 0x2e) by lia.
    iSplitR; [by iApply kv_i23|].
    replace (KernelSyms.kernelvec + 0x2e + 2) with (KernelSyms.kernelvec + 0x30) by lia.
    iSplitR; [by iApply kv_i24|].
    replace (KernelSyms.kernelvec + 0x30 + 2) with (KernelSyms.kernelvec + 0x32) by lia.
    iSplitR; [by iApply kv_i25|].
    replace (KernelSyms.kernelvec + 0x32 + 2) with (KernelSyms.kernelvec + 0x34) by lia.
    iSplitR; [by iApply kv_i26|].
    replace (KernelSyms.kernelvec + 0x34 + 2) with (KernelSyms.kernelvec + 0x36) by lia.
    iSplitR; [by iApply kv_i27|].
    replace (KernelSyms.kernelvec + 0x36 + 2) with (KernelSyms.kernelvec + 0x38) by lia.
    iSplitR; [by iApply kv_i28|].
    replace (KernelSyms.kernelvec + 0x38 + 2) with (KernelSyms.kernelvec + 0x3a) by lia.
    iSplitR; [by iApply kv_i29|].
    replace (KernelSyms.kernelvec + 0x3a + 2) with (KernelSyms.kernelvec + 0x3c) by lia.
    iSplitR; [by iApply kv_i30|].
    replace (KernelSyms.kernelvec + 0x3c + 2) with (KernelSyms.kernelvec + 0x3e) by lia.
    iSplitR; [by iApply kv_i31|].
    replace (KernelSyms.kernelvec + 0x3e + 2) with (KernelSyms.kernelvec + 0x40) by lia.
    iSplitR; [by iApply kv_i32|].
    replace (KernelSyms.kernelvec + 0x40 + 2) with (KernelSyms.kernelvec + 0x42) by lia.
    iSplitR; [by iApply kv_i33|].
    replace (KernelSyms.kernelvec + 0x42 + 2) with (KernelSyms.kernelvec + 0x44) by lia.
    iSplitR; [by iApply kv_i34|].
    replace (KernelSyms.kernelvec + 0x44 + 2) with (KernelSyms.kernelvec + 0x46) by lia.
    iSplitR; [by iApply kv_i35|].
    replace (KernelSyms.kernelvec + 0x46 + 2) with (KernelSyms.kernelvec + 0x48) by lia.
    iSplitR; [by iApply kv_i36|].
    done.
  Qed.

  (* kv_cfg_split / kv_cfg_recombine (the smode_config fraction choreography)
     are shared with push_off/pop_off — now in SmodeCore beside
     smode_config_split/rebuild. *)

  (* hw_config is persistent and bundled inside [smode_config]: peel a copy
     without disturbing the bundle. *)


  (* the 17-instruction register-save run, as ONE block; STRENGTHENED to
     return the CONCRETE input register file [m] (stores don't touch it). *)
  Lemma wp_kv_store_block_vc (root_ppn : mword 44) (γ : gname)
      (m : regfile)
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 : bv 64)
      {dq : dfrac} :
    smode_config γ dq -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec + 0x2)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ vold1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ vold2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ vold3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ vold4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ vold5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ vold6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ vold7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ vold8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ vold9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ vold10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ vold11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ vold12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ vold13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ vold14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ vold15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ vold16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ vold17 -∗
    ( smode_config γ dq -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kernelvec + 0x24)) -∗
      gpr_file m -∗
      (m !!! Regidx csp_rs1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros.
    iIntros "Hsm Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    iDestruct "Hfile" as "(%Hdomm & Hfilemap)".
    iAssert (gpr_file m) with "[Hfilemap]" as "Hfile".
    { rewrite /gpr_file. iSplit; [iPureIntro; exact Hdomm | iExact "Hfilemap"]. }
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 1%nat => m !!! Regidx (mword_of_int 1 : mword 5)
           | 3%nat => m !!! Regidx (mword_of_int 3 : mword 5)
           | 5%nat => m !!! Regidx (mword_of_int 5 : mword 5)
           | 6%nat => m !!! Regidx (mword_of_int 6 : mword 5)
           | 7%nat => m !!! Regidx (mword_of_int 7 : mword 5)
           | 10%nat => m !!! Regidx (mword_of_int 10 : mword 5)
           | 11%nat => m !!! Regidx (mword_of_int 11 : mword 5)
           | 12%nat => m !!! Regidx (mword_of_int 12 : mword 5)
           | 13%nat => m !!! Regidx (mword_of_int 13 : mword 5)
           | 14%nat => m !!! Regidx (mword_of_int 14 : mword 5)
           | 15%nat => m !!! Regidx (mword_of_int 15 : mword 5)
           | 16%nat => m !!! Regidx (mword_of_int 16 : mword 5)
           | 17%nat => m !!! Regidx (mword_of_int 17 : mword 5)
           | 28%nat => m !!! Regidx (mword_of_int 28 : mword 5)
           | 29%nat => m !!! Regidx (mword_of_int 29 : mword 5)
           | 30%nat => m !!! Regidx (mword_of_int 30 : mword 5)
           | 31%nat => m !!! Regidx (mword_of_int 31 : mword 5)
           | 33%nat => (vold1 : mword 64)
           | 34%nat => (vold2 : mword 64)
           | 35%nat => (vold3 : mword 64)
           | 36%nat => (vold4 : mword 64)
           | 37%nat => (vold5 : mword 64)
           | 38%nat => (vold6 : mword 64)
           | 39%nat => (vold7 : mword 64)
           | 40%nat => (vold8 : mword 64)
           | 41%nat => (vold9 : mword 64)
           | 42%nat => (vold10 : mword 64)
           | 43%nat => (vold11 : mword 64)
           | 44%nat => (vold12 : mword 64)
           | 45%nat => (vold13 : mword 64)
           | 46%nat => (vold14 : mword 64)
           | 47%nat => (vold15 : mword 64)
           | 48%nat => (vold16 : mword 64)
           | 49%nat => (vold17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmS : gpr_matches ρ kv_store_regs0 m).
    { unfold kv_store_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVo1 : ρ 33%nat = (vold1 : mword 64)) by reflexivity.
    assert (HVo2 : ρ 34%nat = (vold2 : mword 64)) by reflexivity.
    assert (HVo3 : ρ 35%nat = (vold3 : mword 64)) by reflexivity.
    assert (HVo4 : ρ 36%nat = (vold4 : mword 64)) by reflexivity.
    assert (HVo5 : ρ 37%nat = (vold5 : mword 64)) by reflexivity.
    assert (HVo6 : ρ 38%nat = (vold6 : mword 64)) by reflexivity.
    assert (HVo7 : ρ 39%nat = (vold7 : mword 64)) by reflexivity.
    assert (HVo8 : ρ 40%nat = (vold8 : mword 64)) by reflexivity.
    assert (HVo9 : ρ 41%nat = (vold9 : mword 64)) by reflexivity.
    assert (HVo10 : ρ 42%nat = (vold10 : mword 64)) by reflexivity.
    assert (HVo11 : ρ 43%nat = (vold11 : mword 64)) by reflexivity.
    assert (HVo12 : ρ 44%nat = (vold12 : mword 64)) by reflexivity.
    assert (HVo13 : ρ 45%nat = (vold13 : mword 64)) by reflexivity.
    assert (HVo14 : ρ 46%nat = (vold14 : mword 64)) by reflexivity.
    assert (HVo15 : ρ 47%nat = (vold15 : mword 64)) by reflexivity.
    assert (HVo16 : ρ 48%nat = (vold16 : mword 64)) by reflexivity.
    assert (HVo17 : ρ 49%nat = (vold17 : mword 64)) by reflexivity.
    assert (HVr1 : ρ 1%nat = m !!! Regidx (mword_of_int 1 : mword 5)) by reflexivity.
    assert (HVr3 : ρ 3%nat = m !!! Regidx (mword_of_int 3 : mword 5)) by reflexivity.
    assert (HVr5 : ρ 5%nat = m !!! Regidx (mword_of_int 5 : mword 5)) by reflexivity.
    assert (HVr6 : ρ 6%nat = m !!! Regidx (mword_of_int 6 : mword 5)) by reflexivity.
    assert (HVr7 : ρ 7%nat = m !!! Regidx (mword_of_int 7 : mword 5)) by reflexivity.
    assert (HVr10 : ρ 10%nat = m !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
    assert (HVr11 : ρ 11%nat = m !!! Regidx (mword_of_int 11 : mword 5)) by reflexivity.
    assert (HVr12 : ρ 12%nat = m !!! Regidx (mword_of_int 12 : mword 5)) by reflexivity.
    assert (HVr13 : ρ 13%nat = m !!! Regidx (mword_of_int 13 : mword 5)) by reflexivity.
    assert (HVr14 : ρ 14%nat = m !!! Regidx (mword_of_int 14 : mword 5)) by reflexivity.
    assert (HVr15 : ρ 15%nat = m !!! Regidx (mword_of_int 15 : mword 5)) by reflexivity.
    assert (HVr16 : ρ 16%nat = m !!! Regidx (mword_of_int 16 : mword 5)) by reflexivity.
    assert (HVr17 : ρ 17%nat = m !!! Regidx (mword_of_int 17 : mword 5)) by reflexivity.
    assert (HVr28 : ρ 28%nat = m !!! Regidx (mword_of_int 28 : mword 5)) by reflexivity.
    assert (HVr29 : ρ 29%nat = m !!! Regidx (mword_of_int 29 : mword 5)) by reflexivity.
    assert (HVr30 : ρ 30%nat = m !!! Regidx (mword_of_int 30 : mword 5)) by reflexivity.
    assert (HVr31 : ρ 31%nat = m !!! Regidx (mword_of_int 31 : mword 5)) by reflexivity.
    iDestruct (kv_store_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_store_prog
              (VSt (KernelSyms.kernelvec + 0x2) kv_store_regs0 kv_store_heap0 [])
              (VSt (KernelSyms.kernelvec + 0x24) kv_store_regs0 kv_store_heap1 [])
              ρ m γ
              (dq:=dq)
 kv_store_run HmS
              with "Hsm Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVo1 HVo2 HVo3 HVo4 HVo5 HVo6 HVo7 HVo8 HVo9 HVo10 HVo11 HVo12 HVo13 HVo14 HVo15 HVo16 HVo17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hsm Htlbinv Hpc Hfile Hheap _".
    destruct Hmf as [Hmf Hpres].
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap1;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVr1 HVr3 HVr5 HVr6 HVr7 HVr10 HVr11 HVr12 HVr13 HVr14 HVr15 HVr16 HVr17 HVr28 HVr29 HVr30 HVr31) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (Hall : ∀ r : regidx, mf !!! r = m !!! r).
    { intro r. destruct (kv_store_regs0 !! r) as [sv|] eqn:Er.
      - rewrite (Hmf r sv Er). rewrite (HmS r sv Er). reflexivity.
      - exact (Hpres r Er). }
    iDestruct (gpr_file_ext mf m Hall with "Hfile") as "Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

  (* the 17-instruction register-restore run, as ONE block; STRENGTHENED to
     return the CONCRETE result file [kv_load_result m w1..w17]. *)
  Lemma wp_kv_load_block_vc (root_ppn : mword 44) (γ : gname)
      (m : regfile)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : bv 64)
      {dq : dfrac} :
    smode_config γ dq -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec + 0x28)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ w1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
    ( smode_config γ dq -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kernelvec + 0x4a)) -∗
      gpr_file (kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) -∗
      (m !!! Regidx csp_rs1) ↦₈ w1 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros.
    iIntros "Hsm Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    iDestruct "Hfile" as "(%Hdomm & Hfilemap)".
    iAssert (gpr_file m) with "[Hfilemap]" as "Hfile".
    { rewrite /gpr_file. iSplit; [iPureIntro; exact Hdomm | iExact "Hfilemap"]. }
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 33%nat => (w1 : mword 64)
           | 34%nat => (w2 : mword 64)
           | 35%nat => (w3 : mword 64)
           | 36%nat => (w4 : mword 64)
           | 37%nat => (w5 : mword 64)
           | 38%nat => (w6 : mword 64)
           | 39%nat => (w7 : mword 64)
           | 40%nat => (w8 : mword 64)
           | 41%nat => (w9 : mword 64)
           | 42%nat => (w10 : mword 64)
           | 43%nat => (w11 : mword 64)
           | 44%nat => (w12 : mword 64)
           | 45%nat => (w13 : mword 64)
           | 46%nat => (w14 : mword 64)
           | 47%nat => (w15 : mword 64)
           | 48%nat => (w16 : mword 64)
           | 49%nat => (w17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmL : gpr_matches ρ kv_load_regs0 m).
    { unfold kv_load_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVw1 : ρ 33%nat = (w1 : mword 64)) by reflexivity.
    assert (HVw2 : ρ 34%nat = (w2 : mword 64)) by reflexivity.
    assert (HVw3 : ρ 35%nat = (w3 : mword 64)) by reflexivity.
    assert (HVw4 : ρ 36%nat = (w4 : mword 64)) by reflexivity.
    assert (HVw5 : ρ 37%nat = (w5 : mword 64)) by reflexivity.
    assert (HVw6 : ρ 38%nat = (w6 : mword 64)) by reflexivity.
    assert (HVw7 : ρ 39%nat = (w7 : mword 64)) by reflexivity.
    assert (HVw8 : ρ 40%nat = (w8 : mword 64)) by reflexivity.
    assert (HVw9 : ρ 41%nat = (w9 : mword 64)) by reflexivity.
    assert (HVw10 : ρ 42%nat = (w10 : mword 64)) by reflexivity.
    assert (HVw11 : ρ 43%nat = (w11 : mword 64)) by reflexivity.
    assert (HVw12 : ρ 44%nat = (w12 : mword 64)) by reflexivity.
    assert (HVw13 : ρ 45%nat = (w13 : mword 64)) by reflexivity.
    assert (HVw14 : ρ 46%nat = (w14 : mword 64)) by reflexivity.
    assert (HVw15 : ρ 47%nat = (w15 : mword 64)) by reflexivity.
    assert (HVw16 : ρ 48%nat = (w16 : mword 64)) by reflexivity.
    assert (HVw17 : ρ 49%nat = (w17 : mword 64)) by reflexivity.
    iDestruct (kv_load_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_load_prog
              (VSt (KernelSyms.kernelvec + 0x28) kv_load_regs0 kv_store_heap0 [])
              (VSt (KernelSyms.kernelvec + 0x4a) kv_load_regs1 kv_store_heap0 [])
              ρ m γ
              (dq:=dq)
 kv_load_run HmL
              with "Hsm Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hsm Htlbinv Hpc Hfile Hheap _".
    destruct Hmf as [Hmf Hpres].
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap0;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (F2 : mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { assert (Hl : kv_load_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F1 : mf !!! Regidx (mword_of_int 1 : mword 5) = (w1 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 33 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F3 : mf !!! Regidx (mword_of_int 3 : mword 5) = (w2 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 3 : mword 5) = Some (SX 34 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F5 : mf !!! Regidx (mword_of_int 5 : mword 5) = (w3 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 5 : mword 5) = Some (SX 35 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F6 : mf !!! Regidx (mword_of_int 6 : mword 5) = (w4 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 6 : mword 5) = Some (SX 36 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F7 : mf !!! Regidx (mword_of_int 7 : mword 5) = (w5 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 7 : mword 5) = Some (SX 37 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F10 : mf !!! Regidx (mword_of_int 10 : mword 5) = (w6 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 38 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F11 : mf !!! Regidx (mword_of_int 11 : mword 5) = (w7 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 11 : mword 5) = Some (SX 39 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F12 : mf !!! Regidx (mword_of_int 12 : mword 5) = (w8 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 12 : mword 5) = Some (SX 40 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F13 : mf !!! Regidx (mword_of_int 13 : mword 5) = (w9 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 13 : mword 5) = Some (SX 41 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F14 : mf !!! Regidx (mword_of_int 14 : mword 5) = (w10 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 14 : mword 5) = Some (SX 42 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F15 : mf !!! Regidx (mword_of_int 15 : mword 5) = (w11 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 15 : mword 5) = Some (SX 43 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F16 : mf !!! Regidx (mword_of_int 16 : mword 5) = (w12 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 16 : mword 5) = Some (SX 44 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F17 : mf !!! Regidx (mword_of_int 17 : mword 5) = (w13 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 17 : mword 5) = Some (SX 45 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F28 : mf !!! Regidx (mword_of_int 28 : mword 5) = (w14 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 28 : mword 5) = Some (SX 46 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F29 : mf !!! Regidx (mword_of_int 29 : mword 5) = (w15 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 29 : mword 5) = Some (SX 47 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F30 : mf !!! Regidx (mword_of_int 30 : mword 5) = (w16 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 30 : mword 5) = Some (SX 48 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F31 : mf !!! Regidx (mword_of_int 31 : mword 5) = (w17 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 31 : mword 5) = Some (SX 49 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (Hall : ∀ r : regidx, mf !!! r = kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 !!! r).
    { intro r. unfold kv_load_result.
      destruct (decide (r = Regidx (mword_of_int 31 : mword 5))) as [->|];
        [ rewrite F31; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 30 : mword 5))) as [->|];
        [ rewrite F30; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 29 : mword 5))) as [->|];
        [ rewrite F29; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 28 : mword 5))) as [->|];
        [ rewrite F28; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 17 : mword 5))) as [->|];
        [ rewrite F17; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 16 : mword 5))) as [->|];
        [ rewrite F16; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 15 : mword 5))) as [->|];
        [ rewrite F15; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 14 : mword 5))) as [->|];
        [ rewrite F14; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 13 : mword 5))) as [->|];
        [ rewrite F13; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 12 : mword 5))) as [->|];
        [ rewrite F12; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 11 : mword 5))) as [->|];
        [ rewrite F11; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 10 : mword 5))) as [->|];
        [ rewrite F10; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 7 : mword 5))) as [->|];
        [ rewrite F7; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 6 : mword 5))) as [->|];
        [ rewrite F6; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 5 : mword 5))) as [->|];
        [ rewrite F5; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 3 : mword 5))) as [->|];
        [ rewrite F3; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 1 : mword 5))) as [->|];
        [ rewrite F1; kv_skipt; rewrite upd_eq; reflexivity |].
      destruct (decide (r = Regidx csp_rs1)) as [->|];
        [ rewrite F2; kv_skipt; reflexivity |].
      (* default: r is none of the 18 keys *)
      assert (Hnone : kv_load_regs1 !! r = None).
      { rewrite /kv_load_regs1 /kv_load_regs0.
        kv_skipl. apply lookup_empty. }
      rewrite (Hpres r Hnone).
      kv_skipt. reflexivity. }
    iDestruct (gpr_file_ext mf (kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) Hall with "Hfile") as "Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

  (* =================================================================== *)
  (* wp_kv_prologue: instrs #1..#19 -- c.addi16sp sp,-256 (fetch WALK,    *)
  (* fills TLB slot 5), 17 c.sdsp saves (the first data-WALKS and fills   *)
  (* slot tlb_hash svpn; the rest hit), jal kerneltrap.                   *)
  (* =================================================================== *)
  Lemma wp_kv_prologue (root_ppn : mword 44) (γ : gname)
      (m : regfile)
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64) :
    smode_config γ (DfracOwn (1/2)) -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec) : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ((((kv_sp1 m)))) ↦₈ vold1 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ vold2 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ vold3 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ vold4 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ vold5 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ vold6 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ vold7 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ vold8 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ vold9 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ vold10 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ vold11 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ vold12 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ vold13 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ vold14 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ vold15 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ vold16 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ vold17 -∗
    ( smode_config γ (DfracOwn (1/2)) -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
      gpr_file (kv_m2 m) -∗
      ((((kv_sp1 m)))) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros.
    iIntros "Hsm Htlbinv Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* ---- #1: c.addi16sp sp,-256 @ 0x800053e0 (fetch page-walk, fills slot 5) ---- *)
    iPoseProof (kv_instr1 with "Htext") as "Hi1".
    assert (Hpc1 : add_vec_int (mword_of_int (KernelSyms.kernelvec) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s_pt root_ppn γ (mword_of_int (KernelSyms.kernelvec)) kv_imm1 m
              (1/2)%Qp

              with "Hsm Htlbinv Hpc Hfile Hi1").
    iEval (rewrite Hpc1).
    iIntros "Hsm Htlbinv Hpc Hfile".
    (* the sp-lookup / clobbered-lookup facts over kv_m1 *)
    assert (Hm1sp : kv_m1 m !!! Regidx csp_rs1 = kv_sp1 m)
      by (unfold kv_m1; rewrite upd_eq; reflexivity).
    assert (Hmr1 : kv_m1 m !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr2 : kv_m1 m !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr3 : kv_m1 m !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr4 : kv_m1 m !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr5 : kv_m1 m !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr6 : kv_m1 m !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr7 : kv_m1 m !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr8 : kv_m1 m !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr9 : kv_m1 m !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr10 : kv_m1 m !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr11 : kv_m1 m !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr12 : kv_m1 m !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr13 : kv_m1 m !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr14 : kv_m1 m !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr15 : kv_m1 m !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr16 : kv_m1 m !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hmr17 : kv_m1 m !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5))
      by (unfold kv_m1; rewrite upd_ne; [reflexivity | kv_regne]).
    (* ---- #2..#18: the 17 c.sdsp register saves, as ONE VCgen block ---- *)
    (* bridge each stack cell from the prologue's zero_extend'/concat address
       shape to the block's [add_vec (kv_m1 m !!! csp) (mword_of_int N)] shape. *)
    assert (Heqw2 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 16))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw3 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 32))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw4 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 40))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw5 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 48))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw6 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 72))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw7 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 80))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw8 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 88))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw9 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 96))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw10 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 104))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw11 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 112))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw12 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 120))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw13 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 128))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw14 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 216))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw15 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 224))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw16 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 232))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw17 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 240))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw1".
    iEval (rewrite Heqw2) in "Hw2".
    iEval (rewrite Heqw3) in "Hw3".
    iEval (rewrite Heqw4) in "Hw4".
    iEval (rewrite Heqw5) in "Hw5".
    iEval (rewrite Heqw6) in "Hw6".
    iEval (rewrite Heqw7) in "Hw7".
    iEval (rewrite Heqw8) in "Hw8".
    iEval (rewrite Heqw9) in "Hw9".
    iEval (rewrite Heqw10) in "Hw10".
    iEval (rewrite Heqw11) in "Hw11".
    iEval (rewrite Heqw12) in "Hw12".
    iEval (rewrite Heqw13) in "Hw13".
    iEval (rewrite Heqw14) in "Hw14".
    iEval (rewrite Heqw15) in "Hw15".
    iEval (rewrite Heqw16) in "Hw16".
    iEval (rewrite Heqw17) in "Hw17".
    iApply (wp_kv_store_block_vc root_ppn γ (kv_m1 m)
              vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17
              (dq := DfracOwn (1/2))

              with "Hsm Htlbinv Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* convert the block's result cells back to the prologue's address/value shape *)
    iEval (rewrite Hm1sp Hmr1) in "Hw1".
    iEval (rewrite <- Heqw2; rewrite Hmr2) in "Hw2".
    iEval (rewrite <- Heqw3; rewrite Hmr3) in "Hw3".
    iEval (rewrite <- Heqw4; rewrite Hmr4) in "Hw4".
    iEval (rewrite <- Heqw5; rewrite Hmr5) in "Hw5".
    iEval (rewrite <- Heqw6; rewrite Hmr6) in "Hw6".
    iEval (rewrite <- Heqw7; rewrite Hmr7) in "Hw7".
    iEval (rewrite <- Heqw8; rewrite Hmr8) in "Hw8".
    iEval (rewrite <- Heqw9; rewrite Hmr9) in "Hw9".
    iEval (rewrite <- Heqw10; rewrite Hmr10) in "Hw10".
    iEval (rewrite <- Heqw11; rewrite Hmr11) in "Hw11".
    iEval (rewrite <- Heqw12; rewrite Hmr12) in "Hw12".
    iEval (rewrite <- Heqw13; rewrite Hmr13) in "Hw13".
    iEval (rewrite <- Heqw14; rewrite Hmr14) in "Hw14".
    iEval (rewrite <- Heqw15; rewrite Hmr15) in "Hw15".
    iEval (rewrite <- Heqw16; rewrite Hmr16) in "Hw16".
    iEval (rewrite <- Heqw17; rewrite Hmr17) in "Hw17".
    (* ---- #19: jal ra, kerneltrap @ 0x80005404 ---- *)
    iPoseProof (kv_i19 with "Htext") as "Hi19".
    assert (Hrd19 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; discriminate).
    assert (Hal19 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int KernelConsts.kernelvec_jal_imm : mword 21))) 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    iApply (wp_jal_gpr_s_zca_pt root_ppn γ (mword_of_int (KernelSyms.kernelvec + 0x24)) (mword_of_int 1) (mword_of_int KernelConsts.kernelvec_jal_imm)
              (kv_m1 m) (1/2)%Qp
 Hrd19 Hal19
              with "Hsm Htlbinv Hpc Hfile Hi19").
    iEval (rewrite kv_jal_tgt kv_ra_val).
    iIntros "Hsm Htlbinv Hpc Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.


  (* =================================================================== *)
  (* wp_kv_restore: instrs #20..#37 -- 17 c.ldsp restores (all hits) and  *)
  (* c.addi16sp sp,+256.  IT STOPS BEFORE THE SRET, which the capstone     *)
  (* runs itself through [WpSconfSret.wp_sret_s_sconf]: the sret is the     *)
  (* instruction that flips the SIE ghost and re-forms the enabled arm, so  *)
  (* it needs the FOLDED BUNDLE and the whole [intr_res] / [cpu_claim] /    *)
  (* [sret_bits] package -- none of which this block's raw-cell tier can    *)
  (* even mention.  What it hands back instead is exactly what rebuilding   *)
  (* [sconf] takes, the SIE ghost half included (the old epilogue dropped   *)
  (* that half, because its sret was the raw-cell [wp_sret_gpr_pt] and the  *)
  (* per-trap [γk] it belonged to was a throwaway).                        *)
  (* =================================================================== *)
  Lemma wp_kv_restore (root_ppn : mword 44) (γ : gname)
      (mt : regfile) (spv : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)

      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    mt !!! Regidx csp_rs1 = spv ->
    hw_config -∗ minstret_inv -∗
    smode_config γ (DfracOwn (1/2)) -∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor -∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 -∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v -∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 -∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) -∗
    gpr_file mt -∗
    kernel_text -∗
    (((spv))) ↦₈ v1 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ mstatus0 -∗
      ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_res_pt root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg (add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg v17]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg v16]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg v15]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg v14]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg v13]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg v12]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v11]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg v10]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg v9]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg v8]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg v7]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v6]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg v5]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg v4]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg v3]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg v2]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg v1]> (mt))))))))))))))))))) -∗
      (((spv))) ↦₈ v1 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsp0.
    iIntros "#Hhw #Hinv Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile
             #Htext Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hcont".
    (* ---- #20..#36: the 17 c.ldsp register restores, as ONE VCgen block ---- *)
    (* bridge each stack cell from the epilogue's zero_extend'/concat address
       shape to the block's [add_vec (mt !!! csp) (mword_of_int N)] shape. *)
    assert (Heqv2 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 16))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv3 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 32))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv4 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 40))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv5 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 48))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv6 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 72))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv7 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 80))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv8 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 88))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv9 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 96))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv10 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 104))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv11 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 112))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv12 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 120))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv13 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 128))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv14 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 216))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv15 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 224))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv16 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 232))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv17 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 240))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite <- Hsp0) in "Hv1".
    iEval (rewrite Heqv2) in "Hv2".
    iEval (rewrite Heqv3) in "Hv3".
    iEval (rewrite Heqv4) in "Hv4".
    iEval (rewrite Heqv5) in "Hv5".
    iEval (rewrite Heqv6) in "Hv6".
    iEval (rewrite Heqv7) in "Hv7".
    iEval (rewrite Heqv8) in "Hv8".
    iEval (rewrite Heqv9) in "Hv9".
    iEval (rewrite Heqv10) in "Hv10".
    iEval (rewrite Heqv11) in "Hv11".
    iEval (rewrite Heqv12) in "Hv12".
    iEval (rewrite Heqv13) in "Hv13".
    iEval (rewrite Heqv14) in "Hv14".
    iEval (rewrite Heqv15) in "Hv15".
    iEval (rewrite Heqv16) in "Hv16".
    iEval (rewrite Heqv17) in "Hv17".
    iApply (wp_kv_load_block_vc root_ppn γ mt
              v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
              (dq := DfracOwn (1/2))

              with "Hsm Htlbinv Hpc Hfile Htext Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17").
    iIntros "Hsm Htlbinv Hpc Hfile Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17".
    (* convert the block's result cells back to the epilogue's address shape *)
    iEval (rewrite Hsp0) in "Hv1".
    iEval (rewrite <- Heqv2) in "Hv2".
    iEval (rewrite <- Heqv3) in "Hv3".
    iEval (rewrite <- Heqv4) in "Hv4".
    iEval (rewrite <- Heqv5) in "Hv5".
    iEval (rewrite <- Heqv6) in "Hv6".
    iEval (rewrite <- Heqv7) in "Hv7".
    iEval (rewrite <- Heqv8) in "Hv8".
    iEval (rewrite <- Heqv9) in "Hv9".
    iEval (rewrite <- Heqv10) in "Hv10".
    iEval (rewrite <- Heqv11) in "Hv11".
    iEval (rewrite <- Heqv12) in "Hv12".
    iEval (rewrite <- Heqv13) in "Hv13".
    iEval (rewrite <- Heqv14) in "Hv14".
    iEval (rewrite <- Heqv15) in "Hv15".
    iEval (rewrite <- Heqv16) in "Hv16".
    iEval (rewrite <- Heqv17) in "Hv17".
    assert (Hsp17 : kv_load_result mt v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 !!! Regidx csp_rs1 = spv).
    {{ unfold kv_load_result. kv_skipt. exact Hsp0. }}
    set (mt17 := kv_load_result mt v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17) in *.
    (* ---- #37: c.addi16sp sp,+256 @ 0x8000542a ---- *)
    iPoseProof (kv_i37 with "Htext") as "Hi37".
    assert (Hpc37 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s_pt root_ppn γ (mword_of_int (KernelSyms.kernelvec + 0x4a)) (mword_of_int 16) mt17
              (1/2)%Qp

              with "Hsm Htlbinv Hpc Hfile Hi37").
    iEval (rewrite Hpc37).
    iIntros "Hsm Htlbinv Hpc Hfile".
    iPoseProof (kv_cfg_recombine γ mstatus0 mie_v mdv0 menvcfg0
                  with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hsie & Hmie & Hmdl & Hmenv)".
    iEval (rewrite Hsp17) in "Hfile".
    (* the block stops HERE, at the sret's pc: the capstone runs #38 itself. *)
    iApply ("Hcont" with "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17").
  Qed.



End KernelvecCore.

(* kernelvec's sparse positive-offset save slots, re-addressed as [pa_stk]
   slots below the INTERRUPTED sp: kv_sp1 = sp - 256, so the window at
   kv_sp1 + 8j is stack slot 32 - j. *)
Lemma kv_slot_addr (m : regfile) (off : mword 64) (k : nat) :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1)) off
    = (mword_of_int (- (8 * Z.of_nat k)) : mword 64) ->
  add_vec (kv_sp1 m) off = pa_stk (m !!! Regidx csp_rs1) k.
Proof.
  intros H.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr add_vec_assoc H. unfold pa_stk, add_vec_int. reflexivity.
Qed.

Lemma kv_slot_addr0 (m : regfile) :
  kv_sp1 m = pa_stk (m !!! Regidx csp_rs1) 32.
Proof.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr. unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* THE 32 REGISTERS, ACCOUNTED FOR.  kernelvec's contract hands the        *)
(* interrupted map back VERBATIM, so the file-preservation argument has to *)
(* cover every index -- and with the callee's contract being               *)
(* [CalleeSaved.callee_saved] there are THREE groups, not two:             *)
(*                                                                        *)
(*   - the 18 registers kernelvec WRITES ([kv_saved]: sp + the 17 saved);  *)
(*   - the 12 remaining CALLEE-SAVED ones (s0..s11), which kerneltrap      *)
(*     preserves;                                                         *)
(*   - x0 and tp, which are in NEITHER group and need not be: x0's slot is *)
(*     [zero_reg] in any [gpr_file] ([WpGpr.gpr_file_x0], read off both    *)
(*     files) and tp's is [cid_word_of cpu_id] in any [tp_pin]ned map --    *)
(*     which is exactly why the bundle holds the file at [tp_pin], and why *)
(*     a trap that MIGRATES can hand the same map back at a new hart.      *)
(*                                                                        *)
(* [kv_regidx_cover] is the statement that those three groups are all 32,  *)
(* and it is the one thing here that cannot be derived: it is decided by   *)
(* enumerating [enum regidx].  The legacy round-trip axiom needed nothing  *)
(* like it because it claimed preservation of the whole complement of      *)
(* [kt_clobbered] -- including x0 and tp, which no real function contract  *)
(* may claim.                                                              *)
(* ===================================================================== *)
Lemma kv_regidx_cover (k : mword 5) :
  Regidx k ∉ kv_saved ->
  is_cs_idx k = true \/ k = (mword_of_int 0 : mword 5) \/ Regidx k = Regidx Rtp.
Proof.
  intros Hout.
  pose proof (elem_of_enum (Regidx k)) as Hi. vm_compute in Hi.
  repeat (apply elem_of_cons in Hi;
          destruct Hi as [Heq | Hi];
          [ apply regidx_inj in Heq; subst k;
            first [ left; vm_compute; reflexivity
                  | right; left; apply bv_eq; vm_compute; reflexivity
                  | right; right; vm_compute; reflexivity
                  | exfalso; apply Hout;
                    apply (bool_decide_eq_true_1 _); vm_compute; reflexivity ]
          | ]).
  by apply elem_of_nil in Hi.
Qed.

Lemma kv_file_restore `{CID : CpuId} (m Me mf : regfile) (spv : mword 64) :
  (* what kerneltrap promises about the map kernelvec called it with *)
  callee_saved (kv_m2 Me) mf ->
  (* ...and how that map relates to the interrupted one: it is [m] tp-pinned at
     the ENTRY hart, so it agrees with [m] everywhere except tp -- which is all
     this needs, at sp and at the twelve callee-saved indices. *)
  Me !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 ->
  (forall k : mword 5, is_cs_idx k = true -> Me !!! Regidx k = m !!! Regidx k) ->
  (* the two c.addi16sp cancel *)
  add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
    = m !!! Regidx csp_rs1 ->
  (* x0, read off the two files *)
  m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
  tp_pin mf !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
  forall i : regidx,
    (<[Regidx csp_rs1 :=
         regval_into_reg (add_vec spv
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]>
       (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 31 : mword 5))]>
       (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 30 : mword 5))]>
       (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 29 : mword 5))]>
       (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 28 : mword 5))]>
       (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 17 : mword 5))]>
       (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 16 : mword 5))]>
       (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 15 : mword 5))]>
       (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 14 : mword 5))]>
       (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 13 : mword 5))]>
       (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 12 : mword 5))]>
       (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 11 : mword 5))]>
       (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 10 : mword 5))]>
       (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 7 : mword 5))]>
       (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 6 : mword 5))]>
       (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 5 : mword 5))]>
       (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 3 : mword 5))]>
       (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]>
       (tp_pin mf))))))))))))))))))) !!! i
    = tp_pin m !!! i.
Proof.
  intros Hcs Hsp Hcsm Hspval Hx0m Hx0f i.
  assert (Hin_sp : Regidx csp_rs1 ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx csp_rs1 ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_1 : Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_3 : Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_5 : Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_6 : Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_7 : Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_10 : Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_11 : Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_12 : Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_13 : Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_14 : Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_15 : Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_16 : Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_17 : Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_28 : Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_29 : Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_30 : Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  assert (Hin_31 : Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)
    by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
  rewrite Hspval.
  destruct (decide (i ∈ kv_saved)) as [Hin | Hout].
  - (* one of the 18 written slots: read it off the nest *)
    unfold kv_saved in Hin.
    rewrite !elem_of_union !elem_of_singleton in Hin.
    (* PARENTHESISED: [A; B; [x|y]] parses as [(A; B); [x|y]], so an unbracketed
       tail after an 18-way [destruct] asks for 36 tactics. *)
    repeat match goal with HH : _ ∨ _ |- _ => destruct HH end;
      subst i;
      (repeat (rewrite upd_ne; [| kv_regne]));
      (rewrite upd_eq;
       unfold tp_pin;
       (rewrite upd_ne; [ reflexivity | kv_regne ])).
  - (* outside the written set: peel all 18, then the three groups *)
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_sp ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_31 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_30 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_29 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_28 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_17 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_16 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_15 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_14 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_13 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_12 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_11 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_10 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_7 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_6 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_5 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_3 ].
    rewrite upd_ne;
      [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_1 ].
    destruct i as [k].
    destruct (kv_regidx_cover k Hout) as [Hcsk | [Hx0 | Htp]].
    + (* callee-saved: kerneltrap preserved it, and kernelvec's own two
         writes (ra, sp) are not it *)
      assert (Hktp : Regidx k <> Regidx Rtp)
        by (apply not_eq_sym; apply (is_cs_idx_true_neq Rtp k);
            [ vm_compute; reflexivity | exact Hcsk ]).
      rewrite /tp_pin (upd_ne _ _ _ _ Hktp) (upd_ne _ _ _ _ Hktp).
      rewrite (callee_saved_lookup Hcs k Hcsk).
      unfold kv_m2, kv_m1.
      rewrite upd_ne;
        [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_1 ].
      rewrite upd_ne;
        [| let HeqK := fresh in intros HeqK; apply Hout; rewrite HeqK; exact Hin_sp ].
      exact (Hcsm k Hcsk).
    + (* x0: both files say [zero_reg] *)
      subst k. rewrite Hx0f.
      rewrite /tp_pin upd_ne; [ symmetry; exact Hx0m | kv_regne ].
    + (* tp: both maps are [tp_pin]ned at THIS hart, so both slots are its id *)
      rewrite Htp. rewrite /tp_pin !upd_eq. reflexivity.
Qed.

(* ===================================================================== *)
(* THE CAPSTONE: kernelvec IS the interrupt handler, so its public          *)
(* contract is [IntrDefs.intr_handler_spec] -- and with the contract        *)
(* stated over the FOLDED BUNDLE, three things about this proof follow      *)
(* that were not true of the version it replaces.                          *)
(*                                                                        *)
(* 1. IT CALLS THE REAL kerneltrap.  [SpecKerneltrap.KERNELTRAP] is stated  *)
(*    over exactly the bundle this contract hands in, so the call is an     *)
(*    ordinary function call at the sconf tier: no [kv_cell]s, no           *)
(*    [kt_clobbered], no round-trip axiom.                                  *)
(* 2. THE EPILOGUE RUNS ON A DIFFERENT HART THAN THE PROLOGUE.  kerneltrap  *)
(*    yields on a timer tick when this cpu has a current proc, so its post  *)
(*    is [wp_next true p] and everything after the call is at the RESUMING   *)
(*    hart -- which is why there is no [wp_kernelvec] monolith any more:     *)
(*    prologue, call and restore block are applied separately, the last of   *)
(*    them at [(CID := CIDn)].  (The [KernelvecCore] section closes above,   *)
(*    so those lemmas are generalized and can be applied at another hart.)   *)
(* 3. THE SRET IS THE sconf LEAF.  [WpSconfSret.wp_sret_s_sconf] is what     *)
(*    flips the SIE ghost back to '1' and re-forms the enabled arm, so the   *)
(*    restore block stops one instruction early and the capstone finishes    *)
(*    the function.  Its post IS [ihs_post_of], which is why the last step   *)
(*    of this proof is one [iApply].                                        *)
(*                                                                        *)
(* The SIE ghost is the REAL one now: the old proof allocated a fresh        *)
(* per-trap [γk] because the true half had to stay outside the handler run,  *)
(* and under the bundle it does not -- the half comes in with [sconf], rides  *)
(* through [kv_cfg_split], and comes back out for the sret.                  *)
(* ===================================================================== *)
Section KernelvecHandler.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kernelvec_handler_spec (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname) (pd pav pu : mword 64) :
    kernelvec_handler_spec_body γu γv γdk γtl γs pd pav pu.
  Proof.
    cbv beta delta [kernelvec_handler_spec_body].
    iIntros (Hgs) "#Hhw #Hinv #Htext #Hcaps".
    iApply intr_handler_spec_intro.
    iModIntro.
    iIntros (m av p pc0 sc tv) "%Hpc0 %Hsc Hentry Hnext".
    iEval (rewrite /ihs_entry_of) in "Hentry".
    (* [Hrcpt] is the KPT receipt (IntrDefs §6b), the tenth conjunct: the trap
       hands it over because the handler owes the ENABLED arm back, and the
       sret is what rebuilds that arm.  It goes into kerneltrap (which parks
       with it, inside [trap_csrs]) and comes back at the RESUMING hart. *)
    iDestruct "Hentry" as
      "(Hcg & Hsret & Hsepc & Hscause & Hstval & Hrcpt & Hcpu & Hclm & Hires & Hpc)".
    iEval (rewrite -sie_cap_gpr_of_eq) in "Hcg".
    iEval (rewrite -intr_res_of_eq) in "Hires".
    (* ---- the bundle -> the raw cells the VC tier runs on ---- *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct "Hcap" as "(Hstk & Htr & Hq0)".
    iDestruct "Hsc" as "(_ & _ & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Htie & %Hmsf)".
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    subst menvcfg0.
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    (* SIE = 0 inside the handler: the arm's eighth against the tied half.
       (The C checks this too, and kerneltrap's proof refutes the panic from
       the same fact -- see SpecKerneltrap.) *)
    iDestruct (ghost_var_agree with "Hhalf Hq0") as %HSIE0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
      by (rewrite HSIE0; vm_compute; reflexivity).
    assert (Hleg : WpGprCsrwCommon.legalize_sstatus_val ms
                     (WpGprCsrwCommon.sstatus_write_val ms (mword_of_int 2)) = ms).
    { apply WpGprCsrwC.legalize_sie_clear_idem;
        [ exact HSIE0 | exact HXS | exact HFS | exact HVS | exact HSD | exact HMPP ]. }
    (* the translation slot: SIE = 0 does not refute Bare, but the INSTALLED
       HANDLER does -- [intr_res] owns the stvec cell and so does the Bare
       arm. *)
    iDestruct "Htr" as "[(Hbit0 & Hbare & Hbstv) | (Hbit1 & Hkpt)]".
    { iEval (rewrite /intr_res) in "Hires".
      iDestruct "Hires" as (h0 vb0) "(_ & _ & _ & Hstv & _)".
      iDestruct "Hbstv" as (v0) "Hbstv".
      iDestruct (reg_pointsto_conflict stvec (DfracOwn 1) with "Hstv Hbstv") as %[]. }
    iDestruct "Hkpt" as (root_ppn) "Htlbinv".
    (* THE FILE IS HELD AT THE PINNED MAP, so the whole function runs at
       [tp_pin m] and only the final [gpr_file_ext] converts back.  It is
       spelled out rather than [set] to a local name: the map terms below have
       to match [kv_file_restore]'s statement SYNTACTICALLY, and a let-bound
       abbreviation makes the unifier walk an 18-deep insert nest under a
       delta. *)
    assert (Hsppin : tp_pin m !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by apply tp_pin_sp.
    (* NAME IT OPAQUELY.  Everything before the crossing is stated at the ENTRY
       hart's pinned map; after the crossing [tp_pin m] means the RESUMING
       hart's.  The two differ only inside [tp_pin], so handing both to the
       unifier as 18-deep insert nests does not fail, it HANGS -- an opaque
       name makes every pre-crossing term match syntactically. *)
    remember (tp_pin m) as Me eqn:HMe.
    iEval (rewrite -Hsppin) in "Hstk".
    (* x0's slot on the way IN.  Together with the same read on the way out it
       is what covers the one register neither [kv_saved] nor [callee_saved]
       mentions -- see [kv_file_restore]. *)
    iDestruct (gpr_file_x0 Me (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0m Hfile]".
    (* ---- SPLIT THE CARVE.  [kv_frame_slots] = 90 + av below the interrupted
           sp: kernelvec's own 32-slot frame on top, and [58 + av] underneath
           that ARE kerneltrap's cone budget -- so its [kerneltrap_stack <= av']
           premise is [lia] with nothing to supply.  The 58 is
           [kv_frame_slots - 32] and moves with it. ---- *)
    assert (Hkvs : (trap_res false + (trap_res true + av))%nat = (32 + (58 + av))%nat)
      by (unfold trap_res; lia).
    iEval (rewrite Hkvs stack_own_app) in "Hstk".
    iDestruct "Hstk" as "[Hstk Hdeep]".

    pose proof (kv_slot_addr0 Me) as Hb32.
    assert (Hb30 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 30)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb28 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 28)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb27 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 27)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb26 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 26)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb23 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 23)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb22 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 22)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb21 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 21)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb20 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 20)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb19 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 19)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb18 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 18)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb17 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 17)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb16 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 16)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb5 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 5)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb4 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 4)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb3 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 3)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb2 : add_vec (kv_sp1 Me) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = pa_stk (Me !!! Regidx csp_rs1) 2)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    (* open the 32-slot frame and pull out the 17 save slots *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 &
      S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 &
      S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32 & _)".
    iDestruct "S32" as (w1) "Hw1".   iEval (rewrite -Hb32) in "Hw1".
    iDestruct "S30" as (w2) "Hw2".   iEval (rewrite -Hb30) in "Hw2".
    iDestruct "S28" as (w3) "Hw3".   iEval (rewrite -Hb28) in "Hw3".
    iDestruct "S27" as (w4) "Hw4".   iEval (rewrite -Hb27) in "Hw4".
    iDestruct "S26" as (w5) "Hw5".   iEval (rewrite -Hb26) in "Hw5".
    iDestruct "S23" as (w6) "Hw6".   iEval (rewrite -Hb23) in "Hw6".
    iDestruct "S22" as (w7) "Hw7".   iEval (rewrite -Hb22) in "Hw7".
    iDestruct "S21" as (w8) "Hw8".   iEval (rewrite -Hb21) in "Hw8".
    iDestruct "S20" as (w9) "Hw9".   iEval (rewrite -Hb20) in "Hw9".
    iDestruct "S19" as (w10) "Hw10". iEval (rewrite -Hb19) in "Hw10".
    iDestruct "S18" as (w11) "Hw11". iEval (rewrite -Hb18) in "Hw11".
    iDestruct "S17" as (w12) "Hw12". iEval (rewrite -Hb17) in "Hw12".
    iDestruct "S16" as (w13) "Hw13". iEval (rewrite -Hb16) in "Hw13".
    iDestruct "S5" as (w14) "Hw14".  iEval (rewrite -Hb5) in "Hw14".
    iDestruct "S4" as (w15) "Hw15".  iEval (rewrite -Hb4) in "Hw15".
    iDestruct "S3" as (w16) "Hw16".  iEval (rewrite -Hb3) in "Hw16".
    iDestruct "S2" as (w17) "Hw17".  iEval (rewrite -Hb2) in "Hw17".
    (* ---- the fraction choreography, AT THE REAL SIE GHOST ---- *)
    iDestruct (kv_cfg_split sie_gname ms MIE_S mdv0 MENVCFG_S
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom eq_refl
                 with "Hhw Hinv Hhs Hpriv Hms Hhalf Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    (* ---- instrs #1..#19: the prologue (frame push, 17 saves, jal) ---- *)
    iApply (wp_kv_prologue root_ppn sie_gname Me
              w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
              with "Hsm Htlbinv Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* THE SAVED VALUES ARE MADE HART-FREE HERE, and that is not cosmetic: the
       cells come out of the prologue holding [Me !!! k] at the ENTRY
       hart, while the file this proof must hand back is [tp_pin m] at the
       RESUMING one.  [k] is never tp, so each value is just [m !!! k] -- and
       once they are spelled that way the restored map's slots mention no hart
       at all, which is what lets [kv_file_restore] be stated at ONE hart.
       (Getting this wrong does not fail, it HANGS: the unifier is handed two
       18-deep insert nests that differ only inside a [tp_pin].) *)
    assert (Hv1 : Me !!! Regidx (mword_of_int 1 : mword 5)
                    = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv3 : Me !!! Regidx (mword_of_int 3 : mword 5)
                    = m !!! Regidx (mword_of_int 3 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv5 : Me !!! Regidx (mword_of_int 5 : mword 5)
                    = m !!! Regidx (mword_of_int 5 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv6 : Me !!! Regidx (mword_of_int 6 : mword 5)
                    = m !!! Regidx (mword_of_int 6 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv7 : Me !!! Regidx (mword_of_int 7 : mword 5)
                    = m !!! Regidx (mword_of_int 7 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv10 : Me !!! Regidx (mword_of_int 10 : mword 5)
                    = m !!! Regidx (mword_of_int 10 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv11 : Me !!! Regidx (mword_of_int 11 : mword 5)
                    = m !!! Regidx (mword_of_int 11 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv12 : Me !!! Regidx (mword_of_int 12 : mword 5)
                    = m !!! Regidx (mword_of_int 12 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv13 : Me !!! Regidx (mword_of_int 13 : mword 5)
                    = m !!! Regidx (mword_of_int 13 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv14 : Me !!! Regidx (mword_of_int 14 : mword 5)
                    = m !!! Regidx (mword_of_int 14 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv15 : Me !!! Regidx (mword_of_int 15 : mword 5)
                    = m !!! Regidx (mword_of_int 15 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv16 : Me !!! Regidx (mword_of_int 16 : mword 5)
                    = m !!! Regidx (mword_of_int 16 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv17 : Me !!! Regidx (mword_of_int 17 : mword 5)
                    = m !!! Regidx (mword_of_int 17 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv28 : Me !!! Regidx (mword_of_int 28 : mword 5)
                    = m !!! Regidx (mword_of_int 28 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv29 : Me !!! Regidx (mword_of_int 29 : mword 5)
                    = m !!! Regidx (mword_of_int 29 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv30 : Me !!! Regidx (mword_of_int 30 : mword 5)
                    = m !!! Regidx (mword_of_int 30 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    assert (Hv31 : Me !!! Regidx (mword_of_int 31 : mword 5)
                    = m !!! Regidx (mword_of_int 31 : mword 5))
      by (rewrite HMe; unfold tp_pin; rewrite upd_ne; [reflexivity | kv_regne]).
    iEval (rewrite Hv1) in "Hw1".
    iEval (rewrite Hv3) in "Hw2".
    iEval (rewrite Hv5) in "Hw3".
    iEval (rewrite Hv6) in "Hw4".
    iEval (rewrite Hv7) in "Hw5".
    iEval (rewrite Hv10) in "Hw6".
    iEval (rewrite Hv11) in "Hw7".
    iEval (rewrite Hv12) in "Hw8".
    iEval (rewrite Hv13) in "Hw9".
    iEval (rewrite Hv14) in "Hw10".
    iEval (rewrite Hv15) in "Hw11".
    iEval (rewrite Hv16) in "Hw12".
    iEval (rewrite Hv17) in "Hw13".
    iEval (rewrite Hv28) in "Hw14".
    iEval (rewrite Hv29) in "Hw15".
    iEval (rewrite Hv30) in "Hw16".
    iEval (rewrite Hv31) in "Hw17".
    iPoseProof (kv_cfg_recombine sie_gname ms MIE_S mdv0 MENVCFG_S
                  with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hhalf & Hmie & Hmdl & Hmenv)".
    (* ---- THE CALL.  Re-fold the bundle for the callee: same cells, same
           translation slot, the DEEP carve as its stack, and the four things
           the trap handed us that kerneltrap needs in turn (the travelling
           tie, the installed handler, the per-cpu bookkeeping, the claim). ---- *)
    assert (Hsp_l : kv_m2 Me !!! Regidx csp_rs1 = kv_sp1 Me).
    { unfold kv_m2. rewrite upd_ne; [| kv_regne]. unfold kv_m1. apply upd_eq. }
    assert (Hpin2 : tp_pin (kv_m2 Me) = kv_m2 Me).
    { rewrite HMe. unfold kv_m2, kv_m1.
      rewrite -(tp_pin_upd _ (mword_of_int 1 : mword 5)); [| kv_regne].
      rewrite -(tp_pin_upd _ csp_rs1); [| kv_regne].
      rewrite (tp_pin_id (tp_pin m)); [reflexivity |].
      unfold tp_pin. apply upd_eq. }
    assert (Hdi : devintr_ret sc <> (mword_of_int 0 : mword 64)).
    { destruct Hsc as [-> | ->]; unfold devintr_ret; vm_compute; discriminate. }
    assert (Hb32' : pa_stk (Me !!! Regidx csp_rs1) 32 = kv_sp1 Me)
      by (symmetry; apply kv_slot_addr0).
    iEval (rewrite Hb32') in "Hdeep".
    (* built in three named pieces rather than one [iFrame] over the unfolded
       bundle: [iFrame] re-associates the goal, so a positional [iSplitL] over
       a nine-conjunct nest splits somewhere else than it reads. *)
    iAssert (sconf) with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]" as "Hscn".
    { rewrite /sconf. iFrame "Hhw Hinv Hpriv".
      iSplitL "Hms Hhalf Htie".
      { iExists ms. iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
      repeat split; try assumption; reflexivity. }
    iAssert (sie_cap (kv_m2 Me) (58 + av) false p)
      with "[Hdeep Hbit1 Htlbinv Hq0]" as "Hcapn".
    { rewrite /sie_cap. iSplitL "Hdeep". { rewrite Hsp_l. iExact "Hdeep". }
      iSplitL "Hbit1 Htlbinv".
      { iApply (strans_inv_intro root_ppn with "Hbit1 Htlbinv"). }
      iExact "Hq0". }
    iDestruct (sie_cap_gpr_join with "Hhs Hscn Hcapn [Hfile]") as "Hcgk".
    { rewrite Hpin2. iExact "Hfile". }
    iApply (Kerneltrap.wp_kerneltrap_sconf γu γv γdk γtl γs pd pav pu
              (kv_m2 Me) (58 + av) p pc0 sc tv ∅
              Hgs ltac:(lia) Hdi Hpc0
              with "Hcgk Hsret Hires Hrcpt [Hcpu] Htext Hpc Hsepc Hscause Hstval Hcaps Hclm").
    all: try lkbelow.
    { iFrame "Hcpu". }
    (* ---- THE CROSSING: everything below is at the RESUMING hart ---- *)
    iIntros (CIDn Hsn mf ms_f sc' tv') "%Hcs %Hsppf %Hspief %Hsief Hcgf Hsretf Hiresf Hrcptf Hownf Hsepcf Hscausef Hstvalf Hpcf Hclmf".
    assert (Hret : ret_pc (kv_m2 (tp_pin m) !!! Regidx (mword_of_int 1 : mword 5))
                   = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64)).
    { unfold kv_m2. rewrite upd_eq. unfold ret_pc, regval_into_reg.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpcf".
    iDestruct (sie_cap_gpr_at_close with "Hcgf") as "Hcgf".
    iDestruct (sie_cap_gpr_split with "Hcgf") as "(Hhsf & Hscf & Hcapf & Hfilef)".
    iDestruct "Hcapf" as "(Hstkf & Htrf & Hq0f)".
    (* THE RESUMING HART'S OWN [hw_config] / [minstret_inv]: both hold that
       hart's register cells, so the section's copies are the wrong ones here. *)
    iDestruct "Hscf" as "(#Hhwf & #Hinvf & Hprivf & Hmsxf & Hmiexf & Hmenvxf)".
    iDestruct "Hmsxf" as (msf) "(Hmsf & Hhalff & Htief & %Hmsff)".
    iDestruct "Hmiexf" as (mdvf) "(Hmief & Hmdlf & %Hmmf)".
    iDestruct "Hmenvxf" as (menvcfgf)
      "(Hmenvf & %HPBMTEf & %Hpmmf & %Hlpef & %Hfiomf & %Hmenvvalf)".
    subst menvcfgf.
    pose proof Hmsff as Hmsff'.
    destruct Hmsff' as (HMPRVf & HSXLf & HMXRf & HTSRf & HXSf & HFSf & HVSf & HSDf & HMPPf & HTVMf).
    iDestruct (ghost_var_agree with "Hhalff Hq0f") as %HSIE0f.
    assert (HSIEf : eq_vec (_get_Mstatus_SIE msf) ('b"1") = false)
      by (rewrite HSIE0f; vm_compute; reflexivity).
    assert (Hlegf : WpGprCsrwCommon.legalize_sstatus_val msf
                      (WpGprCsrwCommon.sstatus_write_val msf (mword_of_int 2)) = msf).
    { apply WpGprCsrwC.legalize_sie_clear_idem;
        [ exact HSIE0f | exact HXSf | exact HFSf | exact HVSf | exact HSDf | exact HMPPf ]. }
    iDestruct "Htrf" as "[(Hbit0f & Hbaref & Hbstvf) | (Hbit1f & Hkptf)]".
    { iEval (rewrite /intr_res) in "Hiresf".
      iDestruct "Hiresf" as (h0 vb0) "(_ & _ & _ & Hstv & _)".
      iDestruct "Hbstvf" as (v0) "Hbstvf".
      iDestruct (reg_pointsto_conflict stvec (DfracOwn 1) with "Hstv Hbstvf") as %[]. }
    iDestruct "Hkptf" as (root_ppnf) "Htlbinvf".
    (* x0's slot, read off the returned file while it is still at [tp_pin mf]:
       one of the two registers no [callee_saved] contract can speak about. *)
    iDestruct (gpr_file_x0 (tp_pin mf) (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hfilef") as "[%Hx0f Hfilef]".
    iDestruct "Hownf" as "(Hcellsf & Hcntf)".
    (* sp is callee-saved, so the returned file's sp still names our frame *)
    assert (Hspf : tp_pin mf !!! Regidx csp_rs1 = kv_sp1 Me).
    { rewrite tp_pin_sp. destruct Hcs as (Hsp & _). rewrite Hsp. exact Hsp_l. }
    (* ---- instrs #20..#37: the restore block, AT THE RESUMING HART ---- *)
    iDestruct (kv_cfg_split (CID := CIDn) sie_gname msf MIE_S mdvf MENVCFG_S
                 HSIEf HMPRVf HSXLf HMXRf Hlegf Hmmf HPBMTEf Hpmmf Hlpef Hfiomf eq_refl
                 with "Hhwf Hinvf Hhsf Hprivf Hmsf Hhalff Hmief Hmdlf Hmenvf")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_kv_restore (CID := CIDn) root_ppnf sie_gname (tp_pin mf) (kv_sp1 Me)
              msf MIE_S mdvf MENVCFG_S
              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              HSIEf HMPRVf HSXLf Hmmf HPBMTEf eq_refl Hspf
              with "Hhwf Hinvf Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinvf Hpcf Hfilef
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhsf Hprivf Hmsf Hhalff Hmief Hmdlf Hmenvf Htlbinvf Hpcf Hfilef
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".

    (* ---- the file is back at [tp_pin m], register for register ---- *)
    assert (Hcsm : forall k : mword 5, is_cs_idx k = true ->
                     Me !!! Regidx k = m !!! Regidx k).
    { intros k Hk. rewrite HMe. unfold tp_pin. rewrite upd_ne; [reflexivity |].
      apply not_eq_sym; apply (is_cs_idx_true_neq Rtp k);
        [ vm_compute; reflexivity | exact Hk ]. }
    assert (Hx0m' : m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg).
    { rewrite -Hx0m HMe. unfold tp_pin. rewrite upd_ne; [reflexivity | kv_regne]. }
    assert (Hspcanc : add_vec (kv_sp1 Me)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
                      = m !!! Regidx csp_rs1).
    { unfold kv_sp1, regval_into_reg. rewrite add_vec_assoc kv_cancel.
      rewrite kv_addv_zero. exact Hsppin. }
    iDestruct (gpr_file_ext (CID := CIDn) _ (tp_pin m)
                 (kv_file_restore (CID := CIDn) m Me mf (kv_sp1 Me)
                    Hcs Hsppin Hcsm Hspcanc Hx0m' Hx0f) with "Hfilef") as "Hfilef".
    (* ---- rebuild the 32-slot frame from the 17 restored windows ---- *)
    iEval (rewrite Hb32) in "Hw1".
    iEval (rewrite Hb30) in "Hw2".
    iEval (rewrite Hb28) in "Hw3".
    iEval (rewrite Hb27) in "Hw4".
    iEval (rewrite Hb26) in "Hw5".
    iEval (rewrite Hb23) in "Hw6".
    iEval (rewrite Hb22) in "Hw7".
    iEval (rewrite Hb21) in "Hw8".
    iEval (rewrite Hb20) in "Hw9".
    iEval (rewrite Hb19) in "Hw10".
    iEval (rewrite Hb18) in "Hw11".
    iEval (rewrite Hb17) in "Hw12".
    iEval (rewrite Hb16) in "Hw13".
    iEval (rewrite Hb5) in "Hw14".
    iEval (rewrite Hb4) in "Hw15".
    iEval (rewrite Hb3) in "Hw16".
    iEval (rewrite Hb2) in "Hw17".
    iAssert (stack_own (Me !!! Regidx csp_rs1) 32)
      with "[S1 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S24 S25 S29 S31
            Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17]"
      as "Hstk".
    {
      rewrite stack_own_slots. cbn [seq].
      iSplitL "S1"; [iExact "S1" |].
      iSplitL "Hw17"; [by iExists _ |].
      iSplitL "Hw16"; [by iExists _ |].
      iSplitL "Hw15"; [by iExists _ |].
      iSplitL "Hw14"; [by iExists _ |].
      iSplitL "S6"; [iExact "S6" |].
      iSplitL "S7"; [iExact "S7" |].
      iSplitL "S8"; [iExact "S8" |].
      iSplitL "S9"; [iExact "S9" |].
      iSplitL "S10"; [iExact "S10" |].
      iSplitL "S11"; [iExact "S11" |].
      iSplitL "S12"; [iExact "S12" |].
      iSplitL "S13"; [iExact "S13" |].
      iSplitL "S14"; [iExact "S14" |].
      iSplitL "S15"; [iExact "S15" |].
      iSplitL "Hw13"; [by iExists _ |].
      iSplitL "Hw12"; [by iExists _ |].
      iSplitL "Hw11"; [by iExists _ |].
      iSplitL "Hw10"; [by iExists _ |].
      iSplitL "Hw9"; [by iExists _ |].
      iSplitL "Hw8"; [by iExists _ |].
      iSplitL "Hw7"; [by iExists _ |].
      iSplitL "Hw6"; [by iExists _ |].
      iSplitL "S24"; [iExact "S24" |].
      iSplitL "S25"; [iExact "S25" |].
      iSplitL "Hw5"; [by iExists _ |].
      iSplitL "Hw4"; [by iExists _ |].
      iSplitL "Hw3"; [by iExists _ |].
      iSplitL "S29"; [iExact "S29" |].
      iSplitL "Hw2"; [by iExists _ |].
      iSplitL "S31"; [iExact "S31" |].
      iSplitL "Hw1"; [by iExists _ |].
      done. }
    (* ...and the whole carve, exactly as it arrived: kernelvec's 32 on top,
       the callee budget underneath. *)
    iAssert (stack_own (m !!! Regidx csp_rs1) (trap_res true + av)) with "[Hstk Hstkf]" as "Hstk".
    { iEval (rewrite -Hsppin).
      assert (Hkvs' : (trap_res true + av)%nat = (32 + (58 + av))%nat)
        by (unfold trap_res; lia).
      rewrite Hkvs'. iApply stack_own_app. iSplitL "Hstk"; [iExact "Hstk" |].
      rewrite -(kv_slot_addr0 Me) -Hspf. iExact "Hstkf". }
    (* ---- instr #38: THE SRET, at the sconf tier.  It is the instruction
           that flips the SIE ghost '0' -> '1' and re-forms the enabled arm,
           which is why it needs the whole package rather than the raw cells:
           the bundle, the travelling tie, BOTH ghost eighths (the arm's, in
           the bundle, and the count's, out of [cpu_hart]), the installed
           handler and the running claim.  Its post IS [ihs_post_of]. ---- *)
    iPoseProof (kv_i38 with "Htext") as "Hi38".
    iAssert (sconf (CID := CIDn)) with "[Hprivf Hmsf Hhalff Htief Hmief Hmdlf Hmenvf]"
      as "Hscf".
    { rewrite /sconf. iFrame "Hhwf Hinvf Hprivf".
      iSplitL "Hmsf Hhalff Htief".
      { iExists msf. iFrame "Hmsf Hhalff Htief". iPureIntro. exact Hmsff. }
      iSplitL "Hmief Hmdlf".
      { iExists mdvf. iFrame "Hmief Hmdlf". iPureIntro. exact Hmmf. }
      iExists MENVCFG_S. iFrame "Hmenvf". iPureIntro.
      repeat split; try assumption; reflexivity. }
    iAssert (sie_cap (CID := CIDn) m (trap_res true + av) false p)
      with "[Hstk Hbit1f Htlbinvf Hq0f]" as "Hcapf".
    { rewrite /sie_cap. iSplitL "Hstk". { iExact "Hstk". }
      iSplitL "Hbit1f Htlbinvf".
      { iApply (strans_inv_intro (CID := CIDn) root_ppnf with "Hbit1f Htlbinvf"). }
      iExact "Hq0f". }
    iDestruct (sie_cap_gpr_join (CID := CIDn) with "Hhsf Hscf Hcapf Hfilef") as "Hcgs".
    iApply (wp_sret_s_sconf (CID := CIDn)
              (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64) m av pc0
              with "Hcgs Hsretf Hcntf Hsepcf [Hscausef] [Hstvalf] Hiresf Hrcptf Hcellsf Hclmf Hpcf Hi38").
    { iExists sc'. iExact "Hscausef". }
    { iExists tv'. iExact "Hstvalf". }
    iIntros "Hcg Hpc".
    (* ---- and the post is the engine's own precondition, at THIS hart ---- *)
    iDestruct (wp_next_at true p _ CIDn Hsn with "Hnext") as "Hnext".
    iEval (rewrite /ihs_post_of) in "Hnext".
    iEval (rewrite Hpc0) in "Hpc".
    iApply ("Hnext" with "[Hcg] Hpc").
    iEval (rewrite sie_cap_gpr_of_eq) in "Hcg". iExact "Hcg".
  Qed.

End KernelvecHandler.
End KernelvecProof.
