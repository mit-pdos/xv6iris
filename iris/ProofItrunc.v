(* ProofItrunc.v -- itrunc's instruction chain.  The vocabulary it consumes
   (the map models, the freed-set arithmetic, the frame and the two loop
   states) is in ProofItruncParts.v; this file is about control flow.

   THE SHAPE.  A prologue, a twelve-iteration direct loop, a test on
   [ip->addrs[NDIRECT]] that either falls straight through or takes the
   indirect arm, and a shared tail ([ip->size = 0]; iupdate; epilogue).  The
   indirect arm rejoins the tail by an explicit [j] at +0x92, which is why
   the tail is a lemma rather than a straight continuation of the fallthrough
   path: both predecessors need it.

   S4 IS SAVED CONDITIONALLY.  [sd s4,0(sp)] is at +0x50 and [ld s4,0(sp)]
   at +0x90, both INSIDE the indirect arm, so the direct-only path owns the
   sixth frame slot without ever giving it a value.  [it_frame]'s sixth
   conjunct is existential for exactly that reason. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSmodeHalf.
Require Import ByteCursor ByteBuf.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapEnc BitmapInv.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import SpecBread SpecBrelse SpecBfree SpecIupdate.
Require Import SpecItrunc.
Require Import ProofItruncParts.
Require Import CodeItrunc.
From Kernel Require KernelSyms.
Import Defs.

Local Open Scope Z_scope.

Module ItruncProof (BR : BREAD) (BF : BFREE) (BL : BRELSE) (IU : IUPDATE).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Notation IT := KernelSyms.itrunc.

(* ===================================================================== *)
(*  The continuation: itrunc's postcondition, as a resource               *)
(* ===================================================================== *)
Section ItruncCont.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Definition it_cont `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γ : log_names) (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (used : gset Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (ds : list dinode) (u : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        own_ctx (p_context (proc_addr j)) -∗
        park_hlf j true -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        inode_meta ip (di_trunc dn) -∗
        inode_map γfs ip bm_empty -∗
        inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
        fsblock γfs (IBLOCK inum inodestart)
                (diblk_bytes (<[islot inum := di_trunc dn]> ds)) -∗
        bslots bn 2 -∗
        (∃ u' : nat, ⌜(u <= u' <= S u)%nat⌝ ∗ log_op γ u') -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

End ItruncCont.

(* the register-threading invariants: the five registers the frame saves *)
Definition it_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

(* itrunc pushes with [c.addi16sp sp,-48] (iti_00), not with the
   [sign_extend' 12] shape bfree's [c.addi sp,sp,-32] produces, so the
   offset is spelled as the decoder spells it. *)
Definition it_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))).

(* the push really is -48 and the pop really is +48 -- checked against the
   decoder rather than assumed, since [caddi16sp_imm]'s bit scramble is
   exactly the kind of thing that silently disagrees *)
Lemma it_push_imm :
  bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))
               : mword 64) = 18446744073709551568.
Proof. vm_compute; reflexivity. Qed.

Lemma it_pop_imm :
  bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))
               : mword 64) = 48.
Proof. vm_compute; reflexivity. Qed.

End ItruncProof.
