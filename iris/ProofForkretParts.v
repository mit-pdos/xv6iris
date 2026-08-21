(* ProofForkretParts.v -- forkret's PURE obligations: the address arithmetic
   its five AUIPC/ADDI, LUI/ADDI/SLLI and branch immediates encode.

   Every one of these is a LAYOUT FACT -- that [first.1] really does sit at
   forkret+0x14's auipc target minus 1712, that [userret] is 0x9c past
   [_trampoline], that the [c.beqz] at +0x24 really does skip to +0x64 --
   so a relayout should break one named lemma here rather than a step of
   the walk.  All closed, all [vm_compute].

   The three-instruction [TRAMPOLINE] build (lui a4,0x4000 / c.addi a4,a4,-1 /
   c.slli a4,a4,12) is NOT restated: it is byte-for-byte prepare_return's,
   and [ProofPrepareReturnParts]' [prr_lui_a4] / [prr_addi_a4] /
   [prr_slli_a4] are reused verbatim. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Import TrampPt.
Require Import UserretDefs.
Require Import SpecPrepareReturn.
Require Import SpecForkret.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Notation FR := KernelSyms.forkret.

(* ---- +0x14 auipc a5,0x9 / +0x18 addi a5,a5,-1712 : &first ---- *)
(* the immediate READS as 2384 and SIGN-EXTENDS to -1712; read as positive
   it lands 0x1000 too high, which is the usual confusing failure. *)
(* SPELLED [KernelSyms.first_1], NOT [FirstTok.first_addr], and the two are
   the SAME TERM -- [first_addr]'s body is this.  Naming it here would drag
   [FirstTok]'s whole file-system cone into a file of closed [vm_compute]s,
   for one constant; the walk that consumes this lemma has [first_addr] in
   scope and conversion does the rest. *)
Lemma fkr_first_addr :
  add_vec (add_vec (mword_of_int (FR + 0x14) : mword 64)
             (auipc_off (mword_of_int 9 : mword 20)))
    (sign_extend' 64 (mword_of_int 2384 : mword 12))
  = (mword_of_int KernelSyms.first_1 : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x24 c.beqz a5, +0x64 : the [first == 0] skip ---- *)
Definition fkr_beqz_imm : mword 13 :=
  sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")).

Lemma fkr_beqz_tgt :
  add_vec (mword_of_int (FR + 0x24) : mword 64) (sign_extend' 64 fkr_beqz_imm)
  = mword_of_int (FR + 0x64).
Proof. rewrite /fkr_beqz_imm. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fkr_beqz_align :
  eq_vec (access_vec_dec
            (add_vec (mword_of_int (FR + 0x24) : mword 64)
               (sign_extend' 64 fkr_beqz_imm)) 0) ('b"0") = true.
Proof. rewrite /fkr_beqz_imm. vm_compute. reflexivity. Qed.

(* ---- +0x74 auipc a5,0x4 / +0x78 addi a5,a5,1820 : &userret ---- *)
Lemma fkr_userret_addr :
  add_vec (add_vec (mword_of_int (FR + 0x74) : mword 64)
             (auipc_off (mword_of_int 4 : mword 20)))
    (sign_extend' 64 (mword_of_int 1820 : mword 12))
  = (mword_of_int KernelSyms.userret : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x7c auipc a3,0x4 / +0x80 addi a3,a3,1656 : &_trampoline ---- *)
Lemma fkr_trampoline_addr :
  add_vec (add_vec (mword_of_int (FR + 0x7c) : mword 64)
             (auipc_off (mword_of_int 4 : mword 20)))
    (sign_extend' 64 (mword_of_int 1656 : mword 12))
  = (mword_of_int KernelSyms.trampoline : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x84 c.sub a5,a5,a3 : userret - trampoline = 0x9c ---- *)
Lemma fkr_userret_off :
  sub_vec (mword_of_int KernelSyms.userret : mword 64)
          (mword_of_int KernelSyms.trampoline : mword 64)
  = (mword_of_int 0x9c : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x86 c.add a5,a5,a4 : TRAMPOLINE + (userret - trampoline) ---- *)
(* [uservec_tvec] is [SpecPrepareReturn]'s name for [mword_of_int TRAMPOLINE]
   -- the value the same three instructions build there. *)
Lemma fkr_tramp_userret :
  add_vec (mword_of_int 0x9c : mword 64) uservec_tvec = uva 0x9c.
Proof.
  rewrite /uservec_tvec /uva /TRAMPOLINE. apply bv_eq. vm_compute. reflexivity.
Qed.

(* ---- +0x8e c.jalr a5 : the target is 2-aligned, so [ret_pc] is the
       identity on it ---- *)
Lemma fkr_ret_pc : ret_pc (uva 0x9c) = uva 0x9c.
Proof. rewrite /uva /TRAMPOLINE. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- the push_off depth myproc's contract bounds, at forkret's level 1;
       [lia] cannot evaluate the power, so it is [vm_compute]d once ---- *)
Lemma fkr_n1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
