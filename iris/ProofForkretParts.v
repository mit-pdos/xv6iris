(* ProofForkretParts.v -- forkret's PURE obligations: the address arithmetic
   its AUIPC/ADDI, LUI/ADDI/SLLI, JAL and branch immediates encode.

   Every one of these is a LAYOUT FACT -- that [first.1] really does sit at
   forkret+0x14's auipc target minus 1712, that [userret] is 0x9c past
   [_trampoline], that the [c.beqz] at +0x24 really does skip to +0x64 --
   so a relayout should break one named lemma here rather than a step of
   the walk.  All closed, all [vm_compute], with the two exceptions noted
   below.

   The [if (first)] arm (+0x26 .. +0xa2 -- [fsinit(ROOTDEV)], the release
   store, [kexec("/init", {"/init", 0})] and the [panic("exec")] tail) adds
   the three [jal] targets, a second reading of [&first], the two rodata
   literals, the [beq] to the panic tail and the two frame slots the argv
   array is built in.  The two frame-slot lemmas are the only ones here that
   are NOT closed -- they are universally quantified in the kernel-stack top
   -- and go through [KernelRvcDecode.stk_push] instead.

   The three-instruction [TRAMPOLINE] build (lui a4,0x4000 / c.addi a4,a4,-1 /
   c.slli a4,a4,12) is NOT restated: it is byte-for-byte prepare_return's,
   and [ProofPrepareReturnParts]' [prr_lui_a4] / [prr_addi_a4] /
   [prr_slli_a4] are reused verbatim. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Import StackOwn.        (* [pa_stk] -- the frame-slot spelling *)
Require Import KernelRvcDecode. (* [stk_push] -- the one non-closed proof here *)
Require Import RiscvLang.       (* [GenId] / [CpuId], [text_end] *)
Require Import RiscvModelBytes. (* [pa_add] *)
Require Import RiscvPtsto.      (* [cstring_bytes], [↦ₛ□], [mem_ktier_mono] *)
Require Import KernelDataInv.   (* [kernel_data] and its two extraction rules *)
Require Import ByteBuf.         (* [bb_cstr] -- kexec's shape for the path *)
Require Import PrintkArgs.      (* [pk_desc_res] / [PkAStr] -- panic's shape *)
From Kernel Require KernelData.
Require Import TrampPt.
Require Import UserretDefs.
Require Import SpecPrepareReturn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Notation FR := KernelSyms.forkret.

(* The two rodata literals the [if (first)] arm points at.  Neither has a
   symbol of its own in the image -- both sit in the anonymous string pool
   just past [etext] -- so they are SPELLED here, once, and every lemma below
   is stated against the name rather than against a bare hex constant.  The
   dump agrees: [kernel.asm] annotates the two auipc/addi pairs with
   [# 80007180 <etext+0x180>] and [# 80007188 <etext+0x188>] respectively. *)
Definition fkr_init_path : Z := 0x80007180.   (* the string "/init" *)
Definition fkr_exec_msg  : Z := 0x80007188.   (* the string "exec"  *)

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

(* ===================================================================== *)
(*  The [if (first)] arm: +0x26 .. +0xa2.                                 *)
(* ===================================================================== *)

(* ---- +0x26 c.li a0,1 : fsinit's [ROOTDEV] argument ---- *)
(* [C_LI] executes as [ADDI rd, zreg, sign_extend' 12 imm], so what lands in
   a0 is the [add_vec] off [zero_reg] -- that is the shape the walk sees.
   [SpecFsinit] asks for [sign_extend' 64 (dev : mword 32)] at
   [dev = InodeInv.ROOTDEV]; ROOTDEV is SPELLED as its body
   [mword_of_int 1 : mword 32] rather than named, so that [InodeInv]'s
   file-system cone stays out of a file of closed [vm_compute]s (the same
   reason [fkr_first_addr] spells [KernelSyms.first_1]).  The walk has
   [ROOTDEV] in scope and conversion does the rest. *)
Lemma fkr_rootdev :
  add_vec (zero_reg : mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = sign_extend' 64 (mword_of_int 1 : mword 32).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x28 jal fsinit ---- *)
Lemma fkr_fsinit_tgt :
  add_vec (mword_of_int (FR + 0x28) : mword 64)
    (sign_extend' 64 (mword_of_int 7166 : mword 21))
  = (mword_of_int KernelSyms.fsinit : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x2c auipc a5,0x9 / +0x30 addi a5,a5,-1736 : &first, AGAIN ---- *)
(* the release store recomputes the address rather than reusing the a5 the
   acquire load left, because the [jal fsinit] in between clobbers it.  A
   DIFFERENT auipc/addi pair from +0x14/+0x18's (different pc, so a different
   immediate: 2360 sign-extends to -1736, not -1712) reaching the SAME
   symbol, which is exactly the fact worth pinning.  Spelled
   [KernelSyms.first_1] for [fkr_first_addr]'s reason. *)
Lemma fkr_first_addr2 :
  add_vec (add_vec (mword_of_int (FR + 0x2c) : mword 64)
             (auipc_off (mword_of_int 9 : mword 20)))
    (sign_extend' 64 (mword_of_int 2360 : mword 12))
  = (mword_of_int KernelSyms.first_1 : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x3c auipc a5,0x6 / +0x40 addi a5,a5,-1992 : the "/init" literal ---- *)
Lemma fkr_init_path_addr :
  add_vec (add_vec (mword_of_int (FR + 0x3c) : mword 64)
             (auipc_off (mword_of_int 6 : mword 20)))
    (sign_extend' 64 (mword_of_int 2104 : mword 12))
  = (mword_of_int fkr_init_path : mword 64).
Proof. rewrite /fkr_init_path. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x44 sd a5,-48(s0) / +0x48 sd zero,-40(s0) : the argv array ---- *)
(* forkret's frame is six slots and its frame pointer is the ENTRY sp, so
   [s0 = ksp] and the two words of the [(char *[]){"/init", 0}] compound
   literal are the BOTTOM two slots: -48 is [pa_stk ksp 6] (the same address
   the pushed sp names) and -40 is [pa_stk ksp 5].  These are the only two
   lemmas in this file that are not closed -- [ksp] stays symbolic, which is
   the whole point, so [vm_compute] never sees it and the residual closed
   equation is the immediate's sign-extension alone ([stk_push]).
   The [addi a1,s0,-48] at +0x4c that hands kexec the array's BASE carries
   the same immediate 4048, so it re-uses [fkr_argv0_slot] verbatim -- it is
   the same layout fact read as a value rather than as a store target. *)
Lemma fkr_argv0_slot (ksp : mword 64) :
  add_vec ksp (sign_extend' 64 (mword_of_int 4048 : mword 12)) = pa_stk ksp 6.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fkr_argv1_slot (ksp : mword 64) :
  add_vec ksp (sign_extend' 64 (mword_of_int 4056 : mword 12)) = pa_stk ksp 5.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- +0x52 jal kexec ---- *)
Lemma fkr_kexec_tgt :
  add_vec (mword_of_int (FR + 0x52) : mword 64)
    (sign_extend' 64 (mword_of_int 11862 : mword 21))
  = (mword_of_int KernelSyms.kexec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x5e c.li a5,-1 : kexec's failure return ---- *)
(* 63 is -1 in the six-bit [c.li] field; the value the +0x60 [beq] compares
   [p->trapframe->a0] against, in the [mword_of_int (-1)] spelling kexec's
   contract states its error return at, so the comparison is syntactic. *)
Lemma fkr_minus_one :
  add_vec (zero_reg : mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0x60 beq a4,a5, +0x9a : the [a0 == -1] jump to the panic tail ---- *)
(* the target is the [auipc a0,0x5] that materializes "exec"; unlike the
   [c.beqz] at +0x24 the immediate is a plain thirteen-bit field, so no
   [fkr_beq_imm] reassembly is needed. *)
Lemma fkr_beq_tgt :
  add_vec (mword_of_int (FR + 0x60) : mword 64)
    (sign_extend' 64 (mword_of_int 58 : mword 13))
  = mword_of_int (FR + 0x9a).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fkr_beq_align :
  eq_vec (access_vec_dec
            (add_vec (mword_of_int (FR + 0x60) : mword 64)
               (sign_extend' 64 (mword_of_int 58 : mword 13))) 0) ('b"0") = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- +0x9a auipc a0,0x5 / +0x9e addi a0,a0,2018 : the "exec" literal ---- *)
(* the only forward-reaching pair in forkret whose addi immediate is
   POSITIVE, so it is the one place where reading the field as signed and
   reading it as unsigned agree. *)
Lemma fkr_exec_msg_addr :
  add_vec (add_vec (mword_of_int (FR + 0x9a) : mword 64)
             (auipc_off (mword_of_int 5 : mword 20)))
    (sign_extend' 64 (mword_of_int 2018 : mword 12))
  = (mword_of_int fkr_exec_msg : mword 64).
Proof. rewrite /fkr_exec_msg. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- +0xa2 jal panic : the arm's only exit that is not a fall-through ---- *)
(* 2092646 is a NEGATIVE twenty-one-bit displacement (-4506): [panic] sits
   far below forkret in the image. *)
Lemma fkr_panic_tgt :
  add_vec (mword_of_int (FR + 0xa2) : mword 64)
    (sign_extend' 64 (mword_of_int 2092646 : mword 21))
  = (mword_of_int KernelSyms.panic : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

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

(* ===================================================================== *)
(*  THE TWO .rodata LITERALS, AS RESOURCES.                               *)
(*                                                                        *)
(*  Everything above is address arithmetic; these are the CONTENTS the    *)
(*  two computed addresses point at, in the two shapes the two callees    *)
(*  ask for.  Both are layout facts of the same kind as the rest of the   *)
(*  file -- that the six bytes at [fkr_init_path] really spell "/init"    *)
(*  and the five at [fkr_exec_msg] really spell "exec" -- read off        *)
(*  [KernelData.kernel_data] and pinned here rather than in the walk.     *)
(*  (Checked: 0x80007180..85 = 47 105 110 105 116 0, and                  *)
(*  0x80007188..8c = 101 120 101 99 0.)                                   *)
(* ===================================================================== *)

(* The path bytes as a naming FUNCTION, which is what [SpecKexec] indexes
   its [seq]-shaped premise by.  Defined by lookup into [cstring_bytes]
   rather than as six literals, so it cannot drift from the string: change
   the literal and both [fkr_init_path_cstr] and [fkr_init_path_bytes]
   fail, instead of one of them silently agreeing with the old spelling. *)
Definition fkr_init_bytes (j : nat) : bv 8 := cstring_bytes "/init"%string !!! j.

(* ---- kexec's [bb_cstr pfun plen] at plen = 5: the NUL is at index 5 and
       nowhere before it ---- *)
Lemma fkr_init_path_cstr : bb_cstr fkr_init_bytes 5.
Proof.
  split.
  - intros j Hj.
    do 5 (destruct j as [|j];
          [intro Hc; apply bv_eq in Hc; vm_compute in Hc; discriminate |]).
    exfalso. lia.
  - apply bv_eq. vm_compute. reflexivity.
Qed.

(* ---- the image really holds those six bytes at [fkr_init_path] ---- *)
Lemma fkr_init_path_bytes :
  forall j, (j < 6)%nat ->
    KernelData.kernel_data !! (fkr_init_path + Z.of_nat j)%Z = Some (fkr_init_bytes j).
Proof.
  intros j Hj.
  do 6 (destruct j as [|j]; [vm_compute; reflexivity |]).
  exfalso. lia.
Qed.

(* ---- the image really holds "exec" at [fkr_exec_msg] ---- *)
Lemma fkr_exec_msg_bytes :
  forall j b, cstring_bytes "exec"%string !! j = Some b ->
    KernelData.kernel_data !! (fkr_exec_msg + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 5 (destruct j as [|j];
        [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]).
  vm_compute in Hj. discriminate.
Qed.

(* ---- the pure side conditions [panic]'s contract asks about the message:
       it is a "%s" argument ([PkStr]), the string itself contains no
       embedded NUL, and the pointer is not null (printk's [beqz] on the
       %s argument has to fall through).  [ProofIreclaim]'s [irc_msg_fmt]
       in three-conjunct form. ---- *)
Lemma fkr_exec_msg_fmt :
  pk_desc_kind (PkAStr DfracDiscarded "exec"%string) = PkStr /\
  nonul "exec"%string = true /\
  eq_vec (mword_of_int fkr_exec_msg : mword 64) zero_reg = false.
Proof.
  split_and!; [reflexivity | vm_compute; reflexivity
              | rewrite /fkr_exec_msg; vm_compute; reflexivity].
Qed.

Section ForkretRodata.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- +0x4c addi a1,s0,-48 / a0 = the "/init" pointer: the SIX bytes
         kexec's path premise owns, [seq]-indexed.  The real fact is the
         KT0 window [kernel_data] hands out -- .rodata is identity-mapped
         -- and that is this lemma; every tier above it is a weakening of
         this one, so the read off [KernelData.kernel_data] happens once.
         [SpecKexec] needs both tiers of it: the path premise is written
         [↦ₘ[KT1]] but the argument-strings premise carries no bracket at
         all, so it resolves to [Ktier.curktier_default = KT0]. ---- *)
  Lemma fkr_init_path_run0 :
    (kernel_data : iProp Σ) -∗
    ([∗ list] i ∈ seq 0 6,
       pa_add (mword_of_int fkr_init_path : mword 64) i ↦ₘ[KT0]□ fkr_init_bytes i).
  Proof.
    iIntros "Hkd".
    iApply (kernel_data_bytes fkr_init_path 6 fkr_init_bytes _ eq_refl
              ltac:(unfold text_end, fkr_init_path; lia)
              ltac:(vm_compute; discriminate) fkr_init_path_bytes
             with "Hkd").
  Qed.

  (* ---- the same six bytes at the KERNEL tier, which is the shape
         [kexec]'s path premise asks for: byte-wise [mem_ktier_mono] off
         [fkr_init_path_run0], exactly as [ProofCreateParts]'
         [cr_dot_window_kt1] does it. ---- *)
  Lemma fkr_init_path_run :
    (kernel_data : iProp Σ) -∗
    ([∗ list] i ∈ seq 0 6,
       pa_add (mword_of_int fkr_init_path : mword 64) i ↦ₘ[KT1]□ fkr_init_bytes i).
  Proof.
    iIntros "Hkd".
    iDestruct (fkr_init_path_run0 with "Hkd") as "H".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "H".
    iApply (mem_ktier_mono _ KT1 with "H").
  Qed.

  (* ---- +0x9e a0 = the "exec" pointer: the resource [panic]'s contract
         names as [pk_desc_res msg dm] at [dm = PkAStr DfracDiscarded
         "exec"] -- the string points-to plus the two pure conjuncts.
         [.rodata] is [DfracDiscarded] in [kernel_data], which is why the
         description's fraction is [DfracDiscarded] and the whole thing is
         persistent. ---- *)
  Lemma fkr_exec_msg_res :
    (kernel_data : iProp Σ) -∗
    pk_desc_res (mword_of_int fkr_exec_msg : mword 64)
                (PkAStr DfracDiscarded "exec"%string).
  Proof.
    iIntros "Hkd".
    pose proof fkr_exec_msg_fmt as (_ & Hnon & Hnz).
    rewrite /pk_desc_res.
    iSplit; [iPureIntro; exact Hnon |].
    iSplit; [iPureIntro; exact Hnz |].
    iApply (kernel_data_string fkr_exec_msg "exec"%string _ eq_refl
              ltac:(unfold text_end, fkr_exec_msg; lia)
              ltac:(vm_compute; discriminate) fkr_exec_msg_bytes with "Hkd").
  Qed.

End ForkretRodata.

(* ===================================================================== *)
(*  THE ARGUMENT VECTOR forkret BUILDS IN ITS OWN FRAME.                  *)
(*                                                                        *)
(*    kexec("/init", (char *[]){"/init", 0})                              *)
(*                                                                        *)
(*  is a COMPOUND LITERAL, so gcc materialises the two-element vector on   *)
(*  forkret's stack -- at -48(s0) and -40(s0), the bottom two of the six   *)
(*  slots the prologue carved out.  Those slots are otherwise dead (the    *)
(*  frame is 48 bytes for ra/s0/s1 alone), which is why the boot arm can   *)
(*  spend them and still hand [fkr_tail] the run whole.                    *)
(* ===================================================================== *)

(* the vector's two entries, as the function [SpecKexec] indexes by *)
Definition fkr_argv (i : nat) : mword 64 :=
  match i with
  | O => (mword_of_int fkr_init_path : mword 64)
  | S _ => (mword_of_int 0 : mword 64)
  end.

Lemma fkr_argv_nonnull : forall i, (i < 1)%nat -> fkr_argv i <> (mword_of_int 0 : mword 64).
Proof.
  intros i Hi. destruct i; [| lia]. cbn.
  intro Hc. apply bv_eq in Hc. vm_compute in Hc. discriminate.
Qed.

Lemma fkr_argv_null : fkr_argv 1 = (mword_of_int 0 : mword 64).
Proof. reflexivity. Qed.

(* ...and where the two entries LIVE: [av] is [pa_stk ksp 6], and the
   contract indexes the vector by [pa_add av (8 * i)].  Slot 5 sits eight
   bytes ABOVE slot 6 -- [pa_stk] counts DOWN from the frame top -- so the
   second entry is exactly the second stack word. *)
Lemma fkr_argv_next (ksp : mword 64) : pa_add (pa_stk ksp 6) (8 * 1) = pa_stk ksp 5.
Proof.
  rewrite /pa_add /pa_stk InstrBytes.avi_assoc. f_equal; lia.
Qed.

Lemma fkr_argv_here (ksp : mword 64) : pa_add (pa_stk ksp 6) (8 * 0) = pa_stk ksp 6.
Proof. exact (pa_add_0 _). Qed.
