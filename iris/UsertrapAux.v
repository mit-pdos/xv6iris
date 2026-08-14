(* UsertrapAux.v -- the pure/definitional layer under usertrap's proof: the
   two format strings its unexpected-scause arm passes to printk.

       printk("usertrap(): unexpected scause 0x%lx pid=%d\n",
              r_scause(), p->pid);
       printk("            sepc=0x%lx stval=0x%lx\n", r_sepc(), r_stval());

   Both are ordinary .rodata literals reached by an auipc/addi pair, so all
   this file does is name them, name their addresses, and mint the persistent
   [↦ₛ□] out of [KernelDataInv.kernel_data].  It is [ProcdumpAux.v] §3
   verbatim in shape, and for the same recorded reason: the byte premises are
   pure lemmas passed to [kernel_data_string] BY NAME, because an inline
   [ltac:(...)] byte premise is re-elaborated by the proofmode without the
   [Qed] vm-seal (optimization.md, ProofArgraw's [ar_tbl_bytes]).

   THE VARARGS COST NOTHING, which is the one thing worth knowing before
   reading the arm.  Every conversion in both strings is [%lx] or [%d], i.e.
   [PkNum], and [SpecPrintk.pk_desc_res v PkANum = True] -- so the big-op of
   argument resources printk's contract takes is trivially satisfiable and
   the arm owes only the format string itself.  Had either string carried a
   [%s] the arm would have had to own a second string, which is what makes
   procdump's version of this file four times the size. *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import KernelDataInv.
Require Import PrintkFmt.
Require Import SpecPrintk.    (* [pk_arg_desc] / [pk_desc_kind] *)
From Kernel Require KernelSyms.
From Kernel Require KernelData.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1.  THE TWO LITERALS                                                   *)
(* ===================================================================== *)

(* the addresses the two auipc/addi pairs compute: +0x5c/+0x60 lands on
   0x800072b0 and +0x70/+0x74 on 0x800072e0.  (0x80007290, the panic string,
   is deliberately absent: its arm is REFUTED -- ProofUsertrapParts.v.)
   THESE MOVE WITH EVERY IMAGE RELAYOUT and nothing but this file's own
   [kernel_data_string] obligations will notice, so they are the first thing to
   re-derive after a bump: `awk '/<usertrap>:/,/^$/' xv6-riscv/kernel/kernel.asm
   | grep 'addi.*a0,a0'` prints them as objdump's `#` comments -- but ONLY if
   the local xv6-riscv checkout is at the new $(XV6_REV); against a stale one
   it silently prints the OLD pair.  Deriving them from the tracked image
   instead needs no toolchain: the auipc is `mword_of_int 5` in CodeUsertrap.v,
   so the address is (usertrap + off - 4) + (5 << 12) + sext12(imm).
   (xv6 9dd28f5e had them at 0x80007290 / 0x800072c0, 0024d4b at
   0x800072a8 / 0x800072d8.) *)
Definition ut_fmt1_a : Z := 0x800072b0.
Definition ut_fmt2_a : Z := 0x800072e0.

Definition ut_nl : string := String (ascii_of_nat 10) EmptyString.

Definition ut_fmt1 : string :=
  String.append "usertrap(): unexpected scause 0x%lx pid=%d" ut_nl.
Definition ut_fmt2 : string :=
  String.append "            sepc=0x%lx stval=0x%lx" ut_nl.

Definition ut_fmt1_p : mword 64 := mword_of_int ut_fmt1_a.
Definition ut_fmt2_p : mword 64 := mword_of_int ut_fmt2_a.

(* the vararg descriptors, one list per call.  Both are all-[PkANum]; see the
   header for why that is the whole of the argument obligation. *)
Definition ut_fmt1_descs : list pk_arg_desc := [PkANum; PkANum].
Definition ut_fmt2_descs : list pk_arg_desc := [PkANum; PkANum].

(* ===================================================================== *)
(* 2.  WHAT printk HAS TO BE TOLD ABOUT THEM                              *)
(* ===================================================================== *)

Lemma ut_fmt1_nonul : nonul ut_fmt1 = true. Proof. vm_compute; reflexivity. Qed.
Lemma ut_fmt2_nonul : nonul ut_fmt2 = true. Proof. vm_compute; reflexivity. Qed.

Lemma ut_fmt1_kinds : pk_kinds ut_fmt1 = map pk_desc_kind ut_fmt1_descs.
Proof. vm_compute; reflexivity. Qed.
Lemma ut_fmt2_kinds : pk_kinds ut_fmt2 = map pk_desc_kind ut_fmt2_descs.
Proof. vm_compute; reflexivity. Qed.

Lemma ut_fmt1_len : (Z.of_nat (String.length ut_fmt1) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.
Lemma ut_fmt2_len : (Z.of_nat (String.length ut_fmt2) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.

Lemma ut_fmt1_ndescs : (length ut_fmt1_descs <= 7)%nat.
Proof. unfold ut_fmt1_descs. cbn [length]. lia. Qed.
Lemma ut_fmt2_ndescs : (length ut_fmt2_descs <= 7)%nat.
Proof. unfold ut_fmt2_descs. cbn [length]. lia. Qed.

(* ===================================================================== *)
(* 3.  READING THEM OUT OF THE IMAGE                                      *)
(* ===================================================================== *)

Lemma ut_fmt1_bytes :
  forall j b, cstring_bytes ut_fmt1 !! j = Some b ->
    KernelData.kernel_data !! (ut_fmt1_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 44 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Lemma ut_fmt2_bytes :
  forall j b, cstring_bytes ut_fmt2 !! j = Some b ->
    KernelData.kernel_data !! (ut_fmt2_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 36 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section UsertrapData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma ut_fmt1_str : (kernel_data : iProp Σ) -∗ ut_fmt1_p ↦ₛ□ ut_fmt1.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string ut_fmt1_a ut_fmt1 _ eq_refl
              ltac:(unfold text_end, ut_fmt1_a; lia) ut_fmt1_bytes with "Hd").
  Qed.

  Lemma ut_fmt2_str : (kernel_data : iProp Σ) -∗ ut_fmt2_p ↦ₛ□ ut_fmt2.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string ut_fmt2_a ut_fmt2 _ eq_refl
              ltac:(unfold text_end, ut_fmt2_a; lia) ut_fmt2_bytes with "Hd").
  Qed.

  (* the argument big-op printk takes.  Both lists are all-[PkANum] and
     [pk_desc_res _ PkANum = True], so this is free at ANY register map --
     which is what makes the two calls' argument obligation a one-liner
     instead of procdump's descriptor kit. *)
  Lemma ut_fmt1_descs_res (m : regfile) :
    ⊢ ([∗ list] j ↦ d ∈ ut_fmt1_descs, pk_desc_res (pk_vararg m j) d).
  Proof. rewrite /ut_fmt1_descs /pk_desc_res. cbn [big_opL]. auto. Qed.

  Lemma ut_fmt2_descs_res (m : regfile) :
    ⊢ ([∗ list] j ↦ d ∈ ut_fmt2_descs, pk_desc_res (pk_vararg m j) d).
  Proof. rewrite /ut_fmt2_descs /pk_desc_res. cbn [big_opL]. auto. Qed.

End UsertrapData.
