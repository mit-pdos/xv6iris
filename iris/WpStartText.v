(* WpStartText.v -- per-byte foundation for the start/timerinit chunk proofs.
   Provides the skinstr/kinstr_bytes/E_skinstr/chain_text_split INTERFACE that the
   (unchanged) chunk lemmas use, but reimplemented on the PER-BYTE image:
   - kinstr_bytes is the per-opcode fetch-window form (persistent ↦ₘ□);
   - skinstr i = the i-th instruction's (addr,width,enc) DECODE METADATA
     (KernelInstrs.kernel_instrs); the bytes themselves are extracted per-byte
     from kernel_text via KernelBoot.kernel_window;
   - chain_text_split / start_text_split extract the windows from the PERSISTENT
     kernel_text (kept as chain_tail), so there is no list big_sepL / no reassembly. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpGprCsrrAny WpAlu2 WpGprCsrw WpGprAddi WpGprLui KernelBoot.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.

Section StartText.
  Context `{!riscvGS Σ}.

  Definition kdefault : kinstr := MkKInstr 0 0 0.
  Definition skinstr (i : nat) : kinstr := default kdefault (kernel_instrs !! Z.of_nat i).

  (* per-opcode fetch-window of one instruction (per-byte addresses, persistent). *)
  Definition kinstr_bytes (k : kinstr) : iProp Σ :=
    ([∗ list] j ∈ seq 0 (ki_width k / 8),
      (pa_add (fetch_pa (mword_of_int (ki_addr k))) j)
        ↦ₘ□ nth_byte (mword_of_int (ki_enc k) : mword 32) j)%I.
  Global Instance kinstr_bytes_persistent k : Persistent (kinstr_bytes k).
  Proof. apply _. Qed.

  Definition instr_byte_pairs (k : kinstr) : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa (mword_of_int (ki_addr k))) j,
                   nth_byte (mword_of_int (ki_enc k) : mword 32) j))
        (seq 0 (ki_width k / 8)).
  Lemma kinstr_bytes_pairs (k : kinstr) :
    kinstr_bytes k ⊣⊢ ([∗ list] ab ∈ instr_byte_pairs k, ab.1 ↦ₘ□ ab.2).
  Proof. rewrite /kinstr_bytes /instr_byte_pairs big_sepL_fmap. done. Qed.
  Lemma win_pairs (pc : mword 64) (w : mword 32) (n : nat) :
    ([∗ list] j ∈ seq 0 n, (pa_add (fetch_pa pc) j) ↦ₘ□ nth_byte w j) ⊣⊢
    ([∗ list] ab ∈ map (fun j => (pa_add (fetch_pa pc) j, nth_byte w j)) (seq 0 n),
       ab.1 ↦ₘ□ ab.2).
  Proof. rewrite big_sepL_fmap. done. Qed.

  (* kinstr_bytes IS the window form, so E_skinstr is reflexivity given the fields. *)
  Lemma E_skinstr (i : nat) (addr enc : Z) (width : nat) :
    ki_addr (skinstr i) = addr -> ki_enc (skinstr i) = enc -> ki_width (skinstr i) = width ->
    kinstr_bytes (skinstr i) =
      ([∗ list] j ∈ seq 0 (width / 8),
        (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ□ nth_byte (mword_of_int enc : mword 32) j)%I.
  Proof. intros <- <- <-. reflexivity. Qed.

  (* extract one instruction's window from the persistent per-byte kernel_text. *)
  Lemma skinstr_get_aux (i : kinstr) :
    (forall j, (j < ki_width i / 8)%nat ->
       kernel_bytes !! (ki_addr i + Z.of_nat j)%Z
         = Some (nth_byte (mword_of_int (ki_enc i) : mword 32) j)) ->
    kernel_text -∗ kinstr_bytes i.
  Proof.
    intros Hb. iIntros "H". unfold kinstr_bytes.
    iApply (kernel_window (ki_addr i) (mword_of_int (ki_enc i) : mword 32)
              (ki_width i / 8) Hb with "H").
  Qed.

  Ltac sg i :=
    let Hb := fresh "Hb" in
    assert (Hb : forall j, (j < ki_width (skinstr i) / 8)%nat ->
              kernel_bytes !! (ki_addr (skinstr i) + Z.of_nat j)%Z
                = Some (nth_byte (mword_of_int (ki_enc (skinstr i)) : mword 32) j))
      by (intros j Hj; vm_compute in Hj;
          do 4 (destruct j as [|j];
            [first [vm_compute; f_equal; apply bv_eq; reflexivity | exfalso; lia]|]); lia);
    iApply (skinstr_get_aux (skinstr i) Hb with "H").

  (* No chain_text_split/start_text_split: extract each window per-instruction
     at point of use with the [sg] tactic (kernel_text is duplicable). *)

  Definition swin32 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ□ nth_byte (mword_of_int enc : mword 32) j)%I.
  Definition swin16 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ□ nth_byte (mword_of_int enc : mword 32) j)%I.

  Ltac walk s HmisaC :=
    first
    [ rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) s)); cbn match
    | match goal with
      | |- context[Defs.bind (Defs.and_boolM (currentlyEnabled Ext_Zca) (returnM ?pat)) _] =>
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_cezca_false s pat HmisaC ltac:(vm_compute; reflexivity)));
          cbn match
      end
    | match goal with |- context[if ?g then _ else returnM None] =>
        replace g with false by (vm_compute; reflexivity) end; cbn match
    | match goal with |- context[if ?g then _ else _] =>
        replace g with false by (vm_compute; reflexivity) end; cbn match ].

End StartText.
