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
  Definition skinstr (i : nat) : kinstr := nth i kernel_instrs kdefault.

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
  Lemma skinstr_get_aux (i : nat) :
    (forall j, (j < ki_width (skinstr i) / 8)%nat ->
       kernel_bytes !! (ki_addr (skinstr i) + Z.of_nat j)%Z
         = Some (nth_byte (mword_of_int (ki_enc (skinstr i)) : mword 32) j)) ->
    kernel_text -∗ kinstr_bytes (skinstr i).
  Proof.
    intros Hb. iIntros "H". unfold kinstr_bytes.
    iApply (kernel_window (ki_addr (skinstr i)) (mword_of_int (ki_enc (skinstr i)) : mword 32)
              (ki_width (skinstr i) / 8) Hb with "H").
  Qed.

  Ltac sg i :=
    let Hb := fresh "Hb" in
    assert (Hb : forall j, (j < ki_width (skinstr i) / 8)%nat ->
              kernel_bytes !! (ki_addr (skinstr i) + Z.of_nat j)%Z
                = Some (nth_byte (mword_of_int (ki_enc (skinstr i)) : mword 32) j))
      by (intros j Hj; vm_compute in Hj;
          do 4 (destruct j as [|j];
            [first [vm_compute; f_equal; apply bv_eq; reflexivity | exfalso; lia]|]); lia);
    iApply (skinstr_get_aux i Hb with "H").

  Definition chain_prefix : iProp Σ := emp%I.
  Definition chain_tail : iProp Σ := kernel_text.
  Definition start_prefix : iProp Σ := emp%I.
  Definition start_tail : iProp Σ := kernel_text.

  Lemma chain_text_split :
    kernel_text ⊢ chain_prefix ∗
      kinstr_bytes (skinstr 9) ∗
      kinstr_bytes (skinstr 10) ∗
      kinstr_bytes (skinstr 11) ∗
      kinstr_bytes (skinstr 12) ∗
      kinstr_bytes (skinstr 13) ∗
      kinstr_bytes (skinstr 14) ∗
      kinstr_bytes (skinstr 15) ∗
      kinstr_bytes (skinstr 16) ∗
      kinstr_bytes (skinstr 17) ∗
      kinstr_bytes (skinstr 18) ∗
      kinstr_bytes (skinstr 19) ∗
      kinstr_bytes (skinstr 20) ∗
      kinstr_bytes (skinstr 21) ∗
      kinstr_bytes (skinstr 22) ∗
      kinstr_bytes (skinstr 23) ∗
      kinstr_bytes (skinstr 24) ∗
      kinstr_bytes (skinstr 25) ∗
      kinstr_bytes (skinstr 26) ∗
      kinstr_bytes (skinstr 27) ∗
      kinstr_bytes (skinstr 28) ∗
      kinstr_bytes (skinstr 29) ∗
      kinstr_bytes (skinstr 30) ∗
      kinstr_bytes (skinstr 31) ∗
      kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗
      kinstr_bytes (skinstr 34) ∗
      kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗
      kinstr_bytes (skinstr 37) ∗
      kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗
      kinstr_bytes (skinstr 40) ∗
      kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗
      kinstr_bytes (skinstr 43) ∗
      kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗
      kinstr_bytes (skinstr 46) ∗
      kinstr_bytes (skinstr 47) ∗
      kinstr_bytes (skinstr 48) ∗
      kinstr_bytes (skinstr 49) ∗
      kinstr_bytes (skinstr 50) ∗
      kinstr_bytes (skinstr 51) ∗
      kinstr_bytes (skinstr 52) ∗
      kinstr_bytes (skinstr 53) ∗
      kinstr_bytes (skinstr 54) ∗
      kinstr_bytes (skinstr 55) ∗
      kinstr_bytes (skinstr 56) ∗
      kinstr_bytes (skinstr 57) ∗
      kinstr_bytes (skinstr 58) ∗
      kinstr_bytes (skinstr 59) ∗
      kinstr_bytes (skinstr 60) ∗
      kinstr_bytes (skinstr 61) ∗
      kinstr_bytes (skinstr 62) ∗
      kinstr_bytes (skinstr 63) ∗ chain_tail.
  Proof.
    iIntros "#H". rewrite /chain_prefix /chain_tail. iSplitR; first done.
    iSplitR; [sg 9%nat |
    iSplitR; [sg 10%nat |
    iSplitR; [sg 11%nat |
    iSplitR; [sg 12%nat |
    iSplitR; [sg 13%nat |
    iSplitR; [sg 14%nat |
    iSplitR; [sg 15%nat |
    iSplitR; [sg 16%nat |
    iSplitR; [sg 17%nat |
    iSplitR; [sg 18%nat |
    iSplitR; [sg 19%nat |
    iSplitR; [sg 20%nat |
    iSplitR; [sg 21%nat |
    iSplitR; [sg 22%nat |
    iSplitR; [sg 23%nat |
    iSplitR; [sg 24%nat |
    iSplitR; [sg 25%nat |
    iSplitR; [sg 26%nat |
    iSplitR; [sg 27%nat |
    iSplitR; [sg 28%nat |
    iSplitR; [sg 29%nat |
    iSplitR; [sg 30%nat |
    iSplitR; [sg 31%nat |
    iSplitR; [sg 32%nat |
    iSplitR; [sg 33%nat |
    iSplitR; [sg 34%nat |
    iSplitR; [sg 35%nat |
    iSplitR; [sg 36%nat |
    iSplitR; [sg 37%nat |
    iSplitR; [sg 38%nat |
    iSplitR; [sg 39%nat |
    iSplitR; [sg 40%nat |
    iSplitR; [sg 41%nat |
    iSplitR; [sg 42%nat |
    iSplitR; [sg 43%nat |
    iSplitR; [sg 44%nat |
    iSplitR; [sg 45%nat |
    iSplitR; [sg 46%nat |
    iSplitR; [sg 47%nat |
    iSplitR; [sg 48%nat |
    iSplitR; [sg 49%nat |
    iSplitR; [sg 50%nat |
    iSplitR; [sg 51%nat |
    iSplitR; [sg 52%nat |
    iSplitR; [sg 53%nat |
    iSplitR; [sg 54%nat |
    iSplitR; [sg 55%nat |
    iSplitR; [sg 56%nat |
    iSplitR; [sg 57%nat |
    iSplitR; [sg 58%nat |
    iSplitR; [sg 59%nat |
    iSplitR; [sg 60%nat |
    iSplitR; [sg 61%nat |
    iSplitR; [sg 62%nat |
    iSplitR; [sg 63%nat |
    iApply "H"
    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  Qed.
  Lemma chain_text_combine :
    chain_prefix ∗ kinstr_bytes (skinstr 9) ∗
      kinstr_bytes (skinstr 10) ∗
      kinstr_bytes (skinstr 11) ∗
      kinstr_bytes (skinstr 12) ∗
      kinstr_bytes (skinstr 13) ∗
      kinstr_bytes (skinstr 14) ∗
      kinstr_bytes (skinstr 15) ∗
      kinstr_bytes (skinstr 16) ∗
      kinstr_bytes (skinstr 17) ∗
      kinstr_bytes (skinstr 18) ∗
      kinstr_bytes (skinstr 19) ∗
      kinstr_bytes (skinstr 20) ∗
      kinstr_bytes (skinstr 21) ∗
      kinstr_bytes (skinstr 22) ∗
      kinstr_bytes (skinstr 23) ∗
      kinstr_bytes (skinstr 24) ∗
      kinstr_bytes (skinstr 25) ∗
      kinstr_bytes (skinstr 26) ∗
      kinstr_bytes (skinstr 27) ∗
      kinstr_bytes (skinstr 28) ∗
      kinstr_bytes (skinstr 29) ∗
      kinstr_bytes (skinstr 30) ∗
      kinstr_bytes (skinstr 31) ∗
      kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗
      kinstr_bytes (skinstr 34) ∗
      kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗
      kinstr_bytes (skinstr 37) ∗
      kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗
      kinstr_bytes (skinstr 40) ∗
      kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗
      kinstr_bytes (skinstr 43) ∗
      kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗
      kinstr_bytes (skinstr 46) ∗
      kinstr_bytes (skinstr 47) ∗
      kinstr_bytes (skinstr 48) ∗
      kinstr_bytes (skinstr 49) ∗
      kinstr_bytes (skinstr 50) ∗
      kinstr_bytes (skinstr 51) ∗
      kinstr_bytes (skinstr 52) ∗
      kinstr_bytes (skinstr 53) ∗
      kinstr_bytes (skinstr 54) ∗
      kinstr_bytes (skinstr 55) ∗
      kinstr_bytes (skinstr 56) ∗
      kinstr_bytes (skinstr 57) ∗
      kinstr_bytes (skinstr 58) ∗
      kinstr_bytes (skinstr 59) ∗
      kinstr_bytes (skinstr 60) ∗
      kinstr_bytes (skinstr 61) ∗
      kinstr_bytes (skinstr 62) ∗
      kinstr_bytes (skinstr 63) ∗ chain_tail ⊢ kernel_text.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H)". iApply "H". Qed.

  Lemma start_text_split :
    kernel_text ⊢ start_prefix ∗
      kinstr_bytes (skinstr 30) ∗
      kinstr_bytes (skinstr 31) ∗
      kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗
      kinstr_bytes (skinstr 34) ∗
      kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗
      kinstr_bytes (skinstr 37) ∗
      kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗
      kinstr_bytes (skinstr 40) ∗
      kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗
      kinstr_bytes (skinstr 43) ∗
      kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗
      kinstr_bytes (skinstr 46) ∗
      kinstr_bytes (skinstr 47) ∗ start_tail.
  Proof.
    iIntros "#H". rewrite /start_prefix /start_tail. iSplitR; first done.
    iSplitR; [sg 30%nat |
    iSplitR; [sg 31%nat |
    iSplitR; [sg 32%nat |
    iSplitR; [sg 33%nat |
    iSplitR; [sg 34%nat |
    iSplitR; [sg 35%nat |
    iSplitR; [sg 36%nat |
    iSplitR; [sg 37%nat |
    iSplitR; [sg 38%nat |
    iSplitR; [sg 39%nat |
    iSplitR; [sg 40%nat |
    iSplitR; [sg 41%nat |
    iSplitR; [sg 42%nat |
    iSplitR; [sg 43%nat |
    iSplitR; [sg 44%nat |
    iSplitR; [sg 45%nat |
    iSplitR; [sg 46%nat |
    iSplitR; [sg 47%nat |
    iApply "H"
    ]]]]]]]]]]]]]]]]]].
  Qed.
  Lemma start_text_combine :
    start_prefix ∗ kinstr_bytes (skinstr 30) ∗
      kinstr_bytes (skinstr 31) ∗
      kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗
      kinstr_bytes (skinstr 34) ∗
      kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗
      kinstr_bytes (skinstr 37) ∗
      kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗
      kinstr_bytes (skinstr 40) ∗
      kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗
      kinstr_bytes (skinstr 43) ∗
      kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗
      kinstr_bytes (skinstr 46) ∗
      kinstr_bytes (skinstr 47) ∗ start_tail ⊢ kernel_text.
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H)". iApply "H". Qed.

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
