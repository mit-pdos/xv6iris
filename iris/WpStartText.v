(* Threading infrastructure for the start() chain: decompose [kernel_text] to
   expose start's instruction byte-windows (kernel_instrs idx 30..47), and the
   E_X lemmas converting each [kinstr_bytes] to the per-opcode WP window form.
   Leaf file (imports KernelBoot, imported by nothing) so it is safe to edit.
   Start's WPs use tight windows (seq 0 4 for 32-bit, seq 0 2 for RVC) with NO
   fetch-window overlap, so no split/join regrouping is needed (unlike _entry). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr KernelBoot.
Local Open Scope Z_scope.

Section StartText.
  Context `{!riscvGS Σ}.

  Definition skinstr (i : nat) : KernelInstrs.kinstr :=
    nth i KernelInstrs.kernel_instrs kdefault.

  (* drop 30 kernel_instrs = the 18 start instructions ++ drop 48.  Proved by
     splitting off [take 18 (drop 30)] (a concrete 18-element list = the start
     instrs) and folding [drop 18 (drop 30) = drop 48]. *)
  Lemma start_instrs_decomp :
    KernelInstrs.kernel_instrs =
      take 30 KernelInstrs.kernel_instrs ++
      (skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 ::
       skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 ::
       skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 ::
       skinstr 45 :: skinstr 46 :: skinstr 47 ::
       drop 48 KernelInstrs.kernel_instrs).
  Proof.
    rewrite -{1}(take_drop 30 KernelInstrs.kernel_instrs).
    rewrite -{1}(take_drop 18 (drop 30 KernelInstrs.kernel_instrs)).
    rewrite drop_drop.
    replace (take 18 (drop 30 KernelInstrs.kernel_instrs))
      with (skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 ::
            skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 ::
            skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 ::
            skinstr 45 :: skinstr 46 :: skinstr 47 :: nil)
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* The folded prefix (idx 0..29: _entry + timerinit) and tail (idx 48..). *)
  Definition start_prefix : iProp Σ :=
    ([∗ list] k ∈ take 30 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Definition start_tail : iProp Σ :=
    ([∗ list] k ∈ drop 48 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.

  Lemma start_text_split :
    kernel_text ⊢
      start_prefix ∗
      kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31) ∗ kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗ kinstr_bytes (skinstr 34) ∗ kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗ kinstr_bytes (skinstr 37) ∗ kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗ kinstr_bytes (skinstr 40) ∗ kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗ kinstr_bytes (skinstr 43) ∗ kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗ kinstr_bytes (skinstr 46) ∗ kinstr_bytes (skinstr 47) ∗
      start_tail.
  Proof.
    rewrite /kernel_text {1}start_instrs_decomp big_sepL_app.
    rewrite 18!big_sepL_cons -/start_prefix -/start_tail.
    iIntros "($ & H)". iFrame.
  Qed.

  Lemma start_text_combine :
    start_prefix ∗
      kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31) ∗ kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗ kinstr_bytes (skinstr 34) ∗ kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗ kinstr_bytes (skinstr 37) ∗ kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗ kinstr_bytes (skinstr 40) ∗ kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗ kinstr_bytes (skinstr 43) ∗ kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗ kinstr_bytes (skinstr 46) ∗ kinstr_bytes (skinstr 47) ∗
      start_tail
    ⊢ kernel_text.
  Proof.
    rewrite /kernel_text {1}start_instrs_decomp big_sepL_app.
    rewrite 18!big_sepL_cons -/start_prefix -/start_tail.
    iIntros "($ & H)". iFrame.
  Qed.

  (* ---- E_X: convert kinstr_bytes (skinstr N) to the per-opcode WP window form.
     32-bit: seq 0 4, w = enc:mword 32, pc = addr.  Example for idx 34 (csrr
     mstatus, addr 0x80000060, enc 0x300027f3). ---- *)
  Definition swin32 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.

  Lemma E_s34 : kinstr_bytes (skinstr 34) = swin32 0x80000060 0x300027f3.
  Proof.
    rewrite /kinstr_bytes /swin32.
    replace (KernelInstrs.ki_width (skinstr 34)) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr (skinstr 34)) with (0x80000060)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc (skinstr 34)) with (0x300027f3)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* RVC: seq 0 2, w16 = enc:mword 16.  Example for idx 30 (c.addi16sp, addr
     0x80000058, enc 0x1141).  Needs nth_byte(enc:mword 32) = nth_byte(enc:mword 16)
     for j<2 (concrete enc -> vm_compute). *)
  Definition swin16 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.

  Lemma E_s30 : kinstr_bytes (skinstr 30) = swin16 0x80000058 0x1141.
  Proof.
    rewrite /kinstr_bytes /swin16.
    replace (KernelInstrs.ki_width (skinstr 30)) with 16%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr (skinstr 30)) with (0x80000058)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc (skinstr 30)) with (0x1141)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* Generic byte-window conversion: ONE lemma instead of 55 hand-written E_X.
     The three field equalities are each discharged by [vm_compute; reflexivity]
     at the call site.  width is 32 or 16; the window is seq 0 (width/8). *)
  Lemma E_skinstr (i : nat) (addr enc : Z) (width : nat) :
    KernelInstrs.ki_addr (skinstr i) = addr ->
    KernelInstrs.ki_enc (skinstr i) = enc ->
    KernelInstrs.ki_width (skinstr i) = width ->
    kinstr_bytes (skinstr i) =
      ([∗ list] j ∈ seq 0 (width / 8),
        (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.
  Proof. intros <- <- <-. reflexivity. Qed.

  (* Demo: recover the 32-bit and RVC windows via the generic lemma. *)
  Lemma E_s34' : kinstr_bytes (skinstr 34) = swin32 0x80000060 0x300027f3.
  Proof.
    rewrite (E_skinstr 34 0x80000060 0x300027f3 32%nat
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)).
    reflexivity.
  Qed.

  Lemma chain_instrs_decomp :
    KernelInstrs.kernel_instrs =
      take 9 KernelInstrs.kernel_instrs ++
      (skinstr 9 :: skinstr 10 :: skinstr 11 :: skinstr 12 :: skinstr 13 :: skinstr 14 :: skinstr 15 :: skinstr 16 :: skinstr 17 :: skinstr 18 :: skinstr 19 :: skinstr 20 :: skinstr 21 :: skinstr 22 :: skinstr 23 :: skinstr 24 :: skinstr 25 :: skinstr 26 :: skinstr 27 :: skinstr 28 :: skinstr 29 :: skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 :: skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 :: skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 :: skinstr 45 :: skinstr 46 :: skinstr 47 :: skinstr 48 :: skinstr 49 :: skinstr 50 :: skinstr 51 :: skinstr 52 :: skinstr 53 :: skinstr 54 :: skinstr 55 :: skinstr 56 :: skinstr 57 :: skinstr 58 :: skinstr 59 :: skinstr 60 :: skinstr 61 :: skinstr 62 :: skinstr 63 ::
       drop 64 KernelInstrs.kernel_instrs).
  Proof.
    rewrite -{1}(take_drop 9 KernelInstrs.kernel_instrs).
    rewrite -{1}(take_drop 55 (drop 9 KernelInstrs.kernel_instrs)) drop_drop.
    replace (take 55 (drop 9 KernelInstrs.kernel_instrs))
      with (skinstr 9 :: skinstr 10 :: skinstr 11 :: skinstr 12 :: skinstr 13 :: skinstr 14 :: skinstr 15 :: skinstr 16 :: skinstr 17 :: skinstr 18 :: skinstr 19 :: skinstr 20 :: skinstr 21 :: skinstr 22 :: skinstr 23 :: skinstr 24 :: skinstr 25 :: skinstr 26 :: skinstr 27 :: skinstr 28 :: skinstr 29 :: skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 :: skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 :: skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 :: skinstr 45 :: skinstr 46 :: skinstr 47 :: skinstr 48 :: skinstr 49 :: skinstr 50 :: skinstr 51 :: skinstr 52 :: skinstr 53 :: skinstr 54 :: skinstr 55 :: skinstr 56 :: skinstr 57 :: skinstr 58 :: skinstr 59 :: skinstr 60 :: skinstr 61 :: skinstr 62 :: skinstr 63 :: nil)
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Definition chain_prefix : iProp Σ := ([∗ list] k ∈ take 9 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Definition chain_tail : iProp Σ := ([∗ list] k ∈ drop 64 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
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
      kinstr_bytes (skinstr 63) ∗
      chain_tail.
  Proof.
    rewrite /kernel_text {1}chain_instrs_decomp big_sepL_app.
    rewrite 55!big_sepL_cons -/chain_prefix -/chain_tail.
    iIntros "($ & H)". iFrame.
  Qed.

End StartText.
