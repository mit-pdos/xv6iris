(* KernelText.v -- the kernel instruction-image resource [kernel_text] and the
   generic fetch-window / [instr_bytes] introduction lemmas.

   These are shared fetch plumbing needed by EVERY kernel-code WP proof (S-mode
   leaves, push/pop_off, acquire/release, kalloc/kfree, userret, ...), so they
   live in this lightweight base rather than in [WpEntryNew] (the _entry BOOT
   proof, which additionally pulls in the whole M-mode GPR/decode WP stack).
   Importing this file gives the [kernel_text] image + window lemmas without
   the boot-sequence dependency. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
From Kernel Require KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

Section KernelText.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ================================================================= *)
  (*  The kernel TEXT image + per-instruction [instr] constructors.    *)
  (* ================================================================= *)

  (* The image is the dumper's PER-BYTE map [KernelInstrs.kernel_bytes] (byte
     address -> byte value), each byte resident at its physical address.  The
     code points-to facts are DfracDiscarded (`↦ₘ□`), hence persistent and
     duplicable: a fetch window can be extracted while [kernel_text] stays
     intact — no borrow/return. *)
  Definition kernel_text : iProp Σ :=
    ([∗ map] a↦b ∈ KernelInstrs.kernel_bytes, (mword_of_int a : Arch.pa) ↦ₘ□ b)%I.

  Global Instance kernel_text_persistent : Persistent kernel_text.
  Proof. apply _. Qed.

  (* Keep typeclass resolution (Frame/IntoWand/... in iApply/iIntros/iFrame)
     from unfolding [kernel_text] into its 23K-entry [big_sepM] over
     [kernel_bytes] -- otherwise every chunk's [iApply (... with "Htext")]
     pays a huge TC search (cf. the [kernel_bytes] opacity fix).  Unification
     can still see through it where a proof genuinely needs the [big_sepM]. *)
  Global Typeclasses Opaque kernel_text.

  (* [pa_add] over a literal address, without the [fetch_pa] wrapper (the
     [instr_bytes] footprints are phrased directly over the instruction
     address; virtual = physical in M-mode). *)
  Lemma pa_add_mword (A : Z) (j : nat) :
    pa_add (mword_of_int A : Arch.pa) j = mword_of_int (A + Z.of_nat j).
  Proof. unfold pa_add. apply avi_mword. Qed.

  (* [kernel_window] in [instr_bytes]' address form: the [W]-byte window of
     the word [w] at the literal byte address [A] = [pc], as [pa_add pc j]. *)
  Lemma kernel_window_pc {wd : Z} (A : Z) (w : mword wd) (W : nat) (pc : mword 64) :
    pc = mword_of_int A ->
    (forall j, (j < W)%nat ->
       KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_text -∗
    ([∗ list] j ∈ seq 0 W, (pa_add pc j) ↦ₘ□ nth_byte w j).
  Proof.
    iIntros (-> Hbytes) "#Ht". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (nth_byte w k) with "Ht").
    apply Hbytes. exact Hlt.
  Qed.

  (* ---- generic [instr_bytes] introduction (base / 4-aligned RVC / RVC) ---- *)
  Lemma instr_bytes_base (pc : mword 64) (w : mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₘ□ nth_byte w j) -∗
    instr_bytes pc (F_Base w).
  Proof.
    iIntros (H2 Hn) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hn|].
    iExact "Hw".
  Qed.

  Lemma instr_bytes_rvc4 (pc : mword 64) (h : mword 16) (w : mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC h = true ->
    subrange_vec_dec w 15 0 = h ->
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₘ□ nth_byte w j) -∗
    instr_bytes pc (F_RVC h).
  Proof.
    iIntros (H2 H4 Hr Hs) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    rewrite H4.
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hr|].
    iExists w. iSplitR; [iPureIntro; exact Hs|]. iExact "Hw".
  Qed.

  Lemma instr_bytes_rvc2 (pc : mword 64) (h : mword 16) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    ([∗ list] j ∈ seq 0 2, (pa_add pc j) ↦ₘ□ nth_byte h j) -∗
    instr_bytes pc (F_RVC h).
  Proof.
    iIntros (H2 H4 Hr) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    rewrite H4.
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hr|].
    iExact "Hw".
  Qed.

End KernelText.
