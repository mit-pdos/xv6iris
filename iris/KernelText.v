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
(* for [MISA_C], which [close_dec] reads misa bits out of *)
Require Import RiscvFetchExec.
From Kernel Require KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  The 4-byte fetch window of the kernel image, as a computed word.      *)
(* ===================================================================== *)

(* [kb_word_at A] is the 32-bit little-endian word formed by the image bytes
   at A..A+3 -- the fetch window at [A], whatever [A]'s 4-alignment (see
   [instr_bytes_rvc_any]).  Computing it from the image is what lets a call
   site name an instruction by its address alone, with no hand-written window
   word.  Bytes outside the image default to 0; nothing relies on that, as the
   tactics below prove every byte against [kernel_bytes] explicitly. *)
Definition kb_byte (A : Z) : bv 8 :=
  default (bv_0 8) (KernelInstrs.kernel_bytes !! A).

Definition kb_word_at (A : Z) : mword 32 :=
  mword_of_int (bv_unsigned (kb_byte A)
              + 256 * bv_unsigned (kb_byte (A + 1))
              + 65536 * bv_unsigned (kb_byte (A + 2))
              + 16777216 * bv_unsigned (kb_byte (A + 3))).

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



  (* ---- ALIGNMENT-AGNOSTIC RVC introduction (the one clients should use) ----
     [instr_bytes] asks for 4 bytes at a 4-aligned pc and only 2 at a merely
     2-aligned one, so [instr_bytes_rvc4] / [instr_bytes_rvc2] above oblige the
     caller to know pc's 4-alignment -- which no kernel-code proof should
     depend on, since inserting one instruction anywhere upstream shifts every
     later address by 2 and flips the parity of the rest of the image.
     This lemma discharges BOTH arms from the SAME premises: hand over the
     4-byte window [w] whose low half is [h].  The 4-aligned arm takes it
     as-is; the 2-aligned arm keeps only the low 2 bytes, which ARE [h]'s bytes
     by [nth_byte_subrange_lo].  Owning 4 bytes where the fetch reads 2 is
     free: the window comes from the persistent [kernel_text], and a
     mid-function instruction always has a successor in the image. *)
  Lemma instr_bytes_rvc_any (pc : mword 64) (h : mword 16) (w : mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    isRVC h = true ->
    subrange_vec_dec w 15 0 = h ->
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₘ□ nth_byte w j) -∗
    instr_bytes pc (F_RVC h).
  Proof.
    iIntros (H2 Hr Hs) "#Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hr|].
    (* [h]'s bytes ARE the window's low bytes.  Derived by [apply] (which
       unifies up to conversion) rather than [rewrite]: [subrange_vec_dec]'s
       [autocast] makes the two elaborations non-syntactic. *)
    assert (Hb : forall j : nat, (N.of_nat j < 2)%N -> nth_byte h j = nth_byte w j).
    { intros j Hj. rewrite <- Hs. apply nth_byte_subrange_lo. exact Hj. }
    destruct (is_aligned_vaddr (Virtaddr pc) 4).
    - (* 4-aligned: the window is exactly what this arm asks for *)
      iExists w. iSplitR; [iPureIntro; exact Hs|]. iExact "Hw".
    - (* 2-aligned only: project the window's low 2 bytes onto [h]'s.  The
         bytes are persistent, so the unused high half is simply dropped. *)
      iApply big_sepL_intro. iIntros "!>" (k j Hk).
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      (* pull the byte out while [Hw] is still in [big_sepL] form: a proofmode
         [simpl] would reduce the HYPOTHESIS too and break the unification. *)
      iDestruct (big_sepL_lookup _ _ k k with "Hw") as "Hk".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      rewrite Nat.add_0_l. rewrite (Hb k ltac:(lia)). iExact "Hk".
  Qed.

End KernelText.

(* ===================================================================== *)
(*  The kernel-window [instr] tactics.  This is their one home: every      *)
(*  whole-function proof file imports KernelText, so change them HERE.     *)
(*                                                                        *)
(*    [mk_rvc  A h pc ast decname expname] -- 2-byte compressed instr      *)
(*    [mk_base A w pc ast decname]         -- 4-byte base instr            *)
(*                                                                        *)
(*  Both are ALIGNMENT-AGNOSTIC: neither mentions [A]'s 4-alignment, so an *)
(*  upstream edit shifting the image by 2 -- which flips the parity of     *)
(*  every later address -- leaves every call site untouched.  [mk_rvc]     *)
(*  takes no window word: it computes the window from the image            *)
(*  ([kb_word_at A]) and proves it against [kernel_bytes].                 *)
(*                                                                        *)
(*  [decname]'s side conditions are closed by [close_dec]: either straight *)
(*  from the hypotheses [instr] supplies, or -- for a decoder that wants a *)
(*  specific misa bit (MUL wants misa.M, and so on) -- by computing it out *)
(*  of the [misa = MISA_C] hypothesis, which pins every bit.  So needing a *)
(*  misa bit is NOT a reason to hand-roll a constructor or to take         *)
(*  [hw_config] as a premise.                                             *)
(* ===================================================================== *)

Ltac close_dec decname :=
  apply decname;
  first [ assumption
        | match goal with
          (* Keyed on the RHS alone: this file does [Import Defs], so a pattern
             mentioning [misa] would resolve it to a constant that is NOT the
             one in a client file's hypothesis, and never match.  [MISA_C] is
             unambiguous and appears only in this hypothesis. *)
          | H : _ = MISA_C |- _ => rewrite H; vm_compute; reflexivity
          end ].

Ltac mk_rvc A h pc ast decname expname :=
  let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
  let Hrvc := fresh "Hrvc" in let Hsub := fresh "Hsub" in
  let Hbytes := fresh "Hbytes" in
  assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
  assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
  assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
  assert (Hsub : subrange_vec_dec (kb_word_at A) 15 0 = h)
    by (apply bv_eq; vm_compute; reflexivity);
  assert (Hbytes : forall j, (j < 4)%nat ->
      KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte (kb_word_at A) j))
    by (intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
  iIntros "#Ht"; rewrite /instr;
  iSplitR; [iPureIntro; exact Hlpad|];
  iExists (F_RVC h);
  iSplitR; [iPureIntro; reflexivity|];
  iSplitL "";
  [ iApply (instr_bytes_rvc_any pc h (kb_word_at A) H2al Hrvc Hsub);
    iApply (kernel_window_pc A (kb_word_at A) 4 pc eq_refl Hbytes with "Ht")
  | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
    eexists; (split; [ close_dec decname
                     | split; [ vm_compute; reflexivity
                              | intro; apply expname ] ]) ].

Ltac mk_base A w pc ast decname :=
  let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
  let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
  assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
  assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
  assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
  assert (Hbytes : forall j, (j < 4)%nat ->
      KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
    by (intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
  iIntros "#Ht"; rewrite /instr;
  iSplitR; [iPureIntro; exact Hlpad|];
  iExists (F_Base w);
  iSplitR; [iPureIntro; reflexivity|];
  iSplitL "";
  [ iApply (instr_bytes_base pc w H2al Hnrvc);
    iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
  | iIntros (?) "_"; iPureIntro; intros; close_dec decname ].
