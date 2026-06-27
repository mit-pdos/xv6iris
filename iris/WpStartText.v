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
  Definition skinstr (i : Z) : kinstr := default kdefault (kernel_instrs !! i).

  (* UNIFORM 4-byte fetch window of one instruction (the RISC-V fetch reads a
     4-byte-aligned word whenever Ziccif is enabled -- always, in this model):
     SOME 32-bit word [w] whose low [ki_width k] bits agree (byte-wise) with the
     instruction's encoding, with all 4 bytes stored persistently.
     - 4-byte instruction: all 4 bytes are [ki_enc].
     - 2-byte (RVC) instruction: low 2 bytes are the RVC; upper 2 are the NEXT
       instruction (read-and-discarded by the fetch), hence UNCONSTRAINED.
     The redundant [subrange] clause records the low-16 agreement in the shape an
     RVC decode consumes ([subrange w 15 0]).  This subsumes [twin4]/[regroup]. *)
  Definition kinstr_bytes (k : kinstr) : iProp Σ :=
    (∃ w : mword 32,
       ⌜ ∀ j, (j < ki_width k / 8)%nat ->
              nth_byte w j = nth_byte (mword_of_int (ki_enc k) : mword 32) j ⌝ ∗
       ⌜ subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int (ki_enc k) : mword 32) 15 0 ⌝ ∗
       [∗ list] j ∈ seq 0 4, (pa_add (fetch_pa (mword_of_int (ki_addr k))) j) ↦ₘ□ nth_byte w j)%I.
  Global Instance kinstr_bytes_persistent k : Persistent (kinstr_bytes k).
  Proof. apply _. Qed.

  (* the actual 4-byte image word at address [A] (little-endian over kernel_bytes). *)
  Definition kword4 (A : Z) : mword 32 :=
    mword_of_int (assemble_bytes
      (map (fun j => default (Z_to_bv 8 0) (kernel_bytes !! (A + Z.of_nat j)%Z)) (seq 0 4))).

  (* extract the (always 4-byte) window from the persistent per-byte kernel_text,
     given the witness word [w] and the two (vm-checkable) agreement facts. *)
  Lemma kinstr_get (k : kinstr) (w : mword 32) :
    (∀ j, (j < 4)%nat -> kernel_bytes !! (ki_addr k + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    (∀ j, (j < ki_width k / 8)%nat -> nth_byte w j = nth_byte (mword_of_int (ki_enc k) : mword 32) j) ->
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int (ki_enc k) : mword 32) 15 0 ->
    kernel_text -∗ kinstr_bytes k.
  Proof.
    intros Hb Hbyte Hsub. iIntros "#Ht". iExists w.
    iSplit; [iPureIntro; exact Hbyte|]. iSplit; [iPureIntro; exact Hsub|].
    iApply (kernel_window (ki_addr k) w 4 Hb with "Ht").
  Qed.

  (* precondition for a 32-bit WP: the exact 4-byte window of [enc] at [addr]
     ([addr]/[enc] given concretely, as the old E_skinstr did, so the produced
     window matches the WP's word verbatim). *)
  Lemma kinstr_window32 (k : kinstr) (addr enc : Z) :
    ki_addr k = addr -> ki_enc k = enc -> ki_width k = 32%nat ->
    kinstr_bytes k -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa (mword_of_int addr)) j)
                             ↦ₘ□ nth_byte (mword_of_int enc : mword 32) j).
  Proof.
    intros <- <- Hw. iIntros "(%w & %Hbyte & _ & Hwin)".
    iApply (big_sepL_impl with "Hwin"). iIntros "!>" (i y Hi) "H".
    apply lookup_seq in Hi. destruct Hi as [-> Hlt].
    assert (Hib : (0 + i < ki_width k / 8)%nat) by (rewrite Hw; simpl; lia).
    rewrite (Hbyte _ Hib). iExact "H".
  Qed.

  (* precondition for an RVC instruction fetched as 4 bytes (the [_4] WPs): a
     4-byte window of SOME [w] whose low 16 bits are [enc]'s.
     REPLACES [regroup]/[twin4]: one [kinstr_bytes] suffices, no combining. *)
  Lemma kinstr_rvc4 (k : kinstr) (addr enc : Z) :
    ki_addr k = addr -> ki_enc k = enc ->
    kinstr_bytes k -∗ ∃ w : mword 32,
       ⌜ subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int enc : mword 32) 15 0 ⌝ ∗
       [∗ list] j ∈ seq 0 4, (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ□ nth_byte w j.
  Proof.
    intros <- <-. iIntros "(%w & _ & %Hsub & Hwin)". iExists w. iSplit; [done|]. iExact "Hwin".
  Qed.

  (* precondition for a 2-byte RVC WP: the low-2-byte window of [enc] at [addr]
     (the upper 2 bytes are simply dropped). *)
  Lemma kinstr_window16 (k : kinstr) (addr enc : Z) :
    ki_addr k = addr -> ki_enc k = enc -> (2 <= ki_width k / 8)%nat ->
    kinstr_bytes k -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa (mword_of_int addr)) j)
                             ↦ₘ□ nth_byte (mword_of_int enc : mword 32) j).
  Proof.
    intros <- <- Hge. iIntros "(%w & %Hbyte & _ & Hwin)".
    replace (seq 0 4) with (seq 0 2 ++ seq 2 2)%list by reflexivity.
    rewrite big_sepL_app. iDestruct "Hwin" as "[H2 _]".
    iApply (big_sepL_impl with "H2"). iIntros "!>" (i y Hi) "H".
    apply lookup_seq in Hi. destruct Hi as [-> Hlt].
    assert (Hib : (0 + i < ki_width k / 8)%nat) by lia.
    rewrite (Hbyte _ Hib). iExact "H".
  Qed.

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

(* point-of-use 4-byte window extractor (top level so it is visible to importers).
   Provides [kword4] (the concrete image word) as the witness and discharges the
   three side conditions by vm_compute over the concrete image. *)
Ltac sg i :=
  (* Pre-evaluate the witness word to a CONCRETE bv literal, and -- crucially --
     discharge the three side conditions as NAMED hypotheses via [assert ... by]
     BEFORE the [iApply].  Passing inline [ltac:(...)] proofs to [kinstr_get]
     makes [iApply] re-elaborate those proof terms with slow (non-VM) conversion
     over the 23K-entry [kernel_bytes] gmap (~26s/instruction); a named, already
     type-checked hypothesis is spliced in directly (~0.007s/instruction). *)
  let w := eval vm_compute in (kword4 (ki_addr (skinstr i))) in
  let Hb := fresh "Hsg_b" in
  let Hc := fresh "Hsg_c" in
  let Hd := fresh "Hsg_d" in
  assert (Hb : forall j, (j < 4)%nat ->
            kernel_bytes !! (ki_addr (skinstr i) + Z.of_nat j)%Z = Some (nth_byte w j))
    by (intros j Hj; vm_compute in Hj;
        do 4 (destruct j as [|j];
          [first [vm_compute; f_equal; apply bv_eq; reflexivity | exfalso; lia] | ]); lia);
  assert (Hc : forall j, (j < ki_width (skinstr i) / 8)%nat ->
            nth_byte w j = nth_byte (mword_of_int (ki_enc (skinstr i)) : mword 32) j)
    by (intros j Hj; vm_compute in Hj;
        do 4 (destruct j as [|j];
          [first [apply bv_eq; vm_compute; reflexivity | exfalso; lia] | ]); lia);
  assert (Hd : subrange_vec_dec w 15 0
             = subrange_vec_dec (mword_of_int (ki_enc (skinstr i)) : mword 32) 15 0)
    by (apply bv_eq; vm_compute; reflexivity);
  iApply (kinstr_get (skinstr i) w Hb Hc Hd with "H").

