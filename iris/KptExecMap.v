(* KptExecMap.v -- the PURE fetch-side va↦pa map for the kernel S-mode
   page table (identity kernel text ∪ the high-mapped TRAMPOLINE page), PLUS
   the pure region constants the map (and the InstrBytes/KernelText fetch
   layer) is stated over.

   These definitions are pure (no Iris / ghost context): the executable map
   is STATIC, so a fetch va's physical address is a FUNCTION [kpt_exec_pa] of
   the va -- identity on the text region, offset-remapped onto the trampoline
   page.

   LAYERING: this file sits BELOW InstrBytes (it imports only RiscvPtsto, for
   [ram_base]/[ram_size]) so InstrBytes can key [instr] on the virtual pc
   without a dependency cycle.  The ADDRESS-level text/data region split
   ([text_end]/[addr_is_text]/[addr_is_kdata]) lives in RiscvPtsto -- the
   points-to layer records it (rwx-kmap) -- and is reused here, not
   duplicated.  This file is the single home of the vpn-granularity
   [etext_vpn] and the trampoline geometry [tramp_vpn]/[tramp_ppn]:
   TrampPt.v `Require Export`s this file; KptTree.v/KMap.v Require it
   directly (no duplication, no equality bridge).

   The DATA side ([kpt_data_va]) stays in KptTree.v: its kstack arm is a
   ghost-parameterised RELATION and needs the [kstackG] context.          *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto RiscvExtras.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  Region constants (moved here from KptPt.v / TrampPt.v so they sit     *)
(*  below InstrBytes; KptPt/TrampPt Require Export this file).            *)
(* ===================================================================== *)

(* end of kernel text, as a vpn: KernelSyms.etext = 0x80007000 (the dump
   is authoritative; cross-checked against KernelSyms in KvmSpec.v).  The
   ADDRESS-level split is RiscvPtsto's [text_end]/[addr_is_text]/
   [addr_is_kdata]; this vpn-granularity constant agrees with it: *)
Definition etext_vpn : Z := 0x80007.

Lemma etext_vpn_text_end : etext_vpn * 4096 = text_end.
Proof. vm_compute. reflexivity. Qed.

(* the trampoline page's vpn and physical page number (KernelSyms.trampoline
   >> 12). *)
Definition tramp_vpn : mword 27 := mword_of_int 0x3FFFFFF.
Definition tramp_ppn : mword 44 := mword_of_int 0x80006.

(* ===================================================================== *)
(*  The fetch-side va↦pa map.                                             *)
(* ===================================================================== *)

(* the executable (fetch-legal) window: identity kernel text, plus the
   high-mapped TRAMPOLINE page (va = tramp_vpn·4096 + offset). *)
Definition kpt_exec_mapped (va : mword 64) : Prop :=
  addr_is_text va \/
  bv_unsigned tramp_vpn * 4096 <= uint va
    < bv_unsigned tramp_vpn * 4096 + 4096.

(* the fetch va's physical address: identity on text; on the trampoline
   page, the kernel-text trampoline page pa + the in-page offset. *)
Definition kpt_exec_pa (va : mword 64) : mword 64 :=
  if Z.leb (bv_unsigned tramp_vpn * 4096) (uint va)
  then mword_of_int (bv_unsigned tramp_ppn * 4096
                     + (uint va - bv_unsigned tramp_vpn * 4096))
  else va.

(* the derived relation the fetch absorption theorem is stated over *)
Definition kpt_exec_va (va pa : mword 64) : Prop :=
  kpt_exec_mapped va /\ pa = kpt_exec_pa va.

(* ===================================================================== *)
(*  Rewrite / intro helpers for the Stage-5 fetch engine.                 *)
(*  [instr] stays PA-keyed; the unified S-mode engine consumes            *)
(*  [instr (kpt_exec_pa pc)] + a whole-window [kpt_exec_mapped] premise,  *)
(*  and these lemmas let it evaluate [kpt_exec_pa] and discharge the      *)
(*  mapped-window obligation on each arm (text / trampoline).             *)
(* ===================================================================== *)

(* text arm: identity.  ([addr_is_text va] ⟹ [uint va] far below the
   trampoline range, so the [Z.leb] guard is false.) *)
Lemma kpt_exec_pa_text (va : mword 64) :
  addr_is_text va -> kpt_exec_pa va = va.
Proof.
  unfold addr_is_text, kpt_exec_pa. intros [_ Hhi].
  assert (Ht : bv_unsigned tramp_vpn * 4096 = 274877902848) by (vm_compute; reflexivity).
  assert (He : text_end = 2147512320) by (vm_compute; reflexivity).
  rewrite Ht. rewrite He in Hhi.
  replace (Z.leb 274877902848 (uint va)) with false.
  - reflexivity.
  - symmetry. apply Z.leb_gt. lia.
Qed.

(* trampoline arm: symbolic evaluation to the remapped physical address.
   (Concrete tramp-page addresses also reduce directly by [vm_compute];
   this is the form for a symbolic [va].) *)
Lemma kpt_exec_pa_tramp (va : mword 64) :
  bv_unsigned tramp_vpn * 4096 <= uint va ->
  kpt_exec_pa va = mword_of_int (bv_unsigned tramp_ppn * 4096
                     + (uint va - bv_unsigned tramp_vpn * 4096)).
Proof.
  unfold kpt_exec_pa. intro H.
  replace (Z.leb (bv_unsigned tramp_vpn * 4096) (uint va)) with true.
  - reflexivity.
  - symmetry. apply Z.leb_le. exact H.
Qed.

(* [kpt_exec_pa] shifts a va only by page-aligned (hence even) constants, so it
   preserves 2-alignment: if the physical fetch address [kpt_exec_pa pc] is
   2-aligned then so is the virtual [pc].  (The SIE=1 interrupt arm keys [instr]
   at [kpt_exec_pa pc] but needs [pc]'s alignment to derive [ret_pc pc = pc].)
   Pure arithmetic, kept out of the fragile [access_vec_dec] path so the
   [bv]/[mod] reduction stays stable. *)
Lemma kpt_exec_pa_aligned2 (pc : mword 64) :
  is_aligned_vaddr (Virtaddr (kpt_exec_pa pc)) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 2 = true.
Proof.
  unfold is_aligned_vaddr. rewrite !RiscvExtras.uint_unsigned.
  intro H. apply Z.eqb_eq in H. apply Z.eqb_eq. revert H.
  unfold kpt_exec_pa.
  destruct (Z.leb (bv_unsigned tramp_vpn * 4096) (uint pc)) eqn:Hle.
  2:{ intro H; exact H. }
  unfold mword_of_int, Values.to_word, get_word. cbn.
  rewrite Z_to_bv_unsigned. rewrite RiscvExtras.uint_unsigned.
  intro H.
  pose proof (bv_unsigned_in_range _ pc) as [Hlo Hhi].
  assert (Hm : bv_modulus 64 = 2 ^ 64) by (vm_compute; reflexivity).
  unfold bv_wrap in H. rewrite Hm in H.
  rewrite Z.rem_mod_nonneg in H; [ | apply Z.mod_pos_bound; lia | lia ].
  rewrite (Z.mod_mod_divide _ (2 ^ 64) 2
             ltac:(exists (2 ^ 63); vm_compute; reflexivity)) in H.
  rewrite Z.rem_mod_nonneg; [ | exact Hlo | lia ].
  change (MachineWord.Z_idx 64) with (64%N) in H.
  assert (HA2 : (bv_unsigned tramp_ppn * 4096) mod 2 = 0).
  { replace (bv_unsigned tramp_ppn * 4096)
      with ((bv_unsigned tramp_ppn * 2048) * 2) by lia.
    apply Z.mod_mul. lia. }
  assert (HB2 : (bv_unsigned tramp_vpn * 4096) mod 2 = 0).
  { replace (bv_unsigned tramp_vpn * 4096)
      with ((bv_unsigned tramp_vpn * 2048) * 2) by lia.
    apply Z.mod_mul. lia. }
  change (MachineWord.Z_idx 44) with (44%N) in HA2.
  change (MachineWord.Z_idx 27) with (27%N) in HB2.
  rewrite Zplus_mod in H. rewrite HA2 in H.
  rewrite Zminus_mod in H. rewrite HB2 in H.
  rewrite Z.sub_0_r in H. rewrite Z.add_0_l in H.
  rewrite (Z.mod_mod _ 2 ltac:(lia)) in H.
  rewrite (Z.mod_mod _ 2 ltac:(lia)) in H.
  exact H.
Qed.

(* [kpt_exec_mapped] introduction, one per arm. *)
Lemma kpt_exec_mapped_text (va : mword 64) :
  addr_is_text va -> kpt_exec_mapped va.
Proof. intro H. left. exact H. Qed.

Lemma kpt_exec_mapped_tramp (va : mword 64) :
  bv_unsigned tramp_vpn * 4096 <= uint va
    < bv_unsigned tramp_vpn * 4096 + 4096 ->
  kpt_exec_mapped va.
Proof. intro H. right. exact H. Qed.

(* whole-window exec-mapped: every byte of a [W]-byte window at [va] is
   fetch-legal.  This is the shape the S-mode fetch engine's premise takes
   (uniform over the window per the design note). *)
Definition kpt_exec_window (va : mword 64) (W : nat) : Prop :=
  forall j : nat, (j < W)%nat -> kpt_exec_mapped (pa_add va j).

(* the natural text-window introduction: a window whose every byte lies in
   the kernel text region is exec-mapped throughout. *)
Lemma kpt_exec_window_text (va : mword 64) (W : nat) :
  (forall j : nat, (j < W)%nat -> addr_is_text (pa_add va j)) ->
  kpt_exec_window va W.
Proof. intros H j Hj. left. apply H. exact Hj. Qed.
