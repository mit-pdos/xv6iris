(* TrampText.v -- THE TRAMPOLINE TEXT MINT: the kernel-text bytes of the
   trampoline page, re-keyed from their IDENTITY address onto the TRAMPOLINE
   virtual address, at the KT1 tier.

   This is increment K5 of the sp-migration campaign
   (claude-notes/projects/sp-migration.md).  It is the text-tier twin of
   [KstackOwn.v]: two persistent facts meet, and their conjunction IS the
   same bytes spelled at a NON-IDENTITY va.

   - [WpKvminithart.kvm_M_mint] mints the persistent claim
     [kmap_at tramp_vpn tramp_ppn KP_rx] out of the boot [kmap_auth] -- the
     kernel table maps the top page of the address space onto the physical
     trampoline page, R|X;
   - the trampoline page IS kernel text (ppn 0x80006, below [text_end]), so
     the boot image already hands out each of its bytes as an identity
     [pa ↦ₓ□ b] at the KT0 tier ([BootCarve]/[KernelText.kernel_text]).

   The result is at KT1, and it has to be: [TRAMPOLINE] is not identity
   mapped, so a KT0 datum there would be unsound on a Bare hart
   (RiscvPtsto's [ktier_pin] header).  Driving a FETCH with it therefore
   needs the per-hart witness, which [SRegime.sr_absorb_ktier] takes and
   [SmodeCorePt.s_regime_fetch] threads.

   IT IS A LEMMA, NOT A ONE-OFF BOOT MINT, and deliberately so: BOTH inputs
   are persistent, so the conclusion is persistent and duplicable and there
   is no linear resource to place, no ownership conflict with the identity
   image, and no boot-time seam to thread it through.  A consumer (uservec /
   userret, a later project) applies it wherever it already holds the
   trampoline claim -- which after [kvminithart] is everywhere.

   NEW MACHINERY IS DELIBERATELY LOCAL, exactly as in [KstackOwn.v]: nothing
   in RiscvPtsto / KMap / KptExecMap moved for it.

   THE TIER IS ALWAYS SPELLED.  Every statement below names [[KT0]] or
   [[KT1]] explicitly: this file is precisely the seam between the two
   tiers, so an ambient spelling here would be a silent pin. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.Operators_mwords SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import Ktier.
Require Import KptExecMap.
Require Import KptPt.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1  The trampoline page, as an address predicate + its arithmetic.     *)
(* ===================================================================== *)

(* [va] lies in the TRAMPOLINE page: the top page of the Sv39 positive half
   ([KptExecMap.tramp_vpn] = 0x3FFFFFF), i.e. [2^38 - 4096 <= uint va < 2^38].
   Spelled with the literals so every proof below is plain [lia]; the bridge
   to [KptExecMap.kpt_exec_mapped]'s trampoline disjunct is right below. *)
Definition tramp_page_va (va : mword 64) : Prop :=
  (274877902848 <= uint va < 274877906944)%Z.

(* the two page-number literals, once *)
Lemma tramp_vpn_uns_lit : bv_unsigned tramp_vpn = 67108863.
Proof. vm_compute. reflexivity. Qed.
Lemma tramp_ppn_uns_lit : bv_unsigned tramp_ppn = 524294.
Proof. vm_compute. reflexivity. Qed.

Lemma tramp_page_va_mapped (va : mword 64) :
  tramp_page_va va -> kpt_exec_mapped va.
Proof.
  unfold tramp_page_va. intro Hin. apply kpt_exec_mapped_tramp.
  rewrite tramp_vpn_uns_lit. lia.
Qed.

(* a trampoline va is CANONICAL: the page ends exactly AT 2^38, the top of
   the positive Sv39 half, so [uint va < 2^38] with nothing to spare. *)
Lemma tramp_va_canonical (va : mword 64) :
  tramp_page_va va -> (uint va < 274877906944)%Z.
Proof. unfold tramp_page_va. lia. Qed.

(* ...and its vpn IS [tramp_vpn], which is what matches the claim. *)
Lemma tramp_svpn (va : mword 64) :
  tramp_page_va va -> svpn_of va = tramp_vpn.
Proof.
  intro Hin. pose proof Hin as Hin'. unfold tramp_page_va in Hin'.
  apply bv_eq.
  rewrite (svpn_of_unsigned_lo va (tramp_va_canonical va Hin)).
  rewrite tramp_vpn_uns_lit.
  rewrite (Z.shiftr_div_pow2 (uint va) 12 ltac:(lia)).
  change (2 ^ 12)%Z with 4096%Z.
  (* [Z.div_unique_pos] concludes [q = a / b]; take it in a term so the
     orientation is fixed rather than left to [symmetry]. *)
  pose proof (Z.div_unique_pos (uint va) 4096 67108863
                (uint va - 274877902848)%Z ltac:(lia) ltac:(lia)) as Hu.
  exact (eq_sym Hu).
Qed.

(* round-trip for the one 64-bit literal-address construction below *)
Local Lemma mword64_unsigned (z : Z) :
  (0 <= z < 18446744073709551616)%Z ->
  bv_unsigned (mword_of_int z : mword 64) = z.
Proof.
  intro Hz. unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    as -> by (vm_compute; reflexivity).
  exact Hz.
Qed.

(* THE PA, both spellings.  [kpt_exec_pa] (the fetch-side map, KptExecMap)
   and [pa_of tramp_ppn] (what the trampoline CLAIM takes the va to) are the
   same address: [tramp_ppn * 4096 + va's page offset].  Each is computed to
   the same literal form and then the two are joined. *)
Lemma tramp_exec_pa_uint (va : mword 64) :
  tramp_page_va va ->
  (uint (kpt_exec_pa va) = 2147508224 + (uint va - 274877902848))%Z.
Proof.
  intro Hin. pose proof Hin as Hin'. unfold tramp_page_va in Hin'.
  assert (Hle : (bv_unsigned tramp_vpn * 4096 <= uint va)%Z)
    by (rewrite tramp_vpn_uns_lit; lia).
  rewrite (kpt_exec_pa_tramp va Hle).
  rewrite tramp_vpn_uns_lit tramp_ppn_uns_lit.
  rewrite !uint_unsigned. rewrite uint_unsigned in Hin'.
  (* [rewrite ... by] is not available under ssreflect's [rewrite]; the side
     condition is the SECOND goal. *)
  rewrite mword64_unsigned; [lia | lia].
Qed.

Lemma tramp_pa_of_uint (va : mword 64) :
  tramp_page_va va ->
  (uint (pa_of tramp_ppn va) = 2147508224 + (uint va - 274877902848))%Z.
Proof.
  intro Hin. pose proof Hin as Hin'. unfold tramp_page_va in Hin'.
  rewrite !uint_unsigned. rewrite uint_unsigned in Hin'.
  unfold pa_of. rewrite zext64_concat44_12_unsigned.
  rewrite subrange64_unsigned_11_0. rewrite tramp_ppn_uns_lit.
  change (2 ^ 12)%Z with 4096%Z.
  assert (Hm : (bv_unsigned va `mod` 4096 = bv_unsigned va - 274877902848)%Z).
  { exact (eq_sym (Z.mod_unique_pos (bv_unsigned va) 4096 67108863
             (bv_unsigned va - 274877902848)%Z ltac:(lia) ltac:(lia))). }
  rewrite Hm. lia.
Qed.

Lemma tramp_pa_of (va : mword 64) :
  tramp_page_va va -> pa_of tramp_ppn va = kpt_exec_pa va.
Proof.
  intro Hin. apply bv_eq.
  rewrite <- (uint_unsigned (pa_of tramp_ppn va)).
  rewrite <- (uint_unsigned (kpt_exec_pa va)).
  rewrite (tramp_pa_of_uint va Hin) (tramp_exec_pa_uint va Hin). reflexivity.
Qed.

(* ...and that address is kernel TEXT: the trampoline page sits at
   0x80006000, the LAST page below [text_end] = 0x80007000.  This is the
   whole reason the mint is possible -- the trampoline's bytes ARE kernel
   text, already owned (persistently) at their identity address. *)
Lemma tramp_pa_text (va : mword 64) :
  tramp_page_va va -> addr_is_text (kpt_exec_pa va).
Proof.
  intro Hin. pose proof Hin as Hin'. unfold tramp_page_va in Hin'.
  unfold addr_is_text, ram_base, text_end.
  rewrite (tramp_exec_pa_uint va Hin). lia.
Qed.

(* ===================================================================== *)
(* §2  THE MINT.                                                          *)
(* ===================================================================== *)

Section TrampText.
  Context `{!riscvGS Σ}.

  (* ONE BYTE.  Claim + the same physical byte's identity text fact = the
     byte at its TRAMPOLINE va, at KT1.

     Both premises are PERSISTENT ([kmap_at] is a discarded ghost-map
     element; [↦ₓ□] is [text_pointsto_discarded_persistent]), and so is the
     conclusion -- so this mints without consuming anything: the identity
     image keeps every byte it had, and the same byte is now ALSO owned at
     the high va.  That is sound because both are the DfracDiscarded,
     read-only form; there is no writable text. *)
  Lemma tramp_text_mint (va : mword 64) (b : bv 8) :
    tramp_page_va va ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    (kpt_exec_pa va) ↦ₓ[KT0]□ b -∗
    va ↦ₓ[KT1]□ b.
  Proof.
    intro Hin. iIntros "#Hk #Hid".
    (* the identity byte's own pin (KT0) says its pa IS its va, so the
       [pointsto] it carries is the one at [kpt_exec_pa va]. *)
    iDestruct (text_pointsto_acc (KTR := KT0) with "Hid")
      as (ppn0) "(_ & _ & _ & %Hpin0 & Hp & #Hts & _)".
    apply ktier_pin_id in Hpin0.
    rewrite Hpin0.
    (* re-key onto [va] under the trampoline claim; at KT1 the pin is [I].
       The pristine element travels with the byte: the KT1 va and the KT0
       identity address name the SAME physical byte, so the element minted
       for the image serves the trampoline mapping unchanged. *)
    rewrite /text_pointsto. iExists tramp_ppn.
    rewrite (tramp_svpn va Hin). rewrite (tramp_pa_of va Hin).
    iFrame "Hk Hp Hts". iPureIntro.
    split; [exact (tramp_va_canonical va Hin) |
      split; [exact (tramp_pa_text va Hin) | exact I]].
  Qed.

  (* A WINDOW.  [instr_bytes]' footprint shape ([KernelText.instr_bytes_base]
     / [instr_bytes_rvc_any] are tier-generic, so a KT1 window feeds them
     directly and [SmodeCorePt.s_regime_fetch (KTR := KT1)] then drives the
     fetch).  Pointwise over [tramp_text_mint]; the per-byte in-page premise
     is what rules out a straddle off the end of the page. *)
  Lemma tramp_text_window (va : mword 64) (W : nat) (g : nat -> bv 8) :
    (forall j : nat, (j < W)%nat -> tramp_page_va (pa_add va j)) ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    ([∗ list] j ∈ seq 0 W, (kpt_exec_pa (pa_add va j)) ↦ₓ[KT0]□ g j) -∗
    ([∗ list] j ∈ seq 0 W, (pa_add va j) ↦ₓ[KT1]□ g j).
  Proof.
    intro Hin. iIntros "#Hk #Hw".
    iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. rewrite Nat.add_0_l.
    iDestruct (big_sepL_lookup _ _ k k with "Hw") as "Hbk".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iApply (tramp_text_mint (pa_add va k) (g k) (Hin k Hlt) with "Hk Hbk").
  Qed.

  (* the bundle IS persistent -- duplicable with nothing given back.  (The
     instance is [RiscvPtsto.text_pointsto_discarded_persistent']; this is
     the statement a consumer can point at.) *)
  Lemma tramp_text_dup (va : mword 64) (b : bv 8) :
    va ↦ₓ[KT1]□ b -∗ va ↦ₓ[KT1]□ b ∗ va ↦ₓ[KT1]□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

End TrampText.
