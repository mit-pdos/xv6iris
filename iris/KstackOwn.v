(* KstackOwn.v -- THE MINT: the 64 process kernel stacks, re-keyed from the
   identity-mapped pages kvminit handed out onto their KSTACK(i) virtual
   addresses, at the KT1 tier.

   This is increment K1 of the KSTACK campaign
   (claude-notes/projects/sp-migration.md).  Two facts meet in main's boot
   arm and nowhere else:

   - [SpecKvminit]/[SpecProcMapstacks]' post gives the 64 stack pages as
     [page_own (page_base (pas i))] -- 4096 anonymous bytes at the page's
     IDENTITY kernel va, i.e. at the KT0 tier (the identity pin holds
     trivially there);
   - [WpKvminithart.kvm_M_mint] mints the 64 persistent claims
     [kmap_at (kstack_vpn i) (pas i) KP_rw] out of the boot [kmap_auth].

   A claim plus the physical page it points at IS ownership of the same
   bytes spelled at the VIRTUAL address -- at KT1, because KSTACK(i) is not
   identity-mapped and a KT0 datum there would be unsound on a Bare hart
   (RiscvPtsto's [ktier_pin] header).  [phys_to_mem_map] at [kt := KT1] is
   the constructor; everything here is the ladder around it:

     mem_kt0_phys        a KT0 byte IS its physical byte (the pin says so)
     kstack_byte_rekey   identity byte j -> KSTACK(i)+j byte, at KT1
     kstack_word_rekey   the same, eight bytes at a time
     bwin_words8         a byte window IS a run of word cells (the
                         alignment-generic twin of [PageFields.page_words8],
                         which asks for [page_valid] -- a stack page carries
                         only [node_kdata], see [kvm_pas_ok])
     stack_own_of_words  a base-anchored run of word cells IS a [stack_own]
                         region below the run's top
     kstack_own_intro    the composition, one stack
     kstack_bank_intro   all 64

   NEW MACHINERY IS DELIBERATELY LOCAL.  Everything here Requires only
   existing files; nothing in RiscvPtsto/StackOwn/PageFields moved.  When a
   later increment folds the ladder back, [stack_own_of_words] belongs
   beside [StackOwn.stack_own_base] and [bwin_words8] beside
   [PageFields.page_words8].

   THE TIER IS ALWAYS SPELLED.  Every statement below names [(KTR := KT0)]
   or [(KTR := KT1)] explicitly rather than riding the ambient default --
   this file is exactly the seam between the two tiers, so an ambient
   spelling here would be a silent pin. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import StackOwn.
Require Import PageGeom.
Require Import KallocInv.
Require Import PageFields.
Require Import Pt4kWalk.
Require Import PtTree.
Require Import KvmMap.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(* §1 Pure arithmetic.  Every fact is stated over plain [Z]/[nat] and fed *)
(*     the bitvector values by name: a goal mentioning [bv_unsigned]      *)
(*     defeats [lia] under the transitively-imported [bitvector.tactics]  *)
(*     zify hook (durable-notes).                                         *)
(* ===================================================================== *)

(* 8 divides an offset that is 8 times something -- the divisibility side
   condition of every doubleword slot in a page. *)
Lemma kstk_dvd8 (n : nat) : (8 | Z.of_nat (8 * n)).
Proof.
  exists (Z.of_nat n). rewrite Nat2Z.inj_mul.
  change (Z.of_nat 8) with 8. ring.
Qed.

(* a 4096-aligned base plus an 8-aligned offset is 8-aligned *)
Lemma kstk_rem8 (up oz : Z) :
  0 <= up -> up mod 4096 = 0 -> 0 <= oz -> (8 | oz) -> Z.rem (up + oz) 8 = 0.
Proof.
  intros Hup Hal Ho Hdvd.
  assert (Hrem : Z.rem (up + oz) 8 = (up + oz) mod 8)
    by (apply Z.rem_mod_nonneg; lia).
  rewrite Hrem. apply Z.mod_divide; [lia|].
  apply Z.divide_add_r; [| exact Hdvd].
  apply Z.mod_divide in Hal; [| lia].
  apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact Hal].
Qed.

(* KSTACK(i) is 8192-aligned, hence 4096-aligned *)
Lemma kstk_va_mod4096 (z : Z) :
  0 <= z -> (274877902848 - 8192 * (z + 1)) mod 4096 = 0.
Proof.
  intro Hz.
  replace (274877902848 - 8192 * (z + 1)) with ((67108863 - 2 * (z + 1)) * 4096)
    by ring.
  apply Z.mod_mul. lia.
Qed.

Lemma kstk_va_fit (z oz : Z) :
  0 <= z -> z < 64 -> 0 <= oz -> oz < 4096 ->
  274877902848 - 8192 * (z + 1) + oz < 18446744073709551616.
Proof. intros. lia. Qed.

Lemma kstk_pb_fit (x oz : Z) :
  x + 4096 <= 2281701376 -> 0 <= oz -> oz < 4096 ->
  x + oz < 18446744073709551616.
Proof. intros. lia. Qed.

(* THE alignment lemma both sides of the re-key use: a page-aligned base
   plus an 8-aligned in-range offset gives a doubleword-aligned address.
   (The [page_valid]-based [PageFields.page_off_aligned] does not serve: a
   stack page carries only [node_kdata], and the KSTACK va is nowhere near
   [kmem_hi].) *)
Lemma aligned8_of_page_base (a : mword 64) (o : nat) :
  bv_unsigned a mod 4096 = 0 ->
  bv_unsigned a + Z.of_nat o < 18446744073709551616 ->
  (8 | Z.of_nat o) ->
  is_aligned_paddr (Physaddr (pa_add a o)) 8 = true.
Proof.
  intros Hal Hfit Hdvd.
  pose proof (bv_unsigned_in_range 64 a) as [Hnn _].
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  change (pa_add a o) with (add_vec_int a (Z.of_nat o)).
  rewrite (pa_add_unsigned a (Z.of_nat o) (Nat2Z.is_nonneg o) Hfit).
  exact (kstk_rem8 (bv_unsigned a) (Z.of_nat o) Hnn Hal (Nat2Z.is_nonneg o) Hdvd).
Qed.

Lemma page_base_aligned8 (ppn : mword 44) (o : nat) :
  node_kdata ppn -> (o < 4096)%nat -> (8 | Z.of_nat o) ->
  is_aligned_paddr (Physaddr (pa_add (page_base ppn) o)) 8 = true.
Proof.
  intros [_ Hhi] Ho Hdvd.
  assert (Holt : Z.of_nat o < 4096) by (apply (Nat2Z.inj_lt o 4096) in Ho; exact Ho).
  unfold ram_base, ram_size in Hhi.
  apply aligned8_of_page_base; [| | exact Hdvd].
  - unfold page_base. rewrite page_base_unsigned. apply Z.mod_mul. lia.
  - unfold page_base. rewrite page_base_unsigned.
    exact (kstk_pb_fit (bv_unsigned ppn * 4096) (Z.of_nat o) Hhi
             (Nat2Z.is_nonneg o) Holt).
Qed.

Lemma kstack_va_aligned8 (i o : nat) :
  (i < 64)%nat -> (o < 4096)%nat -> (8 | Z.of_nat o) ->
  is_aligned_paddr (Physaddr (pa_add (kstack_va i) o)) 8 = true.
Proof.
  intros Hi Ho Hdvd.
  assert (Holt : Z.of_nat o < 4096) by (apply (Nat2Z.inj_lt o 4096) in Ho; exact Ho).
  assert (Hilt : Z.of_nat i < 64) by (apply (Nat2Z.inj_lt i 64) in Hi; exact Hi).
  apply aligned8_of_page_base; [| | exact Hdvd].
  - rewrite (kstack_va_uns i Hi).
    exact (kstk_va_mod4096 (Z.of_nat i) (Nat2Z.is_nonneg i)).
  - rewrite (kstack_va_uns i Hi).
    exact (kstk_va_fit (Z.of_nat i) (Z.of_nat o) (Nat2Z.is_nonneg i) Hilt
             (Nat2Z.is_nonneg o) Holt).
Qed.

(* the region top: [base + 8*512] is [base + 4096], in the [add_vec …
   (mword_of_int 4096)] spelling [SpecForkretParkPaid.forkret_park_pkg]
   uses for a stack's top. *)
Lemma pa_add_4096_add_vec (a : mword 64) :
  pa_add a (8 * 512)%nat = add_vec a (mword_of_int 4096).
Proof.
  unfold pa_add, add_vec_int.
  assert (Hz : Z.of_nat (8 * 512)%nat = 4096) by (vm_compute; reflexivity).
  rewrite Hz. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The byte / word re-key: identity page -> KSTACK(i), KT0 -> KT1.     *)
(* ===================================================================== *)

Section rekey.
  Context `{!riscvGS Σ}.

  (* A KT0 datum's tier pin IS [pa_of ppn va = va], so the physical byte it
     owns sits at [va] itself: a KT0 [↦ₘ] is a [↦ₚ] with no claim, no
     ambient bundle and no side condition.  (The claim-carrying twins
     [KMap.mem_ident_phys] / [RiscvPtsto.mem_to_phys_claim] both ask for
     something the pin already provides.) *)
  Lemma mem_kt0_phys (va : mword 64) dq b :
    va ↦ₘ[KT0]{dq} b ⊢ va ↦ₚ{dq} b.
  Proof.
    rewrite /mem_pointsto /phys_pointsto.
    iIntros "H". iDestruct "H" as (ppn) "(_ & _ & %Hram & %Hpin & Hpt)".
    cbn in Hpin. rewrite Hpin in Hram. iEval (rewrite Hpin) in "Hpt".
    iFrame "Hpt". iPureIntro. exact Hram.
  Qed.

  (* ONE byte of stack [i]: the byte at offset [j] of the identity page
     [page_base ppn] is the byte at offset [j] of KSTACK(i), once the claim
     says KSTACK(i)'s vpn maps to [ppn].  KT1, necessarily: the KSTACK va is
     not its own physical address. *)
  Lemma kstack_byte_rekey (i : nat) (ppn : mword 44) (j : nat) dq b :
    (i < 64)%nat -> node_kdata ppn -> (j < 4096)%nat ->
    kmap_at (kstack_vpn i) ppn KP_rw -∗
    (pa_add (page_base ppn) j) ↦ₘ[KT0]{dq} b -∗
    (pa_add (kstack_va i) j) ↦ₘ[KT1]{dq} b.
  Proof.
    intros Hi Hkd Hj. iIntros "#Hcl H".
    iDestruct (mem_kt0_phys with "H") as "Hp".
    assert (Hram : addr_is_ram (pa_of ppn (pa_add (kstack_va i) j))).
    { rewrite (kstack_va_pa_of ppn i j Hi Hj).
      exact (kstack_ident_ram ppn j Hkd Hj). }
    iApply (phys_to_mem_map KT1 (pa_add (kstack_va i) j) ppn dq b
              Hram (kstack_va_canon_add i j Hi Hj) I with "[] [Hp]").
    - rewrite (kstack_va_svpn_add i j Hi Hj). iExact "Hcl".
    - rewrite (kstack_va_pa_of ppn i j Hi Hj). iExact "Hp".
  Qed.

  (* ...and eight of them, as one doubleword cell.  The KSTACK side's
     alignment is re-derived rather than transported: the two addresses are
     congruent mod 4096, but nothing in the [↦₈] bundle says so. *)
  Lemma kstack_word_rekey (i : nat) (ppn : mword 44) (o : nat) (w : bv 64) :
    (i < 64)%nat -> node_kdata ppn -> (o + 8 <= 4096)%nat -> (8 | Z.of_nat o) ->
    kmap_at (kstack_vpn i) ppn KP_rw -∗
    word_pointsto (KTR := KT0) (pa_add (page_base ppn) o) (DfracOwn 1) w -∗
    word_pointsto (KTR := KT1) (pa_add (kstack_va i) o) (DfracOwn 1) w.
  Proof.
    intros Hi Hkd Ho Hdvd. iIntros "#Hcl H".
    rewrite /word_pointsto.
    iDestruct "H" as "[_ Hbs]".
    iSplitR.
    { iPureIntro. apply (kstack_va_aligned8 i o Hi); [lia | exact Hdvd]. }
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hk) "Hb".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    rewrite !pa_add_add.
    iApply (kstack_byte_rekey i ppn (o + (0 + k))%nat (DfracOwn 1) (nth_byte w (0 + k)%nat)
              Hi Hkd ltac:(lia) with "Hcl Hb").
  Qed.

End rekey.

(* ===================================================================== *)
(* §3 The window -> word-run -> [stack_own] ladder.                       *)
(* ===================================================================== *)

Section ladder.
  Context `{!riscvGS Σ}.

  (* [PageFields.page_words8] with the alignment side condition taken as a
     hypothesis instead of derived from [page_valid].  A kalloc'd stack page
     IS [page_valid], but the only thing kvminit's contract exports about it
     is [kvm_pas_ok] = [node_kdata] (which is genuinely weaker -- a page
     between [etext] and [end] is RAM but not kalloc'able), and this ladder
     is also run at the KSTACK va, which is nowhere near [kmem_hi]. *)
  Lemma bwin_words8 (p : mword 64) (n : nat) :
    (forall o : nat, (o + 8 <= 8 * n)%nat -> (8 | Z.of_nat o) ->
       is_aligned_paddr (Physaddr (pa_add p o)) 8 = true) ->
    ([∗ list] j ∈ seq 0 (8 * n), byte_any (pa_add p j)) ⊢
    ∃ ws : list (bv 64), ⌜length ws = n⌝ ∗
      ([∗ list] k ↦ w ∈ ws,
         word_pointsto (KTR := KT0) (pa_add p (8 * k)%nat) (DfracOwn 1) w).
  Proof.
    induction n as [|n IH]; intro Hal.
    - iIntros "_". iExists []. by iSplit.
    - replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
      rewrite (bwin_split p 0 (8 * n) 8).
      iIntros "[Hpre Hlast]".
      iDestruct (IH ltac:(intros o Ho Hd; apply Hal; [lia | exact Hd]) with "Hpre")
        as (ws) "[%Hlen Hws]".
      rewrite Nat.add_0_l bwin_rebase.
      iDestruct (bytes_word8 (pa_add p (8 * n)%nat)
                   (Hal (8 * n)%nat ltac:(lia) (kstk_dvd8 n)) with "Hlast")
        as (w) "Hw".
      iExists (ws ++ [w])%list.
      iSplit; [iPureIntro; rewrite length_app Hlen /=; lia|].
      rewrite big_sepL_app big_sepL_singleton Hlen.
      iFrame "Hws". rewrite Nat.add_0_r. iExact "Hw".
  Qed.

  (* forget the contents of an indexed run: [∗ list] over the values becomes
     [∗ list] over [seq], with each value existentially quantified.  The
     shape [StackOwn.stack_own_base] states its region in. *)
  Lemma bigsep_ws_seq (Φ : nat -> bv 64 -> iProp Σ) (ws : list (bv 64)) :
    ([∗ list] k ↦ w ∈ ws, Φ k w) ⊢
    [∗ list] j ∈ seq 0 (length ws), ∃ w : bv 64, Φ j w.
  Proof.
    induction ws as [|w ws IH] using rev_ind; [ by iIntros "_" | ].
    rewrite length_app /= Nat.add_1_r seq_S big_sepL_app big_sepL_singleton.
    rewrite big_sepL_app big_sepL_singleton.
    iIntros "[Hpre Hlast]".
    iSplitL "Hpre"; [ by iApply IH | ].
    rewrite Nat.add_0_r Nat.add_0_l. iExists w. iExact "Hlast".
  Qed.

  (* A base-anchored run of [n] doubleword cells at [base + 8k] IS the
     [stack_own] region of depth [n] hanging below [base + 8n] -- the stack
     grows down, so the run's TOP is the region's sp.  Tier-generic and
     base-generic: this is the reusable half of the ladder. *)
  Lemma stack_own_of_words (kt : ktier) (base : mword 64) (n : nat)
      (ws : list (bv 64)) :
    length ws = n ->
    ([∗ list] k ↦ w ∈ ws,
       word_pointsto (KTR := kt) (pa_add base (8 * k)%nat) (DfracOwn 1) w) ⊢
    stack_own (KTR := kt) (pa_add base (8 * n)%nat) n.
  Proof.
    intro Hlen.
    rewrite (stack_own_base (KTR := kt) (pa_add base (8 * n)%nat) n).
    assert (Hb : pa_stk (pa_add base (8 * n)%nat) n = base).
    { unfold pa_stk, pa_add. rewrite avi_assoc.
      rewrite Nat2Z.inj_mul. change (Z.of_nat 8) with 8.
      replace (8 * Z.of_nat n + - (8 * Z.of_nat n)) with 0 by ring.
      apply avi0. }
    rewrite Hb.
    rewrite -Hlen.
    iIntros "H".
    iDestruct (bigsep_ws_seq
                 (fun k w => word_pointsto (KTR := kt) (pa_add base (8 * k)%nat)
                               (DfracOwn 1) w) ws with "H") as "H".
    iApply (big_sepL_mono with "H").
    intros k j _. iIntros "H".
    assert (Hj : pa_add base (8 * j)%nat = add_vec_int base (8 * Z.of_nat j)).
    { unfold pa_add. rewrite Nat2Z.inj_mul. change (Z.of_nat 8) with 8. reflexivity. }
    rewrite -Hj. iExact "H".
  Qed.

End ladder.

(* ===================================================================== *)
(* §4 THE MINT.                                                           *)
(* ===================================================================== *)

Section mint.
  Context `{!riscvGS Σ}.

  (* One stack.  The claim [kvm_M_mint] minted plus the page kvminit handed
     out ARE the whole KSTACK(i) page owned at its virtual address, KT1 --
     512 doubleword slots below KSTACK(i)+4096, which is the sp a fresh
     process's context is parked at ([SpecForkretParkPaid]). *)
  Lemma kstack_own_intro (i : nat) (ppn : mword 44) :
    (i < 64)%nat -> node_kdata ppn ->
    kmap_at (kstack_vpn i) ppn KP_rw -∗
    page_own (page_base ppn) -∗
    stack_own (KTR := KT1) (add_vec (kstack_va i) (mword_of_int 4096)) 512.
  Proof.
    intros Hi Hkd. iIntros "#Hcl Hpg".
    rewrite /page_own.
    replace 4096%nat with (8 * 512)%nat by lia.
    iDestruct (bwin_words8 (page_base ppn) 512
                 ltac:(intros o Ho Hd; apply page_base_aligned8;
                       [exact Hkd | lia | exact Hd])
                 with "Hpg") as (ws) "[%Hlen Hws]".
    iAssert ([∗ list] k ↦ w ∈ ws,
               word_pointsto (KTR := KT1) (pa_add (kstack_va i) (8 * k)%nat)
                 (DfracOwn 1) w)%I with "[Hws]" as "Hws".
    { iApply (big_sepL_impl with "Hws").
      iIntros "!>" (k w Hk) "Hw".
      apply lookup_lt_Some in Hk.
      iApply (kstack_word_rekey i ppn (8 * k)%nat w Hi Hkd ltac:(lia)
                (kstk_dvd8 k) with "Hcl Hw"). }
    rewrite -pa_add_4096_add_vec.
    iApply (stack_own_of_words KT1 (kstack_va i) 512 ws Hlen with "Hws").
  Qed.

  (* THE BANK: all 64 stacks, at KT1.  No [pas] argument -- the addresses
     KSTACK(i) are static, and the physical pages behind them are already
     forgotten by [stack_own]'s existential contents.  (An argument the body
     does not mention would be a phantom; durable-notes.) *)
  Definition kstack_bank : iProp Σ :=
    ([∗ list] i ∈ seq 0 64,
       stack_own (KTR := KT1) (add_vec (kstack_va i) (mword_of_int 4096)) 512)%I.

  Lemma kstack_bank_intro (pas : nat -> mword 44) :
    kvm_pas_ok pas ->
    ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw) -∗
    ([∗ list] i ∈ seq 0 64, page_own (page_base (pas i))) -∗
    kstack_bank.
  Proof.
    intros Hok. iIntros "#Hcl Hpg". rewrite /kstack_bank.
    iApply (big_sepL_impl with "Hpg").
    iIntros "!>" (k i Hk) "Hp".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iDestruct (big_sepL_lookup _ (seq 0 64) k (0 + k)%nat with "Hcl") as "Hci".
    { apply lookup_seq. split; [reflexivity | lia]. }
    iApply (kstack_own_intro (0 + k)%nat (pas (0 + k)%nat) ltac:(lia)
              (Hok (0 + k)%nat ltac:(lia)) with "Hci Hp").
  Qed.

End mint.
