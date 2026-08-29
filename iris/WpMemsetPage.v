(* WpMemsetPage.v -- a PAGE-LEVEL S-mode WP for the kernel's [memset], tailored
   to zero/fill a whole 4096-byte page for kalloc/kfree.

   [wp_memset_page] wraps [wp_memset_s_full_kt] (CodeMemset.v): it DERIVES all
   of that lemma's ~30 per-byte side conditions (Sv39 canonicality, the identity
   translation, the gigapage svpn masks, the per-byte PMP TOR match, the pointer
   arithmetic) from the single fact that the page base [p] is RAM-resident and
   4096-aligned ([page_valid p]), and bridges [page_own p] to memset's per-byte
   buffer.  This is the last blocker for both the kalloc and kfree instruction
   proofs. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import WpMemsetS.
Require Import RiscvExtras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  Pure helpers: [add_vec] arithmetic, the address correspondence, and    *)
(*  the page-level geometry.                                               *)
(* ===================================================================== *)

(* [ms_a8]/[ms_pa] are the store's translated (identity) byte address; on
   64-bit both are the identity, and [ms_addr p j] is definitionally [pa_add p
   j].  Hence memset's per-byte address [ms_pa (ms_addr p j)] is exactly the
   [pa_add p j] that [page_own] tiles. *)
Lemma ms_a8_id (cur : mword 64) : ms_a8 cur = cur.
Proof.
  unfold ms_a8.
  assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H0.
  assert (Hc : add_vec cur (mword_of_int 0 : mword 64) = cur) by (exact (avi0 cur)).
  rewrite Hc. rewrite subrange_id. rewrite sign_extend'_id. reflexivity.
Qed.

Lemma ms_pa_id (cur : mword 64) : ms_pa cur = cur.
Proof.
  unfold ms_pa. change (0 * 1)%Z with 0%Z.
  rewrite avi0. rewrite zero_extend'_id. apply ms_a8_id.
Qed.

Lemma ms_pa_ms_addr (p : mword 64) (j : nat) : ms_pa (ms_addr p j) = pa_add p j.
Proof. rewrite ms_pa_id. apply ms_addr_pa_add. Qed.


(* ---- page validity gives RAM residency for the base and every byte ---- *)




(* STEP 3 (the crux): adding an in-page offset [j < 4096] to a 4096-aligned RAM
   base leaves the Sv39 VPN unchanged, because it only touches bits [11:0]. *)

(* The end-pointer loop compare is handled generically by [pa_add_cmp_bound]
   (ByteCursor.v), over an arbitrary byte count rather than a fixed page;
   the page users derive the [uint p + len < 2^64] bound from [page_valid]. *)

Section WpMemsetPage.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* Choice: a big-sep of per-element existentials over a [seq] yields a single
     witness FUNCTION indexed by the element.  (Elements of a [seq] are
     distinct, so the pointwise function-update introduces no collision.) *)
  Lemma bytes_choose (n : nat) :
    forall (start : nat) (P : nat -> bv 8 -> iProp Σ),
    ([∗ list] k ∈ seq start n, ∃ b : bv 8, P k b) ⊢
    ∃ f : nat -> bv 8, [∗ list] k ∈ seq start n, P k (f k).
  Proof.
    induction n as [|n IH]; intros start P.
    - iIntros "_". iExists (fun _ => bv_0 8). done.
    - cbn [seq]. rewrite big_sepL_cons.
      iIntros "[Hh Ht]". iDestruct "Hh" as (b) "Hh".
      iDestruct (IH (S start) P with "Ht") as (f) "Ht".
      iExists (fun k => if Nat.eq_dec k start then b else f k).
      rewrite big_sepL_cons. iSplitL "Hh".
      + destruct (Nat.eq_dec start start) as [_|Hne]; [ iExact "Hh" | done ].
      + iApply (big_sepL_impl with "Ht"). iIntros "!>" (k y Hy) "H".
        destruct (Nat.eq_dec y start) as [He|_].
        * exfalso. apply elem_of_list_lookup_2 in Hy. apply elem_of_seq in Hy. lia.
        * iExact "H".
  Qed.

  (* =================================================================== *)
  (*  THE PAGE-LEVEL memset WP.  memset(p, cval, 4096) fills a whole valid *)
  (*  page, consuming and returning [page_own p].  All of                  *)
  (*  wp_memset_s_full_kt's ~30 per-byte side conditions are DERIVED from   *)
  (*  [page_valid p]; the ~15 standard S-mode config facts are kept.        *)
  (* =================================================================== *)

  (* the same wrapper KEEPING the written bytes (walk's memset(page,0)
     feeds them to [zero_page_to_node]; [wp_memset_page]'s post forgets
     the contents) *)


End WpMemsetPage.
