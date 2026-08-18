(* KptGoodb.v -- the THREE FOOTPRINT CERTIFICATES the per-node walk needs
   for the two PTE tests, and the exec layer never did.

   [WpDecodeBridge.goodb] certifies "this stretch reads only registers in
   [D], writes none, touches no memory".  The swp layer needs one for
   [pte_is_invalid] and one for [check_PTE_permission] at every PTE the
   walk looks at; the exec layer never did, because it evaluates against a
   reference state.  Neither test is register-free IN GENERAL:

     - [pte_is_invalid] reads [menvcfg] on the reserved-encoding branch
       (V=1, R=0, W=1, X=0) and [misa] on the [not (pbmt matches)] branch
       (via [currentlyEnabled Ext_Svpbmt] -> [Ext_Sv39] -> [Ext_S]), and
       again on the Svnapot / Svrsw60t59b / PBMTE probes of the
       reserved-bits group;
     - [check_PTE_permission] reads [menvcfg] on its shadow-stack branch
       (R=0, W=1, X=0).

   At a KERNEL PTE every one of those branches is dead, but killing them
   needs the WORD's own bits, so each certificate is conditioned exactly
   as a caller can supply it:

     - at the claim's LEAF, on the canonical class ([pte_canon] equal to
       [mk_pte ppn (kperm_flags kp)]): the flag byte is one of the four
       A/D variants of 0x0B / 0x07 and the extension field is zero, so
       both terms are register-free and one [vm_compute] per variant
       settles it (the [goodb] twin of [KptPt.kperm_inv_red]);
     - at the two INTERNAL levels, whose words no caller can name, on
       [pte_valid] + [pte_ptr] -- NOT on [pte_ptr] alone.  A non-leaf word
       with PBMT = 'b"11" fails [page_based_mem_type_forwards_matches] and
       the Svpbmt probe then really does read [misa], so the [pte_ptr]-only
       form is FALSE.  Validity is what rules it out: [pte_valid]
       quantifies over ALL states, and [PtTree.pte_ptr_ext_zero] reads the
       whole 10-bit extension field off it, PBMT included.

   [check_PTE_permission]'s remaining non-register obstacle is its
   [is_shadow_stack_access] tail, which for a payload other than Data /
   ShadowStack is an [internal_error] rather than a [Ret]; the certificate
   takes the caller's own [goodb] for that call (which every S-mode
   translation premise list already carries) and discharges the error arms
   from it.                                                              *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte PtAdBits Pt4kWalk PtTree KptPt KMap KptTree.
Require Import WpDecodeBridge.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE INTERNAL LEVELS: a VALID POINTER word's invalidity test is      *)
(*    register-free.                                                     *)
(* ===================================================================== *)

(* the raw form, over the flag byte and the extension field.  [rewrite Hnl]
   BEFORE the bit rewrites is load-bearing: the reserved-bits group tests
   [pte_is_non_leaf f] again, and left symbolic there it makes the whole
   term stuck -- [vm_compute] then does not finish (measured: > 2 min). *)
Lemma goodb_piv_ptr (f : mword 8) (e : mword 10) (D : register -> bool)
    (s : mstate) :
  pte_is_non_leaf f = true -> e = (zeros' 10 : mword 10) ->
  goodb D (pte_is_invalid f e) s = true.
Proof.
  intros Hnl ->.
  pose proof Hnl as Hbits.
  unfold pte_is_non_leaf in Hbits.
  apply andb_prop in Hbits as [HX Hbits]. apply andb_prop in Hbits as [HW HR].
  apply eq_vec_true_iff in HX. apply eq_vec_true_iff in HW.
  apply eq_vec_true_iff in HR.
  unfold pte_is_invalid. rewrite Hnl. rewrite HX, HW, HR.
  destruct (mword1_cases (_get_PTE_Flags_V f)) as [HV | HV]; rewrite HV;
  destruct (mword1_cases (_get_PTE_Flags_A f)) as [HA | HA]; rewrite HA;
  destruct (mword1_cases (_get_PTE_Flags_D f)) as [HD | HD]; rewrite HD;
  destruct (mword1_cases (_get_PTE_Flags_U f)) as [HU | HU]; rewrite HU;
  vm_compute; reflexivity.
Qed.

(* ...and the form a walk holds: [ptree_maps]' pointer conjuncts. *)
Lemma pte_ptr_goodb_invalid (w : mword 64) :
  pte_valid w -> pte_ptr w ->
  forall (D : register -> bool) (s : mstate),
    goodb D (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
               (ext_bits_of_PTE w)) s = true.
Proof.
  intros Hv Hp D s.
  apply (goodb_piv_ptr _ _ D s Hp (pte_ptr_ext_zero w Hv Hp)).
Qed.

(* ===================================================================== *)
(* §2 THE CLAIM'S LEAF: every A/D variant of a class-keyed kernel leaf.   *)
(* ===================================================================== *)

Lemma kperm_variant_goodb_invalid (ppn : mword 44) (pc : kperm) (a d : mword 1)
    (D : register -> bool) (s : mstate) :
  goodb D (pte_is_invalid
             (Mk_PTE_Flags (subrange_vec_dec
                (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) 7 0))
             (ext_bits_of_PTE (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d))) s
  = true.
Proof.
  rewrite (kperm_variant_flags ppn pc a d).
  rewrite (kperm_variant_ext ppn pc a d).
  destruct pc; destruct (mword1_cases a) as [-> | ->];
    destruct (mword1_cases d) as [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma kperm_variant_goodb_check (ppn : mword 44) (pc : kperm) (a d : mword 1)
    (acc : MemoryAccessType mem_payload) (mxr do_sum : bool)
    (D0 : register -> bool) (s0 : mstate) :
  goodb D0 (is_shadow_stack_access acc) s0 = true ->
  forall (D : register -> bool) (s : mstate),
    goodb D (check_PTE_permission acc Supervisor mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec
                  (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) 7 0))
               (ext_bits_of_PTE (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) tt) s
    = true.
Proof.
  intros Hss D s.
  rewrite (kperm_variant_flags ppn pc a d).
  rewrite (kperm_variant_ext ppn pc a d).
  revert Hss.
  destruct acc as [m | m | [[aq rl] m] | [[aq rl] m] | [[[[op aq] rl] m1] m2] | u | c];
    try destruct m; try destruct m1; try destruct m2; try destruct u;
    intros Hss;
    try (cbn [goodb is_shadow_stack_access] in Hss; discriminate Hss);
    destruct pc; destruct (mword1_cases a) as [-> | ->];
      destruct (mword1_cases d) as [-> | ->]; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §3 THE CANON-KEYED FORMS, which is how the per-node walk names its     *)
(*    leaf: the invariant is opened per read, so no caller can name the   *)
(*    A/D bits and every leaf fact is stated at [pte_canon] equality.     *)
(* ===================================================================== *)

Lemma kperm_canon_goodb_invalid (ppn : mword 44) (pc : kperm) (w : mword 64) :
  pte_canon w = pte_canon (mk_pte ppn (kperm_flags pc)) ->
  forall (D : register -> bool) (s : mstate),
    goodb D (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
               (ext_bits_of_PTE w)) s = true.
Proof.
  intros Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
  apply kperm_variant_goodb_invalid.
Qed.

Lemma kperm_canon_goodb_check (ppn : mword 44) (pc : kperm) (w : mword 64)
    (acc : MemoryAccessType mem_payload)
    (D0 : register -> bool) (s0 : mstate) :
  goodb D0 (is_shadow_stack_access acc) s0 = true ->
  pte_canon w = pte_canon (mk_pte ppn (kperm_flags pc)) ->
  forall (mxr do_sum : bool) (D : register -> bool) (s : mstate),
    goodb D (check_PTE_permission acc Supervisor mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec w 7 0))
               (ext_bits_of_PTE w) tt) s = true.
Proof.
  intros Hss Hc mxr do_sum.
  destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
  apply (kperm_variant_goodb_check ppn pc a d acc mxr do_sum D0 s0 Hss).
Qed.

(* ===================================================================== *)
(* §4 THE FETCH'S TWO PURE PROBES.  [RiscvFetchExec] proves the [exec]    *)
(*    twins ([exec_effectivePrivilege_fetch] / [exec_is_shadow_stack_     *)
(*    fetch]); at [InstructionFetch tt] both terms are a bare [returnM],  *)
(*    so their footprint certificates hold at EVERY [D] and every state.  *)
(*    (Their natural home is beside the exec twins; they live here        *)
(*    because RiscvFetchExec is a bottom-of-tree file.)                   *)
(* ===================================================================== *)

Lemma goodb_effectivePrivilege_fetch (D : register -> bool) (m : mword 64)
    (p : Privilege) (s : mstate) :
  goodb D (effectivePrivilege (InstructionFetch tt) m p) s = true.
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma goodb_is_shadow_stack_fetch (D : register -> bool) (s : mstate) :
  goodb D (is_shadow_stack_access (InstructionFetch tt)) s = true.
Proof. reflexivity. Qed.
