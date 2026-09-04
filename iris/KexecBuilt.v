(* KexecBuilt.v -- THE ARGUMENT BLOCK'S ALGEBRA, AND THE FACT BUNDLE THE
   KEXEC CONE CARRIES TO ITS ENTRY-POINT HOLE.

   TWO THINGS LIVE HERE, and they are together for one reason: both have to
   be nameable INSIDE the kernel-side kexec proofs (ProofKexecSeam.v,
   ProofKexecC.v, ProofKexecD.v), which sit far below [SpecKexecAU.v] in
   the dependency order -- [SpecKexecAU] pulls the whole [SpecSysOpenAU] /
   [FsAbs] atomic-update cone, and no kexec block proof may depend on that.
   So the vocabulary the loop invariants are stated in has to be HERE, and
   [KexecImageAlg.v] -- which is above [SpecKexecAU] and may name
   [kexec_args_at] / [kexec_stack_at] -- carries the bridge rows that turn
   these into the contract's own predicates.  The [kxb_] prefix marks
   exactly the predicates that have a twin over there:

       kxb_ustack    = SpecKexecAU.kexec_ustack
       kxb_arg_addr  = SpecKexecAU.kexec_arg_addr
       kxb_args_at   = SpecKexecAU.kexec_args_at
       kxb_stack_at  = SpecKexecAU.kexec_stack_at

   and the twins are DEFINITIONALLY the same predicate, so each bridge is
   the identity ([KexecImageAlg] §5).

   §1-§3 are the push geometry and the zero fill: [kxc_sp] strictly
   decreases by more than the string it just made room for, so the
   copyouts the argv loop performs are pairwise disjoint and the pointer
   vector misses every string; the stack page comes out of [umem_grow] all
   zeros; and every copyout lands inside [kxb_arg_addr], so the zero
   conjunct survives.  (This section used to be [KexecImageAlg] §4, moved
   down whole so the argv loop can name it.)

   §4 is [kexec_built]: the fact bundle the kexec cone's [Q]-premise is
   asked at, stated ONCE so that [ProofKexecD.kxd_phaseD],
   [ProofKexec.kxc_d_tail] / [kxc_cd] and [ProofKexecPin] all quote the
   same Prop.  Read its own header for what it does and does NOT yet
   carry.                                                                  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import RiscvExtras.     (* [uint_unsigned]                           *)
Require Import UserBits.        (* [uint_add_vec_int_small]                  *)
Require Import PageGeom.        (* [PGSIZE]                                  *)
Require Import UserPtTree.      (* [umem_write], [umem_wr], [umem_grow],
                                   [uva_live]                               *)
Require Import ProcDefs.        (* [ustate], [us_M], [us_V], [pv_sz]         *)
Require Import SpecKexec.       (* [kxc_sp], [kxc_sp_final], [kxc_round16],
                                   [kxc_stack_ok]                           *)
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  TWO MAP LAWS AND THE PAGE ROUNDING, needed below (and re-exported  *)
(*      to [KexecImageAlg], which used to own them).                       *)
(* ====================================================================== *)

(* [umem_grow] only ADDS keys ([∪] is left-biased), so nothing already
   established can move. *)
Lemma umem_grow_lookup_old (M : gmap Z (bv 8)) (sz a : Z) (b : bv 8) :
  M !! a = Some b -> umem_grow M sz !! a = Some b.
Proof. intros H. unfold umem_grow. apply lookup_union_Some_l. exact H. Qed.

Lemma umem_grow_lookup_zero (M : gmap Z (bv 8)) (sz a : Z) :
  M !! a = None -> uva_live sz a -> umem_grow M sz !! a = Some (bv_0 8).
Proof.
  intros Hnone Hlive. unfold umem_grow.
  rewrite (lookup_union_r M _ a Hnone).
  apply lookup_gset_to_gmap_Some.
  split; [apply elem_of_live_set, Hlive | reflexivity].
Qed.

Lemma pgroundup_nonneg (sz : Z) : 0 <= sz -> 0 <= pgroundup sz.
Proof.
  intros H. unfold pgroundup.
  apply Z.mul_nonneg_nonneg; [| lia].
  apply Z.div_pos; lia.
Qed.

Lemma pgroundup_mod (sz : Z) : pgroundup sz `mod` 4096 = 0.
Proof. unfold pgroundup. apply Z.mod_mul. lia. Qed.

Lemma pgroundup_aligned (sz : Z) : sz `mod` 4096 = 0 -> pgroundup sz = sz.
Proof.
  intros H. unfold pgroundup.
  pose proof (Z.div_mod sz 4096 ltac:(lia)) as Hdm. rewrite H in Hdm.
  replace (sz + 4095) with ((sz / 4096) * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia.
  assert (H4 : 4095 / 4096 = 0) by reflexivity.
  rewrite H4. lia.
Qed.

(* ====================================================================== *)
(*  1.  THE PUSH GEOMETRY                                                 *)
(* ====================================================================== *)

Lemma kxc_round16_le (x : Z) : kxc_round16 x <= x.
Proof.
  unfold kxc_round16. pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

Lemma kxc_sp_gap (top : Z) (alen : nat -> nat) (i : nat) :
  kxc_sp top alen (S i) + Z.of_nat (alen i) < kxc_sp top alen i.
Proof.
  simpl.
  pose proof (kxc_round16_le (kxc_sp top alen i - (Z.of_nat (alen i) + 1))).
  lia.
Qed.

Lemma kxc_sp_mono (top : Z) (alen : nat -> nat) (i k : nat) :
  (i <= k)%nat -> kxc_sp top alen k <= kxc_sp top alen i.
Proof.
  intros H. induction H as [| k Hk IH]; [lia |].
  pose proof (kxc_sp_gap top alen k). pose proof (Nat2Z.is_nonneg (alen k)).
  lia.
Qed.

Lemma kxc_sp_final_gap (top : Z) (alen : nat -> nat) (na : nat) :
  kxc_sp_final top alen na + 8 * (Z.of_nat na + 1) <= kxc_sp top alen na.
Proof.
  unfold kxc_sp_final.
  pose proof (kxc_round16_le
                (kxc_sp top alen na - 8 * (Z.of_nat na + 1))).
  lia.
Qed.

(* string [i]'s bytes are strictly below every earlier string's sp... *)
Lemma kxc_sp_str_disj (top : Z) (alen : nat -> nat) (i k j : nat) :
  (i < k)%nat ->
  forall m, (m < alen k + 1)%nat ->
    kxc_sp top alen (S i) + Z.of_nat j <> kxc_sp top alen (S k) + Z.of_nat m.
Proof.
  intros Hik m Hm.
  pose proof (kxc_sp_gap top alen k).
  pose proof (kxc_sp_mono top alen (S i) k ltac:(lia)).
  pose proof (Nat2Z.is_nonneg j).
  lia.
Qed.

(* ...and the pointer vector is strictly below every string. *)
Lemma kxc_sp_vec_disj (top : Z) (alen : nat -> nat) (na i j : nat) :
  (i < na)%nat ->
  forall m, (m < 8 * (na + 1))%nat ->
    kxc_sp top alen (S i) + Z.of_nat j
    <> kxc_sp_final top alen na + Z.of_nat m.
Proof.
  intros Hi m Hm.
  pose proof (kxc_sp_final_gap top alen na).
  pose proof (kxc_sp_mono top alen (S i) na ltac:(lia)).
  pose proof (Nat2Z.is_nonneg j).
  lia.
Qed.

(* ====================================================================== *)
(*  2.  THE ADDRESSES THE ARGUMENT BLOCK OCCUPIES                         *)
(* ====================================================================== *)

(* [SpecKexecAU.kexec_ustack] / [kexec_arg_addr], verbatim -- see this
   file's header for why they are spelled twice. *)
Definition kxb_ustack (top : Z) (alen : nat -> nat) (na i : nat) : Z :=
  if decide (i < na)%nat then kxc_sp top alen (S i) else 0.

Definition kxb_arg_addr (top : Z) (alen : nat -> nat) (na : nat) (a : Z) : Prop :=
  (exists i, (i < na)%nat
     /\ kxc_sp top alen (S i) <= a <= kxc_sp top alen (S i) + Z.of_nat (alen i))
  \/ (kxc_sp_final top alen na <= a < kxc_sp_final top alen na + 8 * (Z.of_nat na + 1)).

(* THE ARGV LOOP'S OWN ZONE, at index [k]: the STRINGS ALONE, and only the
   [k] of them the loop has pushed so far.  [kxb_arg_addr] is not usable as
   the loop's invariant -- its pointer-vector disjunct is keyed by the
   FINAL argument count, which moves the vector's address every time [k]
   does, so an invariant stated at [kxb_arg_addr top alen k] is not
   monotone in [k].  This one is ([kxb_str_zone_mono]), and it becomes
   [kxb_arg_addr]'s left disjunct at the exit ([kxb_str_zone_arg]). *)
Definition kxb_str_zone (top : Z) (alen : nat -> nat) (k : nat) (a : Z) : Prop :=
  exists i, (i < k)%nat
    /\ kxc_sp top alen (S i) <= a <= kxc_sp top alen (S i) + Z.of_nat (alen i).

Lemma kxb_str_zone_mono (top : Z) (alen : nat -> nat) (k k' : nat) (a : Z) :
  (k <= k')%nat -> kxb_str_zone top alen k a -> kxb_str_zone top alen k' a.
Proof. intros Hk [i [Hi Ha]]. exists i. split; [lia | exact Ha]. Qed.

Lemma kxb_str_zone_arg (top : Z) (alen : nat -> nat) (na : nat) (a : Z) :
  kxb_str_zone top alen na a -> kxb_arg_addr top alen na a.
Proof. intros H. left. exact H. Qed.

(* the string the loop pushes at index [k] IS in the zone at [S k] *)
Lemma kxb_str_zone_push (top : Z) (alen : nat -> nat) (k j : nat) :
  (j < alen k + 1)%nat ->
  kxb_str_zone top alen (S k) (kxc_sp top alen (S k) + Z.of_nat j).
Proof. intros Hj. exists k. split; [lia | lia]. Qed.

(* every byte a copyout touches is inside [kxb_arg_addr] *)
Lemma kxb_arg_addr_str (top : Z) (alen : nat -> nat) (na i j : nat) :
  (i < na)%nat -> (j < alen i + 1)%nat ->
  kxb_arg_addr top alen na (kxc_sp top alen (S i) + Z.of_nat j).
Proof. intros Hi Hj. left. exists i. split; [exact Hi | lia]. Qed.

Lemma kxb_arg_addr_vec (top : Z) (alen : nat -> nat) (na j : nat) :
  (j < 8 * (na + 1))%nat ->
  kxb_arg_addr top alen na (kxc_sp_final top alen na + Z.of_nat j).
Proof. intros Hj. right. lia. Qed.

(* ====================================================================== *)
(*  3.  THE ZERO FILL, AND THE BYTES THE COPYOUTS PUT BACK                *)
(* ====================================================================== *)

Definition kx_page_zero (top : Z) (M : gmap Z (bv 8)) : Prop :=
  forall a, top - PGSIZE <= a < top -> M !! a = Some (bv_0 8).

(* uvmalloc to [sz1 = top] makes the top page live, and it held nothing
   before ([sz] was at most [top - 2*PGSIZE]), so every one of its bytes
   reads zero. *)
Lemma kx_page_zero_grow (M : gmap Z (bv 8)) (top : Z) :
  top `mod` PGSIZE = 0 -> PGSIZE <= top ->
  (forall a, top - PGSIZE <= a < top -> M !! a = None) ->
  kx_page_zero top (umem_grow M top).
Proof.
  intros Halign Hge Hfresh a Ha. unfold PGSIZE in *.
  apply umem_grow_lookup_zero; [exact (Hfresh a Ha) |].
  unfold uva_live. rewrite (pgroundup_aligned top Halign). lia.
Qed.

(* THE SURVIVING ZEROS: [kxb_stack_at]'s second conjunct, carried through
   the copyouts.  [P] is instantiated with [kxb_str_zone] inside the argv
   loop and with [kxb_arg_addr] at its exit. *)
Definition kx_zero_except (top : Z) (P : Z -> Prop) (M : gmap Z (bv 8)) : Prop :=
  forall a, top - PGSIZE <= a < top -> ~ P a -> M !! a = Some (bv_0 8).

Lemma kx_zero_except_of_page (top : Z) (P : Z -> Prop) (M : gmap Z (bv 8)) :
  kx_page_zero top M -> kx_zero_except top P M.
Proof. intros H a Ha _. exact (H a Ha). Qed.

(* WEAKENING THE EXCEPTION SET: what the argv loop's step needs twice --
   once to move its own invariant from [k] to [S k], once at the exit to
   turn the string zone into [kxb_arg_addr]. *)
Lemma kx_zero_except_mono (top : Z) (P P' : Z -> Prop) (M : gmap Z (bv 8)) :
  (forall a, P a -> P' a) -> kx_zero_except top P M -> kx_zero_except top P' M.
Proof. intros Hsub H a Ha HnP'. apply H; [exact Ha |]. intro Hp. exact (HnP' (Hsub a Hp)). Qed.

Lemma kx_zero_except_write (top : Z) (P : Z -> Prop) (M : gmap Z (bv 8))
    (a : Z) (n : nat) (g : nat -> bv 8) :
  kx_zero_except top P M ->
  (forall j, (j < n)%nat -> P (a + Z.of_nat j)) ->
  kx_zero_except top P (umem_write M a n g).
Proof.
  intros Hz Hin va Hva HnP.
  assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)).
  { intros j Hj Heq. apply HnP. rewrite Heq. exact (Hin j Hj). }
  rewrite (umem_write_lookup_out M a n g va Hne). exact (Hz va Hva HnP).
Qed.

(* ---- the argument block, write by write ---- *)

(* the first two conjuncts of [kxb_args_at], after [k] strings *)
Definition kx_str_at (top : Z) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (k : nat) (M : gmap Z (bv 8)) : Prop :=
  (forall i j, (i < k)%nat -> (j < alen i)%nat ->
     M !! (kxc_sp top alen (S i) + Z.of_nat j) = Some (afun i j))
  /\ (forall i, (i < k)%nat ->
     M !! (kxc_sp top alen (S i) + Z.of_nat (alen i)) = Some (bv_0 8)).

Lemma kx_str_at_0 (top : Z) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) :
  kx_str_at top alen afun 0 M.
Proof. split; intros; exfalso; lia. Qed.

(* ONE PUSH: copyout of [alen k + 1] bytes (the string and its NUL) at
   [kxc_sp top alen (S k)].  The earlier strings sit strictly ABOVE this
   run ([kxc_sp_str_disj]), so they survive verbatim. *)
Lemma kx_str_at_step (top : Z) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (k : nat) (M : gmap Z (bv 8))
    (src : nat -> bv 8) :
  kx_str_at top alen afun k M ->
  (forall j, (j < alen k)%nat -> src j = afun k j) ->
  src (alen k) = bv_0 8 ->
  kx_str_at top alen afun (S k)
    (umem_write M (kxc_sp top alen (S k)) (alen k + 1) src).
Proof.
  intros [Hold Hnul] Hsrc Hsrcnul. split.
  - intros i j Hi Hj. destruct (decide (i = k)) as [-> | Hne].
    + rewrite (umem_write_lookup_in M (kxc_sp top alen (S k))
                 (alen k + 1) src j ltac:(lia)).
      rewrite (Hsrc j Hj). reflexivity.
    + rewrite (umem_write_lookup_out M (kxc_sp top alen (S k))
                 (alen k + 1) src _
                 (kxc_sp_str_disj top alen i k j ltac:(lia))).
      exact (Hold i j ltac:(lia) Hj).
  - intros i Hi. destruct (decide (i = k)) as [-> | Hne].
    + rewrite (umem_write_lookup_in M (kxc_sp top alen (S k))
                 (alen k + 1) src (alen k) ltac:(lia)).
      rewrite Hsrcnul. reflexivity.
    + rewrite (umem_write_lookup_out M (kxc_sp top alen (S k))
                 (alen k + 1) src _
                 (kxc_sp_str_disj top alen i k (alen i) ltac:(lia))).
      exact (Hnul i ltac:(lia)).
Qed.

(* [SpecKexecAU.kexec_args_at] / [kexec_stack_at], verbatim (header). *)
Definition kxb_args_at (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) : Prop :=
  (forall i j, (i < na)%nat -> (j < alen i)%nat ->
     M !! (kxc_sp top alen (S i) + Z.of_nat j) = Some (afun i j))
  /\ (forall i, (i < na)%nat ->
        M !! (kxc_sp top alen (S i) + Z.of_nat (alen i)) = Some (bv_0 8))
  /\ (forall i k, (i <= na)%nat -> (k < 8)%nat ->
        M !! (kxc_sp_final top alen na + 8 * Z.of_nat i + Z.of_nat k)
        = bv_to_little_endian 8 8 (kxb_ustack top alen na i) !! k).

Definition kxb_stack_at (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) : Prop :=
  kxc_stack_ok top (top - PGSIZE) alen na
  /\ (forall a, top - PGSIZE <= a < top -> ~ kxb_arg_addr top alen na a ->
        M !! a = Some (bv_0 8)).

Lemma kxb_stack_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) :
  kxc_stack_ok top (top - PGSIZE) alen na ->
  kx_zero_except top (kxb_arg_addr top alen na) M ->
  kxb_stack_at top alen na M.
Proof. intros Hok Hz. split; [exact Hok | exact Hz]. Qed.

(* THE LAST PUSH: the [8 * (na + 1)]-byte pointer vector, at
   [kxc_sp_final], strictly below every string ([kxc_sp_vec_disj]).  Its
   [i]-th word is [kxb_ustack top alen na i], little-endian, which is
   exactly what [kxb_args_at]'s third conjunct asks for. *)
Lemma kxb_args_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) (src : nat -> bv 8) :
  kx_str_at top alen afun na M ->
  (forall i k, (i <= na)%nat -> (k < 8)%nat ->
     bv_to_little_endian 8 8 (kxb_ustack top alen na i) !! k
     = Some (src (8 * i + k)%nat)) ->
  kxb_args_at top alen na afun
    (umem_write M (kxc_sp_final top alen na) (8 * (na + 1)) src).
Proof.
  intros [Hold Hnul] Hvec. split; [| split].
  - intros i j Hi Hj.
    rewrite (umem_write_lookup_out M (kxc_sp_final top alen na)
               (8 * (na + 1)) src _
               (kxc_sp_vec_disj top alen na i j Hi)).
    exact (Hold i j Hi Hj).
  - intros i Hi.
    rewrite (umem_write_lookup_out M (kxc_sp_final top alen na)
               (8 * (na + 1)) src _
               (kxc_sp_vec_disj top alen na i (alen i) Hi)).
    exact (Hnul i Hi).
  - intros i k Hi Hk.
    replace (kxc_sp_final top alen na + 8 * Z.of_nat i + Z.of_nat k)
      with (kxc_sp_final top alen na + Z.of_nat (8 * i + k)%nat) by lia.
    rewrite (umem_write_lookup_in M (kxc_sp_final top alen na)
               (8 * (na + 1)) src (8 * i + k)%nat ltac:(lia)).
    symmetry. exact (Hvec i k Hi Hk).
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE COPYOUT CONTRACT'S OWN SHAPE.  Everything above is stated on        *)
(*  [umem_write] -- integer-keyed, inside one page.  What a copyout POSTS   *)
(*  is [umem_wr], keyed by [uint (add_vec_int dstva j)], which does not     *)
(*  have to be linear in general.  Under the no-wrap bound the caller       *)
(*  already carries ([uint dstva + n <= uint sz1 < 2^38]) the two runs ARE  *)
(*  the same map, and this is the one row that says so.                     *)
(* ---------------------------------------------------------------------- *)
Lemma umem_wr_write (M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) :
  (forall i, (i < n)%nat ->
     uint (add_vec_int dstva (Z.of_nat i)) = (uint dstva + Z.of_nat i)%Z) ->
  umem_wr M dstva n src = umem_write M (uint dstva) n src.
Proof.
  intros Hlin.
  exact (eq_sym (umem_wr_step M dstva 0 n src (uint dstva)
                   (fun i Hi => Hlin i Hi))).
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE TWO STEPS THE ARGV LOOP ACTUALLY TAKES, packaged so the block       *)
(*  proofs quote one row each.                                              *)
(* ---------------------------------------------------------------------- *)

(* the no-wrap side condition, from the bound the caller already has *)
Lemma kx_wr_linear (dstva : mword 64) (n : nat) :
  (uint dstva + Z.of_nat n <= 18446744073709551616)%Z ->
  forall i, (i < n)%nat ->
    uint (add_vec_int dstva (Z.of_nat i)) = (uint dstva + Z.of_nat i)%Z.
Proof.
  intros Hfit i Hi.
  rewrite uint_unsigned in Hfit.
  rewrite (uint_unsigned (add_vec_int dstva (Z.of_nat i))).
  rewrite (uint_unsigned dstva).
  apply uint_add_vec_int_small; lia.
Qed.

Lemma mword0_bv0 : (mword_of_int 0 : mword 8) = bv_0 8.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ONE ARGUMENT PUSHED: copyout of [alen k + 1] bytes at [kxc_sp top alen
   (S k)].  Both halves of the loop invariant step together. *)
Lemma kx_argv_push (top : Z) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (k : nat) (M : gmap Z (bv 8)) (dstva : mword 64) :
  uint dstva = kxc_sp top alen (S k) ->
  (forall i, (i < S (alen k))%nat ->
     uint (add_vec_int dstva (Z.of_nat i)) = (uint dstva + Z.of_nat i)%Z) ->
  afun k (alen k) = (mword_of_int 0 : mword 8) ->
  kx_str_at top alen afun k M ->
  kx_zero_except top (kxb_str_zone top alen k) M ->
  kx_str_at top alen afun (S k) (umem_wr M dstva (S (alen k)) (afun k))
  /\ kx_zero_except top (kxb_str_zone top alen (S k))
       (umem_wr M dstva (S (alen k)) (afun k)).
Proof.
  intros Hdst Hlin Hnul Hstr Hzero.
  rewrite (umem_wr_write M dstva (S (alen k)) (afun k) Hlin), Hdst.
  replace (S (alen k)) with (alen k + 1)%nat by lia.
  split.
  - apply kx_str_at_step;
      [exact Hstr | intros j _; reflexivity | rewrite Hnul; exact mword0_bv0].
  - apply kx_zero_except_write.
    + apply (kx_zero_except_mono top (kxb_str_zone top alen k));
        [intros a Ha; exact (kxb_str_zone_mono top alen k (S k) a ltac:(lia) Ha)
        | exact Hzero].
    + intros j Hj. apply kxb_str_zone_push. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(*  A WORD'S BYTES ARE ITS LITTLE-ENDIAN ENCODING.  [kxb_args_at]'s third   *)
(*  conjunct is spelled with stdpp's [bv_to_little_endian] (the contract's  *)
(*  own spelling, shared with [SpecSysExecAU]'s window rows); the frame     *)
(*  slots the argv loop wrote hand their bytes over as [nth_byte].  Below   *)
(*  eight bytes the two agree on the nose -- the 64-bit wrap [mword_of_int] *)
(*  applies is invisible to byte [k] for [k < 8].                           *)
(* ---------------------------------------------------------------------- *)
Lemma bv_le_nth_byte (z : Z) (k : nat) :
  (k < 8)%nat ->
  bv_to_little_endian 8 8 z !! k = Some (nth_byte (mword_of_int z : mword 64) k).
Proof.
  intros Hk.
  assert (Hlk : bv_to_little_endian 8 8 z !! k
                = Some (Z_to_bv 8 (Z.land (z ≫ (Z.of_nat k * 8)) (Z.ones 8)))).
  { unfold bv_to_little_endian. rewrite list_lookup_fmap.
    change (Z.of_N 8) with 8.
    assert (Hz : Z_to_little_endian 8 8 z !! k
                 = Some (Z.land (z ≫ (Z.of_nat k * 8)) (Z.ones 8))).
    { apply (Z_to_little_endian_lookup_Some 8 8 z k _ ltac:(lia) ltac:(lia)).
      split; [lia | reflexivity]. }
    rewrite Hz. reflexivity. }
  rewrite Hlk. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned.
  unfold nth_byte. rewrite bv_extract_unsigned, moi64_unsigned.
  rewrite Z.land_ones by lia.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (Z.ones 8) with 255.
  replace (Z.of_N (8 * N.of_nat k)) with (Z.of_nat k * 8) by lia.
  set (n := Z.of_nat k).
  assert (Hn : 0 <= n <= 7) by (unfold n; lia).
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_mod by lia.
  set (q := z / 18446744073709551616).
  assert (Hpow : 2 ^ (64 - n * 8) * 2 ^ (n * 8) = 18446744073709551616).
  { rewrite <- Z.pow_add_r by lia.
    replace (64 - n * 8 + n * 8) with 64 by lia. reflexivity. }
  assert (Hzq : z `mod` 18446744073709551616
                = z + (- (2 ^ (64 - n * 8) * q)) * 2 ^ (n * 8)).
  { pose proof (Z.div_mod z 18446744073709551616 ltac:(lia)) as Hdm.
    fold q in Hdm.
    replace ((- (2 ^ (64 - n * 8) * q)) * 2 ^ (n * 8))
      with (- (q * (2 ^ (64 - n * 8) * 2 ^ (n * 8)))) by ring.
    rewrite Hpow. lia. }
  rewrite Hzq.
  rewrite Z.div_add by (apply Z.pow_nonzero; lia).
  replace (- (2 ^ (64 - n * 8) * q)) with ((- (2 ^ (56 - n * 8) * q)) * 256).
  2:{ replace ((- (2 ^ (56 - n * 8) * q)) * 256)
        with (- (q * (2 ^ (56 - n * 8) * 256))) by ring.
      replace 256 with (2 ^ 8) by reflexivity.
      rewrite <- Z.pow_add_r by lia.
      replace (56 - n * 8 + 8) with (64 - n * 8) by lia. ring. }
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

(* THE CLOSING COPYOUT: the [8 * (na + 1)]-byte pointer vector.  Its run is
   strictly below every string ([kxc_sp_vec_disj]), so the strings survive
   verbatim, and its own bytes are inside [kxb_arg_addr]'s right disjunct,
   so the zero fill widens from the string zone to the whole argument
   block.  [src] is UNCONSTRAINED here -- see [kexec_built]'s header for
   what that costs. *)
Lemma kx_argv_vec (top : Z) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (na : nat) (M : gmap Z (bv 8)) (dstva : mword 64) (src : nat -> bv 8) :
  uint dstva = kxc_sp_final top alen na ->
  (forall i, (i < 8 * S na)%nat ->
     uint (add_vec_int dstva (Z.of_nat i)) = (uint dstva + Z.of_nat i)%Z) ->
  (forall i k, (i <= na)%nat -> (k < 8)%nat ->
     src (8 * i + k)%nat
     = nth_byte (mword_of_int (kxb_ustack top alen na i) : mword 64) k) ->
  kx_str_at top alen afun na M ->
  kx_zero_except top (kxb_str_zone top alen na) M ->
  kxb_args_at top alen na afun (umem_wr M dstva (8 * S na)%nat src)
  /\ kx_zero_except top (kxb_arg_addr top alen na)
       (umem_wr M dstva (8 * S na)%nat src).
Proof.
  intros Hdst Hlin Hsrc Hstr Hzero.
  rewrite (umem_wr_write M dstva (8 * S na)%nat src Hlin), Hdst.
  replace (8 * S na)%nat with (8 * (na + 1))%nat by lia.
  split.
  - apply kxb_args_at_intro; [exact Hstr |].
    intros i k Hi Hk. rewrite (Hsrc i k Hi Hk). exact (bv_le_nth_byte _ k Hk).
  - apply kx_zero_except_write.
    + apply (kx_zero_except_mono top (kxb_str_zone top alen na));
        [intros a Ha; exact (kxb_str_zone_arg top alen na a Ha) | exact Hzero].
    + intros j Hj. apply kxb_arg_addr_vec. lia.
Qed.

(* ====================================================================== *)
(*  4.  THE FACT BUNDLE THE CONE CARRIES TO ITS ENTRY-POINT HOLE          *)
(* ====================================================================== *)

(*  [KexecOkQ.kexec_ok_q]'s success arm has a hole [Q entry U'], and after
    the S2 image threading the ONE site that pays it -- the commit block's
    [ld a4,-408(s0)] -- knows [U'] rather than quantifying over it.  This
    is what it knows ABOUT THE IMAGE IT BUILT, stated once so that
    [ProofKexecD.kxd_phaseD], [ProofKexec.kxc_d_tail] / [kxc_cd] and
    [ProofKexecPin]'s two premise sites all quote the same Prop instead of
    the unguarded [forall U', Q (kxq_entry ef) U'] they used to.

    WHAT IT CARRIES.  [sz1] is the size the run reached ([p->sz] at the
    exit), and over the stack page at [uint sz1] the argument block is
    exactly where [SpecKexecAU.kexec_args_at] says it is and every other
    byte of that page is zero ([kexec_stack_at]'s own second conjunct).
    The strings come from the argv loop's own invariant and the zeros from
    that invariant plus the closing pointer-vector copyout; [KexecImageAlg]
    §5 is the (identity) bridge to the contract's spelling of them.

    The pointer vector's own bytes are in it too, and that needed one new
    resource row: the closing block used to hand copyout its source through
    [StackBytes.slotsn_bytes_own] + [bytes_own_name], which FORGETS the
    ustack slots' values (the run comes back under an existential naming
    function).  [StackBytes.slotsn_bytes_named] is the same split at NAMED
    values, and [bv_le_nth_byte] above is the row that a word's [nth_byte]s
    ARE [bv_to_little_endian 8 8] of it.

    WHAT IT DOES NOT CARRY YET, and why -- both are the SAME missing
    ingredient.  [kexec_image_ok] also asks for [uimg_sub (elf_image f)]
    and for [uint sz1 = kexec_sz f], and each of those is a claim about the
    FILE's bytes.  The kernel-side cone cannot state either: the file's
    byte function is ∃-bound inside [IcacheInv.ic_loaded] (kexec holds the
    inode as [ProofKexecSeam.kxc_open], and [SpecKexecB2.kxc_load_peel] is
    what opens it, under an ∃ that is re-introduced at every readi).  So
    the loadseg window and the phdr loop's [kexec_sz_after] chain cannot be
    written down at [kxc_at_12c] / [kxc_ls_body] at all until that name is
    threaded through the open-inode bundle -- a sweep of its own.  Adding
    the two conjuncts here is then a local edit: this Prop gains the file's
    bytes as a parameter and two more rows, and the five premise sites gain
    them by name.                                                          *)
Definition kexec_built (sz1 : mword 64) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (U' : ustate) : Prop :=
  pv_sz (us_V U') = sz1
  /\ kxb_args_at (uint sz1) alen na afun (us_M U')
  /\ kxb_stack_at (uint sz1) alen na (us_M U').
