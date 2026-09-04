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
Require Import UmodeAbi.        (* [uimg_sub]                                *)
Require Import ElfEnc.          (* [le_at], [ph_at], [eh_phnum]              *)
Require Import ElfFile.         (* the image semantics                       *)
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
(*  0.  Two spellings of the same zero byte                               *)
(* ====================================================================== *)

(* [ElfFile] writes the bss byte as [Z_to_bv 8 0]; the kernel tier writes
   the freshly-zeroed page's byte as [bv_0 8].  They are the same value,
   but not by [reflexivity] -- [bv_eq] is the bridge. *)
Lemma elf_zero_byte_bv0 : elf_zero_byte = bv_0 8.
Proof. unfold elf_zero_byte. apply bv_eq. reflexivity. Qed.

(* ====================================================================== *)
(*  1.  IMAGE ALGEBRA                                                     *)
(* ====================================================================== *)

Lemma uimg_sub_empty (M : gmap Z (bv 8)) : uimg_sub ∅ M.
Proof. intros a b Hb. rewrite lookup_empty in Hb. discriminate. Qed.

(* No disjointness side condition: [∪] is left-biased, so every entry of
   [m1 ∪ m2] is an entry of [m1] or of [m2]. *)
Lemma uimg_sub_union (m1 m2 M : gmap Z (bv 8)) :
  uimg_sub m1 M -> uimg_sub m2 M -> uimg_sub (m1 ∪ m2) M.
Proof.
  intros H1 H2 a b Hb.
  apply lookup_union_Some_raw in Hb as [Hb | [_ Hb]];
    [exact (H1 a b Hb) | exact (H2 a b Hb)].
Qed.

Lemma uimg_sub_segs_union {A : Type} `{EqDecision A}
    (g : A -> gmap Z (bv 8)) (ps : list A) (M : gmap Z (bv 8)) :
  (forall p, p ∈ ps -> uimg_sub (g p) M) -> uimg_sub (segs_union g ps) M.
Proof.
  intros H a b Hb.
  apply segs_union_lookup_inv in Hb as (p & Hp & Hg).
  exact (H p Hp a b Hg).
Qed.

Lemma uimg_sub_seg_map (f : elf_bytes) (p : elf_phdr) (M : gmap Z (bv 8)) :
  uimg_sub (seg_file_map f p) M -> uimg_sub (seg_zero_map p) M ->
  uimg_sub (seg_map f p) M.
Proof. unfold seg_map. apply uimg_sub_union. Qed.

Lemma uimg_sub_elf_image (f : elf_bytes) (M : gmap Z (bv 8)) :
  (forall p, p ∈ elf_loads f -> uimg_sub (seg_map f p) M) ->
  uimg_sub (elf_image f) M.
Proof. unfold elf_image. apply uimg_sub_segs_union. Qed.

(* THE FILE HALF, from the bytes the loop actually wrote.  The source
   index is [Z.to_nat (ep_offset p + j)] -- exactly the [f !!! ...] the
   loadseg step below writes, because [seg_file_bytes]'s [take]/[drop]
   window at list index [j] IS the file at [ep_offset p + j]
   ([ElfFile.seg_file_bytes_lookup]). *)
Lemma uimg_sub_seg_file_map (f : elf_bytes) (p : elf_phdr) (M : gmap Z (bv 8)) :
  phdr_ok f p ->
  (forall j, 0 <= j < ep_filesz p ->
     M !! (ep_vaddr p + j) = Some (f !!! Z.to_nat (ep_offset p + j))) ->
  uimg_sub (seg_file_map f p) M.
Proof.
  intros Hok Hb a b Ha.
  apply (proj1 (lookup_seg_file_map f p a b Hok)) in Ha as [Hrange Hf].
  pose proof (Hb (a - ep_vaddr p) ltac:(lia)) as HM.
  replace (ep_vaddr p + (a - ep_vaddr p)) with a in HM by lia.
  rewrite HM. f_equal. apply list_lookup_total_correct. exact Hf.
Qed.

(* THE bss HALF, from the zeros [umem_grow] left behind. *)
Lemma uimg_sub_seg_zero_map (p : elf_phdr) (M : gmap Z (bv 8)) :
  ep_filesz p <= ep_memsz p ->
  (forall j, ep_filesz p <= j < ep_memsz p ->
     M !! (ep_vaddr p + j) = Some (bv_0 8)) ->
  uimg_sub (seg_zero_map p) M.
Proof.
  intros Hm Hb a b Ha.
  apply (proj1 (lookup_seg_zero_map p a b Hm)) in Ha as [Hrange ->].
  pose proof (Hb (a - ep_vaddr p) ltac:(lia)) as HM.
  replace (ep_vaddr p + (a - ep_vaddr p)) with a in HM by lia.
  rewrite HM, elf_zero_byte_bv0. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  PRESERVATION: what a later step of the loop cannot disturb.            *)
(* ---------------------------------------------------------------------- *)

(* [umem_grow_lookup_old] / [umem_grow_lookup_zero] are [KexecBuilt]'s. *)

Lemma uimg_sub_umem_grow (img M : gmap Z (bv 8)) (sz : Z) :
  uimg_sub img M -> uimg_sub img (umem_grow M sz).
Proof. intros H a b Hb. apply umem_grow_lookup_old. exact (H a b Hb). Qed.

(* A write that lands entirely OUTSIDE the image's domain leaves it. *)
Lemma uimg_sub_umem_write (img M : gmap Z (bv 8)) (a : Z) (n : nat)
    (g : nat -> bv 8) :
  uimg_sub img M ->
  (forall j, (j < n)%nat -> img !! (a + Z.of_nat j) = None) ->
  uimg_sub img (umem_write M a n g).
Proof.
  intros Hsub Hout va b Hb.
  assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)).
  { intros j Hj Heq. rewrite Heq, (Hout j Hj) in Hb. discriminate. }
  rewrite (umem_write_lookup_out M a n g va Hne). exact (Hsub va b Hb).
Qed.

(* ...the same, stated on the RANGE rather than on the indices, which is
   what a caller holding [dom (elf_image f) ⊆ [0, sz)] has in hand. *)
Lemma uimg_sub_umem_write_range (img M : gmap Z (bv 8)) (a : Z) (n : nat)
    (g : nat -> bv 8) :
  uimg_sub img M ->
  (forall va, a <= va < a + Z.of_nat n -> img !! va = None) ->
  uimg_sub img (umem_write M a n g).
Proof.
  intros Hsub Hout. apply (uimg_sub_umem_write img M a n g Hsub).
  intros j Hj. apply Hout. lia.
Qed.

(* ...and the va-keyed run a copyout's contract posts. *)
Lemma uimg_sub_umem_wr (img M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) :
  uimg_sub img M ->
  (forall j, (j < n)%nat ->
     img !! uint (add_vec_int dstva (Z.of_nat j)) = None) ->
  uimg_sub img (umem_wr M dstva n src).
Proof.
  intros Hsub Hout va b Hb.
  assert (Hne : forall j, (j < n)%nat ->
                  va <> uint (add_vec_int dstva (Z.of_nat j))).
  { intros j Hj Heq. rewrite Heq, (Hout j Hj) in Hb. discriminate. }
  rewrite (umem_wr_lookup_out M dstva n src va Hne). exact (Hsub va b Hb).
Qed.

(* ====================================================================== *)
(*  2.  THE loadseg LOOP, PAGE BY PAGE                                    *)
(* ====================================================================== *)

(* THE INVARIANT: the first [n] bytes of the segment are in place.  [n]
   runs [0, PGSIZE, 2*PGSIZE, ..., filesz] as loadseg walks pages. *)
Definition load_win (f : elf_bytes) (off va n : Z) (M : gmap Z (bv 8)) : Prop :=
  forall j, 0 <= j < n -> M !! (va + j) = Some (f !!! Z.to_nat (off + j)).

Lemma load_win_0 (f : elf_bytes) (off va : Z) (M : gmap Z (bv 8)) :
  load_win f off va 0 M.
Proof. intros j Hj. exfalso. lia. Qed.

(* ONE PAGE STEP: loadseg's body is
     [umem_write M (va + i) nn (fun k => f !!! Z.to_nat (off + i + k))]
   with [nn = min PGSIZE (filesz - i)], and it extends the window by [nn]. *)
Lemma load_win_step (f : elf_bytes) (off va i : Z) (nn : nat)
    (M : gmap Z (bv 8)) :
  0 <= i ->
  load_win f off va i M ->
  load_win f off va (i + Z.of_nat nn)
    (umem_write M (va + i) nn (fun k => f !!! Z.to_nat (off + i + Z.of_nat k))).
Proof.
  intros Hi Hinv j Hj.
  destruct (Z_lt_le_dec j i) as [Hlt | Hge].
  - assert (Hne : forall k, (k < nn)%nat -> (va + j) <> (va + i + Z.of_nat k))
      by (intros k Hk; lia).
    rewrite (umem_write_lookup_out M (va + i) nn _ (va + j) Hne).
    exact (Hinv j ltac:(lia)).
  - assert (Hk : (Z.to_nat (j - i) < nn)%nat) by lia.
    replace (va + j) with (va + i + Z.of_nat (Z.to_nat (j - i))) by lia.
    rewrite (umem_write_lookup_in M (va + i) nn _ (Z.to_nat (j - i)) Hk).
    cbn beta. do 2 f_equal. lia.
Qed.

(* the window survives a later uvmalloc... *)
Lemma load_win_grow (f : elf_bytes) (off va n sz : Z) (M : gmap Z (bv 8)) :
  load_win f off va n M -> load_win f off va n (umem_grow M sz).
Proof. intros H j Hj. apply umem_grow_lookup_old. exact (H j Hj). Qed.

(* ...and a later write that misses it. *)
Lemma load_win_write_out (f : elf_bytes) (off va n a : Z) (nn : nat)
    (g : nat -> bv 8) (M : gmap Z (bv 8)) :
  load_win f off va n M ->
  (forall k, (k < nn)%nat -> ~ (va <= a + Z.of_nat k < va + n)) ->
  load_win f off va n (umem_write M a nn g).
Proof.
  intros H Hout j Hj.
  assert (Hne : forall k, (k < nn)%nat -> (va + j) <> (a + Z.of_nat k)).
  { intros k Hk Heq. apply (Hout k Hk). lia. }
  rewrite (umem_write_lookup_out M a nn g (va + j) Hne). exact (H j Hj).
Qed.

(* AT [n = filesz] THE WINDOW IS THE FILE HALF OF THE SEGMENT. *)
Lemma uimg_sub_seg_file_map_win (f : elf_bytes) (p : elf_phdr)
    (M : gmap Z (bv 8)) :
  phdr_ok f p ->
  load_win f (ep_offset p) (ep_vaddr p) (ep_filesz p) M ->
  uimg_sub (seg_file_map f p) M.
Proof. intros Hok Hw. exact (uimg_sub_seg_file_map f p M Hok Hw). Qed.

(* ====================================================================== *)
(*  3.  THE SIZE CHAIN                                                    *)
(* ====================================================================== *)

(* uvmalloc's return value: [oldsz] when the request is a shrink, else the
   request.  (The memory effect is [umem_grow]; this is the SIZE.) *)
Definition kx_uvmalloc (oldsz newsz : Z) : Z :=
  if newsz <? oldsz then oldsz else newsz.

Lemma kx_uvmalloc_max (o n : Z) : kx_uvmalloc o n = Z.max o n.
Proof. unfold kx_uvmalloc. destruct (Z.ltb_spec n o); lia. Qed.

Definition kx_grow (sz : Z) (p : elf_phdr) : Z :=
  kx_uvmalloc sz (ep_vaddr p + ep_memsz p).

(* the loop's [sz] after the PT_LOADs in [ps] have been allocated *)
Definition kexec_sz_after (ps : list elf_phdr) : Z := foldl kx_grow 0 ps.

Lemma kexec_sz_after_nil : kexec_sz_after [] = 0.
Proof. reflexivity. Qed.

Lemma kexec_sz_after_snoc (ps : list elf_phdr) (p : elf_phdr) :
  kexec_sz_after (ps ++ [p])
  = kx_uvmalloc (kexec_sz_after ps) (ep_vaddr p + ep_memsz p).
Proof. unfold kexec_sz_after. rewrite foldl_app. reflexivity. Qed.

(* THE SHRINK CASE NEVER FIRES: this is the whole content of "ascending". *)
Lemma kexec_sz_after_snoc_le (ps : list elf_phdr) (p : elf_phdr) :
  kexec_sz_after ps <= ep_vaddr p + ep_memsz p ->
  kexec_sz_after (ps ++ [p]) = ep_vaddr p + ep_memsz p.
Proof. intros H. rewrite kexec_sz_after_snoc, kx_uvmalloc_max. lia. Qed.

(* ---- [Z.max] folds: order does not matter, so [elf_mem_end] needs no
        ascending hypothesis ---- *)

Lemma foldr_Zmax_ge (l : list Z) (s : Z) : s <= foldr Z.max s l.
Proof. induction l as [| x l IH]; simpl; lia. Qed.

Lemma foldr_Zmax_max (l : list Z) (s t : Z) :
  foldr Z.max (Z.max s t) l = Z.max s (foldr Z.max t l).
Proof. induction l as [| x l IH]; simpl; [lia |]. rewrite IH. lia. Qed.

Lemma foldl_Zmax_foldr (l : list Z) (s : Z) :
  foldl Z.max s l = foldr Z.max s l.
Proof.
  revert s. induction l as [| x l IH]; simpl; intros s; [reflexivity |].
  rewrite IH, (Z.max_comm s x). apply foldr_Zmax_max.
Qed.

Lemma foldl_kx_grow_map (ps : list elf_phdr) (s : Z) :
  foldl kx_grow s ps
  = foldl Z.max s ((fun p => ep_vaddr p + ep_memsz p) <$> ps).
Proof.
  revert s. induction ps as [| q ps IH]; intros s; [reflexivity |].
  rewrite fmap_cons. simpl. rewrite <- kx_uvmalloc_max. apply IH.
Qed.

Lemma kexec_sz_after_zlist_max (ps : list elf_phdr) :
  kexec_sz_after ps
  = match zlist_max ((fun p => ep_vaddr p + ep_memsz p) <$> ps) with
    | Some e => Z.max 0 e
    | None => 0
    end.
Proof.
  unfold kexec_sz_after. rewrite foldl_kx_grow_map.
  destruct ps as [| q ps]; [reflexivity |].
  rewrite fmap_cons. simpl foldl. unfold zlist_max.
  rewrite foldl_Zmax_foldr. apply foldr_Zmax_max.
Qed.

Lemma kexec_sz_after_nonneg (ps : list elf_phdr) : 0 <= kexec_sz_after ps.
Proof.
  rewrite kexec_sz_after_zlist_max.
  destruct (zlist_max _); lia.
Qed.

(* the two nonnegativity facts [elf_wf] buys, in the shape the folds want *)
Definition phdrs_nonneg (ps : list elf_phdr) : Prop :=
  Forall (fun p => 0 <= ep_vaddr p /\ 0 <= ep_memsz p) ps.

Lemma elf_wf_phdrs_nonneg (f : elf_bytes) :
  elf_wf f = true -> phdrs_nonneg (elf_loads f).
Proof.
  intros Hwf. apply Forall_lookup. intros i p Hp.
  destruct (elf_wf_phdr_ok f p Hwf (elem_of_list_lookup_2 _ _ _ Hp)).
  lia.
Qed.

(* THE SIZE THE LOOP LEAVES BEHIND IS [elf_mem_end].  [Z.max] is
   commutative, so this holds with NO ordering hypothesis at all; only the
   [0] the loop starts from needs [ep_vaddr + ep_memsz >= 0]. *)
Lemma kexec_sz_after_mem_end (f : elf_bytes) :
  elf_wf f = true ->
  kexec_sz_after (elf_loads f)
  = match elf_mem_end f with Some e => e | None => 0 end.
Proof.
  intros Hwf.
  pose proof (elf_wf_phdrs_nonneg f Hwf) as Hnn.
  rewrite kexec_sz_after_zlist_max. unfold elf_mem_end.
  destruct (elf_loads f) as [| q ps] eqn:Hl; [reflexivity |].
  rewrite fmap_cons. unfold zlist_max.
  assert (Hq : 0 <= ep_vaddr q + ep_memsz q).
  { destruct (Forall_lookup_1 _ _ 0%nat q Hnn ltac:(reflexivity)).
    lia. }
  pose proof (foldr_Zmax_ge
                ((fun p => ep_vaddr p + ep_memsz p) <$> ps)
                (ep_vaddr q + ep_memsz q)).
  lia.
Qed.


Fixpoint kxb_ascending (ps : list elf_phdr) : Prop :=
  match ps with
  | [] => True
  | p :: ps' =>
      (match ps' with
       | [] => True
       | q :: _ => ep_vaddr p + ep_memsz p <= ep_vaddr q
       end) /\ kxb_ascending ps'
  end.

(* ---- ASCENDING SEGMENTS: prefixes, and the [take i]-indexed invariant ----
       [SpecKexecAU.kxb_ascending], spelled below it (this file's header:
       the kernel-side loops must not depend on the AU cone).
       [KexecImageAlg] §3 is the (one-[rewrite]) bridge. *)

Lemma kxb_ascending_app_l (ps qs : list elf_phdr) :
  kxb_ascending (ps ++ qs) -> kxb_ascending ps.
Proof.
  induction ps as [| p ps IH]; simpl; intros H; [exact I |].
  destruct H as [Hstep Hrest]. split; [| exact (IH Hrest)].
  destruct ps as [| q ps]; [exact I |]. simpl in Hstep. exact Hstep.
Qed.

Lemma kxb_ascending_take (ps : list elf_phdr) (i : nat) :
  kxb_ascending ps -> kxb_ascending (take i ps).
Proof.
  intros H. apply (kxb_ascending_app_l (take i ps) (drop i ps)).
  rewrite take_drop. exact H.
Qed.

Lemma kxb_ascending_adj (ps : list elf_phdr) (i : nat) (p q : elf_phdr) :
  kxb_ascending ps -> ps !! i = Some p -> ps !! S i = Some q ->
  ep_vaddr p + ep_memsz p <= ep_vaddr q.
Proof.
  revert i. induction ps as [| x ps IH]; intros i H Hp Hq;
    [rewrite lookup_nil in Hp; discriminate |].
  destruct i as [| i]; simpl in H, Hp, Hq.
  - injection Hp as <-. destruct H as [Hstep _].
    destruct ps as [| y ps]; [discriminate Hq |].
    simpl in Hq. injection Hq as <-. exact Hstep.
  - destruct H as [_ Hrest]. exact (IH i Hrest Hp Hq).
Qed.

(* THE LOOP INVARIANT, at the phdr number.  Before phdr [i] the running
   [sz] is at or below [ep_vaddr p] (so uvmalloc's growth starts exactly
   at this segment and the shrink case is dead), and after it the running
   [sz] IS [ep_vaddr p + ep_memsz p]. *)
Lemma kxb_sz_after_take_step (ps : list elf_phdr) (i : nat) (p : elf_phdr) :
  kxb_ascending ps -> phdrs_nonneg ps -> ps !! i = Some p ->
  kexec_sz_after (take i ps) <= ep_vaddr p
  /\ kexec_sz_after (take (S i) ps) = ep_vaddr p + ep_memsz p.
Proof.
  intros Hasc Hnn. revert p. induction i as [| i IH]; intros p Hp.
  - destruct (Forall_lookup_1 _ _ _ _ Hnn Hp) as [Hv Hm].
    rewrite (take_S_r ps 0%nat p Hp), take_0, kexec_sz_after_nil.
    split; [lia |].
    apply kexec_sz_after_snoc_le. rewrite kexec_sz_after_nil. lia.
  - destruct (Forall_lookup_1 _ _ _ _ Hnn Hp) as [Hv Hm].
    assert (Hlt : (i < length ps)%nat)
      by (pose proof (lookup_lt_Some _ _ _ Hp); lia).
    destruct (lookup_lt_is_Some_2 ps i Hlt) as [q Hq].
    destruct (IH q Hq) as [_ Hprev].
    pose proof (kxb_ascending_adj ps i q p Hasc Hq Hp) as Hadj.
    split; [lia |].
    rewrite (take_S_r ps (S i) p Hp), kexec_sz_after_snoc_le;
      [reflexivity | lia].
Qed.


(* ====================================================================== *)
(*  3b.  THE LOADER'S OWN VIEW OF THE PROGRAM HEADER TABLE                *)
(* ====================================================================== *)

(*  The phdr loop reads header [i] out of the FILE, into a 56-byte frame
    buffer it overwrites on the next turn.  So its invariant cannot be
    stated on the buffer: it has to be stated on a TOTAL pure function of
    the file's bytes and the ELF header's own [ph_at], which is what these
    four are.  [kxb_phdr_at] is [ElfFile.elf_parse_phdr]'s record without
    the option ([KexecImageAlg] §4 is the identification, under the bounds
    [SpecKexecAU.kexec_loadable] carries); [kxb_phoff] is the offset readi
    is actually handed, i.e. the 32-bit truncation the ABI performs.       *)

Definition kxb_phdr_at (f : elf_bytes) (o : nat) : elf_phdr :=
  ElfPhdr (elf_le_at f o 4) (elf_le_at f (o + 4) 4)
          (elf_le_at f (o + 8) 8) (elf_le_at f (o + 16) 8)
          (elf_le_at f (o + 24) 8) (elf_le_at f (o + 32) 8)
          (elf_le_at f (o + 40) 8) (elf_le_at f (o + 48) 8).

Definition kxb_phoff (ef : nat -> bv 8) (i : nat) : nat :=
  Z.to_nat ((ph_at ef i) `mod` 2 ^ 32).

Definition kxb_phdr (f : elf_bytes) (ef : nat -> bv 8) (i : nat) : elf_phdr :=
  kxb_phdr_at f (kxb_phoff ef i).

(* the PT_LOADs among the first [n] headers, in program-header order --
   the loop's [take i]-indexed list.  Written as a snoc recursion because
   that is exactly the step the loop takes. *)
Fixpoint kxb_loads (f : elf_bytes) (ef : nat -> bv 8) (n : nat)
  : list elf_phdr :=
  match n with
  | O => []
  | S k => kxb_loads f ef k
           ++ (if decide (ep_type (kxb_phdr f ef k) = 1)
               then [kxb_phdr f ef k] else [])
  end.

Lemma kxb_loads_S_load (f : elf_bytes) (ef : nat -> bv 8) (k : nat) :
  ep_type (kxb_phdr f ef k) = 1 ->
  kxb_loads f ef (S k) = (kxb_loads f ef k ++ [kxb_phdr f ef k])%list.
Proof. intros H. simpl. rewrite decide_True by exact H. reflexivity. Qed.

Lemma kxb_loads_S_skip (f : elf_bytes) (ef : nat -> bv 8) (k : nat) :
  ep_type (kxb_phdr f ef k) <> 1 ->
  kxb_loads f ef (S k) = kxb_loads f ef k.
Proof.
  intros H. simpl. rewrite decide_False by exact H.
  apply List.app_nil_r.
Qed.

Lemma kxb_loads_prefix (f : elf_bytes) (ef : nat -> bv 8) (i n : nat) :
  (i <= n)%nat -> exists r, kxb_loads f ef n = (kxb_loads f ef i ++ r)%list.
Proof.
  induction 1 as [| n Hn [r IH]].
  - exists []. rewrite List.app_nil_r. reflexivity.
  - simpl. rewrite IH.
    eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma kxb_loads_take (f : elf_bytes) (ef : nat -> bv 8) (i n : nat) :
  (i <= n)%nat ->
  take (length (kxb_loads f ef i)) (kxb_loads f ef n) = kxb_loads f ef i.
Proof.
  intros Hi. destruct (kxb_loads_prefix f ef i n Hi) as [r ->].
  rewrite take_app_length. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE PHDR LOOP'S INVARIANT, and the guard that makes its step true.     *)
(* ---------------------------------------------------------------------- *)

(* after [n] headers: the running [sz] is the [uvmalloc] fold over the
   PT_LOADs seen so far, and each of their segments is already in the
   image. *)
Definition kxb_at (f : elf_bytes) (ef : nat -> bv 8) (n : nat)
    (szv : Z) (M : gmap Z (bv 8)) : Prop :=
  szv = kexec_sz_after (kxb_loads f ef n)
  /\ (forall p, p ∈ kxb_loads f ef n -> uimg_sub (seg_map f p) M).

(* THE GUARD.  Nothing above is true of an arbitrary file: the step needs
   the walk to be reading the table the ELF semantics parses, that table's
   PT_LOADs to be well-formed, and them to ASCEND (which is what makes the
   later segments' writes miss the earlier ones and the [uvmalloc] fold a
   plain running maximum).  It is a PREMISE of the block lemmas, not a
   conjunct of the states -- [SpecKexecAU.kexec_loadable] is where it comes
   from, and [KexecImageAlg] §4 is the (only) glue. *)
Definition kxb_walk_ok (f : elf_bytes) (ef : nat -> bv 8) : Prop :=
  kxb_loads f ef (Z.to_nat (eh_phnum ef)) = elf_loads f
  /\ Forall (phdr_ok f) (elf_loads f)
  /\ kxb_ascending (elf_loads f).

Lemma kxb_walk_phdr_ok (f : elf_bytes) (ef : nat -> bv 8) (n : nat)
    (p : elf_phdr) :
  kxb_walk_ok f ef -> (n <= Z.to_nat (eh_phnum ef))%nat ->
  p ∈ kxb_loads f ef n -> phdr_ok f p.
Proof.
  intros (Hid & Hok & _) Hn Hp.
  destruct (kxb_loads_prefix f ef n (Z.to_nat (eh_phnum ef)) Hn) as [r Hr].
  rewrite Hid in Hr.
  assert (Hin : p ∈ elf_loads f)
    by (rewrite Hr; apply elem_of_app; left; exact Hp).
  apply elem_of_list_lookup in Hin as [j Hj].
  exact (Forall_lookup_1 _ _ _ _ Hok Hj).
Qed.

(* THE STEP, at a PT_LOAD header: the running [sz] starts at or below this
   segment's [vaddr] (so uvmalloc's shrink case is dead and the growth is
   exactly this segment) and ends at its top. *)
Lemma kxb_walk_step (f : elf_bytes) (ef : nat -> bv 8) (i : nat) :
  kxb_walk_ok f ef -> (S i <= Z.to_nat (eh_phnum ef))%nat ->
  ep_type (kxb_phdr f ef i) = 1 ->
  phdr_ok f (kxb_phdr f ef i)
  /\ kexec_sz_after (kxb_loads f ef i) <= ep_vaddr (kxb_phdr f ef i)
  /\ kexec_sz_after (kxb_loads f ef (S i))
     = ep_vaddr (kxb_phdr f ef i) + ep_memsz (kxb_phdr f ef i).
Proof.
  intros Hw Hi Hty. pose proof Hw as (Hid & Hok & Hasc).
  set (p := kxb_phdr f ef i).
  set (k := length (kxb_loads f ef i)).
  assert (HSi : kxb_loads f ef (S i) = (kxb_loads f ef i ++ [p])%list)
    by (apply kxb_loads_S_load; exact Hty).
  assert (Hpok : phdr_ok f p)
    by (apply (kxb_walk_phdr_ok f ef (S i) p Hw Hi);
        rewrite HSi; apply elem_of_app; right; apply elem_of_list_singleton;
        reflexivity).
  assert (Htk : take k (elf_loads f) = kxb_loads f ef i).
  { rewrite <- Hid. apply kxb_loads_take. lia. }
  assert (HlenS : length (kxb_loads f ef (S i)) = S k)
    by (rewrite HSi, length_app; unfold k; simpl; lia).
  assert (HtSk : take (S k) (elf_loads f) = (kxb_loads f ef i ++ [p])%list).
  { rewrite <- HSi, <- HlenS, <- Hid. apply kxb_loads_take. lia. }
  assert (Hlk : elf_loads f !! k = Some p).
  { assert (Hpref : take (S k) (elf_loads f) !! k = Some p).
    { rewrite HtSk. apply list_lookup_middle. unfold k. reflexivity. }
    rewrite lookup_take in Hpref by lia. exact Hpref. }
  assert (Hnn : phdrs_nonneg (elf_loads f)).
  { unfold phdrs_nonneg. apply Forall_lookup. intros j q Hq.
    pose proof (Forall_lookup_1 _ _ _ _ Hok Hq) as Hq'.
    pose proof (po_vaddr f q Hq'). pose proof (po_filesz f q Hq').
    pose proof (po_memsz f q Hq'). split; lia. }
  destruct (kxb_sz_after_take_step (elf_loads f) k p Hasc Hnn Hlk)
    as [Hle Heq].
  rewrite Htk in Hle. rewrite HtSk in Heq. rewrite <- HSi in Heq.
  split; [exact Hpok | split; [exact Hle | exact Heq]].
Qed.

(* the fold is at least every member's top -- what says an already-loaded
   segment sits strictly below the size the loop has reached. *)
Lemma foldr_Zmax_elem (l : list Z) (s x : Z) :
  x ∈ l -> x <= foldr Z.max s l.
Proof.
  induction l as [| y l IH]; intros Hx; [inversion Hx |].
  apply elem_of_cons in Hx as [-> | Hx]; simpl; [lia |].
  pose proof (IH Hx). lia.
Qed.

Lemma kexec_sz_after_elem (ps : list elf_phdr) (p : elf_phdr) :
  p ∈ ps -> ep_vaddr p + ep_memsz p <= kexec_sz_after ps.
Proof.
  intros Hp. unfold kexec_sz_after.
  rewrite foldl_kx_grow_map, foldl_Zmax_foldr.
  apply foldr_Zmax_elem.
  apply elem_of_list_fmap. exists p. split; [reflexivity | exact Hp].
Qed.

(* ...and a segment's own bytes live inside its own [vaddr] window, which
   is what turns that into "a later write cannot disturb it". *)
Lemma seg_map_lookup_range (f : elf_bytes) (p : elf_phdr) (a : Z) (b : bv 8) :
  phdr_ok f p -> seg_map f p !! a = Some b ->
  ep_vaddr p <= a < ep_vaddr p + ep_memsz p.
Proof.
  intros Hok Ha. pose proof (po_memsz f p Hok) as Hm.
  pose proof (po_filesz f p Hok) as Hf.
  unfold seg_map in Ha.
  apply lookup_union_Some_raw in Ha as [Ha | [_ Ha]].
  - destruct (proj1 (lookup_seg_file_map f p a b Hok) Ha) as [Hr _]. lia.
  - destruct (proj1 (lookup_seg_zero_map p a b Hm) Ha) as [Hr _]. lia.
Qed.

Lemma uimg_sub_seg_map_above (f : elf_bytes) (p : elf_phdr)
    (M : gmap Z (bv 8)) (a : Z) (n : nat) (g : nat -> bv 8) :
  phdr_ok f p -> ep_vaddr p + ep_memsz p <= a ->
  uimg_sub (seg_map f p) M -> uimg_sub (seg_map f p) (umem_write M a n g).
Proof.
  intros Hok Hab Hsub. apply uimg_sub_umem_write_range; [exact Hsub |].
  intros va Hva. destruct (seg_map f p !! va) as [b |] eqn:Hb;
    [| reflexivity].
  exfalso. pose proof (seg_map_lookup_range f p va b Hok Hb). lia.
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

    WHAT IT DOES NOT CARRY YET, and what is now in place for it.
    [kexec_image_ok] also asks for [uimg_sub (elf_image f)] and for
    [uint sz1 = kexec_sz f], and each of those is a claim about the FILE's
    bytes.  Until S3b the kernel-side cone could not state either: the
    file's byte function was ∃-bound inside [IcacheEscrow.ic_loaded], and
    [SpecKexecB2.kxc_load_peel] re-introduced the ∃ at every readi, so no
    phase state could even MENTION it.  That blocker is gone --
    [ProofKexecTail.kxc_ldat] is [ic_loaded]'s payload at a NAMED [datl],
    [ProofKexecSeam.kxc_open] carries it, phase A chooses the name at its
    header readi and publishes [forall j < 64, ef j = file_byte datl j]
    beside it, and every phase-B/B2/B3 state passes it along.  §1-§3b below
    are the vocabulary the two remaining invariants are to be written in:
    [load_win] (the loadseg window), [kexec_sz_after] over [kxb_loads]
    (the phdr loop's size fold) and [kxb_at] / [kxb_walk_ok] (the loop
    invariant and the ascending/well-formedness guard its step needs;
    [KexecImageAlg.kxb_walk_ok_of_loadable] discharges the guard from
    [SpecKexecAU.kexec_loadable]).  What is STILL missing is the in-proof
    work: [ProofKexecB2.kxc_ls] must carry [load_win] through its fuel
    induction and publish it at +0x116, and [ProofKexecB3.kxc_ph_step]
    must step [kxb_at] across the uvmalloc/loadseg pair.  Only then can
    this Prop gain the file's bytes as a parameter and the two rows

        uimg_sub (elf_image f) (us_M U')
        uint sz1 = pgroundup (kexec_sz_after (elf_loads f)) + 8192

    with the five premise sites ([ProofKexecD.kxd_phaseD],
    [ProofKexec.kxc_d_tail] / [kxc_cd], [ProofKexecPin]'s two) gaining
    them by name.                                                          *)
Definition kexec_built (sz1 : mword 64) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (U' : ustate) : Prop :=
  pv_sz (us_V U') = sz1
  /\ kxb_args_at (uint sz1) alen na afun (us_M U')
  /\ kxb_stack_at (uint sz1) alen na (us_M U').
