(* UserPtTree.v -- U-MODE translation over the ptree user table
   (UptTree.v): the successor of UserPt.v's upt record for arbitrary
   user-mode execution.

   Layers:
     §1 privilege bricks: effectivePrivilege at MPRV=0 (access-generic)
        and is_shadow_stack for every access user execution can issue;
     §2 the per-leaf ACCESS classification: at User, a mapped leaf either
        passes the permission check on every A/D variant ([uleaf_ok]) or
        is denied on every variant ([uleaf_denied]) -- decided once per
        map entry from its concrete R/W/X/U flag byte ([upt_acc_wf]).
        The S-mode-only trampoline / trapframe leaves are DENIED for
        every user access (U = 0);
     §3 the user-execution page-table bundle and THE ABSTRACT STATE OF
        THE USER-MODE PROCESS: [user_pt_inv P M] is the tree invariant
        [utlb_inv_pt] + ownership of the process's memory [umem_own P M],
        a [gmap] from USER VIRTUAL ADDRESS to byte, + the no-aliasing and
        access-classification facts.  [user_pt_any P] quantifies [M] and
        is what the user-execution engines take;
     §4 the U-mode Ok absorption instance: a user-mapped, check-passing
        va translates to its leaf page and the invariant absorbs
        whatever the walk did (hit / TLB fill / Svadu A/D write-back).

   The FAULT side (non-canonical / unmapped / denied / hit-denied) is §5.  *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RiscvExtras.   (* [svpn_of_unsigned_lo] / [moi64_unsigned] -- the va keying *)
Require Import UserBits.      (* [bv_subrange11] -- the page-offset arithmetic *)
Require Import PtAdBits.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import TrampPt.
Require Import Pt4kWalk.
Require Import SmodePte.
Require Import KptTree.
Require Import UptTree.
Require Import UserTranslate.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Privilege bricks.                                                    *)
(* ===================================================================== *)

(* with MPRV clear the effective privilege is the current one, for EVERY
   access type (the fetch special case never consults MPRV) *)
Lemma exec_effectivePrivilege_mprv0 (acc : MemoryAccessType mem_payload)
    (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  exec (effectivePrivilege acc m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  apply exec_returnM.
Qed.

(* the access types arbitrary user-mode execution can issue *)
Definition u_acc (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  (exists aq rl, acc = LoadReserved (aq, rl, Data)) \/
  (exists aq rl, acc = StoreConditional (aq, rl, Data)) \/
  (exists op aq rl, acc = Atomic (op, aq, rl, Data, Data)).

Lemma exec_is_shadow_stack_u_acc (acc : MemoryAccessType mem_payload) s :
  u_acc acc ->
  exec (is_shadow_stack_access acc) s = Some (false, s).
Proof.
  intros [-> | [-> | [-> | [(aq & rl & ->) | [(aq & rl & ->) | (op & aq & rl & ->)]]]]];
    unfold is_shadow_stack_access; cbn match; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §2 The per-leaf access classification at User.                          *)
(* ===================================================================== *)

(* the check passes on every A/D variant (check_PTE_permission never
   reads A/D, so this is a fact about the R/W/X/U byte of [w] alone) *)
Definition uleaf_ok (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_ok acc User mxr do_sum (pte_set_ad w a d).

(* ... or is denied on every variant.  NOTE the mxr quantifier: a leaf
   with X=1, R=0 would be load-DENIED only at mxr=0 -- such execute-only
   user pages fall in neither class and are excluded by [upt_acc_wf]
   (xv6 never builds them; user execution pins mstatus.MXR=0 anyway). *)
Definition uleaf_denied (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_denied acc User mxr do_sum (PTE_No_Permission tt) (pte_set_ad w a d).

(* the classification each user-map entry carries: decided once when the
   map is built, from the entry's concrete flag byte (each side is a
   4-way a/d x 4-way mxr/do_sum vm_compute) *)
Definition upt_acc_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn w, um !! vpn = Some w ->
    forall acc, u_acc acc -> uleaf_ok acc w \/ uleaf_denied acc w.

(* the S-mode-only top pages deny every user access before the access
   type is even consulted (U = 0 fails the privilege step) *)
Lemma uleaf_denied_tramp (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc pte_tramp.
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags. rewrite tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

Lemma uleaf_denied_tf (tfp : mword 44) (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc (pte_tf tfp).
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The user-execution page-table bundle, and THE ABSTRACT STATE OF    *)
(*    THE USER-MODE PROCESS.                                             *)
(*                                                                       *)
(* What a user hart owns of memory used to be the mapped pages with      *)
(* EXISTENTIAL contents ([udata_own], a flat pa-set).  That is enough    *)
(* for SAFETY -- user execution never depends on what the bytes are --   *)
(* but it says nothing a kernel-side proof can thread: copyin/copyout,   *)
(* a syscall argument, an exec image are all statements ABOUT THE BYTES, *)
(* at USER VIRTUAL addresses.  So the bundle now EXPOSES that state:     *)
(*                                                                       *)
(*   [M : gmap Z (bv 8)]  the process's memory, keyed by user virtual    *)
(*                        address (the keying the descoped verified tier *)
(*                        already used, [UmodeMem.umem]);                *)
(*   [umem_own P M]       ownership of exactly those bytes, realized as  *)
(*                        the [↦ₚ] cells at the translated addresses;   *)
(*   [user_pt_inv P M]    the tree invariant + [umem_own P M] + the two  *)
(*                        pure side conditions;                          *)
(*   [user_pt_any P]      [∃ M, user_pt_inv P M] -- what the USER-       *)
(*                        EXECUTION engines take, because arbitrary user *)
(*                        code may write arbitrary bytes into its own    *)
(*                        pages and so has nothing to say about [M].     *)
(*                        The DOMAIN is still pinned ([uva_dom P] is a   *)
(*                        function of the table), so quantifying [M] at  *)
(*                        the loop invariant loses nothing: only the     *)
(*                        kernel can change which vas are mapped.        *)
(*                                                                       *)
(* WHY A VA-KEYED MAP FORCES NO ALIASING.  Two user vpns mapping ONE     *)
(* physical page would make [umem_own] own that page's bytes twice, so   *)
(* the resource itself refutes aliasing.  That is not a new restriction: *)
(* [ProcPtOwn.um_inj] -- "distinct vpns, distinct pages" -- is already a *)
(* conjunct of [proc_pt_wf], re-established at every insert from the     *)
(* OWNERSHIP of the page being added.  The user tier states the same     *)
(* fact in its own vocabulary ([uva_pa_inj], at byte granularity) and    *)
(* receives it across the satp switch ([ProcPtOwn.user_pt_inv_close]).   *)
(*                                                                       *)
(* [udata_own] / [udata_cov] STAY, and [uptd]'s [ud_data] field with     *)
(* them: the pre-port [gen_heap_interp] memory layer (UserMemPt /        *)
(* UserMemAccess / UserMemMis / UserFetchPt) is stated over them and is  *)
(* independent of this bundle, which no longer reads [ud_data] at all.   *)
(* ===================================================================== *)

(* the pas a mapped leaf can output: its page, at every offset *)
Definition udata_cov (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa) : Prop :=
  forall vpn w va, um !! vpn = Some w -> u_walk_pa w va ∈ data.

(* ONE pure description of a live user page table, so the whole
   user-execution development closes over a single parameter (the
   [upt]-record successor): the root and trapframe ppns, the abstract
   user map, and the data-page footprint.  [ud_data] is read only by the
   pre-port layer above ([ProcPtOwn.ud_norm] renormalises it); the
   bundle of this section derives its footprint from [ud_um]. *)
Record uptd := UPTD {
  ud_root : mword 44;
  ud_tfp  : mword 44;
  ud_um   : gmap (mword 27) (mword 64);
  ud_data : gset Arch.pa
}.

(* --------------------------------------------------------------------- *)
(* §3a The va -> pa view of a live table, and the user address space.     *)
(* --------------------------------------------------------------------- *)

(* the pa a user virtual address translates to through [P]'s map: the
   recorded level-0 leaf's page, at [va]'s page offset.  TOTAL -- off the
   mapped vpns the value is arbitrary (zeros), and nothing owns bytes
   there. *)
Definition uva_pa (P : uptd) (va : Z) : mword 64 :=
  match P.(ud_um) !! svpn_of (mword_of_int va) with
  | Some w => u_walk_pa w (mword_of_int va)
  | None => zeros' 64
  end.

(* THE USER ADDRESS SPACE: every offset of every mapped page.  Spelled as
   PAGE * 4096 + OFFSET and not through [svpn_of], so that the finite set
   below is a function of [ud_um] with no well-formedness hypothesis and
   no wrap reasoning in its membership proof; [u_data_pa_cov] below is the
   bridge to the [svpn_of] form a memory arm holds. *)
Definition uva_mapped (P : uptd) (va : Z) : Prop :=
  exists (vpn : mword 27) (w : mword 64) (j : nat),
    P.(ud_um) !! vpn = Some w /\ (j < 4096)%nat /\
    va = bv_unsigned vpn * 4096 + Z.of_nat j.

Definition uva_dom (P : uptd) : gset Z :=
  list_to_set (mjoin
    ((fun vw : mword 27 * mword 64 =>
        (fun j : nat => bv_unsigned (fst vw) * 4096 + Z.of_nat j) <$> seq 0 4096)
     <$> map_to_list P.(ud_um))).

Lemma elem_of_uva_dom (P : uptd) (va : Z) :
  va ∈ uva_dom P <-> uva_mapped P va.
Proof.
  unfold uva_dom, uva_mapped.
  rewrite elem_of_list_to_set elem_of_list_join.
  split.
  - intros (l & Hva & Hl).
    apply elem_of_list_fmap in Hl as ([vpn w] & -> & Hin).
    apply elem_of_map_to_list in Hin.
    apply elem_of_list_fmap in Hva as (j & -> & Hj).
    apply elem_of_seq in Hj.
    exists vpn, w, j. split_and!; [exact Hin | lia | reflexivity].
  - intros (vpn & w & j & Hl & Hj & ->).
    exists ((fun j0 : nat => bv_unsigned vpn * 4096 + Z.of_nat j0) <$> seq 0 4096).
    split.
    + apply elem_of_list_fmap. exists j.
      split; [reflexivity |]. apply elem_of_seq. lia.
    + apply elem_of_list_fmap. exists (vpn, w).
      split; [reflexivity |]. apply elem_of_map_to_list. exact Hl.
Qed.

(* the physical addresses the user address space covers -- the successor
   of [udata_cov]'s [data] set.  DERIVED from [ud_um], and stated as a
   PREDICATE rather than a [gset Arch.pa] so that no [Countable Arch.pa]
   instance appears in the interface (see UserBytes.v section 3b on why a
   [gset Arch.pa] does not survive a file boundary here). *)
Definition u_data_pa (P : uptd) (a : mword 64) : Prop :=
  exists va, uva_mapped P va /\ uva_pa P va = a.

(* NO ALIASING, at byte granularity: distinct user vas name distinct
   bytes.  [ProcPtOwn.um_inj] read through [uva_pa]. *)
Definition uva_pa_inj (P : uptd) : Prop :=
  forall va1 va2, uva_mapped P va1 -> uva_mapped P va2 ->
    uva_pa P va1 = uva_pa P va2 -> va1 = va2.

(* the two premises every bridge feeds [bigset_gather_reindex], restated
   over [uva_dom] (its index set) rather than over [uva_mapped] *)
Lemma uva_dom_inj (P : uptd) :
  uva_pa_inj P ->
  forall x y : Z, x ∈ uva_dom P -> y ∈ uva_dom P ->
    uva_pa P x = uva_pa P y -> x = y.
Proof.
  intros Hinj x y Hx Hy Heq.
  apply Hinj; [ by apply elem_of_uva_dom | by apply elem_of_uva_dom | exact Heq ].
Qed.

Lemma u_data_pa_img (P : uptd) (a : mword 64) :
  u_data_pa P a <-> exists va, va ∈ uva_dom P /\ uva_pa P va = a.
Proof.
  unfold u_data_pa. split.
  - intros (va & Hm & <-). exists va.
    split; [ by apply elem_of_uva_dom | reflexivity ].
  - intros (va & Hva & <-). exists va.
    split; [ by apply elem_of_uva_dom | reflexivity ].
Qed.

(* --- the one piece of wrap arithmetic the va keying needs -------------- *)

(* a user page's vas sit below 2^38 (every user vpn is below the
   trapframe's, [upt_map_wf]), so [svpn_of] reads the vpn straight back *)
Local Lemma svpn_of_moi (va : Z) :
  0 <= va < 274877906944 ->
  bv_unsigned (svpn_of (mword_of_int va)) = va / 4096.
Proof.
  intros Hva.
  assert (Hmod : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hu : bv_unsigned (mword_of_int va : mword 64) = va).
  { rewrite moi64_unsigned. apply bv_wrap_small. rewrite Hmod. lia. }
  assert (Hui : uint (mword_of_int va : mword 64) = va)
    by (rewrite uint_unsigned; exact Hu).
  rewrite (svpn_of_unsigned_lo (mword_of_int va) ltac:(rewrite Hui; lia)).
  rewrite Hui. rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096. reflexivity.
Qed.

Lemma uva_svpn_of (vpn : mword 27) (j : nat) :
  (j < 4096)%nat -> bv_unsigned vpn < 67108862 ->
  svpn_of (mword_of_int (bv_unsigned vpn * 4096 + Z.of_nat j)) = vpn.
Proof.
  intros Hj Hvpn.
  pose proof (bv_unsigned_in_range _ vpn) as [Hv0 _].
  assert (Hb : 0 <= bv_unsigned vpn * 4096 + Z.of_nat j < 274877906944) by lia.
  apply bv_eq.
  rewrite (svpn_of_moi _ Hb).
  rewrite Z.div_add_l; [| lia].
  rewrite (Z.div_small (Z.of_nat j) 4096 ltac:(lia)). lia.
Qed.

(* every user vpn is below the trapframe's, read as a number *)
Lemma upt_map_wf_vpn_lt (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> bv_unsigned vpn < 67108862.
Proof.
  intros Hwf Hl. destruct (Hwf _ _ Hl) as (Hlt & _).
  rewrite tf_vpn_unsigned in Hlt. exact Hlt.
Qed.

(* ...so a user va fits in 64 bits with room to spare and [mword_of_int]
   does not wrap it *)
Lemma uva_moi_unsigned (vpn : mword 27) (j : nat) :
  (j < 4096)%nat -> bv_unsigned vpn < 67108862 ->
  bv_unsigned (mword_of_int (bv_unsigned vpn * 4096 + Z.of_nat j) : mword 64)
  = bv_unsigned vpn * 4096 + Z.of_nat j.
Proof.
  intros Hj Hvpn.
  pose proof (bv_unsigned_in_range _ vpn) as [Hv0 _].
  assert (Hmod : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite moi64_unsigned. apply bv_wrap_small. rewrite Hmod. lia.
Qed.

(* ...and so the va -> pa view of a mapped page's va is that page's byte *)
Lemma uva_pa_page (P : uptd) (vpn : mword 27) (w : mword 64) (j : nat) :
  upt_map_wf P.(ud_um) -> P.(ud_um) !! vpn = Some w -> (j < 4096)%nat ->
  uva_pa P (bv_unsigned vpn * 4096 + Z.of_nat j)
  = u_walk_pa w (mword_of_int (bv_unsigned vpn * 4096 + Z.of_nat j)).
Proof.
  intros Hwf Hl Hj.
  unfold uva_pa.
  rewrite (uva_svpn_of vpn j Hj (upt_map_wf_vpn_lt _ _ _ Hwf Hl)) Hl. reflexivity.
Qed.

(* [u_walk_pa] reads only the leaf's ppn and the va's PAGE OFFSET, so two
   vas with the same offset translate through one leaf to one pa *)
Lemma u_walk_pa_off (w va va' : mword 64) :
  bv_unsigned va mod 4096 = bv_unsigned va' mod 4096 ->
  u_walk_pa w va = u_walk_pa w va'.
Proof.
  intros Hoff. unfold u_walk_pa. cbn [bits_of_virtaddr].
  change (Z.sub pagesize_bits 1) with 11.
  assert (Hs : subrange_vec_dec va 11 0 = subrange_vec_dec va' 11 0)
    by (apply bv_eq; rewrite !bv_subrange11; exact Hoff).
  rewrite Hs. reflexivity.
Qed.

(* THE COVERAGE FACT, now a THEOREM rather than a side condition: every
   address a mapped leaf can output belongs to the user address space.
   This is [udata_cov] with the [data] set replaced by [u_data_pa], and
   it is what every memory arm's ownership obligation goes through.
   Note it does NOT ask [vpn = svpn_of va]: the pa depends only on the
   leaf and the page offset, so the CANONICAL va of that page and that
   offset -- which is in [uva_dom P] by construction -- is the witness,
   whatever the high bits of [va] were. *)
Lemma u_data_pa_cov (P : uptd) (vpn : mword 27) (w va : mword 64) :
  upt_map_wf P.(ud_um) -> P.(ud_um) !! vpn = Some w ->
  u_data_pa P (u_walk_pa w va).
Proof.
  intros Hwf Hl.
  pose proof (bv_unsigned_in_range _ va) as [Hva0 _].
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hb.
  assert (Hjlt : (Z.to_nat (bv_unsigned va mod 4096) < 4096)%nat) by lia.
  assert (Hjz : Z.of_nat (Z.to_nat (bv_unsigned va mod 4096))
                = bv_unsigned va mod 4096) by lia.
  exists (bv_unsigned vpn * 4096
          + Z.of_nat (Z.to_nat (bv_unsigned va mod 4096))).
  split.
  - exists vpn, w, (Z.to_nat (bv_unsigned va mod 4096)).
    split_and!; [exact Hl | exact Hjlt | reflexivity].
  - rewrite (uva_pa_page P vpn w _ Hwf Hl Hjlt).
    apply u_walk_pa_off.
    rewrite (uva_moi_unsigned vpn _ Hjlt (upt_map_wf_vpn_lt _ _ _ Hwf Hl)).
    rewrite Hjz Z.add_comm Z_mod_plus_full Zmod_mod. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* §3d' THE PURE WRITE / DELETE VOCABULARY of the byte window (§3e).      *)
(* --------------------------------------------------------------------- *)

(* [M] with the [n] bytes at [a] set to [bs] -- what a copyout does to the *)
(* process's memory, and the identity a copyin does to it. *)
Fixpoint umem_write (M : gmap Z (bv 8)) (a : Z) (n : nat) (bs : nat -> bv 8)
    : gmap Z (bv 8) :=
  match n with
  | O => M
  | S k => <[(a + Z.of_nat k)%Z := bs k]> (umem_write M a k bs)
  end.

(* ...and [M] with those [n] bytes REMOVED -- the frame the accessor keeps *)
Fixpoint umem_del (M : gmap Z (bv 8)) (a : Z) (n : nat) : gmap Z (bv 8) :=
  match n with
  | O => M
  | S k => delete (a + Z.of_nat k)%Z (umem_del M a k)
  end.

Lemma umem_del_lookup_out (M : gmap Z (bv 8)) (a : Z) (n : nat) (va : Z) :
  (forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z) ->
  umem_del M a n !! va = M !! va.
Proof.
  induction n as [| k IH]; intros Hne; [reflexivity |].
  cbn [umem_del].
  rewrite lookup_delete_ne; [| intros Heq; exact (Hne k ltac:(lia) (eq_sym Heq))].
  apply IH. intros j Hj. apply Hne. lia.
Qed.

Lemma umem_write_lookup_out (M : gmap Z (bv 8)) (a : Z) (n : nat)
    (bs : nat -> bv 8) (va : Z) :
  (forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z) ->
  umem_write M a n bs !! va = M !! va.
Proof.
  induction n as [| k IH]; intros Hne; [reflexivity |].
  cbn [umem_write].
  rewrite lookup_insert_ne; [| intros Heq; exact (Hne k ltac:(lia) (eq_sym Heq))].
  apply IH. intros j Hj. apply Hne. lia.
Qed.

Lemma umem_write_lookup_in (M : gmap Z (bv 8)) (a : Z) (n : nat)
    (bs : nat -> bv 8) (j : nat) :
  (j < n)%nat -> umem_write M a n bs !! (a + Z.of_nat j)%Z = Some (bs j).
Proof.
  revert j. induction n as [| k IH]; intros j Hj; [exfalso; lia |].
  cbn [umem_write].
  destruct (decide (j = k)) as [-> | Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne; [| lia]. apply IH. lia.
Qed.

(* membership of the run, in a DECIDABLE form *)
Local Lemma in_run_iff (a : Z) (n : nat) (va : Z) :
  (a <= va < a + Z.of_nat n)%Z <-> exists j, (j < n)%nat /\ va = (a + Z.of_nat j)%Z.
Proof.
  split.
  - intros [Hlo Hhi]. exists (Z.to_nat (va - a)). split; lia.
  - intros (j & Hj & ->). lia.
Qed.

Lemma umem_del_lookup_in (M : gmap Z (bv 8)) (a : Z) (n : nat) (j : nat) :
  (j < n)%nat -> umem_del M a n !! (a + Z.of_nat j)%Z = None.
Proof.
  revert j. induction n as [| k IH]; intros j Hj; [exfalso; lia |].
  cbn [umem_del]. destruct (decide (j = k)) as [-> | Hne].
  - apply lookup_delete.
  - rewrite lookup_delete_ne; [| lia]. apply IH. lia.
Qed.

Lemma umem_del_subseteq (M : gmap Z (bv 8)) (a : Z) (n : nat) :
  umem_del M a n ⊆ M.
Proof.
  apply map_subseteq_spec. intros va b Hb.
  destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hout].
  - apply in_run_iff in Hin as (j & Hj & ->).
    rewrite (umem_del_lookup_in M a n j Hj) in Hb. discriminate.
  - rewrite (umem_del_lookup_out M a n va
               ltac:(intros j Hj Heq; apply Hout; apply in_run_iff; eauto)) in Hb.
    exact Hb.
Qed.

Lemma umem_del_sub (M M' : gmap Z (bv 8)) (a : Z) (n : nat) :
  M ⊆ M' -> umem_del M a n ⊆ umem_del M' a n.
Proof.
  intros Hsub. apply map_subseteq_spec. intros va b Hb.
  destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hout].
  - apply in_run_iff in Hin as (j & Hj & ->).
    rewrite (umem_del_lookup_in M a n j Hj) in Hb. discriminate.
  - assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z)
      by (intros j Hj Heq; apply Hout; apply in_run_iff; eauto).
    rewrite (umem_del_lookup_out M a n va Hne) in Hb.
    rewrite (umem_del_lookup_out M' a n va Hne).
    exact (lookup_weaken _ _ _ _ Hb Hsub).
Qed.

Lemma umem_del_write (M : gmap Z (bv 8)) (a : Z) (n : nat) (bs : nat -> bv 8) :
  umem_del (umem_write M a n bs) a n = umem_del M a n.
Proof.
  (* both sides delete the same [n] keys, and outside them the two maps
     agree, so the equality is pointwise *)
  apply map_eq. intros va.
  destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hout];
    [ apply in_run_iff in Hin as (j & Hj & ->) |].
  - assert (Hdel : forall N : gmap Z (bv 8),
              umem_del N a n !! (a + Z.of_nat j)%Z = None).
    { intros N. clear -Hj. induction n as [| k IH]; [exfalso; lia |].
      cbn [umem_del].
      destruct (decide (j = k)) as [-> | Hne];
        [ apply lookup_delete |].
      rewrite lookup_delete_ne; [| lia]. apply IH. lia. }
    rewrite !Hdel. reflexivity.
  - assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z)
      by (intros j Hj Heq; apply Hout; apply in_run_iff; eauto).
    rewrite !(umem_del_lookup_out _ a n va Hne).
    apply (umem_write_lookup_out M a n bs va Hne).
Qed.

(* writing back the bytes that were already there is the identity -- what a
   copyIN does to the process's memory *)
Lemma umem_write_id (M : gmap Z (bv 8)) (a : Z) (n : nat) (bs : nat -> bv 8) :
  (forall j, (j < n)%nat -> M !! (a + Z.of_nat j)%Z = Some (bs j)) ->
  umem_write M a n bs = M.
Proof.
  induction n as [| k IH]; intros Hb; [reflexivity |].
  cbn [umem_write]. rewrite (IH ltac:(intros j Hj; apply Hb; lia)).
  apply insert_id. apply Hb. lia.
Qed.

(* A whole-PAGE write in which only a sub-window actually changed is the
   same map as the sub-window write.  This is what lets the copyout loop
   hand its user page back through a page-level accessor -- the buffer
   plumbing ([bb_split3] / [bb_join3]) is whole-page, but only the middle
   third of it is new. *)
Lemma umem_write_split (M : gmap Z (bv 8)) (a : Z) (N off n : nat)
    (g : nat -> bv 8) :
  (off + n <= N)%nat ->
  (forall j, (j < N)%nat -> ~ (off <= j < off + n)%nat ->
     M !! (a + Z.of_nat j)%Z = Some (g j)) ->
  umem_write M a N g
  = umem_write M (a + Z.of_nat off)%Z n (fun i => g (off + i)%nat).
Proof.
  intros HN Hout. apply map_eq. intros va.
  destruct (decide (a <= va < a + Z.of_nat N)%Z) as [Hin | Hno].
  - apply in_run_iff in Hin as (j & Hj & ->).
    rewrite (umem_write_lookup_in M a N g j Hj).
    destruct (decide (off <= j < off + n)%nat) as [Hw | Hnw].
    + replace (a + Z.of_nat j)%Z
        with ((a + Z.of_nat off) + Z.of_nat (j - off)%nat)%Z by lia.
      rewrite (umem_write_lookup_in M (a + Z.of_nat off)%Z n
                 (fun i => g (off + i)%nat) (j - off)%nat ltac:(lia)).
      do 2 f_equal. lia.
    + rewrite (umem_write_lookup_out M (a + Z.of_nat off)%Z n
                 (fun i => g (off + i)%nat) (a + Z.of_nat j)%Z
                 ltac:(intros i Hi Heq; lia)).
      symmetry. exact (Hout j Hj Hnw).
  - assert (Hne : forall j, (j < N)%nat -> va <> (a + Z.of_nat j)%Z)
      by (intros j Hj Heq; apply Hno; apply in_run_iff; eauto).
    rewrite (umem_write_lookup_out M a N g va Hne).
    rewrite (umem_write_lookup_out M (a + Z.of_nat off)%Z n
               (fun i => g (off + i)%nat) va
               ltac:(intros i Hi Heq; apply Hno;
                     apply in_run_iff; exists (off + i)%nat;
                     split; [lia | rewrite Nat2Z.inj_add; lia])).
    reflexivity.
Qed.

(* ---- the same run of writes, but keyed by the 64-bit va it started at ---- *)
(* [umem_write] is indexed by an INTEGER base [a + j], which is what an
   accessor over one page can offer: inside a page the vas really are
   consecutive integers.  A copyOUT, though, walks a range given by a
   [mword 64] and a length, and its contract must not have to promise that
   [dstva + j] does not wrap -- so the CONTRACT-level run is keyed by
   [uint (add_vec_int dstva j)] instead, and [umem_wr_step] is the one
   bridge between the two: as long as one chunk's vas are consecutive
   integers (which [uva_pa] forces, since they live in one page), writing
   that chunk advances the va-keyed run by exactly its length. *)
Fixpoint umem_wr (M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) : gmap Z (bv 8) :=
  match n with
  | O => M
  | S k => <[uint (add_vec_int dstva (Z.of_nat k)) := src k]>
             (umem_wr M dstva k src)
  end.

Lemma umem_wr_step (M : gmap Z (bv 8)) (dstva : mword 64) (done n : nat)
    (src : nat -> bv 8) (a : Z) :
  (forall i, (i < n)%nat ->
     uint (add_vec_int dstva (Z.of_nat (done + i))) = (a + Z.of_nat i)%Z) ->
  umem_write (umem_wr M dstva done src) a n (fun i => src (done + i)%nat)
  = umem_wr M dstva (done + n) src.
Proof.
  induction n as [| k IH]; intros Hva.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [umem_write]. rewrite (IH ltac:(intros i Hi; apply Hva; lia)).
    replace (done + S k)%nat with (S (done + k))%nat by lia.
    cbn [umem_wr]. rewrite (Hva k ltac:(lia)). reflexivity.
Qed.

(* what a caller reads back out of the run: needs the vas of the run to be
   distinct, which the caller gets from its own no-wrap bound *)
Lemma umem_wr_lookup_in (M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) (j : nat) :
  (j < n)%nat ->
  (forall i, (i < n)%nat ->
     uint (add_vec_int dstva (Z.of_nat i)) = (uint dstva + Z.of_nat i)%Z) ->
  umem_wr M dstva n src !! uint (add_vec_int dstva (Z.of_nat j)) = Some (src j).
Proof.
  induction n as [| k IH]; intros Hj Hlin; [lia |].
  cbn [umem_wr]. destruct (decide (j = k)) as [-> | Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne.
    + apply IH; [lia |]. intros i Hi. apply Hlin. lia.
    + rewrite (Hlin j ltac:(lia)) (Hlin k ltac:(lia)). lia.
Qed.

(* and what SURVIVES it: any va outside the run *)
Lemma umem_wr_lookup_out (M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) (va : Z) :
  (forall i, (i < n)%nat -> va <> uint (add_vec_int dstva (Z.of_nat i))) ->
  umem_wr M dstva n src !! va = M !! va.
Proof.
  induction n as [| k IH]; intros Hne; [reflexivity |].
  cbn [umem_wr].
  rewrite lookup_insert_ne;
    [| intros Heq; exact (Hne k ltac:(lia) (eq_sym Heq))].
  apply IH. intros i Hi. apply Hne. lia.
Qed.

Lemma umem_wr_dom (M : gmap Z (bv 8)) (dstva : mword 64) (n : nat)
    (src : nat -> bv 8) :
  (forall i, (i < n)%nat ->
     is_Some (M !! uint (add_vec_int dstva (Z.of_nat i)))) ->
  dom (umem_wr M dstva n src) = dom M.
Proof.
  induction n as [| k IH]; intros Hsome; [reflexivity |].
  cbn [umem_wr]. rewrite dom_insert_L.
  rewrite (IH ltac:(intros i Hi; apply Hsome; lia)).
  apply subseteq_union_1_L. apply singleton_subseteq_l.
  apply elem_of_dom. apply Hsome. lia.
Qed.

(* overwriting the same run wins outright *)
Lemma umem_write_overwrite (M : gmap Z (bv 8)) (a : Z) (n : nat) (f g : nat -> bv 8) :
  umem_write (umem_write M a n f) a n g = umem_write M a n g.
Proof.
  apply map_eq. intros va.
  destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hout].
  - apply in_run_iff in Hin as (k & Hk & ->).
    rewrite (umem_write_lookup_in (umem_write M a n f) a n g k Hk).
    rewrite (umem_write_lookup_in M a n g k Hk). reflexivity.
  - assert (Hne : forall k, (k < n)%nat -> va <> (a + Z.of_nat k)%Z)
      by (intros k Hk Heq; apply Hout; apply in_run_iff; eauto).
    rewrite (umem_write_lookup_out (umem_write M a n f) a n g va Hne).
    rewrite (umem_write_lookup_out M a n f va Hne).
    rewrite (umem_write_lookup_out M a n g va Hne). reflexivity.
Qed.

(* two ADJACENT runs are one run -- what makes a loop that fills page
   after page from a single source have a one-line invariant *)
Lemma umem_write_app (M : gmap Z (bv 8)) (a : Z) (n m : nat) (f : nat -> bv 8) :
  umem_write (umem_write M a n f) (a + Z.of_nat n)%Z m (fun i => f (n + i)%nat)
  = umem_write M a (n + m)%nat f.
Proof.
  induction m as [| k IH].
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [umem_write]. rewrite IH.
    replace (n + S k)%nat with (S (n + k))%nat by lia.
    cbn [umem_write].
    replace (a + Z.of_nat n + Z.of_nat k)%Z with (a + Z.of_nat (n + k))%Z
      by (rewrite Nat2Z.inj_add; lia).
    reflexivity.
Qed.

(* two adjacent runs of the SAME byte are one run -- what makes a loop
   that zeroes page after page have a one-line invariant *)
Lemma umem_write_const_app (M : gmap Z (bv 8)) (a : Z) (n m : nat) (c : bv 8) :
  umem_write (umem_write M a n (fun _ => c)) (a + Z.of_nat n)%Z m (fun _ => c)
  = umem_write M a (n + m)%nat (fun _ => c).
Proof.
  induction m as [| k IH].
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [umem_write]. rewrite IH.
    replace (n + S k)%nat with (S (n + k))%nat by lia.
    cbn [umem_write].
    replace (a + Z.of_nat n + Z.of_nat k)%Z with (a + Z.of_nat (n + k))%Z
      by (rewrite Nat2Z.inj_add; lia).
    reflexivity.
Qed.

Lemma umem_write_ext (M : gmap Z (bv 8)) (a : Z) (n : nat) (bs bs' : nat -> bv 8) :
  (forall j, (j < n)%nat -> bs j = bs' j) ->
  umem_write M a n bs = umem_write M a n bs'.
Proof.
  induction n as [| k IH]; intros He; [reflexivity |].
  cbn [umem_write]. rewrite (IH ltac:(intros j Hj; apply He; lia)).
  rewrite (He k ltac:(lia)). reflexivity.
Qed.

Lemma umem_write_dom (M : gmap Z (bv 8)) (a : Z) (n : nat) (bs : nat -> bv 8) :
  (forall j, (j < n)%nat -> is_Some (M !! (a + Z.of_nat j)%Z)) ->
  dom (umem_write M a n bs) = dom M.
Proof.
  intros Hsome. apply set_eq. intros va. rewrite !elem_of_dom.
  destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hout];
    [ apply in_run_iff in Hin as (j & Hj & ->) |].
  - rewrite (umem_write_lookup_in M a n bs j Hj).
    split; [intros _; exact (Hsome j Hj) | intros _; eauto].
  - assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z)
      by (intros j Hj Heq; apply Hout; apply in_run_iff; eauto).
    rewrite (umem_write_lookup_out M a n bs va Hne). reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* §3d'' Pure vocabulary of the LAZY view.                                *)
(*                                                                       *)
(* A va below [p->sz] that the table does not map is NOT an error: it is  *)
(* a page the kernel will allocate, ZERO-FILLED, the first time the       *)
(* process touches it (vmfault).  The process cannot tell that page from  *)
(* one already mapped, so neither should its abstract state.             *)
(* --------------------------------------------------------------------- *)

(* p->sz rounded up to a page boundary: the end of the address space the
   kernel maintains for the process *)
Definition pgroundup (sz : Z) : Z := ((sz + 4095) / 4096) * 4096.

(* a va the process may touch -- mapped or not yet faulted in *)
Definition uva_live (sz : Z) (va : Z) : Prop := (0 <= va < pgroundup sz)%Z.

(* THE PAGE OF A LIVE va IS LIVE.  vmfault maps the page of a va it has
   already checked against [p->sz]; this is what says every va of that page
   -- not just the faulting one -- was already in the process's view. *)
Lemma uva_live_page (sz va : Z) (j : nat) :
  (0 <= va)%Z -> (va < sz)%Z -> (j < 4096)%nat ->
  uva_live sz (4096 * (va / 4096) + Z.of_nat j)%Z.
Proof.
  intros Hva0 Hlt Hj. unfold uva_live, pgroundup.
  pose proof (Z.div_mod va 4096 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound va 4096 ltac:(lia)) as Hmb.
  pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)) as Hds.
  pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)) as Hsb.
  split; lia.
Qed.

Definition live_set (sz : Z) : gset Z := list_to_set (seqZ 0 (pgroundup sz)).

Lemma elem_of_live_set (sz va : Z) : va ∈ live_set sz <-> uva_live sz va.
Proof.
  unfold live_set, uva_live. rewrite elem_of_list_to_set elem_of_seqZ. lia.
Qed.

(* THE VIEW AT A LARGER SIZE.  Growing a process's size does not move a
   single byte it could already read: what changes is that more vas are
   LIVE, and a live va the table does not map reads as zero.  So the view
   at [sz] grows to [M ∪ (zeros over everything live at sz)] -- and
   because the union is left-biased, every byte [M] already recorded
   survives verbatim.  This is uvmalloc's whole effect on memory. *)
Definition umem_grow (M : gmap Z (bv 8)) (sz : Z) : gmap Z (bv 8) :=
  M ∪ gset_to_gmap (bv_0 8) (live_set sz).

Lemma gset_to_gmap_union_Z {A : Type} (c : A) (X Y : gset Z) :
  gset_to_gmap c (X ∪ Y) = gset_to_gmap c X ∪ gset_to_gmap c Y.
Proof.
  apply map_eq. intros a.
  destruct (decide (a ∈ X)) as [HX | HX].
  - assert (Hl : gset_to_gmap c (X ∪ Y) !! a = Some c).
    { apply lookup_gset_to_gmap_Some.
      split; [apply elem_of_union; by left | reflexivity]. }
    rewrite Hl. symmetry.
    apply (lookup_union_Some_l (gset_to_gmap c X) (gset_to_gmap c Y) a c).
    apply lookup_gset_to_gmap_Some. split; [exact HX | reflexivity].
  - rewrite (lookup_union_r (gset_to_gmap c X) (gset_to_gmap c Y) a);
      [| apply lookup_gset_to_gmap_None; exact HX].
    destruct (decide (a ∈ Y)) as [HY | HY].
    + assert (Hl : gset_to_gmap c (X ∪ Y) !! a = Some c).
      { apply lookup_gset_to_gmap_Some.
        split; [apply elem_of_union; by right | reflexivity]. }
      rewrite Hl. symmetry.
      apply lookup_gset_to_gmap_Some. split; [exact HY | reflexivity].
    + assert (Hl : gset_to_gmap c (X ∪ Y) !! a = None).
      { apply lookup_gset_to_gmap_None.
        intros Hin. apply elem_of_union in Hin as [Hc | Hc];
          [exact (HX Hc) | exact (HY Hc)]. }
      rewrite Hl. symmetry.
      apply lookup_gset_to_gmap_None. exact HY.
Qed.

(* two sizes with the same live set give the same view *)
Lemma umem_grow_cong (M : gmap Z (bv 8)) (sz sz' : Z) :
  (forall a : Z, uva_live sz a <-> uva_live sz' a) ->
  umem_grow M sz = umem_grow M sz'.
Proof.
  intros Hlv. unfold umem_grow.
  assert (Hls : live_set sz = live_set sz').
  { apply set_eq. intros a. rewrite !elem_of_live_set. apply Hlv. }
  rewrite Hls. reflexivity.
Qed.

(* growing to a size everything of which is already recorded is a no-op --
   how the loop's invariant starts, at [PGROUNDUP(oldsz)] *)
Lemma umem_grow_id (M : gmap Z (bv 8)) (sz : Z) :
  (forall a : Z, uva_live sz a -> is_Some (M !! a)) -> umem_grow M sz = M.
Proof.
  intros Hin. unfold umem_grow. apply map_eq. intros a.
  destruct (M !! a) as [bb |] eqn:Hb.
  - apply (lookup_union_Some_l M _ a bb Hb).
  - rewrite (lookup_union_r M _ a Hb).
    apply lookup_gset_to_gmap_None. intros Hel.
    apply elem_of_live_set in Hel.
    destruct (Hin a Hel) as [x Hx]. rewrite Hb in Hx. discriminate.
Qed.

(* ...and one page's worth of growth, which is what the loop does *)
Lemma umem_grow_step (M : gmap Z (bv 8)) (sz sz' : Z) (pg : gset Z) :
  (forall a : Z, uva_live sz' a <-> (uva_live sz a \/ a ∈ pg)) ->
  umem_grow M sz' = umem_grow M sz ∪ gset_to_gmap (bv_0 8) pg.
Proof.
  intros Hlv. unfold umem_grow.
  assert (Hls : live_set sz' = live_set sz ∪ pg).
  { apply set_eq. intros a.
    rewrite elem_of_union !elem_of_live_set. apply Hlv. }
  rewrite Hls gset_to_gmap_union_Z map_union_assoc. reflexivity.
Qed.

(* ...and the ROLLBACK: deleting exactly the range that became live undoes
   the growth.  uvmalloc's out-of-memory arm is this -- what the loop had
   added is precisely what uvmdealloc takes away, so the caller gets back
   the view it handed in, not a weaker one. *)
Lemma umem_grow_del (M : gmap Z (bv 8)) (sz sz' : Z) (a : Z) (n : nat) :
  (forall x : Z, uva_live sz x -> is_Some (M !! x)) ->
  (forall x : Z, is_Some (M !! x) -> ~ (a <= x < a + Z.of_nat n)%Z) ->
  (forall x : Z, uva_live sz' x
     <-> (uva_live sz x \/ (a <= x < a + Z.of_nat n)%Z)) ->
  umem_del (umem_grow M sz') a n = M.
Proof.
  intros Hcov Hout Hlv. apply map_eq. intros x.
  destruct (decide (a <= x < a + Z.of_nat n)%Z) as [Hin | Hno].
  - pose proof Hin as Hin'.
    apply in_run_iff in Hin' as (j & Hj & ->).
    rewrite (umem_del_lookup_in _ a n j Hj).
    destruct (M !! (a + Z.of_nat j)%Z) as [bb |] eqn:Hb; [| reflexivity].
    exfalso. exact (Hout _ ltac:(eauto) Hin).
  - assert (Hne : forall j, (j < n)%nat -> x <> (a + Z.of_nat j)%Z)
      by (intros j Hj Heq; apply Hno; apply in_run_iff; eauto).
    rewrite (umem_del_lookup_out _ a n x Hne).
    unfold umem_grow.
    destruct (M !! x) as [bb |] eqn:Hb.
    + apply (lookup_union_Some_l M _ x bb Hb).
    + rewrite (lookup_union_r M _ x Hb).
      apply lookup_gset_to_gmap_None. intros Hel.
      apply elem_of_live_set in Hel. apply (proj1 (Hlv x)) in Hel.
      destruct Hel as [Hlo | Hr]; [| exact (Hno Hr)].
      destruct (Hcov x Hlo) as [y Hy]. rewrite Hb in Hy. discriminate.
Qed.

(* the vas of ONE page, and the byte map one page's worth of bytes makes *)
Definition upage_dom (vpn : mword 27) : gset Z :=
  list_to_set ((fun j : nat => (bv_unsigned vpn * 4096 + Z.of_nat j)%Z)
               <$> seq 0 4096).

Lemma elem_of_upage_dom (vpn : mword 27) (va : Z) :
  va ∈ upage_dom vpn <->
  exists j, (j < 4096)%nat /\ va = (bv_unsigned vpn * 4096 + Z.of_nat j)%Z.
Proof.
  unfold upage_dom. rewrite elem_of_list_to_set elem_of_list_fmap. split.
  - intros (j & -> & Hj). apply elem_of_seq in Hj.
    exists j. split; [lia | reflexivity].
  - intros (j & Hj & ->). exists j.
    split; [reflexivity |]. apply elem_of_seq. lia.
Qed.

Definition upage_kv (vpn : mword 27) (bs : nat -> bv 8) : list (Z * bv 8) :=
  (fun j : nat => ((bv_unsigned vpn * 4096 + Z.of_nat j)%Z, bs j)) <$> seq 0 4096.

Definition upage_map (vpn : mword 27) (bs : nat -> bv 8) : gmap Z (bv 8) :=
  list_to_map (upage_kv vpn bs).

(* the KEYS, spelled without a [cbn]: [cbn] here would evaluate [seq 0 4096]
   into a 4096-element literal (durable-notes' [seq]-explosion trap). *)
Lemma upage_kv_fst (vpn : mword 27) (bs : nat -> bv 8) :
  (upage_kv vpn bs).*1
  = (fun j : nat => (bv_unsigned vpn * 4096 + Z.of_nat j)%Z) <$> seq 0 4096.
Proof.
  unfold upage_kv. rewrite <- list_fmap_compose.
  apply list_fmap_ext. intros i x _. reflexivity.
Qed.

(* [base.NoDup] and not [NoDup]: this file's [List] import makes the bare
   name Stdlib's, and [big_sepM_list_to_map] wants stdpp's. *)
Lemma upage_kv_nodup (vpn : mword 27) (bs : nat -> bv 8) :
  base.NoDup (upage_kv vpn bs).*1.
Proof.
  rewrite upage_kv_fst.
  apply NoDup_fmap_2_strong; [| apply NoDup_seq].
  intros x y Hx Hy Heq. apply elem_of_seq in Hx. apply elem_of_seq in Hy. lia.
Qed.

Lemma upage_map_lookup (vpn : mword 27) (bs : nat -> bv 8) (j : nat) :
  (j < 4096)%nat ->
  upage_map vpn bs !! (bv_unsigned vpn * 4096 + Z.of_nat j)%Z = Some (bs j).
Proof.
  intros Hj. unfold upage_map.
  apply elem_of_list_to_map_1; [ apply upage_kv_nodup |].
  unfold upage_kv. apply elem_of_list_fmap. exists j.
  split; [reflexivity |]. apply elem_of_seq. lia.
Qed.

Lemma upage_map_dom (vpn : mword 27) (bs : nat -> bv 8) :
  dom (upage_map vpn bs) = upage_dom vpn.
Proof.
  unfold upage_map, upage_dom.
  rewrite dom_list_to_map_L upage_kv_fst. reflexivity.
Qed.

Lemma upage_map_lookup_out (vpn : mword 27) (bs : nat -> bv 8) (va : Z) :
  va ∉ upage_dom vpn -> upage_map vpn bs !! va = None.
Proof.
  intros Hn. apply not_elem_of_dom. rewrite upage_map_dom. exact Hn.
Qed.

Section UserPtInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* §3b Generic big-op plumbing.                                        *)
  (*                                                                     *)
  (* Every bridge into or out of [umem_own] -- UserBytes.v's accessor    *)
  (* and ProcPtOwn.v's satp-switch dovetail -- gathers existential bytes *)
  (* out of a big-op over a finite set, and reindexes such a big-op      *)
  (* along an injection.  Neither of those files imports the other, so   *)
  (* both live here.  They are POLYMORPHIC in the key type on purpose:   *)
  (* that is also what lets them be used at BOTH [Countable Arch.pa]     *)
  (* instances the tree carries (UserBytes.v section 3b).                *)
  (* ------------------------------------------------------------------ *)

  Lemma bigset_gather {A} `{Countable A} (Phi : A -> bv 8 -> iProp Σ) (D : gset A) :
    ([∗ set] x ∈ D, ∃ b : bv 8, Phi x b) ⊣⊢
    (∃ m : gmap A (bv 8), ⌜dom m = D⌝ ∗ [∗ map] x ↦ b ∈ m, Phi x b).
  Proof.
    iSplit.
    - iIntros "H".
      iInduction D as [| x D' Hnin] "IH" using set_ind_L.
      + iExists ∅. rewrite big_sepM_empty dom_empty_L. iSplit; done.
      + rewrite big_sepS_insert; [| exact Hnin].
        iDestruct "H" as "[Hx HD]".
        iDestruct ("IH" with "HD") as (m) "[%Hdom Hm]".
        iDestruct "Hx" as (b) "Hx".
        assert (Hnone : m !! x = None)
          by (apply not_elem_of_dom; rewrite Hdom; exact Hnin).
        iExists (<[x := b]> m).
        rewrite big_sepM_insert; [| exact Hnone].
        iFrame "Hx Hm". iPureIntro. rewrite dom_insert_L Hdom. reflexivity.
    - iIntros "H". iDestruct "H" as (m) "[%Hdom Hm]".
      rewrite <- Hdom.
      rewrite <- (big_sepM_dom (fun x => (∃ b : bv 8, Phi x b)%I) m).
      iApply (big_sepM_impl with "Hm").
      iIntros "!>" (x b _) "Hb". iExists b. iExact "Hb".
  Qed.

  (* The target set is taken ABSTRACTLY and characterised by its
     membership, not spelled as [set_map h X]: the two consumers hold a
     [dom md] and a [ud_pas P] respectively, and (see above) the [gset]
     of physical addresses each of them means is at its own [Countable]
     instance, which a [set_map] in this statement would pin to THIS
     file's. *)
  Lemma bigset_reindex {A B} `{Countable A} `{Countable B}
      (h : A -> B) (X : gset A) (S : gset B) (Phi : B -> iProp Σ) :
    (forall x y, x ∈ X -> y ∈ X -> h x = h y -> x = y) ->
    (forall a, a ∈ S <-> exists x, x ∈ X /\ h x = a) ->
    ([∗ set] x ∈ X, Phi (h x)) ⊣⊢ ([∗ set] a ∈ S, Phi a).
  Proof.
    (* NO [set_solver] anywhere below, on purpose: on an abstract
       [Countable] key the hypothesis-discharging goals it would be aimed
       at include a bare [h y = h z], and there it does not terminate. *)
    revert S.
    induction X as [| x X Hnin IH] using set_ind_L; intros S Hinj HS.
    - assert (S = ∅) as ->.
      { apply set_eq. intros a. split.
        - intros Ha. apply HS in Ha as (y & Hy & _).
          exfalso. exact (not_elem_of_empty y Hy).
        - intros Ha. exfalso. exact (not_elem_of_empty a Ha). }
      rewrite !big_sepS_empty. reflexivity.
    - assert (Hxin : x ∈ ({[x]} ∪ X : gset A)).
      { apply elem_of_union. left. apply elem_of_singleton. reflexivity. }
      assert (Hsub : forall y : A, y ∈ X -> y ∈ ({[x]} ∪ X : gset A)).
      { intros y Hy. apply elem_of_union. right. exact Hy. }
      assert (Hhx : h x ∈ S).
      { apply HS. exists x. split; [exact Hxin | reflexivity]. }
      assert (HS' : forall a, a ∈ S ∖ {[h x]} <-> exists y, y ∈ X /\ h y = a).
      { intros a. rewrite elem_of_difference elem_of_singleton. split.
        - intros [Ha Hne]. apply HS in Ha as (y & Hy & <-).
          apply elem_of_union in Hy as [Hy | Hy].
          + apply elem_of_singleton in Hy as ->. exfalso. exact (Hne eq_refl).
          + exists y. split; [exact Hy | reflexivity].
        - intros (y & Hy & <-). split.
          + apply HS. exists y. split; [exact (Hsub y Hy) | reflexivity].
          + intros Heq. apply Hnin.
            rewrite <- (Hinj y x (Hsub y Hy) Hxin Heq). exact Hy. }
      assert (Hdisj1 : ({[x]} : gset A) ## X).
      { apply elem_of_disjoint. intros y Hy1 Hy2.
        apply elem_of_singleton in Hy1 as ->. exact (Hnin Hy2). }
      assert (Hdisj2 : ({[h x]} : gset B) ## S ∖ {[h x]}).
      { apply elem_of_disjoint. intros a Ha1 Ha2.
        apply elem_of_singleton in Ha1 as ->.
        apply elem_of_difference in Ha2 as [_ Hne].
        apply Hne. apply elem_of_singleton. reflexivity. }
      assert (HSeq : S = {[h x]} ∪ (S ∖ {[h x]})).
      { apply set_eq. intros a.
        rewrite elem_of_union elem_of_difference elem_of_singleton.
        destruct (decide (a = h x)) as [-> | Hne].
        - split; [intros _; left; reflexivity | intros _; exact Hhx].
        - split.
          + intros Ha. right. split; [exact Ha | exact Hne].
          + intros [Hc | [Ha _]]; [ exfalso; exact (Hne Hc) | exact Ha ]. }
      rewrite HSeq.
      rewrite (big_sepS_union _ {[x]} X Hdisj1).
      rewrite (big_sepS_union _ {[h x]} (S ∖ {[h x]}) Hdisj2).
      rewrite !big_sepS_singleton.
      rewrite (IH (S ∖ {[h x]})
                 (fun y z Hy Hz Heq => Hinj y z (Hsub y Hy) (Hsub z Hz) Heq) HS').
      reflexivity.
  Qed.

  (* the two composed: a big-op over a finite INDEX set, whose predicate
     is a per-index existential byte at an injectively-mapped address,
     IS one byte map at the image.  This is the only shape the bridges
     use; the image is again taken abstractly, as a PREDICATE. *)
  Lemma bigset_gather_reindex {A B} `{Countable A} `{Countable B}
      (f : A -> B) (D : gset A) (Psi : B -> Prop) (Phi : B -> bv 8 -> iProp Σ) :
    (forall x y, x ∈ D -> y ∈ D -> f x = f y -> x = y) ->
    (forall a, Psi a <-> exists x, x ∈ D /\ f x = a) ->
    ([∗ set] x ∈ D, ∃ b : bv 8, Phi (f x) b) ⊣⊢
    (∃ m : gmap B (bv 8), ⌜forall a, Psi a <-> is_Some (m !! a)⌝ ∗
       [∗ map] a ↦ b ∈ m, Phi a b).
  Proof.
    intros Hinj HPsi.
    assert (Hmem : forall a : B, a ∈ set_map (D := gset B) f D <-> Psi a).
    { intros a. rewrite elem_of_map (HPsi a). split.
      - intros (x & -> & Hx). exists x. split; [exact Hx | reflexivity].
      - intros (x & Hx & <-). exists x. split; [reflexivity | exact Hx]. }
    assert (Himg : forall a : B,
              a ∈ set_map (D := gset B) f D <-> exists x, x ∈ D /\ f x = a).
    { intros a. rewrite (Hmem a). exact (HPsi a). }
    rewrite (bigset_reindex f D (set_map (D := gset B) f D)
               (fun a => (∃ b : bv 8, Phi a b)%I) Hinj Himg).
    rewrite (bigset_gather Phi (set_map (D := gset B) f D)).
    iSplit.
    - iIntros "H". iDestruct "H" as (m) "[%Hdom Hm]". iExists m. iFrame "Hm".
      iPureIntro. intros a. rewrite <- Hmem, <- Hdom. apply elem_of_dom.
    - iIntros "H". iDestruct "H" as (m) "[%Hd Hm]". iExists m. iFrame "Hm".
      iPureIntro. apply set_eq. intros a.
      rewrite elem_of_dom. rewrite <- Hd. rewrite Hmem. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3c The pre-port page ownership, unchanged.                         *)
  (* ------------------------------------------------------------------ *)

  (* the owned bytes of the mapped pages, contents EXISTENTIAL.  One
     aggregated byte map -- accesses look up plain addresses, no per-page
     decomposition; a flat pa-set dedups pages shared by several vpns. *)
  Definition udata_own (data : gset Arch.pa) : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8),
       ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₚ b)%I.

  (* ------------------------------------------------------------------ *)
  (* §3d THE ABSTRACT STATE and the bundle.                              *)
  (* ------------------------------------------------------------------ *)

  (* the process's memory: one byte per mapped user virtual address.  The
     domain is PINNED to the table's address space, so [umem_own P M]
     says "this is ALL of the user's memory", not "some of it". *)
  Definition umem_own (P : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    (⌜dom M = uva_dom P⌝ ∗
     [∗ map] va ↦ b ∈ M, (uva_pa P va : Arch.pa) ↦ₚ b)%I.

  Definition umem_any (P : uptd) : iProp Σ := (∃ M, umem_own P M)%I.

  (* a mapped va is exactly a va the image records *)
  Lemma umem_own_lookup_is_Some (P : uptd) (M : gmap Z (bv 8)) (va : Z) :
    dom M = uva_dom P -> (is_Some (M !! va) <-> uva_mapped P va).
  Proof.
    intros Hdom. rewrite <- elem_of_dom. rewrite Hdom. apply elem_of_uva_dom.
  Qed.

  (* READ OR WRITE ONE BYTE, at a user virtual address: the byte comes out
     at the address it translates to, and handing a cell back at a new
     value moves the abstract state by exactly that insert.  This is the
     accessor the proofs that thread [M] will consume. *)
  Lemma umem_own_acc (P : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
    M !! va = Some b ->
    umem_own P M -∗
    ((uva_pa P va : Arch.pa) ↦ₚ b ∗
     (∀ b' : bv 8, (uva_pa P va : Arch.pa) ↦ₚ b' -∗ umem_own P (<[va := b']> M))).
  Proof.
    iIntros (Hl) "[%Hdom HM]".
    iDestruct (big_sepM_insert_acc with "HM") as "[Hb Hrest]"; [exact Hl |].
    iFrame "Hb". iIntros (b') "Hb". iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Hva : va ∈ uva_dom P)
        by (rewrite <- Hdom; apply elem_of_dom; exists b; exact Hl).
      apply set_eq. intros y. rewrite elem_of_union elem_of_singleton. split.
      - intros [-> | Hy]; [exact Hva | exact Hy].
      - intros Hy. right. exact Hy. }
    iApply ("Hrest" with "Hb").
  Qed.

  (* THE SET FORM both bridges go through: forgetting the contents turns
     the map into a big-op over the address space. *)
  Lemma umem_any_set (P : uptd) :
    umem_any P ⊣⊢
    ([∗ set] va ∈ uva_dom P, ∃ b : bv 8, (uva_pa P va : Arch.pa) ↦ₚ b).
  Proof.
    rewrite /umem_any /umem_own.
    symmetry.
    apply (bigset_gather (fun va b => ((uva_pa P va : Arch.pa) ↦ₚ b)%I) (uva_dom P)).
  Qed.

  (* THE USER-EXECUTION PT BUNDLE: the tree invariant + the process's
     memory + the no-aliasing and access-classification facts. *)
  Definition user_pt_inv (P : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    (utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) ∗
     umem_own P M ∗
     ⌜uva_pa_inj P⌝ ∗
     ⌜upt_acc_wf P.(ud_um)⌝)%I.

  (* ...with the memory quantified: what user execution preserves *)
  Definition user_pt_any (P : uptd) : iProp Σ := (∃ M, user_pt_inv P M)%I.

  Lemma user_pt_any_unfold (P : uptd) :
    user_pt_any P ⊣⊢
    (utlb_inv_pt P.(ud_root) P.(ud_tfp) P.(ud_um) ∗ umem_any P ∗
     ⌜uva_pa_inj P⌝ ∗ ⌜upt_acc_wf P.(ud_um)⌝).
  Proof.
    rewrite /user_pt_any /user_pt_inv /umem_any. iSplit.
    - iIntros "H". iDestruct "H" as (M) "(Htlb & Hm & %Hinj & %Hacc)".
      iFrame "Htlb". iSplitL "Hm"; [iExists M; iExact "Hm" |].
      iPureIntro. split; [exact Hinj | exact Hacc].
    - iIntros "(Htlb & Hm & %Hinj & %Hacc)". iDestruct "Hm" as (M) "Hm".
      iExists M. iFrame "Htlb Hm". iPureIntro. split; [exact Hinj | exact Hacc].
  Qed.

  Lemma user_pt_any_intro (P : uptd) (M : gmap Z (bv 8)) :
    user_pt_inv P M -∗ user_pt_any P.
  Proof. iIntros "H". iExists M. iExact "H". Qed.

  (* ------------------------------------------------------------------ *)
  (* §3e THE BYTE WINDOW: reading and writing a RUN of user vas.         *)
  (*                                                                    *)
  (* The kernel's copy loops (copyin / copyout) work one chunk at a time *)
  (* inside one page, and what they need of the abstract state is ONE    *)
  (* accessor: take the [n] bytes at [a], give them back -- possibly at  *)
  (* new values -- and move [M] by exactly that write.  The window form  *)
  (* rather than a page form is deliberate: it is what the loops hold,   *)
  (* and it makes the whole thing an induction on [n] over              *)
  (* [big_sepM_delete] instead of surgery on a 4096-key submap.         *)
  (* ------------------------------------------------------------------ *)

  Lemma bigM_window (Phi : Z -> bv 8 -> iProp Σ) (M : gmap Z (bv 8))
      (a : Z) (n : nat) :
    (forall j, (j < n)%nat -> is_Some (M !! (a + Z.of_nat j)%Z)) ->
    ([∗ map] va ↦ b ∈ M, Phi va b) ⊣⊢
    ([∗ list] j ∈ seq 0 n, Phi (a + Z.of_nat j)%Z (M !!! (a + Z.of_nat j)%Z)) ∗
    ([∗ map] va ↦ b ∈ umem_del M a n, Phi va b).
  Proof.
    induction n as [| k IH]; intros Hsome.
    - cbn [umem_del]. rewrite big_sepL_nil bi.emp_sep. reflexivity.
    - assert (Hk : forall j, (j < k)%nat -> is_Some (M !! (a + Z.of_nat j)%Z))
        by (intros j Hj; apply Hsome; lia).
      assert (Hdk : umem_del M a k !! (a + Z.of_nat k)%Z = M !! (a + Z.of_nat k)%Z)
        by (apply umem_del_lookup_out; intros j Hj Heq; lia).
      destruct (Hsome k ltac:(lia)) as [bk Hbk].
      rewrite (IH Hk).
      rewrite seq_S big_sepL_app big_sepL_singleton Nat.add_0_l.
      cbn [umem_del].
      rewrite (big_sepM_delete Phi (umem_del M a k) (a + Z.of_nat k)%Z bk
                 ltac:(rewrite Hdk; exact Hbk)).
      assert (Hkt : M !!! (a + Z.of_nat k)%Z = bk)
        by (rewrite lookup_total_alt Hbk; reflexivity).
      rewrite Hkt.
      iSplit.
      + iIntros "[Hw [Hb Hr]]". iFrame "Hw Hb Hr".
      + iIntros "[[Hw Hb] Hr]". iFrame "Hw Hb Hr".
  Qed.

  (* THE ACCESSOR.  [n] bytes at [a], at the values [M] records, and a
     wand that takes them back at ANY values and moves [M] by exactly
     that write.  [copyin] instantiates the wand at the bytes it got
     (nothing moves); [copyout] instantiates it at what it wrote. *)
  Lemma umem_own_window (P : uptd) (M : gmap Z (bv 8)) (a : Z) (n : nat) :
    (forall j, (j < n)%nat -> is_Some (M !! (a + Z.of_nat j)%Z)) ->
    umem_own P M -∗
      ([∗ list] j ∈ seq 0 n,
         (uva_pa P (a + Z.of_nat j)%Z : Arch.pa) ↦ₚ (M !!! (a + Z.of_nat j)%Z)) ∗
      (∀ bs : nat -> bv 8,
         ([∗ list] j ∈ seq 0 n,
            (uva_pa P (a + Z.of_nat j)%Z : Arch.pa) ↦ₚ bs j) -∗
         umem_own P (umem_write M a n bs)).
  Proof.
    intros Hsome. iIntros "[%Hdom HM]".
    rewrite (bigM_window (fun va b => ((uva_pa P va : Arch.pa) ↦ₚ b)%I) M a n Hsome).
    iDestruct "HM" as "[Hwin Hrest]".
    iFrame "Hwin".
    iIntros (bs) "Hwin'".
    assert (Hsome' : forall j, (j < n)%nat ->
              is_Some (umem_write M a n bs !! (a + Z.of_nat j)%Z))
      by (intros j Hj; rewrite (umem_write_lookup_in M a n bs j Hj); eauto).
    iSplitR.
    { iPureIntro. rewrite <- Hdom. exact (umem_write_dom M a n bs Hsome). }
    rewrite (bigM_window (fun va b => ((uva_pa P va : Arch.pa) ↦ₚ b)%I)
               (umem_write M a n bs) a n Hsome').
    rewrite (umem_del_write M a n bs). iFrame "Hrest".
    iApply (big_sepL_mono with "Hwin'"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite lookup_total_alt (umem_write_lookup_in M a n bs _ Hlt). reflexivity.
  Qed.

  (* one page's worth of per-offset resources IS the map that page's
     bytes make -- the shape vmfault's fresh page arrives in, and the
     shape [umem_own] wants *)
  Lemma bigL_page_map (Phi : Z -> bv 8 -> iProp Σ) (vpn : mword 27)
      (bs : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 4096,
       Phi (bv_unsigned vpn * 4096 + Z.of_nat j)%Z (bs j)) ⊣⊢
    ([∗ map] va ↦ b ∈ upage_map vpn bs, Phi va b).
  Proof.
    rewrite /upage_map (big_sepM_list_to_map Phi _ (upage_kv_nodup vpn bs)).
    rewrite /upage_kv big_sepL_fmap. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3f THE LAZY VIEW: the pages the process has NOT faulted in yet.     *)
  (*                                                                    *)
  (* [umem_lazy P sz M] says [M] covers EVERYTHING below [p->sz] rounded *)
  (* up -- with the real byte wherever the table has a leaf, and a 0     *)
  (* wherever it does not.  THE OWNERSHIP OF A LAZY PAGE IS NOTHING AT   *)
  (* ALL (there is no page to own), which is exactly why vmfault         *)
  (* PRESERVES this view instead of extending it: the byte the process   *)
  (* reads after the fault is the same 0 the view already recorded.      *)
  (*                                                                    *)
  (* [Mp] -- the mapped half -- is existential rather than a parameter   *)
  (* because it is a FUNCTION of [M] and the table; carrying it would    *)
  (* mean stating that function, and every user of this predicate wants  *)
  (* [M].                                                                *)
  (* ------------------------------------------------------------------ *)
  Definition umem_lazy (P : uptd) (sz : Z) (M : gmap Z (bv 8)) : iProp Σ :=
    (∃ Mp : gmap Z (bv 8),
       ⌜Mp ⊆ M⌝ ∗
       ⌜forall va, is_Some (M !! va) <-> (uva_mapped P va \/ uva_live sz va)⌝ ∗
       ⌜forall va, ~ uva_mapped P va -> uva_live sz va ->
                   M !! va = Some (bv_0 8)⌝ ∗
       umem_own P Mp)%I.

  (* the mapped half is what the OWNERSHIP is, so the lazy view weakens
     to the mapped-only one and back *)
  Lemma umem_lazy_any (P : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    umem_lazy P sz M -∗ umem_any P.
  Proof.
    iIntros "H". iDestruct "H" as (Mp) "(_ & _ & _ & Hm)".
    iExists Mp. iExact "Hm".
  Qed.

  Lemma umem_lazy_intro (P : uptd) (sz : Z) :
    umem_any P -∗ ∃ M : gmap Z (bv 8), umem_lazy P sz M.
  Proof.
    iIntros "H". iDestruct "H" as (Mp) "Hm".
    iDestruct "Hm" as "[%Hdom Hm]".
    iExists (Mp ∪ gset_to_gmap (bv_0 8) (live_set sz)), Mp.
    assert (Hmp : forall va, is_Some (Mp !! va) <-> uva_mapped P va).
    { intros va. rewrite <- elem_of_dom. rewrite Hdom. apply elem_of_uva_dom. }
    iSplitR; [iPureIntro; apply map_union_subseteq_l |].
    assert (Hgz : forall va, is_Some (gset_to_gmap (bv_0 8) (live_set sz) !! va)
                             <-> uva_live sz va).
    { intros va. rewrite <- elem_of_dom. rewrite dom_gset_to_gmap.
      apply elem_of_live_set. }
    iSplitR.
    { iPureIntro. intros va. rewrite lookup_union_is_Some.
      rewrite (Hmp va) (Hgz va). reflexivity. }
    iSplitR.
    { iPureIntro. intros va Hnm Hlv.
      rewrite lookup_union_r; [| apply not_elem_of_dom; rewrite Hdom;
                                 intros Hin; apply Hnm; by apply elem_of_uva_dom].
      apply lookup_gset_to_gmap_Some.
      split; [ by apply elem_of_live_set | reflexivity]. }
    iSplitR; [iPureIntro; exact Hdom |]. iExact "Hm".
  Qed.

  (* on a MAPPED va the two halves agree, which is what makes the window
     accessor below read [M] and hand back [Mp] *)
  Lemma umem_lazy_mapped_lookup (P : uptd) (M Mp : gmap Z (bv 8)) (va : Z) :
    Mp ⊆ M -> dom Mp = uva_dom P -> uva_mapped P va ->
    Mp !!! va = M !!! va.
  Proof.
    intros Hsub Hdom Hm.
    assert (Hs : is_Some (Mp !! va))
      by (apply elem_of_dom; rewrite Hdom; by apply elem_of_uva_dom).
    destruct Hs as [b Hb].
    rewrite !lookup_total_alt Hb (lookup_weaken _ _ _ _ Hb Hsub). reflexivity.
  Qed.

  (* THE WINDOW, at the lazy view.  Only MAPPED vas can be borrowed --
     a lazy page has no bytes to lend, and a caller that wants one calls
     vmfault first. *)
  Lemma umem_lazy_window (P : uptd) (sz : Z) (M : gmap Z (bv 8))
      (a : Z) (n : nat) :
    (forall j, (j < n)%nat -> uva_mapped P (a + Z.of_nat j)%Z) ->
    umem_lazy P sz M -∗
      ([∗ list] j ∈ seq 0 n,
         (uva_pa P (a + Z.of_nat j)%Z : Arch.pa) ↦ₚ (M !!! (a + Z.of_nat j)%Z)) ∗
      (∀ bs : nat -> bv 8,
         ([∗ list] j ∈ seq 0 n,
            (uva_pa P (a + Z.of_nat j)%Z : Arch.pa) ↦ₚ bs j) -∗
         umem_lazy P sz (umem_write M a n bs)).
  Proof.
    intros Hmap. iIntros "H".
    iDestruct "H" as (Mp) "(%Hsub & %Hdm & %Hlz & Hm)".
    iDestruct "Hm" as "[%Hdom Hm]".
    assert (Hsome : forall j, (j < n)%nat -> is_Some (Mp !! (a + Z.of_nat j)%Z)).
    { intros j Hj. apply elem_of_dom. rewrite Hdom.
      apply elem_of_uva_dom. exact (Hmap j Hj). }
    assert (Hagree : forall j, (j < n)%nat ->
              Mp !!! (a + Z.of_nat j)%Z = M !!! (a + Z.of_nat j)%Z)
      by (intros j Hj; exact (umem_lazy_mapped_lookup P M Mp _ Hsub Hdom (Hmap j Hj))).
    iAssert (umem_own P Mp) with "[Hm]" as "Hm".
    { iSplitR; [iPureIntro; exact Hdom |]. iExact "Hm". }
    iDestruct (umem_own_window P Mp a n Hsome with "Hm") as "[Hwin Hback]".
    iSplitL "Hwin".
    { iApply (big_sepL_mono with "Hwin"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l (Hagree i Hlt).
      reflexivity. }
    iIntros (bs) "Hw".
    iDestruct ("Hback" $! bs with "Hw") as "Hm".
    iExists (umem_write Mp a n bs).
    (* the write lands only on MAPPED vas, so the lazy half does not move *)
    assert (Hout : forall va, ~ uva_mapped P va ->
              forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z)
      by (intros va Hnm j Hj ->; exact (Hnm (Hmap j Hj))).
    iSplitR.
    { iPureIntro. apply map_subseteq_spec. intros va bb Hbb.
      destruct (decide (a <= va < a + Z.of_nat n)%Z) as [Hin | Hoo].
      - apply in_run_iff in Hin as (j & Hj & ->).
        rewrite (umem_write_lookup_in Mp a n bs j Hj) in Hbb.
        rewrite (umem_write_lookup_in M a n bs j Hj). exact Hbb.
      - assert (Hne : forall j, (j < n)%nat -> va <> (a + Z.of_nat j)%Z)
          by (intros j Hj Heq; apply Hoo; apply in_run_iff; eauto).
        rewrite (umem_write_lookup_out Mp a n bs va Hne) in Hbb.
        rewrite (umem_write_lookup_out M a n bs va Hne).
        exact (lookup_weaken _ _ _ _ Hbb Hsub). }
    iSplitR.
    { iPureIntro. intros va. rewrite <- (Hdm va). rewrite <- !elem_of_dom.
      rewrite (umem_write_dom M a n bs
                 ltac:(intros j Hj; apply (proj2 (Hdm _));
                       left; exact (Hmap j Hj))).
      reflexivity. }
    iSplitR.
    { iPureIntro. intros va Hnm Hlv.
      rewrite (umem_write_lookup_out M a n bs va (Hout va Hnm)).
      exact (Hlz va Hnm Hlv). }
    iExact "Hm".
  Qed.

End UserPtInv.

(* ===================================================================== *)
(* §4 The U-mode Ok absorption instance: a user-mapped va whose leaf       *)
(*    passes the check translates to the leaf page; the invariant absorbs  *)
(*    whatever the walk did (hit / TLB fill / A-D write-back).             *)
(* ===================================================================== *)

Section UserPtTranslate.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma utlb_inv_pt_translateAddr_u (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va pa : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok acc w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hl Hchk Hcanon Hout Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    apply (utlb_inv_pt_translateAddr acc User uroot tfp um w va pa σ
             Hchk (or_intror (or_intror Hl))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_U_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.


  (* §4b pure-fact extraction: the PMP entry-0 facts, borrowed from the
     bundle (used before a translation move and, transported, after it) *)
  Lemma utlb_inv_pt_pmp_facts (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (σ : mstate) :
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜(pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
      zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
      (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)%type⌝.
  Proof.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro.
    rewrite Hpcv Hpav. auto 8.
  Qed.

End UserPtTranslate.

(* ===================================================================== *)
(* §5 The U-mode FAULT head: non-canonical / unmapped / denied vas page-  *)
(*    fault with the state UNCHANGED (fault paths write nothing), the     *)
(*    invariant merely borrowed.  The exception value comes through a     *)
(*    [translationException] premise the caller discharges per access     *)
(*    (fetch -> E_Fetch_Page_Fault, load -> E_Load_Page_Fault,            *)
(*    store/AMO -> E_SAMO_Page_Fault) by [cbn; apply exec_returnm].       *)
(* ===================================================================== *)

Section UserPtFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (acc : MemoryAccessType mem_payload).

  (* NON-CANONICAL va: faults at the canonicality test; the invariant is
     borrowed only for the satp mode dispatch *)
  Lemma utlb_inv_pt_translateAddr_u_noncanon (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    exec (translationException acc (PTW_Invalid_Addr tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hcanon Hcp HSXL Heff Hss Hte.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_translateAddr_pt_front_noncanon acc User e usatp va σ
             Heff Hss Hcp
             (exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode)
             Hsatpv Hcanon Hte).
  Qed.

  (* UNMAPPED vpn (not the trampoline/trapframe, not in the user map):
     never TLB-resident (the keystone), and the walk stops at an invalid
     word in the owned tree *)
  Lemma utlb_inv_pt_translateAddr_u_unmapped (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    um !! svpn_of va = None ->
    svpn_of va <> tramp_vpn ->
    svpn_of va <> tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_Invalid_PTE tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hnone Hnt Hntf Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof Hspec as (Hbase & _ & _ & _ & Hblkspec).
    (* the spec blocks in the xv6 ZERO shape; the ownership lemma only needs
       model-invalidity *)
    pose proof (PtBuild.ptree_blocks0_blocks t (svpn_of va)
                  (Hblkspec (svpn_of va) Hnt Hntf Hnone)) as Hblk.
    iDestruct (ptree_own_blocked_mem σ (DfracOwn 1) t (svpn_of va) Hblk with "Hgh Ht")
      as %Hstop.
    iPureIntro.
    set (vpn := svpn_of va) in *.
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
      by exact (tlb_ok_pt_lookup_blocked t vpn tlbvec σ Htlbok Hblk Htlbv).
    (* the stopping prefix, as [read_pte] facts at the walk's spellings *)
    assert (Hstop' :
      (exists w2,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok w2, σ) /\ pte_invalid w2)
      \/ (exists p2 w1,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok p2, σ) /\ pte_valid p2 /\ pte_ptr p2 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) σ
            = Some (Ok w1, σ) /\ pte_invalid w1)
      \/ (exists p2 p1 w0,
          exec (read_pte (Physaddr (u_pte_addr uroot (subrange_vec_dec vpn 26 18))) 8) σ
            = Some (Ok p2, σ) /\ pte_valid p2 /\ pte_ptr p2 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) σ
            = Some (Ok p1, σ) /\ pte_valid p1 /\ pte_ptr p1 /\
          exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) σ
            = Some (Ok w0, σ) /\ pte_invalid w0)).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr uroot (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      destruct Hstop as
        [ (w2 & Hsm2 & Hinv2)
        | [ (p2 & w1 & Hsm2 & Hv2 & Hn2 & Hsm1 & Hinv1)
          | (p2 & p1 & w0 & Hsm2 & Hv2 & Hn2 & Hsm1 & Hv1 & Hn1 & Hsm0 & Hinv0) ] ].
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2))
          as (region2 & Hm2 & Hs2).
        left. exists w2.
        split; [| exact Hinv2].
        exact (pt_read_pte_slot σ _ w2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif).
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2))
          as (region2 & Hm2 & Hs2).
        destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1))
          as (region1 & Hm1 & Hs1).
        right; left. exists p2, w1.
        split; [exact (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif) |].
        split; [exact Hv2 |]. split; [exact Hn2 |].
        split; [| exact Hinv1].
        exact (pt_read_pte_slot σ _ w1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif).
      - rewrite Ha2 in Hsm2.
        destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2))
          as (region2 & Hm2 & Hs2).
        destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1))
          as (region1 & Hm1 & Hs1).
        destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0))
          as (region0 & Hm0 & Hs0).
        right; right. exists p2, p1, w0.
        split; [exact (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif) |].
        split; [exact Hv2 |]. split; [exact Hn2 |].
        split; [exact (pt_read_pte_slot σ _ p1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif) |].
        split; [exact Hv1 |]. split; [exact Hn1 |].
        split; [| exact Hinv0].
        exact (pt_read_pte_slot σ _ w0 region0 Hsm0 HA' Hord' HR' Hcov' Hm0 Hs0 Hhtif). }
    apply (exec_translateAddr_pt_front_err acc User vpn uroot
             (PTW_Invalid_PTE tt) e usatp va σ
             Heff Hss Hcp
             (exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode)
             Hsatpv Hppn Hasid Hcanon eq_refl
             (fun mxr do_sum =>
                exec_translate_pt_blocks acc User mxr do_sum vpn uroot σ Hstop' Hlk)
             Hte).
  Qed.

  (* MAPPED but DENIED (kernel-only trampoline/trapframe pages, or a user
     page whose flags deny this access): the walk reaches the leaf and the
     check fails; a RESIDENT entry (cached by an S-phase access or an
     earlier permitted access) replays the stored check and fails the same
     way -- either way no write, no fill, state unchanged. *)
  Lemma utlb_inv_pt_translateAddr_u_denied (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va : mword 64) (e : ExceptionType) (σ : mstate) :
    upt_leaf_at tfp um (svpn_of va) w ->
    uleaf_denied acc w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_No_Permission tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hleaf Hden Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof Hspec as (Hbase & _).
    destruct (upt_spec_maps uroot tfp um t (svpn_of va) w Hspec Hleaf)
      as (p2 & p1 & a0 & d0 & Hmaps).
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & _ & _).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) t (svpn_of va) p2 p1 _ Hmaps
                 with "Hgh Ht") as %(Hsm2 & Hsm1 & Hsm0).
    iPureIntro.
    set (vpn := svpn_of va) in *.
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Htm := exec_translationMode_U_sv39 usatp σ HSXL Hsatpv Hmode).
    (* the walk-DENIED translate (shared by the empty-slot and
       foreign-entry cases) *)
    assert (Hwalk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ) ->
      forall mxr do_sum,
        exec (translate 39 (mword_of_int 0 : mword 16) uroot vpn acc User mxr do_sum tt) σ
        = Some (Err (PTW_No_Permission tt, tt), σ)).
    { intros Hlk mxr do_sum.
      assert (Ha2 : pt_addr2 t vpn = u_pte_addr uroot (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2.
      destruct (Hpmar (u_pte_addr uroot (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2))
        as (region2 & Hm2 & Hs2).
      destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1))
        as (region1 & Hm1 & Hs1).
      destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0))
        as (region0 & Hm0 & Hs0).
      exact (exec_translate_pt_denied acc User mxr do_sum vpn uroot
               p2 p1 (pte_set_ad w a0 d0) σ
               Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hden a0 d0 mxr do_sum)
               (pt_read_pte_slot σ _ p2 region2 Hsm2 HA' Hord' HR' Hcov' Hm2 Hs2 Hhtif)
               (pt_read_pte_slot σ _ p1 region1 Hsm1 HA' Hord' HR' Hcov' Hm1 Hs1 Hhtif)
               (pt_read_pte_slot σ _ (pte_set_ad w a0 d0) region0 Hsm0
                  HA' Hord' HR' Hcov' Hm0 Hs0 Hhtif)
               Hlk). }
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & q0 & a' & d' & Hm0' & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* own (A/D-variant) entry resident: the HIT replays the check *)
        destruct (ptree_maps_det t vpn q2 q1 q0 p2 p1 (pte_set_ad w a0 d0) Hm0' Hmaps)
          as (-> & -> & ->).
        assert (Htr : forall mxr do_sum,
          exec (translate 39 (mword_of_int 0 : mword 16) uroot vpn acc User mxr do_sum tt) σ
          = Some (Err (PTW_No_Permission tt, tt), σ)).
        { intros mxr do_sum.
          unfold translate.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlbv Hslot
                        (uwe_match_self vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')))).
          cbn match.
          assert (Hdenc : pte_check_denied acc User mxr do_sum
                    (PTE_No_Permission tt)
                    (pte_set_ad (pte_set_ad w a0 d0) a' d')).
          { rewrite (pte_set_ad_absorb w a0 d0 a' d'). apply Hden. }
          apply (exec_translate_TLB_hit_denied_pt acc User mxr do_sum
                   vpn p2 p1 (pte_set_ad (pte_set_ad w a0 d0) a' d')
                   (mword_of_int 0) (tlb_hash (__id 39) vpn) σ Hdenc). }
        apply (exec_translateAddr_pt_front_err acc User vpn uroot
                 (PTW_No_Permission tt) e usatp va σ
                 Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
                 Htr Hte).
      + (* foreign entry: rejected by the tag, the walk runs and denies *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlbv Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a' d')
                         (mword_of_int 0) Hne)).
        apply (exec_translateAddr_pt_front_err acc User vpn uroot
                 (PTW_No_Permission tt) e usatp va σ
                 Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
                 (Hwalk Hlk) Hte).
    - (* empty slot: the walk runs and denies *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlbv Hslot).
      apply (exec_translateAddr_pt_front_err acc User vpn uroot
               (PTW_No_Permission tt) e usatp va σ
               Heff Hss Hcp Htm Hsatpv Hppn Hasid Hcanon eq_refl
               (Hwalk Hlk) Hte).
  Qed.

End UserPtFault.

(* ===================================================================== *)
(* §5b The COMBINED fault wrapper: the three fault flavors, as ONE        *)
(*     access-generic predicate and one dispatch lemma.  (For every       *)
(*     access user execution issues, translationException maps all three  *)
(*     PTW errors to the same page-fault exception -- the caller passes   *)
(*     the three concrete mappings, each a [cbn]-discharge.)              *)
(* ===================================================================== *)

(* the ways a user access at [va] can fault in translation *)
Definition u_fault_flavor (acc : MemoryAccessType mem_payload)
    (tfp : mword 44) (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true
  \/ (neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
      um !! svpn_of va = None /\
      svpn_of va <> tramp_vpn /\ svpn_of va <> tf_vpn)
  \/ (neq_vec (bits_of_virtaddr (Virtaddr va))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
      exists w, upt_leaf_at tfp um (svpn_of va) w /\
                uleaf_denied acc w).

Section UserPtFaultCombined.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma utlb_inv_pt_translateAddr_u_fault (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (e : ExceptionType) (σ : mstate) :
    u_fault_flavor acc tfp um va ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    exec (translationException acc (PTW_Invalid_Addr tt)) σ = Some (e, σ) ->
    exec (translationException acc (PTW_Invalid_PTE tt)) σ = Some (e, σ) ->
    exec (translationException acc (PTW_No_Permission tt)) σ = Some (e, σ) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ)⌝.
  Proof.
    intros Hflavor Hhtif Hcp HSXL Heff Hss Hall Hte1 Hte2 Hte3.
    iIntros "Hri Hgh Hinv".
    destruct Hflavor as
      [ Hnc | [ (Hcanon & Hnone & Hnt & Hntf) | (Hcanon & w & Hleaf & Hden) ] ].
    - iApply (utlb_inv_pt_translateAddr_u_noncanon acc uroot tfp um va e σ
                Hnc Hcp HSXL Heff Hss Hte1 with "Hri Hinv").
    - iApply (utlb_inv_pt_translateAddr_u_unmapped acc uroot tfp um va e σ
                Hnone Hnt Hntf Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte2
                with "Hri Hgh Hinv").
    - iApply (utlb_inv_pt_translateAddr_u_denied acc uroot tfp um w va e σ
                Hleaf Hden Hcanon Hhtif Hcp HSXL Heff Hss Hall Hte3
                with "Hri Hgh Hinv").
  Qed.

End UserPtFaultCombined.

