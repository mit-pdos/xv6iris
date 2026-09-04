(* KexecImageAlg.v -- the PURE algebra kexec's loader loops need to turn
   "what the code did, step by step" into "the ELF semantics' image is in
   memory, the size is [kexec_sz], and the stack page is zero outside the
   argument block".

   WHAT THE CODE DOES (kernel/exec.c, transcribed):

       sz = 0;
       for each PT_LOAD header p, in program-header order:
           sz = uvmalloc(sz, ep_vaddr p + ep_memsz p);   -- ZERO-fills growth
           loadseg(pagetable, ep_vaddr p, ip, ep_offset p, ep_filesz p);
       sz  = PGROUNDUP(sz);
       sz1 = uvmalloc(sz, sz + 2*PGSIZE);                -- guard + stack
       uvmclear(pagetable, sz1 - 2*PGSIZE);              -- no byte changes
       for each argument: copyout the string at [kxc_sp top alen (S i)]
       copyout the pointer vector at [kxc_sp_final top alen na]

   and the three moves it makes on the abstract byte map are
   [UserPtTree.umem_grow] (uvmalloc: only ADDS keys, zeroed),
   [UserPtTree.umem_write] (loadseg / copyout, integer-keyed inside one
   page) and [UserPtTree.umem_wr] (copyout's contract-level, va-keyed run).
   Every lemma below is an equation on [gmap Z (bv 8)] in exactly one of
   those three shapes, so a loop invariant can carry it verbatim.

   THE FOUR SECTIONS, and which S3 item each pays:

     1. IMAGE ALGEBRA (item 6's conclusion).  [uimg_sub (elf_image f) M]
        from one [uimg_sub] per PT_LOAD, one per half of a segment, and
        each half from a window of byte equations -- plus the PRESERVATION
        laws that carry an already-established [uimg_sub] through the
        later [umem_grow]s and the later [umem_write]s (which land outside
        the image's domain).

     2. THE loadseg LOOP (item 6's body).  [load_win] is the invariant
        "the window [va, va + i) already holds the file's bytes"; one page
        step ([umem_write] of [nn <= PGSIZE] bytes at [va + i]) extends it
        to [i + nn], and at [i = filesz] it IS [uimg_sub (seg_file_map f p)].

     3. THE SIZE CHAIN (item 5).  [kexec_sz_after] is the loop's [sz],
        [kx_uvmalloc]-shaped.  Two facts: it equals [elf_mem_end] (no
        [loads_ascending] needed -- [Z.max] does not care about order),
        and UNDER [loads_ascending] the max never picks the old value, so
        after phdr [i] the size is exactly [ep_vaddr p + ep_memsz p] --
        which is the [take i]-indexed loop invariant.

     4. THE STACK (item 9).  The stack page comes out of [umem_grow] all
        zeros; each copyout writes inside [kexec_arg_addr], so the zero
        conjunct of [kexec_stack_at] survives; and the same writes, read
        back, ARE [kexec_args_at].  The non-overlap of the writes is
        [kxc_sp]'s own monotonicity ([kxc_round16 x <= x]).

   iris-FREE in the sense of [ElfFile.v] / [ElfBridge.v]: no proofmode, no
   ghost state, vanilla [rewrite ... by ...] throughout.  It does Require
   [UserPtTree.v] (for [umem_write] / [umem_grow] / [pgroundup]) and
   [SpecKexec*.v] (for [kxc_sp] / [kexec_sz] / [kexec_args_at] and the
   rest of the names the contract is stated in), because there is no
   lighter home for those; that is also why the _CoqProject row sits with
   the kexec specs rather than beside [ElfBridge.v]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import PageGeom.        (* [PGSIZE]                                  *)
Require Import UserPtTree.      (* [umem_write], [umem_wr], [umem_grow],
                                   [pgroundup], [uva_live], [live_set]      *)
Require Import UmodeAbi.        (* [uimg_sub]                                *)
Require Import ElfFile.         (* the image semantics                       *)
Require Import SpecKexec.       (* [kxc_sp], [kxc_sp_final], [kxc_stack_ok]  *)
Require Import SpecKexecAU.     (* [loads_ascending], [kexec_top],
                                   [kexec_sz], [kexec_arg_addr],
                                   [kexec_args_at], [kexec_stack_at],
                                   [kexec_ustack]                            *)
Import Defs.

Local Open Scope Z_scope.

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

(* ...hence [kexec_top] and [kexec_sz] in terms of the loop's own state. *)
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

Lemma kexec_top_of_sz_after (f : elf_bytes) :
  elf_wf f = true -> kexec_top f = pgroundup (kexec_sz_after (elf_loads f)).
Proof.
  intros Hwf. unfold kexec_top. rewrite (kexec_sz_after_mem_end f Hwf).
  destruct (elf_mem_end f); reflexivity.
Qed.

Lemma kexec_sz_of_sz_after (f : elf_bytes) :
  elf_wf f = true ->
  kexec_sz f = pgroundup (kexec_sz_after (elf_loads f)) + 2 * PGSIZE.
Proof.
  intros Hwf. unfold kexec_sz. rewrite (kexec_top_of_sz_after f Hwf).
  reflexivity.
Qed.

Lemma kexec_top_nonneg (f : elf_bytes) : elf_wf f = true -> 0 <= kexec_top f.
Proof.
  intros Hwf. rewrite (kexec_top_of_sz_after f Hwf).
  apply pgroundup_nonneg, kexec_sz_after_nonneg.
Qed.

Lemma kexec_top_mod (f : elf_bytes) : kexec_top f `mod` PGSIZE = 0.
Proof.
  unfold kexec_top, PGSIZE.
  destruct (elf_mem_end f); [apply pgroundup_mod | reflexivity].
Qed.

Lemma kexec_sz_mod (f : elf_bytes) : kexec_sz f `mod` PGSIZE = 0.
Proof.
  pose proof (kexec_top_mod f) as H. unfold kexec_sz, PGSIZE in *.
  rewrite (Z.mod_add (kexec_top f) 2 4096 ltac:(lia)). exact H.
Qed.

Lemma kexec_sz_ge (f : elf_bytes) : elf_wf f = true -> 2 * PGSIZE <= kexec_sz f.
Proof.
  intros Hwf. pose proof (kexec_top_nonneg f Hwf). unfold kexec_sz. lia.
Qed.

(* ---- [loads_ascending]: prefixes, and the [take i]-indexed invariant ---- *)

Lemma loads_ascending_app_l (ps qs : list elf_phdr) :
  loads_ascending (ps ++ qs) -> loads_ascending ps.
Proof.
  induction ps as [| p ps IH]; simpl; intros H; [exact I |].
  destruct H as [Hstep Hrest]. split; [| exact (IH Hrest)].
  destruct ps as [| q ps]; [exact I |]. simpl in Hstep. exact Hstep.
Qed.

Lemma loads_ascending_take (ps : list elf_phdr) (i : nat) :
  loads_ascending ps -> loads_ascending (take i ps).
Proof.
  intros H. apply (loads_ascending_app_l (take i ps) (drop i ps)).
  rewrite take_drop. exact H.
Qed.

Lemma loads_ascending_adj (ps : list elf_phdr) (i : nat) (p q : elf_phdr) :
  loads_ascending ps -> ps !! i = Some p -> ps !! S i = Some q ->
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
Lemma kexec_sz_after_take_step (ps : list elf_phdr) (i : nat) (p : elf_phdr) :
  loads_ascending ps -> phdrs_nonneg ps -> ps !! i = Some p ->
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
    pose proof (loads_ascending_adj ps i q p Hasc Hq Hp) as Hadj.
    split; [lia |].
    rewrite (take_S_r ps (S i) p Hp), kexec_sz_after_snoc_le;
      [reflexivity | lia].
Qed.

(* ...and at the end of the walk the prefix is the whole list. *)
Lemma kexec_sz_after_take_all (ps : list elf_phdr) :
  kexec_sz_after (take (length ps) ps) = kexec_sz_after ps.
Proof. rewrite take_ge by lia. reflexivity. Qed.

(* ====================================================================== *)
(*  4.  THE STACK                                                         *)
(* ====================================================================== *)

(* ---- the push geometry: [kxc_sp] strictly decreases, by more than the
        string it just made room for ---- *)

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

(* every byte a copyout touches is inside [kexec_arg_addr] *)
Lemma kexec_arg_addr_str (top : Z) (alen : nat -> nat) (na i j : nat) :
  (i < na)%nat -> (j < alen i + 1)%nat ->
  kexec_arg_addr top alen na (kxc_sp top alen (S i) + Z.of_nat j).
Proof. intros Hi Hj. left. exists i. split; [exact Hi | lia]. Qed.

Lemma kexec_arg_addr_vec (top : Z) (alen : nat -> nat) (na j : nat) :
  (j < 8 * (na + 1))%nat ->
  kexec_arg_addr top alen na (kxc_sp_final top alen na + Z.of_nat j).
Proof. intros Hj. right. lia. Qed.

(* ---- the zero fill ---- *)

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

(* THE SURVIVING ZEROS: [kexec_stack_at]'s second conjunct, carried
   through the copyouts.  [P] is instantiated with [kexec_arg_addr]. *)
Definition kx_zero_except (top : Z) (P : Z -> Prop) (M : gmap Z (bv 8)) : Prop :=
  forall a, top - PGSIZE <= a < top -> ~ P a -> M !! a = Some (bv_0 8).

Lemma kx_zero_except_of_page (top : Z) (P : Z -> Prop) (M : gmap Z (bv 8)) :
  kx_page_zero top M -> kx_zero_except top P M.
Proof. intros H a Ha _. exact (H a Ha). Qed.

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

Lemma kexec_stack_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) :
  kxc_stack_ok top (top - PGSIZE) alen na ->
  kx_zero_except top (kexec_arg_addr top alen na) M ->
  kexec_stack_at top alen na M.
Proof. intros Hok Hz. split; [exact Hok | exact Hz]. Qed.

(* ---- the argument block, write by write ---- *)

(* the first two conjuncts of [kexec_args_at], after [k] strings *)
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

(* THE LAST PUSH: the [8 * (na + 1)]-byte pointer vector, at
   [kxc_sp_final], strictly below every string ([kxc_sp_vec_disj]).  Its
   [i]-th word is [kexec_ustack top alen na i], little-endian, which is
   exactly what [kexec_args_at]'s third conjunct asks for. *)
Lemma kexec_args_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) (src : nat -> bv 8) :
  kx_str_at top alen afun na M ->
  (forall i k, (i <= na)%nat -> (k < 8)%nat ->
     bv_to_little_endian 8 8 (kexec_ustack top alen na i) !! k
     = Some (src (8 * i + k)%nat)) ->
  kexec_args_at top alen na afun
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
