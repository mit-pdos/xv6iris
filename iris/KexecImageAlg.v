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
Require Import ElfEnc.          (* [ph_at], [eh_phnum] -- the CODE-side readers *)
Require Import ElfFile.         (* the image semantics                       *)
Require Import ElfBridge.       (* [elf_parse_phdr_all], [ph_at_of_ehdr] --
                                   §4's identification of the code's walk  *)
Require Import SpecKexec.       (* [kxc_sp], [kxc_sp_final], [kxc_stack_ok]  *)
Require Export KexecBuilt.      (* the argument block's algebra, spelled
                                   below [SpecKexecAU] so the kexec block
                                   proofs can name it; §5 bridges it       *)
Require Import SpecKexecAU.     (* [loads_ascending], [kexec_top],
                                   [kexec_sz], [kexec_arg_addr],
                                   [kexec_args_at], [kexec_stack_at],
                                   [kexec_ustack]                            *)
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  IMAGE ALGEBRA, THE loadseg WINDOW AND THE SIZE FOLD                *)
(*      -- MOVED WHOLE TO [KexecBuilt.v] (S3b)                             *)
(* ====================================================================== *)

(*  [elf_zero_byte_bv0], [uimg_sub_*], [load_win] and its four step rows,
    and [kx_uvmalloc] / [kexec_sz_after] with the [Z.max] folds all live in
    [KexecBuilt.v] now, and are re-exported by the [Require Export] above.
    The reason is the one §4 already records: the phdr loop's and loadseg's
    INVARIANTS are stated in exactly that vocabulary, and
    [ProofKexecSeam.v] / [ProofKexecB2.v] / [ProofKexecB3.v] sit below
    [SpecKexecAU.v] -- which this file requires and they must not.  What is
    left here is what genuinely names [SpecKexecAU]: [kexec_top] /
    [kexec_sz], [loads_ascending], and §5's bridges.                       *)

(* ...hence [kexec_top] and [kexec_sz] in terms of the loop's own state. *)
(* [pgroundup_nonneg] / [pgroundup_mod] / [pgroundup_aligned] are
   [KexecBuilt]'s. *)

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

(* ---- [loads_ascending] IS [KexecBuilt.kxb_ascending] ---- *)

(*  The kernel-side phdr loop cannot name [loads_ascending] (this file is
    above [SpecKexecAU]); [KexecBuilt.kxb_ascending] is the same fixpoint
    spelled below it, and this is the identification, plus the four rows
    the contract's own spelling wants.  Each is one [rewrite]. *)

Lemma loads_ascending_kxb (ps : list elf_phdr) :
  loads_ascending ps <-> kxb_ascending ps.
Proof.
  induction ps as [| p ps IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma loads_ascending_app_l (ps qs : list elf_phdr) :
  loads_ascending (ps ++ qs) -> loads_ascending ps.
Proof.
  rewrite !loads_ascending_kxb. apply kxb_ascending_app_l.
Qed.

Lemma loads_ascending_take (ps : list elf_phdr) (i : nat) :
  loads_ascending ps -> loads_ascending (take i ps).
Proof. rewrite !loads_ascending_kxb. apply kxb_ascending_take. Qed.

Lemma loads_ascending_adj (ps : list elf_phdr) (i : nat) (p q : elf_phdr) :
  loads_ascending ps -> ps !! i = Some p -> ps !! S i = Some q ->
  ep_vaddr p + ep_memsz p <= ep_vaddr q.
Proof. rewrite loads_ascending_kxb. apply kxb_ascending_adj. Qed.

Lemma kexec_sz_after_take_step (ps : list elf_phdr) (i : nat) (p : elf_phdr) :
  loads_ascending ps -> phdrs_nonneg ps -> ps !! i = Some p ->
  kexec_sz_after (take i ps) <= ep_vaddr p
  /\ kexec_sz_after (take (S i) ps) = ep_vaddr p + ep_memsz p.
Proof. rewrite loads_ascending_kxb. apply kxb_sz_after_take_step. Qed.

Lemma kexec_sz_after_take_all (ps : list elf_phdr) :
  kexec_sz_after (take (length ps) ps) = kexec_sz_after ps.
Proof. rewrite take_ge by lia. reflexivity. Qed.

(* ====================================================================== *)
(*  4.  THE PHDR WALK'S GUARD, FROM [kexec_loadable]                      *)
(* ====================================================================== *)

(*  [KexecBuilt.kxb_walk_ok] is what the phdr loop's step lemmas take as a
    premise; this is the ONE row S4 needs to discharge it, and it is
    discharged from [kexec_loadable f] plus the fact phase A already
    carries -- that the 64-byte [struct elfhdr] in kexec's frame IS the
    file's first 64 bytes.  Everything else the loop needs is derived. *)

Lemma kxb_phdr_at_parse (l : elf_bytes) (o : Z) (p : elf_phdr) :
  elf_parse_phdr l o = Some p -> kxb_phdr_at l (Z.to_nat o) = p.
Proof.
  intros H. unfold kxb_phdr_at. symmetry. exact (elf_parse_phdr_all l o p H).
Qed.

Lemma kxb_loads_of_list (f : elf_bytes) (ef : nat -> bv 8)
    (ps : list elf_phdr) (n : nat) :
  (n <= length ps)%nat ->
  (forall i p, (i < n)%nat -> ps !! i = Some p -> kxb_phdr f ef i = p) ->
  kxb_loads f ef n = List.filter (fun p => Z.eqb (ep_type p) 1) (take n ps).
Proof.
  induction n as [| n IH]; intros Hn Hag; [reflexivity |].
  assert (Hlt : (n < length ps)%nat) by lia.
  destruct (lookup_lt_is_Some_2 ps n Hlt) as [p Hp].
  rewrite (take_S_r ps n p Hp), List.filter_app.
  rewrite <- (IH ltac:(lia)
                 ltac:(intros i q Hi Hq; apply Hag; [lia | exact Hq])).
  assert (Hpe : kxb_phdr f ef n = p) by (apply Hag; [lia | exact Hp]).
  destruct (decide (ep_type p = 1)) as [Ht | Ht].
  - rewrite (kxb_loads_S_load f ef n ltac:(rewrite Hpe; exact Ht)), Hpe.
    f_equal. simpl. rewrite (proj2 (Z.eqb_eq _ _) Ht). reflexivity.
  - rewrite (kxb_loads_S_skip f ef n ltac:(rewrite Hpe; exact Ht)).
    simpl. replace (Z.eqb (ep_type p) 1) with false
      by (symmetry; apply Z.eqb_neq; exact Ht).
    rewrite List.app_nil_r. reflexivity.
Qed.

Lemma kxb_walk_ok_of_loadable (f : elf_bytes) (ef : nat -> bv 8) :
  kexec_loadable f ->
  (forall j, (j < 64)%nat -> ef j = f !!! j) ->
  kxb_walk_ok f ef.
Proof.
  intros (Hwf & (e & He & Hpo) & _ & Hasc) Hag.
  destruct (elf_wf_phdrs f Hwf) as [ps Hps].
  destruct (eh_fields_of_ehdr ef f e He Hag) as (_ & Hphnum & _).
  pose proof (elf_phdrs_length f e ps He Hps) as Hlen.
  (* the two range facts that kill the 32-bit truncation *)
  assert (Hpo0 : 0 <= ee_phoff e).
  { destruct (elf_parse_ehdr_fields f e He) as (_ & _ & H2 & _).
    rewrite H2. apply elf_le_at_bound. }
  assert (Hpn : 0 <= ee_phnum e < 65536).
  { destruct (elf_parse_ehdr_fields f e He) as (_ & _ & _ & _ & H5).
    rewrite H5. pose proof (elf_le_at_bound f 56 2) as Hb.
    change (2 ^ (8 * Z.of_nat 2)) with 65536 in Hb. exact Hb. }
  assert (Hag' : forall i p, (i < length ps)%nat -> ps !! i = Some p ->
                   kxb_phdr f ef i = p).
  { intros i p Hi Hp.
    assert (Hio : ph_at ef i = ee_phoff e + 56 * Z.of_nat i)
      by exact (ph_at_of_ehdr ef f e i He Hag Hpo).
    assert (Hib : 0 <= ee_phoff e + 56 * Z.of_nat i < 2 ^ 32).
    { change (2 ^ 31) with 2147483648 in Hpo. rewrite Hlen in Hi.
      assert (Hiz : Z.of_nat i < 65536) by lia.
      change (2 ^ 32) with 4294967296. lia. }
    unfold kxb_phdr, kxb_phoff. rewrite Hio, (Z.mod_small _ _ Hib).
    exact (kxb_phdr_at_parse f _ p (elf_phdrs_parse f e ps i p Hwf He Hps Hp)). }
  split; [| split].
  - rewrite <- Hphnum in Hlen. rewrite <- Hlen.
    rewrite (kxb_loads_of_list f ef ps (length ps) ltac:(lia) Hag').
    rewrite take_ge by lia. unfold elf_loads. rewrite Hps. reflexivity.
  - apply Forall_forall. intros p Hp.
    apply elf_wf_phdr_ok; [exact Hwf | apply elem_of_list_In; exact Hp].
  - apply loads_ascending_kxb. exact Hasc.
Qed.

(* ====================================================================== *)
(*  4.  THE STACK -- MOVED WHOLE TO [KexecBuilt.v]                        *)
(* ====================================================================== *)

(*  The push geometry ([kxc_sp_gap] / [kxc_sp_mono] / [kxc_sp_str_disj] /
    [kxc_sp_vec_disj]), the zero fill ([kx_page_zero], [kx_zero_except])
    and the argument block written push by push ([kx_str_at],
    [kxb_args_at_intro]) all live in [KexecBuilt.v] now, and are
    re-exported by the [Require Export] above.  The reason is the
    dependency order: the argv loop's INVARIANT is stated in exactly that
    vocabulary, and [ProofKexecSeam.v] / [ProofKexecC.v] sit below
    [SpecKexecAU.v] -- which this file requires and they must not.  So the
    predicates are spelled in [KexecBuilt] and §5 below is the bridge.
    The two [umem_grow] lookup laws and the three [pgroundup] rows moved
    with them, for the same reason ([kx_page_zero_grow] needs them).      *)

(* ====================================================================== *)
(*  5.  THE BRIDGE: [KexecBuilt]'s spelling IS the contract's             *)
(* ====================================================================== *)

(*  [kxb_ustack] / [kxb_arg_addr] / [kxb_args_at] / [kxb_stack_at] are
    [SpecKexecAU]'s four predicates transcribed character for character
    into a file that does not require [SpecKexecAU], so each of these is
    the identity -- and stating them is what lets a client of the exec
    contract consume [KexecBuilt.kexec_built] without ever unfolding it. *)

Lemma kxb_ustack_eq (top : Z) (alen : nat -> nat) (na i : nat) :
  kxb_ustack top alen na i = kexec_ustack top alen na i.
Proof. reflexivity. Qed.

Lemma kxb_arg_addr_eq (top : Z) (alen : nat -> nat) (na : nat) (a : Z) :
  kxb_arg_addr top alen na a <-> kexec_arg_addr top alen na a.
Proof. reflexivity. Qed.

Lemma kxb_args_at_kexec (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) :
  kxb_args_at top alen na afun M -> kexec_args_at top alen na afun M.
Proof. exact (fun H => H). Qed.

Lemma kxb_stack_at_kexec (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) :
  kxb_stack_at top alen na M -> kexec_stack_at top alen na M.
Proof. exact (fun H => H). Qed.

(* ...and the two intro rows, at the contract's own spelling. *)
Lemma kexec_stack_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) :
  kxc_stack_ok top (top - PGSIZE) alen na ->
  kx_zero_except top (kexec_arg_addr top alen na) M ->
  kexec_stack_at top alen na M.
Proof. intros Hok Hz. split; [exact Hok | exact Hz]. Qed.

Lemma kexec_args_at_intro (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) (src : nat -> bv 8) :
  kx_str_at top alen afun na M ->
  (forall i k, (i <= na)%nat -> (k < 8)%nat ->
     bv_to_little_endian 8 8 (kexec_ustack top alen na i) !! k
     = Some (src (8 * i + k)%nat)) ->
  kexec_args_at top alen na afun
    (umem_write M (kxc_sp_final top alen na) (8 * (na + 1)) src).
Proof. exact (kxb_args_at_intro top alen na afun M src). Qed.
