(* WpUmodeLoad.v -- THE MEMORY-READING LEAF of the verified user-execution
   tier (claude-notes/projects/user-verified.md, user-echo.md): the generic
   [wp_uv_load], instantiated at [ld] / [c.ldsp] (k = 8, signed) and [lbu]
   (k = 1, unsigned).

   The exact mirror of WpUmodeStore.v, and for the same reason: a memory
   instruction cannot ride the retire funnel [wp_uv_retire], whose
   post-execute state is the PURE register tower [uv_post] computed FROM the
   pre state.  A load's own [translateAddr] may fill the TLB (or write back
   A/D), so its post state is not a function of its pre state at all -- the
   caller has to establish it and hand it over.  So this file adds,
   ALONGSIDE the funnel (nothing in WpUmodeStep.v or WpUmodeStore.v is
   restructured):

   §1 [uM_word M a k] -- the image-level READ: the little-endian word spelled
      by the [k] image bytes at [a], spelled as the same
      [assemble_bytes]-of-a-byte-list the model's [read_ram] result is
      reconstructed from (UserBits' [bytes_list_of_lookups] +
      RiscvModelBytes' [nth_byte_assemble_len]), exactly as [uM_store8]
      mirrors [write_bytes].  [uM_word_bytes] links it to [uM_bytes].
      Also [uM_byte_val] -- the k = 1 reading a call site actually wants --
      and [uload_width], the per-width side conditions bundled as one
      premise ([uload_width_8] / [uload_width_1] discharge it).
      RELOCATION DEBT: these read naturally beside [uM_bytes] in UmodeMem.v;
      they live here to avoid rebuilding the files above it.

   §2 [umem_load_k] -- the Iris composer, width-generic in a section [k]:
      translate the target at User through
      [utlb_inv_pt_translateAddr_u (Load Data)], read [k] physical bytes
      against [gen_heap_interp], hand back [umem pt M] UNCHANGED together
      with the CONCRETE loaded value.  The concrete-byte twin of
      UserMemPt's [user_pt_load_data_g] (whose loaded value is existential,
      because it owns its pages with existential contents), built the same
      way [umem_store_8] is the concrete twin of [user_pt_store_data_g].

   §3 [exec_execute_LOAD_k_u_walk] -- the value-precise execute at User
      privilege with MPRV = 0, the load twin of
      [exec_execute_STORE_8_u_walk].  No autocast trap on this side: the
      model applies [extend_value] to the read value directly, and the
      accumulator cast is already collapsed inside
      [exec_vmem_read_addr_aligned_load].

   §4 [uv_load_post_fetch] -- the geometry-agnostic middle.  The load twin
      of WpUmodeStore's [uv_store_post_fetch]: that lemma names STORE, the
      [csp_rs1] base and [uM_store8] in its own statement, so it is
      genuinely store-specific and cannot be reused.  What IS reused is
      WpUmodeStore's §4 [uv_retire_post_state] -- the post-execute state
      taken abstractly -- which is exactly the shape both memory leaves
      need.

   §5 [wp_uv_load] -- ONE width- and signedness-generic leaf over all four
      fetch geometries, plus the three [echo] instances [wp_uv_ld] /
      [wp_uv_cldsp] / [wp_uv_lbu]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv WireInv WpGpr RegFile InstrBytes.
Require Import SmodeCore.
Require Import CommonWalk UserBits.
Require Import MemAccessGen WpMmodeLeafBase WpLoad.
Require Import WpDecodeBridge DecodeTotalU.
Require Import UptTree UserPtTree UserExec UserStep.
Require Import UserMemPt UserMemArms UserMemClassify.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep WpUmodeStore.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ---------------------------------------------------------------------
   THE STEP MASK, in ONE place.

   [uv_load_post_fetch] below is the only lemma in the verified-user leaf
   layer that has to SPELL the engine's inner mask (every funnel leaf
   inherits it from [wp_uv_retire]).  That mask is not stable across the
   tree: commit 723de5cb ("user tier: mip is not ownable") grew it by
   [clockN], because the step engines now borrow [mip] from [clock_inv]
   across their own sigma-callback.

   It is spelled here as a NOTATION so that the whole file tracks the
   engine with a ONE-LINE edit.  It must agree with [WpUmodeStep.
   uv_step_obl]'s and [WpUmodeStore.uv_retire_post_state]'s mask:

     pre-723de5cb :  (⊤ ∖ ↑minstretN ∖ ↑wireN)
     post         :  (⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN)

   The same commit is why [wp_uv_load] destructures [user_cfg] into EIGHT
   conjuncts: 723de5cb dropped [uc_mip].  Those are the only two places in
   this file that name the engine's internals; everything else goes through
   [uv_retire_post_state].
   --------------------------------------------------------------------- *)
Local Notation uv_step_E := (⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN).

(* ===================================================================== *)
(* §1 The image-level read.                                               *)
(* ===================================================================== *)

(* the [n] image bytes at [a], as a list (off the image the entry is
   irrelevant -- every use is under a "present in M" premise) *)
Definition uM_bytelist (M : gmap Z (bv 8)) (a : Z) (n : nat) : list (bv 8) :=
  (fun j : nat => default (bv_0 8) (M !! (a + Z.of_nat j))) <$> seq 0 n.

Lemma uM_bytelist_length (M : gmap Z (bv 8)) (a : Z) (n : nat) :
  length (uM_bytelist M a n) = n.
Proof. unfold uM_bytelist. rewrite length_fmap. apply length_seq. Qed.

Lemma uM_bytelist_lookup (M : gmap Z (bv 8)) (a : Z) (n j : nat) :
  (j < n)%nat ->
  uM_bytelist M a n !!! j = default (bv_0 8) (M !! (a + Z.of_nat j)).
Proof.
  intro Hj. unfold uM_bytelist.
  rewrite list_lookup_total_alt. rewrite list_lookup_fmap.
  rewrite (lookup_seq_lt 0 n j Hj). reflexivity.
Qed.

(* THE little-endian word the [k] image bytes at [a] spell out -- the same
   [assemble_bytes] the fetch layer reconstructs a fetched word with. *)
Definition uM_word (M : gmap Z (bv 8)) (a k : Z) : mword (8 * k) :=
  Z_to_bv _ (assemble_bytes (uM_bytelist M a (Z.to_nat k))).

(* ... in the [uM_bytes] shape the fetch/ABI layer speaks *)
Lemma uM_word_bytes (M : gmap Z (bv 8)) (a k : Z) :
  0 <= k ->
  (forall j : nat, (j < Z.to_nat k)%nat ->
     exists b : bv 8, M !! (a + Z.of_nat j) = Some b) ->
  uM_bytes M a (Z.to_nat k) (uM_word M a k).
Proof.
  intros Hk Hex j Hj.
  destruct (Hex j Hj) as (b & Hb). rewrite Hb. f_equal. symmetry.
  transitivity (uM_bytelist M a (Z.to_nat k) !!! j).
  - unfold uM_word. apply nth_byte_assemble_len;
      [ | rewrite uM_bytelist_length; exact Hj ].
    rewrite uM_bytelist_length.
    assert (HZN : Z.of_N (MachineWord.MachineWord.Z_idx (8 * k)) = 8 * k)
      by (unfold MachineWord.MachineWord.Z_idx; apply Z2N.id; lia).
    rewrite HZN. lia.
  - rewrite (uM_bytelist_lookup M a (Z.to_nat k) j Hj). rewrite Hb. reflexivity.
Qed.

(* ---- the STORE-THEN-LOAD round trip ---------------------------------
   A function's epilogue reloads what its prologue spilled, so a verified
   program needs "an 8-byte slot reads back what was stored into it".  It
   is [uM_store8_bytes] (WpUmodeStore.v §1) and [uM_word_bytes] above,
   joined by the fact that eight bytes DETERMINE a 64-bit word
   (RiscvModelBytes' [bv_eq_of_bytes], which is exactly that).
   RELOCATION DEBT: both read naturally beside [uM_bytes] in UmodeMem.v,
   together with [uM_word] itself. *)

(* two byte-window facts for the same window determine the same word *)
Lemma uM_bytes_inj (M : gmap Z (bv 8)) (a : Z) (w1 w2 : mword 64) :
  uM_bytes M a 8 w1 -> uM_bytes M a 8 w2 -> w1 = w2.
Proof.
  intros H1 H2. apply (bv_eq_of_bytes (n := 8)).
  intros j Hj.
  assert (Hj' : (j < 8)%nat) by lia.
  (* stated at the [mword 64] index and closed at [bv (8*8)] by
     conversion -- [congruence] is syntactic and the two indices are not *)
  assert (Hb : nth_byte w1 j = nth_byte w2 j).
  { pose proof (H1 j Hj') as E1. pose proof (H2 j Hj') as E2.
    rewrite E1 in E2. congruence. }
  exact Hb.
Qed.

(* THE round trip: an 8-byte slot reads back what was stored into it *)
Lemma uM_word_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_word (uM_store8 M a v) a 8 = v.
Proof.
  apply (uM_bytes_inj (uM_store8 M a v) a).
  - apply (uM_word_bytes (uM_store8 M a v) a 8 ltac:(lia)).
    intros j Hj. exists (nth_byte v j).
    exact (uM_store8_bytes M a v j ltac:(lia)).
  - exact (uM_store8_bytes M a v).
Qed.

(* the k = 1 reading: ONE image byte *)
Lemma uM_word_byte (M : gmap Z (bv 8)) (a : Z) (b : mword 8) :
  M !! a = Some b -> uM_word M a 1 = b.
Proof.
  intro Hb.
  unfold uM_word, uM_bytelist.
  change (Z.to_nat 1) with 1%nat.
  cbn [seq fmap list_fmap assemble_bytes].
  replace (a + Z.of_nat 0) with a by lia.
  rewrite Hb. cbn [default from_option id].
  rewrite Z.mul_0_r Z.add_0_r.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* the value an unsigned 1-byte load writes: a clean spelling for the call
   sites of [wp_uv_lbu] *)
Definition uM_byte_val (M : gmap Z (bv 8)) (a : Z) : mword 64 :=
  zero_extend' 64 (default (bv_0 8) (M !! a) : mword 8).

Lemma uM_byte_val_of (M : gmap Z (bv 8)) (a : Z) (b : mword 8) :
  M !! a = Some b -> uM_byte_val M a = zero_extend' 64 b.
Proof. intro H. unfold uM_byte_val. rewrite H. reflexivity. Qed.

Lemma uM_word_byte_val (M : gmap Z (bv 8)) (a : Z) (b : mword 8) :
  M !! a = Some b -> extend_value true (uM_word M a 1) = zero_extend' 64 b.
Proof.
  intro H. unfold extend_value. cbn match.
  rewrite (uM_word_byte M a b H). reflexivity.
Qed.

(* at k = 8 the sign/zero extension is the identity, so a call site may
   name the loaded doubleword directly *)
Lemma extend_value_w8 (u : bool) (w : mword (8 * 8)) : extend_value u w = w.
Proof.
  unfold extend_value. destruct u; cbn match;
    [ apply zero_extend'_id | apply sign_extend'_id ].
Qed.

(* ---- the per-width side conditions, as ONE premise ------------------- *)

Lemma vmem_width_le8 (k : Z) : vmem_width k -> k <= 8.
Proof. intros [-> | [-> | [-> | ->]]]; lia. Qed.

Lemma vmem_width_dvd (k : Z) : vmem_width k -> (k | 4096).
Proof.
  intros [-> | [-> | [-> | ->]]];
    [ exists 4096 | exists 2048 | exists 1024 | exists 512 ]; reflexivity.
Qed.

Lemma vmem_width_uint (k : Z) : vmem_width k -> uint (to_bits 64 k) = k.
Proof. intros [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.

(* everything a load leaf needs to know about its access width: the ISA
   width itself, plus the ONE width-TYPED byte-level brick the model's
   [read_ram] reduction bottoms out in (the same split UserMemPt's
   width-generic section makes). *)
Definition uload_width (k : Z) : Prop :=
  vmem_width k /\
  (forall (addr : mword 64) (w : mword (8 * k)) (s : mstate),
     dev_addr addr = false ->
     (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
        s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
     exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s
       = Some ((w, default_meta), s)).

Lemma uload_width_8 : uload_width 8.
Proof.
  split; [ right; right; right; reflexivity | exact exec_read_ram_plain_8 ].
Qed.

Lemma uload_width_1 : uload_width 1.
Proof. split; [ left; reflexivity | exact exec_read_ram_plain_1 ]. Qed.

(* the in-page bound at the ACCESS width (UmodeFetch's [uinpage_nc] is the
   4-byte fetch-window version, WpUmodeStore's [uinpage_nc8] the width-8
   one) *)
Lemma uinpage_nck (va : mword 64) (k : Z) (j : nat) :
  Z.rem (uint va) 4096 <= 4096 - k -> Z.of_nat j < k ->
  bv_unsigned va mod 4096 + Z.of_nat j < 4096.
Proof.
  intros Hpg Hj.
  rewrite uint_unsigned in Hpg.
  rewrite Z.rem_mod_nonneg in Hpg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  lia.
Qed.

(* a 1-byte access never crosses a page: its in-page premise is discharged
   from the address alone. *)
Lemma uinpage_1 (va : mword 64) : Z.rem (uint va) 4096 <= 4096 - 1.
Proof.
  rewrite uint_unsigned.
  rewrite Z.rem_mod_nonneg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)). lia.
Qed.

(* ===================================================================== *)
(* §2 The Iris composer: translate at User, read k owned bytes.            *)
(* ===================================================================== *)

Section UmodeLoadMem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) (s : mstate),
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s
        = Some ((w, default_meta), s)).

  (* the whole access window out of [umem], at the physical addresses the
     read hits: the concrete-byte twin of [udata_read_word_g] (whose word
     is existential). *)
  Lemma umem_read_window (pt : uptd) (M : gmap Z (bv 8))
      (w_ld va : mword 64) (sig : mstate) :
    ud_um pt !! svpn_of va = Some w_ld ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists b : bv 8, M !! (uint va + Z.of_nat j) = Some b) ->
    gen_heap_interp sig.(mem) -∗ umem pt M -∗
    ⌜forall j : nat, (j < Z.to_nat k)%nat ->
       sig.(mem) !! pa_add (u_walk_pa w_ld va) j
         = Some (nth_byte (uM_word M (uint va) k) j)
       /\ addr_is_ram (pa_add (u_walk_pa w_ld va) j)⌝.
  Proof.
    iIntros (Hl Hpg HMb) "Hmem HM".
    rewrite bi.pure_forall. iIntros (j).
    destruct (decide (j < Z.to_nat k)%nat) as [Hj | Hj];
      [ | iPureIntro; intro Hc; exfalso; exact (Hj Hc) ].
    iDestruct (umem_fetch_byte pt M w_ld va j
                 (nth_byte (uM_word M (uint va) k) j) sig Hl
                 (uinpage_nck va k j Hpg ltac:(lia))
                 (uM_word_bytes M (uint va) k ltac:(lia) HMb j Hj)
                 with "Hmem HM") as %Hb.
    iPureIntro. intro. exact Hb.
  Qed.

  (* the k-byte load at a user-mapped, load-permitted, k-aligned,
     in-one-page virtual address.  Everything after the translate is the
     width-k instance of UserMemPt's bricks; the value comes out
     DETERMINED by the image. *)
  Lemma umem_load_k (pt : uptd) (M : gmap Z (bv 8)) (w_ld va : mword 64)
      (sigma : mstate) :
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists b : bv 8, M !! (uint va + Z.of_nat j) = Some b) ->
    register_lookup misa sigma.(sregs) = MISA_C ->
    register_lookup menvcfg sigma.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sigma.(sregs) = None ->
    register_lookup cur_privilege sigma.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus sigma.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus sigma.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions sigma.(sregs)) ->
    reg_interp sigma.(sregs) -∗ gen_heap_interp sigma.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ sig2 : mstate,
      ⌜exec (translateAddr (Virtaddr va) (Load Data)) sigma
        = Some (Ok (Physaddr (u_walk_pa w_ld va), PBMT_PMA, init_ext_ptw), sig2)⌝ ∗
      ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w_ld va)) k
               false false false) sig2
        = Some (Ok (uM_word M (uint va) k), sig2)⌝ ∗
      ⌜sig2.(mdev) = sigma.(mdev)⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r sig2.(sregs) = register_lookup r sigma.(sregs)⌝ ∗
      reg_interp sig2.(sregs) ∗ gen_heap_interp sig2.(mem) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    intros Hl Hchk Hcanon Hpg Hal HMb Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) sigma
                 with "Hri Hinv") as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (Load Data)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_ld va (u_walk_pa w_ld va) sigma
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (Load Data)
               (register_lookup mstatus sigma.(sregs)) User sigma Hmprv)
            (exec_is_shadow_stack_u_acc (Load Data) sigma
               (or_intror (or_introl eq_refl))) Hall
            with "Hri Hgh Hinv")
      as (sig2) "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r sig2.(sregs) = register_lookup r sigma.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (umem_read_window pt M w_ld va sig2 Hl Hpg HMb with "Hgh HM")
      as %Hwin.
    set (pa := u_walk_pa w_ld va) in *.
    set (dv := uM_word M (uint va) k) in *.
    assert (Hbytes : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
              sig2.(mem) !! pa_add pa j = Some (nth_byte dv j)).
    { intros j Hj. exact (proj1 (Hwin j ltac:(lia))). }
    assert (Hram0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). exact (proj2 (Hwin 0%nat ltac:(lia))). }
    assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1))).
    { exact (proj2 (Hwin (Z.to_nat k - 1)%nat ltac:(lia))). }
    iModIntro. iExists sig2.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { destruct (pma_all_ram
                  (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity));
                         exact Hall)
                   : pma_allows_all (register_lookup pma_regions sig2.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
        as (region & Hpmam & _ & Hrd & _).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sig2.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 k)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8 Huintk
                 ltac:(clear -Hk; lia) Hram0 Hramk Hcovp). }
      exact (exec_mem_read_data_U k Hk Hread_plain PBMT_PMA pa region dv sig2
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               Hpmam
               (pa_aligned_div _ va k Hk Hkdvd Hal) Hrd
               (within_clint_false pa k sig2 Hnc Hk)
               (within_sig_false pa k sig2 Hns Hk)
               (within_htif_false pa k sig2
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity));
                         exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Tr | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeLoadMem.

(* ===================================================================== *)
(* §3 The value-precise k-byte LOAD execute at User.                       *)
(* ===================================================================== *)

Section UmodeLoadExec.
  Context (k : Z).
  Context (Hkw : vmem_width k).

  (* THE execute fact: [l{b,h,w,d}[u] rd, imm(rs1)] at User with MPRV = 0.
     The U-mode analog of WpSmodeMemGen's [exec_execute_LOAD_w_gpr_S_walk_pt],
     and the load twin of WpUmodeStore's [exec_execute_STORE_8_u_walk]. *)
  Lemma exec_execute_LOAD_k_u_walk (rs1 rd : mword 5) (imm : mword 12)
      (is_unsigned : bool) (base pa : mword 64) (dv : mword (8 * k))
      (md : SATPMode) (s s2 : mstate) :
    uint rd <> 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    exec (get_pmlen (Load Data) User) s = Some (0, s) ->
    exec (translationMode User) s = Some (md, s) ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    is_aligned_vaddr (Virtaddr (add_vec base (sign_extend' 64 imm))) k = true ->
    exec (translateAddr (Virtaddr (add_vec base (sign_extend' 64 imm))) (Load Data)) s
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s2) ->
    exec (mem_read (Load Data) PBMT_PMA (Physaddr pa) k false false false) s2
      = Some (Ok dv, s2) ->
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s
      = Some (RETIRE_SUCCESS,
              set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value is_unsigned dv))).
  Proof.
    intros Hrd Hcp Heff Hpml Htm Hbase Hal Htr Hmr.
    apply (exec_execute_LOAD_u_ok imm rs1 rd is_unsigned k dv s s2
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (vmem_width_le8 k Hkw)) Hrd).
    apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data)
             false false false md (Ok dv) s s2 Hcp Heff Hpml Htm).
    rewrite Hbase.
    exact (exec_vmem_read_addr_aligned_load k
             (add_vec base (sign_extend' 64 imm)) pa dv User md s s2
             Hkw Hal (ltac:(rewrite Hcp; exact Heff)) Htm
             (exec_translate_and_read_value_g k
                (add_vec base (sign_extend' 64 imm)) pa PBMT_PMA dv s s2 s2 Htr Hmr)).
  Qed.

End UmodeLoadExec.

(* ===================================================================== *)
(* §4/§5 The middle and the leaves.                                       *)
(* ===================================================================== *)

Section WpUmodeLoad.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The geometry-agnostic middle: from the FETCHED state, drive the       *)
  (* nextPC write, the load's translate + read, the execute's rd write and *)
  (* the step assembly.  [Hprog] is the [uv_prog_rvc] / [uv_prog_base]     *)
  (* witness the caller's geometry produced -- the same seam               *)
  (* [uv_retire_post_fetch] and [uv_store_post_fetch] use.  The image [M]  *)
  (* comes back UNCHANGED.                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma uv_load_post_fetch (CIDp : CpuId) (P : iProp Σ)
      (sg sf : mstate) (b : bool) (mst pc : mword 64) (d : Z) (ib : mword 32)
      (m : regfile) (M : gmap Z (bv 8))
      (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (w_ld va wval : mword 64) :
    uload_width k ->
    exec (should_inc_minstret (register_lookup cur_privilege sg.(sregs))) sg
      = Some (b, sg) ->
    register_lookup hart_state
      (set_reg sg (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt ->
    register_lookup PC sf.(sregs) = pc ->
    agree_on D_u sf dstateU ->
    register_lookup htif_tohost_base sf.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus sf.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus sf.(sregs))) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus sf.(sregs))) ('b"0") = true ->
    pma_allows_all (register_lookup pma_regions sf.(sregs)) ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    (forall s_x : mstate,
       exec (execute (uv_exp i o)) (set_reg sf nextPC (add_vec_int pc d))
         = Some (RETIRE_SUCCESS, s_x) ->
       exec (run_hart_active 0) (set_reg sg (R_bool minstret_increment) b)
         = Some (Step_Execute (RETIRE_SUCCESS, ib), s_x)) ->
    mstate_interp sf -∗
    P -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    PC ↦ᵣ pc -∗ nextPC ↦ᵣ pc -∗ gpr_file m -∗
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ b -∗
    ▷ (P -∗
       utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
       umem pt M -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       PC ↦ᵣ add_vec_int pc d -∗ nextPC ↦ᵣ add_vec_int pc d -∗
       gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
       WP (Loop : expr riscv_lang)) -∗
    |={uv_step_E}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) sg = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hkw Hsi Hhart_a Lpcf Hagreef Hhtiff HSXLf Hmprvf Hmxrf Hpmaf
           Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hprog.
    destruct Hkw as (Hvw & Hread_plain).
    pose proof (vmem_width_pos k Hvw) as Hk.
    pose proof (vmem_width_le8 k Hvw) as Hk8.
    pose proof (vmem_width_dvd k Hvw) as Hkdvd.
    pose proof (vmem_width_uint k Hvw) as Huintk.
    iIntros "Hint HP Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hcont".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iMod (reg_update _ nextPC _ (add_vec_int pc d) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    set (s_pc := set_reg sf nextPC (add_vec_int pc d)).
    iAssert (reg_interp s_pc.(sregs)) with "[Hreg]" as "Hreg".
    { unfold s_pc; rewrite ?sregs_set_reg. iExact "Hreg". }
    iAssert (gen_heap_interp s_pc.(mem)) with "[Hmem]" as "Hmem".
    { unfold s_pc; rewrite ?mem_set_reg. iExact "Hmem". }
    iDestruct (gpr_file_values m s_pc with "Hreg Hgpr") as %Hvals.
    (* the pins, transported across the nextPC write *)
    assert (Tn : forall (r : register) (v : type_of_register r),
              register_lookup r sf.(sregs) = v ->
              register_beq r nextPC = false ->
              register_lookup r s_pc.(sregs) = v).
    { intros r v Hv Hne. unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    pose proof (agree_u_set_nextPC sf (add_vec_int pc d) Hagreef) as Hagree.
    pose proof (agree_u_priv s_pc Hagree) as Lprivp.
    pose proof (agree_u_misa s_pc Hagree) as Lmisap.
    pose proof (agree_u_menvcfg s_pc Hagree) as Lmenvp.
    pose proof (agree_u_senvcfg s_pc Hagree) as Lsenvp.
    pose proof (Tn htif_tohost_base _ Hhtiff ltac:(vm_compute; reflexivity)) as Lhtifp.
    assert (Lpmar : register_lookup pma_regions s_pc.(sregs)
                    = register_lookup pma_regions sf.(sregs))
      by (apply (Tn pma_regions _ eq_refl); vm_compute; reflexivity).
    assert (Lpmap : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpmar; exact Hpmaf).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs)
                   = register_lookup mstatus sf.(sregs))
      by (apply (Tn mstatus _ eq_refl); vm_compute; reflexivity).
    assert (HSXLp : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lmsp; exact HSXLf).
    assert (Hmprvp : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s_pc.(sregs)))
                       ('b"1") = false)
      by (rewrite Lmsp; exact Hmprvf).
    assert (Hmxrp : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s_pc.(sregs)))
                      ('b"0") = true)
      by (rewrite Lmsp; exact Hmxrf).
    assert (Lpcp : register_lookup PC s_pc.(sregs) = pc)
      by (apply (Tn PC _ Lpcf); vm_compute; reflexivity).
    assert (Lnpcp : register_lookup nextPC s_pc.(sregs) = add_vec_int pc d)
      by (unfold s_pc; rewrite ?sregs_set_reg; apply register_lookup_set).
    (* the translation mode, read off the invariant *)
    iDestruct (utlb_inv_pt_translationMode_U (ud_root pt) (ud_tfp pt) (ud_um pt)
                 s_pc HSXLp with "Hreg Hutlb") as "(%Htm & Hreg & Hutlb)".
    (* the load *)
    iMod (umem_load_k k Hk Hk8 Hkdvd Huintk Hread_plain pt M w_ld va s_pc
            Hl Hchk Hcanon Hpg Hal HMb Lmisap Lmenvp Lhtifp Lprivp HSXLp Hmprvp Lpmap
            with "Hreg Hmem Hutlb Humem")
      as (sig2) "(%Htr & %Hmr & %Hmdev2 & %Tr2 & Hreg & Hmem & Hutlb & Humem)".
    (* the execute, value-precise *)
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s_pc.(sregs)) = m !!! Regidx rs1)
      by (exact (Hvals rs1)).
    assert (Hex : exec (execute (uv_exp i o)) s_pc
                  = Some (RETIRE_SUCCESS,
                          uv_wr sig2 (Some (rd, wval)))).
    { rewrite Hexp. cbn [uv_wr]. rewrite Hwval.
      apply (exec_execute_LOAD_k_u_walk k Hvw rs1 rd imm is_unsigned
               (m !!! Regidx rs1) (u_walk_pa w_ld va)
               (uM_word M (uint va) k) Sv39 s_pc sig2 Hrd Lprivp
               (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s_pc.(sregs)) User s_pc Hmprvp)
               (exec_get_pmlen_u (Load Data) s_pc
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrp Lmisap Lmenvp Lsenvp)
               Htm Hbase);
        [ rewrite <- Hva; exact Hal
        | rewrite <- Hva; exact Htr
        | exact Hmr ]. }
    pose proof (Hprog _ Hex) as Hha.
    (* the rd write, on the ghost side *)
    iAssert (mstate_interp sig2) with "[Hreg Hmem Hdev]" as "Hint".
    { unfold mstate_interp. rewrite Hmdev2. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev". }
    iMod (uv_wr_ghost sig2 (Some (rd, wval)) m Hrd with "Hint Hgpr")
      as "[Hint Hgpr]".
    iEval (cbn [uv_upd]) in "Hgpr".
    assert (Lnpc2 : register_lookup nextPC sig2.(sregs) = add_vec_int pc d).
    { rewrite (Tr2 nextPC ltac:(vm_compute; reflexivity)). exact Lnpcp. }
    assert (Lnpcx : register_lookup nextPC
              (uv_wr sig2 (Some (rd, wval))).(sregs) = add_vec_int pc d).
    { exact (uv_post_nextPC sig2 None (Some (rd, wval)) (add_vec_int pc d) Lnpc2). }
    iApply (uv_retire_post_state CIDp
              (P ∗ utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
               umem pt M ∗ gpr_file (<[Regidx rd := regval_into_reg wval]> m))%I
              sg (uv_wr sig2 (Some (rd, wval))) b mst pc (add_vec_int pc d) ib
              Hsi Hhart_a Lnpcx Hha
              with "Hint [$HP $Hutlb $Humem $Hgpr] Hhs Hpc Hnpc Hmst Hmi [Hcont]").
    iNext. iIntros "(HP & Hutlb & Humem & Hgpr) Hhs Hpc Hnpc".
    iApply ("Hcont" with "HP Hutlb Humem Hhs Hpc Hnpc Hgpr").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE LOAD LEAF.                                                        *)
  (*                                                                       *)
  (* Width- and signedness-generic: [k] is any [uload_width] (1/2/4/8) and *)
  (* [is_unsigned] any bool, so [lb/lbu/lh/lhu/lw/lwu/ld] and every        *)
  (* compressed load are ONE lemma.  It takes the same [uinstr] /          *)
  (* [uv_redirect] pair the funnel does, so a compressed load names its    *)
  (* [ExecuteAs] expansion; the loaded value is the image word, so the     *)
  (* image comes back UNCHANGED and the register file gains exactly        *)
  (* [<[rd := wval]>].                                                     *)
  (*                                                                       *)
  (* [uint rd <> 0] is a PREMISE: [uinstr] only says what the word decodes *)
  (* to, and a load into x0 is a legal (value-discarding) encoding the     *)
  (* funnel's write layer does not describe.                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_load (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (w_ld va wval : mword 64) :
    uload_width k ->
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hlpad Hexp Hrd Hva Hl Hchk Hcanon Hpg Hal HMb Hwval.
    destruct Hui as [Hal2 Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgprc)".
    iAssert (uv_cap_gpr C pt Ψ M m) with "[Hlin Hgprc]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgprc". }
    iApply (wp_uv_step C pt Ψ M m pc with "Hcg Hpc [Hcont]").
    rewrite /uv_step_obl.
    iIntros (CID0 sg ms_v sc_v stval_v sepc_v)
      "%Hmsok %Lpriv %Lms %Lpc %Hdisp #Hamb Hhs Hpriv Hms Hsc Hstval Hsepc
       Hpc Hnpc Hgpr Hutlb Humem Hcfg Hint Hbody".
    iAssert uv_amb with "[]" as "#Hamb2". { iExact "Hamb". }
    iDestruct "Hamb" as "(#Hhw & #Hmin & #Hwinv)".
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hsenv & Hmse & Hsse)".
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmse") as %Lmse.
    iDestruct (reg_valid_dq with "Hreg Hsse") as %Lsse.
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & #Hpma & #Hhtif & #Help & _ & _ & _ & _ & _ & %Hpma_all
        & _ & _ & %Help_ne & _ & %Hmisaval & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    subst misa0.
    iAssert (user_cfg C)
      with "[Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse". }
    (* ---- the minstret prelude ---- *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege sg.(sregs)) sg) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r sg.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    pose proof (T hart_state _ Lhs eq_refl) as Hhart_a.
    pose proof (T PC _ Lpc eq_refl) as LpcA.
    pose proof (T cur_privilege _ Lpriv eq_refl) as LprivA.
    pose proof (T misa _ Lmisa eq_refl) as LmisaA.
    pose proof (T menvcfg _ Lmenv eq_refl) as LmenvA.
    pose proof (T senvcfg _ Lsenv eq_refl) as LsenvA.
    pose proof (T mstateen0 _ Lmse eq_refl) as LmseA.
    pose proof (T sstateen0 _ Lsse eq_refl) as LsseA.
    pose proof (T elp _ Lelp eq_refl) as LelpA.
    assert (HSXL : _get_Mstatus_SXL
              (register_lookup mstatus (set_reg sg (R_bool minstret_increment) b).(sregs))
              = 'b"10")
      by (rewrite (T mstatus _ Lms eq_refl); exact (proj1 Hmsok)).
    assert (HpmaA : pma_allows_all
              (register_lookup pma_regions
                 (set_reg sg (R_bool minstret_increment) b).(sregs)))
      by (rewrite (T pma_regions _ Lpma eq_refl); exact Hpma_all).
    pose proof (Hdisp b) as HdispA.
    (* every post-fetch pin, in one place *)
    assert (Hsf : forall sf : mstate,
              (forall r : register, register_beq r tlb = false ->
                 register_lookup r sf.(sregs)
                   = register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs)) ->
              register_lookup PC sf.(sregs) = pc /\
              register_lookup cur_privilege sf.(sregs) = User /\
              register_lookup misa sf.(sregs) = MISA_C /\
              eq_vec (register_lookup elp sf.(sregs))
                     (landing_pad_bits_backwards LP_EXPECTED) = false /\
              agree_on D_u sf dstateU /\
              register_lookup htif_tohost_base sf.(sregs) = None /\
              register_lookup mstatus sf.(sregs) = ms_v /\
              pma_allows_all (register_lookup pma_regions sf.(sregs))).
    { intros sf Tr. split_and!.
      - rewrite (Tr PC ltac:(vm_compute; reflexivity)). exact LpcA.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
      - rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr elp ltac:(vm_compute; reflexivity)). rewrite LelpA. exact Help_ne.
      - apply agree_u.
        + rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
        + rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)). exact LmenvA.
        + rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)). exact LsenvA.
        + rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)). exact LmseA.
        + rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)). exact LsseA.
        + rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)).
        exact (T htif_tohost_base _ Lhtif eq_refl).
      - rewrite (Tr mstatus ltac:(vm_compute; reflexivity)).
        exact (T mstatus _ Lms eq_refl).
      - rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)). exact HpmaA. }
    (* the closure every geometry hands to [uv_load_post_fetch] *)
    iAssert (▷ (True -∗
                utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
                umem pt M -∗
                hart_state ↦ᵣ HART_ACTIVE tt -∗
                PC ↦ᵣ add_vec_int pc (if is_rvc then 2 else 4) -∗
                nextPC ↦ᵣ add_vec_int pc (if is_rvc then 2 else 4) -∗
                gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
                WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hpriv Hms Hsc Hstval Hsepc Hcfg]" as "Hk".
    { iNext. iIntros "_ Hutlb Humem Hhs Hpc Hnpc Hgpr".
      iApply ("Hcont" $! CID0 with "[-Hpc Hnpc] [$Hpc $Hnpc]").
      rewrite /uv_cap_gpr /uv_lin.
      iFrame "Hcap Hamb2 Hutlb Humem Hcfg Hgpr".
      rewrite /uv_regs.
      iExists ms_v, sc_v, stval_v, sepc_v.
      iSplitR; [ iPureIntro; exact Hmsok | ].
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc". }
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* 4-aligned: one 4-byte read *)
        destruct (Hnext2 ltac:(first [exact Hal4 | reflexivity]))
          as (b2 & b3 & Hb2 & Hb3).
        iMod (umode_fetch_rvc_4 pt M w_leaf pc h b2 b3
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanonpc Hinpage Hal4 Hbytes Hb2 Hb3 HisRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr)
          as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
        iApply (uv_load_post_fetch CID0 True%I sg sf b mst pc 2
                  (zero_extend' 32 h) m M i o imm rs1 rd is_unsigned k
                  w_ld va wval Hkw
                  Hsi Hhart_a Lpcf Hagree Lhtiff
                  ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                  Hpmaf Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
                  (uv_prog_rvc _ _ h i o pc LprivA HdispA Hfetch
                     (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                     Helpf Lpcf
                     (exec_currentlyEnabled_Zca sf
                        ltac:(rewrite Lmisaf; vm_compute; reflexivity)) Hred)
                  with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        * unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
          iFrame "Hreg Hmem Hdev".
        * done.
      + (* 2 mod 4: one 2-byte read *)
        iMod (umode_fetch_rvc_2 pt M w_leaf pc h
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HisRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr)
          as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
        iApply (uv_load_post_fetch CID0 True%I sg sf b mst pc 2
                  (zero_extend' 32 h) m M i o imm rs1 rd is_unsigned k
                  w_ld va wval Hkw
                  Hsi Hhart_a Lpcf Hagree Lhtiff
                  ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                  Hpmaf Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
                  (uv_prog_rvc _ _ h i o pc LprivA HdispA Hfetch
                     (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                     Helpf Lpcf
                     (exec_currentlyEnabled_Zca sf
                        ltac:(rewrite Lmisaf; vm_compute; reflexivity)) Hred)
                  with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        * unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
          iFrame "Hreg Hmem Hdev".
        * done.
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + iMod (umode_fetch_base_4 pt M w_leaf pc w
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanonpc Hinpage Hal4 Hbytes HnRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr)
          as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
        iApply (uv_load_post_fetch CID0 True%I sg sf b mst pc 4
                  (zero_extend' 32 w) m M i o imm rs1 rd is_unsigned k
                  w_ld va wval Hkw
                  Hsi Hhart_a Lpcf Hagree Lhtiff
                  ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                  Hpmaf Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
                  (uv_prog_base _ _ w i o pc LprivA HdispA Hfetch
                     (Hdecbase sf Hagree) Helpf Hlpad Lpcf Hred)
                  with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        * unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
          iFrame "Hreg Hmem Hdev".
        * done.
      + iMod (umode_fetch_base_2 pt M w_leaf pc w
                (set_reg sg (R_bool minstret_increment) b)
                Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HnRVC
                LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
                HSXL HpmaA
                with "[Hreg] [Hmem] Hutlb Humem")
          as (sf) "(%Hfetch & %Hmdev & %Tr & Hreg & Hmem & Hutlb & Humem)".
        { rewrite ?sregs_set_reg. iExact "Hreg". }
        { rewrite ?mem_set_reg. iExact "Hmem". }
        destruct (Hsf sf Tr)
          as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
        iApply (uv_load_post_fetch CID0 True%I sg sf b mst pc 4
                  (zero_extend' 32 w) m M i o imm rs1 rd is_unsigned k
                  w_ld va wval Hkw
                  Hsi Hhart_a Lpcf Hagree Lhtiff
                  ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                  ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                  Hpmaf Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
                  (uv_prog_base _ _ w i o pc LprivA HdispA Hfetch
                     (Hdecbase sf Hagree) Helpf Hlpad Lpcf Hred)
                  with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
        * unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
          iFrame "Hreg Hmem Hdev".
        * done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ld rd, imm(rs1) -- the base 8-byte SIGNED load (echo's 0x0004b903).  *)
  (* Base geometry, no [ExecuteAs] redirect, so [o := None] and the        *)
  (* extension is the identity ([extend_value_w8]): the register gets the  *)
  (* image doubleword itself.                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_ld (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5)
      (w_ld va wval : mword 64) :
    uinstr pt M pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = uM_word M (uint va) 8 ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hl Hchk Hcanon Hpg Hal HMb Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) None
              imm rs1 rd false 8 w_ld va wval
              uload_width_8 Hui ltac:(intro s; exact I) eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal HMb
              ltac:(rewrite extend_value_w8; exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ldsp rd, uimm(sp) -- the compressed 8-byte load off sp (echo's      *)
  (* 0x60a2 / 0x6402): the [ExecuteAs] expansion is                        *)
  (* [LOAD (zext(uimm ++ 000), sp, rd, false, 8)]                          *)
  (* ([exec_execute_C_LDSP]).  rd = x0 is reserved by the ISA, so          *)
  (* [uint rd <> 0] costs a call site nothing.                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cldsp (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (w_ld va wval : mword 64) :
    uinstr pt M pc true (C_LDSP (uimm, Regidx rd)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = uM_word M (uint va) 8 ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hl Hchk Hcanon Hpg Hal HMb Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc true (C_LDSP (uimm, Regidx rd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           Regidx csp_rs1, Regidx rd, false, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              csp_rs1 rd false 8 w_ld va wval
              uload_width_8 Hui
              ltac:(intro s; apply exec_execute_C_LDSP)
              eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal HMb
              ltac:(rewrite extend_value_w8; exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lbu rd, imm(rs1) -- the base 1-byte UNSIGNED load (echo's 0x00054783 *)
  (* / 0xfff7c703): the value is [zero_extend' 64] of ONE image byte.      *)
  (* A 1-byte access is trivially aligned and can never cross a page, so   *)
  (* both the alignment and the in-page premises are discharged HERE --   *)
  (* the call site supplies only the byte.                                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_lbu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5)
      (w_ld va wval : mword 64) (bb : mword 8) :
    uinstr pt M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    wval = zero_extend' 64 bb ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hl Hchk Hcanon Hbb Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc false
              (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) None
              imm rs1 rd true 1 w_ld va wval
              uload_width_1 Hui ltac:(intro s; exact I) eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon (uinpage_1 va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              ltac:(rewrite (uM_word_byte_val M (uint va) bb Hbb); exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

End WpUmodeLoad.
