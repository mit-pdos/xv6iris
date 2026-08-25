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

   §2 [uv_load_mm] -- THE PORT'S CENTRE, and the exact twin of
      WpUmodeStore's [uv_store_mm].  Per-node semantics own the process
      image as the hart's BYTE MAP [uv_mm t (upa_map pt M)], so the access
      is a PURE [exec]-plus-[goodmb] pair over that map rather than a
      [gen_heap_interp] update behind an Iris composer.  The walk is
      WpUmodeStore's [uv_walk_data] at [Load Data] -- the safety tier's
      [UserMemCert.u_load_pure] says the same thing but only at [u_mem_wf]
      (it owns every mapped data byte) and with an EXISTENTIAL value, and
      this tier has neither.

   §3 [exec_execute_LOAD_k_u_walk] / [goodmb_execute_LOAD_k_u_walk] -- the
      value-precise execute at User privilege with MPRV = 0, and its
      certificate.  No autocast trap on this side: the model applies
      [extend_value] to the read value directly.

   §4 [uv_load_post_fetch] -- the geometry-agnostic middle.  The load twin
      of WpUmodeStore's [uv_store_post_fetch]; the image is UNCHANGED, so
      unlike the store this one hands [WpUmodeStep.uv_psi_active] the
      engine's OWN residue (moved along the walk's tree by [uv_res_move])
      and needs no re-imaged closer.

   §5 [uv_load_obl_base] / [uv_load_obl_rvc] and [wp_uv_load] -- ONE width-
      and signedness-generic leaf over all four fetch geometries, plus the
      [echo] instances [wp_uv_ld] / [wp_uv_cldsp] / [wp_uv_lbu] and the
      [sh] instances [wp_uv_lw] / [wp_uv_lwu] / [wp_uv_clw] / [wp_uv_cld].

   [wp_uv_lw] is the tier's first SIGNED narrow load, and it needed nothing
   from the generic leaf: [is_unsigned] is already a parameter and
   [extend_value] is DEFINITIONALLY the branch on it, so [extend_value_w4_s]
   / [extend_value_w4_u] are [reflexivity].  What the k = 4 call sites did
   need is the arithmetic bridge ([uM_word_w4_val_s] / [_u] and
   [sext32_moi] / [zext32_moi] in §1) that spells the loaded value as a
   [mword_of_int] -- at k = 8 [extend_value_w8] made that question
   disappear. *)
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
Require Import WpGpr RegFile InstrBytes.
Require Import SmodeCore.
Require Import WpDecodeBridge DecodeTotalU.
Require Import CommonWalk.
Require Import PtreeType PtTree.
Require Import UserBits UserPtTree.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserExec.
Require UserTotalU.
Require Import UserActiveClass.
Require Import MemAccessGen WpMmodeLeafBase WpLoad.
Require Import UserMemPt UserMemArms UserMemClassify UserMemAccess UserMemMis.
Require Import UserMemCert UserMemArmsBase UserMemArmsC.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep WpUmodeStore.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* THE STEP MASK IS GONE.  Per-node semantics have no fancy-update inside
   the cycle at all -- the whole step is [swp] -- so this file no longer
   spells [wp_exec_step_minstret]'s inner mask anywhere.  What it still
   names of the engine's internals is [user_cfg]'s EIGHT conjuncts (commit
   723de5cb dropped [uc_mip]); everything else goes through
   WpUmodeStore's shared machinery and [WpUmodeStep.uv_psi_active]. *)

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

(* two byte-window facts for the same window determine the same word, AT ANY
   WIDTH ([uM_bytes] is already width-generic; only its two readings below
   are not).  [uM_bytes] is therefore the ONE image premise a call site
   should have to supply: [uM_bytes_exists] recovers [wp_uv_load]'s
   byte-EXISTENCE premise from it and [uM_word_w8] / [uM_word_w4] its VALUE
   premise. *)
Lemma uM_bytes_inj_n {n : N} (M : gmap Z (bv 8)) (a : Z) (w1 w2 : bv (8 * n)) :
  uM_bytes M a (N.to_nat n) w1 -> uM_bytes M a (N.to_nat n) w2 -> w1 = w2.
Proof.
  intros H1 H2. apply bv_eq_of_bytes.
  intros j Hj.
  assert (Hj' : (j < N.to_nat n)%nat) by lia.
  (* stated at the [mword _] index and closed at [bv (8*n)] by
     conversion -- [congruence] is syntactic and the two indices are not *)
  assert (Hb : nth_byte w1 j = nth_byte w2 j).
  { pose proof (H1 j Hj') as E1. pose proof (H2 j Hj') as E2.
    rewrite E1 in E2. congruence. }
  exact Hb.
Qed.

(* two byte-window facts for the same window determine the same word *)
Lemma uM_bytes_inj (M : gmap Z (bv 8)) (a : Z) (w1 w2 : mword 64) :
  uM_bytes M a 8 w1 -> uM_bytes M a 8 w2 -> w1 = w2.
Proof. exact (uM_bytes_inj_n (n := 8) M a w1 w2). Qed.

Lemma uM_bytes4_inj (M : gmap Z (bv 8)) (a : Z) (w1 w2 : mword 32) :
  uM_bytes M a 4 w1 -> uM_bytes M a 4 w2 -> w1 = w2.
Proof. exact (uM_bytes_inj_n (n := 4) M a w1 w2). Qed.

(* a known byte window says the bytes are THERE *)
Lemma uM_bytes_exists {n : N} (M : gmap Z (bv 8)) (a : Z) (k : nat) (w : bv n) :
  uM_bytes M a k w ->
  forall j : nat, (j < k)%nat -> exists b : bv 8, M !! (a + Z.of_nat j) = Some b.
Proof. intros H j Hj. exists (nth_byte w j). exact (H j Hj). Qed.

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

(* ---- k = 4: the two readings of the SIGN FLAG, and the [mword_of_int]
   bridge ---------------------------------------------------------------
   [extend_value] is definitionally the branch on [wp_uv_load]'s
   [is_unsigned], so the flag costs a call site nothing to READ -- both
   lemmas are [reflexivity].  What it costs is the ARITHMETIC: at k = 8
   [extend_value_w8] made the extension vanish, while at k = 4 it is real
   and a caller working in UmodeArith's [mword_of_int] calculus needs the
   extension of a normalized 32-bit datum spelled as a normalized 64-bit
   one.  That is [sext32_moi] / [zext32_moi] below.
   RELOCATION DEBT: the two [*_moi] bridges read naturally beside
   UmodeArith's [zext8_moi]; they live here so that this file's dependency
   set is unchanged. *)
Lemma extend_value_w4_s (w : mword (8 * 4)) : extend_value false w = sign_extend' 64 w.
Proof. reflexivity. Qed.

Lemma extend_value_w4_u (w : mword (8 * 4)) : extend_value true w = zero_extend' 64 w.
Proof. reflexivity. Qed.

(* the width-32 twin of UmodeArith's [zext8_unsigned] *)
Lemma zext32_unsigned (w : mword 32) :
  bv_unsigned (zero_extend' 64 w : mword 64) = bv_unsigned w.
Proof.
  unfold zero_extend'.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

(* [lw] at a value that fits the signed 32-bit range: the sign extension is
   exact ([2 ^ 31] is UmodeArith's [Z31]). *)
Lemma sext32_moi (z : Z) :
  0 <= z < 2 ^ 31 ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* ... and [lwu] on the whole unsigned 32-bit range ([2 ^ 32] = [Z32]) *)
Lemma zext32_moi (z : Z) :
  0 <= z < 2 ^ 32 ->
  (zero_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intro Hz. apply bv_eq.
  rewrite zext32_unsigned moi32_unsigned moi64_unsigned.
  rewrite (bv_wrap_small 32 z ltac:(change (bv_modulus 32) with (2 ^ 32); lia)).
  symmetry. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* ---- [uM_bytes] as the ONE image premise, at k = 8 and k = 4 ---------- *)

Lemma uM_word_w8 (M : gmap Z (bv 8)) (a : Z) (w : mword 64) :
  uM_bytes M a 8 w -> uM_word M a 8 = w.
Proof.
  intro Hw. apply (uM_bytes_inj M a); [ | exact Hw ].
  exact (uM_word_bytes M a 8 ltac:(lia) (uM_bytes_exists M a 8 w Hw)).
Qed.

Lemma uM_word_w4 (M : gmap Z (bv 8)) (a : Z) (w : mword 32) :
  uM_bytes M a 4 w -> uM_word M a 4 = w.
Proof.
  intro Hw. apply (uM_bytes4_inj M a); [ | exact Hw ].
  exact (uM_word_bytes M a 4 ltac:(lia) (uM_bytes_exists M a 4 w Hw)).
Qed.

(* the k = 4 twins of [uM_word_byte_val]: the value a WORD load writes,
   named off the four image bytes. *)
Lemma uM_word_w4_val_s (M : gmap Z (bv 8)) (a : Z) (w : mword 32) :
  uM_bytes M a 4 w -> extend_value false (uM_word M a 4) = sign_extend' 64 w.
Proof. intro Hw. rewrite extend_value_w4_s (uM_word_w4 M a w Hw). reflexivity. Qed.

Lemma uM_word_w4_val_u (M : gmap Z (bv 8)) (a : Z) (w : mword 32) :
  uM_bytes M a 4 w -> extend_value true (uM_word M a 4) = zero_extend' 64 w.
Proof. intro Hw. rewrite extend_value_w4_u (uM_word_w4 M a w Hw). reflexivity. Qed.

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

Lemma uload_width_4 : uload_width 4.
Proof.
  split; [ right; right; left; reflexivity | exact exec_read_ram_plain_4 ].
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
(* §2 The pure k-byte read at the tier's own byte map.                     *)
(*                                                                        *)
(* The load twin of WpUmodeStore's [uv_store_mm], and built the same way:  *)
(* per-node semantics own the process image as the hart's BYTE MAP, so the *)
(* access is an [exec]-plus-[goodmb] pair over that map rather than a      *)
(* [gen_heap_interp] update behind an Iris composer.  The walk is          *)
(* WpUmodeStore's [uv_walk_data] at [Load Data]; everything above it is    *)
(* the width-k instance of UserMemPt's bricks at the CONCRETE image word.  *)
(* ===================================================================== *)

Section UvLoadPure.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) (s : mstate),
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s
        = Some ((w, default_meta), s)).

  Lemma uv_load_mm (pt : uptd) (t : ptree) (md : PtBytes.pamap) (rs : regstate)
      (w va : mword 64) (dv : mword (8 * k)) :
    ud_um pt !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    uva_canon va ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    in_one_page va k ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       md !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j)) ->
    u_data_cfg rs ->
    u_exec_pins pt t rs ->
    uv_tree_ok pt md t ->
    exists (rs' : regstate) (t' : ptree),
      exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
        (u_state rs (uv_mm t md)) = Some (Ok dv, u_state rs' (uv_mm t' md)) /\
      goodmb Du_r Du_w
        (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
        (u_state rs (uv_mm t md)) (uv_mm t md) = true /\
      u_tlb_only rs rs' /\
      tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
      uv_tree_ok pt md t' /\
      pt_same_shape 2 t t'.
  Proof.
    intros Hl Hleaf Hcanon Hal Hin Hwin Hcfg Hpins Htok.
    destruct (uv_walk_data (Load Data) pt t md rs w va
                (or_intror (or_introl eq_refl))
                Hl Hleaf Hcanon Hcfg Hpins Htok)
      as (rs' & t' & Htr & Htrg & Tonly & Htlbok' & Htok' & Hshape).
    set (pa := u_walk_pa w va) in *.
    set (mm := uv_mm t md) in *.
    set (mm' := uv_mm t' md) in *.
    set (s' := u_state rs' mm').
    pose proof Htok' as (Hdisj' & Hdj' & Hram' & Hwfm' & Hspec').
    (* the access window, in the landing map *)
    assert (Hbytes : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
              s'.(mem) !! pa_add pa j = Some (nth_byte dv j)).
    { intros j Hj. unfold s', mm'; cbn [u_state mem].
      rewrite /uv_mm.
      rewrite (lookup_union_r (ptree_bytes 2 t') md _
                 (uv_mm_tree_none t' md _ Hdj'
                    (mk_is_Some _ _ (Hwin j ltac:(lia))))).
      exact (Hwin j ltac:(lia)). }
    assert (Hws : forall j : nat, (j < Z.to_nat k)%nat -> is_Some (mm' !! pa_add pa j))
      by (intros j Hj; exact (mk_is_Some _ _ (Hbytes j ltac:(lia)))).
    assert (Hown : bytes_owned mm' pa (Z.to_N k) = true).
    { apply bytes_owned_of_dom. intros j Hj. apply elem_of_dom.
      apply Hws. lia. }
    assert (Hramj : forall j : nat, (j < Z.to_nat k)%nat -> addr_is_ram (pa_add pa j))
      by (intros j Hj; apply Hram', elem_of_dom, (Hws j Hj)).
    assert (Hram0 : addr_is_ram pa)
      by (rewrite <- (pa_add_0 pa); apply Hramj; lia).
    assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1)))
      by (apply Hramj; lia).
    assert (Hdev : dev_addr pa = false) by exact (addr_is_ram_not_dev _ Hram0).
    (* the cfg and the pins, at the landing file *)
    assert (Hcfg' : u_data_cfg rs').
    { destruct Hcfg as (Lcp0 & Lms0 & Lmenv0). split_and!;
        [ rewrite (Tonly cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp0
        | rewrite (Tonly mstatus ltac:(vm_compute; reflexivity)); exact Lms0
        | rewrite (Tonly menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv0 ]. }
    assert (Hpins' : u_exec_pins pt t' rs').
    { unfold u_exec_pins, u_hw_pins, u_cfg_pins, u_pt_pins in Hpins |- *.
      destruct Hpins as ((Hmisa0 & Hsec0 & Hsenv0 & Hhtif0 & Hall0 & Help0) &
                         (Hmste0 & Hsste0) &
                         ((usatp0 & Hsatpok0 & Hsatp0) & HA0 & Hord0 & HX0 & HW0 & HR0 & Hcov0) &
                         _).
      split_and!;
        [ rewrite (Tonly misa ltac:(vm_compute; reflexivity)); exact Hmisa0
        | rewrite (Tonly mseccfg ltac:(vm_compute; reflexivity)); exact Hsec0
        | rewrite (Tonly senvcfg ltac:(vm_compute; reflexivity)); exact Hsenv0
        | rewrite (Tonly htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif0
        | rewrite (Tonly pma_regions ltac:(vm_compute; reflexivity)); exact Hall0
        | rewrite (Tonly elp ltac:(vm_compute; reflexivity)); exact Help0
        | rewrite (Tonly mstateen0 ltac:(vm_compute; reflexivity)); exact Hmste0
        | rewrite (Tonly sstateen0 ltac:(vm_compute; reflexivity)); exact Hsste0
        | exists usatp0; split;
            [ exact Hsatpok0
            | rewrite (Tonly satp ltac:(vm_compute; reflexivity)); exact Hsatp0 ]
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA0
        | rewrite (Tonly pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord0
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX0
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW0
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR0
        | rewrite (Tonly pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcov0
        | exact Htlbok' ]. }
    pose proof Hcfg' as (Lcp & Lms & Lmenv).
    pose proof Lms as (Lsxl & Lmprv & Lmxr).
    pose proof Hpins' as ((Hmisa & Hsec & Hsenv & Hhtif & Hall & Help) & _ &
                          ((usatp & _ & Hsatp) & HA & Hord & _ & _ & HR & Hcovp) & _).
    destruct (pma_all_ram Hall pa k
                (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                   Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
      as (region & Hpmam & _ & Hrd & _).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
              (uint pa) (uint (to_bits 64 k)) = PMP_Match)
      by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk ltac:(lia) Huintk
                  ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
    assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
      by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
    assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
      by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
    assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
      by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
    assert (Hhtr : exec (within_htif_readable (Physaddr pa) k) s' = Some (false, s'))
      by exact (within_htif_false pa k s' Hhtif).
    (* the physical read, exec side and certificate side *)
    assert (Hmr : exec (mem_read (Load Data) PBMT_PMA (Physaddr pa) k
                          false false false) s' = Some (Ok dv, s'))
      by exact (exec_mem_read_data_U k Hk Hread_plain PBMT_PMA pa region dv s'
                  HA Hord Hrange HR Hpmam Halign Hrd Hclint Hsig Hhtr Hdev
                  Hbytes Lmprv Lcp).
    assert (Hchke : exec (checked_mem_read (Load Data) PBMT_PMA User (Physaddr pa) k
                            false false false false) s'
                    = Some (Ok (dv, default_meta), s'))
      by exact (exec_checked_mem_read_ram_U k Hk Hread_plain PBMT_PMA pa region dv s'
                  HA Hord Hrange HR Hpmam Halign Hrd Hclint Hsig Hhtr Hdev Hbytes).
    assert (Hchkg : goodmb Du_r Du_w (checked_mem_read (Load Data) PBMT_PMA User
                             (Physaddr pa) k false false false false) s' mm' = true)
      by exact (goodmb_checked_mem_read_ram_U Du_r Du_w k Hk PBMT_PMA pa region
                  dv s' mm'
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  HA Hord Hrange HR Hpmam Halign Hrd Hclint Hsig Hhtif Hdev Hown
                  (Hread_plain pa dv s' Hdev Hbytes)).
    assert (Hmrg : goodmb Du_r Du_w (mem_read (Load Data) PBMT_PMA (Physaddr pa) k
                            false false false) s' mm' = true)
      by exact (goodmb_mem_read_data_U Du_r Du_w k PBMT_PMA pa dv s' mm'
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Lmprv Lcp Hchkg Hchke).
    (* ...and the certificates, read back at the ENTRY map *)
    assert (Hdomm : (dom mm' : gset Arch.pa) = dom mm)
      by (unfold mm, mm'; symmetry; exact (uv_mm_dom t t' md Hshape)).
    assert (Hmrg' : goodmb Du_r Du_w (mem_read (Load Data) PBMT_PMA (Physaddr pa) k
                             false false false) s' mm = true)
      by (rewrite (goodmb_dom Du_r Du_w _ s' mm mm' (eq_sym Hdomm)); exact Hmrg).
    (* the top: the in-one-page vmem read *)
    pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin) as Hsp.
    pose proof (goodmb_split_on_page_boundary_intra Du_r Du_w va k
                  (u_state rs mm) mm Hk Hin) as Hspg.
    pose proof (u_effectivePrivilege_pure (Load Data) rs mm Hcfg) as Heff0.
    pose proof (u_goodmb_effectivePrivilege_pure (Load Data) rs mm mm Hcfg) as Heff0g.
    pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm0.
    pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htm0g.
    pose proof (exec_translate_and_read_value_g k va pa PBMT_PMA dv
                  (u_state rs mm) s' s' Htr Hmr) as Htrv.
    pose proof (goodmb_translate_and_read_value_gen Du_r Du_w k va pa (Load Data)
                  false false false PBMT_PMA dv (u_state rs mm) s' s' mm
                  Htr Htrg Hmr Hmrg') as Htrvg.
    exists rs', t'. split_and!;
      [ | | exact Tonly | exact Htlbok' | exact Htok' | exact Hshape ].
    - exact (exec_vmem_read_addr_intra k va pa dv (Load Data) false false false
               User Sv39 (u_state rs mm) s' Hk Hsp (or_introl Hal) Heff0 Htm0 Htrv
               ltac:(intro Hc; discriminate Hc)).
    - exact (goodmb_vmem_read_addr_intra Du_r Du_w k va pa dv (Load Data)
               false false false User Sv39 (u_state rs mm) s' mm
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Hk Hsp Hspg (or_introl Hal) Heff0 Heff0g Htm0 Htm0g Htrv Htrvg).
  Qed.

End UvLoadPure.

(* ===================================================================== *)
(* §3 The value-precise k-byte LOAD execute at User.                       *)
(* ===================================================================== *)

Section UmodeLoadExec.
  Context (k : Z).
  Context (Hkw : vmem_width k).

  (* THE execute fact: [l{b,h,w,d}[u] rd, imm(rs1)] at User with MPRV = 0,
     and its certificate.  The load twin of WpUmodeStore's
     [exec_execute_STORE_k_u_walk] / [goodmb_execute_STORE_k_u_walk]. *)
  Lemma exec_execute_LOAD_k_u_walk (rs1 rd : mword 5) (imm : mword 12)
      (is_unsigned : bool) (base : mword 64) (dv : mword (8 * k))
      (md : SATPMode) (s s2 : mstate) :
    uint rd <> 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    exec (get_pmlen (Load Data) User) s = Some (0, s) ->
    exec (translationMode User) s = Some (md, s) ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    exec (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s = Some (Ok dv, s2) ->
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s
      = Some (RETIRE_SUCCESS,
              set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value is_unsigned dv))).
  Proof.
    intros Hrd Hcp Heff Hpml Htm Hbase Hvra.
    apply (exec_execute_LOAD_u_ok imm rs1 rd is_unsigned k dv s s2
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (vmem_width_le8 k Hkw)) Hrd).
    apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data)
             false false false md (Ok dv) s s2 Hcp Heff Hpml Htm).
    rewrite Hbase. exact Hvra.
  Qed.

  Lemma goodmb_execute_LOAD_k_u_walk (rs1 rd : mword 5) (imm : mword 12)
      (is_unsigned : bool) (base : mword 64) (dv : mword (8 * k))
      (md : SATPMode) (s s2 : mstate) (mm : PtBytes.pamap) :
    uint rd <> 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    goodmb Du_r Du_w (effectivePrivilege (Load Data)
             (register_lookup mstatus s.(sregs)) User) s mm = true ->
    exec (get_pmlen (Load Data) User) s = Some (0, s) ->
    goodmb Du_r Du_w (get_pmlen (Load Data) User) s mm = true ->
    exec (translationMode User) s = Some (md, s) ->
    goodmb Du_r Du_w (translationMode User) s mm = true ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    exec (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s = Some (Ok dv, s2) ->
    goodmb Du_r Du_w (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s mm = true ->
    goodmb Du_r Du_w (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k)))
      s mm = true.
  Proof.
    intros Hrd Hcp Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvra Hvrag.
    apply (goodmb_execute_LOAD_u_ok Du_r Du_w imm rs1 rd is_unsigned k dv s s2 mm
             (Du_gpr_of_Z rd Hrd)
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (vmem_width_le8 k Hkw)) Hrd).
    - apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data)
               false false false md (Ok dv) s s2 Hcp Heff Hpml Htm).
      rewrite Hbase. exact Hvra.
    - apply (goodmb_vmem_read_u Du_r Du_w rs1 (sign_extend' 64 imm) k (Load Data)
               false false false md (Ok dv) s s2 mm
               (fun H => Du_gpr_of_Z_r rs1 H)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Hcp Heff Heffg Hpml Hpmlg Htm Htmg);
        rewrite Hbase; [ exact Hvra | exact Hvrag ].
  Qed.

End UmodeLoadExec.

(* ===================================================================== *)
(* §4 The load's post-fetch middle.                                        *)
(* ===================================================================== *)

Section UvLoadPostFetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).

  (* the load twin of WpUmodeStore's [uv_store_post_fetch]: from the fetched
     file, write nextPC, run the load, and hand [uv_psi_active] the payload
     at the UNCHANGED image and the gpr-updated register file. *)
  Lemma uv_load_post_fetch (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) :
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned (uM_word M (uint va) kk) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uva_inj pt M ->
    u_exec_pins pt t' rs2 ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rsE)
          (register_lookup (R_bitvector_64 minstretcfg) rsE)
          (register_lookup cur_privilege rsE) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt M) t' ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx lrd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc dpc) -∗
       WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt M)) -∗
    uv_res pt M t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok'.
    destruct Hkw as (Hvw & Hread_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof (vmem_width_le8 kk Hvw) as Hk8.
    pose proof (vmem_width_dvd kk Hvw) as Hkdvd.
    pose proof (vmem_width_uint kk Hvw) as Huintk.
    set (md := upa_map pt M).
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    set (pa := u_walk_pa w_ld va).
    set (dv := uM_word M (uint va) kk).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by (apply (Tn _ _ Lpc2); vm_compute; reflexivity).
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc dpc)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc dpc) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    assert (Hpinsx : u_exec_pins pt t' rsx)
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc dpc) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    (* ---- the access window, in the re-keyed image ---- *)
    assert (Hnc : forall j : nat, (j < Z.to_nat kk)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nck va kk j Hpg). lia. }
    assert (Hwin : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_pa pt (uint va + Z.of_nat j) = pa_add pa j)
      by (intros j Hj; exact (uva_pa_window pt w_ld va j Hl (Hnc j Hj))).
    assert (Hmdw : forall j : nat, (j < Z.to_nat kk)%nat ->
              md !! pa_add pa j = Some (nth_byte dv j)).
    { intros j Hj. rewrite <- (Hwin j Hj).
      exact (upa_map_lookup pt M _ _ Hinj
               (uM_word_bytes M (uint va) kk ltac:(lia) HMb j Hj)). }
    (* ---- the load, pure ---- *)
    destruct (uv_load_mm kk Hk Hk8 Hkdvd Huintk Hread_plain pt t' md rsx
                w_ld va dv Hl Hchk Hcanon Hal (uinpage_one va kk Hpg)
                Hmdw Hcfgx Hpinsx Htok')
      as (rsr & t'' & Hvra & Hvrag & Tonly & Htlbok'' & Htok'' & Hshape).
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint lr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint lr1))) rsx)
                    = m !!! Regidx lr1) by exact (Hvals lr1).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Load Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Load Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Load Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Load Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (RETIRE_SUCCESS,
                          u_state (uv_post_rs rsr None (Some (lrd, wval)))
                            (uv_mm t'' md))).
    { rewrite Hexp Hwval.
      exact (exec_execute_LOAD_k_u_walk kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) dv Sv39 (u_state rsx (uv_mm t' md))
               (u_state rsr (uv_mm t'' md))
               Hrd Lcpx Heff Hpml Htm Hbase
               ltac:(rewrite <- Hva; exact Hvra)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_LOAD_k_u_walk kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) dv Sv39 (u_state rsx (uv_mm t' md))
               (u_state rsr (uv_mm t'' md)) (uv_mm t' md)
               Hrd Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase
               ltac:(rewrite <- Hva; exact Hvra)
               ltac:(rewrite <- Hva; exact Hvrag)). }
    assert (Hdomall : (dom (uv_mm t'' md) : gset Arch.pa) = dom (uv_mm t' md))
      by exact (eq_sym (uv_mm_dom t' t'' md Hshape)).
    (* ---- the post-execute file, from the pre-fetch one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              uv_nogpr r ->
              register_lookup r (uv_post_rs rsr None (Some (lrd, wval))) = vv).
    { intros r vv Hv Hne Hnt Hng.
      rewrite (uv_post_rs_other rsr None (Some (lrd, wval)) r Hne Hng).
      rewrite (Tonly r Hnt). exact (Tn r vv Hv Hne). }
    assert (Lnpcw : register_lookup (R_bitvector_64 nextPC)
                      (uv_post_rs rsr None (Some (lrd, wval))) = add_vec_int pc dpc).
    { cbn [uv_post_rs uv_jmp_rs uv_wr_rs].
      rewrite (irrelevant_register_set _ _ rsr _ (regbeq_nextPC_gpr (uint lrd))).
      rewrite (Tonly (R_bitvector_64 nextPC) ltac:(vm_compute; reflexivity)).
      exact Lnpcx. }
    assert (Hgagr : u_gpr_agree m rsr).
    { intros q Hnz. rewrite (Tonly _ (uv_gpr_ne_tlb (uint q))). exact (Hgagx q Hnz). }
    assert (Ltlbw : register_lookup tlb (uv_post_rs rsr None (Some (lrd, wval)))
                    = register_lookup tlb rsr)
      by exact (uv_post_rs_other rsr None (Some (lrd, wval)) tlb
                  ltac:(vm_compute; reflexivity) uv_nogpr_tlb).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hmm Hres Hrw Hro".
    iApply (uv_swp_exec_mem (uc_dqc C) (uv_mm t' md) (uv_mm t'' md)
              rsx (uv_post_rs rsr None (Some (lrd, wval))) i o ib _
              Hred Hg1 Hexg Hex Hdomall
              with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hmm Hany".
    rewrite /uv_step_post.
    iExists (uv_post_rs rsr None (Some (lrd, wval))).
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_hart)
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_minc)
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 (uv_post_rs rsr None (Some (lrd, wval))) u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3
                 (uv_post_rs rsr None (Some (lrd, wval))) u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_active C pt R Ψ M (<[Regidx lrd := regval_into_reg wval]> m)
              (add_vec_int pc dpc) t'' usatp pcfg paddr
              (uv_post_rs rsr None (Some (lrd, wval)))
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_hart)
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_priv)
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity) uv_nogpr_mst);
                    exact Hms2)
              Lnpcw
              (uv_gpr_agree_post m rsr None (Some (lrd, wval)) Hrd Hgagr)
              (uv_upd_x0 m (Some (lrd, wval)) Hrd Hx0)
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_stvec)
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mie)
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mdl)
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_medl)
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_menv)
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mste)
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_sste)
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_senv)
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_satp)
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_pcfg)
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_paddr)
              Htok'' ltac:(rewrite Ltlbw; exact Htlbok'')
              with "Hamb Hcap Hany Hmm [Hres] Hk").
    iApply (uv_res_move pt M t' t'' usatp pcfg paddr Hshape with "Hres").
  Qed.

End UvLoadPostFetch.

(* ===================================================================== *)
(* §5 The obligation per fetch shape, and the leaf.                        *)
(* ===================================================================== *)

Section UvLoadObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).

  Lemma uv_load_obl_base (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (lr1 lrd : mword 5) (is_unsigned : bool) (w_ld va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned (uM_word M (uint va) kk) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx lrd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗ WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hrd Hva
      Hwval Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, i, pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_load_post_fetch C pt R Ψ M m pc 4 kk i o imm lr1 lrd is_unsigned
              w_ld va wval (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj
              Hpins2
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

  Lemma uv_load_obl_rvc (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (lr1 lrd : mword 5) (is_unsigned : bool) (w_ld va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned (uM_word M (uint va) kk) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx lrd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗ WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hrd Hva
      Hwval Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_load_post_fetch C pt R Ψ M m pc 2 kk i o imm lr1 lrd is_unsigned
              w_ld va wval (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj
              Hpins2
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UvLoadObl.

Section WpUmodeLoad.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* THE LOAD LEAF.                                                        *)
  (*                                                                       *)
  (* Width- and signedness-generic: [k] is any [uload_width] (1/2/4/8) and *)
  (* [is_unsigned] any bool, so [lb/lbu/lh/lhu/lw/lwu/ld] and every        *)
  (* compressed load are ONE lemma.  It takes the same [uinstr] /          *)
  (* [uv_redirect] pair the funnel does, so a compressed load names its    *)
  (* [ExecuteAs] expansion -- and, exactly as the ported funnel does, the  *)
  (* WRAPPER's [goodmb] certificate beside it; the LOAD's own certificate  *)
  (* is produced here from the catalogue.  The loaded value is the image   *)
  (* word, so the image comes back UNCHANGED and the register file gains   *)
  (* exactly [<[rd := wval]>].                                            *)
  (*                                                                       *)
  (* [uint rd <> 0] is a PREMISE: [uinstr] only says what the word decodes *)
  (* to, and a load into x0 is a legal (value-discarding) encoding the     *)
  (* funnel's write layer does not describe.                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_load_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (w_ld va wval : mword 64) :
    uload_width k ->
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
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
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ M
           (<[Regidx rd := regval_into_reg wval]> m) -∗
         pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hl Hchk Hcanon Hpg Hal HMb Hwval.
    destruct Hui as [Hal2 Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_step C pt _ Ψ M m pc with "Hcg Hpc [] Hcont").
    rewrite /uv_step_obl.
    iIntros (R CIDo t rs1s rsA usatp pcfg paddr)
      "%Hpre #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes M (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt M t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uv_load_obl_rvc C pt R Ψ M m pc h i o k imm rs1 rd is_unsigned
                  w_ld va wval t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr
                  Htlbok' Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hrd Hva Hwval
                  Hl Hchk Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_rvc_2 pt M t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_load_obl_rvc C pt R Ψ M m pc h i o k imm rs1 rd is_unsigned
                  w_ld va wval t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr
                  Htlbok' Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hrd Hva Hwval
                  Hl Hchk Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uv_load_obl_base C pt R Ψ M m pc w i o k imm rs1 rd is_unsigned
                  w_ld va wval t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr
                  Htlbok' Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hrd Hva Hwval
                  Hl Hchk Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_base_2 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_load_obl_base C pt R Ψ M m pc w i o k imm rs1 rd is_unsigned
                  w_ld va wval t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr
                  Htlbok' Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hrd Hva Hwval
                  Hl Hchk Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every instance takes *)
  Lemma wp_uv_load (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (w_ld va wval : mword 64) :
    uload_width k ->
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
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
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hl Hchk Hcanon Hpg Hal HMb Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load_later Ψ M m pc is_rvc i o imm rs1 rd is_unsigned k
              w_ld va wval Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hl Hchk Hcanon
              Hpg Hal HMb Hwval with "Hcg Hpc [Hcont]").
    iNext. iExact "Hcont".
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
              uload_width_8 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
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
              (fun s mb => goodmb_execute_C_LDSP_U Du_r Du_w uimm (Regidx rd) s mb)
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
              uload_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon (uinpage_1 va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              ltac:(rewrite (uM_word_byte_val M (uint va) bb Hbb); exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lw rd, imm(rs1) -- the base 4-byte SIGNED load, the tier's first     *)
  (* narrow load whose extension is REAL.  The image premise is the byte  *)
  (* WINDOW [uM_bytes M (uint va) 4 wv]: it carries both of               *)
  (* [wp_uv_load]'s image premises at once (existence via                 *)
  (* [uM_bytes_exists], value via [uM_word_w4]), so a call site states the *)
  (* four bytes ONCE.  [wv] is the loaded halfword-pair as a [mword 32];  *)
  (* [sext32_moi] turns [wval] into the call site's [mword_of_int].       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_lw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5)
      (w_ld va wval : mword 64) (wv : mword 32) :
    uinstr pt M pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = sign_extend' 64 wv ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hl Hchk Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) None
              imm rs1 rd false 4 w_ld va wval
              uload_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_s M (uint va) wv Hbw); exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lwu rd, imm(rs1) -- the same load, UNSIGNED: the only difference is  *)
  (* the flag [wp_uv_load] already carries, and [zext32_moi] on the way   *)
  (* back out.                                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_lwu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5)
      (w_ld va wval : mword 64) (wv : mword 32) :
    uinstr pt M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = zero_extend' 64 wv ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hl Hchk Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc false
              (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) None
              imm rs1 rd true 4 w_ld va wval
              uload_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_u M (uint va) wv Hbw); exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.lw rd', uimm(rs1') -- the compressed 4-byte SIGNED load off a      *)
  (* general register (NOT sp; that is c.lwsp).  Its [ExecuteAs]          *)
  (* expansion is [LOAD (zext(uimm ++ 00), rs1', rd', false, 4)]          *)
  (* ([exec_execute_C_LW_leaf]), and because the encoding names 3-bit     *)
  (* register fields the EXPANDED indices are parameters with             *)
  (* [creg2reg_idx] premises -- exactly as [wp_uv_caddi4spn] takes them.  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_clw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (crs1 crd : mword 3)
      (rs1 rd : mword 5) (w_ld va wval : mword 64) (wv : mword 32) :
    uinstr pt M pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = sign_extend' 64 wv ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcrd Hrd Hva Hl Hchk Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc true (C_LW (uimm, Cregidx crs1, Cregidx crd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                           Regidx rs1, Regidx rd, false, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rd false 4 w_ld va wval
              uload_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_LW_leaf uimm (Cregidx crs1) (Cregidx crd)
                             _ rs1 rd s eq_refl Hcr1 Hcrd))
              (fun s mb => goodmb_execute_C_LW_U Du_r Du_w uimm (Cregidx crs1)
                             (Cregidx crd) s mb)
              eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_s M (uint va) wv Hbw); exact Hwval)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ld rd', uimm(rs1') -- the compressed 8-byte load off a general     *)
  (* register.  NOT [wp_uv_cldsp]: that is the sp-relative C_LDSP, a      *)
  (* different instruction with a different immediate scaling and full    *)
  (* 5-bit register fields.  At k = 8 the extension is the identity       *)
  (* ([extend_value_w8]), so the register gets the image doubleword.      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cld (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (crs1 crd : mword 3)
      (rs1 rd : mword 5) (w_ld va wval : mword 64) :
    uinstr pt M pc true (C_LD (uimm, Cregidx crs1, Cregidx crd)) ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    uM_bytes M (uint va) 8 wval ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcrd Hrd Hva Hl Hchk Hcanon Hpg Hal Hbw.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_load Ψ M m pc true (C_LD (uimm, Cregidx crs1, Cregidx crd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           Regidx rs1, Regidx rd, false, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              rs1 rd false 8 w_ld va wval
              uload_width_8 Hui
              ltac:(intro s;
                    exact (exec_execute_C_LD_leaf uimm (Cregidx crs1) (Cregidx crd)
                             _ rs1 rd s eq_refl Hcr1 Hcrd))
              (fun s mb => goodmb_execute_C_LD_U Du_r Du_w uimm (Cregidx crs1)
                             (Cregidx crd) s mb)
              eq_refl eq_refl Hrd
              Hva Hl Hchk Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 8 wval Hbw)
              ltac:(rewrite extend_value_w8;
                    symmetry; exact (uM_word_w8 M (uint va) wval Hbw))
              with "Hcg Hpc Hcont").
  Qed.

End WpUmodeLoad.
