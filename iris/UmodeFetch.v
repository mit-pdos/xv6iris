(* UmodeFetch.v -- the CONCRETE-byte instruction fetch of the VERIFIED
   user-mode tier (see claude-notes/projects/user-verified.md).

   The safety tier's fetch composer (UserFetchPt.v) sources the fetched
   word from [udata_own] -- pages whose contents are EXISTENTIAL -- and
   therefore hands out an EXISTENTIAL word.  A verified program's fetch
   must hand out the word the program's IMAGE says is there, so this file
   is the same composition over [umem pt M] (UmodeMem.v): every byte of
   the window is a KNOWN [M] entry sitting at [uva_pa pt va ↦ₚ b], and the
   [exec (fetch tt) σ] fact names the concrete instruction word.

   One lemma per fetch geometry (RiscvFetchExec's dispatch):

     [umode_fetch_base_4]  4-aligned pc, non-compressed  -> [F_Base w]
     [umode_fetch_rvc_4]   4-aligned pc, compressed      -> [F_RVC h]
                           (the fetch still READS 4 bytes: the two bytes
                            after the halfword must be present in [M],
                            which is [uinstr]'s extra [ui_code] conjunct)
     [umode_fetch_rvc_2]   2-mod-4 pc, compressed        -> [F_RVC h]
     [umode_fetch_base_2]  2-mod-4 pc, non-compressed    -> [F_Base w]
                           (the split 2+2 fetch)

   All four take the pure translation facts in [uinstr] shape (the pc's
   vpn mapped with a fetch-permitting leaf, [uva_canon], and the
   whole-window-on-one-page bound [Z.rem (uint pc) 4096 <= 4092]) and the
   standard U-mode state pins, and hand back the moved state with
   [utlb_inv_pt] and [umem] intact -- exactly as UserFetchPt does.

   Layout: §1 pure va/window arithmetic (the [uinstr]-premise bridges);
   §2 the concrete byte window out of [umem]; §3 the four composers.     *)
From Stdlib Require Import ZArith Bool Lia Znumtheory.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import CommonWalk.
Require Import SmodeCore.
Require Import KptPt.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import UserMem.
Require Import UserFetch.
Require Import InstrBytes.
Require Import UmodeMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Pure window arithmetic.                                            *)
(*                                                                        *)
(* Everything here is about ONE 4-byte fetch window that does not cross a *)
(* page boundary.  [uinstr] states that as [Z.rem (uint pc) 4096 <= 4092];*)
(* the working form throughout is the no-carry bound                      *)
(* [bv_unsigned pc mod 4096 + d < 4096].  All the real arithmetic is done *)
(* in [mword]-FREE lemmas over plain [Z] (the bitvector zify hook makes   *)
(* [lia] unreliable on goals mentioning [bv_unsigned] -- durable-notes).  *)
(* ===================================================================== *)

(* adding a within-page offset does not disturb any bit above the page
   offset, at ANY modulus that the page size divides *)
Lemma z_mod_add_nocarry (x d m : Z) :
  0 <= x -> 0 <= d -> 0 < m -> (4096 | m) -> x mod 4096 + d < 4096 ->
  (x + d) mod m = x mod m + d.
Proof.
  intros Hx Hd Hm Hdvd Hnc.
  destruct Hdvd as [t Ht].
  assert (Htpos : 0 < t) by nia.
  pose proof (Z.mod_pos_bound x m Hm) as [Hs0 Hsm].
  assert (Hs4 : (x mod m) mod 4096 = x mod 4096).
  { symmetry. apply Znumtheory.Zmod_div_mod; [ lia | lia | exists t; lia ]. }
  pose proof (Z_div_mod_eq_full (x mod m) 4096) as Hdm.
  pose proof (Z.mod_pos_bound (x mod m) 4096 ltac:(lia)) as Hmb.
  assert (Hq : (x mod m) / 4096 < t) by nia.
  rewrite <- (Z.add_mod_idemp_l x d m ltac:(lia)).
  apply Z.mod_small. nia.
Qed.

(* a within-page add never wraps the 64-bit address space *)
Lemma z_win_nowrap (V d : Z) :
  0 <= V < 18446744073709551616 -> 0 <= d -> V mod 4096 + d < 4096 ->
  V + d < 18446744073709551616.
Proof.
  intros Hv Hd Hnc.
  pose proof (Z_div_mod_eq_full V 4096) as Hdm.
  pose proof (Z.mod_pos_bound V 4096 ltac:(lia)) as Hmb.
  assert (Hq : V / 4096 < 4503599627370496) by nia.
  nia.
Qed.

(* ... hence the page number (the shifted-out low 12 bits) is stable *)
Lemma z_shiftr12_add (R d : Z) :
  0 <= R -> 0 <= d -> R mod 4096 + d < 4096 ->
  Z.shiftr (R + d) 12 = Z.shiftr R 12.
Proof.
  intros HR Hd Hnc.
  rewrite (Z.shiftr_div_pow2 (R + d) 12 ltac:(lia)) (Z.shiftr_div_pow2 R 12 ltac:(lia)).
  change (2 ^ 12) with 4096.
  pose proof (Z_div_mod_eq_full R 4096) as Hdm.
  pose proof (Z.mod_pos_bound R 4096 ltac:(lia)) as Hmb.
  replace (R + d) with ((R / 4096) * 4096 + (R mod 4096 + d)) by lia.
  rewrite (Z.div_add_l (R / 4096) 4096 (R mod 4096 + d) ltac:(lia)).
  rewrite (Z.div_small (R mod 4096 + d) 4096 ltac:(lia)). lia.
Qed.

(* ALIGNMENT ALONE BOUNDS THE WINDOW, which is why three of the four fetch
   geometries need no in-page premise at all: a k-aligned pc has a page
   offset that is a multiple of k, hence at most 4096 - k, so a k-byte
   window starting there cannot leave the page.  At k = 4 that covers the
   two 4-ALIGNED reads and at k = 2 the compressed 2-mod-4 one.

   The remaining geometry -- a NON-compressed instruction at a 2-mod-4 pc,
   read as 2 + 2 -- is the one that genuinely CAN straddle a page boundary
   (its low half sits at page offset 4094), and the way to support it is to
   give the second halfword its own leaf rather than to forbid the case with
   an in-page premise. *)
Lemma ualign_page_off (pc : mword 64) (k : Z) :
  0 < k -> (k | 4096) -> is_aligned_vaddr (Virtaddr pc) k = true ->
  (bv_unsigned pc mod 4096) mod k = 0.
Proof.
  intros Hk Hdvd Hal.
  unfold is_aligned_vaddr in Hal. apply Z.eqb_eq in Hal.
  rewrite uint_unsigned in Hal.
  rewrite Z.rem_mod_nonneg in Hal;
    [ | exact (proj1 (bv_unsigned_in_range _ pc)) | lia ].
  rewrite <- (Znumtheory.Zmod_div_mod k 4096 (bv_unsigned pc) Hk ltac:(lia) Hdvd).
  exact Hal.
Qed.

Lemma ualign4_nc (pc : mword 64) (d : Z) :
  is_aligned_vaddr (Virtaddr pc) 4 = true -> 0 <= d <= 3 ->
  bv_unsigned pc mod 4096 + d < 4096.
Proof.
  intros Hal Hd.
  pose proof (ualign_page_off pc 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal) as Hm.
  pose proof (Z.mod_pos_bound (bv_unsigned pc) 4096 ltac:(lia)) as Hb.
  (* [lia] cannot see through the NESTED mod, so hand it the multiple *)
  apply Z.mod_divide in Hm; [ | lia ]. destruct Hm as [q Hq]. lia.
Qed.

Lemma ualign2_nc (pc : mword 64) (d : Z) :
  is_aligned_vaddr (Virtaddr pc) 2 = true -> 0 <= d <= 1 ->
  bv_unsigned pc mod 4096 + d < 4096.
Proof.
  intros Hal Hd.
  pose proof (ualign_page_off pc 2 ltac:(lia) ltac:(exists 2048; reflexivity) Hal) as Hm.
  pose proof (Z.mod_pos_bound (bv_unsigned pc) 4096 ltac:(lia)) as Hb.
  apply Z.mod_divide in Hm; [ | lia ]. destruct Hm as [q Hq]. lia.
Qed.

(* the [uinstr] in-page premise, in the working no-carry form *)
Lemma uinpage_nc (pc : mword 64) (d : Z) :
  Z.rem (uint pc) 4096 <= 4092 -> 0 <= d <= 3 ->
  bv_unsigned pc mod 4096 + d < 4096.
Proof.
  intros Hpg Hd.
  rewrite uint_unsigned in Hpg.
  rewrite Z.rem_mod_nonneg in Hpg;
    [ | exact (proj1 (bv_unsigned_in_range _ pc)) | lia ].
  lia.
Qed.

(* [mword_of_int] of the image key IS the model's address arithmetic *)
Lemma moi_win (pc : mword 64) (d : Z) :
  0 <= d -> bv_unsigned pc mod 4096 + d < 4096 ->
  (mword_of_int (uint pc + d) : mword 64) = add_vec_int pc d.
Proof.
  intros Hd Hnc.
  pose proof (bv_unsigned_in_range _ pc) as Hr.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64 in Hr.
  pose proof (z_win_nowrap (bv_unsigned pc) d Hr Hd Hnc) as Hnw.
  apply bv_eq.
  rewrite moi64_unsigned.
  rewrite (uint_add_vec_int_small pc d Hd Hnw).
  rewrite uint_unsigned.
  apply bvw64_small.
  assert (E : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

(* the vpn is stable across the window *)
Lemma usvpn_window (pc : mword 64) (d : Z) :
  0 <= d -> bv_unsigned pc mod 4096 + d < 4096 ->
  svpn_of (add_vec_int pc d) = svpn_of pc.
Proof.
  intros Hd Hnc.
  pose proof (bv_unsigned_in_range _ pc) as Hr.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64 in Hr.
  pose proof (z_win_nowrap (bv_unsigned pc) d Hr Hd Hnc) as Hnw.
  pose proof (uint_add_vec_int_small pc d Hd Hnw) as Hav.
  apply bv_eq.
  rewrite !svpn_of_extract.
  cbn [bits_of_virtaddr].
  rewrite (subrange_dec_unsigned_lo0 (add_vec_int pc d) (Z.sub 39 1) 549755813888
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (subrange_dec_unsigned_lo0 pc (Z.sub 39 1) 549755813888
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite Hav.
  rewrite (z_mod_add_nocarry (bv_unsigned pc) d 549755813888
             ltac:(lia) Hd ltac:(lia) ltac:(exists 134217728; reflexivity) Hnc).
  apply z_shiftr12_add;
    [ apply Z.mod_pos_bound; lia | exact Hd | ].
  rewrite <- (Znumtheory.Zmod_div_mod 4096 549755813888 (bv_unsigned pc)
                ltac:(lia) ltac:(lia) ltac:(exists 134217728; reflexivity)).
  exact Hnc.
Qed.

(* the page-window lemma at the [uinstr] premise (UserMem's
   [u_walk_pa_window] wants 4-ALIGNMENT; the window bound is what the
   proof actually uses, and the 2-mod-4 geometries have no 4-alignment) *)
Lemma u_walk_pa_window_gen (pte0 pc : mword 64) (j : nat) :
  bv_unsigned pc mod 4096 + Z.of_nat j < 4096 ->
  pa_add (u_walk_pa pte0 pc) j = u_walk_pa pte0 (add_vec_int pc (Z.of_nat j)).
Proof.
  intro Hnc.
  assert (Hp : uint (subrange_vec_dec pc 11 0) + Z.of_nat j < 4096).
  { rewrite uint_subrange11. rewrite uint_unsigned. exact Hnc. }
  exact (pa_window _ pc j Hp).
Qed.

(* THE reduction of [umem]'s address function on the fetch window: the
   image byte at user va [uint pc + j] is owned at the j-th physical byte
   of the pc's translated page. *)
Lemma uva_pa_window (pt : uptd) (w_leaf pc : mword 64) (j : nat) :
  ud_um pt !! svpn_of pc = Some w_leaf ->
  bv_unsigned pc mod 4096 + Z.of_nat j < 4096 ->
  uva_pa pt (uint pc + Z.of_nat j) = pa_add (u_walk_pa w_leaf pc) j.
Proof.
  intros Hl Hnc.
  pose proof (Nat2Z.is_nonneg j) as Hj0.
  unfold uva_pa.
  rewrite (moi_win pc (Z.of_nat j) Hj0 Hnc).
  rewrite (usvpn_window pc (Z.of_nat j) Hj0 Hnc).
  rewrite Hl.
  symmetry. exact (u_walk_pa_window_gen w_leaf pc j Hnc).
Qed.

(* ---- canonicality is stable across the window --------------------- *)

Lemma se39_unsigned (a : mword 64) :
  bv_unsigned (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0))
  = bv_wrap 64 (bv_swrap 39 (bv_unsigned a mod 549755813888)).
Proof.
  cbn [bits_of_virtaddr].
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite (subrange_dec_unsigned_lo0 a (Z.sub 39 1) 549755813888
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  reflexivity.
Qed.

Lemma uva_canon_eq (a : mword 64) :
  uva_canon a <->
  a = sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0).
Proof.
  unfold uva_canon, neq_vec.
  rewrite negb_false_iff. rewrite eq_vec_true_iff.
  cbn [bits_of_virtaddr]. reflexivity.
Qed.

Lemma uva_canon_unsigned (a : mword 64) :
  uva_canon a <->
  bv_unsigned a = bv_wrap 64 (bv_swrap 39 (bv_unsigned a mod 549755813888)).
Proof.
  split.
  - intro H. apply uva_canon_eq in H.
    apply (f_equal bv_unsigned) in H.
    rewrite se39_unsigned in H. exact H.
  - intro H. apply uva_canon_eq.
    apply bv_eq. rewrite se39_unsigned. exact H.
Qed.

Lemma z_canon_add (V d : Z) :
  0 <= V < 18446744073709551616 -> 0 <= d -> V mod 4096 + d < 4096 ->
  V = bv_wrap 64 (bv_swrap 39 (V mod 549755813888)) ->
  V + d = bv_wrap 64 (bv_swrap 39 ((V + d) mod 549755813888)).
Proof.
  intros Hv Hd Hnc Hc.
  assert (Hdvd : (4096 | 549755813888)) by (exists 134217728; reflexivity).
  rewrite (z_mod_add_nocarry V d 549755813888 ltac:(lia) Hd ltac:(lia) Hdvd Hnc).
  pose proof (Z.mod_pos_bound V 549755813888 ltac:(lia)) as HR.
  assert (HR4 : (V mod 549755813888) mod 4096 = V mod 4096).
  { symmetry.
    apply (Znumtheory.Zmod_div_mod 4096 549755813888 V ltac:(lia) ltac:(lia) Hdvd). }
  assert (Hhm : (V mod 549755813888 + 274877906944) mod 4096
                = V mod 549755813888 mod 4096).
  { rewrite Zplus_mod.
    replace (274877906944 mod 4096) with 0 by reflexivity.
    rewrite Z.add_0_r. rewrite Zmod_mod. reflexivity. }
  assert (Hsw : bv_swrap 39 (V mod 549755813888 + d)
                = bv_swrap 39 (V mod 549755813888) + d).
  { unfold bv_swrap, bv_wrap.
    assert (Ehm : bv_half_modulus 39 = 274877906944) by (vm_compute; reflexivity).
    assert (Em : bv_modulus 39 = 549755813888) by (vm_compute; reflexivity).
    rewrite Ehm Em.
    replace (V mod 549755813888 + d + 274877906944)
      with ((V mod 549755813888 + 274877906944) + d) by lia.
    rewrite (z_mod_add_nocarry (V mod 549755813888 + 274877906944) d 549755813888
               ltac:(lia) Hd ltac:(lia) Hdvd ltac:(lia)).
    lia. }
  rewrite Hsw.
  unfold bv_wrap in Hc |- *.
  assert (Em64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Em64 in Hc |- *.
  rewrite <- (Z.add_mod_idemp_l (bv_swrap 39 (V mod 549755813888)) d
                18446744073709551616 ltac:(lia)).
  rewrite <- Hc.
  symmetry. apply Z.mod_small.
  pose proof (z_win_nowrap V d Hv Hd Hnc). lia.
Qed.

Lemma uva_canon_add (pc : mword 64) (d : Z) :
  uva_canon pc -> 0 <= d -> bv_unsigned pc mod 4096 + d < 4096 ->
  uva_canon (add_vec_int pc d).
Proof.
  intros Hc Hd Hnc.
  apply uva_canon_unsigned in Hc.
  apply uva_canon_unsigned.
  pose proof (bv_unsigned_in_range _ pc) as Hr.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64 in Hr.
  pose proof (z_win_nowrap (bv_unsigned pc) d Hr Hd Hnc) as Hnw.
  rewrite (uint_add_vec_int_small pc d Hd Hnw).
  exact (z_canon_add (bv_unsigned pc) d Hr Hd Hnc Hc).
Qed.

(* 2-alignment is stable across the window (the split fetch needs it at
   pc+2) *)
Lemma ualign2_plus2 (pc : mword 64) :
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true.
Proof.
  intro H2.
  pose proof (align2_plus2 pc H2) as H.
  rewrite fetch_pa_id in H. exact H.
Qed.

(* the window shifted to pc+d (the split fetch's second halfword reads at
   pc+2, and every fact it needs is the same fact at the shifted base) *)
Lemma uwin_shift (pc : mword 64) (d : Z) :
  Z.rem (uint pc) 4096 <= 4092 -> 0 <= d <= 3 ->
  uint (add_vec_int pc d) = uint pc + d /\
  bv_unsigned (add_vec_int pc d) mod 4096 = bv_unsigned pc mod 4096 + d.
Proof.
  intros Hpg Hd.
  pose proof (uinpage_nc pc d Hpg Hd) as Hnc.
  pose proof (bv_unsigned_in_range _ pc) as Hr.
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite E64 in Hr.
  pose proof (z_win_nowrap (bv_unsigned pc) d Hr ltac:(lia) Hnc) as Hnw.
  pose proof (uint_add_vec_int_small pc d ltac:(lia) Hnw) as Hav.
  split.
  - rewrite !uint_unsigned. exact Hav.
  - rewrite Hav.
    exact (z_mod_add_nocarry (bv_unsigned pc) d 4096 ltac:(lia) ltac:(lia)
             ltac:(lia) ltac:(exists 1; reflexivity) Hnc).
Qed.

(* ===================================================================== *)
(* §2 Little-endian byte assembly at the two fetch widths.                *)
(*                                                                        *)
(* The 4-aligned COMPRESSED fetch reads four bytes but only the low two   *)
(* are the instruction, so the word it produces has to be built from the  *)
(* halfword's bytes plus the two following image bytes; these are the     *)
(* pure facts that identify its low half.                                 *)
(* ===================================================================== *)

Lemma z_asm16 (H : Z) :
  0 <= H < 65536 ->
  (H mod 256 + 256 * ((H / 256) mod 256 + 256 * 0)) mod 65536 = H.
Proof.
  intro Hb.
  pose proof (Z_div_mod_eq_full H 256) as Hdm.
  pose proof (Z.mod_pos_bound H 256 ltac:(lia)) as Hmb.
  assert (Hd0 : 0 <= H / 256) by (apply Z.div_pos; lia).
  assert (Hd : H / 256 < 256) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (H / 256) 256 ltac:(lia)).
  rewrite (Z.mod_small (H mod 256 + 256 * (H / 256 + 256 * 0)) 65536 ltac:(lia)).
  lia.
Qed.

Lemma z_asm_lo16 (c0 c1 c2 c3 : Z) :
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  ((c0 + 256 * (c1 + 256 * (c2 + 256 * (c3 + 256 * 0)))) mod 4294967296) mod 65536
  = (c0 + 256 * (c1 + 256 * 0)) mod 65536.
Proof.
  intros H0 H1 H2 H3.
  rewrite (Z.mod_small (c0 + 256 * (c1 + 256 * (c2 + 256 * (c3 + 256 * 0))))
             4294967296 ltac:(lia)).
  replace (c0 + 256 * (c1 + 256 * (c2 + 256 * (c3 + 256 * 0))))
    with ((c0 + 256 * c1) + (c2 + 256 * c3) * 65536) by lia.
  rewrite (Z.mod_add (c0 + 256 * c1) (c2 + 256 * c3) 65536 ltac:(lia)).
  f_equal. lia.
Qed.

(* a 16-bit word IS the little-endian assembly of its own two bytes *)
Lemma bv16_of_bytes (h : mword 16) :
  (Z_to_bv 16 (assemble_bytes [nth_byte h 0; nth_byte h 1]) : mword 16) = h.
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  cbn [assemble_bytes].
  rewrite !nth_byte_unsigned.
  change (Z.of_N (8 * N.of_nat 0)) with 0.
  change (Z.of_N (8 * N.of_nat 1)) with 8.
  rewrite Z.shiftr_0_r.
  rewrite (Z.shiftr_div_pow2 (bv_unsigned h) 8 ltac:(lia)).
  change (2 ^ 8) with 256.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 16) with 65536.
  apply z_asm16.
  pose proof (bv_unsigned_in_range _ h) as Hr.
  assert (bv_modulus 16 = 65536) as E by (vm_compute; reflexivity).
  rewrite E in Hr. exact Hr.
Qed.

(* the low halfword of a 4-byte assembly is the assembly of its low two
   bytes *)
Lemma subrange16_assemble4 (b0 b1 b2 b3 : bv 8) :
  subrange_vec_dec (Z_to_bv 32 (assemble_bytes [b0; b1; b2; b3]) : mword 32) 15 0
  = (Z_to_bv 16 (assemble_bytes [b0; b1]) : mword 16).
Proof.
  apply bv_eq.
  rewrite (subrange_dec_unsigned_lo0
             (Z_to_bv 32 (assemble_bytes [b0; b1; b2; b3]) : mword 32) 15 65536
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite !Z_to_bv_unsigned.
  cbn [assemble_bytes].
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296.
  change (2 ^ Z.of_N 16) with 65536.
  change (2 ^ 8) with 256.
  pose proof (bv_unsigned_in_range 8 b0) as R0.
  pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2.
  pose proof (bv_unsigned_in_range 8 b3) as R3.
  assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E8 in R0, R1, R2, R3.
  exact (z_asm_lo16 _ _ _ _ R0 R1 R2 R3).
Qed.

(* ===================================================================== *)
(* §3b The word a COMPRESSED instruction at a 4-ALIGNED pc is fetched as: *)
(*     the fetch unit reads FOUR bytes, so the word carries the two bytes *)
(*     that follow the halfword ([uinstr]'s extra [ui_code] conjunct).    *)
(*     Only its LOW half matters, and that is the halfword.               *)
(* ===================================================================== *)

Definition urvc4_word (h : mword 16) (b2 b3 : bv 8) : mword 32 :=
  Z_to_bv 32 (assemble_bytes [nth_byte h 0; nth_byte h 1; b2; b3]).

Lemma urvc4_byte (h : mword 16) (b2 b3 : bv 8) (j : nat) :
  (j < 4)%nat ->
  nth_byte (urvc4_word h b2 b3) j = [nth_byte h 0; nth_byte h 1; b2; b3] !!! j.
Proof.
  intro Hj. unfold urvc4_word.
  apply nth_byte_assemble4; [ reflexivity | exact Hj ].
Qed.

Lemma urvc4_low (h : mword 16) (b2 b3 : bv 8) :
  subrange_vec_dec (urvc4_word h b2 b3) 15 0 = h.
Proof.
  unfold urvc4_word.
  rewrite subrange16_assemble4. apply bv16_of_bytes.
Qed.

(* ===================================================================== *)
(* THE FETCH COMPOSERS ARE GONE (2026-08-29).                             *)
(*                                                                        *)
(* This file used to end with four whole-fetch composers -- [base_4],     *)
(* [rvc_4], [rvc_2], [base_2] -- plus the physical read lemmas and the    *)
(* byte-assembly arithmetic they needed.  NOTHING OUTSIDE THIS FILE EVER  *)
(* CALLED THEM: the live fetch path is WpUmodeStep.v's [uv_fetch_4] /     *)
(* [uv_fetch_rvc_2] / [uv_fetch_base_2], a parallel set built on          *)
(* [uv_walk_fetch], which UkStep.v, UkStore.v, UkLoad.v and UkBranch.v    *)
(* are the consumers of.  Keeping a second copy meant every change to the *)
(* fetch -- starting with page-crossing support -- would have had to be   *)
(* made twice, once in code no one runs.                                  *)
(*                                                                        *)
(* What survives is what the live path actually imports: §1's window and  *)
(* canonicity arithmetic (including the new alignment bounds), the        *)
(* [u_walk_pa] window lemmas, and §3b's [urvc4_*] view of a compressed    *)
(* instruction fetched as a 4-byte read.                                  *)
(* ===================================================================== *)
