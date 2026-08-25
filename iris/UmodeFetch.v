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
(* §2b The physical fetch reads, at the two widths, from CONCRETE bytes.  *)
(*     (The [udata_*] versions in UserFetchPt.v conjure the word from the *)
(*     existential page contents; here the caller already knows it.)      *)
(* ===================================================================== *)

Lemma umode_mem_read_fetch_4 (pa : mword 64) (iw : mword 32) (σ' : mstate) :
  (forall j : nat, (N.of_nat j < 4)%N ->
     σ'.(mem) !! pa_add pa j = Some (nth_byte iw j)) ->
  addr_is_ram pa -> addr_is_ram (pa_add pa 3) ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ->
  register_lookup cur_privilege σ'.(sregs) = User ->
  register_lookup htif_tohost_base σ'.(sregs) = None ->
  pma_allows_all (register_lookup pma_regions σ'.(sregs)) ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false) σ'
    = Some (Ok iw, σ').
Proof.
  intros Hbytes Hram0 Hram3 Halp HA Hord HX Hcovp Lpriv Lhtif Hall.
  destruct (pma_all_ram Hall pa 4
             (pma_access_ram _ _ _ Hram0 Hram3 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hpmam & Hexec & _).
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
            (uint pa) (uint (to_bits 64 4)) = PMP_Match).
  { exact (ram_fetch_pmp pa _ 4 3 ltac:(lia) ltac:(lia)
             ltac:(vm_compute; reflexivity) ltac:(reflexivity)
             Hram0 Hram3 Hcovp). }
  exact (exec_mem_read_fetch_4_U PBMT_PMA pa region iw σ'
           HA Hord Hrange HX Hpmam Halp Hexec
           (within_clint_false pa 4 σ' Hnc ltac:(lia))
           (within_sig_false pa 4 σ' Hns ltac:(lia))
           (within_htif_false pa 4 σ' Lhtif)
           (addr_is_ram_not_dev _ Hram0)
           Hbytes Lpriv).
Qed.

Lemma umode_mem_read_fetch_2 (pa : mword 64) (ih : mword 16) (σ' : mstate) :
  (forall j : nat, (N.of_nat j < 2)%N ->
     σ'.(mem) !! pa_add pa j = Some (nth_byte ih j)) ->
  addr_is_ram pa -> addr_is_ram (pa_add pa 1) ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z ->
  register_lookup cur_privilege σ'.(sregs) = User ->
  register_lookup htif_tohost_base σ'.(sregs) = None ->
  pma_allows_all (register_lookup pma_regions σ'.(sregs)) ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false) σ'
    = Some (Ok ih, σ').
Proof.
  intros Hbytes Hram0 Hram1 Halp HA Hord HX Hcovp Lpriv Lhtif Hall.
  destruct (pma_all_ram Hall pa 2
             (pma_access_ram _ _ _ Hram0 Hram1 (pma_width_ok 2 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hpmam & Hexec & _).
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
            (uint pa) (uint (to_bits 64 2)) = PMP_Match).
  { exact (ram_fetch_pmp pa _ 2 1 ltac:(lia) ltac:(lia)
             ltac:(vm_compute; reflexivity) ltac:(reflexivity)
             Hram0 Hram1 Hcovp). }
  exact (exec_mem_read_fetch_2_U PBMT_PMA pa region ih σ'
           HA Hord Hrange HX Hpmam Halp Hexec
           (within_clint_false pa 2 σ' Hnc ltac:(lia))
           (within_sig_false pa 2 σ' Hns ltac:(lia))
           (within_htif_false pa 2 σ' Lhtif)
           (addr_is_ram_not_dev _ Hram0)
           Hbytes Lpriv).
Qed.

(* ===================================================================== *)
(* §2c One image byte, borrowed out of [umem].                            *)
(* ===================================================================== *)

Section UmodeFetchWord.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma umem_fetch_byte (pt : uptd) (M : gmap Z (bv 8)) (w_leaf pc : mword 64)
      (j : nat) (b : bv 8) (σ' : mstate) :
    ud_um pt !! svpn_of pc = Some w_leaf ->
    bv_unsigned pc mod 4096 + Z.of_nat j < 4096 ->
    M !! (uint pc + Z.of_nat j) = Some b ->
    gen_heap_interp σ'.(mem) -∗ umem pt M -∗
    ⌜σ'.(mem) !! pa_add (u_walk_pa w_leaf pc) j = Some b /\
     addr_is_ram (pa_add (u_walk_pa w_leaf pc) j)⌝.
  Proof.
    iIntros (Hl Hnc HM) "Hmem HM".
    iDestruct (umem_lookup_acc pt M (uint pc + Z.of_nat j) b HM with "HM")
      as "[Hb Hback]".
    iDestruct (phys_valid with "Hmem Hb") as %Hv.
    iDestruct (phys_ram with "Hb") as %Hr.
    iPureIntro.
    rewrite <- (uva_pa_window pt w_leaf pc j Hl Hnc).
    exact (conj Hv Hr).
  Qed.

End UmodeFetchWord.

(* ===================================================================== *)
(* §3 THE FOUR FETCH COMPOSERS.                                           *)
(*                                                                        *)
(* Same premise list as UserFetchPt's composers (state pins + the         *)
(* translate facts), with the [udata_own]/[udata_cov] pair replaced by     *)
(* [umem pt M] and the concrete [uM_bytes] window; the fetched value is    *)
(* the one the image determines, not an existential.                       *)
(* ===================================================================== *)

Section UmodeFetchOk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* (a) a 4-ALIGNED pc holding a NON-compressed instruction: one 4-byte
     read, result [F_Base iw]. *)
  Lemma umode_fetch_base_4 (pt : uptd) (M : gmap Z (bv 8))
      (w_leaf pc : mword 64) (iw : mword 32) (σ : mstate) :
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    Z.rem (uint pc) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uM_bytes M (uint pc) 4 iw ->
    isRVC (subrange_vec_dec iw 15 0) = false ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ σ' : mstate,
      ⌜exec (fetch tt) σ = Some (F_Base iw, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    intros Hl Hchk Hcanon Hpg Hal Hbytes HnRVC Lpc Hmisa Hmenv Hhtif Hcp HSXL Hall.
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_leaf pc (u_walk_pa w_leaf pc) σ
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    pose proof (uinpage_nc pc 3 Hpg ltac:(lia)) as Hnc3.
    assert (Hnc : forall j : nat, (j < 4)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. lia. }
    iDestruct (umem_fetch_byte pt M w_leaf pc 0 (nth_byte iw 0) σ' Hl
                 (Hnc 0%nat ltac:(lia)) (Hbytes 0%nat ltac:(lia)) with "Hgh HM")
      as %[Hm0 Hr0].
    iDestruct (umem_fetch_byte pt M w_leaf pc 1 (nth_byte iw 1) σ' Hl
                 (Hnc 1%nat ltac:(lia)) (Hbytes 1%nat ltac:(lia)) with "Hgh HM")
      as %[Hm1 Hr1].
    iDestruct (umem_fetch_byte pt M w_leaf pc 2 (nth_byte iw 2) σ' Hl
                 (Hnc 2%nat ltac:(lia)) (Hbytes 2%nat ltac:(lia)) with "Hgh HM")
      as %[Hm2 Hr2].
    iDestruct (umem_fetch_byte pt M w_leaf pc 3 (nth_byte iw 3) σ' Hl
                 (Hnc 3%nat ltac:(lia)) (Hbytes 3%nat ltac:(lia)) with "Hgh HM")
      as %[Hm3 Hr3].
    assert (Hmr : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w_leaf pc)) 4 false false false) σ'
                  = Some (Ok iw, σ')).
    { apply (umode_mem_read_fetch_4 (u_walk_pa w_leaf pc) iw σ').
      - intros j HjN. assert (Hj : (j < 4)%nat) by lia.
        destruct j as [ | [ | [ | [ | ] ] ] ]; try lia;
          [ exact Hm0 | exact Hm1 | exact Hm2 | exact Hm3 ].
      - rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). exact Hr0.
      - exact Hr3.
      - exact (pa4_aligned _ pc Hal).
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord.
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif.
      - rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall. }
    iModIntro. iExists σ'.
    iSplit; [ iPureIntro | ].
    { pose proof (exec_fetch_ok_4 σ σ' pc (u_walk_pa w_leaf pc) iw Lpc Hal Htr Hmr) as Hf.
      rewrite autocast_mword_id in Hf. rewrite HnRVC in Hf. exact Hf. }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iSplit; [ iPureIntro; exact Tr | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeFetchOk.

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

Section UmodeFetchRvc4.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* (b) a 4-ALIGNED pc holding a COMPRESSED instruction: still ONE 4-byte
     read, result [F_RVC h]. *)
  Lemma umode_fetch_rvc_4 (pt : uptd) (M : gmap Z (bv 8))
      (w_leaf pc : mword 64) (h : mword 16) (b2 b3 : bv 8) (σ : mstate) :
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    Z.rem (uint pc) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uM_bytes M (uint pc) 2 h ->
    M !! (uint pc + 2) = Some b2 ->
    M !! (uint pc + 3) = Some b3 ->
    isRVC h = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ σ' : mstate,
      ⌜exec (fetch tt) σ = Some (F_RVC h, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    intros Hl Hchk Hcanon Hpg Hal Hbytes Hb2 Hb3 HisRVC
           Lpc Hmisa Hmenv Hhtif Hcp HSXL Hall.
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_leaf pc (u_walk_pa w_leaf pc) σ
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    pose proof (uinpage_nc pc 3 Hpg ltac:(lia)) as Hnc3.
    assert (Hnc : forall j : nat, (j < 4)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. lia. }
    iDestruct (umem_fetch_byte pt M w_leaf pc 0 (nth_byte h 0) σ' Hl
                 (Hnc 0%nat ltac:(lia)) (Hbytes 0%nat ltac:(lia)) with "Hgh HM")
      as %[Hm0 Hr0].
    iDestruct (umem_fetch_byte pt M w_leaf pc 1 (nth_byte h 1) σ' Hl
                 (Hnc 1%nat ltac:(lia)) (Hbytes 1%nat ltac:(lia)) with "Hgh HM")
      as %[Hm1 Hr1].
    iDestruct (umem_fetch_byte pt M w_leaf pc 2 b2 σ' Hl
                 (Hnc 2%nat ltac:(lia)) Hb2 with "Hgh HM") as %[Hm2 Hr2].
    iDestruct (umem_fetch_byte pt M w_leaf pc 3 b3 σ' Hl
                 (Hnc 3%nat ltac:(lia)) Hb3 with "Hgh HM") as %[Hm3 Hr3].
    assert (Hmr : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w_leaf pc)) 4 false false false) σ'
                  = Some (Ok (urvc4_word h b2 b3), σ')).
    { apply (umode_mem_read_fetch_4 (u_walk_pa w_leaf pc) (urvc4_word h b2 b3) σ').
      - intros j HjN. assert (Hj : (j < 4)%nat) by lia.
        rewrite (urvc4_byte h b2 b3 j Hj).
        destruct j as [ | [ | [ | [ | ] ] ] ]; try lia;
          cbn [lookup_total list_lookup_total];
          [ exact Hm0 | exact Hm1 | exact Hm2 | exact Hm3 ].
      - rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). exact Hr0.
      - exact Hr3.
      - exact (pa4_aligned _ pc Hal).
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord.
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif.
      - rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall. }
    iModIntro. iExists σ'.
    iSplit; [ iPureIntro | ].
    { pose proof (exec_fetch_ok_4 σ σ' pc (u_walk_pa w_leaf pc)
                    (urvc4_word h b2 b3) Lpc Hal Htr Hmr) as Hf.
      rewrite autocast_mword_id in Hf.
      rewrite (urvc4_low h b2 b3) in Hf. rewrite HisRVC in Hf. exact Hf. }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iSplit; [ iPureIntro; exact Tr | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeFetchRvc4.

(* ===================================================================== *)
(* §3c The 2-mod-4 geometries.  The low halfword comes off the pc's page; *)
(*     a NON-compressed instruction then needs the high halfword, which   *)
(*     translates INDEPENDENTLY at pc+2 -- and, since [uinstr] keeps the  *)
(*     whole 4-byte window on ONE page, through the SAME leaf.  So the    *)
(*     mapped/canonical facts at pc+2 are DERIVED here, not assumed.      *)
(* ===================================================================== *)

Section UmodeFetchSplit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* (c) a 2-mod-4 pc holding a COMPRESSED instruction: one 2-byte read,
     result [F_RVC h]. *)
  Lemma umode_fetch_rvc_2 (pt : uptd) (M : gmap Z (bv 8))
      (w_leaf pc : mword 64) (h : mword 16) (σ : mstate) :
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    Z.rem (uint pc) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    uM_bytes M (uint pc) 2 h ->
    isRVC h = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ σ' : mstate,
      ⌜exec (fetch tt) σ = Some (F_RVC h, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    intros Hl Hchk Hcanon Hpg Hal2 Hnal4 Hbytes HisRVC
           Lpc Hmisa Hmenv Hhtif Hcp HSXL Hall.
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_leaf pc (u_walk_pa w_leaf pc) σ
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    pose proof (uinpage_nc pc 3 Hpg ltac:(lia)) as Hnc3.
    assert (Hnc : forall j : nat, (j < 2)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. lia. }
    iDestruct (umem_fetch_byte pt M w_leaf pc 0 (nth_byte h 0) σ' Hl
                 (Hnc 0%nat ltac:(lia)) (Hbytes 0%nat ltac:(lia)) with "Hgh HM")
      as %[Hm0 Hr0].
    iDestruct (umem_fetch_byte pt M w_leaf pc 1 (nth_byte h 1) σ' Hl
                 (Hnc 1%nat ltac:(lia)) (Hbytes 1%nat ltac:(lia)) with "Hgh HM")
      as %[Hm1 Hr1].
    assert (Hmr : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w_leaf pc)) 2 false false false) σ'
                  = Some (Ok h, σ')).
    { apply (umode_mem_read_fetch_2 (u_walk_pa w_leaf pc) h σ').
      - intros j HjN. assert (Hj : (j < 2)%nat) by lia.
        destruct j as [ | [ | ] ]; try lia; [ exact Hm0 | exact Hm1 ].
      - rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). exact Hr0.
      - exact Hr1.
      - exact (pa_aligned_div _ pc 2 ltac:(lia) ltac:(exists 2048; reflexivity) Hal2).
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord.
      - rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX.
      - rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif.
      - rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall. }
    iModIntro. iExists σ'.
    iSplit; [ iPureIntro | ].
    { exact (exec_fetch_rvc_2 σ σ' pc (u_walk_pa w_leaf pc)
               Lpc HmisaC Hbit0 Hbit1 Hnal4 h Htr Hmr HisRVC). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iSplit; [ iPureIntro; exact Tr | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeFetchSplit.

Section UmodeFetchSplitBase.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* (d) a 2-mod-4 pc holding a NON-compressed instruction: the split 2+2
     fetch, result [F_Base iw].  Two absorbed translation moves, so the
     state shape is reported as the lookup-transport property (every
     non-[tlb] register unchanged), exactly as [user_pt_fetch_instr_2]. *)
  Lemma umode_fetch_base_2 (pt : uptd) (M : gmap Z (bv 8))
      (w_leaf pc : mword 64) (iw : mword 32) (σ : mstate) :
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    Z.rem (uint pc) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    uM_bytes M (uint pc) 4 iw ->
    isRVC (subrange_vec_dec iw 15 0) = false ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ σ' : mstate,
      ⌜exec (fetch tt) σ = Some (F_Base iw, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M.
  Proof.
    intros Hl Hchk Hcanon Hpg Hal2 Hnal4 Hbytes HnRVC
           Lpc Hmisa Hmenv Hhtif Hcp HSXL Hall.
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
    pose proof (uinpage_nc pc 3 Hpg ltac:(lia)) as Hnc3.
    pose proof (uinpage_nc pc 2 Hpg ltac:(lia)) as Hnc2.
    (* the SECOND halfword's va lives on the SAME page, hence the same leaf *)
    assert (Hl2 : ud_um pt !! svpn_of (add_vec_int pc 2) = Some w_leaf).
    { rewrite (usvpn_window pc 2 ltac:(lia) Hnc2). exact Hl. }
    pose proof (uva_canon_add pc 2 Hcanon ltac:(lia) Hnc2) as Hcanon2.
    destruct (uwin_shift pc 2 Hpg ltac:(lia)) as [Hu2 Hmod2].
    assert (Hncs : forall j : nat, (j < 2)%nat ->
              bv_unsigned (add_vec_int pc 2) mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. rewrite Hmod2. lia. }
    assert (Hbytes2 : forall j : nat, (j < 2)%nat ->
              M !! (uint (add_vec_int pc 2) + Z.of_nat j)
              = Some (nth_byte iw (2 + j))).
    { intros j Hj.
      pose proof (Hbytes (2 + j)%nat ltac:(lia)) as Hb.
      rewrite Nat2Z.inj_add in Hb. change (Z.of_nat 2) with 2 in Hb.
      rewrite Hu2. rewrite <- Z.add_assoc. exact Hb. }
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    (* --- the low halfword: translate at pc, read 2 bytes --- *)
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_leaf pc (u_walk_pa w_leaf pc) σ
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ.(sregs)) User σ)
            (exec_is_shadow_stack_fetch σ) Hall
            with "Hri Hgh Hinv")
      as (σ1) "(%Htr1 & %Hmdev1 & %Hsregs1 & Hri & Hgh & Hinv)".
    assert (Tr1 : forall r : register, register_beq r tlb = false ->
              register_lookup r σ1.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs1 as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    assert (Hnc : forall j : nat, (j < 2)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. lia. }
    iDestruct (umem_fetch_byte pt M w_leaf pc 0 (nth_byte iw 0) σ1 Hl
                 (Hnc 0%nat ltac:(lia)) (Hbytes 0%nat ltac:(lia)) with "Hgh HM")
      as %[Hm0 Hr0].
    iDestruct (umem_fetch_byte pt M w_leaf pc 1 (nth_byte iw 1) σ1 Hl
                 (Hnc 1%nat ltac:(lia)) (Hbytes 1%nat ltac:(lia)) with "Hgh HM")
      as %[Hm1 Hr1].
    assert (Hmr1 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w_leaf pc)) 2 false false false) σ1
                   = Some (Ok (subrange_vec_dec iw 15 0 : mword 16), σ1)).
    { apply (umode_mem_read_fetch_2 (u_walk_pa w_leaf pc)
               (subrange_vec_dec iw 15 0 : mword 16) σ1).
      - intros j HjN. rewrite (nth_byte_subrange_lo iw j HjN).
        assert (Hj : (j < 2)%nat) by lia.
        destruct j as [ | [ | ] ]; try lia; [ exact Hm0 | exact Hm1 ].
      - rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). exact Hr0.
      - exact Hr1.
      - exact (pa_aligned_div _ pc 2 ltac:(lia) ltac:(exists 2048; reflexivity) Hal2).
      - rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA.
      - rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord.
      - rewrite (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX.
      - rewrite (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp.
      - rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif.
      - rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall. }
    (* --- the high halfword: translate at pc+2 (same leaf), read 2 bytes --- *)
    iMod (utlb_inv_pt_translateAddr_u (InstructionFetch tt)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_leaf (add_vec_int pc 2)
            (u_walk_pa w_leaf (add_vec_int pc 2)) σ1
            Hl2 Hchk Hcanon2 eq_refl
            (ltac:(rewrite (Tr1 misa ltac:(vm_compute; reflexivity)); exact Hmisa))
            (ltac:(rewrite (Tr1 menvcfg ltac:(vm_compute; reflexivity)); exact Hmenv))
            (ltac:(rewrite (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
            (ltac:(rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
            (ltac:(rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact HSXL))
            (exec_effectivePrivilege_fetch (register_lookup mstatus σ1.(sregs)) User σ1)
            (exec_is_shadow_stack_fetch σ1)
            (ltac:(rewrite (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
            with "Hri Hgh Hinv")
      as (σ2) "(%Htr2 & %Hmdev2 & %Hsregs2 & Hri & Hgh & Hinv)".
    assert (Tr2 : forall r : register, register_beq r tlb = false ->
              register_lookup r σ2.(sregs) = register_lookup r σ1.(sregs)).
    { intros r Hne.
      destruct Hsregs2 as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (umem_fetch_byte pt M w_leaf (add_vec_int pc 2) 0
                 (nth_byte iw (2 + 0)) σ2 Hl2
                 (Hncs 0%nat ltac:(lia)) (Hbytes2 0%nat ltac:(lia)) with "Hgh HM")
      as %[Hn0 Hs0].
    iDestruct (umem_fetch_byte pt M w_leaf (add_vec_int pc 2) 1
                 (nth_byte iw (2 + 1)) σ2 Hl2
                 (Hncs 1%nat ltac:(lia)) (Hbytes2 1%nat ltac:(lia)) with "Hgh HM")
      as %[Hn1 Hs1].
    assert (Hmr2 : exec (mem_read (InstructionFetch tt) PBMT_PMA
                     (Physaddr (u_walk_pa w_leaf (add_vec_int pc 2))) 2 false false false) σ2
                   = Some (Ok (subrange_vec_dec iw 31 16 : mword 16), σ2)).
    { apply (umode_mem_read_fetch_2 (u_walk_pa w_leaf (add_vec_int pc 2))
               (subrange_vec_dec iw 31 16 : mword 16) σ2).
      - intros j HjN. rewrite (nth_byte_subrange_hi iw j HjN).
        assert (Hj : (j < 2)%nat) by lia.
        destruct j as [ | [ | ] ]; try lia; [ exact Hn0 | exact Hn1 ].
      - rewrite <- (pa_add_0 (u_walk_pa w_leaf (add_vec_int pc 2))). exact Hs0.
      - exact Hs1.
      - exact (pa_aligned_div _ (add_vec_int pc 2) 2 ltac:(lia)
                 ltac:(exists 2048; reflexivity) (ualign2_plus2 pc Hal2)).
      - rewrite (Tr2 pmpcfg_n ltac:(vm_compute; reflexivity))
                (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA.
      - rewrite (Tr2 pmpaddr_n ltac:(vm_compute; reflexivity))
                (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord.
      - rewrite (Tr2 pmpcfg_n ltac:(vm_compute; reflexivity))
                (Tr1 pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX.
      - rewrite (Tr2 pmpaddr_n ltac:(vm_compute; reflexivity))
                (Tr1 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp.
      - rewrite (Tr2 cur_privilege ltac:(vm_compute; reflexivity))
                (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp.
      - rewrite (Tr2 htif_tohost_base ltac:(vm_compute; reflexivity))
                (Tr1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif.
      - rewrite (Tr2 pma_regions ltac:(vm_compute; reflexivity))
                (Tr1 pma_regions ltac:(vm_compute; reflexivity)); exact Hall. }
    iModIntro. iExists σ2.
    iSplit; [ iPureIntro | ].
    { pose proof (exec_fetch_base_2 σ σ1 pc (u_walk_pa w_leaf pc)
                    Lpc HmisaC Hbit0 Hbit1 Hnal4
                    (subrange_vec_dec iw 15 0 : mword 16) Htr1 Hmr1
                    σ2 (u_walk_pa w_leaf (add_vec_int pc 2))
                    (eq_trans (Tr1 PC ltac:(vm_compute; reflexivity)) Lpc)
                    HnRVC (subrange_vec_dec iw 31 16 : mword 16) Htr2 Hmr2) as Hf.
      rewrite concat_subranges_id in Hf. exact Hf. }
    iSplit; [ iPureIntro; rewrite Hmdev2; exact Hmdev1 | ].
    iSplit; [ iPureIntro;
              intros r Hne; rewrite (Tr2 r Hne); exact (Tr1 r Hne) | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeFetchSplitBase.
