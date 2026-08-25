(* UProofShMem.v -- the VERIFIED-EXECUTION proofs of the `sh` program's two
   MEMORY-WRITING functions (claude-notes/projects/user-sh.md):

     wp_sh_memset      memset @0xa5c   frame; byte loop; unframe   (returns)
     wp_sh_free_first  free   @0x1106  the K&R free-list insert, at
                                       the ONE call morecore makes

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v, fed the matching
   [ui_sh_<hexpc>] fact from UCodeSh.v.  Every leaf continuation re-binds the
   hart ([forall CID]), which is why every lemma here takes [CIDp] as an
   EXPLICIT leading binder rather than a section variable.

   Both contracts are now discharged EXACTLY AS THEY STAND in USpecSh.v --
   no restated body, no extra hypothesis.  Everything the earlier passes
   reported (memset's unprovable [uM_written] postcondition, the missing
   [sh_frame_ok] and [8192 <= dst], free's [nu < 2 ^ 31], its vacuous
   [uM_only ... \/ True], and [Hbpsz]/[bp->s.size] being a FOUR-byte C
   [uint]) is fixed there.

   ONE DEFECT REMAINS, and it is the bad kind: [wp_sh_free_first_body]'s
   premises are INCONSISTENT, so the contract is vacuously true.
   [Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88] claims every byte of
   [0x2010 .. 0x2097] is NUL, and [SH_DATA_PG + 0x10] IS [SH_FREEP] -- but
   [Hfreep] says the eight bytes there spell [SH_BASE] = 0x2088, whose low
   byte is 0x88.  They clash at the very first byte.  (That is also what the
   code does: [malloc] sets [freep = &base] BEFORE calling [morecore], so at
   free's one call site [freep] is emphatically not zero.)  [Hbss] is not
   needed for anything here either -- [base.s.size]'s upper half is already
   pinned by [Hbasesz], which claims all EIGHT bytes at [SH_BASE + 8] are
   zero -- so the fix is to drop [Hbss], or at most to narrow it to a range
   that excludes the cells [malloc] has already written.  The contradiction
   is one line: [Hbss 0] gives [M !! 0x2010 = Some ubyte0] and [Hfreep 0%nat]
   gives [M !! 0x2010 = Some (nth_byte (mword_of_int SH_BASE) 0)], whose
   [bv_unsigned] is 136. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import RiscvModelBytes.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeArith UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* re-imported LAST on purpose: WpUmodeStep.v's funnel names its optional
   gpr write [uv_wr], which otherwise shadows UmodeAbi's writable-window
   record of the same name and makes [uv_wr pt M a n] fail with "pt has
   type uptd while it is expected to have type mstate". *)
Require Import UmodeAbi.
Require User.ShSyms User.ShInstrs User.ShData.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The pure shims.                                                     *)
(* ===================================================================== *)

(* an 8-byte / 1-byte store ABOVE the whole image preserves the text
   inclusion.  sh's text keys stop below 8192 ([UCodeSh.sh_bytes_key_lt]),
   which is why the bound is 8192 and not echo's 4096.
   HOIST CANDIDATE: UProofShLib.v carries a byte-for-byte copy of the
   8-byte one; both belong beside [sh_bytes_key_lt] in UCodeSh.v. *)
Local Lemma sh_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma sh_text_sub_store1 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store M a 1 v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store_lookup_ne M a 1 v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* ---- [replicate], spelled out so no stdpp naming drift can reach us --- *)
Local Lemma len_replicate {A : Type} (k : nat) (x : A) :
  length (replicate k x) = k.
Proof. induction k as [ | k IH ]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Local Lemma lookup_repl {A : Type} (k j : nat) (x : A) :
  (j < k)%nat -> replicate k x !! j = Some x.
Proof.
  revert j. induction k as [ | k IH ]; intros j Hj; [ exfalso; lia | ].
  destruct j as [ | j ]; cbn; [ reflexivity | apply IH; lia ].
Qed.

Local Lemma lookup_repl_inv {A : Type} (k j : nat) (x y : A) :
  replicate k x !! j = Some y -> y = x /\ (j < k)%nat.
Proof.
  revert j. induction k as [ | k IH ]; intros j Hj.
  - destruct j; cbn in Hj; discriminate.
  - destruct j as [ | j ]; cbn in Hj.
    + injection Hj as ->. split; [ reflexivity | lia ].
    + destruct (IH j Hj) as [ -> Hlt ]. split; [ reflexivity | lia ].
Qed.

(* ---- the byte a [sb] of a normalized byte value writes ---------------- *)
Local Lemma nth_byte0_moi (c : bv 8) :
  nth_byte (mword_of_int (bv_unsigned c) : mword 64) 0 = c.
Proof.
  apply bv_eq. rewrite nth_byte_unsigned.
  pose proof (bv_unsigned_in_range 8 c) as Hr.
  assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E8 in Hr.
  rewrite moi_unsigned.
  rewrite (Z.mod_small (bv_unsigned c) Z64 ltac:(unfold Z64; lia)).
  change (Z.of_N (8 * N.of_nat 0)) with 0.
  rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256.
  apply Z.mod_small. lia.
Qed.

(* ---- ONE run of [uM_store _ _ 1] extends a [uM_written] window --------
   HOIST CANDIDATE: this is the only thing a byte loop needs to know about
   its own image effect, and it reads generically (UmodeIo.v, beside
   [uM_written] itself). *)
Lemma uM_written_snoc (M M' : gmap Z (bv 8)) (a : Z) (i : nat) (c : bv 8)
    (v : mword 64) :
  nth_byte v 0 = c ->
  uM_written M M' a (replicate i c) ->
  uM_written M (uM_store M' (a + Z.of_nat i) 1 v) a (replicate (S i) c).
Proof.
  intros Hv (Hin & Hout & Hdom).
  assert (Hhit : uM_store M' (a + Z.of_nat i) 1 v !! (a + Z.of_nat i) = Some c).
  { pose proof (uM_store_lookup M' (a + Z.of_nat i) 1 v 0%nat
                  ltac:(change (Z.to_nat 1) with 1%nat; lia)) as H0.
    replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in H0 by lia.
    rewrite H0. rewrite Hv. reflexivity. }
  split_and!.
  - intros j b Hj.
    destruct (lookup_repl_inv (S i) j c b Hj) as [ -> Hjlt ].
    destruct (decide (j = i)) as [ -> | Hne ]; [ exact Hhit | ].
    rewrite (uM_store_lookup_ne M' (a + Z.of_nat i) 1 v (a + Z.of_nat j)
               ltac:(intros k Hk;
                     change (Z.to_nat 1) with 1%nat in Hk;
                     assert (Hk0 : k = 0%nat) by lia; subst k; lia)).
    exact (Hin j c (lookup_repl i j c ltac:(lia))).
  - intros k Hk. rewrite len_replicate in Hk.
    rewrite (uM_store_lookup_ne M' (a + Z.of_nat i) 1 v k
               ltac:(intros k0 Hk0;
                     change (Z.to_nat 1) with 1%nat in Hk0;
                     assert (Hkk : k0 = 0%nat) by lia; subst k0; lia)).
    apply Hout. rewrite len_replicate. lia.
  - intros k Hk. apply uM_store_is_Some. exact (Hdom k Hk).
Qed.

Lemma uM_written_nil (M : gmap Z (bv 8)) (a : Z) (c : bv 8) :
  uM_written M M a (replicate 0 c).
Proof.
  split_and!.
  - intros j b Hj. destruct (lookup_repl_inv 0 j c b Hj) as [ _ Hlt ]. exfalso; lia.
  - intros k _. reflexivity.
  - intros k Hk. exact Hk.
Qed.

(* ---- a byte of a normalized value does not depend on the width, as long
   as the byte is inside the narrow word.  This is what lets a 4-byte
   [lw]/[c.lw] of a [uint] field be read off an 8-byte [uM_bytes]
   premise. *)
Local Lemma z_byte_mod (z s : Z) :
  0 <= s -> s + 8 <= 32 ->
  ((z mod 2 ^ 32) / 2 ^ s) mod 2 ^ 8 = ((z mod 2 ^ 64) / 2 ^ s) mod 2 ^ 8.
Proof.
  intros Hs Hs8.
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k 8) as [ Hlt | Hge ].
  - rewrite (Z.mod_pow2_bits_low ((z mod 2 ^ 32) / 2 ^ s) 8 k ltac:(lia)).
    rewrite (Z.mod_pow2_bits_low ((z mod 2 ^ 64) / 2 ^ s) 8 k ltac:(lia)).
    rewrite <- (Z.shiftr_div_pow2 (z mod 2 ^ 32) s Hs).
    rewrite <- (Z.shiftr_div_pow2 (z mod 2 ^ 64) s Hs).
    rewrite (Z.shiftr_spec (z mod 2 ^ 32) s k Hk).
    rewrite (Z.shiftr_spec (z mod 2 ^ 64) s k Hk).
    rewrite (Z.mod_pow2_bits_low z 32 (k + s) ltac:(lia)).
    rewrite (Z.mod_pow2_bits_low z 64 (k + s) ltac:(lia)).
    reflexivity.
  - rewrite (Z.mod_pow2_bits_high ((z mod 2 ^ 32) / 2 ^ s) 8 k ltac:(lia)).
    rewrite (Z.mod_pow2_bits_high ((z mod 2 ^ 64) / 2 ^ s) 8 k ltac:(lia)).
    reflexivity.
Qed.

Local Lemma nth_byte_moi_4 (z : Z) (j : nat) :
  (j < 4)%nat ->
  nth_byte (mword_of_int z : mword 32) j = nth_byte (mword_of_int z : mword 64) j.
Proof.
  intro Hj. apply bv_eq. rewrite !nth_byte_unsigned.
  rewrite moi32_unsigned moi64_unsigned. unfold bv_wrap.
  assert (E32 : bv_modulus 32 = 2 ^ 32) by (vm_compute; reflexivity).
  assert (E64 : bv_modulus 64 = 2 ^ 64) by (vm_compute; reflexivity).
  rewrite E32 E64.
  pose proof (N2Z.is_nonneg (8 * N.of_nat j)) as Hnn.
  rewrite (Z.shiftr_div_pow2 (z mod 2 ^ 32) (Z.of_N (8 * N.of_nat j)) Hnn).
  rewrite (Z.shiftr_div_pow2 (z mod 2 ^ 64) (Z.of_N (8 * N.of_nat j)) Hnn).
  apply z_byte_mod; lia.
Qed.

Local Lemma uM_bytes_4_of_8 (M : gmap Z (bv 8)) (a z : Z) :
  uM_bytes M a 8 (mword_of_int z : mword 64) ->
  uM_bytes M a 4 (mword_of_int z : mword 32).
Proof.
  intros H j Hj. rewrite (nth_byte_moi_4 z j Hj). exact (H j ltac:(lia)).
Qed.

(* ---- the unsigned comparisons UmodeArith.v does not carry -------------
   HOIST CANDIDATE: the exact twins of [moi_lt_s] / [moi_ge_s]
   (UmodeArith.v §3); free's scan branches on POINTERS, so it needs the
   unsigned pair. *)


(* ---- gcc's `zero-extend a uint field and scale by 16' idiom ----------- *)
Local Lemma moi_scale16 (z : Z) :
  (mword_of_int (z * 2 ^ 32 / 2 ^ 28) : mword 64) = mword_of_int (z * 16).
Proof.
  f_equal.
  replace (2 ^ 32) with (16 * 2 ^ 28) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc. apply Z.div_mul. vm_compute; discriminate.
Qed.

Section UProofShMem.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  (* user code runs AS the thread: ambient context, and a
     reschedule moves the hart, never the context. *)
  Context `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).

  (* the 4-byte twin of UmodeAbi's [uv_slot8_facts]: every side condition a
     WORD access at a closed 4-aligned address needs.
     HOIST CANDIDATE: it belongs beside [uv_slot8_facts] (UmodeAbi §9). *)

  (* everything an 8-byte LOAD at a closed 8-aligned address needs, off ONE
     [uM_bytes] premise *)
  Local Lemma acc8_facts (Mx : gmap Z (bv 8)) (a v : Z) :
    0 <= a -> a mod 8 = 0 -> a + 8 <= 2 ^ 38 ->
    uM_bytes Mx a 8 (mword_of_int v : mword 64) ->
    uint (mword_of_int a : mword 64) = a /\
    uva_canon (mword_of_int a : mword 64) /\
    Z.rem (uint (mword_of_int a : mword 64)) 4096 <= 4088 /\
    is_aligned_vaddr (Virtaddr (mword_of_int a : mword 64)) 8 = true /\
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8, Mx !! (uint (mword_of_int a : mword 64) + Z.of_nat j) = Some bb) /\
    (mword_of_int v : mword 64) = uM_word Mx (uint (mword_of_int a : mword 64)) 8.
  Proof.
    intros Ha0 Ha8 Hahi Hbw.
    destruct (uv_slot8_facts a (mword_of_int a) Ha0 Ha8 Hahi eq_refl)
      as (Hu & Hcanon & Hpg & Hal).
    split_and!; try assumption.
    - rewrite Hu. exact (uM_bytes_exists Mx a 8 _ Hbw).
    - rewrite Hu. symmetry. exact (uM_word_w8 Mx a _ Hbw).
  Qed.

  (* the HEAP's leaf, at any address inside the mapped region *)
  Local Lemma heap_leaf (a : Z) :
    sh_layout pt hbase hlen -> hbase <= a < hbase + hlen ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w.
  Proof.
    intros Hlay Ha.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (shl_hlen _ _ _ Hlay) as Hhl.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    unfold SH_DATA_PG in Hhlo.
    change (2 ^ 38) with 274877906944 in Hhhi.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    rewrite Z.rem_mod_nonneg in Hhl; [ | lia | lia ].
    assert (Hhlq : hlen = 4096 * (hlen / 4096))
      by (pose proof (Z.div_mod hlen 4096 ltac:(lia)); lia).
    assert (Hbq : hbase = 4096 * (hbase / 4096))
      by (pose proof (Z.div_mod hbase 4096 ltac:(lia)); lia).
    pose proof (Z.div_mod a 4096 ltac:(lia)) as Haq.
    pose proof (Z.div_mod (a - hbase) 4096 ltac:(lia)) as Hdq.
    pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as Har.
    pose proof (Z.mod_pos_bound (a - hbase) 4096 ltac:(lia)) as Hdr.
    assert (Hi : 0 <= (a - hbase) / 4096 < hlen / 4096).
    { split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
    destruct (shl_heap _ _ _ Hlay ((a - hbase) / 4096) Hi) as (w & Hw & Hld & Hst).
    assert (He : hbase + 4096 * ((a - hbase) / 4096) = 4096 * (a / 4096)) by lia.
    exists w. rewrite (sh_svpn_page a ltac:(lia)). rewrite <- He.
    split_and!; assumption.
  Qed.

  (* the .data/.bss page's leaf, at any address on it *)
  Local Lemma data_leaf (a : Z) :
    sh_layout pt hbase hlen -> SH_DATA_PG <= a < SH_DATA_PG + 4096 ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w.
  Proof.
    intros Hlay Ha. unfold SH_DATA_PG in Ha.
    destruct (shl_data _ _ _ Hlay) as (w & Hw & Hld & Hst).
    unfold SH_DATA_PG in Hw.
    assert (Hq : a / 4096 = 2)
      by (symmetry; apply (Zdiv_unique a 4096 2 (a - 8192)); lia).
    exists w. rewrite (sh_svpn_page a ltac:(lia)).
    rewrite Hq. replace (4096 * 2) with 8192 by lia.
    split_and!; assumption.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 memset @0xa5c -- the corrected contract.                          *)
  (* ------------------------------------------------------------------- *)

  (* "k is outside the window [a, a+n) of a [uM_only_in] window list" *)
  Local Lemma not_in_window (ws : list (Z * Z)) (a n k : Z) :
    (a, n) ∈ ws -> ~ uM_in_windows ws k -> k < a \/ a + n <= k.
  Proof.
    intros Hin Hnot.
    destruct (Z.lt_ge_cases k a) as [ Hlt | Hge ]; [ left; lia | ].
    destruct (Z.lt_ge_cases k (a + n)) as [ Hlt2 | Hge2 ]; [ | right; lia ].
    exfalso. apply Hnot. exists (a, n). split; [ exact Hin | simpl; lia ].
  Qed.

  (* ---- THE BYTE LOOP.  Head 0xa70, back edge 0xa76:
       a70  sb a1,0(a5) ; a74  c.addi a5,a5,1 ; a76  bne a5,a4,a70
     Ordinary Rocq induction on the STRICT nat measure [n - i]; the branch
     leaf is later-free, so a bounded loop pays no [>].  [MB] is the image
     the prologue left; the invariant is exactly the postcondition, at [i]
     bytes instead of [n]. ------------------------------------------------ *)
  Local Lemma wp_sh_memset_loop (nn : nat) :
    forall (CIDp : CpuId) (MB Mi : gmap Z (bv 8)) (mE : regfile)
      (dst n i : Z) (c : bv 8),
      (Z.to_nat (n - i) < nn)%nat ->
      sh_text_layout pt -> sh_text_sub MB ->
      uv_wr pt MB dst n ->
      8192 <= dst ->
      0 <= i < n -> n < 2 ^ 31 ->
      uM_written MB Mi dst (replicate (Z.to_nat i) c) ->
      mE !!! Regidx a5_idx = (mword_of_int (dst + i) : mword 64) ->
      mE !!! Regidx a4_idx = (mword_of_int (dst + n) : mword 64) ->
      mE !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh Mi mE -∗
      pc_is (CID := CIDp) (mword_of_int 0xa70) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜uM_written MB M' dst (replicate (Z.to_nat n) c)⌝ -∗
         ⌜forall r : mword 5,
            Regidx r <> Regidx a5_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
         pc_is (CID := CID) (mword_of_int 0xa7a) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp MB Mi mE dst n i c Hmeas Hl Htext Hwr Hdst8 Hi Hn31 Hinv
             Ha5 Ha4 Ha1.
    { exfalso. lia. }
    pose proof (uwr_lo _ _ _ _ Hwr) as Hd0.
    pose proof (uwr_hi _ _ _ _ Hwr) as Hdhi.
    change (2 ^ 38) with 274877906944 in Hdhi.
    destruct Hinv as (Hin & Hout & Hdom).
    (* the text survives, because the buffer is above the image *)
    assert (Htexti : sh_text_sub Mi).
    { intros k b Hk. rewrite (Hout k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    iIntros "Hcg Hpc Hcont".
    (* ---- 0xa70  sb a1,0(a5) ---- *)
    assert (Hva : (mword_of_int (dst + i) : mword 64)
                  = add_vec (mE !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha5.
      assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc0 moi_add. f_equal; lia. }
    destruct (uwr_leaf _ _ _ _ Hwr i ltac:(lia)) as (wst & Hlst & Hokst).
    replace (dst + i) with (dst + i) in Hlst by lia.
    assert (Huva : uint (mword_of_int (dst + i) : mword 64) = dst + i)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hcanon : uva_canon (mword_of_int (dst + i) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    destruct (uwr_bytes _ _ _ _ Hwr i ltac:(lia)) as (bb0 & Hbb0).
    destruct (Hdom (dst + i) (mk_is_Some _ _ Hbb0)) as (bb & Hbb).
    assert (Hbb' : Mi !! (uint (mword_of_int (dst + i) : mword 64)) = Some bb)
      by (rewrite Huva; exact Hbb).
    iApply (wp_uv_sb C pt Psh Mi mE (mword_of_int 0xa70)
              (mword_of_int 0 : mword 12) a5_idx a1_idx
              wst (mword_of_int (dst + i)) (mword_of_int (bv_unsigned c)) bb
              (ui_sh_a70 pt Mi Hl Htexti)
              Hva (eq_sym Ha1) Hlst Hokst Hcanon Hbb'
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    iEval (rewrite Huva) in "Hcg".
    set (Mi1 := uM_store Mi (dst + i) 1 (mword_of_int (bv_unsigned c) : mword 64)).
    assert (Hinv1 : uM_written MB Mi1 dst (replicate (S (Z.to_nat i)) c)).
    { unfold Mi1.
      replace (dst + i) with (dst + Z.of_nat (Z.to_nat i)) by lia.
      exact (uM_written_snoc MB Mi dst (Z.to_nat i) c
               (mword_of_int (bv_unsigned c)) (nth_byte0_moi c)
               (conj Hin (conj Hout Hdom))). }
    assert (Ea70 : add_vec_int (mword_of_int 0xa70 : mword 64) 4 = mword_of_int 0xa74)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea70) in "Hpc".
    assert (Htexti1 : sh_text_sub Mi1)
      by (unfold Mi1; apply sh_text_sub_store1; [ exact Htexti | lia ]).
    (* ---- 0xa74  c.addi a5,a5,1 ---- *)
    assert (Hadd : (mword_of_int (dst + (i + 1)) : mword 64)
                   = add_vec (mE !!! Regidx a5_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
    { rewrite Ha5.
      assert (Hc1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                     : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc1 moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh Mi1 mE (mword_of_int 0xa74)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int (dst + (i + 1)))
              (ui_sh_a74 pt Mi1 Hl Htexti1)
              ltac:(vm_compute; discriminate) Hadd
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mL := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (dst + (i + 1)) : mword 64)]> mE).
    assert (Ea74 : add_vec_int (mword_of_int 0xa74 : mword 64) 2 = mword_of_int 0xa76)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea74) in "Hpc".
    assert (HmLa5 : mL !!! Regidx a5_idx = (mword_of_int (dst + (i + 1)) : mword 64))
      by exact (upd_eq mE (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (dst + (i + 1)) : mword 64))).
    assert (HmLa4 : mL !!! Regidx a4_idx = (mword_of_int (dst + n) : mword 64)).
    { exact (eq_trans
               (upd_ne mE (Regidx a5_idx) (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (dst + (i + 1)) : mword 64))
                  ltac:(vm_compute; discriminate)) Ha4). }
    assert (Hpres : forall r : mword 5,
              Regidx r <> Regidx a5_idx -> mL !!! Regidx r = mE !!! Regidx r).
    { intros r Hr. exact (upd_ne mE (Regidx a5_idx) (Regidx r)
                            (regval_into_reg (mword_of_int (dst + (i + 1)) : mword 64))
                            Hr). }
    assert (Htgt : (mword_of_int 0xa70 : mword 64)
                   = add_vec (mword_of_int 0xa76)
                       (sign_extend' 64 (mword_of_int 8186 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xa76  bne a5,a4,0xa70 ---- *)
    destruct (Z.eq_dec (i + 1) n) as [ Hend | Hne ].
    - (* the last byte: fall through to the epilogue *)
      assert (Htk : false = uv_btaken BNE (mL !!! Regidx a5_idx) (mL !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite HmLa5 HmLa4.
        rewrite (moi_neq_vec (dst + (i + 1)) (dst + n)
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
      iApply (wp_uv_btype C pt Psh Mi1 mL (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE
                false (mword_of_int 0xa70)
                (ui_sh_a76 pt Mi1 Hl Htexti1)
                Htk Htgt ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      assert (Ea76 : (if false then (mword_of_int 0xa70 : mword 64)
                      else add_vec_int (mword_of_int 0xa76 : mword 64) 4)
                     = mword_of_int 0xa7a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea76) in "Hpc".
      iApply ("Hcont" $! CID3 mL Mi1 with "[] [] Hcg Hpc").
      + iPureIntro. replace (Z.to_nat n) with (S (Z.to_nat i)) by lia. exact Hinv1.
      + iPureIntro. exact Hpres.
    - (* a body byte: take the back edge with i := i + 1 *)
      assert (Htk : true = uv_btaken BNE (mL !!! Regidx a5_idx) (mL !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite HmLa5 HmLa4.
        rewrite (moi_neq_vec (dst + (i + 1)) (dst + n)
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
      iApply (wp_uv_btype C pt Psh Mi1 mL (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE
                true (mword_of_int 0xa70)
                (ui_sh_a76 pt Mi1 Hl Htexti1)
                Htk Htgt ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      assert (HmLa1 : mL !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64))
        by (rewrite (Hpres a1_idx ltac:(vm_compute; discriminate)); exact Ha1).
      assert (HmLa5' : mL !!! Regidx a5_idx
                       = (mword_of_int (dst + (i + 1)) : mword 64)) by exact HmLa5.
      iApply (IH CID3 MB Mi1 mL dst n (i + 1) c
                ltac:(lia) Hl Htext Hwr Hdst8 ltac:(lia) Hn31
                ltac:(replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia;
                      exact Hinv1)
                HmLa5' HmLa4 HmLa1
                with "Hcg Hpc").
      iIntros (CID4 m' M') "%Hw %Hp Hcg Hpc".
      iApply ("Hcont" $! CID4 m' M' with "[] [] Hcg Hpc").
      + iPureIntro. exact Hw.
      + iPureIntro. intros r Hr. rewrite (Hp r Hr). exact (Hpres r Hr).
  Qed.

  (* ---- memset, the whole function ------------------------------------ *)
  Lemma wp_sh_memset (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (dst n : Z) (c : bv 8) :
    wp_sh_memset_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 dst n c.
  Proof.
    intros Hlay Htext Hsp Hst Hdst Hc Hn Hnr Hwr Hfr Hdst8 Habove Hret2.
    assert (Hmemset : ShSyms.memset = 0xa5c)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    assert (Hstk8 : 8192 <= uint sp0 - 16) by lia.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (uwr_lo _ _ _ _ Hwr) as Hd0.
    pose proof (uwr_hi _ _ _ _ Hwr) as Hdhi.
    change (2 ^ 38) with 274877906944 in Hdhi.
    change (2 ^ 31) with 2147483648 in Hnr.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hmemset) in "Hpc".
    (* ---- 0xa5c..0xa62  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0xa5c sh_text_sub 8192 M m sp0
              Htext sh_text_sub_store8 Hstk8 Hsp Hst
              (ui_sh_a5c pt M Hl Htext)
              (fun Mx Hx => ui_sh_a5e pt Mx Hl Hx)
              (fun Mx Hx => ui_sh_a60 pt Mx Hl Hx)
              (fun Mx Hx => ui_sh_a62 pt Mx Hl Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (m1 := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx
                    := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k)).
    { intros k Hk. unfold M2, M1.
      exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)). }
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split; [ exact Hdom2 | ].
      intros k Hk. unfold M2.
      rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                 ltac:(intros j Hj; lia)).
      unfold M1.
      exact (uM_store8_lookup_ne M (uint sp0 - 8) (m !!! Regidx ra_idx) k
               ltac:(intros j Hj; lia)). }
    assert (Hwr2 : uv_wr pt M2 dst n) by exact (uv_wr_dom pt M M2 dst n Hdom2 Hwr).
    assert (Hst2 : uv_stack pt M2 sp0 16)
      by exact (uv_stack_dom pt M M2 sp0 16 Hdom2 Hst).
    (* the frame slots, as byte windows over the post-prologue image *)
    assert (Hby0 : uM_bytes M2 (uint sp0 - 16) 8 (m !!! Regidx s0_idx))
      by exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Hby8 : uM_bytes M2 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. unfold M2.
      rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(intros k Hk; lia)).
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    (* the registers the prologue leaves *)
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              m1 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0.
      exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx r)
                  (mword_of_int (uint sp0) : mword 64) Ns0)
               (upd_ne m (Regidx sp_idx) (Regidx r)
                  (mword_of_int (uint sp0 - 16) : mword 64) Nsp)). }
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int dst : mword 64))
      by (rewrite (Hpre a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hdst).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64))
      by (rewrite (Hpre a1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hc).
    assert (Ha2_1 : m1 !!! Regidx a2_idx = (mword_of_int n : mword 64))
      by (rewrite (Hpre a2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hn).
    assert (Hsp_1 : m1 !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0) : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)))). }
    assert (Htgt64 : (mword_of_int 0xa7a : mword 64)
                     = add_vec (mword_of_int 0xa64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 11 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xa64  c.beqz a2,0xa7a ---- *)
    destruct (Z.eq_dec n 0) as [ Hz | Hnz ].
    - (* n = 0: nothing to write; jump straight to the epilogue *)
      assert (Htk : true = eq_vec (m1 !!! Regidx a2_idx) zero_reg).
      { rewrite Ha2_1 (moi_eq_zero n ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_eq. exact Hz. }
      iApply (wp_uv_cbeqz C pt Psh M2 m1 (mword_of_int 0xa64)
                (mword_of_int 11 : mword 8) (mword_of_int 4 : mword 3) a2_idx
                true (mword_of_int 0xa7a)
                (ui_sh_a64 pt M2 Hl Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt64
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID2) "Hcg Hpc".
      iApply (wp_uv_epilogue16 C pt CID2 Psh 0xa7a M2 m1 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst2 Hret2 Hsp_1
                (uM_word_w8 M2 (uint sp0 - 8) _ Hby8)
                (uM_word_w8 M2 (uint sp0 - 16) _ Hby0)
                (ui_sh_a7a pt M2 Hl Htext2)
                (ui_sh_a7c pt M2 Hl Htext2)
                (ui_sh_a7e pt M2 Hl Htext2)
                (ui_sh_a80 pt M2 Hl Htext2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID3 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID3 m' M2 with "[] [] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
        { rewrite Es0 HB. reflexivity. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0). exact (Hpre r Nsp Ns0).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact Ha0_1.
      + iPureIntro. intros j Hj. exfalso. lia.
      + iPureIntro. split; [ exact Hdom2 | ].
        intros k Hk.
        exact (proj2 Honly k
                 (not_in_window _ (uint sp0 - 16) 16 k
                    ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk)).
    - (* n > 0: set up the loop registers and run it *)
      assert (Htk : false = eq_vec (m1 !!! Regidx a2_idx) zero_reg).
      { rewrite Ha2_1 (moi_eq_zero n ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uv_cbeqz C pt Psh M2 m1 (mword_of_int 0xa64)
                (mword_of_int 11 : mword 8) (mword_of_int 4 : mword 3) a2_idx
                false (mword_of_int 0xa7a)
                (ui_sh_a64 pt M2 Hl Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt64
                ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CID2) "Hcg Hpc".
      assert (Ea64 : (if false then (mword_of_int 0xa7a : mword 64)
                      else add_vec_int (mword_of_int 0xa64 : mword 64) 2)
                     = mword_of_int 0xa66)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea64) in "Hpc".
      (* ---- 0xa66  c.mv a5,a0 ---- *)
      assert (Hmv : (mword_of_int dst : mword 64)
                    = add_vec zero_reg (m1 !!! Regidx a0_idx))
        by (rewrite Ha0_1 moi_add_zero_l; reflexivity).
      iApply (wp_uv_cmv C pt Psh M2 m1 (mword_of_int 0xa66)
                a5_idx a0_idx (mword_of_int dst)
                (ui_sh_a66 pt M2 Hl Htext2)
                ltac:(vm_compute; discriminate) Hmv
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      set (m2 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int dst : mword 64)]> m1).
      assert (Ea66 : add_vec_int (mword_of_int 0xa66 : mword 64) 2 = mword_of_int 0xa68)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea66) in "Hpc".
      (* ---- 0xa68  c.slli a2,a2,0x20 ---- *)
      assert (Ha2_2 : m2 !!! Regidx a2_idx = (mword_of_int n : mword 64)).
      { exact (eq_trans
                 (upd_ne m1 (Regidx a5_idx) (Regidx a2_idx)
                    (regval_into_reg (mword_of_int dst : mword 64))
                    ltac:(vm_compute; discriminate)) Ha2_1). }
      assert (Hshl : (mword_of_int (n * 2 ^ 32) : mword 64)
                     = shift_bits_left (m2 !!! Regidx a2_idx)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0)).
      { rewrite Ha2_2. symmetry. exact (moi_shl n 32 ltac:(lia)). }
      iApply (wp_uv_cslli C pt Psh M2 m2 (mword_of_int 0xa68)
                (mword_of_int 32 : mword 6) a2_idx (mword_of_int (n * 2 ^ 32))
                (ui_sh_a68 pt M2 Hl Htext2)
                ltac:(vm_compute; discriminate) Hshl
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      set (m3 := <[Regidx a2_idx
                   := regval_into_reg (mword_of_int (n * 2 ^ 32) : mword 64)]> m2).
      assert (Ea68 : add_vec_int (mword_of_int 0xa68 : mword 64) 2 = mword_of_int 0xa6a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea68) in "Hpc".
      (* ---- 0xa6a  c.srli a2,a2,0x20 ---- *)
      assert (Ha2_3 : m3 !!! Regidx a2_idx = (mword_of_int (n * 2 ^ 32) : mword 64))
        by exact (upd_eq m2 (Regidx a2_idx)
                    (regval_into_reg (mword_of_int (n * 2 ^ 32) : mword 64))).
      assert (Hshr : (mword_of_int n : mword 64)
                     = shift_bits_right (m3 !!! Regidx a2_idx)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0)).
      { rewrite Ha2_3.
        rewrite (moi_shr (n * 2 ^ 32) 32 ltac:(lia)
                   ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
        f_equal. rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ]. }
      iApply (wp_uv_csrli C pt Psh M2 m3 (mword_of_int 0xa6a)
                (mword_of_int 32 : mword 6) (mword_of_int 4 : mword 3) a2_idx
                (mword_of_int n)
                (ui_sh_a6a pt M2 Hl Htext2)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hshr
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      set (m4 := <[Regidx a2_idx
                   := regval_into_reg (mword_of_int n : mword 64)]> m3).
      assert (Ea6a : add_vec_int (mword_of_int 0xa6a : mword 64) 2 = mword_of_int 0xa6c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea6a) in "Hpc".
      (* ---- 0xa6c  add a4,a2,a0 ---- *)
      assert (Ha2_4 : m4 !!! Regidx a2_idx = (mword_of_int n : mword 64))
        by exact (upd_eq m3 (Regidx a2_idx)
                    (regval_into_reg (mword_of_int n : mword 64))).
      assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int dst : mword 64)).
      { exact (eq_trans
                 (upd_ne m3 (Regidx a2_idx) (Regidx a0_idx)
                    (regval_into_reg (mword_of_int n : mword 64))
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne m2 (Regidx a2_idx) (Regidx a0_idx)
                       (regval_into_reg (mword_of_int (n * 2 ^ 32) : mword 64))
                       ltac:(vm_compute; discriminate))
                    (eq_trans
                       (upd_ne m1 (Regidx a5_idx) (Regidx a0_idx)
                          (regval_into_reg (mword_of_int dst : mword 64))
                          ltac:(vm_compute; discriminate)) Ha0_1))). }
      assert (Hsum : (mword_of_int (dst + n) : mword 64)
                     = add_vec (m4 !!! Regidx a2_idx) (m4 !!! Regidx a0_idx)).
      { rewrite Ha2_4 Ha0_4 moi_add. f_equal; lia. }
      iApply (wp_uv_add C pt Psh M2 m4 (mword_of_int 0xa6c)
                a2_idx a0_idx a4_idx (mword_of_int (dst + n))
                (ui_sh_a6c pt M2 Hl Htext2)
                ltac:(vm_compute; discriminate) Hsum
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      set (m5 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int (dst + n) : mword 64)]> m4).
      assert (Ea6c : add_vec_int (mword_of_int 0xa6c : mword 64) 4 = mword_of_int 0xa70)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea6c) in "Hpc".
      (* ---- 0xa70..0xa76  the byte loop ---- *)
      assert (Hbody : forall r : mword 5,
                Regidx r <> Regidx a2_idx -> Regidx r <> Regidx a4_idx ->
                Regidx r <> Regidx a5_idx -> m5 !!! Regidx r = m1 !!! Regidx r).
      { intros r N2 N4 N5.
        exact (eq_trans
                 (upd_ne m4 (Regidx a4_idx) (Regidx r)
                    (regval_into_reg (mword_of_int (dst + n) : mword 64)) N4)
                 (eq_trans
                    (upd_ne m3 (Regidx a2_idx) (Regidx r)
                       (regval_into_reg (mword_of_int n : mword 64)) N2)
                    (eq_trans
                       (upd_ne m2 (Regidx a2_idx) (Regidx r)
                          (regval_into_reg (mword_of_int (n * 2 ^ 32) : mword 64)) N2)
                       (upd_ne m1 (Regidx a5_idx) (Regidx r)
                          (regval_into_reg (mword_of_int dst : mword 64)) N5)))). }
      assert (H5a5 : m5 !!! Regidx a5_idx = (mword_of_int (dst + 0) : mword 64)).
      { replace (dst + 0) with dst by lia.
        exact (eq_trans
                 (upd_ne m4 (Regidx a4_idx) (Regidx a5_idx)
                    (regval_into_reg (mword_of_int (dst + n) : mword 64))
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne m3 (Regidx a2_idx) (Regidx a5_idx)
                       (regval_into_reg (mword_of_int n : mword 64))
                       ltac:(vm_compute; discriminate))
                    (eq_trans
                       (upd_ne m2 (Regidx a2_idx) (Regidx a5_idx)
                          (regval_into_reg (mword_of_int (n * 2 ^ 32) : mword 64))
                          ltac:(vm_compute; discriminate))
                       (upd_eq m1 (Regidx a5_idx)
                          (regval_into_reg (mword_of_int dst : mword 64)))))). }
      assert (H5a4 : m5 !!! Regidx a4_idx = (mword_of_int (dst + n) : mword 64))
        by exact (upd_eq m4 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int (dst + n) : mword 64))).
      assert (H5a1 : m5 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64))
        by (rewrite (Hbody a1_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Ha1_1).
      iApply (wp_sh_memset_loop (S (Z.to_nat n)) CID6 M2 M2 m5 dst n 0 c
                ltac:(lia) Hl Htext2 Hwr2 Hdst8 ltac:(lia) ltac:(lia)
                ltac:(change (Z.to_nat 0) with 0%nat; exact (uM_written_nil M2 dst c))
                H5a5 H5a4 H5a1
                with "Hcg Hpc").
      iIntros (CID7 m6 M') "%Hwrt %Hp6 Hcg Hpc".
      (* the frame is untouched by the buffer writes *)
      destruct Hwrt as (Hwin & Hwout & Hwdom).
      assert (Hfrm : forall k : Z, uint sp0 - 16 <= k < uint sp0 -> M' !! k = M2 !! k).
      { intros k Hk. apply Hwout. rewrite len_replicate. lia. }
      assert (Hby8' : uM_bytes M' (uint sp0 - 8) 8 (m !!! Regidx ra_idx))
        by (intros j Hj; rewrite (Hfrm (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
            exact (Hby8 j Hj)).
      assert (Hby0' : uM_bytes M' (uint sp0 - 16) 8 (m !!! Regidx s0_idx))
        by (intros j Hj; rewrite (Hfrm (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
            exact (Hby0 j Hj)).
      assert (Htext' : sh_text_sub M').
      { intros k b Hk.
        rewrite (Hwout k ltac:(rewrite len_replicate;
                               pose proof (sh_bytes_key_lt k b Hk); lia)).
        exact (Htext2 k b Hk). }
      assert (Hst' : uv_stack pt M' sp0 16)
        by exact (uv_stack_dom pt M2 M' sp0 16 Hwdom Hst2).
      assert (H6sp : m6 !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64)).
      { rewrite (Hp6 sp_idx ltac:(vm_compute; discriminate)).
        rewrite (Hbody sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hsp_1. }
      (* ---- 0xa7a..0xa80  the epilogue ---- *)
      iApply (wp_uv_epilogue16 C pt CID7 Psh 0xa7a M' m6 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst' Hret2 H6sp
                (uM_word_w8 M' (uint sp0 - 8) _ Hby8')
                (uM_word_w8 M' (uint sp0 - 16) _ Hby0')
                (ui_sh_a7a pt M' Hl Htext')
                (ui_sh_a7c pt M' Hl Htext')
                (ui_sh_a7e pt M' Hl Htext')
                (ui_sh_a80 pt M' Hl Htext')
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID8 m7) "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID8 m7 M' with "[] [] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
        { rewrite Es0 HB. reflexivity. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N2 : Regidx r <> Regidx a2_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N4 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0). rewrite (Hp6 r N5). rewrite (Hbody r N2 N4 N5).
        exact (Hpre r Nsp Ns0).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (Hp6 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hbody a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact Ha0_1.
      + iPureIntro. intros j Hj.
        replace (dst + j) with (dst + Z.of_nat (Z.to_nat j)) by lia.
        exact (Hwin (Z.to_nat j) c (lookup_repl (Z.to_nat n) (Z.to_nat j) c
                                      ltac:(lia))).
      + iPureIntro. split.
        * intros k Hk. exact (Hwdom k (Hdom2 k Hk)).
        * intros k Hk.
          rewrite (Hwout k ltac:(rewrite len_replicate;
                                 pose proof (not_in_window _ dst n k
                                   ltac:(apply elem_of_list_here) Hk) as Hnb;
                                 lia)).
          exact (proj2 Honly k
                   (not_in_window _ (uint sp0 - 16) 16 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 free @0x1106 -- the K&R free-list insert, at the ONE call          *)
  (*     [morecore] makes.                                                 *)
  (*                                                                       *)
  (*   1106..110c  the frame                                               *)
  (*   110e        a3 = bp = ap - 16                                       *)
  (*   1112..1116  a5 = freep  (= &base)                                   *)
  (*   111a..1132  THE SCAN.  freep = &base, base self-linked with size 0,  *)
  (*               and bp is in the heap, ABOVE base.  The entry test at    *)
  (*               1128 (`p >= bp'?) fails at once, and the second pair --  *)
  (*               112e (`bp < p->s.ptr'?) and 1132 (`p < p->s.ptr'?) --    *)
  (*               fail too, so the loop body at 111c..1126 NEVER runs and  *)
  (*               p stays &base.  That is why this contract is a state,    *)
  (*               not a free-list invariant.                               *)
  (*   1136..1146  `bp + bp->s.size == p->s.ptr'?  No: p->s.ptr is &base,   *)
  (*               which is below the heap.                                 *)
  (*   114a        bp->s.ptr = &base                                        *)
  (*   114e..115a  `p + p->s.size == bp'?  No: base.s.size is 0.            *)
  (*   115e        base.s.ptr = bp                                          *)
  (*   1160..1164  freep = &base                                            *)
  (*   1168..116e  the frame back                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_free_first (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (bp nu : Z) :
    wp_sh_free_first_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 bp nu.
  Proof.
    intros Hlay Htext Hsp Hst Hap Hbp Hnu Hfreep Hbaseptr Hbasesz Hbpsz
           Hheapw Hbssw Hfr Hret2.
    (* the signed-[lw] bound now travels inside [Hnu] *)
    assert (Hnu31 : nu < 2 ^ 31) by (destruct Hnu as [[_ H] _]; exact H).
    assert (Hfsym : ShSyms.free = 0x1106)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhhi.
    change (2 ^ 31) with 2147483648 in Hnu31.
    change SH_FREEP with 8208 in *. change SH_BASE with 8328 in *.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    destruct Hnu as [ Hnu0 Hnuhi ].
    assert (Hbplo : 12288 <= bp) by lia.
    assert (Hbpm : bp mod 4096 = 0) by (rewrite Hbp; exact Hhb).
    assert (Hbp4 : bp mod 4 = 0).
    { assert (Hd : (4 | 4096)) by (exists 1024; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 4 4096 bp ltac:(lia) ltac:(lia) Hd).
      rewrite Hbpm. reflexivity. }
    assert (Hbp8m : bp mod 8 = 0).
    { assert (Hd : (8 | 4096)) by (exists 512; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 4096 bp ltac:(lia) ltac:(lia) Hd).
      rewrite Hbpm. reflexivity. }
    assert (Hbp84 : (bp + 8) mod 4 = 0).
    { rewrite Zplus_mod. rewrite Hbp4. reflexivity. }
    assert (Hbphi : bp + 16 * nu <= uint sp0 - 16) by lia.
    assert (Hbp38 : bp + 16 * nu <= 274877906944) by lia.
    assert (Hsplo : 77824 <= uint sp0 - 16) by lia.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hfsym) in "Hpc".
    (* ---- 0x1106..0x110c  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0x1106 sh_text_sub 8192 M m sp0
              Htext sh_text_sub_store8 ltac:(lia) Hsp Hst
              (ui_sh_1106 pt M Hl Htext)
              (fun Mx Hx => ui_sh_1108 pt Mx Hl Hx)
              (fun Mx Hx => ui_sh_110a pt Mx Hl Hx)
              (fun Mx Hx => ui_sh_110c pt Mx Hl Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (m1 := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx
                    := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k)).
    { intros k Hk. unfold M2, M1.
      exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)). }
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split; [ exact Hdom2 | ].
      intros k Hk. unfold M2.
      rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                 ltac:(intros j Hj; lia)).
      unfold M1.
      exact (uM_store8_lookup_ne M (uint sp0 - 8) (m !!! Regidx ra_idx) k
               ltac:(intros j Hj; lia)). }
    assert (HeqM2 : forall k : Z, k < uint sp0 - 16 -> M2 !! k = M !! k)
      by (intros k Hk; exact (proj2 Honly k (or_introl Hk))).
    assert (Hst2 : uv_stack pt M2 sp0 16)
      by exact (uv_stack_dom pt M M2 sp0 16 Hdom2 Hst).
    assert (Hby0 : uM_bytes M2 (uint sp0 - 16) 8 (m !!! Regidx s0_idx))
      by exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Hby8 : uM_bytes M2 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. unfold M2.
      rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(intros k Hk; lia)).
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              m1 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0.
      exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx r)
                  (mword_of_int (uint sp0) : mword 64) Ns0)
               (upd_ne m (Regidx sp_idx) (Regidx r)
                  (mword_of_int (uint sp0 - 16) : mword 64) Nsp)). }
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int (bp + 16) : mword 64))
      by (rewrite (Hpre a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hap).
    assert (Hsp_1 : m1 !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0) : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)))). }
    (* ---- 0x110e  addi a3,a0,-16 ---- *)
    assert (Ha3w : (mword_of_int bp : mword 64)
                   = add_vec (m1 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 4080 : mword 12))).
    { rewrite Ha0_1.
      assert (Hc : (sign_extend' 64 (mword_of_int 4080 : mword 12) : mword 64)
                   = mword_of_int (-16)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh M2 m1 (mword_of_int 0x110e)
              (mword_of_int 4080 : mword 12) a0_idx a3_idx (mword_of_int bp)
              (ui_sh_110e pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Ha3w
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (m2 := <[Regidx a3_idx := regval_into_reg (mword_of_int bp : mword 64)]> m1).
    assert (E110e : add_vec_int (mword_of_int 0x110e : mword 64) 4 = mword_of_int 0x1112)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E110e) in "Hpc".
    (* ---- 0x1112  auipc a5,0x1 ---- *)
    assert (Ha5w : (mword_of_int 8466 : mword 64)
                   = add_vec (mword_of_int 0x1112)
                       (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh M2 m2 (mword_of_int 0x1112)
              (mword_of_int 1 : mword 20) a5_idx (mword_of_int 8466)
              (ui_sh_1112 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Ha5w
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (m3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 8466 : mword 64)]> m2).
    assert (E1112 : add_vec_int (mword_of_int 0x1112 : mword 64) 4 = mword_of_int 0x1116)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1112) in "Hpc".
    (* ---- 0x1116  ld a5,-258(a5)  -- a5 = freep = &base ---- *)
    assert (Ha5_3 : m3 !!! Regidx a5_idx = (mword_of_int 8466 : mword 64))
      by exact (upd_eq m2 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 8466 : mword 64))).
    assert (Hva1 : (mword_of_int 8208 : mword 64)
                   = add_vec (m3 !!! Regidx a5_idx)
                       (sign_extend' 64 (mword_of_int 3838 : mword 12)))
      by (rewrite Ha5_3; apply bv_eq; vm_compute; reflexivity).
    assert (Hfreep2 : uM_bytes M2 8208 8 (mword_of_int 8328 : mword 64))
      by (intros j Hj; rewrite (HeqM2 (8208 + Z.of_nat j) ltac:(lia));
          exact (Hfreep j Hj)).
    destruct (acc8_facts M2 8208 8328 ltac:(lia) ltac:(vm_compute; reflexivity)
                ltac:(lia) Hfreep2)
      as (Hu1 & Hcn1 & Hpg1 & Hal1 & Hbe1 & Hwv1).
    destruct (data_leaf 8208 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wd1 & Hwd1 & Hwdl1 & Hwds1).
    iApply (wp_uv_ld C pt Psh M2 m3 (mword_of_int 0x1116)
              (mword_of_int 3838 : mword 12) a5_idx a5_idx
              wd1 (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_1116 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Hva1 Hwd1 Hwdl1 Hcn1 Hpg1 Hal1
              Hbe1 Hwv1
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m4 := <[Regidx a5_idx := regval_into_reg (mword_of_int 8328 : mword 64)]> m3).
    assert (E1116 : add_vec_int (mword_of_int 0x1116 : mword 64) 4 = mword_of_int 0x111a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1116) in "Hpc".
    (* the two long-lived registers, and what the head of the function left *)
    assert (Ha5_4 : m4 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by exact (upd_eq m3 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))).
    assert (Ha3_4 : m4 !!! Regidx a3_idx = (mword_of_int bp : mword 64)).
    { exact (eq_trans
               (upd_ne m3 (Regidx a5_idx) (Regidx a3_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m2 (Regidx a5_idx) (Regidx a3_idx)
                     (regval_into_reg (mword_of_int 8466 : mword 64))
                     ltac:(vm_compute; discriminate))
                  (upd_eq m1 (Regidx a3_idx)
                     (regval_into_reg (mword_of_int bp : mword 64))))). }
    assert (P4 : forall r : mword 5,
              Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a5_idx ->
              m4 !!! Regidx r = m1 !!! Regidx r).
    { intros r N3 N5.
      exact (eq_trans
               (upd_ne m3 (Regidx a5_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 8328 : mword 64)) N5)
               (eq_trans
                  (upd_ne m2 (Regidx a5_idx) (Regidx r)
                     (regval_into_reg (mword_of_int 8466 : mword 64)) N5)
                  (upd_ne m1 (Regidx a3_idx) (Regidx r)
                     (regval_into_reg (mword_of_int bp : mword 64)) N3))). }
    (* ---- 0x111a  c.j 0x1128 ---- *)
    assert (Htj : (mword_of_int 0x1128 : mword 64)
                  = add_vec (mword_of_int 0x111a)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 7 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cj C pt Psh M2 m4 (mword_of_int 0x111a)
              (mword_of_int 7 : mword 11) (mword_of_int 0x1128)
              (ui_sh_111a pt M2 Hl Htext2) Htj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    (* ---- 0x1128  bgeu a5,a3,0x111c -- NOT taken: &base is below bp ---- *)
    assert (Htk1 : false = uv_btaken BGEU (m4 !!! Regidx a5_idx) (m4 !!! Regidx a3_idx)).
    { cbn [uv_btaken]. rewrite Ha5_4 Ha3_4.
      rewrite (moi_ge_u 8328 bp ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uv_btype C pt Psh M2 m4 (mword_of_int 0x1128)
              (mword_of_int 8180 : mword 13) a3_idx a5_idx BGEU
              false (mword_of_int 0x111c)
              (ui_sh_1128 pt M2 Hl Htext2) Htk1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    assert (E1128 : (if false then (mword_of_int 0x111c : mword 64)
                     else add_vec_int (mword_of_int 0x1128 : mword 64) 4)
                    = mword_of_int 0x112c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1128) in "Hpc".
    (* ---- 0x112c  c.ld a4,0(a5)  -- a4 = base.s.ptr = &base ---- *)
    assert (Hbase2 : uM_bytes M2 8328 8 (mword_of_int 8328 : mword 64))
      by (intros j Hj; rewrite (HeqM2 (8328 + Z.of_nat j) ltac:(lia));
          exact (Hbaseptr j Hj)).
    destruct (acc8_facts M2 8328 8328 ltac:(lia) ltac:(vm_compute; reflexivity)
                ltac:(lia) Hbase2)
      as (Hu2 & Hcn2 & Hpg2 & Hal2 & Hbe2 & _).
    destruct (data_leaf 8328 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wd2 & Hwd2 & Hwdl2 & Hwds2).
    assert (Hbw2 : uM_bytes M2 (uint (mword_of_int 8328 : mword 64)) 8
                     (mword_of_int 8328 : mword 64)) by (rewrite Hu2; exact Hbase2).
    assert (Hva2 : (mword_of_int 8328 : mword 64)
                   = add_vec (m4 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Ha5_4; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cld C pt Psh M2 m4 (mword_of_int 0x112c)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 6 : mword 3) a5_idx a4_idx
              wd2 (mword_of_int 8328) (mword_of_int 8328)
              (ui_sh_112c pt M2 Hl Htext2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva2 Hwd2 Hwdl2 Hcn2 Hpg2 Hal2 Hbw2
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (m5 := <[Regidx a4_idx := regval_into_reg (mword_of_int 8328 : mword 64)]> m4).
    assert (E112c : add_vec_int (mword_of_int 0x112c : mword 64) 2 = mword_of_int 0x112e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E112c) in "Hpc".
    assert (Q5 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m5 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (upd_ne m4 (Regidx a4_idx) (Regidx r)
               (regval_into_reg (mword_of_int 8328 : mword 64)) N4). }
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 8328 : mword 64))
      by exact (upd_eq m4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))).
    assert (Ha3_5 : m5 !!! Regidx a3_idx = (mword_of_int bp : mword 64))
      by (rewrite (Q5 a3_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha3_4).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q5 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    (* ---- 0x112e  bltu a3,a4,0x1136 -- NOT taken ---- *)
    assert (Htk2 : false = uv_btaken BLTU (m5 !!! Regidx a3_idx) (m5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha3_5 Ha4_5.
      rewrite (moi_lt_u bp 8328 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uv_btype C pt Psh M2 m5 (mword_of_int 0x112e)
              (mword_of_int 8 : mword 13) a4_idx a3_idx BLTU
              false (mword_of_int 0x1136)
              (ui_sh_112e pt M2 Hl Htext2) Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    assert (E112e : (if false then (mword_of_int 0x1136 : mword 64)
                     else add_vec_int (mword_of_int 0x112e : mword 64) 4)
                    = mword_of_int 0x1132)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E112e) in "Hpc".
    (* ---- 0x1132  bltu a5,a4,0x1126 -- NOT taken (base is self-linked) ---- *)
    assert (Htk3 : false = uv_btaken BLTU (m5 !!! Regidx a5_idx) (m5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha5_5 Ha4_5.
      rewrite (moi_lt_u 8328 8328 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uv_btype C pt Psh M2 m5 (mword_of_int 0x1132)
              (mword_of_int 8180 : mword 13) a4_idx a5_idx BLTU
              false (mword_of_int 0x1126)
              (ui_sh_1132 pt M2 Hl Htext2) Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    assert (E1132 : (if false then (mword_of_int 0x1126 : mword 64)
                     else add_vec_int (mword_of_int 0x1132 : mword 64) 4)
                    = mword_of_int 0x1136)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1132) in "Hpc".
    (* ---- 0x1136  lw a1,-8(a0)  -- a1 = bp->s.size = nu ---- *)
    assert (Ha0_5 : m5 !!! Regidx a0_idx = (mword_of_int (bp + 16) : mword 64)).
    { rewrite (Q5 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (P4 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Ha0_1. }
    assert (Hva3 : (mword_of_int (bp + 8) : mword 64)
                   = add_vec (m5 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 4088 : mword 12))).
    { rewrite Ha0_5.
      assert (Hc : (sign_extend' 64 (mword_of_int 4088 : mword 12) : mword 64)
                   = mword_of_int (-8)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    (* [bp->s.size] is a C [uint]: FOUR bytes, exactly what the [lw] reads *)
    assert (Hbpsz2 : uM_bytes M2 (bp + 8) 4 (mword_of_int nu : mword 32))
      by (intros j Hj; rewrite (HeqM2 (bp + 8 + Z.of_nat j) ltac:(lia));
          exact (Hbpsz j Hj)).
    destruct (uv_slot4_facts (bp + 8) (mword_of_int (bp + 8)) ltac:(lia) ltac:(lia)
                ltac:(lia) eq_refl) as (Hu3 & Hcn3 & Hpg3 & Hal3).
    assert (Hbw3 : uM_bytes M2 (uint (mword_of_int (bp + 8) : mword 64)) 4
                     (mword_of_int nu : mword 32))
      by (rewrite Hu3; exact Hbpsz2).
    destruct (heap_leaf (bp + 8) Hlay ltac:(lia)) as (wh1 & Hwh1 & Hwhl1 & Hwhs1).
    iApply (wp_uv_lw C pt Psh M2 m5 (mword_of_int 0x1136)
              (mword_of_int 4088 : mword 12) a0_idx a1_idx
              wh1 (mword_of_int (bp + 8)) (mword_of_int nu) (mword_of_int nu)
              (ui_sh_1136 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Hva3 Hwh1 Hwhl1 Hcn3 Hpg3 Hal3 Hbw3
              ltac:(symmetry; apply sext32_moi; change (2 ^ 31) with 2147483648; lia)
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (m6 := <[Regidx a1_idx := regval_into_reg (mword_of_int nu : mword 64)]> m5).
    assert (E1136 : add_vec_int (mword_of_int 0x1136 : mword 64) 4 = mword_of_int 0x113a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1136) in "Hpc".
    assert (Q6 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m6 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m5 (Regidx a1_idx) (Regidx r)
                  (regval_into_reg (mword_of_int nu : mword 64)) N1)
               (Q5 r N1 N2 N4 N6)). }
    (* ---- 0x113a  c.ld a2,0(a5)  -- a2 = p->s.ptr = &base ---- *)
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q6 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hva4 : (mword_of_int 8328 : mword 64)
                   = add_vec (m6 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Ha5_6; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cld C pt Psh M2 m6 (mword_of_int 0x113a)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 4 : mword 3) a5_idx a2_idx
              wd2 (mword_of_int 8328) (mword_of_int 8328)
              (ui_sh_113a pt M2 Hl Htext2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva4 Hwd2 Hwdl2 Hcn2 Hpg2 Hal2 Hbw2
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (m7 := <[Regidx a2_idx := regval_into_reg (mword_of_int 8328 : mword 64)]> m6).
    assert (E113a : add_vec_int (mword_of_int 0x113a : mword 64) 2 = mword_of_int 0x113c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E113a) in "Hpc".
    assert (Q7 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m7 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m6 (Regidx a2_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 8328 : mword 64)) N2)
               (Q6 r N1 N2 N4 N6)). }
    (* ---- 0x113c  slli a6,a1,0x20 ---- *)
    assert (Ha1_7 : m7 !!! Regidx a1_idx = (mword_of_int nu : mword 64)).
    { exact (eq_trans
               (upd_ne m6 (Regidx a2_idx) (Regidx a1_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))
                  ltac:(vm_compute; discriminate))
               (upd_eq m5 (Regidx a1_idx)
                  (regval_into_reg (mword_of_int nu : mword 64)))). }
    assert (Hshl1 : (mword_of_int (nu * 2 ^ 32) : mword 64)
                    = shift_bits_left (m7 !!! Regidx a1_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))
      by (rewrite Ha1_7; symmetry; exact (moi_shl nu 32 ltac:(lia))).
    iApply (wp_uv_slli C pt Psh M2 m7 (mword_of_int 0x113c)
              (mword_of_int 32 : mword 6) a1_idx a6_idx (mword_of_int (nu * 2 ^ 32))
              (ui_sh_113c pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Hshl1
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (m8 := <[Regidx a6_idx
                 := regval_into_reg (mword_of_int (nu * 2 ^ 32) : mword 64)]> m7).
    assert (E113c : add_vec_int (mword_of_int 0x113c : mword 64) 4 = mword_of_int 0x1140)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E113c) in "Hpc".
    assert (Q8 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m8 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m7 (Regidx a6_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (nu * 2 ^ 32) : mword 64)) N6)
               (Q7 r N1 N2 N4 N6)). }
    (* ---- 0x1140  srli a4,a6,0x1c  -- a4 = 16 * nu ---- *)
    assert (Ha6_8 : m8 !!! Regidx a6_idx = (mword_of_int (nu * 2 ^ 32) : mword 64))
      by exact (upd_eq m7 (Regidx a6_idx)
                  (regval_into_reg (mword_of_int (nu * 2 ^ 32) : mword 64))).
    assert (Hshr1 : (mword_of_int (16 * nu) : mword 64)
                    = shift_bits_right (m8 !!! Regidx a6_idx)
                        (subrange_vec_dec (mword_of_int 28 : mword 6)
                           (Z.sub log2_xlen 1) 0)).
    { rewrite Ha6_8.
      rewrite (moi_shr (nu * 2 ^ 32) 28 ltac:(lia)
                 ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
      rewrite moi_scale16. f_equal; lia. }
    iApply (wp_uv_srli C pt Psh M2 m8 (mword_of_int 0x1140)
              (mword_of_int 28 : mword 6) a6_idx a4_idx (mword_of_int (16 * nu))
              (ui_sh_1140 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Hshr1
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (16 * nu) : mword 64)]> m8).
    assert (E1140 : add_vec_int (mword_of_int 0x1140 : mword 64) 4 = mword_of_int 0x1144)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1140) in "Hpc".
    assert (Q9 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m9 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m8 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (16 * nu) : mword 64)) N4)
               (Q8 r N1 N2 N4 N6)). }
    (* ---- 0x1144  c.add a4,a4,a3  -- a4 = bp + 16*nu ---- *)
    assert (Ha4_9 : m9 !!! Regidx a4_idx = (mword_of_int (16 * nu) : mword 64))
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (16 * nu) : mword 64))).
    assert (Ha3_9 : m9 !!! Regidx a3_idx = (mword_of_int bp : mword 64))
      by (rewrite (Q9 a3_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha3_4).
    assert (Hadd1 : (mword_of_int (bp + 16 * nu) : mword 64)
                    = add_vec (m9 !!! Regidx a4_idx) (m9 !!! Regidx a3_idx))
      by (rewrite Ha4_9 Ha3_9 moi_add; f_equal; lia).
    iApply (wp_uv_cadd C pt Psh M2 m9 (mword_of_int 0x1144)
              a4_idx a3_idx (mword_of_int (bp + 16 * nu))
              (ui_sh_1144 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate) Hadd1
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (m10 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int (bp + 16 * nu) : mword 64)]> m9).
    assert (E1144 : add_vec_int (mword_of_int 0x1144 : mword 64) 2 = mword_of_int 0x1146)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1144) in "Hpc".
    assert (Q10 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m10 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m9 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bp + 16 * nu) : mword 64)) N4)
               (Q9 r N1 N2 N4 N6)). }
    (* ---- 0x1146  beq a2,a4,0x1170 -- NOT taken: &base is below the heap ---- *)
    assert (Ha4_10 : m10 !!! Regidx a4_idx = (mword_of_int (bp + 16 * nu) : mword 64))
      by exact (upd_eq m9 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bp + 16 * nu) : mword 64))).
    assert (Ha2_10 : m10 !!! Regidx a2_idx = (mword_of_int 8328 : mword 64)).
    { exact (eq_trans
               (upd_ne m9 (Regidx a4_idx) (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (bp + 16 * nu) : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m8 (Regidx a4_idx) (Regidx a2_idx)
                     (regval_into_reg (mword_of_int (16 * nu) : mword 64))
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne m7 (Regidx a6_idx) (Regidx a2_idx)
                        (regval_into_reg (mword_of_int (nu * 2 ^ 32) : mword 64))
                        ltac:(vm_compute; discriminate))
                     (upd_eq m6 (Regidx a2_idx)
                        (regval_into_reg (mword_of_int 8328 : mword 64)))))). }
    assert (Htk4 : false = uv_btaken BEQ (m10 !!! Regidx a2_idx) (m10 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha2_10 Ha4_10.
      rewrite (moi_eq_vec 8328 (bp + 16 * nu) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uv_btype C pt Psh M2 m10 (mword_of_int 0x1146)
              (mword_of_int 42 : mword 13) a4_idx a2_idx BEQ
              false (mword_of_int 0x1170)
              (ui_sh_1146 pt M2 Hl Htext2) Htk4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    assert (E1146 : (if false then (mword_of_int 0x1170 : mword 64)
                     else add_vec_int (mword_of_int 0x1146 : mword 64) 4)
                    = mword_of_int 0x114a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1146) in "Hpc".
    (* ---- 0x114a  sd a2,-16(a0)  -- bp->s.ptr = &base ---- *)
    assert (Ha0_10 : m10 !!! Regidx a0_idx = (mword_of_int (bp + 16) : mword 64)).
    { rewrite (Q10 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (P4 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Ha0_1. }
    assert (Hva5 : (mword_of_int bp : mword 64)
                   = add_vec (m10 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 4080 : mword 12))).
    { rewrite Ha0_10.
      assert (Hc : (sign_extend' 64 (mword_of_int 4080 : mword 12) : mword 64)
                   = mword_of_int (-16)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_slot8_facts bp (mword_of_int bp) ltac:(lia) ltac:(lia) ltac:(lia)
                eq_refl) as (Hubp & Hcnbp & Hpgbp & Halbp).
    destruct (heap_leaf bp Hlay ltac:(lia)) as (wh2 & Hwh2 & Hwhl2 & Hwhs2).
    assert (Hbebp : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (mword_of_int bp : mword 64) + Z.of_nat j) = Some b).
    { intros j Hj. rewrite Hubp.
      destruct (uwr_bytes _ _ _ _ Hheapw (Z.of_nat j) ltac:(lia)) as (b & Hb).
      exact (Hdom2 (bp + Z.of_nat j) (mk_is_Some _ _ Hb)). }
    iApply (wp_uv_sd C pt Psh M2 m10 (mword_of_int 0x114a)
              (mword_of_int 4080 : mword 12) a0_idx a2_idx
              wh2 (mword_of_int bp) (mword_of_int 8328)
              (ui_sh_114a pt M2 Hl Htext2)
              Hva5 (eq_sym Ha2_10) Hwh2 Hwhs2 Hcnbp Hpgbp Halbp Hbebp
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    iEval (rewrite Hubp) in "Hcg".
    set (M3 := uM_store8 M2 bp (mword_of_int 8328 : mword 64)).
    assert (Htext3 : sh_text_sub M3)
      by (unfold M3; apply sh_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hne3 : forall k : Z, (k < bp \/ bp + 8 <= k) -> M3 !! k = M2 !! k)
      by (intros k Hk; unfold M3; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E114a : add_vec_int (mword_of_int 0x114a : mword 64) 4 = mword_of_int 0x114e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E114a) in "Hpc".
    (* ---- 0x114e  c.lw a2,8(a5)  -- a2 = base.s.size = 0 ---- *)
    assert (Ha5_10 : m10 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q10 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hva6 : (mword_of_int 8336 : mword 64)
                   = add_vec (m10 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 2 : mword 5) ('b"00")))))
      by (rewrite Ha5_10; apply bv_eq; vm_compute; reflexivity).
    assert (Hbsz3 : uM_bytes M3 8336 8 (mword_of_int 0 : mword 64)).
    { intros j Hj.
      rewrite (Hne3 (8336 + Z.of_nat j) ltac:(lia)).
      rewrite (HeqM2 (8336 + Z.of_nat j) ltac:(lia)).
      replace (8336 + Z.of_nat j) with (8328 + 8 + Z.of_nat j) by lia.
      exact (Hbasesz j Hj). }
    destruct (uv_slot4_facts 8336 (mword_of_int 8336) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hu4 & Hcn4 & Hpg4 & Hal4).
    assert (Hbw4 : uM_bytes M3 (uint (mword_of_int 8336 : mword 64)) 4
                     (mword_of_int 0 : mword 32))
      by (rewrite Hu4; exact (uM_bytes_4_of_8 M3 8336 0 Hbsz3)).
    destruct (data_leaf 8336 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wd3 & Hwd3 & Hwdl3 & Hwds3).
    iApply (wp_uv_clw C pt Psh M3 m10 (mword_of_int 0x114e)
              (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 4 : mword 3) a5_idx a2_idx
              wd3 (mword_of_int 8336) (mword_of_int 0) (mword_of_int 0)
              (ui_sh_114e pt M3 Hl Htext3)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva6 Hwd3 Hwdl3 Hcn4 Hpg4 Hal4 Hbw4
              ltac:(symmetry; apply sext32_moi; lia)
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    set (m11 := <[Regidx a2_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m10).
    assert (E114e : add_vec_int (mword_of_int 0x114e : mword 64) 2 = mword_of_int 0x1150)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E114e) in "Hpc".
    assert (Q11 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m11 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m10 (Regidx a2_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 0 : mword 64)) N2)
               (Q10 r N1 N2 N4 N6)). }
    (* ---- 0x1150  slli a1,a2,0x20 ---- *)
    assert (Ha2_11 : m11 !!! Regidx a2_idx = (mword_of_int 0 : mword 64))
      by exact (upd_eq m10 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0 : mword 64))).
    assert (Hshl2 : (mword_of_int (0 * 2 ^ 32) : mword 64)
                    = shift_bits_left (m11 !!! Regidx a2_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))
      by (rewrite Ha2_11; symmetry; exact (moi_shl 0 32 ltac:(lia))).
    iApply (wp_uv_slli C pt Psh M3 m11 (mword_of_int 0x1150)
              (mword_of_int 32 : mword 6) a2_idx a1_idx (mword_of_int (0 * 2 ^ 32))
              (ui_sh_1150 pt M3 Hl Htext3)
              ltac:(vm_compute; discriminate) Hshl2
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    set (m12 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int (0 * 2 ^ 32) : mword 64)]> m11).
    assert (E1150 : add_vec_int (mword_of_int 0x1150 : mword 64) 4 = mword_of_int 0x1154)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1150) in "Hpc".
    assert (Q12 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m12 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m11 (Regidx a1_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (0 * 2 ^ 32) : mword 64)) N1)
               (Q11 r N1 N2 N4 N6)). }
    (* ---- 0x1154  srli a4,a1,0x1c  -- a4 = 16 * base.s.size = 0 ---- *)
    assert (Ha1_12 : m12 !!! Regidx a1_idx = (mword_of_int (0 * 2 ^ 32) : mword 64))
      by exact (upd_eq m11 (Regidx a1_idx)
                  (regval_into_reg (mword_of_int (0 * 2 ^ 32) : mword 64))).
    assert (Hshr2 : (mword_of_int 0 : mword 64)
                    = shift_bits_right (m12 !!! Regidx a1_idx)
                        (subrange_vec_dec (mword_of_int 28 : mword 6)
                           (Z.sub log2_xlen 1) 0)).
    { rewrite Ha1_12.
      rewrite (moi_shr (0 * 2 ^ 32) 28 ltac:(lia)
                 ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
      rewrite moi_scale16. f_equal; lia. }
    iApply (wp_uv_srli C pt Psh M3 m12 (mword_of_int 0x1154)
              (mword_of_int 28 : mword 6) a1_idx a4_idx (mword_of_int 0)
              (ui_sh_1154 pt M3 Hl Htext3)
              ltac:(vm_compute; discriminate) Hshr2
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    set (m13 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m12).
    assert (E1154 : add_vec_int (mword_of_int 0x1154 : mword 64) 4 = mword_of_int 0x1158)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1154) in "Hpc".
    assert (Q13 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m13 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m12 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 0 : mword 64)) N4)
               (Q12 r N1 N2 N4 N6)). }
    (* ---- 0x1158  c.add a4,a4,a5  -- a4 = p + p->s.size = &base ---- *)
    assert (Ha4_13 : m13 !!! Regidx a4_idx = (mword_of_int 0 : mword 64))
      by exact (upd_eq m12 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0 : mword 64))).
    assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q13 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hadd2 : (mword_of_int 8328 : mword 64)
                    = add_vec (m13 !!! Regidx a4_idx) (m13 !!! Regidx a5_idx))
      by (rewrite Ha4_13 Ha5_13 moi_add; f_equal; lia).
    iApply (wp_uv_cadd C pt Psh M3 m13 (mword_of_int 0x1158)
              a4_idx a5_idx (mword_of_int 8328)
              (ui_sh_1158 pt M3 Hl Htext3)
              ltac:(vm_compute; discriminate) Hadd2
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    set (m14 := <[Regidx a4_idx := regval_into_reg (mword_of_int 8328 : mword 64)]> m13).
    assert (E1158 : add_vec_int (mword_of_int 0x1158 : mword 64) 2 = mword_of_int 0x115a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1158) in "Hpc".
    assert (Q14 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m14 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m13 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 8328 : mword 64)) N4)
               (Q13 r N1 N2 N4 N6)). }
    (* ---- 0x115a  beq a3,a4,0x117e -- NOT taken: bp is not &base ---- *)
    assert (Ha4_14 : m14 !!! Regidx a4_idx = (mword_of_int 8328 : mword 64))
      by exact (upd_eq m13 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))).
    assert (Ha3_14 : m14 !!! Regidx a3_idx = (mword_of_int bp : mword 64))
      by (rewrite (Q14 a3_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha3_4).
    assert (Ha5_14 : m14 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q14 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Htk5 : false = uv_btaken BEQ (m14 !!! Regidx a3_idx) (m14 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha3_14 Ha4_14.
      rewrite (moi_eq_vec bp 8328 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uv_btype C pt Psh M3 m14 (mword_of_int 0x115a)
              (mword_of_int 36 : mword 13) a4_idx a3_idx BEQ
              false (mword_of_int 0x117e)
              (ui_sh_115a pt M3 Hl Htext3) Htk5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID21) "Hcg Hpc".
    assert (E115a : (if false then (mword_of_int 0x117e : mword 64)
                     else add_vec_int (mword_of_int 0x115a : mword 64) 4)
                    = mword_of_int 0x115e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E115a) in "Hpc".
    (* ---- 0x115e  c.sd a3,0(a5)  -- base.s.ptr = bp ---- *)
    assert (Hva7 : (mword_of_int 8328 : mword 64)
                   = add_vec (m14 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Ha5_14; apply bv_eq; vm_compute; reflexivity).
    assert (Hbe2' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M3 !! (uint (mword_of_int 8328 : mword 64) + Z.of_nat j) = Some b).
    { intros j Hj. rewrite Hu2. rewrite (Hne3 (8328 + Z.of_nat j) ltac:(lia)).
      rewrite Hu2 in Hbe2. exact (Hbe2 j Hj). }
    iApply (wp_uv_csd C pt Psh M3 m14 (mword_of_int 0x115e)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 5 : mword 3) a5_idx a3_idx
              wd2 (mword_of_int 8328) (mword_of_int bp)
              (ui_sh_115e pt M3 Hl Htext3)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva7 (eq_sym Ha3_14) Hwd2 Hwds2 Hcn2 Hpg2 Hal2 Hbe2'
              with "Hcg Hpc").
    iIntros (CID22) "Hcg Hpc".
    iEval (rewrite Hu2) in "Hcg".
    set (M4 := uM_store8 M3 8328 (mword_of_int bp : mword 64)).
    assert (Htext4 : sh_text_sub M4)
      by (unfold M4; apply sh_text_sub_store8; [ exact Htext3 | lia ]).
    assert (Hne4 : forall k : Z, (k < 8328 \/ 8336 <= k) -> M4 !! k = M3 !! k)
      by (intros k Hk; unfold M4; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E115e : add_vec_int (mword_of_int 0x115e : mword 64) 2 = mword_of_int 0x1160)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E115e) in "Hpc".
    (* ---- 0x1160  auipc a4,0x1 ---- *)
    assert (Ha4w : (mword_of_int 8544 : mword 64)
                   = add_vec (mword_of_int 0x1160)
                       (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh M4 m14 (mword_of_int 0x1160)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 8544)
              (ui_sh_1160 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Ha4w
              with "Hcg Hpc").
    iIntros (CID23) "Hcg Hpc".
    set (m15 := <[Regidx a4_idx := regval_into_reg (mword_of_int 8544 : mword 64)]> m14).
    assert (E1160 : add_vec_int (mword_of_int 0x1160 : mword 64) 4 = mword_of_int 0x1164)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1160) in "Hpc".
    assert (Q15 : forall r : mword 5,
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a6_idx ->
              m15 !!! Regidx r = m4 !!! Regidx r).
    { intros r N1 N2 N4 N6.
      exact (eq_trans
               (upd_ne m14 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int 8544 : mword 64)) N4)
               (Q14 r N1 N2 N4 N6)). }
    (* ---- 0x1164  sd a5,-336(a4)  -- freep = &base ---- *)
    assert (Ha4_15 : m15 !!! Regidx a4_idx = (mword_of_int 8544 : mword 64))
      by exact (upd_eq m14 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 8544 : mword 64))).
    assert (Ha5_15 : m15 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (Q15 a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hva8 : (mword_of_int 8208 : mword 64)
                   = add_vec (m15 !!! Regidx a4_idx)
                       (sign_extend' 64 (mword_of_int 3760 : mword 12)))
      by (rewrite Ha4_15; apply bv_eq; vm_compute; reflexivity).
    assert (Hbe1' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M4 !! (uint (mword_of_int 8208 : mword 64) + Z.of_nat j) = Some b).
    { intros j Hj. rewrite Hu1.
      rewrite (Hne4 (8208 + Z.of_nat j) ltac:(lia)).
      rewrite (Hne3 (8208 + Z.of_nat j) ltac:(lia)).
      rewrite Hu1 in Hbe1. exact (Hbe1 j Hj). }
    iApply (wp_uv_sd C pt Psh M4 m15 (mword_of_int 0x1164)
              (mword_of_int 3760 : mword 12) a4_idx a5_idx
              wd1 (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_1164 pt M4 Hl Htext4)
              Hva8 (eq_sym Ha5_15) Hwd1 Hwds1 Hcn1 Hpg1 Hal1 Hbe1'
              with "Hcg Hpc").
    iIntros (CID24) "Hcg Hpc".
    iEval (rewrite Hu1) in "Hcg".
    set (M5 := uM_store8 M4 8208 (mword_of_int 8328 : mword 64)).
    assert (Htext5 : sh_text_sub M5)
      by (unfold M5; apply sh_text_sub_store8; [ exact Htext4 | lia ]).
    assert (Hne5 : forall k : Z, (k < 8208 \/ 8216 <= k) -> M5 !! k = M4 !! k)
      by (intros k Hk; unfold M5; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1164 : add_vec_int (mword_of_int 0x1164 : mword 64) 4 = mword_of_int 0x1168)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1164) in "Hpc".
    (* ---- the epilogue.  The three stores are all far below the frame. ---- *)
    assert (HeqM5 : forall k : Z, uint sp0 - 16 <= k -> M5 !! k = M2 !! k).
    { intros k Hk.
      rewrite (Hne5 k ltac:(lia)). rewrite (Hne4 k ltac:(lia)).
      exact (Hne3 k ltac:(lia)). }
    assert (Hdom5 : forall k : Z, is_Some (M2 !! k) -> is_Some (M5 !! k)).
    { intros k Hk. unfold M5, M4, M3.
      exact (uM_store8_is_Some _ _ _ k
               (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk))). }
    assert (Hst5 : uv_stack pt M5 sp0 16)
      by exact (uv_stack_dom pt M2 M5 sp0 16 Hdom5 Hst2).
    assert (Hby8' : uM_bytes M5 (uint sp0 - 8) 8 (m !!! Regidx ra_idx))
      by (intros j Hj; rewrite (HeqM5 (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
          exact (Hby8 j Hj)).
    assert (Hby0' : uM_bytes M5 (uint sp0 - 16) 8 (m !!! Regidx s0_idx))
      by (intros j Hj; rewrite (HeqM5 (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
          exact (Hby0 j Hj)).
    assert (Hsp_15 : m15 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 16) : mword 64)).
    { rewrite (Q15 sp_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (P4 sp_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hsp_1. }
    iApply (wp_uv_epilogue16 C pt CID24 Psh 0x1168 M5 m15 sp0
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
              Hst5 Hret2 Hsp_15
              (uM_word_w8 M5 (uint sp0 - 8) _ Hby8')
              (uM_word_w8 M5 (uint sp0 - 16) _ Hby0')
              (ui_sh_1168 pt M5 Hl Htext5)
              (ui_sh_116a pt M5 Hl Htext5)
              (ui_sh_116c pt M5 Hl Htext5)
              (ui_sh_116e pt M5 Hl Htext5)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID25 m') "%HA %HB %HC Hcg Hpc".
    (* ---- the four cells the caller is promised ---- *)
    assert (Rbase : uM_bytes M5 8328 8 (mword_of_int bp : mword 64)).
    { intros j Hj. rewrite (Hne5 (8328 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M3 8328 (mword_of_int bp : mword 64) j Hj). }
    assert (Rbp : uM_bytes M5 bp 8 (mword_of_int 8328 : mword 64)).
    { intros j Hj. rewrite (Hne5 (bp + Z.of_nat j) ltac:(lia)).
      rewrite (Hne4 (bp + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M2 bp (mword_of_int 8328 : mword 64) j Hj). }
    assert (Rsz : uM_bytes M5 (bp + 8) 4 (mword_of_int nu : mword 32)).
    { intros j Hj. rewrite (Hne5 (bp + 8 + Z.of_nat j) ltac:(lia)).
      rewrite (Hne4 (bp + 8 + Z.of_nat j) ltac:(lia)).
      rewrite (Hne3 (bp + 8 + Z.of_nat j) ltac:(lia)).
      exact (Hbpsz2 j Hj). }
    assert (Rfreep : uM_bytes M5 8208 8 (mword_of_int 8328 : mword 64))
      by exact (uM_store8_bytes M4 8208 (mword_of_int 8328 : mword 64)).
    iApply ("Hcont" $! CID25 m' M5 with "[] [] [] [] [] [] Hcg Hpc").
    - iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
      { rewrite Esp HA. symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
      { rewrite Es0 HB. reflexivity. }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N3 : Regidx r <> Regidx a3_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (N6 : Regidx r <> Regidx a6_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HC r Nra Nsp Ns0). rewrite (Q15 r N1 N2 N4 N6).
      rewrite (P4 r N3 N5). exact (Hpre r Nsp Ns0).
    - iPureIntro. exact Rbase.
    - iPureIntro. exact Rbp.
    - iPureIntro. exact Rsz.
    - iPureIntro. exact Rfreep.
    - iPureIntro. split.
      + intros k Hk. exact (Hdom5 k (Hdom2 k Hk)).
      + intros k Hk.
        pose proof (not_in_window _ (uint sp0 - 16) 16 k
                      ltac:(apply elem_of_list_here) Hk) as W1.
        pose proof (not_in_window _ 8208 8 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk)
          as W2.
        pose proof (not_in_window _ 8328 16 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_here) Hk) as W3.
        pose proof (not_in_window _ bp 16 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here) Hk)
          as W4.
        rewrite (Hne5 k ltac:(lia)). rewrite (Hne4 k ltac:(lia)).
        rewrite (Hne3 k ltac:(lia)).
        exact (proj2 Honly k ltac:(lia)).
  Qed.

End UProofShMem.
