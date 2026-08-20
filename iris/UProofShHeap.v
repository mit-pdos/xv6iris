(* UProofShHeap.v -- the VERIFIED-EXECUTION proofs of the `sh` program's two
   ALLOCATOR functions (claude-notes/projects/user-sh.md):

     wp_sh_malloc_first  malloc  @0x118c  FIRST CALL ONLY (freep == 0)
     wp_sh_execcmd       execcmd @0x1d2   malloc(168); memset; type = EXEC

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v, fed the matching
   [ui_sh_<hexpc>] fact from UCodeSh.v.  Every leaf continuation re-binds the
   hart ([forall CID]), which is why every lemma here takes [CIDp] as an
   EXPLICIT leading binder rather than a section variable.

   malloc does NOT have the tier's 16-byte gcc frame: its frame is 64 bytes
   and it spills s1/s4/s5/s6 CONDITIONALLY, on two different paths (0x11bc
   and 0x11e2), so [UmodeFrame.wp_uv_prologue16] does not apply and the
   eleven frame instructions are written out.

   ==================================================================
   DRIFT -- what these proofs assume ON TOP of USpecSh.v, and why.
   Reported rather than patched (USpecSh.v is not edited here).
   ==================================================================

   D1..D4, reported from the first pass of this proof, are all FIXED in
   USpecSh.v and this file is resynced to them: [wp_sh_free_first_body]'s
   header-size field is FOUR bytes (a C [uint], written by [sw] at 0x1208
   and read by [lw] at 0x1136 -- the union's other four bytes are padding
   that nothing writes and [uM_grown] does not constrain);
   [wp_sh_malloc_first_body] carries the .bss premises rather than a
   bare [freep = 0];
   [wp_sh_execcmd_body] carries [sh_frame_ok … 128] and states its image
   effect.

   (D5), found while resyncing to that fix and since fixed as well:
   [wp_sh_free_first_body] briefly carried

       (Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)

   -- on FREE's ENTRY image, where it is REFUTABLE.  free is called from
   [morecore], i.e. after malloc's own head has already written the two
   .bss cells the premise quantifies over (0x11f6 [freep := &base],
   0x11fa [base.s.ptr := &base]), so M[8208] is the low byte of 8328.
   What free actually needs about [base.s.size] is its own [Hbasesz], and
   THAT is what malloc's head establishes from its own .bss premises.
   Recorded here
   because of the shape of the bug rather than the bug: an UNSATISFIABLE
   PREMISE is the mirror of a hedged conjunct -- it is invisible to the
   callee's own proof, which compiles fine with one more unused
   hypothesis, and only the CALLER ever discovers the lemma has gone
   vacuous.

   (D6), found by the parser lane and fixed in USpecSh.v / USpecShParse.v:
   [Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88] was the WRONG PREMISE
   for malloc and execcmd, for the same reason one level up.  Its range
   0x2010..0x2098 COVERS `buf.0' at 0x2020, so it asserts the command
   buffer is all zeros -- true on entry to main, and FALSE at the only
   site that ever calls malloc, since [parseexec] reaches it after [gets]
   has filled that buffer with the command.  Both lemmas were correct and
   UNUSABLE.  What the proof actually consumes is two eight-byte windows
   and nothing between them: offsets [0,8) for [freep == 0], and offsets
   [128,136) -- [base.s.size] plus the four padding bytes above it, which
   no instruction writes -- for the rescan.  Those two are now the
   premises ([Hfreep0], [Hbasesz0]).  [main] and [start] keep the
   whole-.bss claim, which is where it is true and where it belongs.

   The general shape, now three times over in this file alone: a premise
   that is perfectly satisfiable IN ISOLATION can still be refutable AT
   THE CALL SITE, and nothing in the callee's own build -- not the
   compiler, not [Print Assumptions] -- can see it.  Only writing the
   caller finds it.

   NOT drift, checked and correct: the window list of
   [wp_sh_malloc_first_body] covers what the code writes.  malloc's own
   frame is [sp0-64, sp0); free and sbrk are BOTH called at sp = sp0-64 and
   so share the frame [sp0-80, sp0-64); the stated [sh_win (uint sp0-96) 96]
   contains both with 16 bytes to spare.  The heap window, [SH_FREEP] and
   [SH_BASE] are exact. *)
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
Require Import AlignBits.
Require Import RiscvModelBytes.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh.
Require Import UProofShLib UProofShMem.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* re-imported LAST on purpose: WpUmodeStep.v's funnel names its optional
   gpr write [uv_wr], which otherwise shadows UmodeAbi's writable-window
   record of the same name. *)
Require Import UmodeAbi.
Require User.ShSyms User.ShInstrs User.ShData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The pure shims.                                                     *)
(*                                                                        *)
(* HOIST CANDIDATES, every one -- none of them exists upstream yet.        *)
(* [sh_text_sub_store8] is now in its THIRD copy (UProofShLib.v,           *)
(* UProofShMem.v, here) and [sh_text_sub_store4] its first; both belong    *)
(* beside [sh_bytes_key_lt] in UCodeSh.v.  The byte-width calculus         *)
(* ([z_byte_mod], [nth_byte_moi_4], [uM_bytes_4_of_8], [uM_bytes_4_of_4],  *)
(* [nth_byte_moi0]) is what EVERY access to a C [uint] field needs now     *)
(* that the allocator's header is correctly typed, and belongs in          *)
(* UmodeArith.v / UmodeMem.v.                                             *)
(* ===================================================================== *)

Local Lemma sh_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma sh_text_sub_store4 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store M a 4 v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store_lookup_ne M a 4 v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* a byte of a normalized value does not depend on the width, as long as
   the byte is inside the narrow word -- what lets a 4-byte [lw]/[sw] of a
   C [uint] field meet an 8-byte [uM_bytes] premise, and back. *)
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

Local Lemma uM_bytes_4_of_4 (M : gmap Z (bv 8)) (a z : Z) :
  uM_bytes M a 4 (mword_of_int z : mword 64) ->
  uM_bytes M a 4 (mword_of_int z : mword 32).
Proof.
  intros H j Hj. rewrite (nth_byte_moi_4 z j Hj). exact (H j Hj).
Qed.

(* the zero byte, as [mword_of_int 0] spells it at any index *)
Local Lemma nth_byte_moi0 (j : nat) :
  nth_byte (mword_of_int 0 : mword 64) j = ubyte0.
Proof.
  apply bv_eq. rewrite nth_byte_unsigned moi_unsigned.
  replace (0 mod Z64) with 0 by (vm_compute; reflexivity).
  rewrite Z.shiftr_0_l.
  assert (E : bv_unsigned ubyte0 = 0) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

(* gcc's `zero-extend a uint field and scale by 16' idiom *)
Local Lemma moi_scale16 (z : Z) :
  (mword_of_int (z * 2 ^ 32 / 2 ^ 28) : mword 64) = mword_of_int (z * 16).
Proof.
  f_equal.
  replace (2 ^ 32) with (16 * 2 ^ 28) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc. apply Z.div_mul. vm_compute; discriminate.
Qed.

Section UProofShHeap.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §2 The leaf-side plumbing, copied from UProofShMem.v (all [Local]     *)
  (* there).  HOIST CANDIDATES, every one.                                *)
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

  (* everything an 8-byte ACCESS at a closed 8-aligned address needs, off
     ONE [uM_bytes] premise *)
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


  (* x0 reads as zero -- what a `sw zero, imm(rs1)' needs about its SOURCE.
     [WpUmodeLeaf.wp_uv_li] and [WpUmodeBranch.wp_uv_btype0] now solve this
     for the two ALU/branch cases upstream, and this file uses them; the
     STORE case has no upstream counterpart, so 0x11fc (`sw zero,8(a5)',
     base.s.size = 0) still needs this.  HOIST CANDIDATE: a [wp_uv_sw0] /
     [wp_uv_store0] beside the store leaves in WpUmodeStore.v would retire
     it and this would be the last local x0 shim in the tier. *)
  Local Lemma uv_x0 (CIDx : CpuId) (Mx : gmap Z (bv 8)) (mx : regfile) :
    uv_cap_gpr (CID := CIDx) C pt Psh Mx mx -∗
    ⌜mx !!! Regidx (mword_of_int 0 : mword 5) = zero_reg⌝ ∗
    uv_cap_gpr (CID := CIDx) C pt Psh Mx mx.
  Proof.
    iIntros "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 mx (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hgpr") as "[%Hz Hgpr]".
    iSplitR; [ iPureIntro; exact Hz | ].
    rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §3b malloc's JOIN, from 0x125c: `freep = prevp; return p + 1',        *)
  (* then the 64-byte frame back.  Both arms of the [beq s2,a4] at 0x1244  *)
  (* -- the exact-fit case and the split case -- land here with the same   *)
  (* [a0] (= &base) and the same [a5] (= the block that is being handed    *)
  (* out), so the nine instructions are written once.                      *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_malloc_join (CIDp : CpuId)
      (M MJ : gmap Z (bv 8)) (m mJ : regfile) (sp0 : mword 64) (nbytes : Z)
      (vra vs0 vs2 vs3 : mword 64) :
    sh_layout pt hbase hlen ->
    sh_text_sub MJ ->
    uv_stack pt MJ sp0 96 ->
    2 <= sh_nunits nbytes <= 4096 ->
    sh_frame_ok hbase hlen sp0 96 ->
    is_aligned_vaddr (Virtaddr vra) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    m !!! Regidx ra_idx = vra ->
    m !!! Regidx s0_idx = vs0 ->
    m !!! Regidx s2_idx = vs2 ->
    m !!! Regidx s3_idx = vs3 ->
    uM_bytes MJ (uint sp0 - 8) 8 vra ->
    uM_bytes MJ (uint sp0 - 16) 8 vs0 ->
    uM_bytes MJ (uint sp0 - 32) 8 vs2 ->
    uM_bytes MJ (uint sp0 - 40) 8 vs3 ->
    uv_wr pt MJ SH_FREEP 0x88 ->
    uv_wr pt MJ (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
                (16 * (sh_nunits nbytes - 1)) ->
    uM_only_in M MJ [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16);
                     (uint sp0 - 96, 96)] ->
    mJ !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mJ !!! Regidx a0_idx = (mword_of_int SH_BASE : mword 64) ->
    mJ !!! Regidx a5_idx
      = (mword_of_int (hbase + 65536 - 16 * sh_nunits nbytes) : mword 64) ->
    (forall r : mword 5,
       ucallee_saved_idx r = true ->
       Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
       Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
       mJ !!! Regidx r = m !!! Regidx r) ->
    uv_cap_gpr (CID := CIDp) C pt Psh MJ mJ -∗
    ubrk gbrk (hbase + 65536) -∗
    pc_is (CID := CIDp) (mword_of_int 0x125c) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
             : mword 64)⌝ -∗
       ⌜uv_wr pt M' (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
                    (16 * (sh_nunits nbytes - 1))⌝ -∗
       ⌜uM_only_in M M' [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16);
                         (uint sp0 - 96, 96)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) vra -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Htext Hst Hnun Hfr Hret2 Hsp Hra Hs0 Hs2 Hs3
           Bra Bs0 Bs2 Bs3 Hbssw Hblk Honly Hspj Ha0j Ha5j Hoth.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhhi, Hcan.
    change SH_FREEP with 8208 in *. change SH_BASE with 8328 in *.
    set (nun := sh_nunits nbytes) in *.
    assert (Hsphi : 77920 <= uint sp0) by lia.
    assert (Hst64 : uv_stack pt MJ sp0 64)
      by exact (proj1 (uv_stack_split pt MJ sp0 96 64 32 ltac:(lia) ltac:(lia)
                         ltac:(vm_compute; reflexivity) ltac:(lia) Hst)).
    destruct (uv_slot8_facts 8208 (mword_of_int 8208) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hufp & Hcnfp & Hpgfp & Halfp).
    destruct (data_leaf 8208 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wfp & Hwfp & Hwfpl & Hwfps).
    iIntros "Hcg Hbrk Hpc Hcont".
    (* ---- 0x125c  auipc a4,0x1 ---- *)
    assert (Hauipc : (mword_of_int 8796 : mword 64)
                     = add_vec (mword_of_int 0x125c)
                         (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh MJ mJ (mword_of_int 0x125c)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 8796)
              (ui_sh_125c pt MJ Hl Htext)
              ltac:(vm_compute; discriminate) Hauipc
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mJ1 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int 8796 : mword 64)]> mJ).
    assert (U1 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              mJ1 !!! Regidx r = mJ !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (E125c : add_vec_int (mword_of_int 0x125c : mword 64) 4
                    = mword_of_int 0x1260)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E125c) in "Hpc".
    (* ---- 0x1260  sd a0,-588(a4)  -- freep = prevp = &base ---- *)
    assert (Ha4_1 : mJ1 !!! Regidx a4_idx = (mword_of_int 8796 : mword 64))
      by exact (upd_eq mJ (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 8796 : mword 64))).
    assert (Ha0_1 : mJ1 !!! Regidx a0_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (U1 a0_idx ltac:(vm_compute; discriminate)); exact Ha0j).
    assert (Hvafp : (mword_of_int 8208 : mword 64)
                    = add_vec (mJ1 !!! Regidx a4_idx)
                        (sign_extend' 64 (mword_of_int 3508 : mword 12)))
      by (rewrite Ha4_1; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_sd C pt Psh MJ mJ1 (mword_of_int 0x1260)
              (mword_of_int 3508 : mword 12) a4_idx a0_idx
              wfp (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_1260 pt MJ Hl Htext)
              Hvafp (eq_sym Ha0_1) Hwfp Hwfps Hcnfp Hpgfp Halfp
              ltac:(rewrite Hufp; intros j Hj;
                    destruct (uwr_bytes _ _ _ _ Hbssw (Z.of_nat j) ltac:(lia))
                      as (b & Hb); exists b; exact Hb)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hufp) in "Hcg".
    set (MJ1 := uM_store8 MJ 8208 (mword_of_int 8328 : mword 64)).
    assert (Htext1 : sh_text_sub MJ1)
      by (unfold MJ1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom1 : forall kk : Z, is_Some (MJ !! kk) -> is_Some (MJ1 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk H)).
    assert (Hne1 : forall k : Z, (k < 8208 \/ 8216 <= k) -> MJ1 !! k = MJ !! k)
      by (intros k Hk; unfold MJ1; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (Hst1 : uv_stack pt MJ1 sp0 96)
      by exact (uv_stack_dom pt MJ MJ1 sp0 96 Hdom1 Hst).
    assert (Hst164 : uv_stack pt MJ1 sp0 64)
      by exact (uv_stack_dom pt MJ MJ1 sp0 64 Hdom1 Hst64).
    assert (E1260 : add_vec_int (mword_of_int 0x1260 : mword 64) 4
                    = mword_of_int 0x1264)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1260) in "Hpc".
    (* ---- 0x1264  addi a0,a5,16  -- return p + 1 ---- *)
    assert (Ha5_1 : mJ1 !!! Regidx a5_idx
                    = (mword_of_int (hbase + 65536 - 16 * nun) : mword 64))
      by (rewrite (U1 a5_idx ltac:(vm_compute; discriminate)); exact Ha5j).
    assert (Hret : (mword_of_int (hbase + 65536 - 16 * (nun - 1)) : mword 64)
                   = add_vec (mJ1 !!! Regidx a5_idx)
                       (sign_extend' 64 (mword_of_int 16 : mword 12))).
    { rewrite Ha5_1.
      assert (Hc : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                   = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh MJ1 mJ1 (mword_of_int 0x1264)
              (mword_of_int 16 : mword 12) a5_idx a0_idx
              (mword_of_int (hbase + 65536 - 16 * (nun - 1)))
              (ui_sh_1264 pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Hret
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mJ2 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (hbase + 65536 - 16 * (nun - 1))
                        : mword 64)]> mJ1).
    assert (U2 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              mJ2 !!! Regidx r = mJ1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1264 : add_vec_int (mword_of_int 0x1264 : mword 64) 4
                    = mword_of_int 0x1268)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1264) in "Hpc".
    (* the four frame slots the epilogue reloads *)
    assert (Hfrm : forall k : Z, uint sp0 - 64 <= k < uint sp0 -> MJ1 !! k = MJ !! k)
      by (intros k Hk; exact (Hne1 k ltac:(lia))).
    assert (Bra1 : uM_bytes MJ1 (uint sp0 - 8) 8 vra)
      by (intros j Hj; rewrite (Hfrm (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
          exact (Bra j Hj)).
    assert (Bs01 : uM_bytes MJ1 (uint sp0 - 16) 8 vs0)
      by (intros j Hj; rewrite (Hfrm (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
          exact (Bs0 j Hj)).
    assert (Bs21 : uM_bytes MJ1 (uint sp0 - 32) 8 vs2)
      by (intros j Hj; rewrite (Hfrm (uint sp0 - 32 + Z.of_nat j) ltac:(lia));
          exact (Bs2 j Hj)).
    assert (Bs31 : uM_bytes MJ1 (uint sp0 - 40) 8 vs3)
      by (intros j Hj; rewrite (Hfrm (uint sp0 - 40 + Z.of_nat j) ltac:(lia));
          exact (Bs3 j Hj)).
    assert (E64_56 : uint sp0 - 64 + 56 = uint sp0 - 8) by lia.
    assert (E64_48 : uint sp0 - 64 + 48 = uint sp0 - 16) by lia.
    assert (E64_32 : uint sp0 - 64 + 32 = uint sp0 - 32) by lia.
    assert (E64_24 : uint sp0 - 64 + 24 = uint sp0 - 40) by lia.
    assert (Hspj2 : mJ2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (U2 sp_idx ltac:(vm_compute; discriminate))
              (U1 sp_idx ltac:(vm_compute; discriminate)). exact Hspj. }
    (* ---- 0x1268  c.ldsp ra,56(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID3 Psh MJ1 mJ2 sp0 (mword_of_int 0x1268)
              (mword_of_int 7 : mword 6) ra_idx 64 56 vra
              (ui_sh_1268 pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Hst164
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hspj2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_56; symmetry;
                    exact (uM_word_w8 MJ1 (uint sp0 - 8) vra Bra1))
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (mJ3 := <[Regidx ra_idx := regval_into_reg vra]> mJ2).
    assert (U3 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              mJ3 !!! Regidx r = mJ2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ2 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (E1268 : add_vec_int (mword_of_int 0x1268 : mword 64) 2
                    = mword_of_int 0x126a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1268) in "Hpc".
    (* ---- 0x126a  c.ldsp s0,48(sp) ---- *)
    assert (Hsp3 : mJ3 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (U3 sp_idx ltac:(vm_compute; discriminate)); exact Hspj2).
    (* ---- 0x126a  c.ldsp s0,48(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID4 Psh MJ1 mJ3 sp0 (mword_of_int 0x126a)
              (mword_of_int 6 : mword 6) s0_idx 64 48 vs0
              (ui_sh_126a pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Hst164
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_48; symmetry;
                    exact (uM_word_w8 MJ1 (uint sp0 - 16) vs0 Bs01))
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (mJ4 := <[Regidx s0_idx := regval_into_reg vs0]> mJ3).
    assert (U4 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              mJ4 !!! Regidx r = mJ3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ3 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (E126a : add_vec_int (mword_of_int 0x126a : mword 64) 2
                    = mword_of_int 0x126c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E126a) in "Hpc".
    (* ---- 0x126c  c.ldsp s2,32(sp) ---- *)
    assert (Hsp4 : mJ4 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (U4 sp_idx ltac:(vm_compute; discriminate)); exact Hsp3).
    (* ---- 0x126c  c.ldsp s2,32(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID5 Psh MJ1 mJ4 sp0 (mword_of_int 0x126c)
              (mword_of_int 4 : mword 6) s2_idx 64 32 vs2
              (ui_sh_126c pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Hst164
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_32; symmetry;
                    exact (uM_word_w8 MJ1 (uint sp0 - 32) vs2 Bs21))
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    set (mJ5 := <[Regidx s2_idx := regval_into_reg vs2]> mJ4).
    assert (U5 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              mJ5 !!! Regidx r = mJ4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ4 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (E126c : add_vec_int (mword_of_int 0x126c : mword 64) 2
                    = mword_of_int 0x126e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E126c) in "Hpc".
    (* ---- 0x126e  c.ldsp s3,24(sp) ---- *)
    assert (Hsp5 : mJ5 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (U5 sp_idx ltac:(vm_compute; discriminate)); exact Hsp4).
    (* ---- 0x126e  c.ldsp s3,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID6 Psh MJ1 mJ5 sp0 (mword_of_int 0x126e)
              (mword_of_int 3 : mword 6) s3_idx 64 24 vs3
              (ui_sh_126e pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Hst164
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_24; symmetry;
                    exact (uM_word_w8 MJ1 (uint sp0 - 40) vs3 Bs31))
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (mJ6 := <[Regidx s3_idx := regval_into_reg vs3]> mJ5).
    assert (U6 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              mJ6 !!! Regidx r = mJ5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ5 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (E126e : add_vec_int (mword_of_int 0x126e : mword 64) 2
                    = mword_of_int 0x1270)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E126e) in "Hpc".
    (* ---- 0x1270  c.addi16sp sp,sp,64 ---- *)
    assert (Hsp6 : mJ6 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (U6 sp_idx ltac:(vm_compute; discriminate)); exact Hsp5).
    assert (Hwsp : sp0 = add_vec (mJ6 !!! Regidx csp_rs1)
                           (sign_extend' 64
                              (caddi16sp_imm (mword_of_int 4 : mword 6)))).
    { rewrite Hsp6.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 64 + 64) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh MJ1 mJ6 (mword_of_int 0x1270)
              (mword_of_int 4 : mword 6) sp0
              (ui_sh_1270 pt MJ1 Hl Htext1) Hwsp
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    set (mJ7 := <[Regidx csp_rs1 := regval_into_reg sp0]> mJ6).
    assert (U7 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              mJ7 !!! Regidx r = mJ6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mJ6 (Regidx sp_idx) (Regidx r) _ Hr)).
    assert (E1270 : add_vec_int (mword_of_int 0x1270 : mword 64) 2
                    = mword_of_int 0x1272)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1270) in "Hpc".
    (* ---- 0x1272  c.jr ra ---- *)
    assert (Hra7 : mJ7 !!! Regidx ra_idx = vra).
    { rewrite (U7 ra_idx ltac:(vm_compute; discriminate))
              (U6 ra_idx ltac:(vm_compute; discriminate))
              (U5 ra_idx ltac:(vm_compute; discriminate))
              (U4 ra_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mJ2 (Regidx ra_idx) (regval_into_reg vra)). }
    assert (Htgt : vra = ret_pc (mJ7 !!! Regidx ra_idx)).
    { rewrite Hra7. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh MJ1 mJ7 (mword_of_int 0x1272)
              ra_idx vra (ui_sh_1272 pt MJ1 Hl Htext1)
              ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    (* ---- the postcondition ---- *)
    assert (Hcs : ucallee_saved m mJ7).
    { intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
      { rewrite Esp.
        rewrite (upd_eq mJ6 (Regidx csp_rs1) (regval_into_reg sp0)).
        symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
      { rewrite Es0.
        rewrite (U7 s0_idx ltac:(vm_compute; discriminate))
                (U6 s0_idx ltac:(vm_compute; discriminate))
                (U5 s0_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq mJ3 (Regidx s0_idx) (regval_into_reg vs0)).
        symmetry. exact Hs0. }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ Es2 | Ns2 ].
      { rewrite Es2.
        rewrite (U7 s2_idx ltac:(vm_compute; discriminate))
                (U6 s2_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq mJ4 (Regidx s2_idx) (regval_into_reg vs2)).
        symmetry. exact Hs2. }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ Es3 | Ns3 ].
      { rewrite Es3.
        rewrite (U7 s3_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq mJ5 (Regidx s3_idx) (regval_into_reg vs3)).
        symmetry. exact Hs3. }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (U7 r Nsp) (U6 r Ns3) (U5 r Ns2) (U4 r Ns0) (U3 r Nra)
              (U2 r Na0) (U1 r Na4).
      exact (Hoth r Hr Nsp Ns0 Ns2 Ns3). }
    assert (Ha0_7 : mJ7 !!! Regidx a0_idx
                    = (mword_of_int (hbase + 65536 - 16 * (nun - 1)) : mword 64)).
    { rewrite (U7 a0_idx ltac:(vm_compute; discriminate))
              (U6 a0_idx ltac:(vm_compute; discriminate))
              (U5 a0_idx ltac:(vm_compute; discriminate))
              (U4 a0_idx ltac:(vm_compute; discriminate))
              (U3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mJ1 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (hbase + 65536 - 16 * (nun - 1)) : mword 64))). }
    iApply ("Hcont" $! CID9 mJ7 MJ1 with "[] [] [] [] Hbrk Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0_7.
    - iPureIntro.
      exact (uv_wr_dom pt MJ MJ1 _ _ Hdom1 Hblk).
    - iPureIntro.
      refine (uM_only_in_trans M MJ MJ1 _ Honly _).
      split; [ exact Hdom1 | ].
      intros k Hk.
      pose proof (not_in_window _ 8208 8 k
                    ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk)
        as W2.
      exact (Hne1 k ltac:(lia)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 malloc @0x118c -- THE TAIL, entered at 0x11ce.                     *)
  (*                                                                      *)
  (* Split here because the [bgeu s3,a4] at 0x11c8 -- morecore's           *)
  (* `if (nu < 4096) nu = 4096' -- reaches 0x11ce with TWO different       *)
  (* register files (the clamp at 0x11cc runs only on the fall-through)    *)
  (* that agree on every VALUE the rest of the function reads.  Stating    *)
  (* the tail over an abstract [mE] with pointwise premises is what lets   *)
  (* the forty instructions behind it be written once.                     *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_malloc_tail (CIDp : CpuId)
      (M MB : gmap Z (bv 8)) (m mE : regfile) (sp0 : mword 64) (nbytes : Z)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : mword 64) :
    sh_layout pt hbase hlen ->
    sh_text_sub MB ->
    uv_stack pt MB sp0 96 ->
    0 < nbytes -> 16 * sh_nunits nbytes <= 65536 ->
    sh_frame_ok hbase hlen sp0 96 ->
    is_aligned_vaddr (Virtaddr vra) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    m !!! Regidx ra_idx = vra ->
    m !!! Regidx s0_idx = vs0 ->
    m !!! Regidx s1_idx = vs1 ->
    m !!! Regidx s2_idx = vs2 ->
    m !!! Regidx s3_idx = vs3 ->
    m !!! Regidx s4_idx = vs4 ->
    m !!! Regidx s5_idx = vs5 ->
    m !!! Regidx s6_idx = vs6 ->
    uM_bytes MB (uint sp0 - 8) 8 vra ->
    uM_bytes MB (uint sp0 - 16) 8 vs0 ->
    uM_bytes MB (uint sp0 - 24) 8 vs1 ->
    uM_bytes MB (uint sp0 - 32) 8 vs2 ->
    uM_bytes MB (uint sp0 - 40) 8 vs3 ->
    uM_bytes MB (uint sp0 - 48) 8 vs4 ->
    uM_bytes MB (uint sp0 - 56) 8 vs5 ->
    uM_bytes MB (uint sp0 - 64) 8 vs6 ->
    uM_bytes MB SH_FREEP 8 (mword_of_int SH_BASE : mword 64) ->
    uM_bytes MB SH_BASE 8 (mword_of_int SH_BASE : mword 64) ->
    uM_bytes MB (SH_BASE + 8) 8 (mword_of_int 0 : mword 64) ->
    uv_wr pt MB SH_FREEP 0x88 ->
    uM_only_in M MB [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16);
                     (uint sp0 - 96, 96)] ->
    mE !!! Regidx sp_idx = (mword_of_int (uint sp0 - 64) : mword 64) ->
    mE !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64) ->
    mE !!! Regidx s2_idx = (mword_of_int (sh_nunits nbytes) : mword 64) ->
    mE !!! Regidx s3_idx = (mword_of_int (sh_nunits nbytes) : mword 64) ->
    mE !!! Regidx s4_idx = (mword_of_int 4096 : mword 64) ->
    (forall r : mword 5,
       ucallee_saved_idx r = true ->
       Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
       Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
       Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
       Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
       mE !!! Regidx r = m !!! Regidx r) ->
    uv_cap_gpr (CID := CIDp) C pt Psh MB mE -∗
    ubrk gbrk hbase -∗
    pc_is (CID := CIDp) (mword_of_int 0x11ce) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
             : mword 64)⌝ -∗
       ⌜uv_wr pt M' (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
                    (16 * (sh_nunits nbytes - 1))⌝ -∗
       ⌜uM_only_in M M' [(hbase, 65536); (SH_FREEP, 8); (SH_BASE, 16);
                         (uint sp0 - 96, 96)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) vra -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Htext Hst Hnb0 Hnbhi Hfr Hret2 Hsp Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6
           Bra Bs0 Bs1 Bs2 Bs3 Bs4 Bs5 Bs6 Bfp Bbs Bsz Hbssw Honly
           Hspe Ha5e Hs2e Hs3e Hs4e Hoth.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhhi, Hcan.
    change SH_FREEP with 8208 in *. change SH_BASE with 8328 in *.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    unfold sh_nunits in *.
    pose proof (Z.div_mod (nbytes + 15) 16 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (nbytes + 15) 16 ltac:(lia)) as Hmb.
    set (q := (nbytes + 15) / 16) in *.
    assert (Hq1 : 1 <= q) by lia.
    assert (Hq4095 : q <= 4095) by lia.
    assert (Hsphi : 77920 <= uint sp0) by lia.
    assert (Hqdef : sh_nunits nbytes = q + 1) by reflexivity.
    (* the callee's stack budget *)
    pose proof (uv_stack_split pt MB sp0 96 64 32 ltac:(lia) ltac:(lia)
                  ltac:(vm_compute; reflexivity) ltac:(lia) Hst) as Hsplit.
    assert (Hst64 : uv_stack pt MB sp0 64) by exact (proj1 Hsplit).
    assert (Hsplo : add_vec_int sp0 (- 64)
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (uv_stack_sp_moi pt MB sp0 64 Hst64).
    assert (Hst32 : uv_stack pt MB (mword_of_int (uint sp0 - 64)) 32)
      by (rewrite <- Hsplo; exact (proj2 Hsplit)).
    assert (Hst16 : uv_stack pt MB (mword_of_int (uint sp0 - 64)) 16)
      by exact (proj1 (uv_stack_split pt MB (mword_of_int (uint sp0 - 64)) 32 16 16
                         ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                         ltac:(lia) Hst32)).
    assert (Hu64 : uint (mword_of_int (uint sp0 - 64) : mword 64) = uint sp0 - 64)
      by (apply uint_moi; unfold Z64; lia).
    iIntros "Hcg Hbrk Hpc Hcont".
    (* ---- 0x11ce  sext.w s6,s4 ---- *)
    assert (Hsw6 : (mword_of_int 4096 : mword 64)
                   = sign_extend' 64
                       (subrange_vec_dec
                          (add_vec (mE !!! Regidx s4_idx)
                             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))
      by (rewrite Hs4e; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_addiw C pt Psh MB mE (mword_of_int 0x11ce)
              (mword_of_int 0 : mword 12) s4_idx s6_idx (mword_of_int 4096)
              (ui_sh_11ce pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hsw6
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (n1 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 4096 : mword 64)]> mE).
    assert (V1 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              n1 !!! Regidx r = mE !!! Regidx r)
      by (intros r Hr; exact (upd_ne mE (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (E11ce : add_vec_int (mword_of_int 0x11ce : mword 64) 4
                    = mword_of_int 0x11d2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11ce) in "Hpc".
    (* ---- 0x11d2  slliw s4,s4,0x4 ---- *)
    assert (Hs4_1 : n1 !!! Regidx s4_idx = (mword_of_int 4096 : mword 64))
      by (rewrite (V1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4e).
    assert (Hsl4 : (mword_of_int 65536 : mword 64)
                   = sign_extend' 64
                       (shift_bits_left
                          (subrange_vec_dec (n1 !!! Regidx s4_idx) 31 0 : mword 32)
                          (mword_of_int 4 : mword 5)))
      by (rewrite Hs4_1; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_slliw C pt Psh MB n1 (mword_of_int 0x11d2)
              (mword_of_int 4 : mword 5) s4_idx s4_idx (mword_of_int 65536)
              (ui_sh_11d2 pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hsl4
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (n2 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 65536 : mword 64)]> n1).
    assert (V2 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (E11d2 : add_vec_int (mword_of_int 0x11d2 : mword 64) 4
                    = mword_of_int 0x11d6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11d2) in "Hpc".
    (* ---- 0x11d6  auipc s1,0x1 ---- *)
    assert (Hau1 : (mword_of_int 8662 : mword 64)
                   = add_vec (mword_of_int 0x11d6)
                       (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh MB n2 (mword_of_int 0x11d6)
              (mword_of_int 1 : mword 20) s1_idx (mword_of_int 8662)
              (ui_sh_11d6 pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hau1
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (n3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 8662 : mword 64)]> n2).
    assert (V3 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              n3 !!! Regidx r = n2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n2 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (E11d6 : add_vec_int (mword_of_int 0x11d6 : mword 64) 4
                    = mword_of_int 0x11da)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11d6) in "Hpc".
    (* ---- 0x11da  addi s1,s1,-454  -- s1 = &freep ---- *)
    assert (Hs1_3 : n3 !!! Regidx s1_idx = (mword_of_int 8662 : mword 64))
      by exact (upd_eq n2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int 8662 : mword 64))).
    assert (Had1 : (mword_of_int 8208 : mword 64)
                   = add_vec (n3 !!! Regidx s1_idx)
                       (sign_extend' 64 (mword_of_int 3642 : mword 12)))
      by (rewrite Hs1_3; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_addi C pt Psh MB n3 (mword_of_int 0x11da)
              (mword_of_int 3642 : mword 12) s1_idx s1_idx (mword_of_int 8208)
              (ui_sh_11da pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Had1
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (n4 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 8208 : mword 64)]> n3).
    assert (V4 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              n4 !!! Regidx r = n3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n3 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (E11da : add_vec_int (mword_of_int 0x11da : mword 64) 4
                    = mword_of_int 0x11de)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11da) in "Hpc".
    (* ---- 0x11de  c.li s5,-1  -- SBRK_ERROR ---- *)
    assert (Hli5 : (mword_of_int 18446744073709551615 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12
                          (mword_of_int 63 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MB n4 (mword_of_int 0x11de)
              (mword_of_int 63 : mword 6) s5_idx
              (mword_of_int 18446744073709551615)
              (ui_sh_11de pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hli5
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (n5 := <[Regidx s5_idx
                 := regval_into_reg
                      (mword_of_int 18446744073709551615 : mword 64)]> n4).
    assert (V5 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
              n5 !!! Regidx r = n4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n4 (Regidx s5_idx) (Regidx r) _ Hr)).
    assert (E11de : add_vec_int (mword_of_int 0x11de : mword 64) 2
                    = mword_of_int 0x11e0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11de) in "Hpc".
    (* ---- 0x11e0  c.j 0x121e ---- *)
    assert (Htj1 : (mword_of_int 0x121e : mword 64)
                   = add_vec (mword_of_int 0x11e0)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 31 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cj C pt Psh MB n5 (mword_of_int 0x11e0)
              (mword_of_int 31 : mword 11) (mword_of_int 0x121e)
              (ui_sh_11e0 pt MB Hl Htext) Htj1
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    (* the registers the scan reads *)
    assert (Hs1_5 : n5 !!! Regidx s1_idx = (mword_of_int 8208 : mword 64)).
    { rewrite (V5 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n3 (Regidx s1_idx)
               (regval_into_reg (mword_of_int 8208 : mword 64))). }
    assert (Ha5_5 : n5 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64)).
    { rewrite (V5 a5_idx ltac:(vm_compute; discriminate))
              (V4 a5_idx ltac:(vm_compute; discriminate))
              (V3 a5_idx ltac:(vm_compute; discriminate))
              (V2 a5_idx ltac:(vm_compute; discriminate))
              (V1 a5_idx ltac:(vm_compute; discriminate)).
      exact Ha5e. }
    assert (Hs4_5 : n5 !!! Regidx s4_idx = (mword_of_int 65536 : mword 64)).
    { rewrite (V5 s4_idx ltac:(vm_compute; discriminate))
              (V4 s4_idx ltac:(vm_compute; discriminate))
              (V3 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n1 (Regidx s4_idx)
               (regval_into_reg (mword_of_int 65536 : mword 64))). }
    assert (Hsp5 : n5 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (V5 sp_idx ltac:(vm_compute; discriminate))
              (V4 sp_idx ltac:(vm_compute; discriminate))
              (V3 sp_idx ltac:(vm_compute; discriminate))
              (V2 sp_idx ltac:(vm_compute; discriminate))
              (V1 sp_idx ltac:(vm_compute; discriminate)).
      exact Hspe. }
    assert (Hs5_5 : n5 !!! Regidx s5_idx
                    = (mword_of_int 18446744073709551615 : mword 64))
      by exact (upd_eq n4 (Regidx s5_idx)
                  (regval_into_reg
                     (mword_of_int 18446744073709551615 : mword 64))).
    assert (Hs6_5 : n5 !!! Regidx s6_idx = (mword_of_int 4096 : mword 64)).
    { rewrite (V5 s6_idx ltac:(vm_compute; discriminate))
              (V4 s6_idx ltac:(vm_compute; discriminate))
              (V3 s6_idx ltac:(vm_compute; discriminate))
              (V2 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mE (Regidx s6_idx)
               (regval_into_reg (mword_of_int 4096 : mword 64))). }
    assert (Hs2_5 : n5 !!! Regidx s2_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (V5 s2_idx ltac:(vm_compute; discriminate))
              (V4 s2_idx ltac:(vm_compute; discriminate))
              (V3 s2_idx ltac:(vm_compute; discriminate))
              (V2 s2_idx ltac:(vm_compute; discriminate))
              (V1 s2_idx ltac:(vm_compute; discriminate)).
      exact Hs2e. }
    assert (Hs3_5 : n5 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (V5 s3_idx ltac:(vm_compute; discriminate))
              (V4 s3_idx ltac:(vm_compute; discriminate))
              (V3 s3_idx ltac:(vm_compute; discriminate))
              (V2 s3_idx ltac:(vm_compute; discriminate))
              (V1 s3_idx ltac:(vm_compute; discriminate)).
      exact Hs3e. }
    assert (V50 : forall r : mword 5,
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
              n5 !!! Regidx r = mE !!! Regidx r).
    { intros r N1 N4 N5 N6.
      rewrite (V5 r N5) (V4 r N1) (V3 r N1) (V2 r N4) (V1 r N6). reflexivity. }
    (* ---- 0x121e  c.ld a4,0(s1)  -- a4 = freep = &base ---- *)
    destruct (uv_slot8_facts 8208 (mword_of_int 8208) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hufp & Hcnfp & Hpgfp & Halfp).
    destruct (uv_slot8_facts 8328 (mword_of_int 8328) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hubs & Hcnbs & Hpgbs & Halbs).
    destruct (data_leaf 8208 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wfp & Hwfp & Hwfpl & Hwfps).
    destruct (data_leaf 8328 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wbs & Hwbs & Hwbsl & Hwbss).
    assert (Hva1 : (mword_of_int 8208 : mword 64)
                   = add_vec (n5 !!! Regidx s1_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Hs1_5; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cld C pt Psh MB n5 (mword_of_int 0x121e)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 6 : mword 3) s1_idx a4_idx
              wfp (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_121e pt MB Hl Htext)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva1 Hwfp Hwfpl Hcnfp Hpgfp Halfp
              ltac:(rewrite Hufp; exact Bfp)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (n6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 8328 : mword 64)]> n5).
    assert (V6 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              n6 !!! Regidx r = n5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n5 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (E121e : add_vec_int (mword_of_int 0x121e : mword 64) 2
                    = mword_of_int 0x1220)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E121e) in "Hpc".
    (* ---- 0x1220  c.mv a0,a5 ---- *)
    assert (Ha5_6 : n6 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (V6 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_5).
    assert (Hmv1 : (mword_of_int 8328 : mword 64)
                   = add_vec zero_reg (n6 !!! Regidx a5_idx))
      by (rewrite Ha5_6 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB n6 (mword_of_int 0x1220)
              a0_idx a5_idx (mword_of_int 8328)
              (ui_sh_1220 pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    set (n7 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 8328 : mword 64)]> n6).
    assert (V7 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              n7 !!! Regidx r = n6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n6 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1220 : add_vec_int (mword_of_int 0x1220 : mword 64) 2
                    = mword_of_int 0x1222)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1220) in "Hpc".
    (* ---- 0x1222  bne a4,a5,0x1216  -- NOT taken: p == freep ---- *)
    assert (Ha4_7 : n7 !!! Regidx a4_idx = (mword_of_int 8328 : mword 64)).
    { rewrite (V7 a4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n5 (Regidx a4_idx)
               (regval_into_reg (mword_of_int 8328 : mword 64))). }
    assert (Ha5_7 : n7 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64))
      by (rewrite (V7 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_6).
    assert (Htk1 : false = uv_btaken BNE (n7 !!! Regidx a4_idx)
                             (n7 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Ha4_7 Ha5_7.
      rewrite (moi_neq_vec 8328 8328 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
    iApply (wp_uv_btype C pt Psh MB n7 (mword_of_int 0x1222)
              (mword_of_int 8180 : mword 13) a5_idx a4_idx BNE
              false (mword_of_int 0x1216)
              (ui_sh_1222 pt MB Hl Htext) Htk1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    assert (E1222 : (if false then (mword_of_int 0x1216 : mword 64)
                     else add_vec_int (mword_of_int 0x1222 : mword 64) 4)
                    = mword_of_int 0x1226)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1222) in "Hpc".
    (* ---- 0x1226  c.mv a0,s4  -- the sbrk argument, 65536 ---- *)
    assert (Hs4_7 : n7 !!! Regidx s4_idx = (mword_of_int 65536 : mword 64)).
    { rewrite (V7 s4_idx ltac:(vm_compute; discriminate))
              (V6 s4_idx ltac:(vm_compute; discriminate)). exact Hs4_5. }
    assert (Hmv2 : (mword_of_int 65536 : mword 64)
                   = add_vec zero_reg (n7 !!! Regidx s4_idx))
      by (rewrite Hs4_7 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB n7 (mword_of_int 0x1226)
              a0_idx s4_idx (mword_of_int 65536)
              (ui_sh_1226 pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Hmv2
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (n8 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 65536 : mword 64)]> n7).
    assert (V8 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              n8 !!! Regidx r = n7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n7 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1226 : add_vec_int (mword_of_int 0x1226 : mword 64) 2
                    = mword_of_int 0x1228)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1226) in "Hpc".
    (* ---- 0x1228  jal ra,0xc52 <sbrk> ---- *)
    assert (Hsbsym : ShSyms.sbrk = 0xc52)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    assert (Htgt1 : (mword_of_int 0xc52 : mword 64)
                    = add_vec (mword_of_int 0x1228)
                        (sign_extend' 64 (mword_of_int 2095658 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk1 : (mword_of_int 0x122c : mword 64)
                    = add_vec_int (mword_of_int 0x1228 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MB n8 (mword_of_int 0x1228)
              (mword_of_int 2095658 : mword 21) ra_idx
              (mword_of_int 0xc52) (mword_of_int 0x122c)
              (ui_sh_1228 pt MB Hl Htext)
              ltac:(vm_compute; discriminate) Htgt1 Hlnk1
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (n9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x122c : mword 64)]> n8).
    assert (V9 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              n9 !!! Regidx r = n8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n8 (Regidx ra_idx) (Regidx r) _ Hr)).
    iEval (rewrite <- Hsbsym) in "Hpc".
    assert (Hra9 : n9 !!! Regidx ra_idx = (mword_of_int 0x122c : mword 64))
      by exact (upd_eq n8 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x122c : mword 64))).
    assert (Ha0_9 : n9 !!! Regidx a0_idx = (mword_of_int 65536 : mword 64)).
    { rewrite (V9 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n7 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 65536 : mword 64))). }
    assert (Hsp9 : n9 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (V9 sp_idx ltac:(vm_compute; discriminate))
              (V8 sp_idx ltac:(vm_compute; discriminate))
              (V7 sp_idx ltac:(vm_compute; discriminate))
              (V6 sp_idx ltac:(vm_compute; discriminate)). exact Hsp5. }
    assert (Hsi : sint (n9 !!! Regidx a0_idx) = 65536)
      by (rewrite Ha0_9; apply sint_moi; unfold Z63; lia).
    (* ---- the call: sbrk(65536) ---- *)
    iApply (wp_sh_sbrk C pt gin gbrk hbase hlen Q CID11 MB n9
              (mword_of_int (uint sp0 - 64)) hbase
              Hlay Htext Hsp9 Hst16
              ltac:(rewrite Hsi; split_and!; [ lia | lia | lia ])
              ltac:(unfold sh_frame_ok; rewrite Hu64; lia)
              ltac:(rewrite Hra9; vm_compute; reflexivity)
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CID12 p1 Ms1 Ms2) "%Hcs1 %Hbrk1 %Honly1 %Hgrow1 Hbrk Hcg Hpc".
    rewrite Hsi in Hgrow1.
    iEval (rewrite Hsi) in "Hbrk".
    iEval (rewrite Hra9) in "Hpc".
    (* what survived the growth: the frame, the .bss, the text ---- *)
    assert (Hdom_s1 : forall k : Z, is_Some (MB !! k) -> is_Some (Ms1 !! k))
      by exact (proj1 Honly1).
    assert (Hne_s1 : forall k : Z,
              (k < uint sp0 - 80 \/ uint sp0 - 64 <= k) -> Ms1 !! k = MB !! k)
      by (intros k Hk; apply (proj2 Honly1); rewrite Hu64; lia).
    destruct Hgrow1 as (Hfresh & Hoff2 & Hdom_s2').
    assert (Hdom_s2 : forall k : Z, is_Some (MB !! k) -> is_Some (Ms2 !! k))
      by (intros k H; exact (Hdom_s2' k (Hdom_s1 k H))).
    assert (HeqS : forall k : Z,
              (k < uint sp0 - 80 \/ uint sp0 - 64 <= k) ->
              (k < hbase \/ hbase + 65536 <= k) -> Ms2 !! k = MB !! k)
      by (intros k H1 H2; rewrite (Hoff2 k H2); exact (Hne_s1 k H1)).
    assert (Htext_s2 : sh_text_sub Ms2).
    { intros k b Hk. pose proof (sh_bytes_key_lt k b Hk) as Hkl.
      rewrite (HeqS k ltac:(lia) ltac:(lia)). exact (Htext k b Hk). }
    assert (Hst_s2 : uv_stack pt Ms2 sp0 96)
      by exact (uv_stack_dom pt MB Ms2 sp0 96 Hdom_s2 Hst).
    assert (Hst16_s2 : uv_stack pt Ms2 (mword_of_int (uint sp0 - 64)) 16)
      by exact (uv_stack_dom pt MB Ms2 _ 16 Hdom_s2 Hst16).
    (* ---- 0x122c  bne a0,s5,0x1208  -- TAKEN: sbrk did not fail ---- *)
    assert (Hs5_p1 : p1 !!! Regidx s5_idx
                     = (mword_of_int 18446744073709551615 : mword 64))
      by (rewrite (Hcs1 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5_5).
    assert (Htk2 : true = uv_btaken BNE (p1 !!! Regidx a0_idx)
                            (p1 !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Hbrk1 Hs5_p1.
      rewrite (moi_neq_vec hbase 18446744073709551615 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Htgt2 : (mword_of_int 0x1208 : mword 64)
                    = add_vec (mword_of_int 0x122c)
                        (sign_extend' 64 (mword_of_int 8156 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_btype C pt Psh Ms2 p1 (mword_of_int 0x122c)
              (mword_of_int 8156 : mword 13) s5_idx a0_idx BNE
              true (mword_of_int 0x1208)
              (ui_sh_122c pt Ms2 Hl Htext_s2) Htk2 Htgt2
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    (* ---- 0x1208  sw s6,8(a0)  -- hp->s.size = nu = 4096 ---- *)
    assert (Hhb4 : hbase mod 4 = 0).
    { assert (Hd : (4 | 4096)) by (exists 1024; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 4 4096 hbase ltac:(lia) ltac:(lia) Hd).
      rewrite Hhb. reflexivity. }
    assert (Hhb84 : (hbase + 8) mod 4 = 0)
      by (rewrite Zplus_mod Hhb4; reflexivity).
    assert (Hhb8m : hbase mod 8 = 0).
    { assert (Hd : (8 | 4096)) by (exists 512; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 4096 hbase ltac:(lia) ltac:(lia) Hd).
      rewrite Hhb. reflexivity. }
    destruct (uv_slot4_facts (hbase + 8) (mword_of_int (hbase + 8)) ltac:(lia)
                ltac:(exact Hhb84) ltac:(change (2 ^ 38) with 274877906944; lia)
                eq_refl)
      as (Huhp & Hcnhp & Hpghp & Halhp).
    destruct (heap_leaf (hbase + 8) Hlay ltac:(lia))
      as (whp & Hwhp & Hwhpl & Hwhps).
    assert (Hs6_p1 : p1 !!! Regidx s6_idx = (mword_of_int 4096 : mword 64))
      by (rewrite (Hcs1 s6_idx ltac:(vm_compute; reflexivity)); exact Hs6_5).
    assert (Hvahp : (mword_of_int (hbase + 8) : mword 64)
                    = add_vec (p1 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite Hbrk1.
      assert (Hc : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. reflexivity. }
    iApply (wp_uv_sw C pt Psh Ms2 p1 (mword_of_int 0x1208)
              (mword_of_int 8 : mword 12) a0_idx s6_idx
              whp (mword_of_int (hbase + 8)) (mword_of_int 4096)
              (ui_sh_1208 pt Ms2 Hl Htext_s2)
              Hvahp (eq_sym Hs6_p1) Hwhp Hwhps Hcnhp Hpghp Halhp
              ltac:(rewrite Huhp; intros j Hj;
                    destruct (Hfresh (8 + Z.of_nat j) ltac:(lia)) as (v & Hv);
                    exists v;
                    replace (hbase + 8 + Z.of_nat j) with (hbase + (8 + Z.of_nat j))
                      by lia;
                    exact Hv)
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    iEval (rewrite Huhp) in "Hcg".
    set (N1 := uM_store Ms2 (hbase + 8) 4 (mword_of_int 4096 : mword 64)).
    assert (Htext_N1 : sh_text_sub N1)
      by (unfold N1; apply sh_text_sub_store4; [ exact Htext_s2 | lia ]).
    assert (Hdom_N1 : forall k : Z, is_Some (MB !! k) -> is_Some (N1 !! k))
      by (intros k H; exact (uM_store_is_Some _ _ _ _ k (Hdom_s2 k H))).
    assert (Hne_N1 : forall k : Z, (k < hbase + 8 \/ hbase + 12 <= k) ->
              N1 !! k = Ms2 !! k)
      by (intros k Hk; unfold N1; apply uM_store_lookup_ne; intros j Hj; lia).
    assert (HeqN : forall k : Z,
              (k < uint sp0 - 80 \/ uint sp0 - 64 <= k) ->
              (k < hbase \/ hbase + 65536 <= k) -> N1 !! k = MB !! k)
      by (intros k H1 H2; rewrite (Hne_N1 k ltac:(lia)); exact (HeqS k H1 H2)).
    assert (E1208 : add_vec_int (mword_of_int 0x1208 : mword 64) 4
                    = mword_of_int 0x120c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1208) in "Hpc".
    (* ---- 0x120c  c.addi a0,a0,16  -- free(hp + 1) ---- *)
    assert (Hadd16 : (mword_of_int (hbase + 16) : mword 64)
                     = add_vec (p1 !!! Regidx a0_idx)
                         (sign_extend' 64 (sign_extend' 12
                            (mword_of_int 16 : mword 6)))).
    { rewrite Hbrk1.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. reflexivity. }
    iApply (wp_uv_caddi C pt Psh N1 p1 (mword_of_int 0x120c)
              (mword_of_int 16 : mword 6) a0_idx (mword_of_int (hbase + 16))
              (ui_sh_120c pt N1 Hl Htext_N1)
              ltac:(vm_compute; discriminate) Hadd16
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    set (p2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (hbase + 16) : mword 64)]> p1).
    assert (W2 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              p2 !!! Regidx r = p1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E120c : add_vec_int (mword_of_int 0x120c : mword 64) 2
                    = mword_of_int 0x120e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E120c) in "Hpc".
    (* ---- 0x120e  jal ra,0x1106 <free> ---- *)
    assert (Hfsym : ShSyms.free = 0x1106)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    assert (Htgt3 : (mword_of_int 0x1106 : mword 64)
                    = add_vec (mword_of_int 0x120e)
                        (sign_extend' 64 (mword_of_int 2096888 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk3 : (mword_of_int 0x1212 : mword 64)
                    = add_vec_int (mword_of_int 0x120e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh N1 p2 (mword_of_int 0x120e)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x1106) (mword_of_int 0x1212)
              (ui_sh_120e pt N1 Hl Htext_N1)
              ltac:(vm_compute; discriminate) Htgt3 Hlnk3
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    set (p3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1212 : mword 64)]> p2).
    assert (W3 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              p3 !!! Regidx r = p2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p2 (Regidx ra_idx) (Regidx r) _ Hr)).
    iEval (rewrite <- Hfsym) in "Hpc".
    (* ---- the call: free(hbase + 16) ---- *)
    assert (Hra3 : p3 !!! Regidx ra_idx = (mword_of_int 0x1212 : mword 64))
      by exact (upd_eq p2 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x1212 : mword 64))).
    assert (Ha0_p3 : p3 !!! Regidx a0_idx = (mword_of_int (hbase + 16) : mword 64)).
    { rewrite (W3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq p1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int (hbase + 16) : mword 64))). }
    assert (Hsp_p3 : p3 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (W3 sp_idx ltac:(vm_compute; discriminate))
              (W2 sp_idx ltac:(vm_compute; discriminate))
              (Hcs1 sp_idx ltac:(vm_compute; reflexivity)).
      exact Hsp9. }
    assert (Hheapw : uv_wr pt N1 hbase 65536).
    { constructor.
      - lia.
      - lia.
      - change (2 ^ 38) with 274877906944; lia.
      - intros j Hj. destruct (heap_leaf (hbase + j) Hlay ltac:(lia))
          as (w & Hw & _ & Hs). exists w. exact (conj Hw Hs).
      - intros j Hj. destruct (Hfresh j Hj) as (v & Hv).
        exact (uM_store_is_Some _ _ _ _ (hbase + j) (mk_is_Some _ _ Hv)). }
    assert (Hbssw_N1 : uv_wr pt N1 8208 136)
      by exact (uv_wr_dom pt MB N1 8208 136 Hdom_N1 Hbssw).
    assert (Hst16_N1 : uv_stack pt N1 (mword_of_int (uint sp0 - 64)) 16)
      by exact (uv_stack_dom pt MB N1 _ 16 Hdom_N1 Hst16).
    assert (Bfp_N1 : uM_bytes N1 8208 8 (mword_of_int 8328 : mword 64))
      by (intros j Hj; rewrite (HeqN (8208 + Z.of_nat j) ltac:(lia) ltac:(lia));
          exact (Bfp j Hj)).
    assert (Bbs_N1 : uM_bytes N1 8328 8 (mword_of_int 8328 : mword 64))
      by (intros j Hj; rewrite (HeqN (8328 + Z.of_nat j) ltac:(lia) ltac:(lia));
          exact (Bbs j Hj)).
    assert (Bsz_N1 : uM_bytes N1 8336 8 (mword_of_int 0 : mword 64))
      by (intros j Hj; rewrite (HeqN (8336 + Z.of_nat j) ltac:(lia) ltac:(lia));
          exact (Bsz j Hj)).
    assert (Bhp_N1 : uM_bytes N1 (hbase + 8) 4 (mword_of_int 4096 : mword 32)).
    { apply uM_bytes_4_of_4. intros j Hj.
      exact (uM_store_bytes Ms2 (hbase + 8) 4 (mword_of_int 4096 : mword 64) j
               ltac:(change (Z.to_nat 4) with 4%nat; lia)). }
    iApply (wp_sh_free_first C pt gin gbrk hbase hlen Q CID16 N1 p3
              (mword_of_int (uint sp0 - 64)) hbase 4096
              Hlay Htext_N1 Hsp_p3 Hst16_N1 Ha0_p3 eq_refl
              ltac:(split; [ change (2 ^ 31) with 2147483648; lia | lia ])
              Bfp_N1 Bbs_N1 Bsz_N1 Bhp_N1 Hheapw Hbssw_N1
              ltac:(unfold sh_frame_ok; rewrite Hu64; lia)
              ltac:(rewrite Hra3; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CID17 p4 N2) "%Hcs2 %Rbase %Rbp %Rsz %Rfreep %Honly2 Hcg Hpc".
    change SH_FREEP with 8208 in Honly2, Rfreep.
    change SH_BASE with 8328 in Honly2, Rbase, Rbp.
    rewrite Hu64 in Honly2.
    iEval (rewrite Hra3) in "Hpc".
    (* what survived free ---- *)
    assert (Hout2 : forall k : Z,
              (k < uint sp0 - 80 \/ uint sp0 - 64 <= k) ->
              (k < 8208 \/ 8216 <= k) -> (k < 8328 \/ 8344 <= k) ->
              (k < hbase \/ hbase + 16 <= k) -> N2 !! k = N1 !! k).
    { intros k H1 H2 H3 H4. apply (proj2 Honly2). intros (w & Hw & Hin).
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_nil in Hw. exact Hw. }
    assert (Hdom_N2 : forall k : Z, is_Some (MB !! k) -> is_Some (N2 !! k))
      by (intros k H; exact (proj1 Honly2 k (Hdom_N1 k H))).
    assert (Htext_N2 : sh_text_sub N2).
    { intros k b Hk. pose proof (sh_bytes_key_lt k b Hk) as Hkl.
      rewrite (Hout2 k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (Htext_N1 k b Hk). }
    assert (Hfrm_N2 : forall k : Z, uint sp0 - 64 <= k < uint sp0 ->
              N2 !! k = MB !! k)
      by (intros k Hk;
          rewrite (Hout2 k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
          exact (HeqN k ltac:(lia) ltac:(lia))).
    assert (Hst_N2 : uv_stack pt N2 sp0 96)
      by exact (uv_stack_dom pt MB N2 sp0 96 Hdom_N2 Hst).
    assert (Hst64_N2 : uv_stack pt N2 sp0 64)
      by exact (uv_stack_dom pt MB N2 sp0 64 Hdom_N2 Hst64).
    (* ---- 0x1212  c.ld a0,0(s1)  -- a0 = freep = &base ---- *)
    assert (Hs1_p4 : p4 !!! Regidx s1_idx = (mword_of_int 8208 : mword 64)).
    { rewrite (Hcs2 s1_idx ltac:(vm_compute; reflexivity))
              (W3 s1_idx ltac:(vm_compute; discriminate))
              (W2 s1_idx ltac:(vm_compute; discriminate))
              (Hcs1 s1_idx ltac:(vm_compute; reflexivity))
              (V9 s1_idx ltac:(vm_compute; discriminate))
              (V8 s1_idx ltac:(vm_compute; discriminate))
              (V7 s1_idx ltac:(vm_compute; discriminate))
              (V6 s1_idx ltac:(vm_compute; discriminate)).
      exact Hs1_5. }
    assert (Hva2 : (mword_of_int 8208 : mword 64)
                   = add_vec (p4 !!! Regidx s1_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Hs1_p4; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cld C pt Psh N2 p4 (mword_of_int 0x1212)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 2 : mword 3) s1_idx a0_idx
              wfp (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_1212 pt N2 Hl Htext_N2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva2 Hwfp Hwfpl Hcnfp Hpgfp Halfp
              ltac:(rewrite Hufp; exact Rfreep)
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    set (r1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 8328 : mword 64)]> p4).
    assert (X1 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              r1 !!! Regidx r = p4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne p4 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1212 : add_vec_int (mword_of_int 0x1212 : mword 64) 2
                    = mword_of_int 0x1214)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1212) in "Hpc".
    (* ---- 0x1214  c.beqz a0,0x1274  -- NOT taken ---- *)
    assert (Ha0_r1 : r1 !!! Regidx a0_idx = (mword_of_int 8328 : mword 64))
      by exact (upd_eq p4 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 8328 : mword 64))).
    assert (Htk3 : false = eq_vec (r1 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_r1 (moi_eq_zero 8328 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uv_cbeqz C pt Psh N2 r1 (mword_of_int 0x1214)
              (mword_of_int 48 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x1274)
              (ui_sh_1214 pt N2 Hl Htext_N2)
              ltac:(vm_compute; reflexivity) Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hcc; discriminate Hcc)
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    assert (E1214 : (if false then (mword_of_int 0x1274 : mword 64)
                     else add_vec_int (mword_of_int 0x1214 : mword 64) 2)
                    = mword_of_int 0x1216)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1214) in "Hpc".
    (* ---- 0x1216  c.ld a5,0(a0)  -- p = base.s.ptr = the new block ---- *)
    assert (Hva3 : (mword_of_int 8328 : mword 64)
                   = add_vec (r1 !!! Regidx a0_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Ha0_r1; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cld C pt Psh N2 r1 (mword_of_int 0x1216)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 7 : mword 3) a0_idx a5_idx
              wbs (mword_of_int 8328) (mword_of_int hbase)
              (ui_sh_1216 pt N2 Hl Htext_N2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva3 Hwbs Hwbsl Hcnbs Hpgbs Halbs
              ltac:(rewrite Hubs; exact Rbase)
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    set (r2 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int hbase : mword 64)]> r1).
    assert (X2 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (E1216 : add_vec_int (mword_of_int 0x1216 : mword 64) 2
                    = mword_of_int 0x1218)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1216) in "Hpc".
    (* ---- 0x1218  c.lw a4,8(a5)  -- p->s.size = 4096 ---- *)
    assert (Ha5_r2 : r2 !!! Regidx a5_idx = (mword_of_int hbase : mword 64))
      by exact (upd_eq r1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int hbase : mword 64))).
    assert (Hva4 : (mword_of_int (hbase + 8) : mword 64)
                   = add_vec (r2 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 2 : mword 5) ('b"00"))))).
    { rewrite Ha5_r2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 2 : mword 5) ('b"00"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. reflexivity. }
    iApply (wp_uv_clw C pt Psh N2 r2 (mword_of_int 0x1218)
              (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 6 : mword 3) a5_idx a4_idx
              whp (mword_of_int (hbase + 8)) (mword_of_int 4096)
              (mword_of_int 4096)
              (ui_sh_1218 pt N2 Hl Htext_N2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva4 Hwhp Hwhpl Hcnhp Hpghp Halhp
              ltac:(rewrite Huhp; exact Rsz)
              ltac:(symmetry; apply sext32_moi;
                    change (2 ^ 31) with 2147483648; lia)
              with "Hcg Hpc").
    iIntros (CID21) "Hcg Hpc".
    set (r3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 4096 : mword 64)]> r2).
    assert (X3 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              r3 !!! Regidx r = r2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r2 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (E1218 : add_vec_int (mword_of_int 0x1218 : mword 64) 2
                    = mword_of_int 0x121a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1218) in "Hpc".
    (* the callee-saved registers, as they stand after both calls *)
    assert (Hcs12 : forall r : mword 5, ucallee_saved_idx r = true ->
              p4 !!! Regidx r = n5 !!! Regidx r).
    { intros r Hr.
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (Hcs2 r Hr) (W3 r Nra) (W2 r Na0) (Hcs1 r Hr)
              (V9 r Nra) (V8 r Na0) (V7 r Na0) (V6 r Na4). reflexivity. }
    assert (Hs2_r3 : r3 !!! Regidx s2_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (X3 s2_idx ltac:(vm_compute; discriminate))
              (X2 s2_idx ltac:(vm_compute; discriminate))
              (X1 s2_idx ltac:(vm_compute; discriminate))
              (Hcs12 s2_idx ltac:(vm_compute; reflexivity)).
      exact Hs2_5. }
    assert (Ha4_r3 : r3 !!! Regidx a4_idx = (mword_of_int 4096 : mword 64))
      by exact (upd_eq r2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 4096 : mword 64))).
    (* ---- 0x121a  bgeu a4,s2,0x123c  -- TAKEN: the block is big enough ---- *)
    assert (Htk4 : true = uv_btaken BGEU (r3 !!! Regidx a4_idx)
                            (r3 !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Ha4_r3 Hs2_r3.
      rewrite (moi_ge_u 4096 (q + 1) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_le. lia. }
    iApply (wp_uv_btype C pt Psh N2 r3 (mword_of_int 0x121a)
              (mword_of_int 34 : mword 13) s2_idx a4_idx BGEU
              true (mword_of_int 0x123c)
              (ui_sh_121a pt N2 Hl Htext_N2) Htk4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID22) "Hcg Hpc".
    (* the four callee-saved reloads at 0x123c..0x1242 *)
    assert (Bs1_N2 : uM_bytes N2 (uint sp0 - 24) 8 vs1)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 24 + Z.of_nat j) ltac:(lia));
          exact (Bs1 j Hj)).
    assert (Bs4_N2 : uM_bytes N2 (uint sp0 - 48) 8 vs4)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 48 + Z.of_nat j) ltac:(lia));
          exact (Bs4 j Hj)).
    assert (Bs5_N2 : uM_bytes N2 (uint sp0 - 56) 8 vs5)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 56 + Z.of_nat j) ltac:(lia));
          exact (Bs5 j Hj)).
    assert (Bs6_N2 : uM_bytes N2 (uint sp0 - 64) 8 vs6)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 64 + Z.of_nat j) ltac:(lia));
          exact (Bs6 j Hj)).
    assert (E64_40 : uint sp0 - 64 + 40 = uint sp0 - 24) by lia.
    assert (E64_16 : uint sp0 - 64 + 16 = uint sp0 - 48) by lia.
    assert (E64_8  : uint sp0 - 64 + 8  = uint sp0 - 56) by lia.
    assert (E64_0  : uint sp0 - 64 + 0  = uint sp0 - 64) by lia.
    assert (Hsp_r3 : r3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (X3 sp_idx ltac:(vm_compute; discriminate))
              (X2 sp_idx ltac:(vm_compute; discriminate))
              (X1 sp_idx ltac:(vm_compute; discriminate))
              (Hcs12 sp_idx ltac:(vm_compute; reflexivity)).
      exact Hsp5. }
    (* ---- 0x123c  c.ldsp s1,40(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID22 Psh N2 r3 sp0 (mword_of_int 0x123c)
              (mword_of_int 5 : mword 6) s1_idx 64 40 vs1
              (ui_sh_123c pt N2 Hl Htext_N2)
              ltac:(vm_compute; discriminate) Hst64_N2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_r3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_40; symmetry;
                    exact (uM_word_w8 N2 (uint sp0 - 24) vs1 Bs1_N2))
              with "Hcg Hpc").
    iIntros (CID23) "Hcg Hpc".
    set (r4 := <[Regidx s1_idx := regval_into_reg vs1]> r3).
    assert (X4 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              r4 !!! Regidx r = r3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r3 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (E123c : add_vec_int (mword_of_int 0x123c : mword 64) 2
                    = mword_of_int 0x123e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E123c) in "Hpc".
    (* ---- 0x123e  c.ldsp s4,16(sp) ---- *)
    assert (Hsp_r4 : r4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (X4 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_r3).
    (* ---- 0x123e  c.ldsp s4,16(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID23 Psh N2 r4 sp0 (mword_of_int 0x123e)
              (mword_of_int 2 : mword 6) s4_idx 64 16 vs4
              (ui_sh_123e pt N2 Hl Htext_N2)
              ltac:(vm_compute; discriminate) Hst64_N2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_r4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_16; symmetry;
                    exact (uM_word_w8 N2 (uint sp0 - 48) vs4 Bs4_N2))
              with "Hcg Hpc").
    iIntros (CID24) "Hcg Hpc".
    set (r5 := <[Regidx s4_idx := regval_into_reg vs4]> r4).
    assert (X5 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              r5 !!! Regidx r = r4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r4 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (E123e : add_vec_int (mword_of_int 0x123e : mword 64) 2
                    = mword_of_int 0x1240)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E123e) in "Hpc".
    (* ---- 0x1240  c.ldsp s5,8(sp) ---- *)
    assert (Hsp_r5 : r5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (X5 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_r4).
    (* ---- 0x1240  c.ldsp s5,8(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID24 Psh N2 r5 sp0 (mword_of_int 0x1240)
              (mword_of_int 1 : mword 6) s5_idx 64 8 vs5
              (ui_sh_1240 pt N2 Hl Htext_N2)
              ltac:(vm_compute; discriminate) Hst64_N2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_r5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_8; symmetry;
                    exact (uM_word_w8 N2 (uint sp0 - 56) vs5 Bs5_N2))
              with "Hcg Hpc").
    iIntros (CID25) "Hcg Hpc".
    set (r6 := <[Regidx s5_idx := regval_into_reg vs5]> r5).
    assert (X6 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
              r6 !!! Regidx r = r5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r5 (Regidx s5_idx) (Regidx r) _ Hr)).
    assert (E1240 : add_vec_int (mword_of_int 0x1240 : mword 64) 2
                    = mword_of_int 0x1242)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1240) in "Hpc".
    (* ---- 0x1242  c.ldsp s6,0(sp) ---- *)
    assert (Hsp_r6 : r6 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (X6 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_r5).
    (* ---- 0x1242  c.ldsp s6,0(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID25 Psh N2 r6 sp0 (mword_of_int 0x1242)
              (mword_of_int 0 : mword 6) s6_idx 64 0 vs6
              (ui_sh_1242 pt N2 Hl Htext_N2)
              ltac:(vm_compute; discriminate) Hst64_N2
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_r6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite E64_0; symmetry;
                    exact (uM_word_w8 N2 (uint sp0 - 64) vs6 Bs6_N2))
              with "Hcg Hpc").
    iIntros (CID26) "Hcg Hpc".
    set (r7 := <[Regidx s6_idx := regval_into_reg vs6]> r6).
    assert (X7 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              r7 !!! Regidx r = r6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r6 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (E1242 : add_vec_int (mword_of_int 0x1242 : mword 64) 2
                    = mword_of_int 0x1244)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1242) in "Hpc".
    (* the register state the two arms of 0x1244 share *)
    assert (Hsp_r7 : r7 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (X7 sp_idx ltac:(vm_compute; discriminate))
              (X6 sp_idx ltac:(vm_compute; discriminate)). exact Hsp_r5. }
    assert (Ha0_r7 : r7 !!! Regidx a0_idx = (mword_of_int 8328 : mword 64)).
    { rewrite (X7 a0_idx ltac:(vm_compute; discriminate))
              (X6 a0_idx ltac:(vm_compute; discriminate))
              (X5 a0_idx ltac:(vm_compute; discriminate))
              (X4 a0_idx ltac:(vm_compute; discriminate))
              (X3 a0_idx ltac:(vm_compute; discriminate))
              (X2 a0_idx ltac:(vm_compute; discriminate)).
      exact Ha0_r1. }
    assert (Ha5_r7 : r7 !!! Regidx a5_idx = (mword_of_int hbase : mword 64)).
    { rewrite (X7 a5_idx ltac:(vm_compute; discriminate))
              (X6 a5_idx ltac:(vm_compute; discriminate))
              (X5 a5_idx ltac:(vm_compute; discriminate))
              (X4 a5_idx ltac:(vm_compute; discriminate))
              (X3 a5_idx ltac:(vm_compute; discriminate)).
      exact Ha5_r2. }
    assert (Ha4_r7 : r7 !!! Regidx a4_idx = (mword_of_int 4096 : mword 64)).
    { rewrite (X7 a4_idx ltac:(vm_compute; discriminate))
              (X6 a4_idx ltac:(vm_compute; discriminate))
              (X5 a4_idx ltac:(vm_compute; discriminate))
              (X4 a4_idx ltac:(vm_compute; discriminate)).
      exact Ha4_r3. }
    assert (Hs2_r7 : r7 !!! Regidx s2_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (X7 s2_idx ltac:(vm_compute; discriminate))
              (X6 s2_idx ltac:(vm_compute; discriminate))
              (X5 s2_idx ltac:(vm_compute; discriminate))
              (X4 s2_idx ltac:(vm_compute; discriminate)).
      exact Hs2_r3. }
    assert (Hs3_r7 : r7 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (X7 s3_idx ltac:(vm_compute; discriminate))
              (X6 s3_idx ltac:(vm_compute; discriminate))
              (X5 s3_idx ltac:(vm_compute; discriminate))
              (X4 s3_idx ltac:(vm_compute; discriminate))
              (X3 s3_idx ltac:(vm_compute; discriminate))
              (X2 s3_idx ltac:(vm_compute; discriminate))
              (X1 s3_idx ltac:(vm_compute; discriminate))
              (Hcs12 s3_idx ltac:(vm_compute; reflexivity)).
      exact Hs3_5. }
    assert (Hoth_r7 : forall r : mword 5,
              ucallee_saved_idx r = true ->
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
              r7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 N2i N3i.
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | Nn1 ].
      { rewrite E1 (X7 s1_idx ltac:(vm_compute; discriminate))
                  (X6 s1_idx ltac:(vm_compute; discriminate))
                  (X5 s1_idx ltac:(vm_compute; discriminate)) Hs1.
        exact (upd_eq r3 (Regidx s1_idx) (regval_into_reg vs1)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ E4 | Nn4 ].
      { rewrite E4 (X7 s4_idx ltac:(vm_compute; discriminate))
                  (X6 s4_idx ltac:(vm_compute; discriminate)) Hs4.
        exact (upd_eq r4 (Regidx s4_idx) (regval_into_reg vs4)). }
      destruct (decide (Regidx r = Regidx s5_idx)) as [ E5 | Nn5 ].
      { rewrite E5 (X7 s5_idx ltac:(vm_compute; discriminate)) Hs5.
        exact (upd_eq r5 (Regidx s5_idx) (regval_into_reg vs5)). }
      destruct (decide (Regidx r = Regidx s6_idx)) as [ E6 | Nn6 ].
      { rewrite E6 Hs6.
        exact (upd_eq r6 (Regidx s6_idx) (regval_into_reg vs6)). }
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (X7 r Nn6) (X6 r Nn5) (X5 r Nn4) (X4 r Nn1) (X3 r Na4)
              (X2 r Na5) (X1 r Na0) (Hcs12 r Hr)
              (V50 r Nn1 Nn4 Nn5 Nn6).
      exact (Hoth r Hr Nsp Ns0 Nn1 N2i N3i Nn4 Nn5 Nn6). }
    (* the image effect so far, at the shape the caller was promised *)
    assert (HonlyN2 : uM_only_in M N2 [(hbase, 65536); (8208, 8); (8328, 16);
                                       (uint sp0 - 96, 96)]).
    { refine (uM_only_in_trans M MB N2 _ Honly _).
      refine (uM_only_in_trans MB N1 N2 _ _ _).
      - split; [ exact Hdom_N1 | ].
        intros k Hk.
        pose proof (not_in_window _ hbase 65536 k
                      ltac:(apply elem_of_list_here) Hk) as Y1.
        pose proof (not_in_window _ (uint sp0 - 96) 96 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as Y4.
        exact (HeqN k ltac:(lia) ltac:(lia)).
      - split; [ exact (proj1 Honly2) | ].
        intros k Hk.
        pose proof (not_in_window _ hbase 65536 k
                      ltac:(apply elem_of_list_here) Hk) as Y1.
        pose proof (not_in_window _ 8208 8 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as Y2.
        pose proof (not_in_window _ 8328 16 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_here) Hk) as Y3.
        pose proof (not_in_window _ (uint sp0 - 96) 96 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as Y4.
        exact (Hout2 k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (Bra_N2 : uM_bytes N2 (uint sp0 - 8) 8 vra)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
          exact (Bra j Hj)).
    assert (Bs0_N2 : uM_bytes N2 (uint sp0 - 16) 8 vs0)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
          exact (Bs0 j Hj)).
    assert (Bs2_N2 : uM_bytes N2 (uint sp0 - 32) 8 vs2)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 32 + Z.of_nat j) ltac:(lia));
          exact (Bs2 j Hj)).
    assert (Bs3_N2 : uM_bytes N2 (uint sp0 - 40) 8 vs3)
      by (intros j Hj; rewrite (Hfrm_N2 (uint sp0 - 40 + Z.of_nat j) ltac:(lia));
          exact (Bs3 j Hj)).
    assert (Hbssw_N2 : uv_wr pt N2 8208 136)
      by exact (uv_wr_dom pt MB N2 8208 136 Hdom_N2 Hbssw).
    assert (Hheapw_N2 : uv_wr pt N2 hbase 65536)
      by exact (uv_wr_dom pt N1 N2 hbase 65536 (proj1 Honly2) Hheapw).
    assert (Htgt5 : (mword_of_int 0x1202 : mword 64)
                    = add_vec (mword_of_int 0x1244)
                        (sign_extend' 64 (mword_of_int 8126 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec q 4095) as [ Hq95 | Hq95 ].
    - (* ---- 0x1244  beq s2,a4  TAKEN: the block fits exactly ---- *)
      assert (Htk5 : true = uv_btaken BEQ (r7 !!! Regidx s2_idx)
                              (r7 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Hs2_r7 Ha4_r7.
        rewrite (moi_eq_vec (q + 1) 4096 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_eq. lia. }
      iApply (wp_uv_btype C pt Psh N2 r7 (mword_of_int 0x1244)
                (mword_of_int 8126 : mword 13) a4_idx s2_idx BEQ
                true (mword_of_int 0x1202)
                (ui_sh_1244 pt N2 Hl Htext_N2) Htk5 Htgt5
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID27) "Hcg Hpc".
      (* ---- 0x1202  c.ld a4,0(a5)  -- a4 = p->s.ptr = &base ---- *)
      destruct (uv_slot8_facts hbase (mword_of_int hbase) ltac:(lia)
                  ltac:(exact Hhb8m)
                  ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
        as (Huhb & Hcnhb & Hpghb & Halhb).
      destruct (heap_leaf hbase Hlay ltac:(lia))
        as (whb & Hwhb & Hwhbl & Hwhbs).
      assert (Hva5 : (mword_of_int hbase : mword 64)
                     = add_vec (r7 !!! Regidx a5_idx)
                         (sign_extend' 64 (zero_extend' 12
                            (concat_vec (mword_of_int 0 : mword 5) ('b"000"))))).
      { rewrite Ha5_r7.
        assert (Hc : (sign_extend' 64 (zero_extend' 12
                        (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                      : mword 64) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal; lia. }
      iApply (wp_uv_cld C pt Psh N2 r7 (mword_of_int 0x1202)
                (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
                (mword_of_int 6 : mword 3) a5_idx a4_idx
                whb (mword_of_int hbase) (mword_of_int 8328)
                (ui_sh_1202 pt N2 Hl Htext_N2)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) Hva5 Hwhb Hwhbl Hcnhb Hpghb Halhb
                ltac:(rewrite Huhb; exact Rbp)
                with "Hcg Hpc").
      iIntros (CID28) "Hcg Hpc".
      set (r8 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 8328 : mword 64)]> r7).
      assert (X8 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                r8 !!! Regidx r = r7 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r7 (Regidx a4_idx) (Regidx r) _ Hr)).
      assert (E1202 : add_vec_int (mword_of_int 0x1202 : mword 64) 2
                      = mword_of_int 0x1204)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1202) in "Hpc".
      (* ---- 0x1204  c.sd a4,0(a0)  -- prevp->s.ptr = p->s.ptr ---- *)
      assert (Ha4_r8 : r8 !!! Regidx a4_idx = (mword_of_int 8328 : mword 64))
        by exact (upd_eq r7 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 8328 : mword 64))).
      assert (Ha0_r8 : r8 !!! Regidx a0_idx = (mword_of_int 8328 : mword 64))
        by (rewrite (X8 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_r7).
      assert (Hva6 : (mword_of_int 8328 : mword 64)
                     = add_vec (r8 !!! Regidx a0_idx)
                         (sign_extend' 64 (zero_extend' 12
                            (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
        by (rewrite Ha0_r8; apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_csd C pt Psh N2 r8 (mword_of_int 0x1204)
                (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 6 : mword 3) a0_idx a4_idx
                wbs (mword_of_int 8328) (mword_of_int 8328)
                (ui_sh_1204 pt N2 Hl Htext_N2)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Hva6 (eq_sym Ha4_r8) Hwbs Hwbss Hcnbs Hpgbs Halbs
                ltac:(rewrite Hubs; intros j Hj;
                      destruct (uwr_bytes _ _ _ _ Hbssw_N2 (120 + Z.of_nat j)
                                  ltac:(lia)) as (b & Hb);
                      exists b;
                      replace (8328 + Z.of_nat j) with (8208 + (120 + Z.of_nat j))
                        by lia;
                      exact Hb)
                with "Hcg Hpc").
      iIntros (CID29) "Hcg Hpc".
      iEval (rewrite Hubs) in "Hcg".
      set (MJ := uM_store8 N2 8328 (mword_of_int 8328 : mword 64)).
      assert (Htext_MJ : sh_text_sub MJ)
        by (unfold MJ; apply sh_text_sub_store8; [ exact Htext_N2 | lia ]).
      assert (Hdom_MJ : forall k : Z, is_Some (N2 !! k) -> is_Some (MJ !! k))
        by (intros k H; exact (uM_store8_is_Some _ _ _ k H)).
      assert (Hne_MJ : forall k : Z, (k < 8328 \/ 8336 <= k) -> MJ !! k = N2 !! k)
        by (intros k Hk; unfold MJ; apply uM_store8_lookup_ne; intros j Hj; lia).
      assert (E1204 : add_vec_int (mword_of_int 0x1204 : mword 64) 2
                      = mword_of_int 0x1206)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1204) in "Hpc".
      (* ---- 0x1206  c.j 0x125c ---- *)
      assert (Htj2 : (mword_of_int 0x125c : mword 64)
                     = add_vec (mword_of_int 0x1206)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 43 : mword 11) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cj C pt Psh MJ r8 (mword_of_int 0x1206)
                (mword_of_int 43 : mword 11) (mword_of_int 0x125c)
                (ui_sh_1206 pt MJ Hl Htext_MJ) Htj2
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID30) "Hcg Hpc".
      iApply (wp_sh_malloc_join CID30 M MJ m r8 sp0 nbytes
                vra vs0 vs2
                vs3
                Hlay Htext_MJ
                ltac:(exact (uv_stack_dom pt N2 MJ sp0 96 Hdom_MJ Hst_N2))
                ltac:(rewrite Hqdef; lia)
                ltac:(unfold sh_frame_ok; lia)
                Hret2
                Hsp Hra Hs0 Hs2 Hs3
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 8 + Z.of_nat j) ltac:(lia));
                      exact (Bra_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 16 + Z.of_nat j) ltac:(lia));
                      exact (Bs0_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 32 + Z.of_nat j) ltac:(lia));
                      exact (Bs2_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 40 + Z.of_nat j) ltac:(lia));
                      exact (Bs3_N2 j Hj))
                ltac:(exact (uv_wr_dom pt N2 MJ 8208 136 Hdom_MJ Hbssw_N2))
                ltac:(rewrite Hqdef;
                      refine (uv_wr_sub pt MJ hbase 65536 _ _
                                (uv_wr_dom pt N2 MJ hbase 65536 Hdom_MJ Hheapw_N2)
                                _ _ _); lia)
                ltac:(refine (uM_only_in_trans M N2 MJ _ HonlyN2 _);
                      split; [ exact Hdom_MJ | ];
                      intros k Hk;
                      pose proof (not_in_window _ 8328 16 k
                                    ltac:(apply elem_of_list_further;
                                          apply elem_of_list_further;
                                          apply elem_of_list_here) Hk) as Z3;
                      exact (Hne_MJ k ltac:(lia)))
                ltac:(rewrite (X8 sp_idx ltac:(vm_compute; discriminate));
                      exact Hsp_r7)
                Ha0_r8
                ltac:(rewrite Hqdef (X8 a5_idx ltac:(vm_compute; discriminate))
                              Ha5_r7; f_equal; lia)
                ltac:(intros r Hr Nsp Ns0 N2i N3i;
                      assert (Na4 : Regidx r <> Regidx a4_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      rewrite (X8 r Na4);
                      exact (Hoth_r7 r Hr Nsp Ns0 N2i N3i))
                with "Hcg Hbrk Hpc Hcont").
    - (* ---- 0x1244  beq s2,a4  NOT taken: split the block ---- *)
      assert (Htk5 : false = uv_btaken BEQ (r7 !!! Regidx s2_idx)
                               (r7 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Hs2_r7 Ha4_r7.
        rewrite (moi_eq_vec (q + 1) 4096 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. lia. }
      iApply (wp_uv_btype C pt Psh N2 r7 (mword_of_int 0x1244)
                (mword_of_int 8126 : mword 13) a4_idx s2_idx BEQ
                false (mword_of_int 0x1202)
                (ui_sh_1244 pt N2 Hl Htext_N2) Htk5 Htgt5
                ltac:(intro Hcc; discriminate Hcc)
                with "Hcg Hpc").
      iIntros (CID27) "Hcg Hpc".
      assert (E1244 : (if false then (mword_of_int 0x1202 : mword 64)
                       else add_vec_int (mword_of_int 0x1244 : mword 64) 4)
                      = mword_of_int 0x1248)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1244) in "Hpc".
      (* ---- 0x1248  subw a4,a4,s3  -- p->s.size -= nunits ---- *)
      assert (Hsubw : (mword_of_int (4096 - (q + 1)) : mword 64)
                      = sign_extend' 64
                          (sub_vec
                             (subrange_vec_dec (r7 !!! Regidx a4_idx) 31 0
                              : mword 32)
                             (subrange_vec_dec (r7 !!! Regidx s3_idx) 31 0
                              : mword 32))).
      { rewrite Ha4_r7 Hs3_r7. symmetry.
        exact (moi_subw 4096 (q + 1) ltac:(unfold Z31; lia)). }
      iApply (wp_uv_subw C pt Psh N2 r7 (mword_of_int 0x1248)
                a4_idx s3_idx a4_idx (mword_of_int (4096 - (q + 1)))
                (ui_sh_1248 pt N2 Hl Htext_N2)
                ltac:(vm_compute; discriminate) Hsubw
                with "Hcg Hpc").
      iIntros (CID28) "Hcg Hpc".
      set (r8 := <[Regidx a4_idx
                   := regval_into_reg
                        (mword_of_int (4096 - (q + 1)) : mword 64)]> r7).
      assert (X8 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                r8 !!! Regidx r = r7 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r7 (Regidx a4_idx) (Regidx r) _ Hr)).
      assert (E1248 : add_vec_int (mword_of_int 0x1248 : mword 64) 4
                      = mword_of_int 0x124c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1248) in "Hpc".
      (* ---- 0x124c  c.sw a4,8(a5) ---- *)
      assert (Ha4_r8 : r8 !!! Regidx a4_idx
                       = (mword_of_int (4096 - (q + 1)) : mword 64))
        by exact (upd_eq r7 (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (4096 - (q + 1)) : mword 64))).
      assert (Ha5_r8 : r8 !!! Regidx a5_idx = (mword_of_int hbase : mword 64))
        by (rewrite (X8 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_r7).
      assert (Hva7 : (mword_of_int (hbase + 8) : mword 64)
                     = add_vec (r8 !!! Regidx a5_idx)
                         (sign_extend' 64 (zero_extend' 12
                            (concat_vec (mword_of_int 2 : mword 5) ('b"00"))))).
      { rewrite Ha5_r8.
        assert (Hc : (sign_extend' 64 (zero_extend' 12
                        (concat_vec (mword_of_int 2 : mword 5) ('b"00")))
                      : mword 64) = mword_of_int 8)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. reflexivity. }
      iApply (wp_uv_csw C pt Psh N2 r8 (mword_of_int 0x124c)
                (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
                (mword_of_int 6 : mword 3) a5_idx a4_idx
                whp (mword_of_int (hbase + 8))
                (mword_of_int (4096 - (q + 1)))
                (ui_sh_124c pt N2 Hl Htext_N2)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Hva7 (eq_sym Ha4_r8) Hwhp Hwhps Hcnhp Hpghp Halhp
                ltac:(rewrite Huhp; intros j Hj;
                      destruct (uwr_bytes _ _ _ _ Hheapw_N2 (8 + Z.of_nat j)
                                  ltac:(lia)) as (b & Hb);
                      exists b;
                      replace (hbase + 8 + Z.of_nat j)
                        with (hbase + (8 + Z.of_nat j)) by lia;
                      exact Hb)
                with "Hcg Hpc").
      iIntros (CID29) "Hcg Hpc".
      iEval (rewrite Huhp) in "Hcg".
      set (N3 := uM_store N2 (hbase + 8) 4
                   (mword_of_int (4096 - (q + 1)) : mword 64)).
      assert (Htext_N3 : sh_text_sub N3)
        by (unfold N3; apply sh_text_sub_store4; [ exact Htext_N2 | lia ]).
      assert (Hdom_N3 : forall k : Z, is_Some (N2 !! k) -> is_Some (N3 !! k))
        by (intros k H; exact (uM_store_is_Some _ _ _ _ k H)).
      assert (Hne_N3 : forall k : Z, (k < hbase + 8 \/ hbase + 12 <= k) ->
                N3 !! k = N2 !! k)
        by (intros k Hk; unfold N3; apply uM_store_lookup_ne; intros j Hj; lia).
      assert (E124c : add_vec_int (mword_of_int 0x124c : mword 64) 2
                      = mword_of_int 0x124e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E124c) in "Hpc".
      (* ---- 0x124e  slli a3,a4,0x20 ---- *)
      assert (Hshl : (mword_of_int ((4096 - (q + 1)) * 2 ^ 32) : mword 64)
                     = shift_bits_left (r8 !!! Regidx a4_idx)
                         (subrange_vec_dec (mword_of_int 32 : mword 6)
                            (Z.sub log2_xlen 1) 0))
        by (rewrite Ha4_r8; symmetry;
            exact (moi_shl (4096 - (q + 1)) 32 ltac:(lia))).
      iApply (wp_uv_slli C pt Psh N3 r8 (mword_of_int 0x124e)
                (mword_of_int 32 : mword 6) a4_idx a3_idx
                (mword_of_int ((4096 - (q + 1)) * 2 ^ 32))
                (ui_sh_124e pt N3 Hl Htext_N3)
                ltac:(vm_compute; discriminate) Hshl
                with "Hcg Hpc").
      iIntros (CID30) "Hcg Hpc".
      set (r9 := <[Regidx a3_idx
                   := regval_into_reg
                        (mword_of_int ((4096 - (q + 1)) * 2 ^ 32)
                         : mword 64)]> r8).
      assert (X9 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                r9 !!! Regidx r = r8 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r8 (Regidx a3_idx) (Regidx r) _ Hr)).
      assert (E124e : add_vec_int (mword_of_int 0x124e : mword 64) 4
                      = mword_of_int 0x1252)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E124e) in "Hpc".
      (* ---- 0x1252  srli a4,a3,0x1c  -- 16 * (p->s.size) ---- *)
      assert (Ha3_r9 : r9 !!! Regidx a3_idx
                       = (mword_of_int ((4096 - (q + 1)) * 2 ^ 32) : mword 64))
        by exact (upd_eq r8 (Regidx a3_idx)
                    (regval_into_reg
                       (mword_of_int ((4096 - (q + 1)) * 2 ^ 32) : mword 64))).
      assert (Hshr : (mword_of_int (16 * (4096 - (q + 1))) : mword 64)
                     = shift_bits_right (r9 !!! Regidx a3_idx)
                         (subrange_vec_dec (mword_of_int 28 : mword 6)
                            (Z.sub log2_xlen 1) 0)).
      { rewrite Ha3_r9.
        rewrite (moi_shr ((4096 - (q + 1)) * 2 ^ 32) 28 ltac:(lia)
                   ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
        rewrite moi_scale16. f_equal; lia. }
      iApply (wp_uv_srli C pt Psh N3 r9 (mword_of_int 0x1252)
                (mword_of_int 28 : mword 6) a3_idx a4_idx
                (mword_of_int (16 * (4096 - (q + 1))))
                (ui_sh_1252 pt N3 Hl Htext_N3)
                ltac:(vm_compute; discriminate) Hshr
                with "Hcg Hpc").
      iIntros (CID31) "Hcg Hpc".
      set (r10 := <[Regidx a4_idx
                    := regval_into_reg
                         (mword_of_int (16 * (4096 - (q + 1)))
                          : mword 64)]> r9).
      assert (X10 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                r10 !!! Regidx r = r9 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r9 (Regidx a4_idx) (Regidx r) _ Hr)).
      assert (E1252 : add_vec_int (mword_of_int 0x1252 : mword 64) 4
                      = mword_of_int 0x1256)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1252) in "Hpc".
      (* ---- 0x1256  c.add a5,a5,a4  -- p += p->s.size ---- *)
      assert (Ha4_r10 : r10 !!! Regidx a4_idx
                        = (mword_of_int (16 * (4096 - (q + 1))) : mword 64))
        by exact (upd_eq r9 (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (16 * (4096 - (q + 1))) : mword 64))).
      assert (Ha5_r10 : r10 !!! Regidx a5_idx = (mword_of_int hbase : mword 64)).
      { rewrite (X10 a5_idx ltac:(vm_compute; discriminate))
                (X9 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_r8. }
      assert (Hadd2 : (mword_of_int (hbase + 16 * (4096 - (q + 1))) : mword 64)
                      = add_vec (r10 !!! Regidx a5_idx) (r10 !!! Regidx a4_idx))
        by (rewrite Ha5_r10 Ha4_r10 moi_add; f_equal; lia).
      iApply (wp_uv_cadd C pt Psh N3 r10 (mword_of_int 0x1256)
                a5_idx a4_idx (mword_of_int (hbase + 16 * (4096 - (q + 1))))
                (ui_sh_1256 pt N3 Hl Htext_N3)
                ltac:(vm_compute; discriminate) Hadd2
                with "Hcg Hpc").
      iIntros (CID32) "Hcg Hpc".
      set (r11 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (hbase + 16 * (4096 - (q + 1)))
                          : mword 64)]> r10).
      assert (X11 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                r11 !!! Regidx r = r10 !!! Regidx r)
        by (intros r Hr; exact (upd_ne r10 (Regidx a5_idx) (Regidx r) _ Hr)).
      assert (E1256 : add_vec_int (mword_of_int 0x1256 : mword 64) 2
                      = mword_of_int 0x1258)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1256) in "Hpc".
      (* ---- 0x1258  sw s3,8(a5)  -- p->s.size = nunits ---- *)
      set (asplit := hbase + 16 * (4096 - (q + 1))).
      assert (Hasp4 : (asplit + 8) mod 4 = 0).
      { unfold asplit.
        destruct (proj1 (Z.mod_divide hbase 4 ltac:(lia)) Hhb4) as (c & Hc).
        apply (proj2 (Z.mod_divide _ 4 ltac:(lia))).
        exists (c + 4 * (4096 - (q + 1)) + 2). lia. }
      destruct (uv_slot4_facts (asplit + 8) (mword_of_int (asplit + 8))
                  ltac:(unfold asplit; lia) ltac:(exact Hasp4)
                  ltac:(unfold asplit; change (2 ^ 38) with 274877906944; lia)
                  eq_refl)
        as (Husp & Hcnsp & Hpgsp & Halsp).
      destruct (heap_leaf (asplit + 8) Hlay ltac:(unfold asplit; lia))
        as (wsp & Hwsp & Hwspl & Hwsps).
      assert (Ha5_r11 : r11 !!! Regidx a5_idx
                        = (mword_of_int asplit : mword 64))
        by exact (upd_eq r10 (Regidx a5_idx)
                    (regval_into_reg (mword_of_int asplit : mword 64))).
      assert (Hs3_r11 : r11 !!! Regidx s3_idx
                        = (mword_of_int (q + 1) : mword 64)).
      { rewrite (X11 s3_idx ltac:(vm_compute; discriminate))
                (X10 s3_idx ltac:(vm_compute; discriminate))
                (X9 s3_idx ltac:(vm_compute; discriminate))
                (X8 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_r7. }
      assert (Hva8 : (mword_of_int (asplit + 8) : mword 64)
                     = add_vec (r11 !!! Regidx a5_idx)
                         (sign_extend' 64 (mword_of_int 8 : mword 12))).
      { rewrite Ha5_r11.
        assert (Hc : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                     = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. reflexivity. }
      iApply (wp_uv_sw C pt Psh N3 r11 (mword_of_int 0x1258)
                (mword_of_int 8 : mword 12) a5_idx s3_idx
                wsp (mword_of_int (asplit + 8)) (mword_of_int (q + 1))
                (ui_sh_1258 pt N3 Hl Htext_N3)
                Hva8 (eq_sym Hs3_r11) Hwsp Hwsps Hcnsp Hpgsp Halsp
                ltac:(rewrite Husp; intros j Hj;
                      destruct (uwr_bytes _ _ _ _ Hheapw_N2
                                  (asplit + 8 - hbase + Z.of_nat j)
                                  ltac:(unfold asplit; lia)) as (b & Hb);
                      destruct (Hdom_N3 (hbase + (asplit + 8 - hbase + Z.of_nat j))
                                  (mk_is_Some _ _ Hb)) as (b' & Hb');
                      exists b';
                      replace (asplit + 8 + Z.of_nat j)
                        with (hbase + (asplit + 8 - hbase + Z.of_nat j)) by lia;
                      exact Hb')
                with "Hcg Hpc").
      iIntros (CID33) "Hcg Hpc".
      iEval (rewrite Husp) in "Hcg".
      set (MJ := uM_store N3 (asplit + 8) 4 (mword_of_int (q + 1) : mword 64)).
      assert (Htext_MJ : sh_text_sub MJ)
        by (unfold MJ; apply sh_text_sub_store4;
            [ exact Htext_N3 | unfold asplit; lia ]).
      assert (Hdom_MJ : forall k : Z, is_Some (N2 !! k) -> is_Some (MJ !! k))
        by (intros k H; exact (uM_store_is_Some _ _ _ _ k (Hdom_N3 k H))).
      assert (Hne_MJ : forall k : Z,
                (k < hbase + 8 \/ hbase + 12 <= k) ->
                (k < asplit + 8 \/ asplit + 12 <= k) -> MJ !! k = N2 !! k).
      { intros k H1 H2. unfold MJ.
        rewrite (uM_store_lookup_ne N3 (asplit + 8) 4 _ k
                   ltac:(intros j Hj; lia)).
        exact (Hne_N3 k H1). }
      assert (E1258 : add_vec_int (mword_of_int 0x1258 : mword 64) 4
                      = mword_of_int 0x125c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E1258) in "Hpc".
      iApply (wp_sh_malloc_join CID33 M MJ m r11 sp0 nbytes
                vra vs0 vs2
                vs3
                Hlay Htext_MJ
                ltac:(exact (uv_stack_dom pt N2 MJ sp0 96 Hdom_MJ Hst_N2))
                ltac:(rewrite Hqdef; lia)
                ltac:(unfold sh_frame_ok; lia)
                Hret2
                Hsp Hra Hs0 Hs2 Hs3
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 8 + Z.of_nat j)
                                 ltac:(unfold asplit; lia)
                                 ltac:(unfold asplit; lia));
                      exact (Bra_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 16 + Z.of_nat j)
                                 ltac:(unfold asplit; lia)
                                 ltac:(unfold asplit; lia));
                      exact (Bs0_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 32 + Z.of_nat j)
                                 ltac:(unfold asplit; lia)
                                 ltac:(unfold asplit; lia));
                      exact (Bs2_N2 j Hj))
                ltac:(intros j Hj;
                      rewrite (Hne_MJ (uint sp0 - 40 + Z.of_nat j)
                                 ltac:(unfold asplit; lia)
                                 ltac:(unfold asplit; lia));
                      exact (Bs3_N2 j Hj))
                ltac:(exact (uv_wr_dom pt N2 MJ 8208 136 Hdom_MJ Hbssw_N2))
                ltac:(rewrite Hqdef;
                      refine (uv_wr_sub pt MJ hbase 65536 _ _
                                (uv_wr_dom pt N2 MJ hbase 65536 Hdom_MJ Hheapw_N2)
                                _ _ _); lia)
                ltac:(refine (uM_only_in_trans M N2 MJ _ HonlyN2 _);
                      split; [ exact Hdom_MJ | ];
                      intros k Hk;
                      pose proof (not_in_window _ hbase 65536 k
                                    ltac:(apply elem_of_list_here) Hk) as Z1;
                      exact (Hne_MJ k ltac:(unfold asplit; lia)
                               ltac:(unfold asplit; lia)))
                ltac:(rewrite (X11 sp_idx ltac:(vm_compute; discriminate))
                              (X10 sp_idx ltac:(vm_compute; discriminate))
                              (X9 sp_idx ltac:(vm_compute; discriminate))
                              (X8 sp_idx ltac:(vm_compute; discriminate));
                      exact Hsp_r7)
                ltac:(rewrite (X11 a0_idx ltac:(vm_compute; discriminate))
                              (X10 a0_idx ltac:(vm_compute; discriminate))
                              (X9 a0_idx ltac:(vm_compute; discriminate))
                              (X8 a0_idx ltac:(vm_compute; discriminate));
                      exact Ha0_r7)
                ltac:(rewrite Hqdef Ha5_r11; unfold asplit; f_equal; lia)
                ltac:(intros r Hr Nsp Ns0 N2i N3i;
                      assert (Na3 : Regidx r <> Regidx a3_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      assert (Na4 : Regidx r <> Regidx a4_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      assert (Na5 : Regidx r <> Regidx a5_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      rewrite (X11 r Na5) (X10 r Na4) (X9 r Na3) (X8 r Na4);
                      exact (Hoth_r7 r Hr Nsp Ns0 N2i N3i))
                with "Hcg Hbrk Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4 malloc @0x118c -- THE HEAD.                                        *)
  (*                                                                      *)
  (*   118c..1196  the 64-byte frame: ra/s0/s2/s3 spilled unconditionally  *)
  (*   1198..11a8  nunits = (nbytes+15)/16 + 1, in s3 and s2               *)
  (*   11aa..11b2  prevp = freep;  it is 0, so the branch is TAKEN         *)
  (*   11e2..11e8  the four CONDITIONAL spills (s1/s4/s5/s6)               *)
  (*   11ea..11fc  base.s.ptr = freep = &base;  base.s.size = 0            *)
  (*   1200        j 11c4                                                  *)
  (*   11c4..11cc  morecore's constants; s4 := max(nunits,4096)            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_malloc_first (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (nbytes : Z) :
    wp_sh_malloc_first_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 nbytes.
  Proof.
    intros Hlay Htext Hsp Hst Hn Hnr Hfreep0 Hbasesz0 Hbssw Hfr Hret2.
    assert (Hmalloc : ShSyms.malloc = 0x118c)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhhi, Hcan.
    change SH_FREEP with 8208 in *. change SH_BASE with 8328 in *.
    change SH_FREEP with 8208 in Hfreep0.
    change (SH_BASE + 8) with 8336 in Hbasesz0.
    unfold sh_nunits in *.
    pose proof (Z.div_mod (nbytes + 15) 16 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (nbytes + 15) 16 ltac:(lia)) as Hmb.
    set (q := (nbytes + 15) / 16) in *.
    destruct Hnr as (Hnb0 & Hnbhi).
    assert (Hq1 : 1 <= q) by lia.
    assert (Hq4095 : q <= 4095) by lia.
    assert (Hnbsm : nbytes <= 65520) by lia.
    assert (Hsphi : 77920 <= uint sp0) by lia.
    assert (Hqdef : sh_nunits nbytes = q + 1) by reflexivity.
    assert (Hst64 : uv_stack pt M sp0 64)
      by exact (proj1 (uv_stack_split pt M sp0 96 64 32 ltac:(lia) ltac:(lia)
                         ltac:(vm_compute; reflexivity) ltac:(lia) Hst)).
    (* ... and every .bss byte the allocator touches *)
    assert (Hbeb : forall (Mx : gmap Z (bv 8)) (a : Z) (k : nat),
              (forall kk : Z, is_Some (M !! kk) -> is_Some (Mx !! kk)) ->
              8208 <= a -> a + Z.of_nat k <= 8344 ->
              forall j : nat, (j < k)%nat ->
                exists b : bv 8, Mx !! (a + Z.of_nat j) = Some b).
    { intros Mx a k Hdom Ha1 Ha2 j Hj.
      destruct (uwr_bytes _ _ _ _ Hbssw (a - 8208 + Z.of_nat j) ltac:(lia))
        as (b & Hb).
      replace (8208 + (a - 8208 + Z.of_nat j)) with (a + Z.of_nat j) in Hb by lia.
      exact (Hdom (a + Z.of_nat j) (mk_is_Some _ _ Hb)). }
    (* the eight frame slots, as absolute addresses *)
    assert (E64_56 : uint sp0 - 64 + 56 = uint sp0 - 8) by lia.
    assert (E64_48 : uint sp0 - 64 + 48 = uint sp0 - 16) by lia.
    assert (E64_40 : uint sp0 - 64 + 40 = uint sp0 - 24) by lia.
    assert (E64_32 : uint sp0 - 64 + 32 = uint sp0 - 32) by lia.
    assert (E64_24 : uint sp0 - 64 + 24 = uint sp0 - 40) by lia.
    assert (E64_16 : uint sp0 - 64 + 16 = uint sp0 - 48) by lia.
    assert (E64_8  : uint sp0 - 64 + 8  = uint sp0 - 56) by lia.
    assert (E64_0  : uint sp0 - 64 + 0  = uint sp0 - 64) by lia.
    (* the three .bss cells *)
    destruct (uv_slot8_facts 8208 (mword_of_int 8208) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hufp & Hcnfp & Hpgfp & Halfp).
    destruct (uv_slot8_facts 8328 (mword_of_int 8328) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Hubs & Hcnbs & Hpgbs & Halbs).
    destruct (uv_slot4_facts 8336 (mword_of_int 8336) ltac:(lia)
                ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl)
      as (Husz & Hcnsz & Hpgsz & Halsz).
    destruct (data_leaf 8208 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wfp & Hwfp & Hwfpl & Hwfps).
    destruct (data_leaf 8328 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wbs & Hwbs & Hwbsl & Hwbss).
    destruct (data_leaf 8336 Hlay ltac:(unfold SH_DATA_PG; lia))
      as (wsz & Hwsz & Hwszl & Hwszs).
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hmalloc) in "Hpc".
    (* ---- 0x118c  c.addi16sp sp,sp,-64 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x118c)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_sh_118c pt M Hl Htext) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    assert (E118c : add_vec_int (mword_of_int 0x118c : mword 64) 2
                    = mword_of_int 0x118e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E118c) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64))).
    assert (Hpre1 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx sp_idx) (Regidx r) _ Hr)).
    (* ---- 0x118e  c.sdsp ra,56(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID1 Psh M m1 sp0 (mword_of_int 0x118e)
              (mword_of_int 7 : mword 6) ra_idx 64 56
              (ui_sh_118e pt M Hl Htext) Hst64
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite E64_56 (Hpre1 ra_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom1 : forall kk : Z, is_Some (M !! kk) -> is_Some (M1 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk H)).
    assert (Hne1 : forall k : Z, (k < uint sp0 - 8 \/ uint sp0 <= k) ->
              M1 !! k = M !! k)
      by (intros k Hk; unfold M1; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E118e : add_vec_int (mword_of_int 0x118e : mword 64) 2
                    = mword_of_int 0x1190)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E118e) in "Hpc".
    (* ---- 0x1190  c.sdsp s0,48(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID2 Psh M1 m1 sp0 (mword_of_int 0x1190)
              (mword_of_int 6 : mword 6) s0_idx 64 48
              (ui_sh_1190 pt M1 Hl Htext1) ltac:(exact (uv_stack_dom pt M M1 sp0 64 Hdom1 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite E64_48 (Hpre1 s0_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom2 : forall kk : Z, is_Some (M !! kk) -> is_Some (M2 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom1 kk H))).
    assert (Hne2 : forall k : Z, (k < uint sp0 - 16 \/ uint sp0 - 8 <= k) ->
              M2 !! k = M1 !! k)
      by (intros k Hk; unfold M2; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1190 : add_vec_int (mword_of_int 0x1190 : mword 64) 2
                    = mword_of_int 0x1192)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1190) in "Hpc".
    (* ---- 0x1192  c.sdsp s2,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID3 Psh M2 m1 sp0 (mword_of_int 0x1192)
              (mword_of_int 4 : mword 6) s2_idx 64 32
              (ui_sh_1192 pt M2 Hl Htext2) ltac:(exact (uv_stack_dom pt M M2 sp0 64 Hdom2 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite E64_32 (Hpre1 s2_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M3 := uM_store8 M2 (uint sp0 - 32) (m !!! Regidx s2_idx)).
    assert (Htext3 : sh_text_sub M3)
      by (unfold M3; apply sh_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall kk : Z, is_Some (M !! kk) -> is_Some (M3 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom2 kk H))).
    assert (Hne3 : forall k : Z, (k < uint sp0 - 32 \/ uint sp0 - 24 <= k) ->
              M3 !! k = M2 !! k)
      by (intros k Hk; unfold M3; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1192 : add_vec_int (mword_of_int 0x1192 : mword 64) 2
                    = mword_of_int 0x1194)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1192) in "Hpc".
    (* ---- 0x1194  c.sdsp s3,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID4 Psh M3 m1 sp0 (mword_of_int 0x1194)
              (mword_of_int 3 : mword 6) s3_idx 64 24
              (ui_sh_1194 pt M3 Hl Htext3) ltac:(exact (uv_stack_dom pt M M3 sp0 64 Hdom3 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite E64_24 (Hpre1 s3_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M4 := uM_store8 M3 (uint sp0 - 40) (m !!! Regidx s3_idx)).
    assert (Htext4 : sh_text_sub M4)
      by (unfold M4; apply sh_text_sub_store8; [ exact Htext3 | lia ]).
    assert (Hdom4 : forall kk : Z, is_Some (M !! kk) -> is_Some (M4 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom3 kk H))).
    assert (Hne4 : forall k : Z, (k < uint sp0 - 40 \/ uint sp0 - 32 <= k) ->
              M4 !! k = M3 !! k)
      by (intros k Hk; unfold M4; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1194 : add_vec_int (mword_of_int 0x1194 : mword 64) 2
                    = mword_of_int 0x1196)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1194) in "Hpc".
    (* ---- 0x1196  c.addi4spn s0,sp,64 ---- *)
    assert (Hw64 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh M4 m1 (mword_of_int 0x1196)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_1196 pt M4 Hl Htext4)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw64
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (E1196 : add_vec_int (mword_of_int 0x1196 : mword 64) 2
                    = mword_of_int 0x1198)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1196) in "Hpc".
    assert (Hpre2 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              Regidx r <> Regidx s0_idx -> m2 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0.
      exact (eq_trans (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Ns0)
               (Hpre1 r Nsp)). }
    assert (Hsp2 : m2 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (exact (eq_trans (upd_ne m1 (Regidx s0_idx) (Regidx sp_idx) _
                             ltac:(vm_compute; discriminate)) Hsp1)).
    (* ---- 0x1198  slli s3,a0,0x20 ---- *)
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int nbytes : mword 64))
      by (rewrite (Hpre2 a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hn).
    assert (Hshl1 : (mword_of_int (nbytes * 2 ^ 32) : mword 64)
                    = shift_bits_left (m2 !!! Regidx a0_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))
      by (rewrite Ha0_2; symmetry; exact (moi_shl nbytes 32 ltac:(lia))).
    iApply (wp_uv_slli C pt Psh M4 m2 (mword_of_int 0x1198)
              (mword_of_int 32 : mword 6) a0_idx s3_idx
              (mword_of_int (nbytes * 2 ^ 32))
              (ui_sh_1198 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hshl1
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (m3 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (nbytes * 2 ^ 32) : mword 64)]> m2).
    assert (E1198 : add_vec_int (mword_of_int 0x1198 : mword 64) 4
                    = mword_of_int 0x119c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1198) in "Hpc".
    (* ---- 0x119c  srli s3,s3,0x20 ---- *)
    assert (Hs3_3 : m3 !!! Regidx s3_idx
                    = (mword_of_int (nbytes * 2 ^ 32) : mword 64))
      by exact (upd_eq m2 (Regidx s3_idx) _).
    assert (Hshr1 : (mword_of_int nbytes : mword 64)
                    = shift_bits_right (m3 !!! Regidx s3_idx)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0)).
    { rewrite Hs3_3.
      rewrite (moi_shr (nbytes * 2 ^ 32) 32 ltac:(lia)
                 ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
      f_equal. rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ]. }
    iApply (wp_uv_srli C pt Psh M4 m3 (mword_of_int 0x119c)
              (mword_of_int 32 : mword 6) s3_idx s3_idx (mword_of_int nbytes)
              (ui_sh_119c pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hshr1
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int nbytes : mword 64)]> m3).
    assert (E119c : add_vec_int (mword_of_int 0x119c : mword 64) 4
                    = mword_of_int 0x11a0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E119c) in "Hpc".
    (* ---- 0x11a0  c.addi s3,s3,15 ---- *)
    assert (Hs3_4 : m4 !!! Regidx s3_idx = (mword_of_int nbytes : mword 64))
      by exact (upd_eq m3 (Regidx s3_idx) _).
    assert (Hadd15 : (mword_of_int (nbytes + 15) : mword 64)
                     = add_vec (m4 !!! Regidx s3_idx)
                         (sign_extend' 64 (sign_extend' 12
                            (mword_of_int 15 : mword 6)))).
    { rewrite Hs3_4.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6))
                    : mword 64) = mword_of_int 15)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. reflexivity. }
    iApply (wp_uv_caddi C pt Psh M4 m4 (mword_of_int 0x11a0)
              (mword_of_int 15 : mword 6) s3_idx (mword_of_int (nbytes + 15))
              (ui_sh_11a0 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hadd15
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    set (m5 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (nbytes + 15) : mword 64)]> m4).
    assert (E11a0 : add_vec_int (mword_of_int 0x11a0 : mword 64) 2
                    = mword_of_int 0x11a2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11a0) in "Hpc".
    (* ---- 0x11a2  srli s3,s3,0x4 ---- *)
    assert (Hs3_5 : m5 !!! Regidx s3_idx = (mword_of_int (nbytes + 15) : mword 64))
      by exact (upd_eq m4 (Regidx s3_idx) _).
    assert (Hshr2 : (mword_of_int q : mword 64)
                    = shift_bits_right (m5 !!! Regidx s3_idx)
                        (subrange_vec_dec (mword_of_int 4 : mword 6)
                           (Z.sub log2_xlen 1) 0)).
    { rewrite Hs3_5.
      rewrite (moi_shr (nbytes + 15) 4 ltac:(lia) ltac:(unfold Z64; lia)).
      replace (2 ^ 4) with 16 by (vm_compute; reflexivity). reflexivity. }
    iApply (wp_uv_srli C pt Psh M4 m5 (mword_of_int 0x11a2)
              (mword_of_int 4 : mword 6) s3_idx s3_idx (mword_of_int q)
              (ui_sh_11a2 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hshr2
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (m6 := <[Regidx s3_idx := regval_into_reg (mword_of_int q : mword 64)]> m5).
    assert (E11a2 : add_vec_int (mword_of_int 0x11a2 : mword 64) 4
                    = mword_of_int 0x11a6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11a2) in "Hpc".
    (* ---- 0x11a6  c.addiw s3,s3,1 ---- *)
    assert (Hs3_6 : m6 !!! Regidx s3_idx = (mword_of_int q : mword 64))
      by exact (upd_eq m5 (Regidx s3_idx) _).
    assert (Haddw : (mword_of_int (q + 1) : mword 64)
                    = sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (m6 !!! Regidx s3_idx)
                              (sign_extend' 64 (sign_extend' 12
                                 (mword_of_int 1 : mword 6)))) 31 0)).
    { rewrite Hs3_6.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                    : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact (moi_addw q 1 ltac:(unfold Z31; lia)). }
    iApply (wp_uv_caddiw C pt Psh M4 m6 (mword_of_int 0x11a6)
              (mword_of_int 1 : mword 6) s3_idx (mword_of_int (q + 1))
              (ui_sh_11a6 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Haddw
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (q + 1) : mword 64)]> m6).
    assert (E11a6 : add_vec_int (mword_of_int 0x11a6 : mword 64) 2
                    = mword_of_int 0x11a8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11a6) in "Hpc".
    (* ---- 0x11a8  c.mv s2,s3 ---- *)
    assert (Hs3_7 : m7 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64))
      by exact (upd_eq m6 (Regidx s3_idx) _).
    assert (Hmv1 : (mword_of_int (q + 1) : mword 64)
                   = add_vec zero_reg (m7 !!! Regidx s3_idx))
      by (rewrite Hs3_7 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M4 m7 (mword_of_int 0x11a8)
              s2_idx s3_idx (mword_of_int (q + 1))
              (ui_sh_11a8 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (m8 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (q + 1) : mword 64)]> m7).
    assert (E11a8 : add_vec_int (mword_of_int 0x11a8 : mword 64) 2
                    = mword_of_int 0x11aa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11a8) in "Hpc".
    (* ---- 0x11aa  auipc a0,0x1 ---- *)
    assert (Hauipc1 : (mword_of_int 8618 : mword 64)
                      = add_vec (mword_of_int 0x11aa)
                          (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh M4 m8 (mword_of_int 0x11aa)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 8618)
              (ui_sh_11aa pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hauipc1
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    set (m9 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 8618 : mword 64)]> m8).
    assert (E11aa : add_vec_int (mword_of_int 0x11aa : mword 64) 4
                    = mword_of_int 0x11ae)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11aa) in "Hpc".
    (* ---- 0x11ae  ld a0,-410(a0)  -- a0 = freep = 0 ---- *)
    assert (Ha0_9 : m9 !!! Regidx a0_idx = (mword_of_int 8618 : mword 64))
      by exact (upd_eq m8 (Regidx a0_idx) _).
    assert (Hvafp : (mword_of_int 8208 : mword 64)
                    = add_vec (m9 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 3686 : mword 12)))
      by (rewrite Ha0_9; apply bv_eq; vm_compute; reflexivity).
    assert (Hfp4 : uM_bytes M4 8208 8 (mword_of_int 0 : mword 64)).
    { intros j Hj.
      rewrite (Hne4 (8208 + Z.of_nat j) ltac:(lia))
              (Hne3 (8208 + Z.of_nat j) ltac:(lia))
              (Hne2 (8208 + Z.of_nat j) ltac:(lia))
              (Hne1 (8208 + Z.of_nat j) ltac:(lia)).
      rewrite nth_byte_moi0. exact (Hfreep0 (Z.of_nat j) ltac:(lia)). }
    iApply (wp_uv_ld C pt Psh M4 m9 (mword_of_int 0x11ae)
              (mword_of_int 3686 : mword 12) a0_idx a0_idx
              wfp (mword_of_int 8208) (mword_of_int 0)
              (ui_sh_11ae pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hvafp Hwfp Hwfpl Hcnfp Hpgfp Halfp
              ltac:(rewrite Hufp; exact (Hbeb M4 8208 8%nat Hdom4 ltac:(lia) ltac:(lia)))
              ltac:(rewrite Hufp; symmetry; exact (uM_word_w8 M4 8208 _ Hfp4))
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (m10 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int 0 : mword 64)]> m9).
    assert (E11ae : add_vec_int (mword_of_int 0x11ae : mword 64) 4
                    = mword_of_int 0x11b2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11ae) in "Hpc".
    (* the registers the head has settled *)
    assert (S32 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (S43 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (S54 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (S65 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (S76 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (S87 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (S98 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (SA9 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              m10 !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hpre10 : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
              Regidx r <> Regidx a0_idx -> m10 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0 N2 N3 N0.
      rewrite (SA9 r N0) (S98 r N0) (S87 r N2) (S76 r N3) (S65 r N3)
              (S54 r N3) (S43 r N3) (S32 r N3).
      exact (Hpre2 r Nsp Ns0). }
    assert (Hsp10 : m10 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (SA9 sp_idx ltac:(vm_compute; discriminate))
              (S98 sp_idx ltac:(vm_compute; discriminate))
              (S87 sp_idx ltac:(vm_compute; discriminate))
              (S76 sp_idx ltac:(vm_compute; discriminate))
              (S65 sp_idx ltac:(vm_compute; discriminate))
              (S54 sp_idx ltac:(vm_compute; discriminate))
              (S43 sp_idx ltac:(vm_compute; discriminate))
              (S32 sp_idx ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Hs3_10 : m10 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (SA9 s3_idx ltac:(vm_compute; discriminate))
              (S98 s3_idx ltac:(vm_compute; discriminate))
              (S87 s3_idx ltac:(vm_compute; discriminate)).
      exact Hs3_7. }
    assert (Hs2_10 : m10 !!! Regidx s2_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (SA9 s2_idx ltac:(vm_compute; discriminate))
              (S98 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m7 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (q + 1) : mword 64))). }
    assert (Ha0_10 : m10 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
      by exact (upd_eq m9 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0 : mword 64))).
    (* ---- 0x11b2  c.beqz a0,0x11e2  -- TAKEN: freep is 0 ---- *)
    assert (Htk0 : true = eq_vec (m10 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_10 (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    assert (Htgt0 : (mword_of_int 0x11e2 : mword 64)
                    = add_vec (mword_of_int 0x11b2)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 24 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cbeqz C pt Psh M4 m10 (mword_of_int 0x11b2)
              (mword_of_int 24 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x11e2)
              (ui_sh_11b2 pt M4 Hl Htext4)
              ltac:(vm_compute; reflexivity) Htk0 Htgt0
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    (* ---- 0x11e2  c.sdsp s1,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID15 Psh M4 m10 sp0 (mword_of_int 0x11e2)
              (mword_of_int 5 : mword 6) s1_idx 64 40
              (ui_sh_11e2 pt M4 Hl Htext4) ltac:(exact (uv_stack_dom pt M M4 sp0 64 Hdom4 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp10
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    iEval (rewrite E64_40 (Hpre10 s1_idx ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))) in "Hcg".
    set (M5 := uM_store8 M4 (uint sp0 - 24) (m !!! Regidx s1_idx)).
    assert (Htext5 : sh_text_sub M5)
      by (unfold M5; apply sh_text_sub_store8; [ exact Htext4 | lia ]).
    assert (Hdom5 : forall kk : Z, is_Some (M !! kk) -> is_Some (M5 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom4 kk H))).
    assert (Hne5 : forall k : Z, (k < uint sp0 - 24 \/ uint sp0 - 16 <= k) ->
              M5 !! k = M4 !! k)
      by (intros k Hk; unfold M5; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11e2 : add_vec_int (mword_of_int 0x11e2 : mword 64) 2
                    = mword_of_int 0x11e4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11e2) in "Hpc".
    (* ---- 0x11e4  c.sdsp s4,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID16 Psh M5 m10 sp0 (mword_of_int 0x11e4)
              (mword_of_int 2 : mword 6) s4_idx 64 16
              (ui_sh_11e4 pt M5 Hl Htext5) ltac:(exact (uv_stack_dom pt M M5 sp0 64 Hdom5 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp10
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    iEval (rewrite E64_16 (Hpre10 s4_idx ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))) in "Hcg".
    set (M6 := uM_store8 M5 (uint sp0 - 48) (m !!! Regidx s4_idx)).
    assert (Htext6 : sh_text_sub M6)
      by (unfold M6; apply sh_text_sub_store8; [ exact Htext5 | lia ]).
    assert (Hdom6 : forall kk : Z, is_Some (M !! kk) -> is_Some (M6 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom5 kk H))).
    assert (Hne6 : forall k : Z, (k < uint sp0 - 48 \/ uint sp0 - 40 <= k) ->
              M6 !! k = M5 !! k)
      by (intros k Hk; unfold M6; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11e4 : add_vec_int (mword_of_int 0x11e4 : mword 64) 2
                    = mword_of_int 0x11e6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11e4) in "Hpc".
    (* ---- 0x11e6  c.sdsp s5,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID17 Psh M6 m10 sp0 (mword_of_int 0x11e6)
              (mword_of_int 1 : mword 6) s5_idx 64 8
              (ui_sh_11e6 pt M6 Hl Htext6) ltac:(exact (uv_stack_dom pt M M6 sp0 64 Hdom6 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp10
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    iEval (rewrite E64_8 (Hpre10 s5_idx ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))) in "Hcg".
    set (M7 := uM_store8 M6 (uint sp0 - 56) (m !!! Regidx s5_idx)).
    assert (Htext7 : sh_text_sub M7)
      by (unfold M7; apply sh_text_sub_store8; [ exact Htext6 | lia ]).
    assert (Hdom7 : forall kk : Z, is_Some (M !! kk) -> is_Some (M7 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom6 kk H))).
    assert (Hne7 : forall k : Z, (k < uint sp0 - 56 \/ uint sp0 - 48 <= k) ->
              M7 !! k = M6 !! k)
      by (intros k Hk; unfold M7; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11e6 : add_vec_int (mword_of_int 0x11e6 : mword 64) 2
                    = mword_of_int 0x11e8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11e6) in "Hpc".
    (* ---- 0x11e8  c.sdsp s6,0(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID18 Psh M7 m10 sp0 (mword_of_int 0x11e8)
              (mword_of_int 0 : mword 6) s6_idx 64 0
              (ui_sh_11e8 pt M7 Hl Htext7) ltac:(exact (uv_stack_dom pt M M7 sp0 64 Hdom7 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp10
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    iEval (rewrite E64_0 (Hpre10 s6_idx ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))) in "Hcg".
    set (M8 := uM_store8 M7 (uint sp0 - 64) (m !!! Regidx s6_idx)).
    assert (Htext8 : sh_text_sub M8)
      by (unfold M8; apply sh_text_sub_store8; [ exact Htext7 | lia ]).
    assert (Hdom8 : forall kk : Z, is_Some (M !! kk) -> is_Some (M8 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom7 kk H))).
    assert (Hne8 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 - 56 <= k) ->
              M8 !! k = M7 !! k)
      by (intros k Hk; unfold M8; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11e8 : add_vec_int (mword_of_int 0x11e8 : mword 64) 2
                    = mword_of_int 0x11ea)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11e8) in "Hpc".
    (* ---- 0x11ea  auipc a5,0x1 ---- *)
    assert (Hauipc2 : (mword_of_int 8682 : mword 64)
                      = add_vec (mword_of_int 0x11ea)
                          (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh M8 m10 (mword_of_int 0x11ea)
              (mword_of_int 1 : mword 20) a5_idx (mword_of_int 8682)
              (ui_sh_11ea pt M8 Hl Htext8)
              ltac:(vm_compute; discriminate) Hauipc2
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 8682 : mword 64)]> m10).
    assert (T11 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              m11 !!! Regidx r = m10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m10 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (E11ea : add_vec_int (mword_of_int 0x11ea : mword 64) 4
                    = mword_of_int 0x11ee)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11ea) in "Hpc".
    (* ---- 0x11ee  addi a5,a5,-354  -- a5 = &base ---- *)
    assert (Ha5_11 : m11 !!! Regidx a5_idx = (mword_of_int 8682 : mword 64))
      by exact (upd_eq m10 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 8682 : mword 64))).
    assert (Haddi1 : (mword_of_int 8328 : mword 64)
                     = add_vec (m11 !!! Regidx a5_idx)
                         (sign_extend' 64 (mword_of_int 3742 : mword 12)))
      by (rewrite Ha5_11; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_addi C pt Psh M8 m11 (mword_of_int 0x11ee)
              (mword_of_int 3742 : mword 12) a5_idx a5_idx (mword_of_int 8328)
              (ui_sh_11ee pt M8 Hl Htext8)
              ltac:(vm_compute; discriminate) Haddi1
              with "Hcg Hpc").
    iIntros (CID21) "Hcg Hpc".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 8328 : mword 64)]> m11).
    assert (T12 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              m12 !!! Regidx r = m11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m11 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (E11ee : add_vec_int (mword_of_int 0x11ee : mword 64) 4
                    = mword_of_int 0x11f2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11ee) in "Hpc".
    (* ---- 0x11f2  auipc a4,0x1 ---- *)
    assert (Hauipc3 : (mword_of_int 8690 : mword 64)
                      = add_vec (mword_of_int 0x11f2)
                          (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh M8 m12 (mword_of_int 0x11f2)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 8690)
              (ui_sh_11f2 pt M8 Hl Htext8)
              ltac:(vm_compute; discriminate) Hauipc3
              with "Hcg Hpc").
    iIntros (CID22) "Hcg Hpc".
    set (m13 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int 8690 : mword 64)]> m12).
    assert (T13 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              m13 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (E11f2 : add_vec_int (mword_of_int 0x11f2 : mword 64) 4
                    = mword_of_int 0x11f6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11f2) in "Hpc".
    assert (Ha4_13 : m13 !!! Regidx a4_idx = (mword_of_int 8690 : mword 64))
      by exact (upd_eq m12 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 8690 : mword 64))).
    assert (Ha5_13 : m13 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64)).
    { rewrite (T13 a5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a5_idx)
               (regval_into_reg (mword_of_int 8328 : mword 64))). }
    (* ---- 0x11f6  sd a5,-482(a4)  -- freep = &base ---- *)
    assert (Hvafp2 : (mword_of_int 8208 : mword 64)
                     = add_vec (m13 !!! Regidx a4_idx)
                         (sign_extend' 64 (mword_of_int 3614 : mword 12)))
      by (rewrite Ha4_13; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_sd C pt Psh M8 m13 (mword_of_int 0x11f6)
              (mword_of_int 3614 : mword 12) a4_idx a5_idx
              wfp (mword_of_int 8208) (mword_of_int 8328)
              (ui_sh_11f6 pt M8 Hl Htext8)
              Hvafp2 (eq_sym Ha5_13) Hwfp Hwfps Hcnfp Hpgfp Halfp
              ltac:(rewrite Hufp; exact (Hbeb M8 8208 8%nat Hdom8
                                           ltac:(lia) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID23) "Hcg Hpc".
    iEval (rewrite Hufp) in "Hcg".
    set (M9 := uM_store8 M8 8208 (mword_of_int 8328 : mword 64)).
    assert (Htext9 : sh_text_sub M9)
      by (unfold M9; apply sh_text_sub_store8; [ exact Htext8 | lia ]).
    assert (Hdom9 : forall kk : Z, is_Some (M !! kk) -> is_Some (M9 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom8 kk H))).
    assert (Hne9 : forall k : Z, (k < 8208 \/ 8216 <= k) -> M9 !! k = M8 !! k)
      by (intros k Hk; unfold M9; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11f6 : add_vec_int (mword_of_int 0x11f6 : mword 64) 4
                    = mword_of_int 0x11fa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11f6) in "Hpc".
    (* ---- 0x11fa  c.sd a5,0(a5)  -- base.s.ptr = &base ---- *)
    assert (Hvabs : (mword_of_int 8328 : mword 64)
                    = add_vec (m13 !!! Regidx a5_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 0 : mword 5) ('b"000")))))
      by (rewrite Ha5_13; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_csd C pt Psh M9 m13 (mword_of_int 0x11fa)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx
              wbs (mword_of_int 8328) (mword_of_int 8328)
              (ui_sh_11fa pt M9 Hl Htext9)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hvabs (eq_sym Ha5_13) Hwbs Hwbss Hcnbs Hpgbs Halbs
              ltac:(rewrite Hubs; exact (Hbeb M9 8328 8%nat Hdom9
                                           ltac:(lia) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID24) "Hcg Hpc".
    iEval (rewrite Hubs) in "Hcg".
    set (M10 := uM_store8 M9 8328 (mword_of_int 8328 : mword 64)).
    assert (Htext10 : sh_text_sub M10)
      by (unfold M10; apply sh_text_sub_store8; [ exact Htext9 | lia ]).
    assert (Hdom10 : forall kk : Z, is_Some (M !! kk) -> is_Some (M10 !! kk))
      by (intros kk H; exact (uM_store8_is_Some _ _ _ kk (Hdom9 kk H))).
    assert (Hne10 : forall k : Z, (k < 8328 \/ 8336 <= k) -> M10 !! k = M9 !! k)
      by (intros k Hk; unfold M10; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E11fa : add_vec_int (mword_of_int 0x11fa : mword 64) 2
                    = mword_of_int 0x11fc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11fa) in "Hpc".
    (* ---- 0x11fc  sw zero,8(a5)  -- base.s.size = 0 ---- *)
    iDestruct (uv_x0 CID24 M10 m13 with "Hcg") as "[%Hzr Hcg]".
    assert (Hvasz : (mword_of_int 8336 : mword 64)
                    = add_vec (m13 !!! Regidx a5_idx)
                        (sign_extend' 64 (mword_of_int 8 : mword 12)))
      by (rewrite Ha5_13; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_sw C pt Psh M10 m13 (mword_of_int 0x11fc)
              (mword_of_int 8 : mword 12) a5_idx (mword_of_int 0 : mword 5)
              wsz (mword_of_int 8336) (mword_of_int 0)
              (ui_sh_11fc pt M10 Hl Htext10)
              Hvasz ltac:(rewrite Hzr; symmetry; exact zero_reg_moi)
              Hwsz Hwszs Hcnsz Hpgsz Halsz
              ltac:(rewrite Husz; exact (Hbeb M10 8336 4%nat Hdom10
                                           ltac:(lia) ltac:(lia)))
              with "Hcg Hpc").
    iIntros (CID25) "Hcg Hpc".
    iEval (rewrite Husz) in "Hcg".
    set (M11 := uM_store M10 8336 4 (mword_of_int 0 : mword 64)).
    assert (Htext11 : sh_text_sub M11)
      by (unfold M11; apply sh_text_sub_store4; [ exact Htext10 | lia ]).
    assert (Hdom11 : forall kk : Z, is_Some (M !! kk) -> is_Some (M11 !! kk))
      by (intros kk H; exact (uM_store_is_Some _ _ _ _ kk (Hdom10 kk H))).
    assert (Hne11 : forall k : Z, (k < 8336 \/ 8340 <= k) -> M11 !! k = M10 !! k)
      by (intros k Hk; unfold M11; apply uM_store_lookup_ne; intros j Hj; lia).
    assert (E11fc : add_vec_int (mword_of_int 0x11fc : mword 64) 4
                    = mword_of_int 0x1200)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11fc) in "Hpc".
    (* ---- 0x1200  c.j 0x11c4 ---- *)
    assert (Htj : (mword_of_int 0x11c4 : mword 64)
                  = add_vec (mword_of_int 0x1200)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2018 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cj C pt Psh M11 m13 (mword_of_int 0x1200)
              (mword_of_int 2018 : mword 11) (mword_of_int 0x11c4)
              (ui_sh_1200 pt M11 Hl Htext11) Htj
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID26) "Hcg Hpc".
    (* ---- 0x11c4  c.mv s4,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (T13 s3_idx ltac:(vm_compute; discriminate))
              (T12 s3_idx ltac:(vm_compute; discriminate))
              (T11 s3_idx ltac:(vm_compute; discriminate)).
      exact Hs3_10. }
    assert (Hmv2 : (mword_of_int (q + 1) : mword 64)
                   = add_vec zero_reg (m13 !!! Regidx s3_idx))
      by (rewrite Hs3_13 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M11 m13 (mword_of_int 0x11c4)
              s4_idx s3_idx (mword_of_int (q + 1))
              (ui_sh_11c4 pt M11 Hl Htext11)
              ltac:(vm_compute; discriminate) Hmv2
              with "Hcg Hpc").
    iIntros (CID27) "Hcg Hpc".
    set (m14 := <[Regidx s4_idx
                  := regval_into_reg (mword_of_int (q + 1) : mword 64)]> m13).
    assert (T14 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              m14 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (E11c4 : add_vec_int (mword_of_int 0x11c4 : mword 64) 2
                    = mword_of_int 0x11c6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11c4) in "Hpc".
    (* ---- 0x11c6  c.lui a4,0x1 ---- *)
    iApply (wp_uv_clui C pt Psh M11 m14 (mword_of_int 0x11c6)
              (mword_of_int 1 : mword 6) a4_idx (mword_of_int 4096)
              (ui_sh_11c6 pt M11 Hl Htext11)
              ltac:(vm_compute; discriminate)
              ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID28) "Hcg Hpc".
    set (m15 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int 4096 : mword 64)]> m14).
    assert (T15 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              m15 !!! Regidx r = m14 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m14 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (E11c6 : add_vec_int (mword_of_int 0x11c6 : mword 64) 2
                    = mword_of_int 0x11c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E11c6) in "Hpc".
    (* ---- what the head leaves for the tail ---- *)
    assert (RBra : uM_bytes M11 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne6 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne5 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne4 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne3 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
              (Hne2 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (RBs0 : uM_bytes M11 (uint sp0 - 16) 8 (m !!! Regidx s0_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne6 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne5 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne4 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
              (Hne3 (uint sp0 - 16 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx) j Hj). }
    assert (RBs2 : uM_bytes M11 (uint sp0 - 32) 8 (m !!! Regidx s2_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne6 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne5 (uint sp0 - 32 + Z.of_nat j) ltac:(lia))
              (Hne4 (uint sp0 - 32 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M2 (uint sp0 - 32) (m !!! Regidx s2_idx) j Hj). }
    assert (RBs3 : uM_bytes M11 (uint sp0 - 40) 8 (m !!! Regidx s3_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne6 (uint sp0 - 40 + Z.of_nat j) ltac:(lia))
              (Hne5 (uint sp0 - 40 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M3 (uint sp0 - 40) (m !!! Regidx s3_idx) j Hj). }
    assert (RBs1 : uM_bytes M11 (uint sp0 - 24) 8 (m !!! Regidx s1_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 24 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 24 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 24 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 24 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 24 + Z.of_nat j) ltac:(lia))
              (Hne6 (uint sp0 - 24 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M4 (uint sp0 - 24) (m !!! Regidx s1_idx) j Hj). }
    assert (RBs4 : uM_bytes M11 (uint sp0 - 48) 8 (m !!! Regidx s4_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 48 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 48 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 48 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 48 + Z.of_nat j) ltac:(lia))
              (Hne7 (uint sp0 - 48 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M5 (uint sp0 - 48) (m !!! Regidx s4_idx) j Hj). }
    assert (RBs5 : uM_bytes M11 (uint sp0 - 56) 8 (m !!! Regidx s5_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 56 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 56 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 56 + Z.of_nat j) ltac:(lia))
              (Hne8 (uint sp0 - 56 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M6 (uint sp0 - 56) (m !!! Regidx s5_idx) j Hj). }
    assert (RBs6 : uM_bytes M11 (uint sp0 - 64) 8 (m !!! Regidx s6_idx)).
    { intros j Hj.
      rewrite (Hne11 (uint sp0 - 64 + Z.of_nat j) ltac:(lia))
              (Hne10 (uint sp0 - 64 + Z.of_nat j) ltac:(lia))
              (Hne9 (uint sp0 - 64 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M7 (uint sp0 - 64) (m !!! Regidx s6_idx) j Hj). }
    assert (RBfp : uM_bytes M11 8208 8 (mword_of_int 8328 : mword 64)).
    { intros j Hj.
      rewrite (Hne11 (8208 + Z.of_nat j) ltac:(lia))
              (Hne10 (8208 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M8 8208 (mword_of_int 8328 : mword 64) j Hj). }
    assert (RBbs : uM_bytes M11 8328 8 (mword_of_int 8328 : mword 64)).
    { intros j Hj.
      rewrite (Hne11 (8328 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M9 8328 (mword_of_int 8328 : mword 64) j Hj). }
    assert (RBsz : uM_bytes M11 8336 8 (mword_of_int 0 : mword 64)).
    { intros j Hj.
      destruct (decide (j < 4)%nat) as [ Hlt | Hge ].
      - exact (uM_store_bytes M10 8336 4 (mword_of_int 0 : mword 64) j
                 ltac:(change (Z.to_nat 4) with 4%nat; lia)).
      - rewrite (Hne11 (8336 + Z.of_nat j) ltac:(lia))
                (Hne10 (8336 + Z.of_nat j) ltac:(lia))
                (Hne9 (8336 + Z.of_nat j) ltac:(lia))
                (Hne8 (8336 + Z.of_nat j) ltac:(lia))
                (Hne7 (8336 + Z.of_nat j) ltac:(lia))
                (Hne6 (8336 + Z.of_nat j) ltac:(lia))
                (Hne5 (8336 + Z.of_nat j) ltac:(lia))
                (Hne4 (8336 + Z.of_nat j) ltac:(lia))
                (Hne3 (8336 + Z.of_nat j) ltac:(lia))
                (Hne2 (8336 + Z.of_nat j) ltac:(lia))
                (Hne1 (8336 + Z.of_nat j) ltac:(lia)).
        rewrite nth_byte_moi0.
        exact (Hbasesz0 (Z.of_nat j) ltac:(lia)). }
    assert (RBwr : uv_wr pt M11 8208 136)
      by exact (uv_wr_dom pt M M11 8208 136 Hdom11 Hbssw).
    assert (RBst : uv_stack pt M11 sp0 96)
      by exact (uv_stack_dom pt M M11 sp0 96 Hdom11 Hst).
    assert (HonlyB : uM_only_in M M11 [(hbase, 65536); (8208, 8); (8328, 16);
                                       (uint sp0 - 96, 96)]).
    { split; [ exact Hdom11 | ].
      intros k Hk.
      pose proof (not_in_window _ 8208 8 k
                    ltac:(apply elem_of_list_further; apply elem_of_list_here) Hk)
        as W2.
      pose proof (not_in_window _ 8328 16 k
                    ltac:(apply elem_of_list_further; apply elem_of_list_further;
                          apply elem_of_list_here) Hk) as W3.
      pose proof (not_in_window _ (uint sp0 - 96) 96 k
                    ltac:(apply elem_of_list_further; apply elem_of_list_further;
                          apply elem_of_list_further; apply elem_of_list_here) Hk)
        as W4.
      rewrite (Hne11 k ltac:(lia)) (Hne10 k ltac:(lia)) (Hne9 k ltac:(lia))
              (Hne8 k ltac:(lia)) (Hne7 k ltac:(lia)) (Hne6 k ltac:(lia))
              (Hne5 k ltac:(lia)) (Hne4 k ltac:(lia)) (Hne3 k ltac:(lia))
              (Hne2 k ltac:(lia)) (Hne1 k ltac:(lia)).
      reflexivity. }
    (* ---- 0x11c8  bgeu s3,a4,0x11ce  -- morecore's `nu < 4096' clamp ---- *)
    assert (Hs3_15 : m15 !!! Regidx s3_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (T15 s3_idx ltac:(vm_compute; discriminate))
              (T14 s3_idx ltac:(vm_compute; discriminate)).
      exact Hs3_13. }
    assert (Ha4_15 : m15 !!! Regidx a4_idx = (mword_of_int 4096 : mword 64))
      by exact (upd_eq m14 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 4096 : mword 64))).
    assert (Hs4_15 : m15 !!! Regidx s4_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (T15 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx s4_idx)
               (regval_into_reg (mword_of_int (q + 1) : mword 64))). }
    assert (Ha5_15 : m15 !!! Regidx a5_idx = (mword_of_int 8328 : mword 64)).
    { rewrite (T15 a5_idx ltac:(vm_compute; discriminate))
              (T14 a5_idx ltac:(vm_compute; discriminate)).
      exact Ha5_13. }
    assert (Hs2_15 : m15 !!! Regidx s2_idx = (mword_of_int (q + 1) : mword 64)).
    { rewrite (T15 s2_idx ltac:(vm_compute; discriminate))
              (T14 s2_idx ltac:(vm_compute; discriminate))
              (T13 s2_idx ltac:(vm_compute; discriminate))
              (T12 s2_idx ltac:(vm_compute; discriminate))
              (T11 s2_idx ltac:(vm_compute; discriminate)).
      exact Hs2_10. }
    assert (Hsp15 : m15 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (T15 sp_idx ltac:(vm_compute; discriminate))
              (T14 sp_idx ltac:(vm_compute; discriminate))
              (T13 sp_idx ltac:(vm_compute; discriminate))
              (T12 sp_idx ltac:(vm_compute; discriminate))
              (T11 sp_idx ltac:(vm_compute; discriminate)).
      exact Hsp10. }
    assert (Hoth15 : forall r : mword 5,
              ucallee_saved_idx r = true ->
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
              m15 !!! Regidx r = m !!! Regidx r).
    { intros r Hcs Nsp Ns0 N1 N2 N3 N4 N5 N6.
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcs; discriminate).
      assert (Na4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcs; discriminate).
      assert (Na5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcs; discriminate).
      rewrite (T15 r Na4) (T14 r N4) (T13 r Na4) (T12 r Na5) (T11 r Na5).
      exact (Hpre10 r Nsp Ns0 N2 N3 Na0). }
    assert (Htgtb : (mword_of_int 0x11ce : mword 64)
                    = add_vec (mword_of_int 0x11c8)
                        (sign_extend' 64 (mword_of_int 6 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec q 4095) as [ Hq95 | Hq95 ].
    - (* nunits = 4096 already: the clamp at 0x11cc is SKIPPED *)
      assert (Htkb : true = uv_btaken BGEU (m15 !!! Regidx s3_idx)
                              (m15 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Hs3_15 Ha4_15.
        rewrite (moi_ge_u (q + 1) 4096 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. rewrite Z.geb_leb. apply Z.leb_le. lia. }
      iApply (wp_uv_btype C pt Psh M11 m15 (mword_of_int 0x11c8)
                (mword_of_int 6 : mword 13) a4_idx s3_idx BGEU
                true (mword_of_int 0x11ce)
                (ui_sh_11c8 pt M11 Hl Htext11) Htkb Htgtb
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID29) "Hcg Hpc".
      iApply (wp_sh_malloc_tail CID29 M M11 m m15 sp0 nbytes
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
                (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) (m !!! Regidx s4_idx)
                (m !!! Regidx s5_idx) (m !!! Regidx s6_idx)
                Hlay Htext11 RBst ltac:(lia) ltac:(rewrite Hqdef; lia)
                ltac:(unfold sh_frame_ok; lia)
                Hret2 Hsp eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl
                RBra RBs0 RBs1 RBs2 RBs3 RBs4 RBs5 RBs6
                RBfp RBbs RBsz RBwr HonlyB
                Hsp15 Ha5_15 Hs2_15 Hs3_15
                ltac:(rewrite Hs4_15; f_equal; lia) Hoth15
                with "Hcg Hbrk Hpc Hcont").
    - (* nunits < 4096: the clamp runs ---- 0x11cc  c.lui s4,0x1 ---- *)
      assert (Htkb : false = uv_btaken BGEU (m15 !!! Regidx s3_idx)
                               (m15 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Hs3_15 Ha4_15.
        rewrite (moi_ge_u (q + 1) 4096 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      iApply (wp_uv_btype C pt Psh M11 m15 (mword_of_int 0x11c8)
                (mword_of_int 6 : mword 13) a4_idx s3_idx BGEU
                false (mword_of_int 0x11ce)
                (ui_sh_11c8 pt M11 Hl Htext11) Htkb Htgtb
                ltac:(intro Hcc; discriminate Hcc)
                with "Hcg Hpc").
      iIntros (CID29) "Hcg Hpc".
      assert (E11c8 : (if false then (mword_of_int 0x11ce : mword 64)
                       else add_vec_int (mword_of_int 0x11c8 : mword 64) 4)
                      = mword_of_int 0x11cc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E11c8) in "Hpc".
      iApply (wp_uv_clui C pt Psh M11 m15 (mword_of_int 0x11cc)
                (mword_of_int 1 : mword 6) s4_idx (mword_of_int 4096)
                (ui_sh_11cc pt M11 Hl Htext11)
                ltac:(vm_compute; discriminate)
                ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID30) "Hcg Hpc".
      set (m16 := <[Regidx s4_idx
                    := regval_into_reg (mword_of_int 4096 : mword 64)]> m15).
      assert (T16 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
                m16 !!! Regidx r = m15 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m15 (Regidx s4_idx) (Regidx r) _ Hr)).
      assert (E11cc : add_vec_int (mword_of_int 0x11cc : mword 64) 2
                      = mword_of_int 0x11ce)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E11cc) in "Hpc".
      iApply (wp_sh_malloc_tail CID30 M M11 m m16 sp0 nbytes
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) (m !!! Regidx s1_idx)
                (m !!! Regidx s2_idx) (m !!! Regidx s3_idx) (m !!! Regidx s4_idx)
                (m !!! Regidx s5_idx) (m !!! Regidx s6_idx)
                Hlay Htext11 RBst ltac:(lia) ltac:(rewrite Hqdef; lia)
                ltac:(unfold sh_frame_ok; lia)
                Hret2 Hsp eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl
                RBra RBs0 RBs1 RBs2 RBs3 RBs4 RBs5 RBs6
                RBfp RBbs RBsz RBwr HonlyB
                ltac:(rewrite (T16 sp_idx ltac:(vm_compute; discriminate));
                      exact Hsp15)
                ltac:(rewrite (T16 a5_idx ltac:(vm_compute; discriminate));
                      exact Ha5_15)
                ltac:(rewrite (T16 s2_idx ltac:(vm_compute; discriminate));
                      exact Hs2_15)
                ltac:(rewrite (T16 s3_idx ltac:(vm_compute; discriminate));
                      exact Hs3_15)
                ltac:(exact (upd_eq m15 (Regidx s4_idx)
                               (regval_into_reg (mword_of_int 4096 : mword 64))))
                ltac:(intros r Hcs Nsp Ns0 N1 N2 N3 N4 N5 N6;
                      rewrite (T16 r N4); exact (Hoth15 r Hcs Nsp Ns0 N1 N2 N3 N4 N5 N6))
                with "Hcg Hbrk Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5 execcmd @0x1d2.                                                    *)
  (*                                                                      *)
  (*   1d2..1da  the 32-byte frame (ra/s0/s1)                             *)
  (*   1dc..1e4  cmd = malloc(168);  s1 = cmd                             *)
  (*   1e6..1ec  memset(cmd, 0, 168)                                      *)
  (*   1f0..1f4  cmd->type = EXEC;  return cmd                            *)
  (*   1f6..1fe  the frame back                                            *)
  (*                                                                      *)
  (* [Hfr] is drift note D3: [wp_sh_execcmd_body] does not carry the       *)
  (* frame-clears-the-image premise its call to malloc needs.              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_execcmd (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_sh_execcmd_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0.
  Proof.
    intros Hlay Htext Hsp Hst Hfreep0 Hbasesz0 Hbssw Hfr Hret2.
    assert (Hesym : ShSyms.execcmd = 0x1d2)
      by (destruct sh_syms_pins as (_&_&_&_&_&_&H&_); exact H).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    unfold SH_DATA_PG in Hhlo. unfold sh_frame_ok in Hfr.
    change (2 ^ 38) with 274877906944 in Hhhi, Hcan.
    change SH_FREEP with 8208 in *. change SH_BASE with 8328 in *.
    change SH_FREEP with 8208 in Hfreep0.
    change (SH_BASE + 8) with 8336 in Hbasesz0.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    assert (Hnu12 : sh_nunits 168 = 12) by (vm_compute; reflexivity).
    assert (Hub0 : bv_unsigned ubyte0 = 0) by (vm_compute; reflexivity).
    assert (Hsphi : 77952 <= uint sp0) by lia.
    assert (Hhb4 : hbase mod 4 = 0).
    { assert (Hd : (4 | 4096)) by (exists 1024; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 4 4096 hbase ltac:(lia) ltac:(lia) Hd).
      rewrite Hhb. reflexivity. }
    pose proof (uv_stack_split pt M sp0 128 32 96 ltac:(lia) ltac:(lia)
                  ltac:(vm_compute; reflexivity) ltac:(lia) Hst) as Hsplit.
    assert (Hst32 : uv_stack pt M sp0 32) by exact (proj1 Hsplit).
    assert (Hsplo : add_vec_int sp0 (- 32)
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (uv_stack_sp_moi pt M sp0 32 Hst32).
    assert (Hst96 : uv_stack pt M (mword_of_int (uint sp0 - 32)) 96)
      by (rewrite <- Hsplo; exact (proj2 Hsplit)).
    assert (Hu32 : uint (mword_of_int (uint sp0 - 32) : mword 64)
                   = uint sp0 - 32)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hst16 : uv_stack pt M (mword_of_int (uint sp0 - 32)) 16)
      by exact (proj1 (uv_stack_split pt M (mword_of_int (uint sp0 - 32)) 96 16 80
                         ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                         ltac:(lia) Hst96)).
    (* the three frame slots *)
    (* the three frame slots, as absolute addresses *)
    assert (Ea24 : uint sp0 - 32 + 24 = uint sp0 - 8) by lia.
    assert (Ea16 : uint sp0 - 32 + 16 = uint sp0 - 16) by lia.
    assert (Ea08 : uint sp0 - 32 + 8 = uint sp0 - 24) by lia.
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hesym) in "Hpc".
    (* ---- 0x1d2  c.addi sp,sp,-32 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 32) : mword 64)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12
                          (mword_of_int 32 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                    : mword 64) = mword_of_int (-32))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh M m (mword_of_int 0x1d2)
              (mword_of_int 32 : mword 6) sp_idx (mword_of_int (uint sp0 - 32))
              (ui_sh_1d2 pt M Hl Htext)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (e1 := <[Regidx sp_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64)]> m).
    assert (Y1 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              e1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx sp_idx) (Regidx r) _ Hr)).
    assert (Hsp1 : e1 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64))).
    assert (E1d2 : add_vec_int (mword_of_int 0x1d2 : mword 64) 2
                   = mword_of_int 0x1d4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1d2) in "Hpc".
    (* ---- 0x1d4  c.sdsp ra,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID1 Psh M e1 sp0 (mword_of_int 0x1d4)
              (mword_of_int 3 : mword 6) ra_idx 32 24
              (ui_sh_1d4 pt M Hl Htext) Hst32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Ea24 (Y1 ra_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom1 : forall k : Z, is_Some (M !! k) -> is_Some (M1 !! k))
      by (intros k H; exact (uM_store8_is_Some _ _ _ k H)).
    assert (Hne1 : forall k : Z, (k < uint sp0 - 8 \/ uint sp0 <= k) ->
              M1 !! k = M !! k)
      by (intros k Hk; unfold M1; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1d4 : add_vec_int (mword_of_int 0x1d4 : mword 64) 2
                   = mword_of_int 0x1d6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1d4) in "Hpc".
    (* ---- 0x1d6  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID2 Psh M1 e1 sp0 (mword_of_int 0x1d6)
              (mword_of_int 2 : mword 6) s0_idx 32 16
              (ui_sh_1d6 pt M1 Hl Htext1)
              ltac:(exact (uv_stack_dom pt M M1 sp0 32 Hdom1 Hst32))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite Ea16 (Y1 s0_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k))
      by (intros k H; exact (uM_store8_is_Some _ _ _ k (Hdom1 k H))).
    assert (Hne2 : forall k : Z, (k < uint sp0 - 16 \/ uint sp0 - 8 <= k) ->
              M2 !! k = M1 !! k)
      by (intros k Hk; unfold M2; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (E1d6 : add_vec_int (mword_of_int 0x1d6 : mword 64) 2
                   = mword_of_int 0x1d8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1d6) in "Hpc".
    (* ---- 0x1d8  c.sdsp s1,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID3 Psh M2 e1 sp0 (mword_of_int 0x1d8)
              (mword_of_int 1 : mword 6) s1_idx 32 8
              (ui_sh_1d8 pt M2 Hl Htext2)
              ltac:(exact (uv_stack_dom pt M M2 sp0 32 Hdom2 Hst32))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite Ea08 (Y1 s1_idx ltac:(vm_compute; discriminate))) in "Hcg".
    set (M3 := uM_store8 M2 (uint sp0 - 24) (m !!! Regidx s1_idx)).
    assert (Htext3 : sh_text_sub M3)
      by (unfold M3; apply sh_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall k : Z, is_Some (M !! k) -> is_Some (M3 !! k))
      by (intros k H; exact (uM_store8_is_Some _ _ _ k (Hdom2 k H))).
    assert (Hne3 : forall k : Z, (k < uint sp0 - 24 \/ uint sp0 - 16 <= k) ->
              M3 !! k = M2 !! k)
      by (intros k Hk; unfold M3; apply uM_store8_lookup_ne; intros j Hj; lia).
    assert (HeqM3 : forall k : Z, (k < uint sp0 - 24 \/ uint sp0 <= k) ->
              M3 !! k = M !! k)
      by (intros k Hk; rewrite (Hne3 k ltac:(lia)) (Hne2 k ltac:(lia));
          exact (Hne1 k ltac:(lia))).
    assert (E1d8 : add_vec_int (mword_of_int 0x1d8 : mword 64) 2
                   = mword_of_int 0x1da)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1d8) in "Hpc".
    (* ---- 0x1da  c.addi4spn s0,sp,32 ---- *)
    assert (Hw32 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (e1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh M3 e1 (mword_of_int 0x1da)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_1da pt M3 Hl Htext3)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw32
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (e2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> e1).
    assert (Y2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              e2 !!! Regidx r = e1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (E1da : add_vec_int (mword_of_int 0x1da : mword 64) 2
                   = mword_of_int 0x1dc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1da) in "Hpc".
    (* ---- 0x1dc  li a0,168 ---- *)
    assert (Hli0 : (mword_of_int 168 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (mword_of_int 168 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_li C pt Psh M3 e2 (mword_of_int 0x1dc)
              (mword_of_int 168 : mword 12) a0_idx
              (mword_of_int 168)
              (ui_sh_1dc pt M3 Hl Htext3)
              ltac:(vm_compute; discriminate) Hli0
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    set (e3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> e2).
    assert (Y3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              e3 !!! Regidx r = e2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e2 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1dc : add_vec_int (mword_of_int 0x1dc : mword 64) 4
                   = mword_of_int 0x1e0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1dc) in "Hpc".
    (* ---- 0x1e0  jal ra,0x118c <malloc> ---- *)
    assert (Hmsym : ShSyms.malloc = 0x118c)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    assert (Htgtm : (mword_of_int 0x118c : mword 64)
                    = add_vec (mword_of_int 0x1e0)
                        (sign_extend' 64 (mword_of_int 4012 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnkm : (mword_of_int 0x1e4 : mword 64)
                    = add_vec_int (mword_of_int 0x1e0 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh M3 e3 (mword_of_int 0x1e0)
              (mword_of_int 4012 : mword 21) ra_idx
              (mword_of_int 0x118c) (mword_of_int 0x1e4)
              (ui_sh_1e0 pt M3 Hl Htext3)
              ltac:(vm_compute; discriminate) Htgtm Hlnkm
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (e4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1e4 : mword 64)]> e3).
    assert (Y4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              e4 !!! Regidx r = e3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne e3 (Regidx ra_idx) (Regidx r) _ Hr)).
    iEval (rewrite <- Hmsym) in "Hpc".
    assert (Hra4 : e4 !!! Regidx ra_idx = (mword_of_int 0x1e4 : mword 64))
      by exact (upd_eq e3 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x1e4 : mword 64))).
    assert (Ha0_4 : e4 !!! Regidx a0_idx = (mword_of_int 168 : mword 64)).
    { rewrite (Y4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq e2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 168 : mword 64))). }
    assert (Hsp4 : e4 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (Y4 sp_idx ltac:(vm_compute; discriminate))
              (Y3 sp_idx ltac:(vm_compute; discriminate))
              (Y2 sp_idx ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* the .bss and the stack, as malloc needs them *)
    assert (Hfreep03 : sh_zeroed M3 8208 0 8)
      by (intros j Hj; rewrite (HeqM3 (8208 + j) ltac:(lia)); exact (Hfreep0 j Hj)).
    assert (Hbasesz03 : sh_zeroed M3 8336 0 8)
      by (intros j Hj; rewrite (HeqM3 (8336 + j) ltac:(lia)); exact (Hbasesz0 j Hj)).
    assert (Hbssw3 : uv_wr pt M3 8208 136)
      by exact (uv_wr_dom pt M M3 8208 136 Hdom3 Hbssw).
    assert (Hst96_3 : uv_stack pt M3 (mword_of_int (uint sp0 - 32)) 96)
      by exact (uv_stack_dom pt M M3 _ 96 Hdom3 Hst96).
    (* ---- the call: malloc(168) ---- *)
    iApply (wp_sh_malloc_first CID7 M3 e4 (mword_of_int (uint sp0 - 32)) 168
              Hlay Htext3 Hsp4 Hst96_3 Ha0_4
              ltac:(rewrite Hnu12; lia) Hfreep03 Hbasesz03 Hbssw3
              ltac:(unfold sh_frame_ok; rewrite Hu32; lia)
              ltac:(rewrite Hra4; vm_compute; reflexivity)
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CID8 f0 M4) "%Hcsm %Ha0_m %Hwr_m %Honly_m Hbrk Hcg Hpc".
    rewrite Hnu12 in Ha0_m.
    rewrite Hnu12 in Hwr_m.
    change SH_FREEP with 8208 in Honly_m.
    change SH_BASE with 8328 in Honly_m.
    rewrite Hu32 in Honly_m.
    replace (hbase + 65536 - 16 * (12 - 1)) with (hbase + 65360) in Ha0_m by lia.
    replace (hbase + 65536 - 16 * (12 - 1)) with (hbase + 65360) in Hwr_m by lia.
    replace (16 * (12 - 1)) with 176 in Hwr_m by lia.
    iEval (rewrite Hra4) in "Hpc".
    (* what survived malloc *)
    assert (Hdom4 : forall k : Z, is_Some (M3 !! k) -> is_Some (M4 !! k))
      by exact (proj1 Honly_m).
    assert (Hout4 : forall k : Z,
              (k < hbase \/ hbase + 65536 <= k) ->
              (k < 8208 \/ 8216 <= k) -> (k < 8328 \/ 8344 <= k) ->
              (k < uint sp0 - 128 \/ uint sp0 - 32 <= k) -> M4 !! k = M3 !! k).
    { intros k H1 H2 H3 H4. apply (proj2 Honly_m). intros (w & Hw & Hin).
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_nil in Hw. exact Hw. }
    assert (Htext4 : sh_text_sub M4).
    { intros k b Hk. pose proof (sh_bytes_key_lt k b Hk) as Hkl.
      rewrite (Hout4 k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (Htext3 k b Hk). }
    assert (Hfrm4 : forall k : Z, uint sp0 - 32 <= k < uint sp0 ->
              M4 !! k = M3 !! k)
      by (intros k Hk; exact (Hout4 k ltac:(lia) ltac:(lia) ltac:(lia)
                                ltac:(lia))).
    assert (Hst4 : uv_stack pt M4 sp0 128)
      by exact (uv_stack_dom pt M3 M4 sp0 128 Hdom4
                  (uv_stack_dom pt M M3 sp0 128 Hdom3 Hst)).
    assert (Hst16_4 : uv_stack pt M4 (mword_of_int (uint sp0 - 32)) 16)
      by exact (uv_stack_dom pt M M4 _ 16 (fun k H => Hdom4 k (Hdom3 k H)) Hst16).
    (* ---- 0x1e4  c.mv s1,a0 ---- *)
    assert (Hmv1 : (mword_of_int (hbase + 65360) : mword 64)
                   = add_vec zero_reg (f0 !!! Regidx a0_idx))
      by (rewrite Ha0_m moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M4 f0 (mword_of_int 0x1e4)
              s1_idx a0_idx (mword_of_int (hbase + 65360))
              (ui_sh_1e4 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    set (f1 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (hbase + 65360) : mword 64)]> f0).
    assert (Z1 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              f1 !!! Regidx r = f0 !!! Regidx r)
      by (intros r Hr; exact (upd_ne f0 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (E1e4 : add_vec_int (mword_of_int 0x1e4 : mword 64) 2
                   = mword_of_int 0x1e6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1e4) in "Hpc".
    (* ---- 0x1e6  li a2,168 ---- *)
    assert (Hli2 : (mword_of_int 168 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (mword_of_int 168 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_li C pt Psh M4 f1 (mword_of_int 0x1e6)
              (mword_of_int 168 : mword 12) a2_idx
              (mword_of_int 168)
              (ui_sh_1e6 pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hli2
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    set (f2 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> f1).
    assert (Z2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
              f2 !!! Regidx r = f1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne f1 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (E1e6 : add_vec_int (mword_of_int 0x1e6 : mword 64) 4
                   = mword_of_int 0x1ea)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1e6) in "Hpc".
    (* ---- 0x1ea  c.li a1,0 ---- *)
    assert (Hli1 : (mword_of_int 0 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12
                          (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh M4 f2 (mword_of_int 0x1ea)
              (mword_of_int 0 : mword 6) a1_idx (mword_of_int 0)
              (ui_sh_1ea pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Hli1
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (f3 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> f2).
    assert (Z3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              f3 !!! Regidx r = f2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne f2 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (E1ea : add_vec_int (mword_of_int 0x1ea : mword 64) 2
                   = mword_of_int 0x1ec)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1ea) in "Hpc".
    (* ---- 0x1ec  jal ra,0xa5c <memset> ---- *)
    assert (Hmssym : ShSyms.memset = 0xa5c)
      by (destruct sh_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    assert (Htgts : (mword_of_int 0xa5c : mword 64)
                    = add_vec (mword_of_int 0x1ec)
                        (sign_extend' 64 (mword_of_int 2160 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnks : (mword_of_int 0x1f0 : mword 64)
                    = add_vec_int (mword_of_int 0x1ec : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh M4 f3 (mword_of_int 0x1ec)
              (mword_of_int 2160 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x1f0)
              (ui_sh_1ec pt M4 Hl Htext4)
              ltac:(vm_compute; discriminate) Htgts Hlnks
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (f4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1f0 : mword 64)]> f3).
    assert (Z4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              f4 !!! Regidx r = f3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne f3 (Regidx ra_idx) (Regidx r) _ Hr)).
    iEval (rewrite <- Hmssym) in "Hpc".
    assert (Hra_f4 : f4 !!! Regidx ra_idx = (mword_of_int 0x1f0 : mword 64))
      by exact (upd_eq f3 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x1f0 : mword 64))).
    assert (Ha0_f4 : f4 !!! Regidx a0_idx
                     = (mword_of_int (hbase + 65360) : mword 64)).
    { rewrite (Z4 a0_idx ltac:(vm_compute; discriminate))
              (Z3 a0_idx ltac:(vm_compute; discriminate))
              (Z2 a0_idx ltac:(vm_compute; discriminate))
              (Z1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_m. }
    assert (Ha1_f4 : f4 !!! Regidx a1_idx
                     = (mword_of_int (bv_unsigned ubyte0) : mword 64)).
    { rewrite Hub0 (Z4 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq f2 (Regidx a1_idx)
               (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Ha2_f4 : f4 !!! Regidx a2_idx = (mword_of_int 168 : mword 64)).
    { rewrite (Z4 a2_idx ltac:(vm_compute; discriminate))
              (Z3 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq f1 (Regidx a2_idx)
               (regval_into_reg (mword_of_int 168 : mword 64))). }
    assert (Hsp_f4 : f4 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (Z4 sp_idx ltac:(vm_compute; discriminate))
              (Z3 sp_idx ltac:(vm_compute; discriminate))
              (Z2 sp_idx ltac:(vm_compute; discriminate))
              (Z1 sp_idx ltac:(vm_compute; discriminate))
              (Hcsm sp_idx ltac:(vm_compute; reflexivity)). exact Hsp4. }
    assert (Hs1_f4 : f4 !!! Regidx s1_idx
                     = (mword_of_int (hbase + 65360) : mword 64)).
    { rewrite (Z4 s1_idx ltac:(vm_compute; discriminate))
              (Z3 s1_idx ltac:(vm_compute; discriminate))
              (Z2 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq f0 (Regidx s1_idx)
               (regval_into_reg (mword_of_int (hbase + 65360) : mword 64))). }
    (* ---- the call: memset(cmd, 0, 168) ---- *)
    iApply (wp_sh_memset C pt gin gbrk hbase hlen Q CID12 M4 f4
              (mword_of_int (uint sp0 - 32)) (hbase + 65360) 168 ubyte0
              Hlay Htext4 Hsp_f4 Hst16_4 Ha0_f4 Ha1_f4 Ha2_f4
              ltac:(change (2 ^ 31) with 2147483648; lia)
              ltac:(refine (uv_wr_sub pt M4 (hbase + 65360) 176 _ _ Hwr_m
                              _ _ _); lia)
              ltac:(unfold sh_frame_ok; rewrite Hu32; lia)
              ltac:(lia)
              ltac:(rewrite Hu32; right; lia)
              ltac:(rewrite Hra_f4; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CID13 g0 M5) "%Hcss %Ha0_s %Hfill %Honly_s Hcg Hpc".
    rewrite Hu32 in Honly_s.
    iEval (rewrite Hra_f4) in "Hpc".
    assert (Hdom5 : forall k : Z, is_Some (M4 !! k) -> is_Some (M5 !! k))
      by exact (proj1 Honly_s).
    assert (Hout5 : forall k : Z,
              (k < hbase + 65360 \/ hbase + 65528 <= k) ->
              (k < uint sp0 - 48 \/ uint sp0 - 32 <= k) -> M5 !! k = M4 !! k).
    { intros k H1 H2. apply (proj2 Honly_s). intros (w & Hw & Hin).
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_cons in Hw. destruct Hw as [ -> | Hw ]. { cbv [sh_win] in Hin. simpl in Hin. lia. }
      apply elem_of_nil in Hw. exact Hw. }
    assert (Htext5 : sh_text_sub M5).
    { intros k b Hk. pose proof (sh_bytes_key_lt k b Hk) as Hkl.
      rewrite (Hout5 k ltac:(lia) ltac:(lia)). exact (Htext4 k b Hk). }
    assert (Hfrm5 : forall k : Z, uint sp0 - 32 <= k < uint sp0 ->
              M5 !! k = M3 !! k)
      by (intros k Hk; rewrite (Hout5 k ltac:(lia) ltac:(lia));
          exact (Hfrm4 k Hk)).
    assert (Hst5 : uv_stack pt M5 sp0 128)
      by exact (uv_stack_dom pt M4 M5 sp0 128 Hdom5 Hst4).
    assert (Hwr5 : uv_wr pt M5 (hbase + 65360) 176)
      by exact (uv_wr_dom pt M4 M5 _ _ Hdom5 Hwr_m).
    (* ---- 0x1f0  c.li a5,1 ---- *)
    assert (Hli5 : (mword_of_int 1 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12
                          (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh M5 g0 (mword_of_int 0x1f0)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int 1)
              (ui_sh_1f0 pt M5 Hl Htext5)
              ltac:(vm_compute; discriminate) Hli5
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (g1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> g0).
    assert (U1 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              g1 !!! Regidx r = g0 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g0 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (E1f0 : add_vec_int (mword_of_int 0x1f0 : mword 64) 2
                   = mword_of_int 0x1f2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1f0) in "Hpc".
    (* ---- 0x1f2  c.sw a5,0(s1)  -- cmd->type = EXEC ---- *)
    assert (Hcmd4 : (hbase + 65360) mod 4 = 0).
    { destruct (proj1 (Z.mod_divide hbase 4 ltac:(lia)) Hhb4) as (c & Hc).
      apply (proj2 (Z.mod_divide _ 4 ltac:(lia))).
      exists (c + 16340). lia. }
    destruct (uv_slot4_facts (hbase + 65360) (mword_of_int (hbase + 65360))
                ltac:(lia) ltac:(exact Hcmd4)
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Hucmd & Hcncmd & Hpgcmd & Halcmd).
    destruct (heap_leaf (hbase + 65360) Hlay ltac:(lia))
      as (wcmd & Hwcmd & Hwcmdl & Hwcmds).
    assert (Hs1_g1 : g1 !!! Regidx s1_idx
                     = (mword_of_int (hbase + 65360) : mword 64)).
    { rewrite (U1 s1_idx ltac:(vm_compute; discriminate))
              (Hcss s1_idx ltac:(vm_compute; reflexivity)). exact Hs1_f4. }
    assert (Ha5_g1 : g1 !!! Regidx a5_idx = (mword_of_int 1 : mword 64))
      by exact (upd_eq g0 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 1 : mword 64))).
    assert (Hvac : (mword_of_int (hbase + 65360) : mword 64)
                   = add_vec (g1 !!! Regidx s1_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))).
    { rewrite Hs1_g1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
                    : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_csw C pt Psh M5 g1 (mword_of_int 0x1f2)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx
              wcmd (mword_of_int (hbase + 65360)) (mword_of_int 1)
              (ui_sh_1f2 pt M5 Hl Htext5)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hvac (eq_sym Ha5_g1) Hwcmd Hwcmds Hcncmd Hpgcmd Halcmd
              ltac:(rewrite Hucmd; intros j Hj;
                    destruct (uwr_bytes _ _ _ _ Hwr5 (Z.of_nat j) ltac:(lia))
                      as (b & Hb); exists b; exact Hb)
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    iEval (rewrite Hucmd) in "Hcg".
    set (M6 := uM_store M5 (hbase + 65360) 4 (mword_of_int 1 : mword 64)).
    assert (Htext6 : sh_text_sub M6)
      by (unfold M6; apply sh_text_sub_store4; [ exact Htext5 | lia ]).
    assert (Hdom6 : forall k : Z, is_Some (M5 !! k) -> is_Some (M6 !! k))
      by (intros k H; exact (uM_store_is_Some _ _ _ _ k H)).
    assert (Hne6 : forall k : Z,
              (k < hbase + 65360 \/ hbase + 65364 <= k) -> M6 !! k = M5 !! k)
      by (intros k Hk; unfold M6; apply uM_store_lookup_ne; intros j Hj; lia).
    assert (Hst6 : uv_stack pt M6 sp0 128)
      by exact (uv_stack_dom pt M5 M6 sp0 128 Hdom6 Hst5).
    assert (Hst32_6 : uv_stack pt M6 sp0 32)
      by exact (proj1 (uv_stack_split pt M6 sp0 128 32 96 ltac:(lia) ltac:(lia)
                         ltac:(vm_compute; reflexivity) ltac:(lia) Hst6)).
    assert (E1f2 : add_vec_int (mword_of_int 0x1f2 : mword 64) 2
                   = mword_of_int 0x1f4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1f2) in "Hpc".
    (* ---- 0x1f4  c.mv a0,s1 ---- *)
    assert (Hmv2 : (mword_of_int (hbase + 65360) : mword 64)
                   = add_vec zero_reg (g1 !!! Regidx s1_idx))
      by (rewrite Hs1_g1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M6 g1 (mword_of_int 0x1f4)
              a0_idx s1_idx (mword_of_int (hbase + 65360))
              (ui_sh_1f4 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hmv2
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    set (g2 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (hbase + 65360) : mword 64)]> g1).
    assert (U2 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              g2 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (E1f4 : add_vec_int (mword_of_int 0x1f4 : mword 64) 2
                   = mword_of_int 0x1f6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1f4) in "Hpc".
    (* the frame slots, as the epilogue will read them back *)
    assert (Hfrm6 : forall k : Z, uint sp0 - 32 <= k < uint sp0 ->
              M6 !! k = M3 !! k)
      by (intros k Hk; rewrite (Hne6 k ltac:(lia)); exact (Hfrm5 k Hk)).
    assert (Bra6 : uM_bytes M6 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. rewrite (Hfrm6 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
                           (Hne3 (uint sp0 - 8 + Z.of_nat j) ltac:(lia))
                           (Hne2 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (Bs06 : uM_bytes M6 (uint sp0 - 16) 8 (m !!! Regidx s0_idx)).
    { intros j Hj. rewrite (Hfrm6 (uint sp0 - 16 + Z.of_nat j) ltac:(lia))
                           (Hne3 (uint sp0 - 16 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx) j Hj). }
    assert (Bs16 : uM_bytes M6 (uint sp0 - 24) 8 (m !!! Regidx s1_idx)).
    { intros j Hj. rewrite (Hfrm6 (uint sp0 - 24 + Z.of_nat j) ltac:(lia)).
      exact (uM_store8_bytes M2 (uint sp0 - 24) (m !!! Regidx s1_idx) j Hj). }
    assert (Hsp_g2 : g2 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (U2 sp_idx ltac:(vm_compute; discriminate))
              (U1 sp_idx ltac:(vm_compute; discriminate))
              (Hcss sp_idx ltac:(vm_compute; reflexivity)). exact Hsp_f4. }
    (* ---- 0x1f6  c.ldsp ra,24(sp) ---- *)
    iApply (wp_uv_frame_load C pt CID16 Psh M6 g2 sp0 (mword_of_int 0x1f6)
              (mword_of_int 3 : mword 6) ra_idx 32 24 (m !!! Regidx ra_idx)
              (ui_sh_1f6 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hst32_6
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_g2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Ea24; symmetry;
                    exact (uM_word_w8 M6 (uint sp0 - 8) _ Bra6))
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    set (g3 := <[Regidx ra_idx
                 := regval_into_reg (m !!! Regidx ra_idx)]> g2).
    assert (U3 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              g3 !!! Regidx r = g2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g2 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (E1f6 : add_vec_int (mword_of_int 0x1f6 : mword 64) 2
                   = mword_of_int 0x1f8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1f6) in "Hpc".
    (* ---- 0x1f8  c.ldsp s0,16(sp) ---- *)
    assert (Hsp_g3 : g3 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 32) : mword 64))
      by (rewrite (U3 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_g2).
    iApply (wp_uv_frame_load C pt CID17 Psh M6 g3 sp0 (mword_of_int 0x1f8)
              (mword_of_int 2 : mword 6) s0_idx 32 16 (m !!! Regidx s0_idx)
              (ui_sh_1f8 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hst32_6
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_g3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Ea16; symmetry;
                    exact (uM_word_w8 M6 (uint sp0 - 16) _ Bs06))
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    set (g4 := <[Regidx s0_idx
                 := regval_into_reg (m !!! Regidx s0_idx)]> g3).
    assert (U4 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              g4 !!! Regidx r = g3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g3 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (E1f8 : add_vec_int (mword_of_int 0x1f8 : mword 64) 2
                   = mword_of_int 0x1fa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1f8) in "Hpc".
    (* ---- 0x1fa  c.ldsp s1,8(sp) ---- *)
    assert (Hsp_g4 : g4 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 32) : mword 64))
      by (rewrite (U4 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_g3).
    iApply (wp_uv_frame_load C pt CID18 Psh M6 g4 sp0 (mword_of_int 0x1fa)
              (mword_of_int 1 : mword 6) s1_idx 32 8 (m !!! Regidx s1_idx)
              (ui_sh_1fa pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hst32_6
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp_g4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Ea08; symmetry;
                    exact (uM_word_w8 M6 (uint sp0 - 24) _ Bs16))
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    set (g5 := <[Regidx s1_idx
                 := regval_into_reg (m !!! Regidx s1_idx)]> g4).
    assert (U5 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              g5 !!! Regidx r = g4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g4 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (E1fa : add_vec_int (mword_of_int 0x1fa : mword 64) 2
                   = mword_of_int 0x1fc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1fa) in "Hpc".
    (* ---- 0x1fc  c.addi16sp sp,sp,32 ---- *)
    assert (Hsp_g5 : g5 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 32) : mword 64))
      by (rewrite (U5 sp_idx ltac:(vm_compute; discriminate)); exact Hsp_g4).
    assert (Hwsp2 : sp0 = add_vec (g5 !!! Regidx csp_rs1)
                           (sign_extend' 64
                              (caddi16sp_imm (mword_of_int 2 : mword 6)))).
    { rewrite Hsp_g5.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 32 + 32) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh M6 g5 (mword_of_int 0x1fc)
              (mword_of_int 2 : mword 6) sp0
              (ui_sh_1fc pt M6 Hl Htext6) Hwsp2
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    set (g6 := <[Regidx csp_rs1 := regval_into_reg sp0]> g5).
    assert (U6 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              g6 !!! Regidx r = g5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g5 (Regidx sp_idx) (Regidx r) _ Hr)).
    assert (E1fc : add_vec_int (mword_of_int 0x1fc : mword 64) 2
                   = mword_of_int 0x1fe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1fc) in "Hpc".
    (* ---- 0x1fe  c.jr ra ---- *)
    assert (Hra_g6 : g6 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (U6 ra_idx ltac:(vm_compute; discriminate))
              (U5 ra_idx ltac:(vm_compute; discriminate))
              (U4 ra_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g2 (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    assert (Htgtr : (m !!! Regidx ra_idx) = ret_pc (g6 !!! Regidx ra_idx)).
    { rewrite Hra_g6. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M6 g6 (mword_of_int 0x1fe)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_1fe pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Htgtr
              with "Hcg Hpc").
    iIntros (CID21) "Hcg Hpc".
    (* ---- the postcondition ---- *)
    assert (Hcs : ucallee_saved m g6).
    { intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [ Esp | Nsp ].
      { rewrite Esp (upd_eq g5 (Regidx csp_rs1) (regval_into_reg sp0)).
        symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [ Es0 | Ns0 ].
      { rewrite Es0 (U6 s0_idx ltac:(vm_compute; discriminate))
                    (U5 s0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq g3 (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ Es1 | Ns1 ].
      { rewrite Es1 (U6 s1_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq g4 (Regidx s1_idx)
                 (regval_into_reg (m !!! Regidx s1_idx))). }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (U6 r Nsp) (U5 r Ns1) (U4 r Ns0) (U3 r Nra) (U2 r Na0) (U1 r Na5)
              (Hcss r Hr) (Z4 r Nra) (Z3 r Na1) (Z2 r Na2) (Z1 r Ns1)
              (Hcsm r Hr) (Y4 r Nra) (Y3 r Na0) (Y2 r Ns0) (Y1 r Nsp).
      reflexivity. }
    assert (Ha0_g6 : g6 !!! Regidx a0_idx
                     = (mword_of_int (hbase + 65360) : mword 64)).
    { rewrite (U6 a0_idx ltac:(vm_compute; discriminate))
              (U5 a0_idx ltac:(vm_compute; discriminate))
              (U4 a0_idx ltac:(vm_compute; discriminate))
              (U3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g1 (Regidx a0_idx)
               (regval_into_reg
                  (mword_of_int (hbase + 65360) : mword 64))). }
    assert (Honly_ex : uM_only_in M M6
              [sh_win hbase 65536; sh_win 8208 8; sh_win 8328 16;
               sh_win (hbase + 65360) SH_EXECCMD_SZ;
               sh_win (uint sp0 - 128) 128]).
    { refine (uM_only_in_trans M M3 M6 _ _ _).
      - split; [ exact Hdom3 | ].
        intros k Hk.
        pose proof (not_in_window _ (uint sp0 - 128) 128 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_further;
                            apply elem_of_list_here) Hk) as W5.
        rewrite (Hne3 k ltac:(lia)) (Hne2 k ltac:(lia)).
        exact (Hne1 k ltac:(lia)).
      - refine (uM_only_in_trans M3 M4 M6 _ _ _).
        + split; [ exact (proj1 Honly_m) | ].
          intros k Hk.
          pose proof (not_in_window _ hbase 65536 k
                        ltac:(apply elem_of_list_here) Hk) as W1.
          pose proof (not_in_window _ 8208 8 k
                        ltac:(apply elem_of_list_further; apply elem_of_list_here)
                        Hk) as W2.
          pose proof (not_in_window _ 8328 16 k
                        ltac:(apply elem_of_list_further;
                              apply elem_of_list_further;
                              apply elem_of_list_here) Hk) as W3.
          pose proof (not_in_window _ (uint sp0 - 128) 128 k
                        ltac:(apply elem_of_list_further;
                              apply elem_of_list_further;
                              apply elem_of_list_further;
                              apply elem_of_list_further;
                              apply elem_of_list_here) Hk) as W5.
          exact (Hout4 k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        + refine (uM_only_in_trans M4 M5 M6 _ _ _).
          * split; [ exact Hdom5 | ].
            intros k Hk.
            pose proof (not_in_window _ (hbase + 65360) SH_EXECCMD_SZ k
                          ltac:(apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_here) Hk) as W4.
            pose proof (not_in_window _ (uint sp0 - 128) 128 k
                          ltac:(apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_here) Hk) as W5.
            unfold SH_EXECCMD_SZ in W4.
            exact (Hout5 k ltac:(lia) ltac:(lia)).
          * split; [ exact Hdom6 | ].
            intros k Hk.
            pose proof (not_in_window _ (hbase + 65360) SH_EXECCMD_SZ k
                          ltac:(apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_further;
                                apply elem_of_list_here) Hk) as W4.
            unfold SH_EXECCMD_SZ in W4.
            exact (Hne6 k ltac:(lia)). }
    iApply ("Hcont" $! CID21 g6 M6 (hbase + 65360)
              with "[] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0_g6.
    - iPureIntro. unfold SH_EXECCMD_SZ. rewrite Hnu12. lia.
    - iPureIntro. apply uM_bytes_4_of_4. intros j Hj.
      exact (uM_store_bytes M5 (hbase + 65360) 4 (mword_of_int 1 : mword 64) j
               ltac:(change (Z.to_nat 4) with 4%nat; lia)).
    - iPureIntro. intros j Hj. unfold SH_EXECCMD_SZ in Hj.
      rewrite (Hne6 (hbase + 65360 + j) ltac:(lia)). exact (Hfill j ltac:(lia)).
    - iPureIntro. unfold SH_EXECCMD_SZ.
      refine (uv_wr_sub pt M6 (hbase + 65360) 176 _ _
                (uv_wr_dom pt M5 M6 _ _ Hdom6 Hwr5) _ _ _); lia.
    - iPureIntro. exact Honly_ex.
  Qed.

End UProofShHeap.

(* sentinel: malloc and execcmd rest on nothing but the platform axioms and
   functional extensionality -- and, as the header's drift note D1 records,
   -- no section hypothesis: [free], [sbrk] and [memset] are called
   through their real contracts. *)
Print Assumptions wp_sh_malloc_first.
Print Assumptions wp_sh_execcmd.
