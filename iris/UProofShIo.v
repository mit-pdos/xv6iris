(* UProofShIo.v -- the VERIFIED-EXECUTION proofs of the `sh` program's INPUT
   PATH (claude-notes/projects/user-sh.md):

     wp_sh_gets    gets   @0xaaa  96-byte frame, ra + s0..s8 spilled
     wp_sh_getcmd  getcmd @0x0    32-byte frame, three calls

   Both discharge USpecSh.v's contracts AS THEY STAND -- no extra premise,
   no restated body.

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v, fed the matching
   [ui_sh_<hexpc>] fact from UCodeSh.v.  gets' frame is 96 bytes and
   getcmd's is 32, so UmodeFrame.v's 16-byte [wp_uv_prologue16] /
   [wp_uv_epilogue16] do not apply; the frames are built ONE SLOT at a time
   out of [wp_sh_spill] / [wp_sh_reload] (§2), which take the frame size,
   the slot offset, the register and the protocol as parameters.  That is
   deliberately not a [wp_uv_prologue32/_64/_96] family: what varies with
   the frame size is not only the size -- getcmd spills ra,s0,s1,s2 and
   gets spills ra,s0..s8, and the parser's wider frames spill different
   sets again -- so a per-size lemma would have to fix the register LIST
   too, and that is the cross-product this tier refuses.

   OWED, at the next resync: §1 and §2 are LOCAL copies of apparatus that
   now exists upstream, and should be retired in its favour --
   [wp_sh_spill] / [wp_sh_reload] for [UmodeFrame.wp_uv_frame_store] /
   [wp_uv_frame_load], and [stack_leaf] / [stack_wr] for
   [UmodeAbi.uv_stack_slotk_moi] / [uv_stack_byte_moi] (check first that
   the latter reach the one-byte read slot at sp0-81, which is neither
   8-aligned nor the budget's base -- that is the whole reason §1 exists).
   Likewise [gets]' [blez a0] / [beqz] / [bnez] should become
   [WpUmodeBranch.wp_uv_btype0], which reads x0 off [gpr_file] rather than
   making each call site do it by hand.

   TWO SHAPES THIS FILE EXISTS TO GET RIGHT, both about a function that
   reads or writes memory OUTSIDE its own frame:

   - gets' image effect is [ustr_at] (the content) PLUS [uM_only_in] over
     the buffer AND its own 96-byte frame.  A bare [uM_written] would be
     FALSE, not weak: the prologue spills ra and s0..s8 and [read] writes
     the one-byte slot at sp0-81, and the epilogue only RELOADS them.
     Inside the loop the same fact is carried by [sh_io_win], which is
     [uM_written] with ONE extra excluded point -- exactly what a function
     that reads into its own frame needs.
   - getcmd READS buf[0] (`lbu a0,0(s1)' at 0x32, the EOF test), so it
     needs a LOAD leaf at [buf]; [uv_wr]'s leaf is store-only, which is why
     the contract carries [uv_rd] as well as [uv_wr].  [stack_wr] is the same gap on the stack side: [uv_stack] states its
     leaf only at the budget's BASE, and gets' read slot at sp0-81 is
     neither the base nor 8-aligned.

   The [i + 1 < max] exit of gets' loop is NOT reachable under [Hfit]
   ([|taken| + 1 < max]); it is discharged as a contradiction, and so is
   the '\r' exit at 0xafc, from [sh_gets_taken]. *)
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
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UCodeSh USpecSh UProofShLib UProofShMem.
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
(* ===================================================================== *)

Local Lemma sh_text_sub_store8' (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma sh_data_sub_store8' (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_data_sub M -> 12288 <= a -> sh_data_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_data_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma um8_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (k < a \/ a + 8 <= k) -> uM_store8 M a v !! k = M !! k.
Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

Local Lemma um1_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  k <> a -> uM_store M a 1 v !! k = M !! k.
Proof. intro H. apply uM_store_lookup_ne. intros j Hj. change (Z.to_nat 1) with 1%nat in Hj. lia. Qed.

Local Lemma only_step8 (M Mk : gmap Z (bv 8)) (lo a n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n ->
  uM_only M Mk lo n -> uM_only M (uM_store8 Mk a v) lo n.
Proof.
  intros H1 H2 (Hd & Ho). split.
  - intros k Hk. apply uM_store8_is_Some. exact (Hd k Hk).
  - intros k Hk. rewrite (um8_ne Mk a v k ltac:(lia)). exact (Ho k Hk).
Qed.

Local Lemma bytes_win (Mx My : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  (forall k : Z, a <= k < a + 8 -> My !! k = Mx !! k) ->
  uM_bytes Mx a 8 v -> uM_bytes My a 8 v.
Proof.
  intros Hk Hb j Hj. rewrite (Hk (a + Z.of_nat j) ltac:(lia)). exact (Hb j Hj).
Qed.

(* an 8-byte window survives a DISJOINT 8-byte store *)
Local Lemma store8_bytes_ne (M : gmap Z (bv 8)) (a b : Z) (v w : mword 64) :
  (b + 8 <= a \/ a + 8 <= b) -> uM_bytes M a 8 v -> uM_bytes (uM_store8 M b w) a 8 v.
Proof.
  intros Hd Hby j Hj.
  rewrite (um8_ne M b w (a + Z.of_nat j) ltac:(lia)). exact (Hby j Hj).
Qed.

Local Lemma bv8_rng (b : bv 8) : 0 <= bv_unsigned b < 256.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (E8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E8 in Hr. exact Hr.
Qed.

Local Lemma bv8_eq0 (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

(* the byte a [sb] of a normalized byte value writes *)
Local Lemma nth_byte0_moi' (c : bv 8) :
  nth_byte (mword_of_int (bv_unsigned c) : mword 64) 0 = c.
Proof.
  apply bv_eq. rewrite nth_byte_unsigned.
  pose proof (bv8_rng c) as Hr.
  rewrite moi_unsigned.
  rewrite (Z.mod_small (bv_unsigned c) Z64 ltac:(unfold Z64; lia)).
  change (Z.of_N (8 * N.of_nat 0)) with 0.
  rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256.
  apply Z.mod_small. lia.
Qed.

Local Lemma nth_byte0_zero : nth_byte (zero_reg : mword 64) 0 = ubyte0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [x - d = 0] as the machine decides it, on two BYTE-sized operands *)
Local Lemma moi_eq_zero_sub (x d : Z) :
  0 <= x < 256 -> 0 <= d < 256 ->
  eq_vec (mword_of_int (x - d) : mword 64) zero_reg = Z.eqb x d.
Proof.
  intros Hx Hd.
  destruct (Z.le_gt_cases d x) as [ Hge | Hlt ].
  - rewrite (moi_eq_zero (x - d) ltac:(unfold Z64; lia)).
    destruct (Z.eqb_spec (x - d) 0) as [ H0 | Hn0 ];
      [ symmetry; apply Z.eqb_eq; lia | symmetry; apply Z.eqb_neq; lia ].
  - rewrite (moi_mod (x - d) (x - d + Z64)
               ltac:(assert (E : x - d + Z64 = x - d + 1 * Z64) by lia;
                     rewrite E; symmetry; apply Z_mod_plus_full)).
    rewrite (moi_eq_zero (x - d + Z64) ltac:(unfold Z64; lia)).
    destruct (Z.eqb_spec (x - d + Z64) 0) as [ H0 | Hn0 ];
      [ exfalso; unfold Z64 in H0; lia | symmetry; apply Z.eqb_neq; lia ].
Qed.

Local Lemma moi_neq_zero_sub (x d : Z) :
  0 <= x < 256 -> 0 <= d < 256 ->
  neq_vec (mword_of_int (x - d) : mword 64) zero_reg = negb (Z.eqb x d).
Proof.
  intros Hx Hd. unfold neq_vec. rewrite (moi_eq_zero_sub x d Hx Hd). reflexivity.
Qed.

(* ---- windows ------------------------------------------------------- *)

Local Lemma in_win2 (a1 n1 a2 n2 k : Z) :
  (a1 <= k < a1 + n1) \/ (a2 <= k < a2 + n2) -> uM_in_windows [(a1,n1);(a2,n2)] k.
Proof.
  intros [ H | H ].
  - exists (a1, n1). split; [ apply elem_of_list_here | simpl; lia ].
  - exists (a2, n2). split;
      [ apply elem_of_list_further; apply elem_of_list_here | simpl; lia ].
Qed.

Local Lemma in_win2_inv (a1 n1 a2 n2 k : Z) :
  uM_in_windows [(a1,n1);(a2,n2)] k ->
  (a1 <= k < a1 + n1) \/ (a2 <= k < a2 + n2).
Proof.
  intros ((a,n) & Hin & Hk). simpl in Hk.
  apply elem_of_cons in Hin as [ He | Hin ].
  { injection He as -> ->. left; exact Hk. }
  apply elem_of_cons in Hin as [ He | Hin ].
  { injection He as -> ->. right; exact Hk. }
  exfalso. exact (not_elem_of_nil _ Hin).
Qed.

(* ---- gets' image invariant ------------------------------------------
   [pre] written at [buf], the ONE-BYTE read slot at [rb] disturbed, and
   nothing else.  This is [uM_written] with one extra excluded point --
   which is what a function that reads into its OWN frame needs, and what
   a bare [uM_written] cannot express. *)
Definition sh_io_win (MB Mi : gmap Z (bv 8)) (buf rb : Z)
    (pre : list (bv 8)) : Prop :=
  (forall (j : nat) (b : bv 8), pre !! j = Some b ->
     Mi !! (buf + Z.of_nat j) = Some b) /\
  (forall k : Z, (k < buf \/ buf + Z.of_nat (length pre) <= k) -> k <> rb ->
     Mi !! k = MB !! k) /\
  (forall k : Z, is_Some (MB !! k) -> is_Some (Mi !! k)).

Local Lemma sh_io_win_refl (MB : gmap Z (bv 8)) (buf rb : Z) :
  sh_io_win MB MB buf rb [].
Proof.
  split_and!.
  - intros j b Hj. destruct j; cbn in Hj; discriminate.
  - intros k _ _. reflexivity.
  - intros k Hk. exact Hk.
Qed.

Local Lemma sh_io_win_rd (MB Mi Mi' : gmap Z (bv 8)) (buf rb n : Z)
    (pre bs : list (bv 8)) :
  (rb < buf \/ buf + n <= rb) -> Z.of_nat (length pre) <= n ->
  (length bs <= 1)%nat ->
  uM_written Mi Mi' rb bs ->
  sh_io_win MB Mi buf rb pre ->
  sh_io_win MB Mi' buf rb pre.
Proof.
  intros Hrb Hpre Hbs (Hw & Hoff & Hdm) (Hin & Hout & Hdom).
  split_and!.
  - intros j b Hj.
    pose proof (lookup_lt_Some pre j b Hj) as Hjl.
    rewrite (Hoff (buf + Z.of_nat j) ltac:(lia)). exact (Hin j b Hj).
  - intros k Hk Hkne. rewrite (Hoff k ltac:(lia)). exact (Hout k Hk Hkne).
  - intros k Hk. exact (Hdm k (Hdom k Hk)).
Qed.

Local Lemma sh_io_win_sb (MB Mi : gmap Z (bv 8)) (buf rb : Z)
    (pre : list (bv 8)) (c : bv 8) (v : mword 64) :
  nth_byte v 0 = c ->
  sh_io_win MB Mi buf rb pre ->
  sh_io_win MB (uM_store Mi (buf + Z.of_nat (length pre)) 1 v)
    buf rb (pre ++ [c]).
Proof.
  intros Hv (Hin & Hout & Hdom).
  assert (Hhit : uM_store Mi (buf + Z.of_nat (length pre)) 1 v
                   !! (buf + Z.of_nat (length pre)) = Some c).
  { pose proof (uM_store_lookup Mi (buf + Z.of_nat (length pre)) 1 v 0%nat
                  ltac:(change (Z.to_nat 1) with 1%nat; lia)) as H0.
    replace (buf + Z.of_nat (length pre) + Z.of_nat 0)
      with (buf + Z.of_nat (length pre)) in H0 by lia.
    rewrite H0 Hv. reflexivity. }
  split_and!.
  - intros j b Hj.
    destruct (decide (j < length pre)%nat) as [ Hlt | Hge ].
    + rewrite (lookup_app_l pre [c] j Hlt) in Hj.
      rewrite (um1_ne Mi (buf + Z.of_nat (length pre)) v (buf + Z.of_nat j)
                 ltac:(lia)).
      exact (Hin j b Hj).
    + pose proof (lookup_lt_Some _ j b Hj) as Hjl.
      rewrite length_app in Hjl. cbn [length] in Hjl.
      assert (Hje : j = length pre) by lia. subst j.
      rewrite (lookup_app_r pre [c] (length pre) ltac:(lia)) in Hj.
      rewrite Nat.sub_diag in Hj. cbn in Hj. injection Hj as <-.
      exact Hhit.
  - intros k Hk Hkne.
    rewrite length_app in Hk. cbn [length] in Hk.
    rewrite (um1_ne Mi (buf + Z.of_nat (length pre)) v k ltac:(lia)).
    exact (Hout k ltac:(lia) Hkne).
  - intros k Hk. apply uM_store_is_Some. exact (Hdom k Hk).
Qed.

Local Lemma sh_io_win_text (MB Mi : gmap Z (bv 8)) (buf rb : Z)
    (pre : list (bv 8)) :
  8192 <= buf -> 8192 <= rb ->
  sh_io_win MB Mi buf rb pre -> sh_text_sub MB -> sh_text_sub Mi.
Proof.
  intros Hb Hr (Hin & Hout & Hdom) Ht k b Hk.
  pose proof (sh_bytes_key_lt k b Hk) as Hlt.
  rewrite (Hout k ltac:(lia) ltac:(lia)). exact (Ht k b Hk).
Qed.

Local Lemma nl_val : bv_unsigned ubyte_nl = 10.
Proof. vm_compute. reflexivity. Qed.
Local Lemma cr_val : bv_unsigned ubyte_cr = 13.
Proof. vm_compute. reflexivity. Qed.
Local Lemma bv8_is_nl (b : bv 8) : bv_unsigned b = 10 <-> b = ubyte_nl.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H nl_val. reflexivity.
  - intro H. subst b. exact nl_val.
Qed.
Local Lemma bv8_is_cr (b : bv 8) : bv_unsigned b = 13 <-> b = ubyte_cr.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H cr_val. reflexivity.
  - intro H. subst b. exact cr_val.
Qed.

(* the text survives a call whose two disturbed windows are both above the
   program image *)
Local Lemma only_in2_text (M M' : gmap Z (bv 8)) (a1 n1 a2 n2 : Z) :
  8192 <= a1 -> 8192 <= a2 ->
  uM_only_in M M' [(a1,n1);(a2,n2)] -> sh_text_sub M -> sh_text_sub M'.
Proof.
  intros H1 H2 (Hd & Ho) Ht k b Hk.
  pose proof (sh_bytes_key_lt k b Hk) as Hlt.
  rewrite (Ho k ltac:(intro Hc;
                      destruct (in_win2_inv a1 n1 a2 n2 k Hc) as [ Hw | Hw ];
                      lia)).
  exact (Ht k b Hk).
Qed.

Section UProofShIo.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).
  (* [UVG] is deliberately not abbreviated: every occurrence names its hart. *)

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation x0_idx := (mword_of_int 0 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §1 A STACK BUDGET IS A WRITABLE (AND READABLE) WINDOW.                *)
  (*                                                                       *)
  (* [uv_stack]'s own leaf is stated at ONE address -- the bottom of the    *)
  (* budget -- and [us_page] says the whole budget is on that page, so      *)
  (* every byte of it has the same leaf.  gets needs this because its       *)
  (* one-byte [read] slot sits at sp0-81, which is neither 8-aligned nor    *)
  (* the budget's base.                                                     *)
  (* ------------------------------------------------------------------- *)
  Lemma stack_leaf (M : gmap Z (bv 8)) (sp0 : mword 64) (n a : Z) :
    uv_stack pt M sp0 n -> uint sp0 - n <= a < uint sp0 ->
    exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
      uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w.
  Proof.
    intros HS Ha.
    pose proof (us_lo _ _ _ _ HS) as Hlo.
    pose proof (us_page _ _ _ _ HS) as Hpg.
    pose proof (us_canon _ _ _ _ HS) as Hc.
    pose proof (us_n0 _ _ _ _ HS) as Hn0.
    change (2 ^ 38) with 274877906944 in Hc.
    rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
    destruct (us_leaf _ _ _ _ HS ltac:(lia)) as (w & Hw & Hst & Hld).
    rewrite (uv_stack_sp_moi pt M sp0 n HS) in Hw.
    pose proof (Z.div_mod (uint sp0 - n) 4096 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (uint sp0 - n) 4096 ltac:(lia)) as Hmb.
    assert (Hq : a / 4096 = (uint sp0 - n) / 4096).
    { symmetry.
      apply (Zdiv_unique a 4096 ((uint sp0 - n) / 4096)
               ((uint sp0 - n) mod 4096 + (a - (uint sp0 - n)))); lia. }
    exists w.
    rewrite (sh_svpn_page a ltac:(lia)).
    rewrite (sh_svpn_page (uint sp0 - n) ltac:(lia)) in Hw.
    rewrite Hq. split_and!; assumption.
  Qed.

  Lemma stack_wr (M : gmap Z (bv 8)) (sp0 : mword 64) (n a k : Z) :
    uv_stack pt M sp0 n -> uint sp0 - n <= a -> 0 <= k -> a + k <= uint sp0 ->
    uv_wr pt M a k.
  Proof.
    intros HS Ha Hk Hak.
    pose proof (us_lo _ _ _ _ HS) as Hlo.
    pose proof (us_canon _ _ _ _ HS) as Hc.
    pose proof (us_bytes _ _ _ _ HS) as Hb.
    change (2 ^ 38) with 274877906944 in Hc.
    constructor.
    - lia.
    - lia.
    - change (2 ^ 38) with 274877906944. lia.
    - intros j Hj.
      destruct (stack_leaf M sp0 n (a + j) HS ltac:(lia)) as (w & Hw & Hst & _).
      exists w. split; assumption.
    - intros j Hj.
      destruct (Hb (a + j - (uint sp0 - n)) ltac:(lia)) as (b & Hbb).
      exists b. replace (a + j) with (uint sp0 - n + (a + j - (uint sp0 - n))) by lia.
      exact Hbb.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 ONE frame slot, spilled and reloaded.  Frame-size generic, so the  *)
  (* same two lemmas serve gets' 96-byte frame and getcmd's 32-byte one.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_spill (CIDp : CpuId) (Ps : usys_protocol Σ)
      (pcz pcn fr d : Z) (uimm : mword 6)
      (rs2 : mword 5) (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    uv_stack pt M sp0 fr ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - fr) : mword 64) ->
    0 <= d -> d + 8 <= fr -> Z.rem d 8 = 0 ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    uinstr pt M (mword_of_int pcz) true (C_SDSP (uimm, Regidx rs2)) ->
    add_vec_int (mword_of_int pcz : mword 64) 2 = mword_of_int pcn ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) (mword_of_int pcz) -∗
    (∀ CID : CpuId,
       uv_cap_gpr (CID := CID) C pt Ps
         (uM_store8 M (uint sp0 - fr + d) (m !!! Regidx rs2)) m -∗
       pc_is (CID := CID) (mword_of_int pcn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HS Hsp Hd0 Hdn Hd8 Himm Hui Etick.
    destruct (uv_stack_slot_moi pt M sp0 fr d
                (mword_of_int (uint sp0 - fr + d)) HS Hd0 Hdn Hd8 eq_refl)
      as (Hq & (w & Hl & Hoks & _) & Hcanon & Hpg & Hal & Hb).
    iIntros "Hcg Hpc Hcont".
    assert (Htg : (mword_of_int (uint sp0 - fr + d) : mword 64)
                  = add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Hsp Himm moi_add. f_equal; lia. }
    iApply (wp_uv_csdsp C pt Ps M m (mword_of_int pcz) uimm rs2
              w (mword_of_int (uint sp0 - fr + d)) (m !!! Regidx rs2)
              Hui Htg eq_refl Hl Hoks Hcanon Hpg Hal Hb
              with "Hcg Hpc").
    iIntros (CID) "Hcg Hpc".
    iEval (rewrite Hq) in "Hcg".
    iEval (rewrite Etick) in "Hpc".
    iApply ("Hcont" $! CID with "Hcg Hpc").
  Qed.

  Lemma wp_sh_reload (CIDp : CpuId) (Ps : usys_protocol Σ)
      (pcz pcn fr d : Z) (uimm : mword 6)
      (rd : mword 5) (v : mword 64)
      (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    uv_stack pt M sp0 fr ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - fr) : mword 64) ->
    0 <= d -> d + 8 <= fr -> Z.rem d 8 = 0 ->
    uint rd <> 0 ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    uM_bytes M (uint sp0 - fr + d) 8 v ->
    uinstr pt M (mword_of_int pcz) true (C_LDSP (uimm, Regidx rd)) ->
    add_vec_int (mword_of_int pcz : mword 64) 2 = mword_of_int pcn ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) (mword_of_int pcz) -∗
    (∀ CID : CpuId,
       uv_cap_gpr (CID := CID) C pt Ps M
         (<[Regidx rd := regval_into_reg v]> m) -∗
       pc_is (CID := CID) (mword_of_int pcn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HS Hsp Hd0 Hdn Hd8 Hrd Himm Hby Hui Etick.
    destruct (uv_stack_slot_moi pt M sp0 fr d
                (mword_of_int (uint sp0 - fr + d)) HS Hd0 Hdn Hd8 eq_refl)
      as (Hq & (w & Hl & _ & Hokl) & Hcanon & Hpg & Hal & Hb).
    iIntros "Hcg Hpc Hcont".
    assert (Htg : (mword_of_int (uint sp0 - fr + d) : mword 64)
                  = add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Hsp Himm moi_add. f_equal; lia. }
    assert (Hwv : v = uM_word M (uint (mword_of_int (uint sp0 - fr + d) : mword 64)) 8).
    { rewrite Hq. symmetry. exact (uM_word_w8 M (uint sp0 - fr + d) v Hby). }
    iApply (wp_uv_cldsp C pt Ps M m (mword_of_int pcz) uimm rd
              w (mword_of_int (uint sp0 - fr + d)) v
              Hui Hrd Htg Hl Hokl Hcanon Hpg Hal Hb Hwv
              with "Hcg Hpc").
    iIntros (CID) "Hcg Hpc".
    iEval (rewrite Etick) in "Hpc".
    iApply ("Hcont" $! CID with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 gets' READ LOOP, head 0xad0, back edge 0xafc.                      *)
  (*                                                                       *)
  (*   ad0  mv s8,s1       ad2  addiw s3,s1,1   ad6  mv s1,s3              *)
  (*   ad8  bge s3,s4,b00      -- the `i+1 < max' exit: NOT reachable      *)
  (*   adc  mv a2,s5       ade  mv a1,s6       ae0  li a0,0                *)
  (*   ae2  jal read       ae6  blez a0,b00    -- the EOF exit             *)
  (*   aea  lbu a5,-81(s0) aee  sb a5,0(s2)    af2  addi s2,s2,1           *)
  (*   af4  addi a4,a5,-10 af8  beqz a4,afe    -- the '\n' exit            *)
  (*   afa  addi a5,a5,-13 afc  bnez a5,ad0    -- the '\r' exit (dead)     *)
  (*   afe  mv s8,s3                                                       *)
  (*                                                                       *)
  (* Ordinary Rocq induction on the STRICT nat measure [|taken| - i], as    *)
  (* in [wp_sh_strchr_loop]: the branch leaf is later-free, so a bounded    *)
  (* loop pays no [>].  [MB] is the image the prologue left.                *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_gets_loop (nn : nat) :
    forall (CIDp : CpuId) (MB Mi : gmap Z (bv 8)) (mE : regfile)
      (sp0 : mword 64) (buf max : Z) (taken rest : list (bv 8)) (i : nat),
      (length taken - i < nn)%nat ->
      sh_layout pt hbase hlen ->
      sh_text_sub MB ->
      uv_stack pt MB sp0 96 ->
      8192 <= uint sp0 - 96 ->
      8192 <= buf ->
      uv_wr pt MB buf max ->
      (buf + max <= uint sp0 - 96 \/ uint sp0 <= buf) ->
      sh_gets_taken taken rest ->
      Z.of_nat (length taken) + 1 < max -> max < 2 ^ 31 ->
      ((i < length taken)%nat \/ (taken = [] /\ i = 0%nat)) ->
      sh_io_win MB Mi buf (uint sp0 - 81) (take i taken) ->
      mE !!! Regidx sp_idx = (mword_of_int (uint sp0 - 96) : mword 64) ->
      mE !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64) ->
      mE !!! Regidx s1_idx = (mword_of_int (Z.of_nat i) : mword 64) ->
      mE !!! Regidx s2_idx = (mword_of_int (buf + Z.of_nat i) : mword 64) ->
      mE !!! Regidx s4_idx = (mword_of_int max : mword 64) ->
      mE !!! Regidx s5_idx = (mword_of_int 1 : mword 64) ->
      mE !!! Regidx s6_idx = (mword_of_int (uint sp0 - 81) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh Mi mE -∗
      ustdin gin (drop i taken ++ rest) -∗
      pc_is (CID := CIDp) (mword_of_int 0xad0) -∗
      (∀ (CID : CpuId) (m' : regfile) (M' : gmap Z (bv 8)),
         ⌜sh_io_win MB M' buf (uint sp0 - 81) taken⌝ -∗
         ⌜m' !!! Regidx s8_idx
            = (mword_of_int (Z.of_nat (length taken)) : mword 64)⌝ -∗
         ⌜forall r : mword 5, ucallee_saved_idx r = true ->
            Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
            Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s8_idx ->
            m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         ustdin gin rest -∗
         uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
         pc_is (CID := CID) (mword_of_int 0xb00) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp MB Mi mE sp0 buf max taken rest i
             Hmeas Hlay Htext HstB Hsphi Hbuflo HwrB Hdisj Htk Hfit Hmax31
             Hi Hwin Hsp Hs0 Hs1 Hs2 Hs4 Hs5 Hs6.
    { exfalso. lia. }
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (us_lo _ _ _ _ HstB) as Hlo96.
    pose proof (us_canon _ _ _ _ HstB) as Hcan96.
    change (2 ^ 38) with 274877906944 in Hcan96.
    change (2 ^ 31) with 2147483648 in Hmax31.
    pose proof (uwr_lo _ _ _ _ HwrB) as Hbuf0.
    pose proof (uwr_hi _ _ _ _ HwrB) as Hbufhi.
    pose proof (uwr_n0 _ _ _ _ HwrB) as Hmax0.
    change (2 ^ 38) with 274877906944 in Hbufhi.
    assert (Hrb8 : 8192 <= uint sp0 - 81) by lia.
    assert (Hile : (i <= length taken)%nat)
      by (destruct Hi as [ H | (_ & ->) ]; lia).
    assert (Hroom : Z.of_nat i + 1 < max).
    { destruct Hi as [ Hlt | (He & Hi0) ]; [ lia | ].
      rewrite He in Hfit. cbn [length] in Hfit. lia. }
    assert (Hrbdisj : uint sp0 - 81 < buf \/ buf + max <= uint sp0 - 81)
      by (destruct Hdisj; [ right | left ]; lia).
    assert (Htakelen : Z.of_nat (length (take i taken)) <= max)
      by (rewrite length_take; lia).
    pose proof Hwin as (HwI & HwO & HwD).
    assert (HtextI : sh_text_sub Mi)
      by exact (sh_io_win_text MB Mi buf (uint sp0 - 81) (take i taken)
                  Hbuflo Hrb8 Hwin Htext).
    assert (HstI : uv_stack pt Mi sp0 96)
      by exact (uv_stack_dom pt MB Mi sp0 96 HwD HstB).
    assert (HwrI : uv_wr pt Mi buf max)
      by exact (uv_wr_dom pt MB Mi buf max HwD HwrB).
    destruct sh_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&
                              Hsread & _).
    iIntros "Hcg Hin Hpc Hcont".
    (* ---- 0xad0  c.mv s8,s1 ---- *)
    assert (Hmv0 : (mword_of_int (Z.of_nat i) : mword 64)
                   = add_vec zero_reg (mE !!! Regidx s1_idx))
      by (rewrite Hs1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi mE (mword_of_int 0xad0)
              s8_idx s1_idx (mword_of_int (Z.of_nat i))
              (ui_sh_ad0 pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Hmv0
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mA := <[Regidx s8_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i) : mword 64)]> mE).
    assert (Ead0 : add_vec_int (mword_of_int 0xad0 : mword 64) 2 = mword_of_int 0xad2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ead0) in "Hpc".
    assert (HAs1 : mA !!! Regidx s1_idx = (mword_of_int (Z.of_nat i) : mword 64)).
    { exact (eq_trans (upd_ne mE (Regidx s8_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)) Hs1). }
    (* ---- 0xad2  addiw s3,s1,1 ---- *)
    assert (Hsx1 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                   = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Haddw : (mword_of_int (Z.of_nat i + 1) : mword 64)
                    = sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mA !!! Regidx s1_idx)
                              (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)).
    { rewrite HAs1 Hsx1. symmetry. apply moi_addw. unfold Z31. lia. }
    iApply (wp_uv_addiw C pt Psh Mi mA (mword_of_int 0xad2)
              (mword_of_int 1 : mword 12) s1_idx s3_idx
              (mword_of_int (Z.of_nat i + 1))
              (ui_sh_ad2 pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Haddw
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mB := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64)]> mA).
    assert (Ead2 : add_vec_int (mword_of_int 0xad2 : mword 64) 4 = mword_of_int 0xad6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ead2) in "Hpc".
    assert (HBs3 : mB !!! Regidx s3_idx
                   = (mword_of_int (Z.of_nat i + 1) : mword 64))
      by exact (upd_eq mA (Regidx s3_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))).
    (* ---- 0xad6  c.mv s1,s3 ---- *)
    assert (Hmv1 : (mword_of_int (Z.of_nat i + 1) : mword 64)
                   = add_vec zero_reg (mB !!! Regidx s3_idx))
      by (rewrite HBs3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi mB (mword_of_int 0xad6)
              s1_idx s3_idx (mword_of_int (Z.of_nat i + 1))
              (ui_sh_ad6 pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mC := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64)]> mB).
    assert (Ead6 : add_vec_int (mword_of_int 0xad6 : mword 64) 2 = mword_of_int 0xad8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ead6) in "Hpc".
    (* ---- 0xad8  bge s3,s4,0xb00 -- NOT taken under [Hfit] ---- *)
    assert (HCs3 : mC !!! Regidx s3_idx
                   = (mword_of_int (Z.of_nat i + 1) : mword 64)).
    { exact (eq_trans (upd_ne mB (Regidx s1_idx) (Regidx s3_idx) _
                         ltac:(vm_compute; discriminate)) HBs3). }
    assert (HCs4 : mC !!! Regidx s4_idx = (mword_of_int max : mword 64)).
    { exact (eq_trans
               (upd_ne mB (Regidx s1_idx) (Regidx s4_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mA (Regidx s3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mE (Regidx s8_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)) Hs4))). }
    assert (Htgt00 : (mword_of_int 0xb00 : mword 64)
                     = add_vec (mword_of_int 0xad8)
                         (sign_extend' 64 (mword_of_int 40 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Htk0 : false = uv_btaken BGE (mC !!! Regidx s3_idx)
                             (mC !!! Regidx s4_idx)).
    { cbn [uv_btaken]. rewrite HCs3 HCs4.
      rewrite (moi_ge_s (Z.of_nat i + 1) max
                 ltac:(unfold Z63; lia) ltac:(unfold Z63; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uv_btype C pt Psh Mi mC (mword_of_int 0xad8)
              (mword_of_int 40 : mword 13) s4_idx s3_idx BGE
              false (mword_of_int 0xb00)
              (ui_sh_ad8 pt Mi Hl HtextI)
              Htk0 Htgt00 ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    assert (Ead8 : (if false then (mword_of_int 0xb00 : mword 64)
                    else add_vec_int (mword_of_int 0xad8 : mword 64) 4)
                   = mword_of_int 0xadc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ead8) in "Hpc".
    (* ---- 0xadc  c.mv a2,s5 ---- *)
    assert (HCs5 : mC !!! Regidx s5_idx = (mword_of_int 1 : mword 64)).
    { exact (eq_trans
               (upd_ne mB (Regidx s1_idx) (Regidx s5_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mA (Regidx s3_idx) (Regidx s5_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mE (Regidx s8_idx) (Regidx s5_idx) _
                        ltac:(vm_compute; discriminate)) Hs5))). }
    assert (Hmv2 : (mword_of_int 1 : mword 64)
                   = add_vec zero_reg (mC !!! Regidx s5_idx))
      by (rewrite HCs5 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi mC (mword_of_int 0xadc)
              a2_idx s5_idx (mword_of_int 1)
              (ui_sh_adc pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Hmv2
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (mD := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> mC).
    assert (Eadc : add_vec_int (mword_of_int 0xadc : mword 64) 2 = mword_of_int 0xade)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eadc) in "Hpc".
    (* ---- 0xade  c.mv a1,s6 ---- *)
    assert (HDs6 : mD !!! Regidx s6_idx
                   = (mword_of_int (uint sp0 - 81) : mword 64)).
    { exact (eq_trans
               (upd_ne mC (Regidx a2_idx) (Regidx s6_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mB (Regidx s1_idx) (Regidx s6_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mA (Regidx s3_idx) (Regidx s6_idx) _
                        ltac:(vm_compute; discriminate))
                     (eq_trans
                        (upd_ne mE (Regidx s8_idx) (Regidx s6_idx) _
                           ltac:(vm_compute; discriminate)) Hs6)))). }
    assert (Hmv3 : (mword_of_int (uint sp0 - 81) : mword 64)
                   = add_vec zero_reg (mD !!! Regidx s6_idx))
      by (rewrite HDs6 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mi mD (mword_of_int 0xade)
              a1_idx s6_idx (mword_of_int (uint sp0 - 81))
              (ui_sh_ade pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Hmv3
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    set (mF := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 81) : mword 64)]> mD).
    assert (Eade : add_vec_int (mword_of_int 0xade : mword 64) 2 = mword_of_int 0xae0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eade) in "Hpc".
    (* ---- 0xae0  c.li a0,0 ---- *)
    assert (Hli0 : (mword_of_int 0 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh Mi mF (mword_of_int 0xae0)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (ui_sh_ae0 pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Hli0
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (mG := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> mF).
    assert (Eae0 : add_vec_int (mword_of_int 0xae0 : mword 64) 2 = mword_of_int 0xae2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eae0) in "Hpc".
    (* ---- 0xae2  jal ra, 0xc9e <read> ---- *)
    assert (Htgtr : (mword_of_int 0xc9e : mword 64)
                    = add_vec (mword_of_int 0xae2)
                        (sign_extend' 64 (mword_of_int 444 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlinkr : (mword_of_int 0xae6 : mword 64)
                     = add_vec_int (mword_of_int 0xae2 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh Mi mG (mword_of_int 0xae2)
              (mword_of_int 444 : mword 21) ra_idx
              (mword_of_int 0xc9e) (mword_of_int 0xae6)
              (ui_sh_ae2 pt Mi Hl HtextI)
              ltac:(vm_compute; discriminate) Htgtr Hlinkr
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    set (mR := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xae6 : mword 64)]> mG).
    iEval (rewrite <- Hsread) in "Hpc".
    (* the register file the callee sees *)
    assert (HRra : mR !!! Regidx ra_idx = (mword_of_int 0xae6 : mword 64))
      by exact (upd_eq mG (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xae6 : mword 64))).
    assert (HRa1 : mR !!! Regidx a1_idx
                   = (mword_of_int (uint sp0 - 81) : mword 64)).
    { exact (eq_trans
               (upd_ne mG (Regidx ra_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mF (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate))
                  (upd_eq mD (Regidx a1_idx)
                     (regval_into_reg
                        (mword_of_int (uint sp0 - 81) : mword 64))))). }
    assert (HRa2 : mR !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
    { exact (eq_trans
               (upd_ne mG (Regidx ra_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mF (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mD (Regidx a1_idx) (Regidx a2_idx) _
                        ltac:(vm_compute; discriminate))
                     (upd_eq mC (Regidx a2_idx)
                        (regval_into_reg (mword_of_int 1 : mword 64)))))). }
    assert (Hu81 : uint (mword_of_int (uint sp0 - 81) : mword 64) = uint sp0 - 81)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hu1 : uint (mword_of_int 1 : mword 64) = 1)
      by (apply uint_moi; unfold Z64; lia).
    (* ---- the call: read(0, sp0-81, 1) ---- *)
    iApply (wp_sh_read C pt gin gbrk hbase hlen Q CID8 Mi mR
              (drop i taken ++ rest)
              ltac:(split_and!;
                    [ exact Hlay | exact HtextI
                    | rewrite HRra; vm_compute; reflexivity ])
              ltac:(rewrite HRa1 HRa2 Hu81 Hu1;
                    exact (stack_wr Mi sp0 96 (uint sp0 - 81) 1 HstI
                             ltac:(lia) ltac:(lia) ltac:(lia)))
              ltac:(rewrite HRa1 Hu81; lia)
              with "Hcg Hin Hpc [Hcont]").
    iIntros (CID9 k M') "%Hklen %Hkn %Heof %Hwrt Hin Hcg Hpc".
    rewrite HRa2 Hu1 in Hkn. rewrite HRa1 Hu81 in Hwrt.
    iEval (rewrite HRra) in "Hpc".
    set (mS := <[Regidx a0_idx := (mword_of_int (Z.of_nat k) : mword 64)]>
                 (<[Regidx a7_idx := (mword_of_int SYS_read : mword 64)]> mR)).
    (* the image invariant survives the one-byte read *)
    assert (Hwin' : sh_io_win MB M' buf (uint sp0 - 81) (take i taken)).
    { exact (sh_io_win_rd MB Mi M' buf (uint sp0 - 81) max
               (take i taken) (take k (drop i taken ++ rest))
               Hrbdisj Htakelen
               ltac:(rewrite length_take; lia) Hwrt Hwin). }
    assert (HtextI' : sh_text_sub M')
      by exact (sh_io_win_text MB M' buf (uint sp0 - 81) (take i taken)
                  Hbuflo Hrb8 Hwin' Htext).
    pose proof Hwin' as (HwI' & HwO' & HwD').
    assert (HstI' : uv_stack pt M' sp0 96)
      by exact (uv_stack_dom pt MB M' sp0 96 HwD' HstB).
    assert (HwrI' : uv_wr pt M' buf max)
      by exact (uv_wr_dom pt MB M' buf max HwD' HwrB).
    (* ---- 0xae6  blez a0,0xb00 ---- *)
    assert (HSa0 : mS !!! Regidx a0_idx = (mword_of_int (Z.of_nat k) : mword 64))
      by exact (upd_eq _ (Regidx a0_idx)
                  (mword_of_int (Z.of_nat k) : mword 64)).
    iDestruct "Hcg" as "(#Hcapx & Hlinx & Hgprx)".
    iDestruct (gpr_file_x0 mS x0_idx ltac:(vm_compute; reflexivity) with "Hgprx")
      as "[%Hx0 Hgprx]".
    iAssert (uv_cap_gpr (CID := CID9) C pt Psh M' mS) with "[Hlinx Hgprx]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcapx Hlinx Hgprx". }
    assert (Hkr : (0 <= Z.of_nat k <= 1)%Z) by lia.
    assert (Htgt00' : (mword_of_int 0xb00 : mword 64)
                      = add_vec (mword_of_int 0xae6)
                          (sign_extend' 64 (mword_of_int 26 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct Hi as [ Hlt | (Hnil & Hi0) ].
    - (* ============ a byte is there: k = 1 ============ *)
      destruct (lookup_lt_is_Some_2 taken i Hlt) as (bc & Hbc).
      assert (Hdr : drop i taken = bc :: drop (S i) taken)
        by (apply drop_S; exact Hbc).
      assert (Hne : drop i taken ++ rest <> []).
      { rewrite Hdr. cbn [app]. intro He. discriminate He. }
      assert (Hk1 : k = 1%nat).
      { destruct k as [ | k' ]; [ exfalso; exact (Hne (Heof eq_refl)) | lia ]. }
      subst k.
      assert (Htake1 : take 1 (drop i taken ++ rest) = [bc])
        by (rewrite Hdr; reflexivity).
      assert (Hdrop1 : drop 1 (drop i taken ++ rest) = drop (S i) taken ++ rest)
        by (rewrite Hdr; reflexivity).
      rewrite Htake1 in Hwrt.
      iEval (rewrite Hdrop1) in "Hin".
      destruct Hwrt as (Hwt1 & Hwt2 & Hwt3).
      assert (Hbcat : M' !! (uint sp0 - 81) = Some bc).
      { pose proof (Hwt1 0%nat bc eq_refl) as Hh.
        replace (uint sp0 - 81 + Z.of_nat 0) with (uint sp0 - 81) in Hh by lia.
        exact Hh. }
      assert (Htkb : false = uv_btaken BGE (mS !!! Regidx x0_idx)
                               (mS !!! Regidx a0_idx)).
      { cbn [uv_btaken]. rewrite Hx0 HSa0 zero_reg_moi.
        rewrite (moi_ge_s 0 (Z.of_nat 1) ltac:(unfold Z63; lia)
                   ltac:(unfold Z63; cbn; lia)).
        reflexivity. }
      iApply (wp_uv_btype C pt Psh M' mS (mword_of_int 0xae6)
                (mword_of_int 26 : mword 13) a0_idx x0_idx BGE
                false (mword_of_int 0xb00)
                (ui_sh_ae6 pt M' Hl HtextI')
                Htkb Htgt00' ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CID10) "Hcg Hpc".
      assert (Eae6 : (if false then (mword_of_int 0xb00 : mword 64)
                      else add_vec_int (mword_of_int 0xae6 : mword 64) 4)
                     = mword_of_int 0xaea)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eae6) in "Hpc".
      (* ---- 0xaea  lbu a5,-81(s0) ---- *)
      assert (HSs0 : mS !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
      { exact (eq_trans
                 (upd_ne _ (Regidx a0_idx) (Regidx s0_idx) _
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne mR (Regidx a7_idx) (Regidx s0_idx) _
                       ltac:(vm_compute; discriminate))
                    (eq_trans
                       (upd_ne mG (Regidx ra_idx) (Regidx s0_idx) _
                          ltac:(vm_compute; discriminate))
                       (eq_trans
                          (upd_ne mF (Regidx a0_idx) (Regidx s0_idx) _
                             ltac:(vm_compute; discriminate))
                          (eq_trans
                             (upd_ne mD (Regidx a1_idx) (Regidx s0_idx) _
                                ltac:(vm_compute; discriminate))
                             (eq_trans
                                (upd_ne mC (Regidx a2_idx) (Regidx s0_idx) _
                                   ltac:(vm_compute; discriminate))
                                (eq_trans
                                   (upd_ne mB (Regidx s1_idx) (Regidx s0_idx) _
                                      ltac:(vm_compute; discriminate))
                                   (eq_trans
                                      (upd_ne mA (Regidx s3_idx) (Regidx s0_idx) _
                                         ltac:(vm_compute; discriminate))
                                      (eq_trans
                                         (upd_ne mE (Regidx s8_idx) (Regidx s0_idx) _
                                            ltac:(vm_compute; discriminate))
                                         Hs0))))))))). }
      assert (Hm81 : (sign_extend' 64 (mword_of_int 4015 : mword 12) : mword 64)
                     = mword_of_int (-81))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hvarb : (mword_of_int (uint sp0 - 81) : mword 64)
                      = add_vec (mS !!! Regidx s0_idx)
                          (sign_extend' 64 (mword_of_int 4015 : mword 12))).
      { rewrite HSs0 Hm81 moi_add. f_equal; lia. }
      destruct (stack_leaf M' sp0 96 (uint sp0 - 81) HstI' ltac:(lia))
        as (wrb & Hwrbl & _ & Hwrbld).
      assert (Hcanrb : uva_canon (mword_of_int (uint sp0 - 81) : mword 64))
        by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
      assert (Hbcat' : M' !! (uint (mword_of_int (uint sp0 - 81) : mword 64))
                       = Some bc) by (rewrite Hu81; exact Hbcat).
      iApply (wp_uv_lbu C pt Psh M' mS (mword_of_int 0xaea)
                (mword_of_int 4015 : mword 12) s0_idx a5_idx
                wrb (mword_of_int (uint sp0 - 81))
                (mword_of_int (bv_unsigned bc)) bc
                (ui_sh_aea pt M' Hl HtextI')
                ltac:(vm_compute; discriminate) Hvarb Hwrbl Hwrbld Hcanrb
                Hbcat' ltac:(symmetry; apply zext8_moi)
                with "Hcg Hpc").
      iIntros (CID11) "Hcg Hpc".
      set (mT := <[Regidx a5_idx
                   := regval_into_reg
                        (mword_of_int (bv_unsigned bc) : mword 64)]> mS).
      assert (Eaea : add_vec_int (mword_of_int 0xaea : mword 64) 4
                     = mword_of_int 0xaee)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eaea) in "Hpc".
      (* ---- 0xaee  sb a5,0(s2) ---- *)
      assert (HTs2 : mT !!! Regidx s2_idx
                     = (mword_of_int (buf + Z.of_nat i) : mword 64)).
      { exact (eq_trans
                 (upd_ne mS (Regidx a5_idx) (Regidx s2_idx) _
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne _ (Regidx a0_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate))
                    (eq_trans
                       (upd_ne mR (Regidx a7_idx) (Regidx s2_idx) _
                          ltac:(vm_compute; discriminate))
                       (eq_trans
                          (upd_ne mG (Regidx ra_idx) (Regidx s2_idx) _
                             ltac:(vm_compute; discriminate))
                          (eq_trans
                             (upd_ne mF (Regidx a0_idx) (Regidx s2_idx) _
                                ltac:(vm_compute; discriminate))
                             (eq_trans
                                (upd_ne mD (Regidx a1_idx) (Regidx s2_idx) _
                                   ltac:(vm_compute; discriminate))
                                (eq_trans
                                   (upd_ne mC (Regidx a2_idx) (Regidx s2_idx) _
                                      ltac:(vm_compute; discriminate))
                                   (eq_trans
                                      (upd_ne mB (Regidx s1_idx) (Regidx s2_idx) _
                                         ltac:(vm_compute; discriminate))
                                      (eq_trans
                                         (upd_ne mA (Regidx s3_idx) (Regidx s2_idx) _
                                            ltac:(vm_compute; discriminate))
                                         (eq_trans
                                            (upd_ne mE (Regidx s8_idx) (Regidx s2_idx) _
                                               ltac:(vm_compute; discriminate))
                                            Hs2)))))))))). }
      assert (HTa5 : mT !!! Regidx a5_idx
                     = (mword_of_int (bv_unsigned bc) : mword 64))
        by exact (upd_eq mS (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (bv_unsigned bc) : mword 64))).
      assert (Hz0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hvasb : (mword_of_int (buf + Z.of_nat i) : mword 64)
                      = add_vec (mT !!! Regidx s2_idx)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite HTs2 Hz0 moi_add. f_equal; lia. }
      destruct (uwr_leaf _ _ _ _ HwrI' (Z.of_nat i) ltac:(lia))
        as (wsb & Hwsbl & Hwsbok).
      assert (Huvi : uint (mword_of_int (buf + Z.of_nat i) : mword 64)
                     = buf + Z.of_nat i) by (apply uint_moi; unfold Z64; lia).
      assert (Hcansb : uva_canon (mword_of_int (buf + Z.of_nat i) : mword 64))
        by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
      destruct (uwr_bytes _ _ _ _ HwrI' (Z.of_nat i) ltac:(lia)) as (bo & Hbo).
      assert (Hbo' : M' !! (uint (mword_of_int (buf + Z.of_nat i) : mword 64))
                     = Some bo) by (rewrite Huvi; exact Hbo).
      iApply (wp_uv_sb C pt Psh M' mT (mword_of_int 0xaee)
                (mword_of_int 0 : mword 12) s2_idx a5_idx
                wsb (mword_of_int (buf + Z.of_nat i))
                (mword_of_int (bv_unsigned bc)) bo
                (ui_sh_aee pt M' Hl HtextI')
                Hvasb (eq_sym HTa5) Hwsbl Hwsbok Hcansb Hbo'
                with "Hcg Hpc").
      iIntros (CID12) "Hcg Hpc".
      iEval (rewrite Huvi) in "Hcg".
      set (M2 := uM_store M' (buf + Z.of_nat i) 1
                   (mword_of_int (bv_unsigned bc) : mword 64)).
      assert (Eaee : add_vec_int (mword_of_int 0xaee : mword 64) 4
                     = mword_of_int 0xaf2)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eaee) in "Hpc".
      assert (Hlentake : length (take i taken) = i)
        by (rewrite length_take; lia).
      assert (Hwin2 : sh_io_win MB M2 buf (uint sp0 - 81)
                        (take i taken ++ [bc])).
      { unfold M2.
        replace (buf + Z.of_nat i)
          with (buf + Z.of_nat (length (take i taken))) by (rewrite Hlentake; lia).
        exact (sh_io_win_sb MB M' buf (uint sp0 - 81) (take i taken) bc
                 (mword_of_int (bv_unsigned bc)) (nth_byte0_moi' bc) Hwin'). }
      assert (Htake2 : take (S i) taken = take i taken ++ [bc])
        by (rewrite (take_S_r taken i bc Hbc); reflexivity).
      assert (Htext2 : sh_text_sub M2)
        by exact (sh_io_win_text MB M2 buf (uint sp0 - 81) _ Hbuflo Hrb8
                    Hwin2 Htext).
      pose proof Hwin2 as (Hw2I & Hw2O & Hw2D).
      assert (Hst2 : uv_stack pt M2 sp0 96)
        by exact (uv_stack_dom pt MB M2 sp0 96 Hw2D HstB).
      (* ---- 0xaf2  c.addi s2,s2,1 ---- *)
      assert (Hc1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                     : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hadds2 : (mword_of_int (buf + Z.of_nat (S i)) : mword 64)
                       = add_vec (mT !!! Regidx s2_idx)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 1 : mword 6)))).
      { rewrite HTs2 Hc1 moi_add. f_equal; lia. }
      iApply (wp_uv_caddi C pt Psh M2 mT (mword_of_int 0xaf2)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (buf + Z.of_nat (S i)))
                (ui_sh_af2 pt M2 Hl Htext2)
                ltac:(vm_compute; discriminate) Hadds2
                with "Hcg Hpc").
      iIntros (CID13) "Hcg Hpc".
      set (mU := <[Regidx s2_idx
                   := regval_into_reg
                        (mword_of_int (buf + Z.of_nat (S i)) : mword 64)]> mT).
      assert (Eaf2 : add_vec_int (mword_of_int 0xaf2 : mword 64) 2
                     = mword_of_int 0xaf4)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eaf2) in "Hpc".
      (* ---- 0xaf4  addi a4,a5,-10 ---- *)
      assert (HUa5 : mU !!! Regidx a5_idx
                     = (mword_of_int (bv_unsigned bc) : mword 64)).
      { exact (eq_trans (upd_ne mT (Regidx s2_idx) (Regidx a5_idx) _
                           ltac:(vm_compute; discriminate)) HTa5). }
      assert (Hm10 : (sign_extend' 64 (mword_of_int 4086 : mword 12) : mword 64)
                     = mword_of_int (-10))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Ha4v : (mword_of_int (bv_unsigned bc - 10) : mword 64)
                     = add_vec (mU !!! Regidx a5_idx)
                         (sign_extend' 64 (mword_of_int 4086 : mword 12))).
      { rewrite HUa5 Hm10 moi_add. f_equal; lia. }
      iApply (wp_uv_addi C pt Psh M2 mU (mword_of_int 0xaf4)
                (mword_of_int 4086 : mword 12) a5_idx a4_idx
                (mword_of_int (bv_unsigned bc - 10))
                (ui_sh_af4 pt M2 Hl Htext2)
                ltac:(vm_compute; discriminate) Ha4v
                with "Hcg Hpc").
      iIntros (CID14) "Hcg Hpc".
      set (mV := <[Regidx a4_idx
                   := regval_into_reg
                        (mword_of_int (bv_unsigned bc - 10) : mword 64)]> mU).
      assert (Eaf4 : add_vec_int (mword_of_int 0xaf4 : mword 64) 4
                     = mword_of_int 0xaf8)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eaf4) in "Hpc".
      assert (HVa4 : mV !!! Regidx a4_idx
                     = (mword_of_int (bv_unsigned bc - 10) : mword 64))
        by exact (upd_eq mU (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (bv_unsigned bc - 10) : mword 64))).
      assert (Htgtfe : (mword_of_int 0xafe : mword 64)
                       = add_vec (mword_of_int 0xaf8)
                           (sign_extend' 64 (sign_extend' 13
                              (concat_vec (mword_of_int 3 : mword 8) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      (* the register bundle every exit hands back *)
      assert (HVpres : forall r : mword 5, ucallee_saved_idx r = true ->
                Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s8_idx ->
                mV !!! Regidx r = mE !!! Regidx r).
      { intros r Hr N9 N18 N19 N24.
        assert (N1 : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N10 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N11 : Regidx r <> Regidx a1_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N12 : Regidx r <> Regidx a2_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N14 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N15 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N17 : Regidx r <> Regidx a7_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        exact (eq_trans (upd_ne mU (Regidx a4_idx) (Regidx r) _ N14)
                 (eq_trans (upd_ne mT (Regidx s2_idx) (Regidx r) _ N18)
                    (eq_trans (upd_ne mS (Regidx a5_idx) (Regidx r) _ N15)
                       (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx r) _ N10)
                          (eq_trans (upd_ne mR (Regidx a7_idx) (Regidx r) _ N17)
                             (eq_trans (upd_ne mG (Regidx ra_idx) (Regidx r) _ N1)
                                (eq_trans (upd_ne mF (Regidx a0_idx) (Regidx r) _ N10)
                                   (eq_trans (upd_ne mD (Regidx a1_idx) (Regidx r) _ N11)
                                      (eq_trans (upd_ne mC (Regidx a2_idx) (Regidx r) _ N12)
                                         (eq_trans (upd_ne mB (Regidx s1_idx) (Regidx r) _ N9)
                                            (eq_trans (upd_ne mA (Regidx s3_idx) (Regidx r) _ N19)
                                               (upd_ne mE (Regidx s8_idx) (Regidx r) _ N24)))))))))))). }
      pose proof (bv8_rng bc) as Hbcr.
      destruct (Z.eq_dec (bv_unsigned bc) 10) as [ Hnl | Hnnl ].
      + (* ---- the byte is '\n': beqz taken, s8 := i+1, exit ---- *)
        assert (Hbcnl : bc = ubyte_nl) by (apply bv8_is_nl; exact Hnl).
        assert (Htkn : true = eq_vec (mV !!! Regidx a4_idx) zero_reg).
        { rewrite HVa4 (moi_eq_zero_sub (bv_unsigned bc) 10 Hbcr ltac:(lia)).
          symmetry. apply Z.eqb_eq. exact Hnl. }
        iApply (wp_uv_cbeqz C pt Psh M2 mV (mword_of_int 0xaf8)
                  (mword_of_int 3 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                  true (mword_of_int 0xafe)
                  (ui_sh_af8 pt M2 Hl Htext2)
                  ltac:(vm_compute; reflexivity) Htkn Htgtfe
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID15) "Hcg Hpc".
        (* ---- 0xafe  c.mv s8,s3 ---- *)
        assert (HVs3 : mV !!! Regidx s3_idx
                       = (mword_of_int (Z.of_nat i + 1) : mword 64)).
        { exact (eq_trans
                   (upd_ne mU (Regidx a4_idx) (Regidx s3_idx) _
                      ltac:(vm_compute; discriminate))
                   (eq_trans
                      (upd_ne mT (Regidx s2_idx) (Regidx s3_idx) _
                         ltac:(vm_compute; discriminate))
                      (eq_trans
                         (upd_ne mS (Regidx a5_idx) (Regidx s3_idx) _
                            ltac:(vm_compute; discriminate))
                         (eq_trans
                            (upd_ne _ (Regidx a0_idx) (Regidx s3_idx) _
                               ltac:(vm_compute; discriminate))
                            (eq_trans
                               (upd_ne mR (Regidx a7_idx) (Regidx s3_idx) _
                                  ltac:(vm_compute; discriminate))
                               (eq_trans
                                  (upd_ne mG (Regidx ra_idx) (Regidx s3_idx) _
                                     ltac:(vm_compute; discriminate))
                                  (eq_trans
                                     (upd_ne mF (Regidx a0_idx) (Regidx s3_idx) _
                                        ltac:(vm_compute; discriminate))
                                     (eq_trans
                                        (upd_ne mD (Regidx a1_idx) (Regidx s3_idx) _
                                           ltac:(vm_compute; discriminate))
                                        (eq_trans
                                           (upd_ne mC (Regidx a2_idx) (Regidx s3_idx) _
                                              ltac:(vm_compute; discriminate))
                                           (eq_trans
                                              (upd_ne mB (Regidx s1_idx) (Regidx s3_idx) _
                                                 ltac:(vm_compute; discriminate))
                                              HBs3)))))))))). }
        assert (Hmv4 : (mword_of_int (Z.of_nat i + 1) : mword 64)
                       = add_vec zero_reg (mV !!! Regidx s3_idx))
          by (rewrite HVs3 moi_add_zero_l; reflexivity).
        iApply (wp_uv_cmv C pt Psh M2 mV (mword_of_int 0xafe)
                  s8_idx s3_idx (mword_of_int (Z.of_nat i + 1))
                  (ui_sh_afe pt M2 Hl Htext2)
                  ltac:(vm_compute; discriminate) Hmv4
                  with "Hcg Hpc").
        iIntros (CID16) "Hcg Hpc".
        assert (Eafe : add_vec_int (mword_of_int 0xafe : mword 64) 2
                       = mword_of_int 0xb00)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Eafe) in "Hpc".
        (* the newline is the LAST byte of [taken] *)
        assert (Hend : S i = length taken).
        { destruct Htk as [ (line & Hline & Hlnz) | (He & _) ].
          - assert (Hll : length taken = S (length line))
              by (rewrite Hline length_app; cbn [length]; lia).
            destruct (decide (i < length line)%nat) as [ Hlti | Hgei ].
            + exfalso.
              rewrite Hline (lookup_app_l line [ubyte_nl] i Hlti) in Hbc.
              destruct (Hlnz i bc Hbc) as (Hn1 & _). exact (Hn1 Hbcnl).
            + lia.
          - exfalso. rewrite He in Hlt. cbn [length] in Hlt. lia. }
        assert (Hfull : take (S i) taken = taken)
          by (apply take_ge; lia).
        assert (Hdropnil : drop (S i) taken ++ rest = rest)
          by (rewrite (drop_ge taken (S i) ltac:(lia)); reflexivity).
        iEval (rewrite Hdropnil) in "Hin".
        iApply ("Hcont" $! CID16
                  (<[Regidx s8_idx
                     := regval_into_reg
                          (mword_of_int (Z.of_nat i + 1) : mword 64)]> mV)
                  M2 with "[] [] [] Hin Hcg Hpc").
        * iPureIntro. rewrite <- Hfull, Htake2. exact Hwin2.
        * iPureIntro.
          replace (Z.of_nat (length taken)) with (Z.of_nat i + 1) by lia.
          exact (upd_eq mV (Regidx s8_idx)
                   (regval_into_reg
                      (mword_of_int (Z.of_nat i + 1) : mword 64))).
        * iPureIntro. intros r Hr N9 N18 N19 N24.
          rewrite (upd_ne mV (Regidx s8_idx) (Regidx r) _ N24).
          exact (HVpres r Hr N9 N18 N19 N24).
      + (* ---- an ordinary byte: beqz falls through, bnez takes the edge ---- *)
        assert (Hncr : bv_unsigned bc <> 13).
        { intro Hcr.
          destruct Htk as [ (line & Hline & Hlnz) | (He & _) ].
          - assert (Hll : length taken = S (length line))
              by (rewrite Hline length_app; cbn [length]; lia).
            destruct (decide (i < length line)%nat) as [ Hlti | Hgei ].
            + rewrite Hline (lookup_app_l line [ubyte_nl] i Hlti) in Hbc.
              destruct (Hlnz i bc Hbc) as (_ & Hn2).
              exact (Hn2 (proj1 (bv8_is_cr bc) Hcr)).
            + assert (Hie : i = length line) by lia.
              rewrite Hline Hie (lookup_app_r line [ubyte_nl] (length line)
                                   ltac:(lia)) in Hbc.
              rewrite Nat.sub_diag in Hbc. cbn in Hbc. injection Hbc as <-.
              rewrite nl_val in Hnnl. exact (Hnnl eq_refl).
          - exfalso. rewrite He in Hlt. cbn [length] in Hlt. lia. }
        assert (Htkn : false = eq_vec (mV !!! Regidx a4_idx) zero_reg).
        { rewrite HVa4 (moi_eq_zero_sub (bv_unsigned bc) 10 Hbcr ltac:(lia)).
          symmetry. apply Z.eqb_neq. exact Hnnl. }
        iApply (wp_uv_cbeqz C pt Psh M2 mV (mword_of_int 0xaf8)
                  (mword_of_int 3 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                  false (mword_of_int 0xafe)
                  (ui_sh_af8 pt M2 Hl Htext2)
                  ltac:(vm_compute; reflexivity) Htkn Htgtfe
                  ltac:(intro Hc0; discriminate Hc0)
                  with "Hcg Hpc").
        iIntros (CID15) "Hcg Hpc".
        assert (Eaf8 : (if false then (mword_of_int 0xafe : mword 64)
                        else add_vec_int (mword_of_int 0xaf8 : mword 64) 2)
                       = mword_of_int 0xafa)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Eaf8) in "Hpc".
        (* ---- 0xafa  c.addi a5,a5,-13 ---- *)
        assert (HVa5 : mV !!! Regidx a5_idx
                       = (mword_of_int (bv_unsigned bc) : mword 64)).
        { exact (eq_trans (upd_ne mU (Regidx a4_idx) (Regidx a5_idx) _
                             ltac:(vm_compute; discriminate)) HUa5). }
        assert (Hc13 : (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 51 : mword 6)) : mword 64)
                       = mword_of_int (-13))
          by (apply bv_eq; vm_compute; reflexivity).
        assert (Ha5v : (mword_of_int (bv_unsigned bc - 13) : mword 64)
                       = add_vec (mV !!! Regidx a5_idx)
                           (sign_extend' 64
                              (sign_extend' 12 (mword_of_int 51 : mword 6)))).
        { rewrite HVa5 Hc13 moi_add. f_equal; lia. }
        iApply (wp_uv_caddi C pt Psh M2 mV (mword_of_int 0xafa)
                  (mword_of_int 51 : mword 6) a5_idx
                  (mword_of_int (bv_unsigned bc - 13))
                  (ui_sh_afa pt M2 Hl Htext2)
                  ltac:(vm_compute; discriminate) Ha5v
                  with "Hcg Hpc").
        iIntros (CID16) "Hcg Hpc".
        set (mW := <[Regidx a5_idx
                     := regval_into_reg
                          (mword_of_int (bv_unsigned bc - 13) : mword 64)]> mV).
        assert (Eafa : add_vec_int (mword_of_int 0xafa : mword 64) 2
                       = mword_of_int 0xafc)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Eafa) in "Hpc".
        (* ---- 0xafc  c.bnez a5,0xad0 -- the back edge ---- *)
        assert (HWa5 : mW !!! Regidx a5_idx
                       = (mword_of_int (bv_unsigned bc - 13) : mword 64))
          by exact (upd_eq mV (Regidx a5_idx)
                      (regval_into_reg
                         (mword_of_int (bv_unsigned bc - 13) : mword 64))).
        assert (Htkbz : true = neq_vec (mW !!! Regidx a5_idx) zero_reg).
        { rewrite HWa5 (moi_neq_zero_sub (bv_unsigned bc) 13 Hbcr ltac:(lia)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hncr. }
        assert (Htgtd0 : (mword_of_int 0xad0 : mword 64)
                         = add_vec (mword_of_int 0xafc)
                             (sign_extend' 64 (sign_extend' 13
                                (concat_vec (mword_of_int 234 : mword 8) ('b"0")))))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_uv_cbnez C pt Psh M2 mW (mword_of_int 0xafc)
                  (mword_of_int 234 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                  true (mword_of_int 0xad0)
                  (ui_sh_afc pt M2 Hl Htext2)
                  ltac:(vm_compute; reflexivity) Htkbz Htgtd0
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID17) "Hcg Hpc".
        (* [S i] is still inside [taken]: the byte just read was not '\n' *)
        assert (Hnext : (S i < length taken)%nat).
        { destruct Htk as [ (line & Hline & Hlnz) | (He & _) ].
          - assert (Hll : length taken = S (length line))
              by (rewrite Hline length_app; cbn [length]; lia).
            destruct (decide (i < length line)%nat) as [ Hlti | Hgei ];
              [ lia | ].
            exfalso.
            assert (Hie : i = length line) by lia.
            rewrite Hline Hie (lookup_app_r line [ubyte_nl] (length line)
                                 ltac:(lia)) in Hbc.
            rewrite Nat.sub_diag in Hbc. cbn in Hbc. injection Hbc as <-.
            rewrite nl_val in Hnnl. exact (Hnnl eq_refl).
          - exfalso. rewrite He in Hlt. cbn [length] in Hlt. lia. }
        (* the loop registers, at [S i] *)
        assert (HWpres : forall r : mword 5, ucallee_saved_idx r = true ->
                  Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                  Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s8_idx ->
                  mW !!! Regidx r = mE !!! Regidx r).
        { intros r Hr N9 N18 N19 N24.
          assert (N15 : Regidx r <> Regidx a5_idx)
            by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
          rewrite (upd_ne mV (Regidx a5_idx) (Regidx r) _ N15).
          exact (HVpres r Hr N9 N18 N19 N24). }
        assert (HWsp : mW !!! Regidx sp_idx
                       = (mword_of_int (uint sp0 - 96) : mword 64))
          by (rewrite (HWpres sp_idx ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hsp).
        assert (HWs0 : mW !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
          by (rewrite (HWpres s0_idx ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hs0).
        assert (HWs4 : mW !!! Regidx s4_idx = (mword_of_int max : mword 64))
          by (rewrite (HWpres s4_idx ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hs4).
        assert (HWs5 : mW !!! Regidx s5_idx = (mword_of_int 1 : mword 64))
          by (rewrite (HWpres s5_idx ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hs5).
        assert (HWs6 : mW !!! Regidx s6_idx
                       = (mword_of_int (uint sp0 - 81) : mword 64))
          by (rewrite (HWpres s6_idx ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hs6).
        assert (HWs1 : mW !!! Regidx s1_idx
                       = (mword_of_int (Z.of_nat (S i)) : mword 64)).
        { rewrite (upd_ne mV (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mU (Regidx a4_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mT (Regidx s2_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mS (Regidx a5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mR (Regidx a7_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mG (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mF (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mD (Regidx a1_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mC (Regidx a2_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_eq mB (Regidx s1_idx)
                     (regval_into_reg
                        (mword_of_int (Z.of_nat i + 1) : mword 64))).
          replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia.
          reflexivity. }
        assert (HWs2 : mW !!! Regidx s2_idx
                       = (mword_of_int (buf + Z.of_nat (S i)) : mword 64)).
        { rewrite (upd_ne mV (Regidx a5_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mU (Regidx a4_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
          exact (upd_eq mT (Regidx s2_idx)
                   (regval_into_reg
                      (mword_of_int (buf + Z.of_nat (S i)) : mword 64))). }
        iApply (IH CID17 MB M2 mW sp0 buf max taken rest (S i)
                  ltac:(lia) Hlay Htext HstB Hsphi Hbuflo HwrB Hdisj Htk
                  Hfit Hmax31 ltac:(left; exact Hnext)
                  ltac:(rewrite Htake2; exact Hwin2)
                  HWsp HWs0 HWs1 HWs2 HWs4 HWs5 HWs6
                  with "Hcg Hin Hpc").
        iIntros (CID18 m' M'') "%HA %HB %HC Hin Hcg Hpc".
        iApply ("Hcont" $! CID18 m' M'' with "[] [] [] Hin Hcg Hpc").
        * iPureIntro. exact HA.
        * iPureIntro. exact HB.
        * iPureIntro. intros r Hr N9 N18 N19 N24.
          rewrite (HC r Hr N9 N18 N19 N24). exact (HWpres r Hr N9 N18 N19 N24).
    - (* ============ EOF on the first read: k = 0, taken = [] ============ *)
      assert (Hrestnil : rest = []).
      { destruct Htk as [ (line & Hline & _) | (_ & Hr) ]; [ | exact Hr ].
        exfalso. rewrite Hnil in Hline.
        destruct line as [ | x xs ]; cbn in Hline; discriminate. }
      subst i.
      assert (Hstrnil : drop 0%nat taken ++ rest = [])
        by (rewrite Hnil Hrestnil; reflexivity).
      assert (Hk0 : k = 0%nat).
      { rewrite Hstrnil in Hklen. cbn [length] in Hklen. lia. }
      subst k.
      assert (Hdrop0 : drop 0%nat (drop 0%nat taken ++ rest) = rest)
        by (rewrite Hnil; reflexivity).
      iEval (rewrite Hdrop0) in "Hin".
      assert (Htkb : true = uv_btaken BGE (mS !!! Regidx x0_idx)
                              (mS !!! Regidx a0_idx)).
      { cbn [uv_btaken]. rewrite Hx0 HSa0 zero_reg_moi.
        rewrite (moi_ge_s 0 (Z.of_nat 0) ltac:(unfold Z63; lia)
                   ltac:(unfold Z63; cbn; lia)).
        reflexivity. }
      iApply (wp_uv_btype C pt Psh M' mS (mword_of_int 0xae6)
                (mword_of_int 26 : mword 13) a0_idx x0_idx BGE
                true (mword_of_int 0xb00)
                (ui_sh_ae6 pt M' Hl HtextI')
                Htkb Htgt00' ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID10) "Hcg Hpc".
      iApply ("Hcont" $! CID10 mS M' with "[] [] [] Hin Hcg Hpc").
      + iPureIntro. rewrite Hnil. rewrite Hnil in Hwin'. exact Hwin'.
      + iPureIntro.
        replace (Z.of_nat (length taken)) with 0 by (rewrite Hnil; reflexivity).
        assert (HSs8 : mS !!! Regidx s8_idx = (mword_of_int 0 : mword 64)).
        { rewrite (upd_ne _ (Regidx a0_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mR (Regidx a7_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mG (Regidx ra_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mF (Regidx a0_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mD (Regidx a1_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mC (Regidx a2_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mB (Regidx s1_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite (upd_ne mA (Regidx s3_idx) (Regidx s8_idx) _
                     ltac:(vm_compute; discriminate)).
          exact (upd_eq mE (Regidx s8_idx)
                   (regval_into_reg (mword_of_int 0 : mword 64))). }
        exact HSs8.
      + iPureIntro. intros r Hr N9 N18 N19 N24.
        assert (N1 : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N10 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N11 : Regidx r <> Regidx a1_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N12 : Regidx r <> Regidx a2_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (N17 : Regidx r <> Regidx a7_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        exact (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx r) _ N10)
                 (eq_trans (upd_ne mR (Regidx a7_idx) (Regidx r) _ N17)
                    (eq_trans (upd_ne mG (Regidx ra_idx) (Regidx r) _ N1)
                       (eq_trans (upd_ne mF (Regidx a0_idx) (Regidx r) _ N10)
                          (eq_trans (upd_ne mD (Regidx a1_idx) (Regidx r) _ N11)
                             (eq_trans (upd_ne mC (Regidx a2_idx) (Regidx r) _ N12)
                                (eq_trans (upd_ne mB (Regidx s1_idx) (Regidx r) _ N9)
                                   (eq_trans (upd_ne mA (Regidx s3_idx) (Regidx r) _ N19)
                                      (upd_ne mE (Regidx s8_idx) (Regidx r) _ N24))))))))).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §4 gets @0xaaa -- the whole function.                                 *)
  (*                                                                       *)
  (*   aaa..ac0  the 96-byte frame (ra, s0..s8)                            *)
  (*   ac2..ace  s7 = buf, s4 = max, s2 = &buf[i], s1 = i, s6 = &c, s5 = 1 *)
  (*   ad0..afe  the read loop                                             *)
  (*   b00..b06  buf[i] = 0; a0 = buf                                      *)
  (*   b08..b1e  the frame back                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_gets (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (buf max : Z) (taken rest : list (bv 8)) :
    wp_sh_gets_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 buf max
      taken rest.
  Proof.
    intros Hlay Htext Hsp Hst Hbufa Hmaxa Htk Hfit Hwr Hfr Hbuflo Hdisj
           Hret2.
    destruct Hfit as (Hfit1 & Hfit2).
    destruct sh_syms_pins as (_&_&_& Hsgets & _).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    assert (Hsphi : 8192 <= uint sp0 - 96) by lia.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 31) with 2147483648 in Hfit2.
    pose proof (uwr_lo _ _ _ _ Hwr) as Hb0.
    pose proof (uwr_hi _ _ _ _ Hwr) as Hbhi.
    change (2 ^ 38) with 274877906944 in Hbhi.
    assert (Honly0 : uM_only M M (uint sp0 - 96) 96) by (apply uM_only_refl).
    iIntros "Hcg Hin Hpc Hcont".
    iEval (rewrite Hsgets) in "Hpc".
    (* ---- 0xaaa  c.addi16sp sp,sp,-96 ---- *)
    assert (Hspc : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
    assert (Hi16 : (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))
                    : mword 64) = mword_of_int (-96))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hspw : (mword_of_int (uint sp0 - 96) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    { rewrite Hspc Hi16 moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0xaaa)
              (mword_of_int 58 : mword 6) (mword_of_int (uint sp0 - 96))
              (ui_sh_aaa pt M Hl Htext) Hspw with "Hcg Hpc").
    iIntros (CIDs0) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64)]> m).
    assert (Eaaa : add_vec_int (mword_of_int 0xaaa : mword 64) 2
                   = mword_of_int 0xaac)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eaaa) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 96) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 96) : mword 64))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xaac  c.sdsp ra_idx,88(sp) ---- *)
    iApply (wp_sh_spill CIDs0 Psh 0xaac 0xaae 96 88 (mword_of_int 11 : mword 6)
              ra_idx M m1 sp0 Hst Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_aac pt M Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs1) "Hcg Hpc".
    set (MB1 := uM_store8 M (uint sp0 - 96 + 88) (m1 !!! Regidx ra_idx)).
    assert (Htext1 : sh_text_sub MB1)
      by (unfold MB1; apply sh_text_sub_store8'; [ exact Htext | lia ]).
    assert (Hst1 : uv_stack pt MB1 sp0 96).
    { apply (uv_stack_dom pt M MB1 sp0 96); [ | exact Hst ].
      intros x Hx. unfold MB1. apply uM_store8_is_Some. exact Hx. }
    assert (Honly1 : uM_only M MB1 (uint sp0 - 96) 96)
      by (unfold MB1; apply only_step8; [ lia | lia | exact Honly0 ]).
    (* ---- 0xaae  c.sdsp s0_idx,80(sp) ---- *)
    iApply (wp_sh_spill CIDs1 Psh 0xaae 0xab0 96 80 (mword_of_int 10 : mword 6)
              s0_idx MB1 m1 sp0 Hst1 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_aae pt MB1 Hl Htext1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs2) "Hcg Hpc".
    set (MB2 := uM_store8 MB1 (uint sp0 - 96 + 80) (m1 !!! Regidx s0_idx)).
    assert (Htext2 : sh_text_sub MB2)
      by (unfold MB2; apply sh_text_sub_store8'; [ exact Htext1 | lia ]).
    assert (Hst2 : uv_stack pt MB2 sp0 96).
    { apply (uv_stack_dom pt MB1 MB2 sp0 96); [ | exact Hst1 ].
      intros x Hx. unfold MB2. apply uM_store8_is_Some. exact Hx. }
    assert (Honly2 : uM_only M MB2 (uint sp0 - 96) 96)
      by (unfold MB2; apply only_step8; [ lia | lia | exact Honly1 ]).
    (* ---- 0xab0  c.sdsp s1_idx,72(sp) ---- *)
    iApply (wp_sh_spill CIDs2 Psh 0xab0 0xab2 96 72 (mword_of_int 9 : mword 6)
              s1_idx MB2 m1 sp0 Hst2 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_ab0 pt MB2 Hl Htext2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs3) "Hcg Hpc".
    set (MB3 := uM_store8 MB2 (uint sp0 - 96 + 72) (m1 !!! Regidx s1_idx)).
    assert (Htext3 : sh_text_sub MB3)
      by (unfold MB3; apply sh_text_sub_store8'; [ exact Htext2 | lia ]).
    assert (Hst3 : uv_stack pt MB3 sp0 96).
    { apply (uv_stack_dom pt MB2 MB3 sp0 96); [ | exact Hst2 ].
      intros x Hx. unfold MB3. apply uM_store8_is_Some. exact Hx. }
    assert (Honly3 : uM_only M MB3 (uint sp0 - 96) 96)
      by (unfold MB3; apply only_step8; [ lia | lia | exact Honly2 ]).
    (* ---- 0xab2  c.sdsp s2_idx,64(sp) ---- *)
    iApply (wp_sh_spill CIDs3 Psh 0xab2 0xab4 96 64 (mword_of_int 8 : mword 6)
              s2_idx MB3 m1 sp0 Hst3 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_ab2 pt MB3 Hl Htext3)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs4) "Hcg Hpc".
    set (MB4 := uM_store8 MB3 (uint sp0 - 96 + 64) (m1 !!! Regidx s2_idx)).
    assert (Htext4 : sh_text_sub MB4)
      by (unfold MB4; apply sh_text_sub_store8'; [ exact Htext3 | lia ]).
    assert (Hst4 : uv_stack pt MB4 sp0 96).
    { apply (uv_stack_dom pt MB3 MB4 sp0 96); [ | exact Hst3 ].
      intros x Hx. unfold MB4. apply uM_store8_is_Some. exact Hx. }
    assert (Honly4 : uM_only M MB4 (uint sp0 - 96) 96)
      by (unfold MB4; apply only_step8; [ lia | lia | exact Honly3 ]).
    (* ---- 0xab4  c.sdsp s3_idx,56(sp) ---- *)
    iApply (wp_sh_spill CIDs4 Psh 0xab4 0xab6 96 56 (mword_of_int 7 : mword 6)
              s3_idx MB4 m1 sp0 Hst4 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_ab4 pt MB4 Hl Htext4)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs5) "Hcg Hpc".
    set (MB5 := uM_store8 MB4 (uint sp0 - 96 + 56) (m1 !!! Regidx s3_idx)).
    assert (Htext5 : sh_text_sub MB5)
      by (unfold MB5; apply sh_text_sub_store8'; [ exact Htext4 | lia ]).
    assert (Hst5 : uv_stack pt MB5 sp0 96).
    { apply (uv_stack_dom pt MB4 MB5 sp0 96); [ | exact Hst4 ].
      intros x Hx. unfold MB5. apply uM_store8_is_Some. exact Hx. }
    assert (Honly5 : uM_only M MB5 (uint sp0 - 96) 96)
      by (unfold MB5; apply only_step8; [ lia | lia | exact Honly4 ]).
    (* ---- 0xab6  c.sdsp s4_idx,48(sp) ---- *)
    iApply (wp_sh_spill CIDs5 Psh 0xab6 0xab8 96 48 (mword_of_int 6 : mword 6)
              s4_idx MB5 m1 sp0 Hst5 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_ab6 pt MB5 Hl Htext5)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs6) "Hcg Hpc".
    set (MB6 := uM_store8 MB5 (uint sp0 - 96 + 48) (m1 !!! Regidx s4_idx)).
    assert (Htext6 : sh_text_sub MB6)
      by (unfold MB6; apply sh_text_sub_store8'; [ exact Htext5 | lia ]).
    assert (Hst6 : uv_stack pt MB6 sp0 96).
    { apply (uv_stack_dom pt MB5 MB6 sp0 96); [ | exact Hst5 ].
      intros x Hx. unfold MB6. apply uM_store8_is_Some. exact Hx. }
    assert (Honly6 : uM_only M MB6 (uint sp0 - 96) 96)
      by (unfold MB6; apply only_step8; [ lia | lia | exact Honly5 ]).
    (* ---- 0xab8  c.sdsp s5_idx,40(sp) ---- *)
    iApply (wp_sh_spill CIDs6 Psh 0xab8 0xaba 96 40 (mword_of_int 5 : mword 6)
              s5_idx MB6 m1 sp0 Hst6 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_ab8 pt MB6 Hl Htext6)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs7) "Hcg Hpc".
    set (MB7 := uM_store8 MB6 (uint sp0 - 96 + 40) (m1 !!! Regidx s5_idx)).
    assert (Htext7 : sh_text_sub MB7)
      by (unfold MB7; apply sh_text_sub_store8'; [ exact Htext6 | lia ]).
    assert (Hst7 : uv_stack pt MB7 sp0 96).
    { apply (uv_stack_dom pt MB6 MB7 sp0 96); [ | exact Hst6 ].
      intros x Hx. unfold MB7. apply uM_store8_is_Some. exact Hx. }
    assert (Honly7 : uM_only M MB7 (uint sp0 - 96) 96)
      by (unfold MB7; apply only_step8; [ lia | lia | exact Honly6 ]).
    (* ---- 0xaba  c.sdsp s6_idx,32(sp) ---- *)
    iApply (wp_sh_spill CIDs7 Psh 0xaba 0xabc 96 32 (mword_of_int 4 : mword 6)
              s6_idx MB7 m1 sp0 Hst7 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_aba pt MB7 Hl Htext7)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs8) "Hcg Hpc".
    set (MB8 := uM_store8 MB7 (uint sp0 - 96 + 32) (m1 !!! Regidx s6_idx)).
    assert (Htext8 : sh_text_sub MB8)
      by (unfold MB8; apply sh_text_sub_store8'; [ exact Htext7 | lia ]).
    assert (Hst8 : uv_stack pt MB8 sp0 96).
    { apply (uv_stack_dom pt MB7 MB8 sp0 96); [ | exact Hst7 ].
      intros x Hx. unfold MB8. apply uM_store8_is_Some. exact Hx. }
    assert (Honly8 : uM_only M MB8 (uint sp0 - 96) 96)
      by (unfold MB8; apply only_step8; [ lia | lia | exact Honly7 ]).
    (* ---- 0xabc  c.sdsp s7_idx,24(sp) ---- *)
    iApply (wp_sh_spill CIDs8 Psh 0xabc 0xabe 96 24 (mword_of_int 3 : mword 6)
              s7_idx MB8 m1 sp0 Hst8 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_abc pt MB8 Hl Htext8)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs9) "Hcg Hpc".
    set (MB9 := uM_store8 MB8 (uint sp0 - 96 + 24) (m1 !!! Regidx s7_idx)).
    assert (Htext9 : sh_text_sub MB9)
      by (unfold MB9; apply sh_text_sub_store8'; [ exact Htext8 | lia ]).
    assert (Hst9 : uv_stack pt MB9 sp0 96).
    { apply (uv_stack_dom pt MB8 MB9 sp0 96); [ | exact Hst8 ].
      intros x Hx. unfold MB9. apply uM_store8_is_Some. exact Hx. }
    assert (Honly9 : uM_only M MB9 (uint sp0 - 96) 96)
      by (unfold MB9; apply only_step8; [ lia | lia | exact Honly8 ]).
    (* ---- 0xabe  c.sdsp s8_idx,16(sp) ---- *)
    iApply (wp_sh_spill CIDs9 Psh 0xabe 0xac0 96 16 (mword_of_int 2 : mword 6)
              s8_idx MB9 m1 sp0 Hst9 Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_abe pt MB9 Hl Htext9)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDs10) "Hcg Hpc".
    set (MB10 := uM_store8 MB9 (uint sp0 - 96 + 16) (m1 !!! Regidx s8_idx)).
    assert (Htext10 : sh_text_sub MB10)
      by (unfold MB10; apply sh_text_sub_store8'; [ exact Htext9 | lia ]).
    assert (Hst10 : uv_stack pt MB10 sp0 96).
    { apply (uv_stack_dom pt MB9 MB10 sp0 96); [ | exact Hst9 ].
      intros x Hx. unfold MB10. apply uM_store8_is_Some. exact Hx. }
    assert (Honly10 : uM_only M MB10 (uint sp0 - 96) 96)
      by (unfold MB10; apply only_step8; [ lia | lia | exact Honly9 ]).
    (* ---- 0xac0  c.addi4spn s0,sp,96 ---- *)
    assert (Hi4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   : mword 64) = mword_of_int 96)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hs0w : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))).
    { rewrite Hsp1 Hi4 moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh MB10 m1 (mword_of_int 0xac0)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_ac0 pt MB10 Hl Htext10)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hs0w
              with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (Eac0 : add_vec_int (mword_of_int 0xac0 : mword 64) 2
                   = mword_of_int 0xac2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eac0) in "Hpc".
    (* ---- 0xac2  c.mv s7,a0 ---- *)
    assert (Hm2a0 : m2 !!! Regidx a0_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Hbufa. }
    assert (Hw7 : (mword_of_int buf : mword 64)
                  = add_vec zero_reg (m2 !!! Regidx a0_idx))
      by (rewrite Hm2a0 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB10 m2 (mword_of_int 0xac2)
              s7_idx a0_idx (mword_of_int buf)
              (ui_sh_ac2 pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hw7 with "Hcg Hpc").
    iIntros (CIDp3) "Hcg Hpc".
    set (m3 := <[Regidx s7_idx
                 := regval_into_reg (mword_of_int buf : mword 64)]> m2).
    assert (Eac2 : add_vec_int (mword_of_int 0xac2 : mword 64) 2
                   = mword_of_int 0xac4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eac2) in "Hpc".
    (* ---- 0xac4  c.mv s4,a1 ---- *)
    assert (Hm3a1 : m3 !!! Regidx a1_idx = (mword_of_int max : mword 64)).
    { rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Hmaxa. }
    assert (Hw4 : (mword_of_int max : mword 64)
                  = add_vec zero_reg (m3 !!! Regidx a1_idx))
      by (rewrite Hm3a1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB10 m3 (mword_of_int 0xac4)
              s4_idx a1_idx (mword_of_int max)
              (ui_sh_ac4 pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hw4 with "Hcg Hpc").
    iIntros (CIDp4) "Hcg Hpc".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int max : mword 64)]> m3).
    assert (Eac4 : add_vec_int (mword_of_int 0xac4 : mword 64) 2
                   = mword_of_int 0xac6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eac4) in "Hpc".
    (* ---- 0xac6  c.mv s2,a0 ---- *)
    assert (Hm4a0 : m4 !!! Regidx a0_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne m3 (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hm2a0. }
    assert (Hw2 : (mword_of_int buf : mword 64)
                  = add_vec zero_reg (m4 !!! Regidx a0_idx))
      by (rewrite Hm4a0 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB10 m4 (mword_of_int 0xac6)
              s2_idx a0_idx (mword_of_int buf)
              (ui_sh_ac6 pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hw2 with "Hcg Hpc").
    iIntros (CIDp5) "Hcg Hpc".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int buf : mword 64)]> m4).
    assert (Eac6 : add_vec_int (mword_of_int 0xac6 : mword 64) 2
                   = mword_of_int 0xac8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eac6) in "Hpc".
    (* ---- 0xac8  c.li s1,0 ---- *)
    assert (Hwli0 : (mword_of_int 0 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MB10 m5 (mword_of_int 0xac8)
              (mword_of_int 0 : mword 6) s1_idx (mword_of_int 0 : mword 64)
              (ui_sh_ac8 pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hwli0 with "Hcg Hpc").
    iIntros (CIDp6) "Hcg Hpc".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m5).
    assert (Eac8 : add_vec_int (mword_of_int 0xac8 : mword 64) 2
                   = mword_of_int 0xaca)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eac8) in "Hpc".
    (* ---- 0xaca  addi s6,s0,-81 ---- *)
    assert (Hm6s0 : m6 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) _). }
    assert (Hm81' : (sign_extend' 64 (mword_of_int 4015 : mword 12) : mword 64)
                    = mword_of_int (-81))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hw6 : (mword_of_int (uint sp0 - 81) : mword 64)
                  = add_vec (m6 !!! Regidx s0_idx)
                      (sign_extend' 64 (mword_of_int 4015 : mword 12))).
    { rewrite Hm6s0 Hm81' moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh MB10 m6 (mword_of_int 0xaca)
              (mword_of_int 4015 : mword 12) s0_idx s6_idx
              (mword_of_int (uint sp0 - 81))
              (ui_sh_aca pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hw6 with "Hcg Hpc").
    iIntros (CIDp7) "Hcg Hpc".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 81) : mword 64)]> m6).
    assert (Eaca : add_vec_int (mword_of_int 0xaca : mword 64) 4
                   = mword_of_int 0xace)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eaca) in "Hpc".
    (* ---- 0xace  c.li s5,1 ---- *)
    assert (Hwli1 : (mword_of_int 1 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MB10 m7 (mword_of_int 0xace)
              (mword_of_int 1 : mword 6) s5_idx (mword_of_int 1 : mword 64)
              (ui_sh_ace pt MB10 Hl Htext10)
              ltac:(vm_compute; discriminate) Hwli1 with "Hcg Hpc").
    iIntros (CIDp8) "Hcg Hpc".
    set (m8 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m7).
    assert (Eace : add_vec_int (mword_of_int 0xace : mword 64) 2
                   = mword_of_int 0xad0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eace) in "Hpc".
    assert (Hb88 : uM_bytes MB10 (uint sp0 - 96 + 88) 8 (m1 !!! Regidx ra_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb80 : uM_bytes MB10 (uint sp0 - 96 + 80) 8 (m1 !!! Regidx s0_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb72 : uM_bytes MB10 (uint sp0 - 96 + 72) 8 (m1 !!! Regidx s1_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb64 : uM_bytes MB10 (uint sp0 - 96 + 64) 8 (m1 !!! Regidx s2_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb56 : uM_bytes MB10 (uint sp0 - 96 + 56) 8 (m1 !!! Regidx s3_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb48 : uM_bytes MB10 (uint sp0 - 96 + 48) 8 (m1 !!! Regidx s4_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb40 : uM_bytes MB10 (uint sp0 - 96 + 40) 8 (m1 !!! Regidx s5_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb32 : uM_bytes MB10 (uint sp0 - 96 + 32) 8 (m1 !!! Regidx s6_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb24 : uM_bytes MB10 (uint sp0 - 96 + 24) 8 (m1 !!! Regidx s7_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hb16 : uM_bytes MB10 (uint sp0 - 96 + 16) 8 (m1 !!! Regidx s8_idx)).
    { unfold MB10, MB9, MB8, MB7, MB6, MB5, MB4, MB3, MB2, MB1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hm8sp : m8 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 96) : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) _).
    }
    assert (Hm8s0 : m8 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) _).
    }
    assert (Hm8s7 : m8 !!! Regidx s7_idx = (mword_of_int buf : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s7_idx) _).
    }
    assert (Hm8s4 : m8 !!! Regidx s4_idx = (mword_of_int max : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s4_idx) _).
    }
    assert (Hm8s1 : m8 !!! Regidx s1_idx = (mword_of_int 0 : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s1_idx) _).
    }
    assert (Hm8s6 : m8 !!! Regidx s6_idx = (mword_of_int (uint sp0 - 81) : mword 64)).
    {
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s6_idx) _).
    }
    assert (Hm8s5 : m8 !!! Regidx s5_idx = (mword_of_int 1 : mword 64)).
    {
      exact (upd_eq m7 (Regidx s5_idx) _).
    }
    assert (Hm8s2 : m8 !!! Regidx s2_idx
                    = (mword_of_int (buf + Z.of_nat 0) : mword 64)).
    {
      replace (buf + Z.of_nat 0) with buf by lia.
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx) _).
    }
    assert (Hm8pres : forall r : mword 5,
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s4_idx -> Regidx r <> Regidx s5_idx ->
              Regidx r <> Regidx s6_idx -> Regidx r <> Regidx s7_idx ->
              m8 !!! Regidx r = m !!! Regidx r).
    { intros r Ncsp_rs1 Ns0_idx Ns1_idx Ns2_idx Ns4_idx Ns5_idx Ns6_idx Ns7_idx.
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx r) _ Ns5_idx).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx r) _ Ns6_idx).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx r) _ Ns1_idx).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx r) _ Ns2_idx).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx r) _ Ns4_idx).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx r) _ Ns7_idx).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Ns0_idx).
      rewrite (upd_ne m (Regidx csp_rs1) (Regidx r) _ Ncsp_rs1).
      reflexivity. }
    (* ---- 0xad0..0xafe  the read loop ---- *)
    assert (HwrB : uv_wr pt MB10 buf max).
    { apply (uv_wr_dom pt M MB10 buf max); [ | exact Hwr ].
      exact (proj1 Honly10). }
    iApply (wp_sh_gets_loop (S (length taken)) CIDp8 MB10 MB10 m8 sp0 buf max
              taken rest 0%nat
              ltac:(lia) Hlay Htext10 Hst10 Hsphi Hbuflo HwrB Hdisj Htk
              Hfit1 Hfit2
              ltac:(destruct taken as [ | b0 tl ];
                    [ right; split; reflexivity | left; cbn [length]; lia ])
              (sh_io_win_refl MB10 buf (uint sp0 - 81))
              Hm8sp Hm8s0 Hm8s1 Hm8s2 Hm8s4 Hm8s5 Hm8s6
              with "Hcg Hin Hpc").
    iIntros (CIDL mL ML) "%HwinL %HLs8 %HLpres Hin Hcg Hpc".
    assert (HtextL : sh_text_sub ML)
      by exact (sh_io_win_text MB10 ML buf (uint sp0 - 81) taken Hbuflo
                  ltac:(lia) HwinL Htext10).
    pose proof HwinL as (HLin & HLout & HLdom).
    assert (HstL : uv_stack pt ML sp0 96)
      by exact (uv_stack_dom pt MB10 ML sp0 96 HLdom Hst10).
    assert (HwrL : uv_wr pt ML buf max)
      by exact (uv_wr_dom pt MB10 ML buf max HLdom HwrB).
    (* ---- 0xb00  c.add s8,s8,s7 ---- *)
    assert (HLs7 : mL !!! Regidx s7_idx = (mword_of_int buf : mword 64)).
    { rewrite (HLpres s7_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Hm8s7. }
    assert (Hadd8 : (mword_of_int (buf + Z.of_nat (length taken)) : mword 64)
                    = add_vec (mL !!! Regidx s8_idx) (mL !!! Regidx s7_idx)).
    { rewrite HLs8 HLs7 moi_add. f_equal; lia. }
    iApply (wp_uv_cadd C pt Psh ML mL (mword_of_int 0xb00)
              s8_idx s7_idx (mword_of_int (buf + Z.of_nat (length taken)))
              (ui_sh_b00 pt ML Hl HtextL)
              ltac:(vm_compute; discriminate) Hadd8 with "Hcg Hpc").
    iIntros (CIDN) "Hcg Hpc".
    set (mN := <[Regidx s8_idx
                 := regval_into_reg
                      (mword_of_int (buf + Z.of_nat (length taken)) : mword 64)]> mL).
    assert (Eb00 : add_vec_int (mword_of_int 0xb00 : mword 64) 2
                   = mword_of_int 0xb02)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb00) in "Hpc".
    (* ---- 0xb02  sb zero,0(s8) ---- *)
    iDestruct "Hcg" as "(#Hcapz & Hlinz & Hgprz)".
    iDestruct (gpr_file_x0 mN x0_idx ltac:(vm_compute; reflexivity) with "Hgprz")
      as "[%Hx0 Hgprz]".
    iAssert (uv_cap_gpr (CID := CIDN) C pt Psh ML mN) with "[Hlinz Hgprz]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcapz Hlinz Hgprz". }
    assert (HNs8 : mN !!! Regidx s8_idx
                   = (mword_of_int (buf + Z.of_nat (length taken)) : mword 64))
      by exact (upd_eq mL (Regidx s8_idx) _).
    assert (Hz0' : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hvanul : (mword_of_int (buf + Z.of_nat (length taken)) : mword 64)
                     = add_vec (mN !!! Regidx s8_idx)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HNs8 Hz0' moi_add. f_equal; lia. }
    destruct (uwr_leaf _ _ _ _ HwrL (Z.of_nat (length taken)) ltac:(lia))
      as (wnl & Hwnll & Hwnlok).
    assert (Huvn : uint (mword_of_int (buf + Z.of_nat (length taken)) : mword 64)
                   = buf + Z.of_nat (length taken))
      by (apply uint_moi; unfold Z64; lia).
    assert (Hcannul : uva_canon
                        (mword_of_int (buf + Z.of_nat (length taken)) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    destruct (uwr_bytes _ _ _ _ HwrL (Z.of_nat (length taken)) ltac:(lia))
      as (bon & Hbon).
    assert (Hbon' : ML !! (uint (mword_of_int (buf + Z.of_nat (length taken))
                                 : mword 64)) = Some bon)
      by (rewrite Huvn; exact Hbon).
    iApply (wp_uv_sb C pt Psh ML mN (mword_of_int 0xb02)
              (mword_of_int 0 : mword 12) s8_idx x0_idx
              wnl (mword_of_int (buf + Z.of_nat (length taken)))
              (zero_reg : mword 64) bon
              (ui_sh_b02 pt ML Hl HtextL)
              Hvanul (eq_sym Hx0) Hwnll Hwnlok Hcannul Hbon'
              with "Hcg Hpc").
    iIntros (CIDF) "Hcg Hpc".
    iEval (rewrite Huvn) in "Hcg".
    set (M2f := uM_store ML (buf + Z.of_nat (length taken)) 1 (zero_reg : mword 64)).
    assert (Eb02 : add_vec_int (mword_of_int 0xb02 : mword 64) 4
                   = mword_of_int 0xb06)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb02) in "Hpc".
    assert (Hwin2f : sh_io_win MB10 M2f buf (uint sp0 - 81) (taken ++ [ubyte0])).
    { unfold M2f.
      exact (sh_io_win_sb MB10 ML buf (uint sp0 - 81) taken ubyte0
               (zero_reg : mword 64) nth_byte0_zero HwinL). }
    assert (Htext2f : sh_text_sub M2f)
      by exact (sh_io_win_text MB10 M2f buf (uint sp0 - 81) (taken ++ [ubyte0])
                  Hbuflo ltac:(lia) Hwin2f Htext10).
    pose proof Hwin2f as (H2in & H2out & H2dom).
    assert (Hst2f : uv_stack pt M2f sp0 96)
      by exact (uv_stack_dom pt MB10 M2f sp0 96 H2dom Hst10).
    (* ---- 0xb06  c.mv a0,s7 ---- *)
    assert (HNs7 : mN !!! Regidx s7_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne mL (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact HLs7. }
    assert (Hwa0 : (mword_of_int buf : mword 64)
                   = add_vec zero_reg (mN !!! Regidx s7_idx))
      by (rewrite HNs7 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M2f mN (mword_of_int 0xb06)
              a0_idx s7_idx (mword_of_int buf)
              (ui_sh_b06 pt M2f Hl Htext2f)
              ltac:(vm_compute; discriminate) Hwa0 with "Hcg Hpc").
    iIntros (CIDe0) "Hcg Hpc".
    set (mE0 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int buf : mword 64)]> mN).
    assert (Eb06 : add_vec_int (mword_of_int 0xb06 : mword 64) 2
                   = mword_of_int 0xb08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb06) in "Hpc".
    assert (HspE0 : mE0 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mN (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mL (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (HLpres csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Hm8sp. }
    (* the frame slots survive: the loop only moved [buf..] and sp0-81 ---- *)
    assert (Hfrsurv : forall k : Z, uint sp0 - 96 + 16 <= k < uint sp0 - 96 + 96 ->
              M2f !! k = MB10 !! k).
    { intros k Hk. apply H2out; [ | lia ].
      rewrite length_app. cbn [length]. destruct Hdisj as [ Hd | Hd ]; lia. }
    assert (Hby88 : uM_bytes M2f (uint sp0 - 96 + 88) 8 (m1 !!! Regidx ra_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 88) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb88).
    assert (Hby80 : uM_bytes M2f (uint sp0 - 96 + 80) 8 (m1 !!! Regidx s0_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 80) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb80).
    assert (Hby72 : uM_bytes M2f (uint sp0 - 96 + 72) 8 (m1 !!! Regidx s1_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 72) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb72).
    assert (Hby64 : uM_bytes M2f (uint sp0 - 96 + 64) 8 (m1 !!! Regidx s2_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 64) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb64).
    assert (Hby56 : uM_bytes M2f (uint sp0 - 96 + 56) 8 (m1 !!! Regidx s3_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 56) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb56).
    assert (Hby48 : uM_bytes M2f (uint sp0 - 96 + 48) 8 (m1 !!! Regidx s4_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 48) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb48).
    assert (Hby40 : uM_bytes M2f (uint sp0 - 96 + 40) 8 (m1 !!! Regidx s5_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 40) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb40).
    assert (Hby32 : uM_bytes M2f (uint sp0 - 96 + 32) 8 (m1 !!! Regidx s6_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 32) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb32).
    assert (Hby24 : uM_bytes M2f (uint sp0 - 96 + 24) 8 (m1 !!! Regidx s7_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 24) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb24).
    assert (Hby16 : uM_bytes M2f (uint sp0 - 96 + 16) 8 (m1 !!! Regidx s8_idx))
      by exact (bytes_win MB10 M2f (uint sp0 - 96 + 16) _
                  ltac:(intros k Hk; apply Hfrsurv; lia) Hb16).
    (* ---- 0xb08  c.ldsp ra_idx,88(sp) ---- *)
    iApply (wp_sh_reload CIDe0 Psh 0xb08 0xb0a 96 88 (mword_of_int 11 : mword 6)
              ra_idx (m1 !!! Regidx ra_idx) M2f mE0 sp0
              Hst2f HspE0
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby88
              (ui_sh_b08 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe1) "Hcg Hpc".
    set (mE1 := <[Regidx ra_idx := regval_into_reg (m1 !!! Regidx ra_idx)]> mE0).
    assert (HspE1 : mE1 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE0 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE0. }
    (* ---- 0xb0a  c.ldsp s0_idx,80(sp) ---- *)
    iApply (wp_sh_reload CIDe1 Psh 0xb0a 0xb0c 96 80 (mword_of_int 10 : mword 6)
              s0_idx (m1 !!! Regidx s0_idx) M2f mE1 sp0
              Hst2f HspE1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby80
              (ui_sh_b0a pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe2) "Hcg Hpc".
    set (mE2 := <[Regidx s0_idx := regval_into_reg (m1 !!! Regidx s0_idx)]> mE1).
    assert (HspE2 : mE2 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE1. }
    (* ---- 0xb0c  c.ldsp s1_idx,72(sp) ---- *)
    iApply (wp_sh_reload CIDe2 Psh 0xb0c 0xb0e 96 72 (mword_of_int 9 : mword 6)
              s1_idx (m1 !!! Regidx s1_idx) M2f mE2 sp0
              Hst2f HspE2
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby72
              (ui_sh_b0c pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe3) "Hcg Hpc".
    set (mE3 := <[Regidx s1_idx := regval_into_reg (m1 !!! Regidx s1_idx)]> mE2).
    assert (HspE3 : mE3 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE2. }
    (* ---- 0xb0e  c.ldsp s2_idx,64(sp) ---- *)
    iApply (wp_sh_reload CIDe3 Psh 0xb0e 0xb10 96 64 (mword_of_int 8 : mword 6)
              s2_idx (m1 !!! Regidx s2_idx) M2f mE3 sp0
              Hst2f HspE3
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby64
              (ui_sh_b0e pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe4) "Hcg Hpc".
    set (mE4 := <[Regidx s2_idx := regval_into_reg (m1 !!! Regidx s2_idx)]> mE3).
    assert (HspE4 : mE4 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE3. }
    (* ---- 0xb10  c.ldsp s3_idx,56(sp) ---- *)
    iApply (wp_sh_reload CIDe4 Psh 0xb10 0xb12 96 56 (mword_of_int 7 : mword 6)
              s3_idx (m1 !!! Regidx s3_idx) M2f mE4 sp0
              Hst2f HspE4
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby56
              (ui_sh_b10 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe5) "Hcg Hpc".
    set (mE5 := <[Regidx s3_idx := regval_into_reg (m1 !!! Regidx s3_idx)]> mE4).
    assert (HspE5 : mE5 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE4. }
    (* ---- 0xb12  c.ldsp s4_idx,48(sp) ---- *)
    iApply (wp_sh_reload CIDe5 Psh 0xb12 0xb14 96 48 (mword_of_int 6 : mword 6)
              s4_idx (m1 !!! Regidx s4_idx) M2f mE5 sp0
              Hst2f HspE5
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby48
              (ui_sh_b12 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe6) "Hcg Hpc".
    set (mE6 := <[Regidx s4_idx := regval_into_reg (m1 !!! Regidx s4_idx)]> mE5).
    assert (HspE6 : mE6 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE5. }
    (* ---- 0xb14  c.ldsp s5_idx,40(sp) ---- *)
    iApply (wp_sh_reload CIDe6 Psh 0xb14 0xb16 96 40 (mword_of_int 5 : mword 6)
              s5_idx (m1 !!! Regidx s5_idx) M2f mE6 sp0
              Hst2f HspE6
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby40
              (ui_sh_b14 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe7) "Hcg Hpc".
    set (mE7 := <[Regidx s5_idx := regval_into_reg (m1 !!! Regidx s5_idx)]> mE6).
    assert (HspE7 : mE7 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE6. }
    (* ---- 0xb16  c.ldsp s6_idx,32(sp) ---- *)
    iApply (wp_sh_reload CIDe7 Psh 0xb16 0xb18 96 32 (mword_of_int 4 : mword 6)
              s6_idx (m1 !!! Regidx s6_idx) M2f mE7 sp0
              Hst2f HspE7
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby32
              (ui_sh_b16 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe8) "Hcg Hpc".
    set (mE8 := <[Regidx s6_idx := regval_into_reg (m1 !!! Regidx s6_idx)]> mE7).
    assert (HspE8 : mE8 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE7. }
    (* ---- 0xb18  c.ldsp s7_idx,24(sp) ---- *)
    iApply (wp_sh_reload CIDe8 Psh 0xb18 0xb1a 96 24 (mword_of_int 3 : mword 6)
              s7_idx (m1 !!! Regidx s7_idx) M2f mE8 sp0
              Hst2f HspE8
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby24
              (ui_sh_b18 pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe9) "Hcg Hpc".
    set (mE9 := <[Regidx s7_idx := regval_into_reg (m1 !!! Regidx s7_idx)]> mE8).
    assert (HspE9 : mE9 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE8. }
    (* ---- 0xb1a  c.ldsp s8_idx,16(sp) ---- *)
    iApply (wp_sh_reload CIDe9 Psh 0xb1a 0xb1c 96 16 (mword_of_int 2 : mword 6)
              s8_idx (m1 !!! Regidx s8_idx) M2f mE9 sp0
              Hst2f HspE9
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hby16
              (ui_sh_b1a pt M2f Hl Htext2f)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe10) "Hcg Hpc".
    set (mE10 := <[Regidx s8_idx := regval_into_reg (m1 !!! Regidx s8_idx)]> mE9).
    assert (HspE10 : mE10 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 96) : mword 64)).
    { rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HspE9. }
    assert (Hresra_idx : mE10 !!! Regidx ra_idx = m1 !!! Regidx ra_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE0 (Regidx ra_idx) _).
    }
    assert (Hress0_idx : mE10 !!! Regidx s0_idx = m1 !!! Regidx s0_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE1 (Regidx s0_idx) _).
    }
    assert (Hress1_idx : mE10 !!! Regidx s1_idx = m1 !!! Regidx s1_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE2 (Regidx s1_idx) _).
    }
    assert (Hress2_idx : mE10 !!! Regidx s2_idx = m1 !!! Regidx s2_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE3 (Regidx s2_idx) _).
    }
    assert (Hress3_idx : mE10 !!! Regidx s3_idx = m1 !!! Regidx s3_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE4 (Regidx s3_idx) _).
    }
    assert (Hress4_idx : mE10 !!! Regidx s4_idx = m1 !!! Regidx s4_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE5 (Regidx s4_idx) _).
    }
    assert (Hress5_idx : mE10 !!! Regidx s5_idx = m1 !!! Regidx s5_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE6 (Regidx s5_idx) _).
    }
    assert (Hress6_idx : mE10 !!! Regidx s6_idx = m1 !!! Regidx s6_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE7 (Regidx s6_idx) _).
    }
    assert (Hress7_idx : mE10 !!! Regidx s7_idx = m1 !!! Regidx s7_idx).
    {
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mE8 (Regidx s7_idx) _).
    }
    assert (Hress8_idx : mE10 !!! Regidx s8_idx = m1 !!! Regidx s8_idx).
    {
      exact (upd_eq mE9 (Regidx s8_idx) _).
    }
    assert (HpresE : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s6_idx ->
              Regidx r <> Regidx s7_idx -> Regidx r <> Regidx s8_idx ->
              mE10 !!! Regidx r = mE0 !!! Regidx r).
    { intros r Nra_idx Ns0_idx Ns1_idx Ns2_idx Ns3_idx Ns4_idx Ns5_idx Ns6_idx
             Ns7_idx Ns8_idx.
      rewrite (upd_ne mE9 (Regidx s8_idx) (Regidx r) _ Ns8_idx).
      rewrite (upd_ne mE8 (Regidx s7_idx) (Regidx r) _ Ns7_idx).
      rewrite (upd_ne mE7 (Regidx s6_idx) (Regidx r) _ Ns6_idx).
      rewrite (upd_ne mE6 (Regidx s5_idx) (Regidx r) _ Ns5_idx).
      rewrite (upd_ne mE5 (Regidx s4_idx) (Regidx r) _ Ns4_idx).
      rewrite (upd_ne mE4 (Regidx s3_idx) (Regidx r) _ Ns3_idx).
      rewrite (upd_ne mE3 (Regidx s2_idx) (Regidx r) _ Ns2_idx).
      rewrite (upd_ne mE2 (Regidx s1_idx) (Regidx r) _ Ns1_idx).
      rewrite (upd_ne mE1 (Regidx s0_idx) (Regidx r) _ Ns0_idx).
      rewrite (upd_ne mE0 (Regidx ra_idx) (Regidx r) _ Nra_idx).
      reflexivity. }
    (* ---- 0xb1c  c.addi16sp sp,sp,96 ---- *)
    assert (Hi16b : (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                     : mword 64) = mword_of_int 96)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hspback : sp0 = add_vec (mE10 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))).
    { rewrite HspE10 Hi16b moi_add.
      replace (uint sp0 - 96 + 96) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh M2f mE10 (mword_of_int 0xb1c)
              (mword_of_int 6 : mword 6) sp0
              (ui_sh_b1c pt M2f Hl Htext2f) Hspback with "Hcg Hpc").
    iIntros (CIDe11) "Hcg Hpc".
    set (mF := <[Regidx csp_rs1 := regval_into_reg (sp0 : mword 64)]> mE10).
    assert (Eb1c : add_vec_int (mword_of_int 0xb1c : mword 64) 2
                   = mword_of_int 0xb1e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb1c) in "Hpc".
    assert (HFpres : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              mF !!! Regidx r = mE10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne mE10 (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xb1e  c.jr ra ---- *)
    assert (HFra : mF !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (HFpres ra_idx ltac:(vm_compute; discriminate)).
      rewrite Hresra_idx. exact (Hm1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtret : (m !!! Regidx ra_idx) = ret_pc (mF !!! Regidx ra_idx)).
    { rewrite HFra. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M2f mF (mword_of_int 0xb1e)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_b1e pt M2f Hl Htext2f)
              ltac:(vm_compute; discriminate) Htgtret with "Hcg Hpc").
    iIntros (CIDz) "Hcg Hpc".
    iApply ("Hcont" $! CIDz mF M2f with "[] [] [] [] Hin Hcg Hpc").
    - (* ---- ucallee_saved ---- *)
      iPureIntro. intros r Hr.
      destruct (decide (Regidx r = Regidx csp_rs1)) as [ Esp | Nsp ].
      { rewrite Esp. rewrite (upd_eq mE10 (Regidx csp_rs1)
                                (regval_into_reg (sp0 : mword 64))).
        symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | N0 ].
      { rewrite E0 (HFpres s0_idx ltac:(vm_compute; discriminate)) Hress0_idx.
        exact (Hm1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | N1 ].
      { rewrite E1 (HFpres s1_idx ltac:(vm_compute; discriminate)) Hress1_idx.
        exact (Hm1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ E2 | N2 ].
      { rewrite E2 (HFpres s2_idx ltac:(vm_compute; discriminate)) Hress2_idx.
        exact (Hm1 s2_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s3_idx)) as [ E3 | N3 ].
      { rewrite E3 (HFpres s3_idx ltac:(vm_compute; discriminate)) Hress3_idx.
        exact (Hm1 s3_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s4_idx)) as [ E4 | N4 ].
      { rewrite E4 (HFpres s4_idx ltac:(vm_compute; discriminate)) Hress4_idx.
        exact (Hm1 s4_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s5_idx)) as [ E5 | N5 ].
      { rewrite E5 (HFpres s5_idx ltac:(vm_compute; discriminate)) Hress5_idx.
        exact (Hm1 s5_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s6_idx)) as [ E6 | N6 ].
      { rewrite E6 (HFpres s6_idx ltac:(vm_compute; discriminate)) Hress6_idx.
        exact (Hm1 s6_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s7_idx)) as [ E7 | N7 ].
      { rewrite E7 (HFpres s7_idx ltac:(vm_compute; discriminate)) Hress7_idx.
        exact (Hm1 s7_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s8_idx)) as [ E8 | N8 ].
      { rewrite E8 (HFpres s8_idx ltac:(vm_compute; discriminate)) Hress8_idx.
        exact (Hm1 s8_idx ltac:(vm_compute; discriminate)). }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HFpres r Nsp).
      rewrite (HpresE r Nra N0 N1 N2 N3 N4 N5 N6 N7 N8).
      rewrite (upd_ne mN (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne mL (Regidx s8_idx) (Regidx r) _ N8).
      rewrite (HLpres r Hr N1 N2 N3 N8).
      exact (Hm8pres r Nsp N0 N1 N2 N4 N5 N6 N7).
    - (* ---- a0 = buf ---- *)
      iPureIntro.
      rewrite (HFpres a0_idx ltac:(vm_compute; discriminate)).
      rewrite (HpresE a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mN (Regidx a0_idx)
               (regval_into_reg (mword_of_int buf : mword 64))).
    - (* ---- the line, NUL-terminated, at [buf] ---- *)
      iPureIntro. split.
      + intros j b Hj. apply H2in.
        rewrite (lookup_app_l taken [ubyte0] j
                   ltac:(pose proof (lookup_lt_Some taken j b Hj); lia)).
        exact Hj.
      + apply H2in.
        rewrite (lookup_app_r taken [ubyte0] (length taken) ltac:(lia)).
        rewrite Nat.sub_diag. reflexivity.
    - (* ---- and NOTHING outside the buffer and gets' own frame moved ---- *)
      iPureIntro. unfold sh_win. split.
      + intros k Hk. exact (H2dom k (proj1 Honly10 k Hk)).
      + intros k Hk.
        assert (Hk1 : k < buf \/ buf + (Z.of_nat (length taken) + 1) <= k).
        { destruct (Z.lt_ge_cases k buf) as [ Ha | Ha ]; [ left; lia | ].
          destruct (Z.lt_ge_cases k (buf + (Z.of_nat (length taken) + 1)))
            as [ Hb | Hb ];
            [ exfalso; apply Hk; apply in_win2; left; lia | right; lia ]. }
        assert (Hk2 : k < uint sp0 - 96 \/ uint sp0 - 96 + 96 <= k).
        { destruct (Z.lt_ge_cases k (uint sp0 - 96)) as [ Ha | Ha ];
            [ left; lia | ].
          destruct (Z.lt_ge_cases k (uint sp0 - 96 + 96)) as [ Hb | Hb ];
            [ exfalso; apply Hk; apply in_win2; right; lia | right; lia ]. }
        rewrite (H2out k ltac:(rewrite length_app; cbn [length]; lia)
                   ltac:(lia)).
        exact (proj2 Honly10 k Hk2).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §5 getcmd @0x0 -- prompt, zero the buffer, gets, report EOF.          *)
  (*                                                                       *)
  (*   0..a   the 32-byte frame (ra,s0,s1,s2)     c..e  s1 = buf, s2 = nbuf *)
  (*   10..1c write(2, "$ ", 2)   -- the literal is at 0x1280, in .rodata   *)
  (*   20..26 memset(buf, 0, nbuf)                                          *)
  (*   2a..2e gets(buf, nbuf)                                               *)
  (*   32..3a lbu a0,0(s1); seqz a0,a0; negw a0,a0                          *)
  (*   3e..48 the frame back                                                *)
  (*                                                                       *)
  (* The 128 bytes [uM_only_in] names are getcmd's own 32 plus gets' 96;    *)
  (* memset's 16 and gets' read slot sit inside them.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_getcmd (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (buf nbuf : Z) (taken rest : list (bv 8)) :
    wp_sh_getcmd_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 buf nbuf
      taken rest.
  Proof.
    intros Hlay Himg Hsp Hst Hbufa Hnbufa Htk Hfit Hwr Hrdb Hfr Hbuflo Hnul
           Hdisj Hret2.
    destruct Hfit as (Hfit1 & Hfit2).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (sh_img_data M Himg) as Hdata.
    destruct sh_syms_pins as (_&_& Hsgetcmd & Hsgets & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & Hsmemset & _ & _ & _ &
                              _ & _ & _ & Hswrite & _).
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    unfold sh_frame_ok in Hfr.
    change (32 + 96) with 128 in Hst.
    assert (Hsphi : 12288 <= uint sp0 - 128) by lia.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    assert (Hfit2' : nbuf < 2 ^ 31) by exact Hfit2.
    change (2 ^ 31) with 2147483648 in Hfit2.
    pose proof (uwr_lo _ _ _ _ Hwr) as Hb0.
    pose proof (uwr_hi _ _ _ _ Hwr) as Hbhi.
    change (2 ^ 38) with 274877906944 in Hbhi.
    (* the two stack slices: getcmd's own frame, and everything below it *)
    destruct (uv_stack_split pt M sp0 128 32 96 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hst32 & Hst96r).
    rewrite (uv_stack_sp_moi pt M sp0 32 Hst32) in Hst96r.
    assert (Husp : uint (mword_of_int (uint sp0 - 32) : mword 64)
                   = uint sp0 - 32) by (apply uint_moi; unfold Z64; lia).
    destruct (uv_stack_split pt M (mword_of_int (uint sp0 - 32)) 96 16 80
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hst96r)
      as (Hst16r & _).
    assert (Honl0 : uM_only M M (uint sp0 - 32) 32) by (apply uM_only_refl).
    iIntros "Hcg Hin Hpc Hcont".
    iEval (rewrite Hsgetcmd) in "Hpc".
    (* ---- 0x0  c.addi sp,sp,-32 ---- *)
    assert (Hi32 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                    : mword 64) = mword_of_int (-32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hgspw : (mword_of_int (uint sp0 - 32) : mword 64)
                    = add_vec (m !!! Regidx sp_idx)
                        (sign_extend' 64
                           (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite Hsp Hi32 moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh M m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) sp_idx (mword_of_int (uint sp0 - 32))
              (ui_sh_00 pt M Hl Htext)
              ltac:(vm_compute; discriminate) Hgspw with "Hcg Hpc").
    iIntros (CIDg0) "Hcg Hpc".
    set (g1 := <[Regidx sp_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64)]> m).
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2 = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E00) in "Hpc".
    assert (Hgsp1 : g1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64))).
    assert (Hg1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              g1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx sp_idx) (Regidx r) _ Hr)).
    (* ---- 0x02  c.sdsp ra_idx,24(sp) ---- *)
    iApply (wp_sh_spill CIDg0 Psh 0x02 0x04 32 24 (mword_of_int 3 : mword 6)
              ra_idx M g1 sp0 Hst32 Hgsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_02 pt M Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDg1) "Hcg Hpc".
    set (MG1 := uM_store8 M (uint sp0 - 32 + 24) (g1 !!! Regidx ra_idx)).
    assert (Htxt1 : sh_text_sub MG1)
      by (unfold MG1; apply sh_text_sub_store8'; [ exact Htext | lia ]).
    assert (Hdat1 : sh_data_sub MG1)
      by (unfold MG1; apply sh_data_sub_store8'; [ exact Hdata | lia ]).
    assert (Hstk1 : uv_stack pt MG1 sp0 32).
    { apply (uv_stack_dom pt M MG1 sp0 32); [ | exact Hst32 ].
      intros x Hx. unfold MG1. apply uM_store8_is_Some. exact Hx. }
    assert (Honl1 : uM_only M MG1 (uint sp0 - 32) 32)
      by (unfold MG1; apply only_step8; [ lia | lia | exact Honl0 ]).
    (* ---- 0x04  c.sdsp s0_idx,16(sp) ---- *)
    iApply (wp_sh_spill CIDg1 Psh 0x04 0x06 32 16 (mword_of_int 2 : mword 6)
              s0_idx MG1 g1 sp0 Hstk1 Hgsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_04 pt MG1 Hl Htxt1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDg2) "Hcg Hpc".
    set (MG2 := uM_store8 MG1 (uint sp0 - 32 + 16) (g1 !!! Regidx s0_idx)).
    assert (Htxt2 : sh_text_sub MG2)
      by (unfold MG2; apply sh_text_sub_store8'; [ exact Htxt1 | lia ]).
    assert (Hdat2 : sh_data_sub MG2)
      by (unfold MG2; apply sh_data_sub_store8'; [ exact Hdat1 | lia ]).
    assert (Hstk2 : uv_stack pt MG2 sp0 32).
    { apply (uv_stack_dom pt MG1 MG2 sp0 32); [ | exact Hstk1 ].
      intros x Hx. unfold MG2. apply uM_store8_is_Some. exact Hx. }
    assert (Honl2 : uM_only M MG2 (uint sp0 - 32) 32)
      by (unfold MG2; apply only_step8; [ lia | lia | exact Honl1 ]).
    (* ---- 0x06  c.sdsp s1_idx,8(sp) ---- *)
    iApply (wp_sh_spill CIDg2 Psh 0x06 0x08 32 8 (mword_of_int 1 : mword 6)
              s1_idx MG2 g1 sp0 Hstk2 Hgsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_06 pt MG2 Hl Htxt2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDg3) "Hcg Hpc".
    set (MG3 := uM_store8 MG2 (uint sp0 - 32 + 8) (g1 !!! Regidx s1_idx)).
    assert (Htxt3 : sh_text_sub MG3)
      by (unfold MG3; apply sh_text_sub_store8'; [ exact Htxt2 | lia ]).
    assert (Hdat3 : sh_data_sub MG3)
      by (unfold MG3; apply sh_data_sub_store8'; [ exact Hdat2 | lia ]).
    assert (Hstk3 : uv_stack pt MG3 sp0 32).
    { apply (uv_stack_dom pt MG2 MG3 sp0 32); [ | exact Hstk2 ].
      intros x Hx. unfold MG3. apply uM_store8_is_Some. exact Hx. }
    assert (Honl3 : uM_only M MG3 (uint sp0 - 32) 32)
      by (unfold MG3; apply only_step8; [ lia | lia | exact Honl2 ]).
    (* ---- 0x08  c.sdsp s2_idx,0(sp) ---- *)
    iApply (wp_sh_spill CIDg3 Psh 0x08 0x0a 32 0 (mword_of_int 0 : mword 6)
              s2_idx MG3 g1 sp0 Hstk3 Hgsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_08 pt MG3 Hl Htxt3)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDg4) "Hcg Hpc".
    set (MG4 := uM_store8 MG3 (uint sp0 - 32 + 0) (g1 !!! Regidx s2_idx)).
    assert (Htxt4 : sh_text_sub MG4)
      by (unfold MG4; apply sh_text_sub_store8'; [ exact Htxt3 | lia ]).
    assert (Hdat4 : sh_data_sub MG4)
      by (unfold MG4; apply sh_data_sub_store8'; [ exact Hdat3 | lia ]).
    assert (Hstk4 : uv_stack pt MG4 sp0 32).
    { apply (uv_stack_dom pt MG3 MG4 sp0 32); [ | exact Hstk3 ].
      intros x Hx. unfold MG4. apply uM_store8_is_Some. exact Hx. }
    assert (Honl4 : uM_only M MG4 (uint sp0 - 32) 32)
      by (unfold MG4; apply only_step8; [ lia | lia | exact Honl3 ]).
    assert (Hgb24 : uM_bytes MG4 (uint sp0 - 32 + 24) 8 (g1 !!! Regidx ra_idx)).
    { unfold MG4, MG3, MG2, MG1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hgb16 : uM_bytes MG4 (uint sp0 - 32 + 16) 8 (g1 !!! Regidx s0_idx)).
    { unfold MG4, MG3, MG2, MG1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hgb8 : uM_bytes MG4 (uint sp0 - 32 + 8) 8 (g1 !!! Regidx s1_idx)).
    { unfold MG4, MG3, MG2, MG1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    assert (Hgb0 : uM_bytes MG4 (uint sp0 - 32 + 0) 8 (g1 !!! Regidx s2_idx)).
    { unfold MG4, MG3, MG2, MG1.
      repeat (apply store8_bytes_ne; [ lia | ]). apply uM_store8_bytes. }
    (* ---- 0xa  c.addi4spn s0,sp,32 ---- *)
    assert (Hgi4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                    : mword 64) = mword_of_int 32)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hgs0w : (mword_of_int (uint sp0) : mword 64)
                    = add_vec (g1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hgsp1 Hgi4 moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh MG4 g1 (mword_of_int 0xa)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_0a pt MG4 Hl Htxt4)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hgs0w
              with "Hcg Hpc").
    iIntros (CIDh0) "Hcg Hpc".
    set (g2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> g1).
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2 = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0a) in "Hpc".
    (* ---- 0xc  c.mv s1,a0 ---- *)
    assert (Hg2a0 : g2 !!! Regidx a0_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne g1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hg1 a0_idx ltac:(vm_compute; discriminate)). exact Hbufa. }
    assert (Hgw1 : (mword_of_int buf : mword 64)
                   = add_vec zero_reg (g2 !!! Regidx a0_idx))
      by (rewrite Hg2a0 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MG4 g2 (mword_of_int 0xc)
              s1_idx a0_idx (mword_of_int buf)
              (ui_sh_0c pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgw1 with "Hcg Hpc").
    iIntros (CIDh1) "Hcg Hpc".
    set (g3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int buf : mword 64)]> g2).
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2 = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0c) in "Hpc".
    (* ---- 0xe  c.mv s2,a1 ---- *)
    assert (Hg3a1 : g3 !!! Regidx a1_idx = (mword_of_int nbuf : mword 64)).
    { rewrite (upd_ne g2 (Regidx s1_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g1 (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hg1 a1_idx ltac:(vm_compute; discriminate)). exact Hnbufa. }
    assert (Hgw2 : (mword_of_int nbuf : mword 64)
                   = add_vec zero_reg (g3 !!! Regidx a1_idx))
      by (rewrite Hg3a1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MG4 g3 (mword_of_int 0xe)
              s2_idx a1_idx (mword_of_int nbuf)
              (ui_sh_0e pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgw2 with "Hcg Hpc").
    iIntros (CIDh2) "Hcg Hpc".
    set (g4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int nbuf : mword 64)]> g3).
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 2 = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0e) in "Hpc".
    (* ---- 0x10  c.li a2,2 ---- *)
    assert (Hgli2 : (mword_of_int 2 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MG4 g4 (mword_of_int 0x10)
              (mword_of_int 2 : mword 6) a2_idx (mword_of_int 2 : mword 64)
              (ui_sh_10 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgli2 with "Hcg Hpc").
    iIntros (CIDh3) "Hcg Hpc".
    set (g5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> g4).
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2 = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E10) in "Hpc".
    (* ---- 0x12  auipc a1,0x1 ---- *)
    assert (Hgauipc : (mword_of_int 4114 : mword 64)
                      = add_vec (mword_of_int 0x12)
                          (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh MG4 g5 (mword_of_int 0x12)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 4114)
              (ui_sh_12 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgauipc with "Hcg Hpc").
    iIntros (CIDh4) "Hcg Hpc".
    set (g6 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 4114 : mword 64)]> g5).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E12) in "Hpc".
    (* ---- 0x16  addi a1,a1,622 ---- *)
    assert (Hg6a1 : g6 !!! Regidx a1_idx = (mword_of_int 4114 : mword 64))
      by exact (upd_eq g5 (Regidx a1_idx)
                  (regval_into_reg (mword_of_int 4114 : mword 64))).
    assert (Hgaddr : (mword_of_int 4736 : mword 64)
                     = add_vec (g6 !!! Regidx a1_idx)
                         (sign_extend' 64 (mword_of_int 622 : mword 12))).
    { rewrite Hg6a1. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uv_addi C pt Psh MG4 g6 (mword_of_int 0x16)
              (mword_of_int 622 : mword 12) a1_idx a1_idx (mword_of_int 4736)
              (ui_sh_16 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgaddr with "Hcg Hpc").
    iIntros (CIDh5) "Hcg Hpc".
    set (g7 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 4736 : mword 64)]> g6).
    assert (E16 : add_vec_int (mword_of_int 0x16 : mword 64) 4 = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E16) in "Hpc".
    (* ---- 0x1a  c.mv a0,a2 ---- *)
    assert (Hg7a2 : g7 !!! Regidx a2_idx = (mword_of_int 2 : mword 64)).
    { rewrite (upd_ne g6 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g4 (Regidx a2_idx) _). }
    assert (Hgw0 : (mword_of_int 2 : mword 64)
                   = add_vec zero_reg (g7 !!! Regidx a2_idx))
      by (rewrite Hg7a2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MG4 g7 (mword_of_int 0x1a)
              a0_idx a2_idx (mword_of_int 2)
              (ui_sh_1a pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgw0 with "Hcg Hpc").
    iIntros (CIDh6) "Hcg Hpc".
    set (g8 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> g7).
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 2 = mword_of_int 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1a) in "Hpc".
    (* ---- 0x1c  jal ra, 0xca6 <write> ---- *)
    assert (Hgtgtw : (mword_of_int 0xca6 : mword 64)
                     = add_vec (mword_of_int 0x1c)
                         (sign_extend' 64 (mword_of_int 3210 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hglinkw : (mword_of_int 0x20 : mword 64)
                      = add_vec_int (mword_of_int 0x1c : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MG4 g8 (mword_of_int 0x1c)
              (mword_of_int 3210 : mword 21) ra_idx
              (mword_of_int 0xca6) (mword_of_int 0x20)
              (ui_sh_1c pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgtgtw Hglinkw
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDh7) "Hcg Hpc".
    set (g9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x20 : mword 64)]> g8).
    iEval (rewrite <- Hswrite) in "Hpc".
    assert (Hg9ra : g9 !!! Regidx ra_idx = (mword_of_int 0x20 : mword 64))
      by exact (upd_eq g8 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x20 : mword 64))).
    assert (Hg9a1 : g9 !!! Regidx a1_idx = (mword_of_int 4736 : mword 64)).
    { rewrite (upd_ne g8 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g6 (Regidx a1_idx) _). }
    assert (Hg9a2 : g9 !!! Regidx a2_idx = (mword_of_int 2 : mword 64)).
    { rewrite (upd_ne g8 (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Hg7a2. }
    (* the "$ " literal, as a readable two-byte window *)
    assert (Hrodata : uv_rd pt MG4 4736 2).
    { constructor.
      - lia.
      - lia.
      - change (2 ^ 38) with 274877906944. lia.
      - intros j Hj. exact (sh_text_layout_load pt (4736 + j) Hl ltac:(lia)).
      - intros j Hj.
        destruct (Z.eq_dec j 0) as [ -> | Hj1 ].
        + exists (Z_to_bv 8 0x24). apply Hdat4.
          vm_compute. first [ reflexivity | f_equal; apply bv_eq; reflexivity ].
        + assert (Hj' : j = 1) by lia. subst j.
          exists (Z_to_bv 8 0x20). apply Hdat4.
          vm_compute. first [ reflexivity | f_equal; apply bv_eq; reflexivity ]. }
    iApply (wp_sh_write C pt gin gbrk hbase hlen Q CIDh7 MG4 g9
              ltac:(split_and!;
                    [ exact Hlay | exact Htxt4
                    | rewrite Hg9ra; vm_compute; reflexivity ])
              ltac:(rewrite Hg9a1 Hg9a2;
                    rewrite (uint_moi 4736 ltac:(unfold Z64; lia));
                    rewrite (uint_moi 2 ltac:(unfold Z64; lia));
                    exact Hrodata)
              with "Hcg Hpc [Hin Hcont]").
    iIntros (CIDh8 retw) "Hcg Hpc".
    iEval (rewrite Hg9ra) in "Hpc".
    set (gW7 := <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> g9).
    set (gW := <[Regidx a0_idx := retw]> gW7).
    assert (HWs1 : gW !!! Regidx s1_idx = (mword_of_int buf : mword 64)).
    {
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g2 (Regidx s1_idx) _).
    }
    assert (HWs2 : gW !!! Regidx s2_idx = (mword_of_int nbuf : mword 64)).
    {
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g3 (Regidx s2_idx) _).
    }
    (* ---- 0x20  c.mv a2,s2 ---- *)
    assert (Hgwa2 : (mword_of_int nbuf : mword 64)
                    = add_vec zero_reg (gW !!! Regidx s2_idx))
      by (rewrite HWs2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MG4 gW (mword_of_int 0x20)
              a2_idx s2_idx (mword_of_int nbuf)
              (ui_sh_20 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgwa2 with "Hcg Hpc").
    iIntros (CIDh9) "Hcg Hpc".
    set (gA := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int nbuf : mword 64)]> gW).
    assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 2 = mword_of_int 0x22)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E20) in "Hpc".
    (* ---- 0x22  c.li a1,0 ---- *)
    assert (Hgli0 : (mword_of_int 0 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MG4 gA (mword_of_int 0x22)
              (mword_of_int 0 : mword 6) a1_idx (mword_of_int 0 : mword 64)
              (ui_sh_22 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgli0 with "Hcg Hpc").
    iIntros (CIDh10) "Hcg Hpc".
    set (gB := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> gA).
    assert (E22 : add_vec_int (mword_of_int 0x22 : mword 64) 2 = mword_of_int 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E22) in "Hpc".
    (* ---- 0x24  c.mv a0,s1 ---- *)
    assert (HBs1 : gB !!! Regidx s1_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne gA (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact HWs1. }
    assert (Hgwa0 : (mword_of_int buf : mword 64)
                    = add_vec zero_reg (gB !!! Regidx s1_idx))
      by (rewrite HBs1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MG4 gB (mword_of_int 0x24)
              a0_idx s1_idx (mword_of_int buf)
              (ui_sh_24 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgwa0 with "Hcg Hpc").
    iIntros (CIDh11) "Hcg Hpc".
    set (gC := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int buf : mword 64)]> gB).
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2 = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E24) in "Hpc".
    (* ---- 0x26  jal ra, 0xa5c <memset> ---- *)
    assert (Hgtgtm : (mword_of_int 0xa5c : mword 64)
                     = add_vec (mword_of_int 0x26)
                         (sign_extend' 64 (mword_of_int 2614 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hglinkm : (mword_of_int 0x2a : mword 64)
                      = add_vec_int (mword_of_int 0x26 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MG4 gC (mword_of_int 0x26)
              (mword_of_int 2614 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x2a)
              (ui_sh_26 pt MG4 Hl Htxt4)
              ltac:(vm_compute; discriminate) Hgtgtm Hglinkm
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDh12) "Hcg Hpc".
    set (gD := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x2a : mword 64)]> gC).
    iEval (rewrite <- Hsmemset) in "Hpc".
    assert (HDsp : gD !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gA (Regidx a1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW (Regidx a2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) _).
    }
    assert (HDs1 : gD !!! Regidx s1_idx = (mword_of_int buf : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gA (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g2 (Regidx s1_idx) _).
    }
    assert (HDs2 : gD !!! Regidx s2_idx = (mword_of_int nbuf : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gA (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq g3 (Regidx s2_idx) _).
    }
    assert (HDra : gD !!! Regidx ra_idx = (mword_of_int 0x2a : mword 64)).
    {
      exact (upd_eq gC (Regidx ra_idx) _).
    }
    assert (HDa0 : gD !!! Regidx a0_idx = (mword_of_int buf : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gB (Regidx a0_idx) _).
    }
    assert (HDa1 : gD !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gA (Regidx a1_idx) _).
    }
    assert (HDa2 : gD !!! Regidx a2_idx = (mword_of_int nbuf : mword 64)).
    {
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gA (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gW (Regidx a2_idx) _).
    }
    assert (HDpres : forall r : mword 5,
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a1_idx ->
              Regidx r <> Regidx a2_idx -> Regidx r <> Regidx a7_idx ->
              Regidx r <> Regidx ra_idx ->
              gD !!! Regidx r = m !!! Regidx r).
    { intros r Ncsp_rs1 Ns0_idx Ns1_idx Ns2_idx Na0_idx Na1_idx Na2_idx Na7_idx
             Nra_idx.
      rewrite (upd_ne gC (Regidx ra_idx) (Regidx r) _ Nra_idx).
      rewrite (upd_ne gB (Regidx a0_idx) (Regidx r) _ Na0_idx).
      rewrite (upd_ne gA (Regidx a1_idx) (Regidx r) _ Na1_idx).
      rewrite (upd_ne gW (Regidx a2_idx) (Regidx r) _ Na2_idx).
      rewrite (upd_ne gW7 (Regidx a0_idx) (Regidx r) _ Na0_idx).
      rewrite (upd_ne g9 (Regidx a7_idx) (Regidx r) _ Na7_idx).
      rewrite (upd_ne g8 (Regidx ra_idx) (Regidx r) _ Nra_idx).
      rewrite (upd_ne g7 (Regidx a0_idx) (Regidx r) _ Na0_idx).
      rewrite (upd_ne g6 (Regidx a1_idx) (Regidx r) _ Na1_idx).
      rewrite (upd_ne g5 (Regidx a1_idx) (Regidx r) _ Na1_idx).
      rewrite (upd_ne g4 (Regidx a2_idx) (Regidx r) _ Na2_idx).
      rewrite (upd_ne g3 (Regidx s2_idx) (Regidx r) _ Ns2_idx).
      rewrite (upd_ne g2 (Regidx s1_idx) (Regidx r) _ Ns1_idx).
      rewrite (upd_ne g1 (Regidx s0_idx) (Regidx r) _ Ns0_idx).
      rewrite (upd_ne m (Regidx csp_rs1) (Regidx r) _ Ncsp_rs1).
      reflexivity. }
    (* ---- the call: memset(buf, 0, nbuf) ---- *)
    assert (Hstk16 : uv_stack pt MG4 (mword_of_int (uint sp0 - 32)) 16)
      by exact (uv_stack_dom pt M MG4 _ 16 (proj1 Honl4) Hst16r).
    assert (Hstk96 : uv_stack pt MG4 (mword_of_int (uint sp0 - 32)) 96)
      by exact (uv_stack_dom pt M MG4 _ 96 (proj1 Honl4) Hst96r).
    assert (Hwr4 : uv_wr pt MG4 buf nbuf)
      by exact (uv_wr_dom pt M MG4 buf nbuf (proj1 Honl4) Hwr).
    assert (Hc0 : gD !!! Regidx a1_idx
                  = (mword_of_int (bv_unsigned ubyte0) : mword 64)).
    { replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
      exact HDa1. }
    iApply (wp_sh_memset C pt gin gbrk hbase hlen Q CIDh12 MG4 gD
              (mword_of_int (uint sp0 - 32)) buf nbuf ubyte0
              Hlay Htxt4 HDsp Hstk16 HDa0 Hc0 HDa2
              ltac:(lia) Hwr4 ltac:(unfold sh_frame_ok; rewrite Husp; lia)
              Hbuflo
              ltac:(rewrite Husp; destruct Hdisj; [ right | left ]; lia)
              ltac:(rewrite HDra; vm_compute; reflexivity)
              with "Hcg Hpc [Hin Hcont]").
    iIntros (CIDh13 gM M5) "%Hcsms %HMa0 %Hfilled %Honlyms Hcg Hpc".
    unfold sh_win in Honlyms. rewrite Husp in Honlyms.
    iEval (rewrite HDra) in "Hpc".
    assert (Htxt5 : sh_text_sub M5)
      by exact (only_in2_text MG4 M5 buf nbuf (uint sp0 - 32 - 16) 16
                  Hbuflo ltac:(lia) Honlyms Htxt4).
    assert (Hstk5 : uv_stack pt M5 (mword_of_int (uint sp0 - 32)) 96)
      by exact (uv_stack_dom pt MG4 M5 _ 96 (proj1 Honlyms) Hstk96).
    assert (Hwr5 : uv_wr pt M5 buf nbuf)
      by exact (uv_wr_dom pt MG4 M5 buf nbuf (proj1 Honlyms) Hwr4).
    assert (HMsp : gM !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 32) : mword 64))
      by (rewrite (Hcsms csp_rs1 ltac:(vm_compute; reflexivity)); exact HDsp).
    assert (HMs1 : gM !!! Regidx s1_idx = (mword_of_int buf : mword 64))
      by (rewrite (Hcsms s1_idx ltac:(vm_compute; reflexivity)); exact HDs1).
    assert (HMs2 : gM !!! Regidx s2_idx = (mword_of_int nbuf : mword 64))
      by (rewrite (Hcsms s2_idx ltac:(vm_compute; reflexivity)); exact HDs2).
    (* ---- 0x2a  c.mv a1,s2 ---- *)
    assert (Hgea1 : (mword_of_int nbuf : mword 64)
                    = add_vec zero_reg (gM !!! Regidx s2_idx))
      by (rewrite HMs2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M5 gM (mword_of_int 0x2a)
              a1_idx s2_idx (mword_of_int nbuf)
              (ui_sh_2a pt M5 Hl Htxt5)
              ltac:(vm_compute; discriminate) Hgea1 with "Hcg Hpc").
    iIntros (CIDh14) "Hcg Hpc".
    set (gE := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int nbuf : mword 64)]> gM).
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 2 = mword_of_int 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E2a) in "Hpc".
    (* ---- 0x2c  c.mv a0,s1 ---- *)
    assert (HEs1 : gE !!! Regidx s1_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne gM (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact HMs1. }
    assert (Hgea0 : (mword_of_int buf : mword 64)
                    = add_vec zero_reg (gE !!! Regidx s1_idx))
      by (rewrite HEs1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh M5 gE (mword_of_int 0x2c)
              a0_idx s1_idx (mword_of_int buf)
              (ui_sh_2c pt M5 Hl Htxt5)
              ltac:(vm_compute; discriminate) Hgea0 with "Hcg Hpc").
    iIntros (CIDh15) "Hcg Hpc".
    set (gF := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int buf : mword 64)]> gE).
    assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2 = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E2c) in "Hpc".
    (* ---- 0x2e  jal ra, 0xaaa <gets> ---- *)
    assert (Hgtgtg : (mword_of_int 0xaaa : mword 64)
                     = add_vec (mword_of_int 0x2e)
                         (sign_extend' 64 (mword_of_int 2684 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hglinkg : (mword_of_int 0x32 : mword 64)
                      = add_vec_int (mword_of_int 0x2e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh M5 gF (mword_of_int 0x2e)
              (mword_of_int 2684 : mword 21) ra_idx
              (mword_of_int 0xaaa) (mword_of_int 0x32)
              (ui_sh_2e pt M5 Hl Htxt5)
              ltac:(vm_compute; discriminate) Hgtgtg Hglinkg
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDh16) "Hcg Hpc".
    set (gG := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x32 : mword 64)]> gF).
    iEval (rewrite <- Hsgets) in "Hpc".
    assert (HGra : gG !!! Regidx ra_idx = (mword_of_int 0x32 : mword 64))
      by exact (upd_eq gF (Regidx ra_idx) _).
    assert (HGa0 : gG !!! Regidx a0_idx = (mword_of_int buf : mword 64)).
    { rewrite (upd_ne gF (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gE (Regidx a0_idx) _). }
    assert (HGa1 : gG !!! Regidx a1_idx = (mword_of_int nbuf : mword 64)).
    { rewrite (upd_ne gF (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gE (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gM (Regidx a1_idx) _). }
    assert (HGsp : gG !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gF (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gE (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gM (Regidx a1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HMsp. }
    (* ---- the call: gets(buf, nbuf) ---- *)
    iApply (wp_sh_gets CIDh16 M5 gG (mword_of_int (uint sp0 - 32)) buf nbuf
              taken rest
              Hlay Htxt5 HGsp Hstk5 HGa0 HGa1 Htk (conj Hfit1 Hfit2')
              Hwr5
              ltac:(unfold sh_frame_ok; rewrite Husp; lia) Hbuflo
              ltac:(rewrite Husp; destruct Hdisj; [ left | right ]; lia)
              ltac:(rewrite HGra; vm_compute; reflexivity)
              with "Hcg Hin Hpc [Hcont]").
    iIntros (CIDh17 gH M6) "%Hcsgt %HHa0 %Hstr6 %Honlygt Hin Hcg Hpc".
    unfold sh_win in Honlygt. rewrite Husp in Honlygt.
    iEval (rewrite HGra) in "Hpc".
    assert (Htext6 : sh_text_sub M6)
      by exact (only_in2_text M5 M6 buf (Z.of_nat (length taken) + 1)
                  (uint sp0 - 32 - 96) 96 Hbuflo ltac:(lia) Honlygt Htxt5).
    assert (Hstk6 : uv_stack pt M6 sp0 32)
      by exact (uv_stack_dom pt M M6 sp0 32
                  ltac:(intros x Hx;
                        exact (proj1 Honlygt x (proj1 Honlyms x
                                 (proj1 Honl4 x Hx)))) Hst32).
    assert (HHs1 : gH !!! Regidx s1_idx = (mword_of_int buf : mword 64))
      by (rewrite (Hcsgt s1_idx ltac:(vm_compute; reflexivity));
          rewrite (upd_ne gF (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne gE (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate));
          exact HEs1).
    assert (HHsp : gH !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 32) : mword 64))
      by (rewrite (Hcsgt csp_rs1 ltac:(vm_compute; reflexivity)); exact HGsp).
    (* the byte [buf[0]] the EOF test reads *)
    assert (Hbyte0 : exists b0 : bv 8,
              M6 !! buf = Some b0 /\ (bv_unsigned b0 = 0 <-> taken = [])).
    { destruct Hstr6 as (Hc1 & Hc2).
      destruct taken as [ | b0 tl ].
      - exists ubyte0. split.
        + replace buf with (buf + Z.of_nat (length (@nil (bv 8)))) by (cbn; lia).
          exact Hc2.
        + split; [ intros _; reflexivity | intros _; vm_compute; reflexivity ].
      - exists b0. split.
        + replace buf with (buf + Z.of_nat 0) by lia.
          exact (Hc1 0%nat b0 eq_refl).
        + split;
            [ intro Hz; exfalso; apply (Hnul b0 eq_refl); apply bv8_eq0; exact Hz
            | intro Hc; discriminate Hc ]. }
    destruct Hbyte0 as (b0 & Hb0at & Hb0z).
    pose proof (bv8_rng b0) as Hb0r.
    (* ---- 0x32  lbu a0,0(s1) ---- *)
    assert (Hz0g : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hvab0 : (mword_of_int buf : mword 64)
                    = add_vec (gH !!! Regidx s1_idx)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite HHs1 Hz0g moi_add. f_equal; lia. }
    assert (Hrd6 : uv_rd pt M6 buf nbuf).
    { apply (uv_rd_dom pt M M6 buf nbuf); [ | exact Hrdb ].
      intros x Hx.
      exact (proj1 Honlygt x (proj1 Honlyms x (proj1 Honl4 x Hx))). }
    assert (Hubuf : uint (mword_of_int buf : mword 64) = buf)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hcanbuf : uva_canon (mword_of_int buf : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hb0at' : M6 !! (uint (mword_of_int buf : mword 64)) = Some b0)
      by (rewrite Hubuf; exact Hb0at).
    destruct (uv_rd_leaf_at pt M6 buf nbuf buf Hrd6 ltac:(lia))
      as (wrd & Hwrdl & Hwrdok).
    iApply (wp_uv_lbu C pt Psh M6 gH (mword_of_int 0x32)
              (mword_of_int 0 : mword 12) s1_idx a0_idx
              wrd (mword_of_int buf) (mword_of_int (bv_unsigned b0)) b0
              (ui_sh_32 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hvab0 Hwrdl Hwrdok Hcanbuf
              Hb0at' ltac:(symmetry; apply zext8_moi)
              with "Hcg Hpc").
    iIntros (CIDh18) "Hcg Hpc".
    set (gI := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> gH).
    assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 4 = mword_of_int 0x36)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E32) in "Hpc".
    (* ---- 0x36  seqz a0,a0 ---- *)
    assert (HIa0 : gI !!! Regidx a0_idx
                   = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq gH (Regidx a0_idx) _).
    assert (Hsx1g : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                    = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hseqz : (mword_of_int (if bool_decide (taken = []) then 1 else 0)
                     : mword 64)
                    = zero_extend' 64
                        (bool_to_bit
                           (zopz0zI_u (gI !!! Regidx a0_idx)
                              (sign_extend' 64 (mword_of_int 1 : mword 12))))).
    { rewrite HIa0 Hsx1g.
      rewrite (moi_lt_u (bv_unsigned b0) 1 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      destruct (bool_decide_reflect (taken = [])) as [ He | He ].
      - replace (Z.ltb (bv_unsigned b0) 1) with true.
        + apply bv_eq; vm_compute; reflexivity.
        + symmetry. apply Z.ltb_lt.
          assert (Hz : bv_unsigned b0 = 0) by (apply Hb0z; exact He). lia.
      - replace (Z.ltb (bv_unsigned b0) 1) with false.
        + apply bv_eq; vm_compute; reflexivity.
        + symmetry. apply Z.ltb_ge.
          assert (Hz : bv_unsigned b0 <> 0)
            by (intro Hz0; apply He; apply Hb0z; exact Hz0). lia. }
    iApply (wp_uv_sltiu C pt Psh M6 gI (mword_of_int 0x36)
              (mword_of_int 1 : mword 12) a0_idx a0_idx
              (mword_of_int (if bool_decide (taken = []) then 1 else 0))
              (ui_sh_36 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hseqz with "Hcg Hpc").
    iIntros (CIDh19) "Hcg Hpc".
    set (gJ := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (if bool_decide (taken = []) then 1 else 0)
                       : mword 64)]> gI).
    assert (E36 : add_vec_int (mword_of_int 0x36 : mword 64) 4 = mword_of_int 0x3a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E36) in "Hpc".
    (* ---- 0x3a  negw a0,a0 ---- *)
    iDestruct "Hcg" as "(#Hcapg & Hling & Hgprg)".
    iDestruct (gpr_file_x0 gJ x0_idx ltac:(vm_compute; reflexivity) with "Hgprg")
      as "[%Hgx0 Hgprg]".
    iAssert (uv_cap_gpr (CID := CIDh19) C pt Psh M6 gJ) with "[Hling Hgprg]"
      as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcapg Hling Hgprg". }
    assert (HJa0 : gJ !!! Regidx a0_idx
                   = (mword_of_int (if bool_decide (taken = []) then 1 else 0)
                      : mword 64))
      by exact (upd_eq gI (Regidx a0_idx) _).
    assert (Hnegw : (mword_of_int (if bool_decide (taken = []) then (-1) else 0)
                     : mword 64)
                    = sign_extend' 64
                        (sub_vec
                           (subrange_vec_dec (gJ !!! Regidx x0_idx) 31 0 : mword 32)
                           (subrange_vec_dec (gJ !!! Regidx a0_idx) 31 0
                            : mword 32))).
    { rewrite Hgx0 HJa0 zero_reg_moi.
      destruct (bool_decide (taken = [])); apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uv_subw C pt Psh M6 gJ (mword_of_int 0x3a)
              x0_idx a0_idx a0_idx
              (mword_of_int (if bool_decide (taken = []) then (-1) else 0))
              (ui_sh_3a pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hnegw with "Hcg Hpc").
    iIntros (CIDr0) "Hcg Hpc".
    set (gR0 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (if bool_decide (taken = []) then (-1) else 0)
                        : mword 64)]> gJ).
    assert (E3a : add_vec_int (mword_of_int 0x3a : mword 64) 4 = mword_of_int 0x3e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E3a) in "Hpc".
    assert (HgspR0 : gR0 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gJ (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gI (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gH (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HHsp. }
    (* the four frame slots survive memset and gets *)
    assert (Hgsurv : forall k : Z, uint sp0 - 32 <= k < uint sp0 ->
              M6 !! k = MG4 !! k).
    { intros k Hk.
      rewrite (proj2 Honlygt k
                 ltac:(intro Hc;
                       destruct (in_win2_inv _ _ _ _ _ Hc) as [ Hw | Hw ];
                       [ destruct Hdisj; lia | lia ])).
      exact (proj2 Honlyms k
               ltac:(intro Hc;
                     destruct (in_win2_inv _ _ _ _ _ Hc) as [ Hw | Hw ];
                     [ destruct Hdisj; lia | lia ])). }
    assert (Hgby24 : uM_bytes M6 (uint sp0 - 32 + 24) 8 (g1 !!! Regidx ra_idx))
      by exact (bytes_win MG4 M6 (uint sp0 - 32 + 24) _
                  ltac:(intros k Hk; apply Hgsurv; lia) Hgb24).
    assert (Hgby16 : uM_bytes M6 (uint sp0 - 32 + 16) 8 (g1 !!! Regidx s0_idx))
      by exact (bytes_win MG4 M6 (uint sp0 - 32 + 16) _
                  ltac:(intros k Hk; apply Hgsurv; lia) Hgb16).
    assert (Hgby8 : uM_bytes M6 (uint sp0 - 32 + 8) 8 (g1 !!! Regidx s1_idx))
      by exact (bytes_win MG4 M6 (uint sp0 - 32 + 8) _
                  ltac:(intros k Hk; apply Hgsurv; lia) Hgb8).
    assert (Hgby0 : uM_bytes M6 (uint sp0 - 32 + 0) 8 (g1 !!! Regidx s2_idx))
      by exact (bytes_win MG4 M6 (uint sp0 - 32 + 0) _
                  ltac:(intros k Hk; apply Hgsurv; lia) Hgb0).
    (* ---- 0x3e  c.ldsp ra_idx,24(sp) ---- *)
    iApply (wp_sh_reload CIDr0 Psh 0x3e 0x40 32 24 (mword_of_int 3 : mword 6)
              ra_idx (g1 !!! Regidx ra_idx) M6 gR0 sp0
              Hstk6 HgspR0
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hgby24
              (ui_sh_3e pt M6 Hl Htext6)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDr1) "Hcg Hpc".
    set (gR1 := <[Regidx ra_idx := regval_into_reg (g1 !!! Regidx ra_idx)]> gR0).
    assert (HgspR1 : gR1 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gR0 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HgspR0. }
    (* ---- 0x40  c.ldsp s0_idx,16(sp) ---- *)
    iApply (wp_sh_reload CIDr1 Psh 0x40 0x42 32 16 (mword_of_int 2 : mword 6)
              s0_idx (g1 !!! Regidx s0_idx) M6 gR1 sp0
              Hstk6 HgspR1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hgby16
              (ui_sh_40 pt M6 Hl Htext6)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDr2) "Hcg Hpc".
    set (gR2 := <[Regidx s0_idx := regval_into_reg (g1 !!! Regidx s0_idx)]> gR1).
    assert (HgspR2 : gR2 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gR1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HgspR1. }
    (* ---- 0x42  c.ldsp s1_idx,8(sp) ---- *)
    iApply (wp_sh_reload CIDr2 Psh 0x42 0x44 32 8 (mword_of_int 1 : mword 6)
              s1_idx (g1 !!! Regidx s1_idx) M6 gR2 sp0
              Hstk6 HgspR2
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hgby8
              (ui_sh_42 pt M6 Hl Htext6)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDr3) "Hcg Hpc".
    set (gR3 := <[Regidx s1_idx := regval_into_reg (g1 !!! Regidx s1_idx)]> gR2).
    assert (HgspR3 : gR3 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gR2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HgspR2. }
    (* ---- 0x44  c.ldsp s2_idx,0(sp) ---- *)
    iApply (wp_sh_reload CIDr3 Psh 0x44 0x46 32 0 (mword_of_int 0 : mword 6)
              s2_idx (g1 !!! Regidx s2_idx) M6 gR3 sp0
              Hstk6 HgspR3
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hgby0
              (ui_sh_44 pt M6 Hl Htext6)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDr4) "Hcg Hpc".
    set (gR4 := <[Regidx s2_idx := regval_into_reg (g1 !!! Regidx s2_idx)]> gR3).
    assert (HgspR4 : gR4 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne gR3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact HgspR3. }
    assert (Hgresra_idx : gR4 !!! Regidx ra_idx = g1 !!! Regidx ra_idx).
    {
      rewrite (upd_ne gR3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gR2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gR1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gR0 (Regidx ra_idx) _).
    }
    assert (Hgress0_idx : gR4 !!! Regidx s0_idx = g1 !!! Regidx s0_idx).
    {
      rewrite (upd_ne gR3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne gR2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gR1 (Regidx s0_idx) _).
    }
    assert (Hgress1_idx : gR4 !!! Regidx s1_idx = g1 !!! Regidx s1_idx).
    {
      rewrite (upd_ne gR3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gR2 (Regidx s1_idx) _).
    }
    assert (Hgress2_idx : gR4 !!! Regidx s2_idx = g1 !!! Regidx s2_idx).
    {
      exact (upd_eq gR3 (Regidx s2_idx) _).
    }
    assert (HgpresR : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              gR4 !!! Regidx r = gR0 !!! Regidx r).
    { intros r Nra_idx Ns0_idx Ns1_idx Ns2_idx.
      rewrite (upd_ne gR3 (Regidx s2_idx) (Regidx r) _ Ns2_idx).
      rewrite (upd_ne gR2 (Regidx s1_idx) (Regidx r) _ Ns1_idx).
      rewrite (upd_ne gR1 (Regidx s0_idx) (Regidx r) _ Ns0_idx).
      rewrite (upd_ne gR0 (Regidx ra_idx) (Regidx r) _ Nra_idx).
      reflexivity. }
    (* ---- 0x46  c.addi16sp sp,sp,32 ---- *)
    assert (Hgi16b : (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))
                      : mword 64) = mword_of_int 32)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hgspback : sp0 = add_vec (gR4 !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))).
    { rewrite HgspR4 Hgi16b moi_add.
      replace (uint sp0 - 32 + 32) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh M6 gR4 (mword_of_int 0x46)
              (mword_of_int 2 : mword 6) sp0
              (ui_sh_46 pt M6 Hl Htext6) Hgspback with "Hcg Hpc").
    iIntros (CIDr5) "Hcg Hpc".
    set (gRF := <[Regidx csp_rs1 := regval_into_reg (sp0 : mword 64)]> gR4).
    assert (E46 : add_vec_int (mword_of_int 0x46 : mword 64) 2 = mword_of_int 0x48)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E46) in "Hpc".
    assert (HgFpres : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              gRF !!! Regidx r = gR4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne gR4 (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x48  c.jr ra ---- *)
    assert (HgFra : gRF !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (HgFpres ra_idx ltac:(vm_compute; discriminate)).
      rewrite Hgresra_idx. exact (Hg1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Hgtgtret : (m !!! Regidx ra_idx) = ret_pc (gRF !!! Regidx ra_idx)).
    { rewrite HgFra. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M6 gRF (mword_of_int 0x48)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_48 pt M6 Hl Htext6)
              ltac:(vm_compute; discriminate) Hgtgtret with "Hcg Hpc").
    iIntros (CIDzz) "Hcg Hpc".
    iApply ("Hcont" $! CIDzz gRF M6 with "[] [] [] [] [] Hin Hcg Hpc").
    - (* ---- ucallee_saved ---- *)
      iPureIntro. intros r Hr.
      destruct (decide (Regidx r = Regidx csp_rs1)) as [ Esp | Nsp ].
      { rewrite Esp. rewrite (upd_eq gR4 (Regidx csp_rs1)
                                (regval_into_reg (sp0 : mword 64))).
        symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | N0 ].
      { rewrite E0 (HgFpres s0_idx ltac:(vm_compute; discriminate)) Hgress0_idx.
        exact (Hg1 s0_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | N1 ].
      { rewrite E1 (HgFpres s1_idx ltac:(vm_compute; discriminate)) Hgress1_idx.
        exact (Hg1 s1_idx ltac:(vm_compute; discriminate)). }
      destruct (decide (Regidx r = Regidx s2_idx)) as [ E2 | N2 ].
      { rewrite E2 (HgFpres s2_idx ltac:(vm_compute; discriminate)) Hgress2_idx.
        exact (Hg1 s2_idx ltac:(vm_compute; discriminate)). }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HgFpres r Nsp).
      rewrite (HgpresR r Nra N0 N1 N2).
      rewrite (upd_ne gJ (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne gI (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne gH (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (Hcsgt r Hr).
      rewrite (upd_ne gF (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne gE (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne gM (Regidx a1_idx) (Regidx r) _ Na1).
      rewrite (Hcsms r Hr).
      exact (HDpres r Nsp N0 N1 N2 Na0 Na1 Na2 Na7 Nra).
    - (* ---- the return value ---- *)
      iPureIntro.
      rewrite (HgFpres a0_idx ltac:(vm_compute; discriminate)).
      rewrite (HgpresR a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq gJ (Regidx a0_idx) _).
    - (* ---- the line, NUL-terminated, at [buf] ---- *)
      iPureIntro. exact Hstr6.
    - (* ---- and memset's zeros beyond it ---- *)
      iPureIntro. intros j Hj.
      rewrite (proj2 Honlygt (buf + j)
                 ltac:(intro Hc;
                       destruct (in_win2_inv _ _ _ _ _ Hc) as [ Hw | Hw ];
                       [ lia | destruct Hdisj; lia ])).
      exact (Hfilled j ltac:(lia)).
    - (* ---- and NOTHING outside the buffer and the 128-byte frame moved ---- *)
      iPureIntro. unfold sh_win. split.
      + intros k Hk.
        exact (proj1 Honlygt k (proj1 Honlyms k (proj1 Honl4 k Hk))).
      + intros k Hk.
        assert (Hk1 : k < buf \/ buf + nbuf <= k).
        { destruct (Z.lt_ge_cases k buf) as [ Ha | Ha ]; [ left; lia | ].
          destruct (Z.lt_ge_cases k (buf + nbuf)) as [ Hb | Hb ];
            [ exfalso; apply Hk; apply in_win2; left; lia | right; lia ]. }
        assert (Hk2 : k < uint sp0 - 128 \/ uint sp0 <= k).
        { destruct (Z.lt_ge_cases k (uint sp0 - 128)) as [ Ha | Ha ];
            [ left; lia | ].
          destruct (Z.lt_ge_cases k (uint sp0)) as [ Hb | Hb ];
            [ exfalso; apply Hk; apply in_win2; right; lia | right; lia ]. }
        rewrite (proj2 Honlygt k
                   ltac:(intro Hc;
                         destruct (in_win2_inv _ _ _ _ _ Hc) as [ Hw | Hw ];
                         lia)).
        rewrite (proj2 Honlyms k
                   ltac:(intro Hc;
                         destruct (in_win2_inv _ _ _ _ _ Hc) as [ Hw | Hw ];
                         lia)).
        exact (proj2 Honl4 k ltac:(lia)).
  Qed.

End UProofShIo.

Print Assumptions wp_sh_gets.
Print Assumptions wp_sh_getcmd.
