(* UProofEchoA.v -- the VERIFIED-EXECUTION proofs of the `echo` user
   program's LEAF functions (claude-notes/projects/user-echo.md): the two
   syscall stubs and `strlen`.  `main` and `start`, which call these, are
   UProofEcho.v.

     wp_echo_exit    exit   @0x332  c.li a7,2;  ecall              (diverges)
     wp_echo_write   write  @0x352  c.li a7,16; ecall; c.jr ra     (returns)
     wp_echo_strlen  strlen @0xdc   prologue; scan loop; epilogue  (returns)

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v, fed the matching
   [ui_echo_<off>] fact from UCodeEcho.v.  Every leaf continuation re-binds
   the hart ([∀ CID]): a user process can be preempted at any instruction and
   resumed on another hart, which is why every lemma here takes [CIDp] as an
   EXPLICIT leading binder rather than a section variable. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall.
Require Import WpUmodeStep WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UCodeEcho USpecEcho.
Require User.EchoSyms User.EchoInstrs User.EchoData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The pure shims [strlen] needs on top of UmodeArith.v / UmodeAbi.v.   *)
(*                                                                        *)
(* Everything here is about keeping every live register in the ONE shape   *)
(* [mword_of_int z] (see UmodeArith.v's header), plus the two byte facts a *)
(* string scan branches on.                                               *)
(* ===================================================================== *)

(* the workhorse [moi_add] at a register that is NOT yet normalized -- the
   shape every "pointer + closed displacement" step lands in *)

Local Lemma bv8_range (b : bv 8) : 0 <= bv_unsigned b < Z64.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E in Hr. unfold Z64. lia.
Qed.

(* "the byte is the NUL", as a [Z] fact -- the branch condition of a string
   scan, read off [ucstr]'s [ubyte0] *)
Local Lemma bv8_zero (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

(* an [lbu] leaves the byte zero-extended; normalize it like everything else *)

(* Sv39-canonicality of a normalized address, from its numeric range *)

(* an 8-byte store ABOVE the text preserves the text inclusion (the twin of
   UProofSync's [sync_text_sub_store8]) *)
Local Lemma echo_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  echo_text_sub M -> 4096 <= a -> echo_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (echo_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Section UProofEchoA.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  Local Notation Ψxv6 := (xv6_sys_protocol C pt).

  (* the ABI indices UmodeAbi.v does not name (it names only ra/sp/a0/a1/a2) *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* [uv_stack_slot] with the slot address NORMALIZED: every side          *)
  (* condition of the load AND store leaves at [sp0 - 16 + d], stated over  *)
  (* [mword_of_int a] rather than the [add_vec_int] tower the budget lemma  *)
  (* produces.  [a] is its own parameter so a call site may spell the       *)
  (* address the way the rest of its proof does ([uint sp0 - 8], not        *)
  (* [uint sp0 - 16 + 8]).                                                  *)
  (* ------------------------------------------------------------------- *)
  Local Lemma slot_facts (M : gmap Z (bv 8)) (sp0 : mword 64) (d a : Z) :
    uv_stack pt M sp0 16 -> 0 <= d -> d + 8 <= 16 -> Z.rem d 8 = 0 ->
    a = uint sp0 - 16 + d ->
    uint (mword_of_int a : mword 64) = a /\
    (exists w : mword 64,
       ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
       uleaf_ok (Store Data) w /\ uleaf_ok (Load Data) w) /\
    uva_canon (mword_of_int a : mword 64) /\
    Z.rem (uint (mword_of_int a : mword 64)) 4096 <= 4088 /\
    is_aligned_vaddr (Virtaddr (mword_of_int a : mword 64)) 8 = true /\
    (forall j : nat, (j < 8)%nat ->
       exists b : bv 8, M !! (uint (mword_of_int a : mword 64) + Z.of_nat j) = Some b).
  Proof.
    intros HS Hd0 Hdn Hd8 Ha. subst a.
    exact (uv_stack_slot_moi pt M sp0 16 d
             (mword_of_int (uint sp0 - 16 + d)) HS Hd0 Hdn Hd8 eq_refl).
  Qed.

  (* [uv_rd]'s per-byte mapping fact at an ABSOLUTE address *)

  (* ------------------------------------------------------------------- *)
  (* exit @0x332: c.li a7,2; ecall.  The ecall's protocol payload is the   *)
  (* [UsysNoRet] arm ([emp]) -- the syscall never comes back, so the WP is *)
  (* absorbed and there is nothing after it.  (The c.jr at 0x338 is dead    *)
  (* code and has no [uinstr] fact.)                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_echo_exit (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_echo_exit_body (CID := CIDp) C pt M m.
  Proof.
    intros Hlay Htext.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsexit) in "Hpc".
    (* 0x332  c.li a7,2 *)
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ψxv6 M m (mword_of_int 0x332)
              (mword_of_int 2 : mword 6) a7_idx (mword_of_int 2 : mword 64)
              (ui_echo_332 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hw2
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx a7_idx := regval_into_reg (mword_of_int 2 : mword 64)]> m).
    assert (Epc : add_vec_int (mword_of_int 0x332 : mword 64) 2 = mword_of_int 0x334)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc) in "Hpc".
    (* 0x334  ecall -- SYS_exit, the non-returning arm *)
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = 2)
      by (rewrite /m1; reg_lookup).
    iApply (wp_uv_ecall C pt Ψxv6 M m1 (mword_of_int 0x334)
              (ui_echo_334 pt M Hlay Htext)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x334) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x334)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hcg Hpc").
    rewrite /xv6_sys_protocol /usys_protocol_of.
    rewrite Ha7.
    change (xv6_sys_sem 2) with UsysNoRet.
    cbn [usys_arm]. done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* write @0x352: c.li a7,16; ecall; c.jr ra.  SYS_write is               *)
  (* [UsysReadsBuf], so the payload is a PAIR: the pure obligation that     *)
  (* (a1, a2) names a readable window of the process image -- discharged    *)
  (* from the caller's [Hbuf], since neither a1 nor a2 is a7 -- and then    *)
  (* the same resume continuation a pure-return syscall has.  The c.jr      *)
  (* returns to the caller's ra (2-aligned, so [ret_pc] is the identity).   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_echo_write (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_echo_write_body (CID := CIDp) C pt M m.
  Proof.
    intros Hlay Htext Hbuf Hret2.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hswrite) in "Hpc".
    (* the capability is persistent: keep a copy for the post-syscall repack *)
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgpr)".
    iAssert (uv_cap_gpr C pt Ψxv6 M m) with "[Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    (* 0x352  c.li a7,16 *)
    assert (Hw16 : (mword_of_int 16 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Ψxv6 M m (mword_of_int 0x352)
              (mword_of_int 16 : mword 6) a7_idx (mword_of_int 16 : mword 64)
              (ui_echo_352 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 16 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by reflexivity.
    iEval (rewrite Hnorm) in "Hcg".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x352 : mword 64) 2 = mword_of_int 0x354)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc1) in "Hpc".
    (* 0x354  ecall -- SYS_write, the buffer-reading arm *)
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = 16) by (rewrite /m1; reg_lookup).
    (* the buffer pair survives the a7 write *)
    assert (Ha1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_ecall C pt Ψxv6 M m1 (mword_of_int 0x354)
              (ui_echo_354 pt M Hlay Htext)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x354) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x354)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hcg Hpc").
    rewrite /xv6_sys_protocol /usys_protocol_of.
    rewrite Ha7.
    change (xv6_sys_sem 16) with UsysReadsBuf.
    cbn [usys_arm].
    iSplitR.
    { iPureIntro. rewrite Ha1 Ha2. exact Hbuf. }
    rewrite /usys_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Epc2 : add_vec_int (mword_of_int 0x354 : mword 64) 4 = mword_of_int 0x358)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Epc2) in "Hrun".
    iDestruct (uv_run_cap_gpr (CID := CID2) C pt Ψxv6 M
                 (<[Regidx a0_idx := ret]> m1) (mword_of_int 0x358)
                 with "Hcap Hrun") as "[Hcg Hpc]".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* 0x358  c.jr ra -- neither insert touches ra *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx (mword_of_int 1 : mword 5)) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 16) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx)
                   = ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra2. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Ψxv6 M m2 (mword_of_int 0x358)
              (mword_of_int 1 : mword 5) (m !!! Regidx ra_idx)
              (ui_echo_358 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* strlen's EPILOGUE @0xfc, shared verbatim by both arms of the entry    *)
  (* test (the len = 0 arm reaches it by the c.j at 0x106):                *)
  (*                                                                       *)
  (*   fc  c.ldsp ra,8(sp) ; fe  c.ldsp s0,0(sp) ; 100 c.addi sp,sp,16     *)
  (*   102 c.jr ra                                                          *)
  (*                                                                       *)
  (* The content is the two RELOADS: their [wval] is [uM_word M2 _ 8] over  *)
  (* the image the prologue left, and the epilogue must prove that equals   *)
  (* what the prologue stored.  For the s0 slot that is [uM_word_store8]    *)
  (* directly (M2 IS that store); for the ra slot one has to see through    *)
  (* the s0 store first, whose eight-byte window [sp0-16, sp0-8) is         *)
  (* disjoint from [sp0-8, sp0).                                            *)
  (*                                                                       *)
  (* The exit is stated POINTWISE over the registers (x1/x2/x8 by value,    *)
  (* everything else unchanged) rather than as an insert tower: the caller  *)
  (* owes [ucallee_saved], whose index is a VARIABLE, and a tower cannot be *)
  (* peeled at one.                                                        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_echo_strlen_epi (CIDp : CpuId) (M : gmap Z (bv 8))
      (mF : regfile) (sp0 v8 v0 : mword 64) :
    echo_layout pt ->
    echo_text_sub M ->
    uv_stack pt M sp0 16 ->
    is_aligned_vaddr (Virtaddr v8) 2 = true ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64) ->
    uv_cap_gpr (CID := CIDp) C pt Ψxv6
      (uM_store8 (uM_store8 M (uint sp0 - 8) v8) (uint sp0 - 16) v0) mF -∗
    pc_is (CID := CIDp) (mword_of_int 0xfc) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜m' !!! Regidx sp_idx = sp0⌝ -∗
       ⌜m' !!! Regidx s0_idx = v0⌝ -∗
       ⌜forall r : mword 5,
          Regidx r <> Regidx ra_idx -> Regidx r <> Regidx sp_idx ->
          Regidx r <> Regidx s0_idx -> m' !!! Regidx r = mF !!! Regidx r⌝ -∗
       uv_cap_gpr (CID := CID) C pt Ψxv6
         (uM_store8 (uM_store8 M (uint sp0 - 8) v8) (uint sp0 - 16) v0) m' -∗
       pc_is (CID := CID) v8 -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Htext Hst Hret2 Hsp.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    destruct (slot_facts M sp0 8 (uint sp0 - 8) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hu8 & (w8 & Hl8 & _ & Hok8) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (slot_facts M sp0 0 (uint sp0 - 16) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hu0 & (w0 & Hl0 & _ & Hok0) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    set (M1 := uM_store8 M (uint sp0 - 8) v8).
    set (M2 := uM_store8 M1 (uint sp0 - 16) v0).
    assert (Htext1 : echo_text_sub M1)
      by (unfold M1; apply echo_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : echo_text_sub M2)
      by (unfold M2; apply echo_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k)).
    { intros k Hk. unfold M2, M1.
      exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)). }
    assert (Hb8' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (mword_of_int (uint sp0 - 8) : mword 64) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb8 j Hj) as (b & Hb). exact (Hdom _ (mk_is_Some _ _ Hb)). }
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (mword_of_int (uint sp0 - 16) : mword 64) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb). exact (Hdom _ (mk_is_Some _ _ Hb)). }
    (* the ra slot reads back what the prologue stored *)
    assert (Hw8 : v8 = uM_word M2 (uint (mword_of_int (uint sp0 - 8) : mword 64)) 8).
    { rewrite Hu8. symmetry. apply (uM_bytes_inj M2 (uint sp0 - 8)).
      - apply (uM_word_bytes M2 (uint sp0 - 8) 8 ltac:(lia)).
        intros j Hj. destruct (Hb8' j Hj) as (b & Hb).
        rewrite Hu8 in Hb. exists b. exact Hb.
      - intros j Hj. unfold M2.
        rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) v0
                   (uint sp0 - 8 + Z.of_nat j) ltac:(intros i Hi; lia)).
        exact (uM_store8_bytes M (uint sp0 - 8) v8 j Hj). }
    (* ... and the s0 slot is the round trip itself *)
    assert (Hw0 : v0 = uM_word M2 (uint (mword_of_int (uint sp0 - 16) : mword 64)) 8).
    { rewrite Hu0. unfold M2. symmetry. apply uM_word_store8. }
    iIntros "Hcg Hpc Hcont".
    (* ---- 0xfc  c.ldsp ra,8(sp) ---- *)
    assert (Hva8 : (mword_of_int (uint sp0 - 8) : mword 64)
                   = add_vec (mF !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { assert (Hs : mF !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 16) : mword 64))
        by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_cldsp C pt Ψxv6 M2 mF (mword_of_int 0xfc)
              (mword_of_int 1 : mword 6) ra_idx
              w8 (mword_of_int (uint sp0 - 8)) v8
              (ui_echo_fc pt M2 Hlay Htext2)
              ltac:(vm_compute; discriminate) Hva8 Hl8 Hok8 Hcanon8 Hpg8 Hal8 Hb8' Hw8
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mF1 := <[Regidx ra_idx := regval_into_reg v8]> mF).
    assert (Efc : add_vec_int (mword_of_int 0xfc : mword 64) 2 = mword_of_int 0xfe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Efc) in "Hpc".
    (* ---- 0xfe  c.ldsp s0,0(sp) ---- *)
    assert (Hsp1 : mF1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne mF (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg v8)
                  ltac:(vm_compute; discriminate)) Hsp). }
    assert (Hva0 : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (mF1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_cldsp C pt Ψxv6 M2 mF1 (mword_of_int 0xfe)
              (mword_of_int 0 : mword 6) s0_idx
              w0 (mword_of_int (uint sp0 - 16)) v0
              (ui_echo_fe pt M2 Hlay Htext2)
              ltac:(vm_compute; discriminate) Hva0 Hl0 Hok0 Hcanon0 Hpg0 Hal0 Hb0' Hw0
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mF2 := <[Regidx s0_idx := regval_into_reg v0]> mF1).
    assert (Efe : add_vec_int (mword_of_int 0xfe : mword 64) 2 = mword_of_int 0x100)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Efe) in "Hpc".
    (* ---- 0x100  c.addi sp,sp,16 ---- *)
    assert (Hsp2 : mF2 !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne mF1 (Regidx s0_idx) (Regidx sp_idx) (regval_into_reg v0)
                  ltac:(vm_compute; discriminate)) Hsp1). }
    assert (Hwsp : sp0 = add_vec (mF2 !!! Regidx sp_idx)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))).
    { rewrite Hsp2.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 16 + 16) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi C pt Ψxv6 M2 mF2 (mword_of_int 0x100)
              (mword_of_int 16 : mword 6) sp_idx sp0
              (ui_echo_100 pt M2 Hlay Htext2)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mF3 := <[Regidx sp_idx := regval_into_reg sp0]> mF2).
    assert (E100 : add_vec_int (mword_of_int 0x100 : mword 64) 2 = mword_of_int 0x102)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E100) in "Hpc".
    (* ---- 0x102  c.jr ra ---- *)
    assert (Hra3 : mF3 !!! Regidx (mword_of_int 1 : mword 5) = v8).
    { exact (eq_trans
               (upd_ne mF2 (Regidx sp_idx) (Regidx (mword_of_int 1 : mword 5))
                  (regval_into_reg sp0) ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mF1 (Regidx s0_idx) (Regidx (mword_of_int 1 : mword 5))
                     (regval_into_reg v0) ltac:(vm_compute; discriminate))
                  (upd_eq mF (Regidx ra_idx) (regval_into_reg v8)))). }
    assert (Htgt : v8 = ret_pc (mF3 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra3. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Ψxv6 M2 mF3 (mword_of_int 0x102)
              (mword_of_int 1 : mword 5) v8
              (ui_echo_102 pt M2 Hlay Htext2)
              ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    (* the three exit facts *)
    assert (HA : mF3 !!! Regidx sp_idx = sp0)
      by exact (upd_eq mF2 (Regidx sp_idx) (regval_into_reg sp0)).
    assert (HB : mF3 !!! Regidx s0_idx = v0).
    { exact (eq_trans
               (upd_ne mF2 (Regidx sp_idx) (Regidx s0_idx) (regval_into_reg sp0)
                  ltac:(vm_compute; discriminate))
               (upd_eq mF1 (Regidx s0_idx) (regval_into_reg v0))). }
    assert (HC : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx sp_idx ->
              Regidx r <> Regidx s0_idx -> mF3 !!! Regidx r = mF !!! Regidx r).
    { intros r Hra Hsp' Hs0.
      exact (eq_trans (upd_ne mF2 (Regidx sp_idx) (Regidx r) (regval_into_reg sp0) Hsp')
               (eq_trans
                  (upd_ne mF1 (Regidx s0_idx) (Regidx r) (regval_into_reg v0) Hs0)
                  (upd_ne mF (Regidx ra_idx) (Regidx r) (regval_into_reg v8) Hra))). }
    iApply ("Hcont" $! CID4 mF3 with "[] [] [] Hcg Hpc").
    - iPureIntro. exact HA.
    - iPureIntro. exact HB.
    - iPureIntro. exact HC.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SCAN LOOP.  Head 0xee, back edge 0xf6:                            *)
  (*                                                                       *)
  (*   ee  c.mv   a3,a5 ; f0  c.addi a5,a5,1 ; f2  lbu a4,-1(a5)           *)
  (*   f6  c.bnez a4,0xee                                                   *)
  (*                                                                       *)
  (* This is an ORDINARY Rocq induction on the nat measure [len-1-j], NOT   *)
  (* an [iLob]: the loop is BOUNDED by the NUL's index, and WpUmodeBranch's *)
  (* leaf is later-free precisely so a bounded loop need not pay a [>].     *)
  (* The measure premise is STRICT (< n) so the n = 0 case is closed by     *)
  (* [lia] and the four-instruction body is written exactly once.           *)
  (*                                                                       *)
  (* Invariant at 0xee: a5 = s+1+j with 0 <= j <= len-1.  Exit: a3 =        *)
  (* s+len, at 0xf8.  Everything OTHER than a3/a4/a5 comes back            *)
  (* POINTWISE -- an insert tower would change shape every iteration and    *)
  (* could not compose with itself.                                        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_echo_strlen_loop (n : nat) :
    forall (CIDp : CpuId) (M : gmap Z (bv 8)) (mE : regfile) (s len j : Z),
      (Z.to_nat (len - 1 - j) < n)%nat ->
      echo_layout pt -> echo_text_sub M ->
      ucstr M s len -> uv_rd pt M s (len + 1) ->
      0 <= j <= len - 1 ->
      mE !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Ψxv6 M mE -∗
      pc_is (CID := CIDp) (mword_of_int 0xee) -∗
      (∀ (CID : CpuId) (m' : regfile),
         ⌜m' !!! Regidx a3_idx = (mword_of_int (s + len) : mword 64)⌝ -∗
         ⌜forall r : mword 5,
            Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
            Regidx r <> Regidx a5_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Ψxv6 M m' -∗
         pc_is (CID := CID) (mword_of_int 0xf8) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction n as [ | n IH ];
      intros CIDp M mE s len j Hn Hlay Htext Hstr Hrd Hj Ha5.
    { exfalso. lia. }
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    (* THE byte this iteration tests, and the dichotomy it decides *)
    assert (Hbex : exists bj : bv 8,
              M !! (s + 1 + j) = Some bj /\ (bj = ubyte0 <-> 1 + j = len)).
    { destruct (Z.eq_dec (1 + j) len) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr) as Hnul.
        replace (s + len) with (s + 1 + j) in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr (1 + j) ltac:(lia)) as (b & Hb & Hb0).
        replace (s + (1 + j)) with (s + 1 + j) in Hb by lia.
        exists b. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hb0 He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (bj & Hbj & Hbjiff).
    iIntros "Hcg Hpc Hcont".
    (* ---- 0xee  c.mv a3,a5 ---- *)
    assert (Hmv : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec zero_reg (mE !!! Regidx a5_idx)).
    { rewrite Ha5 moi_add_zero_l. reflexivity. }
    iApply (wp_uv_cmv C pt Ψxv6 M mE (mword_of_int 0xee)
              a3_idx a5_idx (mword_of_int (s + 1 + j))
              (ui_echo_ee pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hmv
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mL1 := <[Regidx a3_idx
                  := regval_into_reg (mword_of_int (s + 1 + j) : mword 64)]> mE).
    assert (Eee : add_vec_int (mword_of_int 0xee : mword 64) 2 = mword_of_int 0xf0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eee) in "Hpc".
    (* ---- 0xf0  c.addi a5,a5,1 ---- *)
    assert (Ha5_1 : mL1 !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64)).
    { exact (eq_trans
               (upd_ne mE (Regidx a3_idx) (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))
                  ltac:(vm_compute; discriminate)) Ha5). }
    assert (Hadd : (mword_of_int (s + 2 + j) : mword 64)
                   = add_vec (mL1 !!! Regidx a5_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
    { rewrite Ha5_1.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                    : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Ψxv6 M mL1 (mword_of_int 0xf0)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int (s + 2 + j))
              (ui_echo_f0 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hadd
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mL2 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (s + 2 + j) : mword 64)]> mL1).
    assert (Ef0 : add_vec_int (mword_of_int 0xf0 : mword 64) 2 = mword_of_int 0xf2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ef0) in "Hpc".
    (* ---- 0xf2  lbu a4,-1(a5) ---- *)
    assert (Ha5_2 : mL2 !!! Regidx a5_idx = (mword_of_int (s + 2 + j) : mword 64))
      by exact (upd_eq mL1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))).
    assert (Hva : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec (mL2 !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 4095 : mword 12))).
    { rewrite Ha5_2.
      assert (Hc : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M s (len + 1) (s + 1 + j) Hrd ltac:(lia)) as (wj & Hlj & Hokj).
    assert (Huva : uint (mword_of_int (s + 1 + j) : mword 64) = s + 1 + j)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hbyte : M !! (uint (mword_of_int (s + 1 + j) : mword 64)) = Some bj)
      by (rewrite Huva; exact Hbj).
    assert (Hcanonj : uva_canon (mword_of_int (s + 1 + j) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwvj : (mword_of_int (bv_unsigned bj) : mword 64)
                   = zero_extend' 64 (bj : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Ψxv6 M mL2 (mword_of_int 0xf2)
              (mword_of_int 4095 : mword 12) a5_idx a4_idx
              wj (mword_of_int (s + 1 + j)) (mword_of_int (bv_unsigned bj)) bj
              (ui_echo_f2 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hva Hlj Hokj Hcanonj Hbyte Hwvj
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mL3 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)]> mL2).
    assert (Ef2 : add_vec_int (mword_of_int 0xf2 : mword 64) 4 = mword_of_int 0xf6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ef2) in "Hpc".
    assert (Ha4 : mL3 !!! Regidx a4_idx = (mword_of_int (bv_unsigned bj) : mword 64))
      by exact (upd_eq mL2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))).
    (* what the iteration leaves of the OTHER registers *)
    assert (Hpres : forall r : mword 5,
              Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> mL3 !!! Regidx r = mE !!! Regidx r).
    { intros r H3 H4 H5.
      exact (eq_trans
               (upd_ne mL2 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)) H4)
               (eq_trans
                  (upd_ne mL1 (Regidx a5_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 2 + j) : mword 64)) H5)
                  (upd_ne mE (Regidx a3_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 1 + j) : mword 64)) H3))). }
    assert (Htgt : (mword_of_int 0xee : mword 64)
                   = add_vec (mword_of_int 0xf6)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 252 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xf6  c.bnez a4,0xee -- the ONE dichotomy of a string scan ---- *)
    destruct (Z.eq_dec (1 + j) len) as [Hend | Hne].
    - (* the byte is the NUL: fall through to 0xf8 with a3 = s + len *)
      assert (Hz : bv_unsigned bj = 0)
        by (apply bv8_zero; apply Hbjiff; exact Hend).
      assert (Htk : false = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4 (moi_neq_zero (bv_unsigned bj) (bv8_range bj)) Hz. reflexivity. }
      iApply (wp_uv_cbnez C pt Ψxv6 M mL3 (mword_of_int 0xf6)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                false (mword_of_int 0xee)
                (ui_echo_f6 pt M Hlay Htext)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      assert (Ef6 : (if false then (mword_of_int 0xee : mword 64)
                     else add_vec_int (mword_of_int 0xf6 : mword 64) 2)
                    = mword_of_int 0xf8)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ef6) in "Hpc".
      assert (H3 : mL3 !!! Regidx a3_idx = (mword_of_int (s + 1 + j) : mword 64)).
      { exact (eq_trans
                 (upd_ne mL2 (Regidx a4_idx) (Regidx a3_idx)
                    (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne mL1 (Regidx a5_idx) (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))
                       ltac:(vm_compute; discriminate))
                    (upd_eq mE (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))))). }
      iApply ("Hcont" $! CID4 mL3 with "[] [] Hcg Hpc").
      + iPureIntro. rewrite H3. f_equal; lia.
      + iPureIntro. exact Hpres.
    - (* a body byte: take the back edge with j := j + 1 *)
      assert (Hnz : bv_unsigned bj <> 0)
        by (intro Hz; apply Hne; apply Hbjiff; apply bv8_zero; exact Hz).
      assert (Htk : true = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4 (moi_neq_zero (bv_unsigned bj) (bv8_range bj)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uv_cbnez C pt Ψxv6 M mL3 (mword_of_int 0xf6)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                true (mword_of_int 0xee)
                (ui_echo_f6 pt M Hlay Htext)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      (* the taken pc is the loop head itself -- no normalization needed *)
      assert (Ha5' : mL3 !!! Regidx a5_idx
                     = (mword_of_int (s + 1 + (j + 1)) : mword 64)).
      { rewrite (upd_ne mL2 (Regidx a4_idx) (Regidx a5_idx)
                   (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                   ltac:(vm_compute; discriminate)).
        rewrite Ha5_2. f_equal; lia. }
      assert (Hmeas : (Z.to_nat (len - 1 - (j + 1)) < n)%nat) by lia.
      assert (Hj' : 0 <= j + 1 <= len - 1) by lia.
      iApply (IH CID4 M mL3 s len (j + 1) Hmeas Hlay Htext Hstr Hrd Hj' Ha5'
                with "Hcg Hpc").
      iIntros (CID5 m') "%Hm3 %Hmp Hcg Hpc".
      iApply ("Hcont" $! CID5 m' with "[] [] Hcg Hpc").
      + iPureIntro. exact Hm3.
      + iPureIntro. intros r H3 H4 H5.
        rewrite (Hmp r H3 H4 H5). exact (Hpres r H3 H4 H5).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* strlen @0xdc -- the whole function.                                   *)
  (*                                                                       *)
  (*   dc..e2  the gcc prologue (16-byte frame; ra and s0 spilled)         *)
  (*   e4..e8  load the first byte and test it -- the empty-string arm     *)
  (*   ea      a5 := s+1, then the scan loop (wp_echo_strlen_loop)         *)
  (*   f8      a0 := a3 - a0, i.e. the length, as a 32-bit subtract        *)
  (*   fc..102 the epilogue (wp_echo_strlen_epi), shared by both arms      *)
  (*                                                                       *)
  (* The two arms differ only in HOW a0 gets the answer (c.li 0 vs subw);  *)
  (* the entry test's dichotomy is [ucstr]'s, byte-for-byte.                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_echo_strlen (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s len : Z) :
    wp_echo_strlen_body (CID := CIDp) C pt M m sp0 s len.
  Proof.
    intros Hlay Htext Hsp Hst Hs Hstr Hrd Hlen Habove Hret2.
    destruct echo_syms_pins as (Hsmain & Hsstart & Hsstrlen & Hsexit & Hswrite).
    change (2 ^ 31) with 2147483648 in Hlen.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    destruct (slot_facts M sp0 8 (uint sp0 - 8) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hu8 & (w8 & Hl8 & Hok8s & _) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (slot_facts M sp0 0 (uint sp0 - 16) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hu0 & (w0 & Hl0 & Hok0s & _) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsstrlen) in "Hpc".
    (* ---- 0xdc  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi C pt Ψxv6 M m (mword_of_int 0xdc)
              (mword_of_int 48 : mword 6) sp_idx (mword_of_int (uint sp0 - 16))
              (ui_echo_dc pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx sp_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)]> m).
    assert (Edc : add_vec_int (mword_of_int 0xdc : mword 64) 2 = mword_of_int 0xde)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Edc) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))).
    (* ---- 0xde  c.sdsp ra,8(sp) ---- *)
    assert (Htg8 : (mword_of_int (uint sp0 - 8) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M m1 (mword_of_int 0xde)
              (mword_of_int 1 : mword 6) ra_idx
              w8 (mword_of_int (uint sp0 - 8)) (m !!! Regidx ra_idx)
              (ui_echo_de pt M Hlay Htext)
              Htg8 Hwra Hl8 Hok8s Hcanon8 Hpg8 Hal8 Hb8
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hu8) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext1 : echo_text_sub M1)
      by (unfold M1; apply echo_text_sub_store8; [ exact Htext | lia ]).
    assert (Ede : add_vec_int (mword_of_int 0xde : mword 64) 2 = mword_of_int 0xe0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ede) in "Hpc".
    (* ---- 0xe0  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M1 !! (uint (mword_of_int (uint sp0 - 16) : mword 64) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb). unfold M1.
      exact (uM_store8_is_Some _ _ _ _ (mk_is_Some _ _ Hb)). }
    assert (Htg0 : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    assert (Hws0 : m !!! Regidx s0_idx = m1 !!! Regidx s0_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx s0_idx)
                          (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uv_csdsp C pt Ψxv6 M1 m1 (mword_of_int 0xe0)
              (mword_of_int 0 : mword 6) s0_idx
              w0 (mword_of_int (uint sp0 - 16)) (m !!! Regidx s0_idx)
              (ui_echo_e0 pt M1 Hlay Htext1)
              Htg0 Hws0 Hl0 Hok0s Hcanon0 Hpg0 Hal0 Hb0'
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite Hu0) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (Htext2 : echo_text_sub M2)
      by (unfold M2; apply echo_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Ee0 : add_vec_int (mword_of_int 0xe0 : mword 64) 2 = mword_of_int 0xe2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ee0) in "Hpc".
    (* THE image postcondition, and the two transports it powers *)
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { unfold uM_only. split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (uM_store8_lookup_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(intros i Hi; lia)).
        unfold M1.
        exact (uM_store8_lookup_ne M (uint sp0 - 8) (m !!! Regidx ra_idx) k
                 ltac:(intros i Hi; lia)). }
    assert (Hrd2 : uv_rd pt M2 s (len + 1))
      by exact (uM_only_rd pt M M2 s (len + 1) (uint sp0 - 16) 16
                  Honly ltac:(lia) Hrd).
    assert (Hstr2 : ucstr M2 s len)
      by exact (uM_only_cstr M M2 s len (uint sp0 - 16) 16 Honly ltac:(lia) Hstr).
    (* ---- 0xe2  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Ψxv6 M2 m1 (mword_of_int 0xe2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_echo_e2 pt M2 Hlay Htext2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (Ee2 : add_vec_int (mword_of_int 0xe2 : mword 64) 2 = mword_of_int 0xe4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ee2) in "Hpc".
    (* ---- 0xe4  lbu a5,0(a0) -- the first byte of the string ---- *)
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int (uint sp0) : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m (Regidx sp_idx) (Regidx a0_idx)
                     (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))
                     ltac:(vm_compute; discriminate))
                  Hs)). }
    assert (Hvas : (mword_of_int s : mword 64)
                   = add_vec (m2 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha0_2.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M2 s (len + 1) s Hrd2 ltac:(lia)) as (we & Hle & Hoke).
    assert (Hbex : exists b0 : bv 8, M2 !! s = Some b0 /\ (b0 = ubyte0 <-> len = 0)).
    { destruct (Z.eq_dec len 0) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr2) as Hnul.
        replace (s + len) with s in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr2 0 ltac:(lia)) as (b & Hb & Hbz).
        replace (s + 0) with s in Hb by lia.
        exists b. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hbz He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (b0 & Hb0e & Hb0iff).
    assert (Huvas : uint (mword_of_int s : mword 64) = s)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hbytes : M2 !! (uint (mword_of_int s : mword 64)) = Some b0)
      by (rewrite Huvas; exact Hb0e).
    assert (Hcanons : uva_canon (mword_of_int s : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwv0 : (mword_of_int (bv_unsigned b0) : mword 64)
                   = zero_extend' 64 (b0 : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Ψxv6 M2 m2 (mword_of_int 0xe4)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              we (mword_of_int s) (mword_of_int (bv_unsigned b0)) b0
              (ui_echo_e4 pt M2 Hlay Htext2)
              ltac:(vm_compute; discriminate) Hvas Hle Hoke Hcanons Hbytes Hwv0
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> m2).
    assert (Ee4 : add_vec_int (mword_of_int 0xe4 : mword 64) 4 = mword_of_int 0xe8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ee4) in "Hpc".
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq m2 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx a0_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))
                  ltac:(vm_compute; discriminate))
               Ha0_2). }
    assert (Hsp3 : m3 !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m1 (Regidx s0_idx) (Regidx sp_idx)
                     (regval_into_reg (mword_of_int (uint sp0) : mword 64))
                     ltac:(vm_compute; discriminate))
                  (upd_eq m (Regidx sp_idx)
                     (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))))). }
    (* what the PROLOGUE left of every register the epilogue does not restore *)
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx a5_idx -> m3 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0 Na5.
      exact (eq_trans
               (upd_ne m2 (Regidx a5_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)) Na5)
               (eq_trans
                  (upd_ne m1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (uint sp0) : mword 64)) Ns0)
                  (upd_ne m (Regidx sp_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))
                     Nsp))). }
    assert (Htgt : (mword_of_int 0x104 : mword 64)
                   = add_vec (mword_of_int 0xe8)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 14 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xe8  c.beqz a5,0x104 ---- *)
    destruct (Z.eq_dec len 0) as [Hlz | Hlne].
    - (* THE EMPTY STRING: a0 := 0 at 0x104, then jump to the epilogue *)
      subst len.
      assert (Hz : bv_unsigned b0 = 0)
        by (apply bv8_zero; apply Hb0iff; reflexivity).
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)) Hz. reflexivity. }
      iApply (wp_uv_cbeqz C pt Ψxv6 M2 m3 (mword_of_int 0xe8)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                true (mword_of_int 0x104)
                (ui_echo_e8 pt M2 Hlay Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      (* ---- 0x104  c.li a0,0 ---- *)
      assert (Hwa0 : (mword_of_int 0 : mword 64)
                     = add_vec zero_reg
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cli C pt Ψxv6 M2 m3 (mword_of_int 0x104)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (ui_echo_104 pt M2 Hlay Htext2)
                ltac:(vm_compute; discriminate) Hwa0
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (m4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m3).
      assert (E104 : add_vec_int (mword_of_int 0x104 : mword 64) 2 = mword_of_int 0x106)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E104) in "Hpc".
      (* ---- 0x106  c.j 0xfc ---- *)
      assert (Htj : (mword_of_int 0xfc : mword 64)
                    = add_vec (mword_of_int 0x106)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cj C pt Ψxv6 M2 m4 (mword_of_int 0x106)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xfc)
                (ui_echo_106 pt M2 Hlay Htext2)
                Htj ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID8) "Hcg Hpc".
      (* ---- the epilogue ---- *)
      assert (Hsp4 : m4 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 16) : mword 64)).
      { exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx sp_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))
                    ltac:(vm_compute; discriminate)) Hsp3). }
      iApply (wp_echo_strlen_epi CID8 M m4 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hlay Htext Hst Hret2 Hsp4 with "Hcg Hpc").
      iIntros (CID9 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID9 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx r)
                    (regval_into_reg (mword_of_int 0 : mword 64)) Na0)
                 (Hpre r Nsp Ns0 Na5)).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg (mword_of_int 0 : mword 64))).
      + iPureIntro. exact Honly.
    - (* A NON-EMPTY STRING: a5 := s+1, scan, then subw ---- *)
      assert (Hnz : bv_unsigned b0 <> 0)
        by (intro Hz; apply Hlne; apply Hb0iff; apply bv8_zero; exact Hz).
      assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)).
        symmetry. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uv_cbeqz C pt Ψxv6 M2 m3 (mword_of_int 0xe8)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                false (mword_of_int 0x104)
                (ui_echo_e8 pt M2 Hlay Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      assert (Ee8 : (if false then (mword_of_int 0x104 : mword 64)
                     else add_vec_int (mword_of_int 0xe8 : mword 64) 2)
                    = mword_of_int 0xea)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ee8) in "Hpc".
      (* ---- 0xea  addi a5,a0,1 ---- *)
      assert (Hadd1 : (mword_of_int (s + 1) : mword 64)
                      = add_vec (m3 !!! Regidx a0_idx)
                          (sign_extend' 64 (mword_of_int 1 : mword 12))).
      { rewrite Ha0_3.
        assert (Hc : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. reflexivity. }
      iApply (wp_uv_addi C pt Ψxv6 M2 m3 (mword_of_int 0xea)
                (mword_of_int 1 : mword 12) a0_idx a5_idx (mword_of_int (s + 1))
                (ui_echo_ea pt M2 Hlay Htext2)
                ltac:(vm_compute; discriminate) Hadd1
                with "Hcg Hpc").
      iIntros (CID7) "Hcg Hpc".
      set (m4 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (s + 1) : mword 64)]> m3).
      assert (Eea : add_vec_int (mword_of_int 0xea : mword 64) 4 = mword_of_int 0xee)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eea) in "Hpc".
      (* ---- 0xee..0xf6  the scan loop ---- *)
      assert (Ha5_4 : m4 !!! Regidx a5_idx = (mword_of_int (s + 1 + 0) : mword 64)).
      { replace (s + 1 + 0) with (s + 1) by lia.
        exact (upd_eq m3 (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (s + 1) : mword 64))). }
      iApply (wp_echo_strlen_loop (S (Z.to_nat (len - 1))) CID7 M2 m4 s len 0
                ltac:(lia) Hlay Htext2 Hstr2 Hrd2 ltac:(lia) Ha5_4
                with "Hcg Hpc").
      iIntros (CID8 m5) "%Ha3_5 %Hpres5 Hcg Hpc".
      (* ---- 0xf8  subw a0,a3,a0 ---- *)
      assert (Ha0_5 : m5 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
      { rewrite (Hpres5 a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx a0_idx)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64))
                    ltac:(vm_compute; discriminate)) Ha0_3). }
      assert (Hsub : (mword_of_int len : mword 64)
                     = sign_extend' 64
                         (sub_vec (subrange_vec_dec (m5 !!! Regidx a3_idx) 31 0
                                   : mword 32)
                                  (subrange_vec_dec (m5 !!! Regidx a0_idx) 31 0
                                   : mword 32))).
      { rewrite Ha3_5 Ha0_5 (moi_subw (s + len) s ltac:(unfold Z31; lia)).
        f_equal; lia. }
      iApply (wp_uv_subw C pt Ψxv6 M2 m5 (mword_of_int 0xf8)
                a3_idx a0_idx a0_idx (mword_of_int len)
                (ui_echo_f8 pt M2 Hlay Htext2)
                ltac:(vm_compute; discriminate) Hsub
                with "Hcg Hpc").
      iIntros (CID9) "Hcg Hpc".
      set (m6 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int len : mword 64)]> m5).
      assert (Ef8 : add_vec_int (mword_of_int 0xf8 : mword 64) 4 = mword_of_int 0xfc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ef8) in "Hpc".
      (* ---- the epilogue ---- *)
      assert (Hsp6 : m6 !!! Regidx sp_idx
                     = (mword_of_int (uint sp0 - 16) : mword 64)).
      { rewrite (upd_ne m5 (Regidx a0_idx) (Regidx sp_idx)
                   (regval_into_reg (mword_of_int len : mword 64))
                   ltac:(vm_compute; discriminate)).
        rewrite (Hpres5 sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx sp_idx)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64))
                    ltac:(vm_compute; discriminate)) Hsp3). }
      iApply (wp_echo_strlen_epi CID9 M m6 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hlay Htext Hst Hret2 Hsp6 with "Hcg Hpc").
      iIntros (CID10 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID10 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na3 : Regidx r <> Regidx a3_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na4 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        rewrite (upd_ne m5 (Regidx a0_idx) (Regidx r)
                   (regval_into_reg (mword_of_int len : mword 64)) Na0).
        rewrite (Hpres5 r Na3 Na4 Na5).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx r)
                    (regval_into_reg (mword_of_int (s + 1) : mword 64)) Na5)
                 (Hpre r Nsp Ns0 Na5)).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m5 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int len : mword 64))).
      + iPureIntro. exact Honly.
  Qed.

End UProofEchoA.

(* sentinel: strlen -- the first verified user function with a loop, with a
   memory read, and with a computed return value -- rests on nothing but the
   platform axioms and functional extensionality *)
Print Assumptions wp_echo_strlen.
