(* UmodeFrame.v -- THE gcc 16-BYTE FRAME, once.
   (claude-notes/projects/user-verified.md is the tier; user-echo.md and
   user-sh.md are the programs that made this file necessary.)

   Every leaf C function gcc compiles for rv64 with -O opens and closes with
   the same eight instructions:

     <pro>+0  c.addi  sp,sp,-16      <epi>+0  c.ldsp  ra,8(sp)
     <pro>+2  c.sdsp  ra,8(sp)       <epi>+2  c.ldsp  s0,0(sp)
     <pro>+4  c.sdsp  s0,0(sp)       <epi>+4  c.addi  sp,sp,16
     <pro>+6  c.addi4spn s0,sp,16    <epi>+6  c.jr    ra

   sh alone has five of them ([strlen], [strchr], [sbrk], [memset], and the
   frame of every parser routine); echo has one.  Replaying those eight
   instructions per function is ~140 lines of identical bitvector plumbing
   each, so they are proved HERE, once, and every consumer supplies only
   what actually varies:

     - the ENTRY ADDRESS ([pro] / [epi]), as a [Z];
     - the eight [uinstr] facts, one per pc, out of the program's own
       UCode<Prog>.v catalog;
     - the four pc ticks, each a [vm_compute] at the call site;
     - the SYSCALL PROTOCOL [Ps], which the frame never inspects;
     - and, for the prologue only, an ABSTRACT image predicate [T] -- in
       practice "this program's text is present in the image" -- with the
       one closure property a frame carve needs: [T] survives an 8-byte
       store at or above [lim], the program image's key bound.  That single
       premise is what replaces a per-program [<prog>_text_sub_store8].

   So nothing here is about any particular program OR any particular
   protocol; only the section's [C] / [pt] remain.

   The epilogue takes the two reloaded words as PREMISES
   ([uM_word Mx (uint sp0 - 8) 8 = v8], likewise for [v0]) rather than
   hard-coding the store tower a prologue leaves behind.  That is what lets
   a function whose callee CHANGED the image in between -- sh's [sbrk],
   whose [sys_sbrk] call grows the heap between the spill and the reload --
   reuse it unchanged.

   Both exits are stated POINTWISE over the registers (x1/x2/x8 by value,
   everything else unchanged) rather than as an insert tower: a caller owes
   [ucallee_saved], whose index is a VARIABLE, and a tower cannot be peeled
   at one. *)
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
Require Import AlignBits UserBits.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeFetch.
Require Import WpUmodeStep WpUmodeLeaf WpUmodeStore WpUmodeLoad.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

Section UmodeFrame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* the ABI index UmodeAbi.v does not name (it names only ra/sp/a0/a1/a2) *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).

  (* [uv_stack_slot] with the slot address NORMALIZED (UProofEchoA's shim) *)
  Lemma uv_slot16 (M : gmap Z (bv 8)) (sp0 : mword 64) (d a : Z) :
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

  (* ---- the PROLOGUE: addi sp,-16 ; sd ra,8 ; sd s0,0 ; addi s0,sp,16 --
     PROGRAM- AND PROTOCOL-GENERIC: the entry address, the syscall protocol
     [Ps], the four [uinstr] facts and each pc tick are all parameters, and
     the image side is an ABSTRACT predicate [T] (in practice "this
     program's text is present") together with the one closure property a
     frame carve needs -- [T] survives an 8-byte store at or above [lim],
     the image's key bound.  Nothing about sh is left, so this belongs in a
     shared file beside WpUmodeStore.v. *)
  Lemma wp_uv_prologue16 (CIDp : CpuId) (Ps : usys_protocol Σ) (pro : Z)
      (T : gmap Z (bv 8) -> Prop) (lim : Z)
      (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    T M ->
    (forall (Mx : gmap Z (bv 8)) (a : Z) (v : mword 64),
       T Mx -> lim <= a -> T (uM_store8 Mx a v)) ->
    lim <= uint sp0 - 16 ->
    m !!! Regidx sp_idx = sp0 ->
    uv_stack pt M sp0 16 ->
    uinstr pt M (mword_of_int pro) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx sp_idx)) ->
    (forall Mx : gmap Z (bv 8), T Mx ->
       uinstr pt Mx (mword_of_int (pro + 2)) true
         (C_SDSP (mword_of_int 1 : mword 6, Regidx ra_idx))) ->
    (forall Mx : gmap Z (bv 8), T Mx ->
       uinstr pt Mx (mword_of_int (pro + 4)) true
         (C_SDSP (mword_of_int 0 : mword 6, Regidx s0_idx))) ->
    (forall Mx : gmap Z (bv 8), T Mx ->
       uinstr pt Mx (mword_of_int (pro + 6)) true
         (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8))) ->
    add_vec_int (mword_of_int pro : mword 64) 2 = mword_of_int (pro + 2) ->
    add_vec_int (mword_of_int (pro + 2) : mword 64) 2 = mword_of_int (pro + 4) ->
    add_vec_int (mword_of_int (pro + 4) : mword 64) 2 = mword_of_int (pro + 6) ->
    add_vec_int (mword_of_int (pro + 6) : mword 64) 2 = mword_of_int (pro + 8) ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) (mword_of_int pro) -∗
    (∀ CID : CpuId,
       uv_cap_gpr (CID := CID) C pt Ps
         (uM_store8 (uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx))
            (uint sp0 - 16) (m !!! Regidx s0_idx))
         (<[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
            (<[Regidx sp_idx := (mword_of_int (uint sp0 - 16) : mword 64)]> m)) -∗
       pc_is (CID := CID) (mword_of_int (pro + 8)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HT HTst Hlim Hsp Hst Hu0 Hu2 Hu4 Hu6 E0 E2 E4 E6.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    destruct (uv_slot16 M sp0 8 (uint sp0 - 8) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hq8 & (w8 & Hl8 & Hok8s & _) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uv_slot16 M sp0 0 (uint sp0 - 16) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hq0 & (w0 & Hl0 & Hok0s & _) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    iIntros "Hcg Hpc Hcont".
    (* ---- pro  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi C pt Ps M m (mword_of_int pro)
              (mword_of_int 48 : mword 6) sp_idx (mword_of_int (uint sp0 - 16))
              Hu0 ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx sp_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)]> m).
    iEval (rewrite E0) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (upd_eq m (Regidx sp_idx)
                  (regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64))).
    (* ---- pro+2  c.sdsp ra,8(sp) ---- *)
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
    iApply (wp_uv_csdsp C pt Ps M m1 (mword_of_int (pro + 2))
              (mword_of_int 1 : mword 6) ra_idx
              w8 (mword_of_int (uint sp0 - 8)) (m !!! Regidx ra_idx)
              (Hu2 M HT)
              Htg8 Hwra Hl8 Hok8s Hcanon8 Hpg8 Hal8 Hb8
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hq8) in "Hcg".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (HT1 : T M1)
      by (unfold M1; apply HTst; [ exact HT | lia ]).
    iEval (rewrite E2) in "Hpc".
    (* ---- pro+4  c.sdsp s0,0(sp) ---- *)
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
    iApply (wp_uv_csdsp C pt Ps M1 m1 (mword_of_int (pro + 4))
              (mword_of_int 0 : mword 6) s0_idx
              w0 (mword_of_int (uint sp0 - 16)) (m !!! Regidx s0_idx)
              (Hu4 M1 HT1)
              Htg0 Hws0 Hl0 Hok0s Hcanon0 Hpg0 Hal0 Hb0'
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite Hq0) in "Hcg".
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    assert (HT2 : T M2)
      by (unfold M2; apply HTst; [ exact HT1 | lia ]).
    iEval (rewrite E4) in "Hpc".
    (* ---- pro+6  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Ps M2 m1 (mword_of_int (pro + 6))
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (Hu6 M2 HT2)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite E6) in "Hpc".
    iApply ("Hcont" $! CID4 with "Hcg Hpc").
  Qed.

  (* ---- the EPILOGUE: ld ra,8 ; ld s0,0 ; addi sp,16 ; ret ------------- *)
  Lemma wp_uv_epilogue16 (CIDp : CpuId) (Ps : usys_protocol Σ) (epi : Z)
      (Mx : gmap Z (bv 8)) (mF : regfile) (sp0 v8 v0 : mword 64) :
    uv_stack pt Mx sp0 16 ->
    is_aligned_vaddr (Virtaddr v8) 2 = true ->
    mF !!! Regidx sp_idx = (mword_of_int (uint sp0 - 16) : mword 64) ->
    uM_word Mx (uint sp0 - 8) 8 = v8 ->
    uM_word Mx (uint sp0 - 16) 8 = v0 ->
    uinstr pt Mx (mword_of_int epi) true
      (C_LDSP (mword_of_int 1 : mword 6, Regidx ra_idx)) ->
    uinstr pt Mx (mword_of_int (epi + 2)) true
      (C_LDSP (mword_of_int 0 : mword 6, Regidx s0_idx)) ->
    uinstr pt Mx (mword_of_int (epi + 4)) true
      (C_ADDI (mword_of_int 16 : mword 6, Regidx sp_idx)) ->
    uinstr pt Mx (mword_of_int (epi + 6)) true (C_JR (Regidx ra_idx)) ->
    add_vec_int (mword_of_int epi : mword 64) 2 = mword_of_int (epi + 2) ->
    add_vec_int (mword_of_int (epi + 2) : mword 64) 2 = mword_of_int (epi + 4) ->
    add_vec_int (mword_of_int (epi + 4) : mword 64) 2 = mword_of_int (epi + 6) ->
    uv_cap_gpr (CID := CIDp) C pt Ps Mx mF -∗
    pc_is (CID := CIDp) (mword_of_int epi) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜m' !!! Regidx sp_idx = sp0⌝ -∗
       ⌜m' !!! Regidx s0_idx = v0⌝ -∗
       ⌜forall r : mword 5,
          Regidx r <> Regidx ra_idx -> Regidx r <> Regidx sp_idx ->
          Regidx r <> Regidx s0_idx -> m' !!! Regidx r = mF !!! Regidx r⌝ -∗
       uv_cap_gpr (CID := CID) C pt Ps Mx m' -∗
       pc_is (CID := CID) v8 -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hst Hret2 Hsp Hw8 Hw0 Hu0 Hu2 Hu4 Hu6 E0 E2 E4.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    destruct (uv_slot16 Mx sp0 8 (uint sp0 - 8) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hq8 & (w8 & Hl8 & _ & Hok8) & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uv_slot16 Mx sp0 0 (uint sp0 - 16) Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia))
      as (Hq0 & (w0 & Hl0 & _ & Hok0) & Hcanon0 & Hpg0 & Hal0 & Hb0).
    iIntros "Hcg Hpc Hcont".
    (* ---- epi  c.ldsp ra,8(sp) ---- *)
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
    assert (Hwv8 : v8 = uM_word Mx (uint (mword_of_int (uint sp0 - 8) : mword 64)) 8)
      by (rewrite Hq8; symmetry; exact Hw8).
    iApply (wp_uv_cldsp C pt Ps Mx mF (mword_of_int epi)
              (mword_of_int 1 : mword 6) ra_idx
              w8 (mword_of_int (uint sp0 - 8)) v8
              Hu0 ltac:(vm_compute; discriminate) Hva8 Hl8 Hok8 Hcanon8 Hpg8
              Hal8 Hb8 Hwv8
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mF1 := <[Regidx ra_idx := regval_into_reg v8]> mF).
    iEval (rewrite E0) in "Hpc".
    (* ---- epi+2  c.ldsp s0,0(sp) ---- *)
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
    assert (Hwv0 : v0 = uM_word Mx (uint (mword_of_int (uint sp0 - 16) : mword 64)) 8)
      by (rewrite Hq0; symmetry; exact Hw0).
    iApply (wp_uv_cldsp C pt Ps Mx mF1 (mword_of_int (epi + 2))
              (mword_of_int 0 : mword 6) s0_idx
              w0 (mword_of_int (uint sp0 - 16)) v0
              Hu2 ltac:(vm_compute; discriminate) Hva0 Hl0 Hok0 Hcanon0 Hpg0
              Hal0 Hb0 Hwv0
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mF2 := <[Regidx s0_idx := regval_into_reg v0]> mF1).
    iEval (rewrite E2) in "Hpc".
    (* ---- epi+4  c.addi sp,sp,16 ---- *)
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
    iApply (wp_uv_caddi C pt Ps Mx mF2 (mword_of_int (epi + 4))
              (mword_of_int 16 : mword 6) sp_idx sp0
              Hu4 ltac:(vm_compute; discriminate) Hwsp
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mF3 := <[Regidx sp_idx := regval_into_reg sp0]> mF2).
    iEval (rewrite E4) in "Hpc".
    (* ---- epi+6  c.jr ra ---- *)
    assert (Hra3 : mF3 !!! Regidx ra_idx = v8).
    { exact (eq_trans
               (upd_ne mF2 (Regidx sp_idx) (Regidx ra_idx)
                  (regval_into_reg sp0) ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mF1 (Regidx s0_idx) (Regidx ra_idx)
                     (regval_into_reg v0) ltac:(vm_compute; discriminate))
                  (upd_eq mF (Regidx ra_idx) (regval_into_reg v8)))). }
    assert (Htgt : v8 = ret_pc (mF3 !!! Regidx ra_idx)).
    { rewrite Hra3. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Ps Mx mF3 (mword_of_int (epi + 6))
              ra_idx v8 Hu6 ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
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
  (* THE FRAME SLOT, store and load.                                      *)
  (*                                                                      *)
  (* [c.sdsp rs2,d(sp)] / [c.ldsp rd,d(sp)] with sp at the BOTTOM of a     *)
  (* budget: the address is [sp0 - n + d], every side condition comes off  *)
  (* [uv_stack_slot_moi], and the image effect is one [uM_store8].  These  *)
  (* two are what a prologue and an epilogue are made of at ANY frame      *)
  (* size, so they generalize [wp_uv_prologue16] / [wp_uv_epilogue16]      *)
  (* below the point where the 16-byte layout is fixed.                    *)
  (*                                                                      *)
  (* (UProofEcho.v's [echo_pro_store] is the same lemma pinned to one      *)
  (* protocol; init needs it at frame sizes 16, 32 and 96, which is what   *)
  (* made hoisting it worthwhile.)                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_frame_store (CIDp : CpuId) (Ps : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
      (uimm : mword 6) (rs2 : mword 5) (n d : Z) :
    uinstr pt M pc true (C_SDSP (uimm, Regidx rs2)) ->
    uv_stack pt M sp0 n ->
    0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - n) : mword 64) ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ps
         (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui HS Hd0 Hdn Hd8 Hsp Himm.
    destruct (uv_stack_slot_moi pt M sp0 n d (mword_of_int (uint sp0 - n + d))
                HS Hd0 Hdn Hd8 eq_refl)
      as (Hu & (w & Hl & Hok & _) & Hcanon & Hpg & Hal & Hb).
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_csdsp C pt Ps M m pc uimm rs2 w
              (mword_of_int (uint sp0 - n + d)) (m !!! Regidx rs2)
              Hui
              ltac:(rewrite Hsp; rewrite Himm; rewrite moi_add; reflexivity)
              eq_refl Hl Hok Hcanon Hpg Hal Hb
              with "Hcg Hpc [Hcont]").
    iIntros (CID0) "Hcg Hpc".
    iEval (rewrite Hu) in "Hcg".
    iApply ("Hcont" with "Hcg Hpc").
  Qed.

  Lemma wp_uv_frame_load (CIDp : CpuId) (Ps : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
      (uimm : mword 6) (rd : mword 5) (n d : Z) (wval : mword 64) :
    uinstr pt M pc true (C_LDSP (uimm, Regidx rd)) ->
    uint rd <> 0 ->
    uv_stack pt M sp0 n ->
    0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - n) : mword 64) ->
    (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64)
      = mword_of_int d ->
    wval = uM_word M (uint sp0 - n + d) 8 ->
    uv_cap_gpr (CID := CIDp) C pt Ps M m -∗
    pc_is (CID := CIDp) pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ps M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd HS Hd0 Hdn Hd8 Hsp Himm Hwv.
    destruct (uv_stack_slot_moi pt M sp0 n d (mword_of_int (uint sp0 - n + d))
                HS Hd0 Hdn Hd8 eq_refl)
      as (Hu & (w & Hl & _ & Hok) & Hcanon & Hpg & Hal & Hb).
    iIntros "Hcg Hpc Hcont".
    assert (Hva : (mword_of_int (uint sp0 - n + d) : mword 64)
                  = add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))))
      by (rewrite Hsp; rewrite Himm; rewrite moi_add; reflexivity).
    iApply (wp_uv_cldsp C pt Ps M m pc uimm rd w
              (mword_of_int (uint sp0 - n + d)) wval
              Hui Hrd Hva Hl Hok Hcanon Hpg Hal Hb
              ltac:(rewrite Hu; exact Hwv)
              with "Hcg Hpc Hcont").
  Qed.

End UmodeFrame.
