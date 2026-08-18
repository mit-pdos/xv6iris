(* UProofInit.v -- init's [main] and [start], and THE TOP THEOREM.
   (claude-notes/projects/user-init.md; the contracts are USpecInit.v.)

   main is the first UNBOUNDED loop in the verified-user tier, and it has
   two, nested:

     the RESTART loop  head 0x32, back edge [beq s1,a0,32] at 0x4a
     the WAIT loop     head 0x44, back edge [bgez a0,44]   at 0x4e

   Both are closed with [iLoeb] through the [|>]-exposing branch leaves
   ([WpUmodeBranch.wp_uv_btype_later] / [wp_uv_btype0_later]) -- a later-
   free leaf can never strip a [|>]-guarded IH, which is exactly the rule
   design/kernel-proofs.md states and the reason those leaves exist.

   EVERY BRANCH IS PROVED, both ways.  init's protocol returns an
   arbitrary value from every syscall, so the proof never learns what
   [open], [fork] or [wait] returned; it simply [destruct]s the branch
   condition and discharges both arms.  That is what makes init's theorem
   assumption-free where sh's needs three.

   The loop invariant is small, because main never returns: its own frame
   is written once in the prologue and never read again (there is no
   epilogue), and everything below it belongs to [printf].  What is
   carried is the image, the stack budget, sp, and s2 -- the register
   holding the address of "init: starting sh\n". *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import InstrBytes RegFile.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo
               UmodeInitIo UmodeFetch.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore.
Require Import UmodeFrame.
Require Import UCodeInit USpecInit UProofInitLib UProofInitPrintf.
Require User.InitSyms User.InitInstrs User.InitData.
Local Open Scope Z_scope.
Import Defs.
Import ListNotations.
Set Printing Depth 40.

(* every byte of one of init's four messages is a byte [W] may observe *)
Lemma init_msg_sub (bs : list (bv 8)) (b : bv 8) :
  bs = init_msg_sh \/ bs = init_msg_fork \/ bs = init_msg_exec \/
  bs = init_msg_wait ->
  b ∈ bs -> b ∈ init_msg_bytes.
Proof.
  intros Hbs Hb. unfold init_msg_bytes.
  destruct Hbs as [ -> | [ -> | [ -> | -> ] ] ];
    rewrite ?elem_of_app; tauto.
Qed.

Section UProofInit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).
  Context (W : Z -> list (bv 8) -> iProp Σ).

  Local Notation Pinit := (xv6_init_protocol C pt Q W).

  (* ------------------------------------------------------------------- *)
  (* §1 THE DIAGNOSTIC TAIL, which init has three of (fork failed, exec sh *)
  (* failed, wait returned an error):                                      *)
  (*   e    auipc a0,0x1 ; e+4 addi a0,a0,<msg> ; e+8 jal printf           *)
  (*   e+12 li a0,1      ; e+14 jal exit                                   *)
  (* Address-generic, so the three sites are three instantiations.         *)
  (* ------------------------------------------------------------------- *)
  Lemma init_diag_exit (CIDp : CpuId) (e ai jp je msg : Z) (bs : list (bv 8))
      (M : gmap Z (bv 8)) (m : regfile) (spx : mword 64) :
    init_layout pt ->
    init_img_sub M ->
    uv_stack pt M spx 224 ->
    8192 <= uint spx - 224 ->
    m !!! Regidx csp_rs1 = spx ->
    init_lit M msg bs ->
    (forall Mx : gmap Z (bv 8), init_text_sub Mx ->
       uinstr pt Mx (mword_of_int e) false
         (UTYPE (mword_of_int 1 : mword 20, Regidx a0_idx, AUIPC))) ->
    (forall Mx : gmap Z (bv 8), init_text_sub Mx ->
       uinstr pt Mx (mword_of_int (e + 4)) false
         (ITYPE (mword_of_int ai : mword 12, Regidx a0_idx, Regidx a0_idx, ADDI))) ->
    (forall Mx : gmap Z (bv 8), init_text_sub Mx ->
       uinstr pt Mx (mword_of_int (e + 8)) false
         (JAL (mword_of_int jp : mword 21, Regidx ra_idx))) ->
    (forall Mx : gmap Z (bv 8), init_text_sub Mx ->
       uinstr pt Mx (mword_of_int (e + 12)) true
         (C_LI (mword_of_int 1 : mword 6, Regidx a0_idx))) ->
    (forall Mx : gmap Z (bv 8), init_text_sub Mx ->
       uinstr pt Mx (mword_of_int (e + 14)) false
         (JAL (mword_of_int je : mword 21, Regidx ra_idx))) ->
    add_vec (mword_of_int e : mword 64) (auipc_off (mword_of_int 1 : mword 20))
      = mword_of_int (e + 4096) ->
    (sign_extend' 64 (mword_of_int ai : mword 12) : mword 64)
      = mword_of_int (msg - (e + 4096)) ->
    add_vec (mword_of_int (e + 8) : mword 64)
      (sign_extend' 64 (mword_of_int jp : mword 21)) = mword_of_int 0x7c0 ->
    add_vec (mword_of_int (e + 14) : mword 64)
      (sign_extend' 64 (mword_of_int je : mword 21)) = mword_of_int 0x372 ->
    add_vec_int (mword_of_int e : mword 64) 4 = mword_of_int (e + 4) ->
    add_vec_int (mword_of_int (e + 4) : mword 64) 4 = mword_of_int (e + 8) ->
    add_vec_int (mword_of_int (e + 8) : mword 64) 4 = mword_of_int (e + 12) ->
    add_vec_int (mword_of_int (e + 12) : mword 64) 2 = mword_of_int (e + 14) ->
    add_vec_int (mword_of_int (e + 14) : mword 64) 4 = mword_of_int (e + 18) ->
    is_aligned_vaddr (Virtaddr (mword_of_int (e + 12) : mword 64)) 2 = true ->
    init_wobs W 1 bs -∗
    uv_cap_gpr (CID := CIDp) C pt Pinit M m -∗
    pc_is (CID := CIDp) (mword_of_int e) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Himg Hst Hfr Hspx Hlit Hu0 Hu4 Hu8 Hu12 Hu14
           Eau Eai Ejp Eje Et0 Et4 Et8 Et12 Et14 Hal12.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    iIntros "#Hwobs Hcg Hpc".

    (* ---- e  auipc a0,0x1 ---- *)
    iApply (wp_uv_auipc C pt Pinit M m (mword_of_int e)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int (e + 4096))
              (Hu0 M (init_img_text M Himg))
              ltac:(vm_compute; discriminate) ltac:(symmetry; exact Eau)
              with "Hcg Hpc").
    iIntros (X1) "Hcg Hpc".
    set (d1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (e + 4096) : mword 64)]> m).
    assert (Hd1a0 : d1 !!! Regidx a0_idx = (mword_of_int (e + 4096) : mword 64))
      by exact (upd_eq m (Regidx a0_idx) _).
    iEval (rewrite Et0) in "Hpc".

    (* ---- e+4  addi a0,a0,<msg - (e+4096)> ---- *)
    iApply (wp_uv_addi C pt Pinit M d1 (mword_of_int (e + 4))
              (mword_of_int ai : mword 12) a0_idx a0_idx (mword_of_int msg)
              (Hu4 M (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hd1a0; rewrite Eai; rewrite moi_add; f_equal; lia)
              with "Hcg Hpc").
    iIntros (X2) "Hcg Hpc".
    set (d2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int msg : mword 64)]> d1).
    assert (Hd2a0 : d2 !!! Regidx a0_idx = (mword_of_int msg : mword 64))
      by exact (upd_eq d1 (Regidx a0_idx) _).
    assert (Hd2sp : d2 !!! Regidx csp_rs1 = spx).
    { refine (eq_trans (upd_ne d1 (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne m (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hspx. }
    iEval (rewrite Et4) in "Hpc".

    (* ---- e+8  jal printf ---- *)
    iApply (wp_uv_jal C pt Pinit M d2 (mword_of_int (e + 8))
              (mword_of_int jp : mword 21) ra_idx
              (mword_of_int 0x7c0) (mword_of_int (e + 12))
              (Hu8 M (init_img_text M Himg))
              ltac:(vm_compute; discriminate) ltac:(symmetry; exact Ejp)
              ltac:(symmetry; exact Et8) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (X3) "Hcg Hpc".
    set (d3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int (e + 12) : mword 64)]> d2).
    assert (Hd3a0 : d3 !!! Regidx a0_idx = (mword_of_int msg : mword 64))
      by exact (eq_trans (upd_ne d2 (Regidx ra_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)) Hd2a0).
    assert (Hd3sp : d3 !!! Regidx csp_rs1 = spx)
      by exact (eq_trans (upd_ne d2 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hd2sp).
    assert (Hd3ra : d3 !!! Regidx ra_idx = (mword_of_int (e + 12) : mword 64))
      by exact (upd_eq d2 (Regidx ra_idx) _).
    iEval (change (mword_of_int 0x7c0 : mword 64)
             with (mword_of_int InitSyms.printf : mword 64)) in "Hpc".
    iApply (wp_init_printf C pt Q W X3 M d3 spx msg bs
              Hlay Himg Hd3sp Hst ltac:(unfold init_frame_ok; lia)
              Hd3a0 Hlit ltac:(rewrite Hd3ra; exact Hal12)
              with "Hcg Hwobs Hpc []").
    iIntros (X4 m4 M4) "%Hcs4 %Ho4 Hcg Hpc".
    iEval (rewrite Hd3ra) in "Hpc".
    assert (Himg4 : init_img_sub M4)
      by exact (init_img_only M M4 (uint spx - 224) 224 ltac:(lia) Ho4 Himg).

    (* ---- e+12  li a0,1 ---- *)
    iApply (wp_uv_cli C pt Pinit M4 m4 (mword_of_int (e + 12))
              (mword_of_int 1 : mword 6) a0_idx (mword_of_int 1)
              (Hu12 M4 (init_img_text M4 Himg4))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (X5) "Hcg Hpc".
    set (d4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m4).
    iEval (rewrite Et12) in "Hpc".

    (* ---- e+14  jal exit ---- *)
    iApply (wp_uv_jal C pt Pinit M4 d4 (mword_of_int (e + 14))
              (mword_of_int je : mword 21) ra_idx
              (mword_of_int 0x372) (mword_of_int (e + 18))
              (Hu14 M4 (init_img_text M4 Himg4))
              ltac:(vm_compute; discriminate) ltac:(symmetry; exact Eje)
              ltac:(symmetry; exact Et14) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (X6) "Hcg Hpc".
    set (d5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int (e + 18) : mword 64)]> d4).
    iEval (change (mword_of_int 0x372 : mword 64)
             with (mword_of_int InitSyms.exit : mword 64)) in "Hpc".
    iApply (wp_init_exit C pt Q W X6 M4 d5 Hlay (init_img_text M4 Himg4)
              with "Hcg Hpc").
  Qed.

  (* every message is a sub-list of the observable set *)
  Lemma init_wobs_sub (bs : list (bv 8)) :
    bs = init_msg_sh \/ bs = init_msg_fork \/ bs = init_msg_exec \/
    bs = init_msg_wait ->
    init_wobs W 1 init_msg_bytes -∗ init_wobs W 1 bs.
  Proof.
    intro Hbs. iIntros "#Hall". rewrite /init_wobs. iModIntro.
    iIntros (b) "%Hb". iApply ("Hall" $! b). iPureIntro.
    exact (init_msg_sub bs b Hbs Hb).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 THE TWO NESTED UNBOUNDED LOOPS.                                    *)
  (*                                                                      *)
  (*   0x32 mv a0,s2 ; jal printf ; jal fork ; mv s1,a0                    *)
  (*   0x3e bltz a0,84    (fork failed -> diagnostic, exit)                *)
  (*   0x42 beqz a0,96    (child      -> exec "sh")                        *)
  (*   0x44 li a0,0 ; jal wait                                             *)
  (*   0x4a beq s1,a0,32  (the shell exited -> RESTART)                    *)
  (*   0x4e bgez a0,44    (some other child -> WAIT again)                 *)
  (*   0x52 diagnostic, exit                                               *)
  (* ------------------------------------------------------------------- *)
  Lemma init_main_loop (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    init_layout pt ->
    8192 <= uint sp0 - 256 ->
    init_img_sub M ->
    uv_stack pt M sp0 256 ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64) ->
    m !!! Regidx (mword_of_int 18 : mword 5)
      = (mword_of_int INIT_MSG_SH : mword 64) ->
    init_obs Q W -∗
    uv_cap_gpr (CID := CIDp) C pt Pinit M m -∗
    pc_is (CID := CIDp) (mword_of_int 0x32) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hfr Himg0 Hst0 Hsp0 Hs20.
    iIntros "#Hobs Hcg Hpc".
    iDestruct "Hobs" as "[#HQ #Hwall]".
    iDestruct (init_wobs_sub init_msg_sh   ltac:(tauto) with "Hwall") as "#Hwsh".
    iDestruct (init_wobs_sub init_msg_fork ltac:(tauto) with "Hwall") as "#Hwfk".
    iDestruct (init_wobs_sub init_msg_exec ltac:(tauto) with "Hwall") as "#Hwex".
    iDestruct (init_wobs_sub init_msg_wait ltac:(tauto) with "Hwall") as "#Hwwt".
    pose proof (us_canon _ _ _ _ Hst0) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    (* the sp that every call below runs at *)
    assert (Hspm : forall Mx : gmap Z (bv 8), uv_stack pt Mx sp0 256 ->
              add_vec_int sp0 (- 32) = (mword_of_int (uint sp0 - 32) : mword 64)).
    { intros Mx Hx.
      destruct (uv_stack_split pt Mx sp0 256 32 224 eq_refl ltac:(lia)
                  ltac:(reflexivity) ltac:(lia) Hx) as (Hx32 & _).
      exact (uv_stack_sp_moi pt Mx sp0 32 Hx32). }
    assert (Husp : uint (mword_of_int (uint sp0 - 32) : mword 64) = uint sp0 - 32)
      by (apply uint_moi; unfold Z64; lia).
    (* THE OUTER (restart) LOOP *)
    iAssert (∀ (CID : CpuId) (Mx : gmap Z (bv 8)) (mx : regfile),
               ⌜init_img_sub Mx /\ uv_stack pt Mx sp0 256 /\
                mx !!! Regidx csp_rs1
                  = (mword_of_int (uint sp0 - 32) : mword 64) /\
                mx !!! Regidx (mword_of_int 18 : mword 5)
                  = (mword_of_int INIT_MSG_SH : mword 64)⌝ -∗
               uv_cap_gpr (CID := CID) C pt Pinit Mx mx -∗
               pc_is (CID := CID) (mword_of_int 0x32) -∗
               WP (Loop : expr riscv_lang))%I with "[]" as "Outer".
    { iLöb as "IHo".
      iIntros (CID Mx mx) "%Hinv Hcg Hpc".
      destruct Hinv as (Himg & Hst & Hsp & Hs2).
      destruct (uv_stack_split pt Mx sp0 256 32 224 eq_refl ltac:(lia)
                  ltac:(reflexivity) ltac:(lia) Hst) as (Hst32 & Hst224).
      rewrite (Hspm Mx Hst) in Hst224.

      (* ---- 0x32  mv a0,s2 ---- *)
      iApply (wp_uv_cmv C pt Pinit Mx mx (mword_of_int 0x32)
                (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
                (mword_of_int INIT_MSG_SH)
                (ui_init_32 pt Mx (ilay_text pt Hlay) (init_img_text Mx Himg))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite add_vec_zero_l; rewrite Hs2; reflexivity)
                with "Hcg Hpc").
      iIntros (Y1) "Hcg Hpc".
      set (g1 := <[Regidx (mword_of_int 10 : mword 5)
                   := regval_into_reg (mword_of_int INIT_MSG_SH : mword 64)]> mx).
      assert (Hg1a0 : g1 !!! Regidx a0_idx
                      = (mword_of_int INIT_MSG_SH : mword 64))
        by exact (upd_eq mx (Regidx a0_idx) _).
      assert (Hg1sp : g1 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne mx (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hsp).
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2
                    = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E32) in "Hpc".

      (* ---- 0x34  jal printf ---- *)
      iApply (wp_uv_jal C pt Pinit Mx g1 (mword_of_int 0x34)
                (mword_of_int 1932 : mword 21) ra_idx
                (mword_of_int 0x7c0) (mword_of_int 0x38)
                (ui_init_34 pt Mx (ilay_text pt Hlay) (init_img_text Mx Himg))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (Y2) "Hcg Hpc".
      set (g2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x38 : mword 64)]> g1).
      assert (Hg2a0 : g2 !!! Regidx a0_idx
                      = (mword_of_int INIT_MSG_SH : mword 64))
        by exact (eq_trans (upd_ne g1 (Regidx ra_idx) (Regidx a0_idx) _
                              ltac:(vm_compute; discriminate)) Hg1a0).
      assert (Hg2sp : g2 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne g1 (Regidx ra_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hg1sp).
      assert (Hg2ra : g2 !!! Regidx ra_idx = (mword_of_int 0x38 : mword 64))
        by exact (upd_eq g1 (Regidx ra_idx) _).
      iEval (change (mword_of_int 0x7c0 : mword 64)
               with (mword_of_int InitSyms.printf : mword 64)) in "Hpc".
      iApply (wp_init_printf C pt Q W Y2 Mx g2
                (mword_of_int (uint sp0 - 32)) INIT_MSG_SH init_msg_sh
                Hlay Himg Hg2sp Hst224
                ltac:(unfold init_frame_ok; rewrite Husp; lia)
                Hg2a0 (init_lit_sh Mx (init_img_data Mx Himg))
                ltac:(rewrite Hg2ra; vm_compute; reflexivity)
                with "Hcg Hwsh Hpc []").
      iIntros (Y3 g3 Mx3) "%Hcs3 %Ho3 Hcg Hpc".
      rewrite Husp in Ho3.
      iEval (rewrite Hg2ra) in "Hpc".
      assert (Himg3 : init_img_sub Mx3)
        by exact (init_img_only Mx Mx3 (uint sp0 - 32 - 224) 224 ltac:(lia) Ho3 Himg).
      assert (Hst3 : uv_stack pt Mx3 sp0 256)
        by exact (uM_only_stack pt Mx Mx3 sp0 256 (uint sp0 - 32 - 224) 224 Ho3 Hst).
      assert (Hg3sp : g3 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (Hcs3 (mword_of_int 2 : mword 5)
                              ltac:(vm_compute; reflexivity)) Hg2sp).
      assert (Hg3s2 : g3 !!! Regidx (mword_of_int 18 : mword 5)
                      = (mword_of_int INIT_MSG_SH : mword 64)).
      { rewrite (Hcs3 (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
        refine (eq_trans (upd_ne g1 (Regidx ra_idx)
                            (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne mx (Regidx a0_idx)
                            (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hs2. }

      (* ---- 0x38  jal fork ---- *)
      iApply (wp_uv_jal C pt Pinit Mx3 g3 (mword_of_int 0x38)
                (mword_of_int 818 : mword 21) ra_idx
                (mword_of_int 0x36a) (mword_of_int 0x3c)
                (ui_init_38 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (Y4) "Hcg Hpc".
      set (g4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x3c : mword 64)]> g3).
      assert (Hg4ra : g4 !!! Regidx ra_idx = (mword_of_int 0x3c : mword 64))
        by exact (upd_eq g3 (Regidx ra_idx) _).
      assert (Hg4sp : g4 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne g3 (Regidx ra_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hg3sp).
      assert (Hg4s2 : g4 !!! Regidx (mword_of_int 18 : mword 5)
                      = (mword_of_int INIT_MSG_SH : mword 64))
        by exact (eq_trans (upd_ne g3 (Regidx ra_idx)
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) Hg3s2).
      iEval (change (mword_of_int 0x36a : mword 64)
               with (mword_of_int InitSyms.fork : mword 64)) in "Hpc".
      assert (Hpre4 : init_layout pt /\ init_text_sub Mx3 /\
                      is_aligned_vaddr (Virtaddr (g4 !!! Regidx ra_idx)) 2 = true).
      { split_and!; [ exact Hlay | exact (init_img_text Mx3 Himg3)
                    | rewrite Hg4ra; vm_compute; reflexivity ]. }
      iApply (wp_init_fork C pt Q W Y4 Mx3 g4 Hpre4
                (init_proto_fork C pt Q W)
                with "Hcg Hpc []").
      iIntros (Y5 ret) "Hcg Hpc".
      iEval (rewrite Hg4ra) in "Hpc".
      set (g5 := <[Regidx a0_idx := ret]>
                   (<[Regidx a7_idx := (mword_of_int SYS_fork : mword 64)]> g4)).
      assert (Hg5a0 : g5 !!! Regidx a0_idx = ret)
        by exact (upd_eq _ (Regidx a0_idx) ret).
      assert (Hg5sp : g5 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64)).
      { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne g4 (Regidx a7_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hg4sp. }
      assert (Hg5s2 : g5 !!! Regidx (mword_of_int 18 : mword 5)
                      = (mword_of_int INIT_MSG_SH : mword 64)).
      { refine (eq_trans (upd_ne _ (Regidx a0_idx)
                            (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne g4 (Regidx a7_idx)
                            (Regidx (mword_of_int 18 : mword 5)) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hg4s2. }

      (* ---- 0x3c  mv s1,a0 ---- *)
      iApply (wp_uv_cmv C pt Pinit Mx3 g5 (mword_of_int 0x3c)
                (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5) ret
                (ui_init_3c pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite add_vec_zero_l; rewrite Hg5a0; reflexivity)
                with "Hcg Hpc").
      iIntros (Y6) "Hcg Hpc".
      set (g6 := <[Regidx (mword_of_int 9 : mword 5)
                   := regval_into_reg ret]> g5).
      assert (Hg6a0 : g6 !!! Regidx a0_idx = ret)
        by exact (eq_trans (upd_ne g5 (Regidx (mword_of_int 9 : mword 5))
                              (Regidx a0_idx) _ ltac:(vm_compute; discriminate))
                           Hg5a0).
      assert (Hg6sp : g6 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne g5 (Regidx (mword_of_int 9 : mword 5))
                              (Regidx csp_rs1) _ ltac:(vm_compute; discriminate))
                           Hg5sp).
      assert (Hg6s2 : g6 !!! Regidx (mword_of_int 18 : mword 5)
                      = (mword_of_int INIT_MSG_SH : mword 64))
        by exact (eq_trans (upd_ne g5 (Regidx (mword_of_int 9 : mword 5))
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) Hg5s2).
      assert (E3c : add_vec_int (mword_of_int 0x3c : mword 64) 2
                    = mword_of_int 0x3e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E3c) in "Hpc".

      (* ---- THE INNER (wait) LOOP, set up before the branches ---- *)
      iAssert (∀ (CIDi : CpuId) (My : gmap Z (bv 8)) (my : regfile),
                 ⌜init_img_sub My /\ uv_stack pt My sp0 256 /\
                  my !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64) /\
                  my !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int INIT_MSG_SH : mword 64)⌝ -∗
                 uv_cap_gpr (CID := CIDi) C pt Pinit My my -∗
                 pc_is (CID := CIDi) (mword_of_int 0x44) -∗
                 WP (Loop : expr riscv_lang))%I with "[]" as "Inner".
      { iLöb as "IHi".
        iIntros (CIDi My my) "%Hinvi Hcg Hpc".
        destruct Hinvi as (Himgi & Hsti & Hspi & Hs2i).
        destruct (uv_stack_split pt My sp0 256 32 224 eq_refl ltac:(lia)
                    ltac:(reflexivity) ltac:(lia) Hsti) as (_ & Hsti224).
        rewrite (Hspm My Hsti) in Hsti224.

        (* ---- 0x44  li a0,0 ---- *)
        iApply (wp_uv_cli C pt Pinit My my (mword_of_int 0x44)
                  (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0)
                  (ui_init_44 pt My (ilay_text pt Hlay) (init_img_text My Himgi))
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (Z1) "Hcg Hpc".
        set (h1 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int 0 : mword 64)]> my).
        assert (E44 : add_vec_int (mword_of_int 0x44 : mword 64) 2
                      = mword_of_int 0x46)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E44) in "Hpc".

        (* ---- 0x46  jal wait ---- *)
        iApply (wp_uv_jal C pt Pinit My h1 (mword_of_int 0x46)
                  (mword_of_int 820 : mword 21) ra_idx
                  (mword_of_int 0x37a) (mword_of_int 0x4a)
                  (ui_init_46 pt My (ilay_text pt Hlay) (init_img_text My Himgi))
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (Z2) "Hcg Hpc".
        set (h2 := <[Regidx ra_idx
                     := regval_into_reg (mword_of_int 0x4a : mword 64)]> h1).
        assert (Hh2ra : h2 !!! Regidx ra_idx = (mword_of_int 0x4a : mword 64))
          by exact (upd_eq h1 (Regidx ra_idx) _).
        assert (Hh2a0 : h2 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
          by exact (eq_trans (upd_ne h1 (Regidx ra_idx) (Regidx a0_idx) _
                                ltac:(vm_compute; discriminate))
                             (upd_eq my (Regidx a0_idx) _)).
        assert (Hh2sp : h2 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
        { refine (eq_trans (upd_ne h1 (Regidx ra_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne my (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hspi. }
        assert (Hh2s2 : h2 !!! Regidx (mword_of_int 18 : mword 5)
                        = (mword_of_int INIT_MSG_SH : mword 64)).
        { refine (eq_trans (upd_ne h1 (Regidx ra_idx)
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne my (Regidx a0_idx)
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hs2i. }
        iEval (change (mword_of_int 0x37a : mword 64)
                 with (mword_of_int InitSyms.wait : mword 64)) in "Hpc".
        assert (Hprew : init_layout pt /\ init_text_sub My /\
                        is_aligned_vaddr (Virtaddr (h2 !!! Regidx ra_idx)) 2 = true).
        { split_and!; [ exact Hlay | exact (init_img_text My Himgi)
                      | rewrite Hh2ra; vm_compute; reflexivity ]. }
        assert (Hnullw : uint (h2 !!! Regidx a0_idx) = 0)
          by (rewrite Hh2a0; vm_compute; reflexivity).
        iApply (wp_init_wait C pt Q W Z2 My h2 Hprew Hnullw
                  with "Hcg Hpc []").
        iIntros (Z3 wret) "Hcg Hpc".
        iEval (rewrite Hh2ra) in "Hpc".
        set (h3 := <[Regidx a0_idx := wret]>
                     (<[Regidx a7_idx := (mword_of_int SYS_wait : mword 64)]> h2)).
        assert (Hh3sp : h3 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
        { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne h2 (Regidx a7_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hh2sp. }
        assert (Hh3s2 : h3 !!! Regidx (mword_of_int 18 : mword 5)
                        = (mword_of_int INIT_MSG_SH : mword 64)).
        { refine (eq_trans (upd_ne _ (Regidx a0_idx)
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne h2 (Regidx a7_idx)
                              (Regidx (mword_of_int 18 : mword 5)) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hh2s2. }

        (* ---- 0x4a  beq s1,a0,32  -- THE RESTART BACK EDGE ---- *)
        destruct (uv_btaken BEQ (h3 !!! Regidx (mword_of_int 9 : mword 5))
                                (h3 !!! Regidx (mword_of_int 10 : mword 5)))
          eqn:Htk4a.
        - (* the shell exited: back to 0x32 through the OUTER IH *)
          iApply (wp_uv_btype_later C pt Pinit My h3 (mword_of_int 0x4a)
                    (mword_of_int 8168 : mword 13) (mword_of_int 10 : mword 5)
                    (mword_of_int 9 : mword 5) BEQ true (mword_of_int 0x32)
                    (ui_init_4a pt My (ilay_text pt Hlay) (init_img_text My Himgi))
                    ltac:(symmetry; exact Htk4a)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(intro Hx; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          iNext. iIntros (Z4) "Hcg Hpc".
          iApply ("IHo" $! Z4 My h3 with "[] Hcg Hpc").
          iPureIntro. split_and!; assumption.
        - (* not the shell *)
          iApply (wp_uv_btype_later C pt Pinit My h3 (mword_of_int 0x4a)
                    (mword_of_int 8168 : mword 13) (mword_of_int 10 : mword 5)
                    (mword_of_int 9 : mword 5) BEQ false (mword_of_int 0x32)
                    (ui_init_4a pt My (ilay_text pt Hlay) (init_img_text My Himgi))
                    ltac:(symmetry; exact Htk4a)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(intro Hx; discriminate)
                    with "Hcg Hpc []").
          iNext. iIntros (Z4) "Hcg Hpc".
          assert (E4a : add_vec_int (mword_of_int 0x4a : mword 64) 4
                        = mword_of_int 0x4e)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite E4a) in "Hpc".

          (* ---- 0x4e  bgez a0,44  -- THE WAIT BACK EDGE ---- *)
          destruct (uv_btaken BGE (h3 !!! Regidx (mword_of_int 10 : mword 5))
                                  zero_reg) eqn:Htk4e.
          + (* a parentless child: wait again *)
            iApply (wp_uv_btype0_later C pt Pinit My h3 (mword_of_int 0x4e)
                      (mword_of_int 8182 : mword 13) (mword_of_int 10 : mword 5)
                      BGE true (mword_of_int 0x44)
                      (ui_init_4e pt My (ilay_text pt Hlay)
                         (init_img_text My Himgi))
                      ltac:(symmetry; exact Htk4e)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(intro Hx; vm_compute; reflexivity)
                      with "Hcg Hpc []").
            iNext. iIntros (Z5) "Hcg Hpc".
            iApply ("IHi" $! Z5 My h3 with "[] Hcg Hpc").
            iPureIntro. split_and!; assumption.
          + (* wait returned an error: diagnose and exit *)
            iApply (wp_uv_btype0_later C pt Pinit My h3 (mword_of_int 0x4e)
                      (mword_of_int 8182 : mword 13) (mword_of_int 10 : mword 5)
                      BGE false (mword_of_int 0x44)
                      (ui_init_4e pt My (ilay_text pt Hlay)
                         (init_img_text My Himgi))
                      ltac:(symmetry; exact Htk4e)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(intro Hx; discriminate)
                      with "Hcg Hpc []").
            iNext. iIntros (Z5) "Hcg Hpc".
            assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 4
                          = mword_of_int 0x52)
              by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite E4e) in "Hpc".
            iApply (init_diag_exit Z5 0x52 2422 1894 786 INIT_MSG_WAIT
                      init_msg_wait My h3 (mword_of_int (uint sp0 - 32))
                      Hlay Himgi Hsti224 ltac:(rewrite Husp; lia) Hh3sp
                      (init_lit_wait My (init_img_data My Himgi))
                      ltac:(intros Mz Hz; exact (ui_init_52 pt Mz (ilay_text pt Hlay) Hz))
                      ltac:(intros Mz Hz; exact (ui_init_56 pt Mz (ilay_text pt Hlay) Hz))
                      ltac:(intros Mz Hz; exact (ui_init_5a pt Mz (ilay_text pt Hlay) Hz))
                      ltac:(intros Mz Hz; exact (ui_init_5e pt Mz (ilay_text pt Hlay) Hz))
                      ltac:(intros Mz Hz; exact (ui_init_60 pt Mz (ilay_text pt Hlay) Hz))
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(apply bv_eq; vm_compute; reflexivity)
                      ltac:(vm_compute; reflexivity)
                      with "Hwwt Hcg Hpc"). }

      (* ---- 0x3e  bltz a0,84  -- did fork fail? ---- *)
      destruct (uv_btaken BLT (g6 !!! Regidx (mword_of_int 10 : mword 5))
                              zero_reg) eqn:Htk3e.
      { (* fork failed: diagnose and exit *)
        iApply (wp_uv_btype0 C pt Pinit Mx3 g6 (mword_of_int 0x3e)
                  (mword_of_int 70 : mword 13) (mword_of_int 10 : mword 5)
                  BLT true (mword_of_int 0x84)
                  (ui_init_3e pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(symmetry; exact Htk3e)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hx; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (Y7) "Hcg Hpc".
        destruct (uv_stack_split pt Mx3 sp0 256 32 224 eq_refl ltac:(lia)
                    ltac:(reflexivity) ltac:(lia) Hst3) as (_ & Hst3224).
        rewrite (Hspm Mx3 Hst3) in Hst3224.
        iApply (init_diag_exit Y7 0x84 2316 1844 736 INIT_MSG_FORK
                  init_msg_fork Mx3 g6 (mword_of_int (uint sp0 - 32))
                  Hlay Himg3 Hst3224 ltac:(rewrite Husp; lia) Hg6sp
                  (init_lit_fork Mx3 (init_img_data Mx3 Himg3))
                  ltac:(intros Mz Hz; exact (ui_init_84 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_88 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_8c pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_90 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_92 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hwfk Hcg Hpc"). }
      iApply (wp_uv_btype0 C pt Pinit Mx3 g6 (mword_of_int 0x3e)
                (mword_of_int 70 : mword 13) (mword_of_int 10 : mword 5)
                BLT false (mword_of_int 0x84)
                (ui_init_3e pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                ltac:(symmetry; exact Htk3e)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hx; discriminate)
                with "Hcg Hpc").
      iIntros (Y7) "Hcg Hpc".
      assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 4
                    = mword_of_int 0x42)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E3e) in "Hpc".

      (* ---- 0x42  beqz a0,96  -- are we the child? ---- *)
      destruct (eq_vec (g6 !!! Regidx (mword_of_int 10 : mword 5)) zero_reg)
        eqn:Htk42.
      { (* THE CHILD: exec("sh", argv) ---------------------------------- *)
        iApply (wp_uv_cbeqz C pt Pinit Mx3 g6 (mword_of_int 0x42)
                  (mword_of_int 42 : mword 8) (mword_of_int 2 : mword 3)
                  (mword_of_int 10 : mword 5) true (mword_of_int 0x96)
                  (ui_init_42 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; reflexivity)
                  ltac:(symmetry; exact Htk42)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intro Hx; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (Y8) "Hcg Hpc".

        (* ---- 0x96  auipc a1,0x1 ---- *)
        iApply (wp_uv_auipc C pt Pinit Mx3 g6 (mword_of_int 0x96)
                  (mword_of_int 1 : mword 20) (mword_of_int 11 : mword 5)
                  (mword_of_int 0x1096)
                  (ui_init_96 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (Y9) "Hcg Hpc".
        set (k1 := <[Regidx (mword_of_int 11 : mword 5)
                     := regval_into_reg (mword_of_int 0x1096 : mword 64)]> g6).
        assert (Hk1a1 : k1 !!! Regidx a1_idx = (mword_of_int 0x1096 : mword 64))
          by exact (upd_eq g6 (Regidx a1_idx) _).
        assert (E96 : add_vec_int (mword_of_int 0x96 : mword 64) 4
                      = mword_of_int 0x9a)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E96) in "Hpc".

        (* ---- 0x9a  addi a1,a1,-150   (&argv) ---- *)
        iApply (wp_uv_addi C pt Pinit Mx3 k1 (mword_of_int 0x9a)
                  (mword_of_int 3946 : mword 12) (mword_of_int 11 : mword 5)
                  (mword_of_int 11 : mword 5) (mword_of_int INIT_ARGV)
                  (ui_init_9a pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hk1a1;
                        assert (Hc : (sign_extend' 64 (mword_of_int 3946 : mword 12)
                                      : mword 64) = mword_of_int (-150))
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Hc; rewrite moi_add; f_equal;
                        unfold INIT_ARGV; lia)
                  with "Hcg Hpc").
        iIntros (YA) "Hcg Hpc".
        set (k2 := <[Regidx (mword_of_int 11 : mword 5)
                     := regval_into_reg (mword_of_int INIT_ARGV : mword 64)]> k1).
        assert (E9a : add_vec_int (mword_of_int 0x9a : mword 64) 4
                      = mword_of_int 0x9e)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E9a) in "Hpc".

        (* ---- 0x9e  auipc a0,0x1 ---- *)
        iApply (wp_uv_auipc C pt Pinit Mx3 k2 (mword_of_int 0x9e)
                  (mword_of_int 1 : mword 20) (mword_of_int 10 : mword 5)
                  (mword_of_int 0x109e)
                  (ui_init_9e pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (YB) "Hcg Hpc".
        set (k3 := <[Regidx (mword_of_int 10 : mword 5)
                     := regval_into_reg (mword_of_int 0x109e : mword 64)]> k2).
        assert (Hk3a0 : k3 !!! Regidx a0_idx = (mword_of_int 0x109e : mword 64))
          by exact (upd_eq k2 (Regidx a0_idx) _).
        assert (E9e : add_vec_int (mword_of_int 0x9e : mword 64) 4
                      = mword_of_int 0xa2)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E9e) in "Hpc".

        (* ---- 0xa2  addi a0,a0,-1782   ("sh") ---- *)
        iApply (wp_uv_addi C pt Pinit Mx3 k3 (mword_of_int 0xa2)
                  (mword_of_int 2314 : mword 12) (mword_of_int 10 : mword 5)
                  (mword_of_int 10 : mword 5) (mword_of_int INIT_SH)
                  (ui_init_a2 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hk3a0;
                        assert (Hc : (sign_extend' 64 (mword_of_int 2314 : mword 12)
                                      : mword 64) = mword_of_int (-1782))
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Hc; rewrite moi_add; f_equal;
                        unfold INIT_SH; lia)
                  with "Hcg Hpc").
        iIntros (YC) "Hcg Hpc".
        set (k4 := <[Regidx (mword_of_int 10 : mword 5)
                     := regval_into_reg (mword_of_int INIT_SH : mword 64)]> k3).
        assert (Ea2 : add_vec_int (mword_of_int 0xa2 : mword 64) 4
                      = mword_of_int 0xa6)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Ea2) in "Hpc".

        (* ---- 0xa6  jal exec ---- *)
        iApply (wp_uv_jal C pt Pinit Mx3 k4 (mword_of_int 0xa6)
                  (mword_of_int 772 : mword 21) ra_idx
                  (mword_of_int 0x3aa) (mword_of_int 0xaa)
                  (ui_init_a6 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (YD) "Hcg Hpc".
        set (k5 := <[Regidx ra_idx
                     := regval_into_reg (mword_of_int 0xaa : mword 64)]> k4).
        assert (Hk5ra : k5 !!! Regidx ra_idx = (mword_of_int 0xaa : mword 64))
          by exact (upd_eq k4 (Regidx ra_idx) _).
        assert (Hk5a0 : k5 !!! Regidx a0_idx = (mword_of_int INIT_SH : mword 64))
          by exact (eq_trans (upd_ne k4 (Regidx ra_idx) (Regidx a0_idx) _
                                ltac:(vm_compute; discriminate))
                             (upd_eq k3 (Regidx a0_idx) _)).
        assert (Hk5a1 : k5 !!! Regidx a1_idx = (mword_of_int INIT_ARGV : mword 64)).
        { refine (eq_trans (upd_ne k4 (Regidx ra_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k3 (Regidx a0_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k2 (Regidx a0_idx) (Regidx a1_idx) _
                              ltac:(vm_compute; discriminate)) _).
          exact (upd_eq k1 (Regidx a1_idx) _). }
        assert (Hk5sp : k5 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
        { refine (eq_trans (upd_ne k4 (Regidx ra_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k3 (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k2 (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k1 (Regidx a1_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne g6 (Regidx a1_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hg6sp. }
        iEval (change (mword_of_int 0x3aa : mword 64)
                 with (mword_of_int InitSyms.exec : mword 64)) in "Hpc".
        assert (Huargs : uint (k5 !!! Regidx a0_idx) = INIT_SH /\
                         uint (k5 !!! Regidx a1_idx) = INIT_ARGV).
        { rewrite Hk5a0. rewrite Hk5a1. split;
            [ apply uint_moi; unfold INIT_SH, Z64; lia
            | apply uint_moi; unfold INIT_ARGV, Z64; lia ]. }
        assert (Hpree : init_layout pt /\ init_text_sub Mx3 /\
                        is_aligned_vaddr (Virtaddr (k5 !!! Regidx ra_idx)) 2 = true).
        { split_and!; [ exact Hlay | exact (init_img_text Mx3 Himg3)
                      | rewrite Hk5ra; vm_compute; reflexivity ]. }
        assert (Hargse : uexec_args Mx3 (uint (k5 !!! Regidx a0_idx))
                           (uint (k5 !!! Regidx a1_idx)) init_sh_path init_sh_argv).
        { destruct Huargs as (Ha & Hb). rewrite Ha. rewrite Hb.
          exact (init_exec_args Mx3 (init_img_data Mx3 Himg3)). }
        iApply (wp_init_exec C pt Q W YD Mx3 k5 init_sh_path init_sh_argv
                  Hpree Hargse
                  with "Hcg HQ Hpc []").
        iIntros (YE eret) "Hcg Hpc".
        iEval (rewrite Hk5ra) in "Hpc".
        set (k6 := <[Regidx a0_idx := eret]>
                     (<[Regidx a7_idx := (mword_of_int SYS_exec : mword 64)]> k5)).
        assert (Hk6sp : k6 !!! Regidx csp_rs1
                        = (mword_of_int (uint sp0 - 32) : mword 64)).
        { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          refine (eq_trans (upd_ne k5 (Regidx a7_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) _).
          exact Hk5sp. }
        destruct (uv_stack_split pt Mx3 sp0 256 32 224 eq_refl ltac:(lia)
                    ltac:(reflexivity) ltac:(lia) Hst3) as (_ & Hst3224).
        rewrite (Hspm Mx3 Hst3) in Hst3224.
        iApply (init_diag_exit YE 0xaa 2310 1806 698 INIT_MSG_EXEC
                  init_msg_exec Mx3 k6 (mword_of_int (uint sp0 - 32))
                  Hlay Himg3 Hst3224 ltac:(rewrite Husp; lia) Hk6sp
                  (init_lit_exec Mx3 (init_img_data Mx3 Himg3))
                  ltac:(intros Mz Hz; exact (ui_init_aa pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_ae pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_b2 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_b6 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(intros Mz Hz; exact (ui_init_b8 pt Mz (ilay_text pt Hlay) Hz))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hwex Hcg Hpc"). }
      (* THE PARENT: fall through to the wait loop -------------------- *)
      iApply (wp_uv_cbeqz C pt Pinit Mx3 g6 (mword_of_int 0x42)
                (mword_of_int 42 : mword 8) (mword_of_int 2 : mword 3)
                (mword_of_int 10 : mword 5) false (mword_of_int 0x96)
                (ui_init_42 pt Mx3 (ilay_text pt Hlay) (init_img_text Mx3 Himg3))
                ltac:(vm_compute; reflexivity)
                ltac:(symmetry; exact Htk42)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hx; discriminate)
                with "Hcg Hpc").
      iIntros (Y8) "Hcg Hpc".
      assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2
                    = mword_of_int 0x44)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E42) in "Hpc".
      iApply ("Inner" $! Y8 Mx3 g6 with "[] Hcg Hpc").
      iPureIntro. split_and!; assumption. }
    iApply ("Outer" $! CIDp M m with "[] Hcg Hpc").
    iPureIntro. split_and!; assumption.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 main from 0x1e -- the two [dup]s and the message pointer, which    *)
  (* BOTH arms of the `open("console") < 0' test reach.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma init_main_from1e (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    init_layout pt ->
    8192 <= uint sp0 - 256 ->
    init_img_sub M ->
    uv_stack pt M sp0 256 ->
    m !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64) ->
    init_obs Q W -∗
    uv_cap_gpr (CID := CIDp) C pt Pinit M m -∗
    pc_is (CID := CIDp) (mword_of_int 0x1e) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlay Hfr Himg Hst Hsp.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    iIntros "#Hobs Hcg Hpc".

    (* ---- 0x1e  li a0,0 ---- *)
    iApply (wp_uv_cli C pt Pinit M m (mword_of_int 0x1e)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0)
              (ui_init_1e pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (B1) "Hcg Hpc".
    set (u1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (Hu1sp : u1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne m (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hsp).
    assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2
                  = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1e) in "Hpc".

    (* ---- 0x20  jal dup ---- *)
    iApply (wp_uv_jal C pt Pinit M u1 (mword_of_int 0x20)
              (mword_of_int 970 : mword 21) ra_idx
              (mword_of_int 0x3ea) (mword_of_int 0x24)
              (ui_init_20 pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (B2) "Hcg Hpc".
    set (u2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x24 : mword 64)]> u1).
    assert (Hu2ra : u2 !!! Regidx ra_idx = (mword_of_int 0x24 : mword 64))
      by exact (upd_eq u1 (Regidx ra_idx) _).
    assert (Hu2sp : u2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne u1 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hu1sp).
    iEval (change (mword_of_int 0x3ea : mword 64)
             with (mword_of_int InitSyms.dup : mword 64)) in "Hpc".
    assert (Hpred1 : init_layout pt /\ init_text_sub M /\
                     is_aligned_vaddr (Virtaddr (u2 !!! Regidx ra_idx)) 2 = true).
    { split_and!; [ exact Hlay | exact (init_img_text M Himg)
                  | rewrite Hu2ra; vm_compute; reflexivity ]. }
    iApply (wp_init_dup C pt Q W B2 M u2 Hpred1 (init_proto_dup C pt Q W)
              with "Hcg Hpc []").
    iIntros (B3 r1) "Hcg Hpc".
    iEval (rewrite Hu2ra) in "Hpc".
    set (u3 := <[Regidx a0_idx := r1]>
                 (<[Regidx a7_idx := (mword_of_int SYS_dup : mword 64)]> u2)).
    assert (Hu3sp : u3 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64)).
    { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne u2 (Regidx a7_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hu2sp. }

    (* ---- 0x24  li a0,0 ---- *)
    iApply (wp_uv_cli C pt Pinit M u3 (mword_of_int 0x24)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0)
              (ui_init_24 pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (B4) "Hcg Hpc".
    set (u4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> u3).
    assert (Hu4sp : u4 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne u3 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hu3sp).
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E24) in "Hpc".

    (* ---- 0x26  jal dup ---- *)
    iApply (wp_uv_jal C pt Pinit M u4 (mword_of_int 0x26)
              (mword_of_int 964 : mword 21) ra_idx
              (mword_of_int 0x3ea) (mword_of_int 0x2a)
              (ui_init_26 pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (B5) "Hcg Hpc".
    set (u5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x2a : mword 64)]> u4).
    assert (Hu5ra : u5 !!! Regidx ra_idx = (mword_of_int 0x2a : mword 64))
      by exact (upd_eq u4 (Regidx ra_idx) _).
    assert (Hu5sp : u5 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne u4 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hu4sp).
    iEval (change (mword_of_int 0x3ea : mword 64)
             with (mword_of_int InitSyms.dup : mword 64)) in "Hpc".
    assert (Hpred2 : init_layout pt /\ init_text_sub M /\
                     is_aligned_vaddr (Virtaddr (u5 !!! Regidx ra_idx)) 2 = true).
    { split_and!; [ exact Hlay | exact (init_img_text M Himg)
                  | rewrite Hu5ra; vm_compute; reflexivity ]. }
    iApply (wp_init_dup C pt Q W B5 M u5 Hpred2 (init_proto_dup C pt Q W)
              with "Hcg Hpc []").
    iIntros (B6 r2) "Hcg Hpc".
    iEval (rewrite Hu5ra) in "Hpc".
    set (u6 := <[Regidx a0_idx := r2]>
                 (<[Regidx a7_idx := (mword_of_int SYS_dup : mword 64)]> u5)).
    assert (Hu6sp : u6 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64)).
    { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne u5 (Regidx a7_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hu5sp. }

    (* ---- 0x2a  auipc s2,0x1 ---- *)
    iApply (wp_uv_auipc C pt Pinit M u6 (mword_of_int 0x2a)
              (mword_of_int 1 : mword 20) (mword_of_int 18 : mword 5)
              (mword_of_int 0x102a)
              (ui_init_2a pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (B7) "Hcg Hpc".
    set (u7 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (mword_of_int 0x102a : mword 64)]> u6).
    assert (Hu7s2 : u7 !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int 0x102a : mword 64))
      by exact (upd_eq u6 (Regidx (mword_of_int 18 : mword 5)) _).
    assert (Hu7sp : u7 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne u6 (Regidx (mword_of_int 18 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate))
                         Hu6sp).
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 4
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E2a) in "Hpc".

    (* ---- 0x2e  addi s2,s2,-1714   ("init: starting sh\n") ---- *)
    iApply (wp_uv_addi C pt Pinit M u7 (mword_of_int 0x2e)
              (mword_of_int 2382 : mword 12) (mword_of_int 18 : mword 5)
              (mword_of_int 18 : mword 5) (mword_of_int INIT_MSG_SH)
              (ui_init_2e pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hu7s2;
                    assert (Hc : (sign_extend' 64 (mword_of_int 2382 : mword 12)
                                  : mword 64) = mword_of_int (-1714))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Hc; rewrite moi_add; f_equal;
                    unfold INIT_MSG_SH; lia)
              with "Hcg Hpc").
    iIntros (B8) "Hcg Hpc".
    set (u8 := <[Regidx (mword_of_int 18 : mword 5)
                 := regval_into_reg (mword_of_int INIT_MSG_SH : mword 64)]> u7).
    assert (Hu8s2 : u8 !!! Regidx (mword_of_int 18 : mword 5)
                    = (mword_of_int INIT_MSG_SH : mword 64))
      by exact (upd_eq u7 (Regidx (mword_of_int 18 : mword 5)) _).
    assert (Hu8sp : u8 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne u7 (Regidx (mword_of_int 18 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate))
                         Hu7sp).
    assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4
                  = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E2e) in "Hpc".
    iApply (init_main_loop B8 M u8 sp0 Hlay Hfr Himg Hst Hu8sp Hu8s2
              with "Hobs Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4 main: the prologue, [open("console", O_RDWR)], and BOTH arms of    *)
  (* the failure test -- the [mknod] path is proved, not assumed away.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_init_main (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_init_main_body (CID := CIDp) C pt Q W M m sp0.
  Proof.
    intros Hlay Himg Hsp Hst Hfr.
    unfold init_frame_ok in Hfr.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    destruct (uv_stack_split pt M sp0 256 32 224 eq_refl ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hs32 & _).
    assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
      by (rewrite moi_of_uint; exact Hsp).
    iIntros "Hcg #Hobs Hpc".
    iEval (change (mword_of_int InitSyms.main : mword 64)
             with (mword_of_int 0x0 : mword 64)) in "Hpc".

    (* ---- 0x00  c.addi sp,sp,-32 ---- *)
    assert (Hw00 : (mword_of_int (uint sp0 - 32) : mword 64)
                   = add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                      : mword 64) = mword_of_int (-32))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Pinit M m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 5)
              (mword_of_int (uint sp0 - 32))
              (ui_init_00 pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate) Hw00
              with "Hcg Hpc").
    iIntros (A0h) "Hcg Hpc".
    set (p1 := <[Regidx (mword_of_int 2 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64)]> m).
    assert (Hspp1 : p1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E00) in "Hpc".

    (* ---- 0x02  c.sdsp ra,24(sp) ---- *)
    assert (Hp1r1 : p1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 1 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt A0h Pinit M p1 sp0 (mword_of_int 0x02)
              (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5) 32 24
              (ui_init_02 pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hs32
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A1h) "Hcg Hpc".
    iEval (rewrite Hp1r1) in "Hcg".
    set (A1 := uM_store8 M (uint sp0 - 32 + 24) (m !!! Regidx (mword_of_int 1 : mword 5))).
    assert (Hoa1 : uM_only M A1 (uint sp0 - 32) 32)
      by (rewrite /A1; apply uM_only_store8; lia).
    assert (Hac1 : uM_only M A1 (uint sp0 - 32) 32) by exact Hoa1.
    assert (Ha1 : init_img_sub A1)
      by exact (init_img_only M A1 (uint sp0 - 32) 32 ltac:(lia) Hoa1 Himg).
    assert (Hz1 : uv_stack pt A1 sp0 32)
      by exact (uM_only_stack pt M A1 sp0 32 (uint sp0 - 32) 32 Hoa1 Hs32).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2
                   = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E02) in "Hpc".

    (* ---- 0x04  c.sdsp s0,16(sp) ---- *)
    assert (Hp1r8 : p1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 8 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt A1h Pinit A1 p1 sp0 (mword_of_int 0x04)
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5) 32 16
              (ui_init_04 pt A1 (ilay_text pt Hlay) (init_img_text A1 Ha1)) Hz1
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A2h) "Hcg Hpc".
    iEval (rewrite Hp1r8) in "Hcg".
    set (A2 := uM_store8 A1 (uint sp0 - 32 + 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Hoa2 : uM_only A1 A2 (uint sp0 - 32) 32)
      by (rewrite /A2; apply uM_only_store8; lia).
    assert (Hac2 : uM_only M A2 (uint sp0 - 32) 32) by exact (uM_only_trans M A1 A2 (uint sp0 - 32) 32 Hac1 Hoa2).
    assert (Ha2 : init_img_sub A2)
      by exact (init_img_only A1 A2 (uint sp0 - 32) 32 ltac:(lia) Hoa2 Ha1).
    assert (Hz2 : uv_stack pt A2 sp0 32)
      by exact (uM_only_stack pt A1 A2 sp0 32 (uint sp0 - 32) 32 Hoa2 Hz1).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2
                   = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E04) in "Hpc".

    (* ---- 0x06  c.sdsp s1,8(sp) ---- *)
    assert (Hp1r9 : p1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 9 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt A2h Pinit A2 p1 sp0 (mword_of_int 0x06)
              (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5) 32 8
              (ui_init_06 pt A2 (ilay_text pt Hlay) (init_img_text A2 Ha2)) Hz2
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A3h) "Hcg Hpc".
    iEval (rewrite Hp1r9) in "Hcg".
    set (A3 := uM_store8 A2 (uint sp0 - 32 + 8) (m !!! Regidx (mword_of_int 9 : mword 5))).
    assert (Hoa3 : uM_only A2 A3 (uint sp0 - 32) 32)
      by (rewrite /A3; apply uM_only_store8; lia).
    assert (Hac3 : uM_only M A3 (uint sp0 - 32) 32) by exact (uM_only_trans M A2 A3 (uint sp0 - 32) 32 Hac2 Hoa3).
    assert (Ha3 : init_img_sub A3)
      by exact (init_img_only A2 A3 (uint sp0 - 32) 32 ltac:(lia) Hoa3 Ha2).
    assert (Hz3 : uv_stack pt A3 sp0 32)
      by exact (uM_only_stack pt A2 A3 sp0 32 (uint sp0 - 32) 32 Hoa3 Hz2).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2
                   = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E06) in "Hpc".

    (* ---- 0x08  c.sdsp s2,0(sp) ---- *)
    assert (Hp1r18 : p1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 18 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uv_frame_store C pt A3h Pinit A3 p1 sp0 (mword_of_int 0x08)
              (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5) 32 0
              (ui_init_08 pt A3 (ilay_text pt Hlay) (init_img_text A3 Ha3)) Hz3
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hspp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A4h) "Hcg Hpc".
    iEval (rewrite Hp1r18) in "Hcg".
    set (A4 := uM_store8 A3 (uint sp0 - 32 + 0) (m !!! Regidx (mword_of_int 18 : mword 5))).
    assert (Hoa4 : uM_only A3 A4 (uint sp0 - 32) 32)
      by (rewrite /A4; apply uM_only_store8; lia).
    assert (Hac4 : uM_only M A4 (uint sp0 - 32) 32) by exact (uM_only_trans M A3 A4 (uint sp0 - 32) 32 Hac3 Hoa4).
    assert (Ha4 : init_img_sub A4)
      by exact (init_img_only A3 A4 (uint sp0 - 32) 32 ltac:(lia) Hoa4 Ha3).
    assert (Hz4 : uv_stack pt A4 sp0 32)
      by exact (uM_only_stack pt A3 A4 sp0 32 (uint sp0 - 32) 32 Hoa4 Hz3).
    assert (E08 : add_vec_int (mword_of_int 0x08 : mword 64) 2
                   = mword_of_int 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E08) in "Hpc".

    (* the whole-budget invariants after the four spills *)
    assert (Hst4 : uv_stack pt A4 sp0 256)
      by exact (uM_only_stack pt M A4 sp0 256 (uint sp0 - 32) 32 Hac4 Hst).

    (* ---- 0x0a  c.addi4spn s0,sp,32 ---- *)
    assert (Hw0a : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (p1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { assert (Hcst : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hspp1. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Pinit A4 p1 (mword_of_int 0xa)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0))
              (ui_init_0a pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw0a
              with "Hcg Hpc").
    iIntros (A5h) "Hcg Hpc".
    set (p2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> p1).
    assert (Hspp2 : p2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne p1 (Regidx (mword_of_int 8 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate))
                         Hspp1).
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2
                  = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0a) in "Hpc".

    (* ---- 0x0c  li a1,2   (O_RDWR) ---- *)
    iApply (wp_uv_cli C pt Pinit A4 p2 (mword_of_int 0xc)
              (mword_of_int 2 : mword 6) a1_idx (mword_of_int 2)
              (ui_init_0c pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A6h) "Hcg Hpc".
    set (p3 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> p2).
    assert (Hspp3 : p3 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne p2 (Regidx a1_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspp2).
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0c) in "Hpc".

    (* ---- 0x0e  auipc a0,0x1 ---- *)
    iApply (wp_uv_auipc C pt Pinit A4 p3 (mword_of_int 0xe)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x100e)
              (ui_init_0e pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A7h) "Hcg Hpc".
    set (p4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0x100e : mword 64)]> p3).
    assert (Hp4a0 : p4 !!! Regidx a0_idx = (mword_of_int 0x100e : mword 64))
      by exact (upd_eq p3 (Regidx a0_idx) _).
    assert (Hspp4 : p4 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne p3 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspp3).
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 4
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E0e) in "Hpc".

    (* ---- 0x12  addi a0,a0,-1694   ("console") ---- *)
    iApply (wp_uv_addi C pt Pinit A4 p4 (mword_of_int 0x12)
              (mword_of_int 2402 : mword 12) a0_idx a0_idx
              (mword_of_int INIT_CONSOLE)
              (ui_init_12 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hp4a0;
                    assert (Hc : (sign_extend' 64 (mword_of_int 2402 : mword 12)
                                  : mword 64) = mword_of_int (-1694))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Hc; rewrite moi_add; f_equal;
                    unfold INIT_CONSOLE; lia)
              with "Hcg Hpc").
    iIntros (A8h) "Hcg Hpc".
    set (p5 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int INIT_CONSOLE : mword 64)]> p4).
    assert (Hp5a0 : p5 !!! Regidx a0_idx = (mword_of_int INIT_CONSOLE : mword 64))
      by exact (upd_eq p4 (Regidx a0_idx) _).
    assert (Hspp5 : p5 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne p4 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspp4).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E12) in "Hpc".

    (* the "console" path argument, at every image below *)
    assert (Hcons : forall Mz : gmap Z (bv 8), init_img_sub Mz ->
              uio_str_arg pt Mz INIT_CONSOLE).
    { intros Mz Hz.
      exact (init_str_arg pt Mz INIT_CONSOLE init_console (ilay_text pt Hlay)
               (init_lit_from_data Mz INIT_CONSOLE init_console
                  (init_img_data Mz Hz)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))). }
    assert (Hucons : uint (mword_of_int INIT_CONSOLE : mword 64) = INIT_CONSOLE)
      by (apply uint_moi; unfold INIT_CONSOLE, Z64; lia).

    (* ---- 0x16  jal open ---- *)
    iApply (wp_uv_jal C pt Pinit A4 p5 (mword_of_int 0x16)
              (mword_of_int 924 : mword 21) ra_idx
              (mword_of_int 0x3b2) (mword_of_int 0x1a)
              (ui_init_16 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (A9h) "Hcg Hpc".
    set (p6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1a : mword 64)]> p5).
    assert (Hp6ra : p6 !!! Regidx ra_idx = (mword_of_int 0x1a : mword 64))
      by exact (upd_eq p5 (Regidx ra_idx) _).
    assert (Hp6a0 : p6 !!! Regidx a0_idx = (mword_of_int INIT_CONSOLE : mword 64))
      by exact (eq_trans (upd_ne p5 (Regidx ra_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)) Hp5a0).
    assert (Hspp6 : p6 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (eq_trans (upd_ne p5 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hspp5).
    iEval (change (mword_of_int 0x3b2 : mword 64)
             with (mword_of_int InitSyms.open : mword 64)) in "Hpc".
    assert (Hpreo : init_layout pt /\ init_text_sub A4 /\
                    is_aligned_vaddr (Virtaddr (p6 !!! Regidx ra_idx)) 2 = true).
    { split_and!; [ exact Hlay | exact (init_img_text A4 Ha4)
                  | rewrite Hp6ra; vm_compute; reflexivity ]. }
    iApply (wp_init_open C pt Q W A9h A4 p6 Hpreo (init_proto_open C pt Q W)
              ltac:(rewrite Hp6a0; rewrite Hucons; exact (Hcons A4 Ha4))
              with "Hcg Hpc []").
    iIntros (AAh oret) "Hcg Hpc".
    iEval (rewrite Hp6ra) in "Hpc".
    set (p7 := <[Regidx a0_idx := oret]>
                 (<[Regidx a7_idx := (mword_of_int SYS_open : mword 64)]> p6)).
    assert (Hspp7 : p7 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64)).
    { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      refine (eq_trans (upd_ne p6 (Regidx a7_idx) (Regidx csp_rs1) _
                          ltac:(vm_compute; discriminate)) _).
      exact Hspp6. }

    (* ---- 0x1a  bltz a0,64   -- did open fail? ---- *)
    destruct (uv_btaken BLT (p7 !!! Regidx (mword_of_int 10 : mword 5))
                            zero_reg) eqn:Htk1a.
    { (* NO console: mknod it, open it again, and rejoin at 0x1e ------- *)
      iApply (wp_uv_btype0 C pt Pinit A4 p7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) (mword_of_int 10 : mword 5)
                BLT true (mword_of_int 0x64)
                (ui_init_1a pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(symmetry; exact Htk1a)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hx; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AB) "Hcg Hpc".

      (* ---- 0x64  li a2,0 ---- *)
      iApply (wp_uv_cli C pt Pinit A4 p7 (mword_of_int 0x64)
                (mword_of_int 0 : mword 6) a2_idx (mword_of_int 0)
                (ui_init_64 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AC) "Hcg Hpc".
      set (q1 := <[Regidx a2_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> p7).
      assert (E64 : add_vec_int (mword_of_int 0x64 : mword 64) 2
                    = mword_of_int 0x66)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E64) in "Hpc".

      (* ---- 0x66  li a1,1   (CONSOLE major) ---- *)
      iApply (wp_uv_cli C pt Pinit A4 q1 (mword_of_int 0x66)
                (mword_of_int 1 : mword 6) a1_idx (mword_of_int 1)
                (ui_init_66 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AD) "Hcg Hpc".
      set (q2 := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int 1 : mword 64)]> q1).
      assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2
                    = mword_of_int 0x68)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E66) in "Hpc".

      (* ---- 0x68  auipc a0,0x1 ---- *)
      iApply (wp_uv_auipc C pt Pinit A4 q2 (mword_of_int 0x68)
                (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x1068)
                (ui_init_68 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AE) "Hcg Hpc".
      set (q3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x1068 : mword 64)]> q2).
      assert (Hq3a0 : q3 !!! Regidx a0_idx = (mword_of_int 0x1068 : mword 64))
        by exact (upd_eq q2 (Regidx a0_idx) _).
      assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 4
                    = mword_of_int 0x6c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E68) in "Hpc".

      (* ---- 0x6c  addi a0,a0,-1784 ---- *)
      iApply (wp_uv_addi C pt Pinit A4 q3 (mword_of_int 0x6c)
                (mword_of_int 2312 : mword 12) a0_idx a0_idx
                (mword_of_int INIT_CONSOLE)
                (ui_init_6c pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hq3a0;
                      assert (Hc : (sign_extend' 64 (mword_of_int 2312 : mword 12)
                                    : mword 64) = mword_of_int (-1784))
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Hc; rewrite moi_add; f_equal;
                      unfold INIT_CONSOLE; lia)
                with "Hcg Hpc").
      iIntros (AF) "Hcg Hpc".
      set (q4 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int INIT_CONSOLE : mword 64)]> q3).
      assert (Hq4a0 : q4 !!! Regidx a0_idx
                      = (mword_of_int INIT_CONSOLE : mword 64))
        by exact (upd_eq q3 (Regidx a0_idx) _).
      assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 4
                    = mword_of_int 0x70)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E6c) in "Hpc".

      (* ---- 0x70  jal mknod ---- *)
      iApply (wp_uv_jal C pt Pinit A4 q4 (mword_of_int 0x70)
                (mword_of_int 842 : mword 21) ra_idx
                (mword_of_int 0x3ba) (mword_of_int 0x74)
                (ui_init_70 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AG) "Hcg Hpc".
      set (q5 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x74 : mword 64)]> q4).
      assert (Hq5ra : q5 !!! Regidx ra_idx = (mword_of_int 0x74 : mword 64))
        by exact (upd_eq q4 (Regidx ra_idx) _).
      assert (Hq5a0 : q5 !!! Regidx a0_idx
                      = (mword_of_int INIT_CONSOLE : mword 64))
        by exact (eq_trans (upd_ne q4 (Regidx ra_idx) (Regidx a0_idx) _
                              ltac:(vm_compute; discriminate)) Hq4a0).
      assert (Hq5sp : q5 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64)).
      { refine (eq_trans (upd_ne q4 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne q3 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne q2 (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne q1 (Regidx a1_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne p7 (Regidx a2_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hspp7. }
      iEval (change (mword_of_int 0x3ba : mword 64)
               with (mword_of_int InitSyms.mknod : mword 64)) in "Hpc".
      assert (Hprem : init_layout pt /\ init_text_sub A4 /\
                      is_aligned_vaddr (Virtaddr (q5 !!! Regidx ra_idx)) 2 = true).
      { split_and!; [ exact Hlay | exact (init_img_text A4 Ha4)
                    | rewrite Hq5ra; vm_compute; reflexivity ]. }
      iApply (wp_init_mknod C pt Q W AG A4 q5 Hprem (init_proto_mknod C pt Q W)
                ltac:(rewrite Hq5a0; rewrite Hucons; exact (Hcons A4 Ha4))
                with "Hcg Hpc []").
      iIntros (AH mret) "Hcg Hpc".
      iEval (rewrite Hq5ra) in "Hpc".
      set (q6 := <[Regidx a0_idx := mret]>
                   (<[Regidx a7_idx := (mword_of_int SYS_mknod : mword 64)]> q5)).
      assert (Hq6sp : q6 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64)).
      { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne q5 (Regidx a7_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hq5sp. }

      (* ---- 0x74  li a1,2 ---- *)
      iApply (wp_uv_cli C pt Pinit A4 q6 (mword_of_int 0x74)
                (mword_of_int 2 : mword 6) a1_idx (mword_of_int 2)
                (ui_init_74 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AI) "Hcg Hpc".
      set (q7 := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int 2 : mword 64)]> q6).
      assert (Hq7sp : q7 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne q6 (Regidx a1_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hq6sp).
      assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2
                    = mword_of_int 0x76)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E74) in "Hpc".

      (* ---- 0x76  auipc a0,0x1 ---- *)
      iApply (wp_uv_auipc C pt Pinit A4 q7 (mword_of_int 0x76)
                (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x1076)
                (ui_init_76 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AJ) "Hcg Hpc".
      set (q8 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x1076 : mword 64)]> q7).
      assert (Hq8a0 : q8 !!! Regidx a0_idx = (mword_of_int 0x1076 : mword 64))
        by exact (upd_eq q7 (Regidx a0_idx) _).
      assert (Hq8sp : q8 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne q7 (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hq7sp).
      assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 4
                    = mword_of_int 0x7a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E76) in "Hpc".

      (* ---- 0x7a  addi a0,a0,-1798 ---- *)
      iApply (wp_uv_addi C pt Pinit A4 q8 (mword_of_int 0x7a)
                (mword_of_int 2298 : mword 12) a0_idx a0_idx
                (mword_of_int INIT_CONSOLE)
                (ui_init_7a pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hq8a0;
                      assert (Hc : (sign_extend' 64 (mword_of_int 2298 : mword 12)
                                    : mword 64) = mword_of_int (-1798))
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Hc; rewrite moi_add; f_equal;
                      unfold INIT_CONSOLE; lia)
                with "Hcg Hpc").
      iIntros (AK) "Hcg Hpc".
      set (q9 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int INIT_CONSOLE : mword 64)]> q8).
      assert (Hq9a0 : q9 !!! Regidx a0_idx
                      = (mword_of_int INIT_CONSOLE : mword 64))
        by exact (upd_eq q8 (Regidx a0_idx) _).
      assert (Hq9sp : q9 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne q8 (Regidx a0_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hq8sp).
      assert (E7a : add_vec_int (mword_of_int 0x7a : mword 64) 4
                    = mword_of_int 0x7e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E7a) in "Hpc".

      (* ---- 0x7e  jal open ---- *)
      iApply (wp_uv_jal C pt Pinit A4 q9 (mword_of_int 0x7e)
                (mword_of_int 820 : mword 21) ra_idx
                (mword_of_int 0x3b2) (mword_of_int 0x82)
                (ui_init_7e pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AL) "Hcg Hpc".
      set (qa := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x82 : mword 64)]> q9).
      assert (Hqara : qa !!! Regidx ra_idx = (mword_of_int 0x82 : mword 64))
        by exact (upd_eq q9 (Regidx ra_idx) _).
      assert (Hqaa0 : qa !!! Regidx a0_idx
                      = (mword_of_int INIT_CONSOLE : mword 64))
        by exact (eq_trans (upd_ne q9 (Regidx ra_idx) (Regidx a0_idx) _
                              ltac:(vm_compute; discriminate)) Hq9a0).
      assert (Hqasp : qa !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64))
        by exact (eq_trans (upd_ne q9 (Regidx ra_idx) (Regidx csp_rs1) _
                              ltac:(vm_compute; discriminate)) Hq9sp).
      iEval (change (mword_of_int 0x3b2 : mword 64)
               with (mword_of_int InitSyms.open : mword 64)) in "Hpc".
      assert (Hpreo2 : init_layout pt /\ init_text_sub A4 /\
                       is_aligned_vaddr (Virtaddr (qa !!! Regidx ra_idx)) 2 = true).
      { split_and!; [ exact Hlay | exact (init_img_text A4 Ha4)
                    | rewrite Hqara; vm_compute; reflexivity ]. }
      iApply (wp_init_open C pt Q W AL A4 qa Hpreo2 (init_proto_open C pt Q W)
                ltac:(rewrite Hqaa0; rewrite Hucons; exact (Hcons A4 Ha4))
                with "Hcg Hpc []").
      iIntros (AM oret2) "Hcg Hpc".
      iEval (rewrite Hqara) in "Hpc".
      set (qb := <[Regidx a0_idx := oret2]>
                   (<[Regidx a7_idx := (mword_of_int SYS_open : mword 64)]> qa)).
      assert (Hqbsp : qb !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 32) : mword 64)).
      { refine (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        refine (eq_trans (upd_ne qa (Regidx a7_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) _).
        exact Hqasp. }

      (* ---- 0x82  j 1e ---- *)
      iApply (wp_uv_cj C pt Pinit A4 qb (mword_of_int 0x82)
                (mword_of_int 1998 : mword 11) (mword_of_int 0x1e)
                (ui_init_82 pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (AN) "Hcg Hpc".
      iApply (init_main_from1e AN A4 qb sp0 Hlay ltac:(lia) Ha4 Hst4 Hqbsp
                with "Hobs Hcg Hpc"). }

    (* the console was there ------------------------------------------- *)
    iApply (wp_uv_btype0 C pt Pinit A4 p7 (mword_of_int 0x1a)
              (mword_of_int 74 : mword 13) (mword_of_int 10 : mword 5)
              BLT false (mword_of_int 0x64)
              (ui_init_1a pt A4 (ilay_text pt Hlay) (init_img_text A4 Ha4))
              ltac:(symmetry; exact Htk1a)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hx; discriminate)
              with "Hcg Hpc").
    iIntros (AB) "Hcg Hpc".
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 4
                  = mword_of_int 0x1e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E1a) in "Hpc".
    iApply (init_main_from1e AB A4 p7 sp0 Hlay ltac:(lia) Ha4 Hst4 Hspp7
              with "Hobs Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5 start, and THE TOP THEOREM.                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_init_start (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_init_start_body (CID := CIDp) C pt Q W M m sp0.
  Proof.
    intros Hlay Himg Hsp Hst Hfr.
    unfold init_frame_ok in Hfr.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    destruct (uv_stack_split pt M sp0 272 16 256 eq_refl ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hs16 & Hs256).
    assert (Espb : add_vec_int sp0 (- 16) = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (uv_stack_sp_moi pt M sp0 16 Hs16).
    rewrite Espb in Hs256.
    assert (Husp : uint (mword_of_int (uint sp0 - 16) : mword 64) = uint sp0 - 16)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hsp' : m !!! Regidx csp_rs1 = (mword_of_int (uint sp0) : mword 64))
      by (rewrite moi_of_uint; exact Hsp).
    iIntros "Hcg #Hobs Hpc".
    iEval (change (mword_of_int InitSyms.start : mword 64)
             with (mword_of_int 0xbc : mword 64)) in "Hpc".

    (* ---- 0xbc  c.addi sp,sp,-16 ---- *)
    assert (Hwbc : (mword_of_int (uint sp0 - 16) : mword 64)
                   = add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { assert (Hcst : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                      : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hsp'. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Pinit M m (mword_of_int 0xbc)
              (mword_of_int 48 : mword 6) (mword_of_int 2 : mword 5)
              (mword_of_int (uint sp0 - 16))
              (ui_init_bc pt M (ilay_text pt Hlay) (init_img_text M Himg))
              ltac:(vm_compute; discriminate) Hwbc
              with "Hcg Hpc").
    iIntros (S1) "Hcg Hpc".
    set (v1 := <[Regidx (mword_of_int 2 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0 - 16) : mword 64)]> m).
    assert (Hv1sp : v1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hv1ra : v1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hv1s0 : v1 !!! Regidx (mword_of_int 8 : mword 5)
                    = m !!! Regidx (mword_of_int 8 : mword 5))
      by exact (upd_ne m (Regidx csp_rs1) (Regidx (mword_of_int 8 : mword 5)) _
                  ltac:(vm_compute; discriminate)).
    assert (Ebc : add_vec_int (mword_of_int 0xbc : mword 64) 2
                  = mword_of_int 0xbe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ebc) in "Hpc".

    (* ---- 0xbe  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt S1 Pinit M v1 sp0 (mword_of_int 0xbe)
              (mword_of_int 1 : mword 6) ra_idx 16 8
              (ui_init_be pt M (ilay_text pt Hlay) (init_img_text M Himg)) Hs16
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hv1sp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (S2) "Hcg Hpc".
    iEval (rewrite Hv1ra) in "Hcg".
    set (B1 := uM_store8 M (uint sp0 - 16 + 8) (m !!! Regidx ra_idx)).
    assert (Hob1 : uM_only M B1 (uint sp0 - 16) 16)
      by (rewrite /B1; apply uM_only_store8; lia).
    assert (Hb1i : init_img_sub B1)
      by exact (init_img_only M B1 (uint sp0 - 16) 16 ltac:(lia) Hob1 Himg).
    assert (Hb1s : uv_stack pt B1 sp0 16)
      by exact (uM_only_stack pt M B1 sp0 16 (uint sp0 - 16) 16 Hob1 Hs16).
    assert (Ebe : add_vec_int (mword_of_int 0xbe : mword 64) 2
                  = mword_of_int 0xc0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ebe) in "Hpc".

    (* ---- 0xc0  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uv_frame_store C pt S2 Pinit B1 v1 sp0 (mword_of_int 0xc0)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5) 16 0
              (ui_init_c0 pt B1 (ilay_text pt Hlay) (init_img_text B1 Hb1i)) Hb1s
              ltac:(lia) ltac:(lia) ltac:(reflexivity) Hv1sp
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (S3) "Hcg Hpc".
    iEval (rewrite Hv1s0) in "Hcg".
    set (B2 := uM_store8 B1 (uint sp0 - 16 + 0)
                 (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Hob2 : uM_only B1 B2 (uint sp0 - 16) 16)
      by (rewrite /B2; apply uM_only_store8; lia).
    assert (Hb2i : init_img_sub B2)
      by exact (init_img_only B1 B2 (uint sp0 - 16) 16 ltac:(lia) Hob2 Hb1i).
    assert (Hacc2 : uM_only M B2 (uint sp0 - 16) 16)
      by exact (uM_only_trans M B1 B2 (uint sp0 - 16) 16 Hob1 Hob2).
    assert (Hb2s : uv_stack pt B2 sp0 272)
      by exact (uM_only_stack pt M B2 sp0 272 (uint sp0 - 16) 16 Hacc2 Hst).
    assert (Hb2s256 : uv_stack pt B2 (mword_of_int (uint sp0 - 16)) 256)
      by exact (uM_only_stack pt M B2 (mword_of_int (uint sp0 - 16)) 256
                  (uint sp0 - 16) 16 Hacc2 Hs256).
    assert (Ec0 : add_vec_int (mword_of_int 0xc0 : mword 64) 2
                  = mword_of_int 0xc2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ec0) in "Hpc".

    (* ---- 0xc2  c.addi4spn s0,sp,16 ---- *)
    assert (Hwc2 : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (v1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { assert (Hcst : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                      : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hcst. rewrite Hv1sp. rewrite moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Pinit B2 v1 (mword_of_int 0xc2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (mword_of_int (uint sp0))
              (ui_init_c2 pt B2 (ilay_text pt Hlay) (init_img_text B2 Hb2i))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hwc2
              with "Hcg Hpc").
    iIntros (S4) "Hcg Hpc".
    set (v2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> v1).
    assert (Hv2sp : v2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (eq_trans (upd_ne v1 (Regidx (mword_of_int 8 : mword 5))
                            (Regidx csp_rs1) _ ltac:(vm_compute; discriminate))
                         Hv1sp).
    assert (Ec2 : add_vec_int (mword_of_int 0xc2 : mword 64) 2
                  = mword_of_int 0xc4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ec2) in "Hpc".

    (* ---- 0xc4  jal main   (which never returns) ---- *)
    iApply (wp_uv_jal C pt Pinit B2 v2 (mword_of_int 0xc4)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x0) (mword_of_int 0xc8)
              (ui_init_c4 pt B2 (ilay_text pt Hlay) (init_img_text B2 Hb2i))
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (S5) "Hcg Hpc".
    set (v3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xc8 : mword 64)]> v2).
    assert (Hv3sp : v3 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 16) : mword 64))
      by exact (eq_trans (upd_ne v2 (Regidx ra_idx) (Regidx csp_rs1) _
                            ltac:(vm_compute; discriminate)) Hv2sp).
    iEval (change (mword_of_int 0x0 : mword 64)
             with (mword_of_int InitSyms.main : mword 64)) in "Hpc".
    iApply (wp_init_main S5 B2 v3 (mword_of_int (uint sp0 - 16))
              Hlay Hb2i Hv3sp Hb2s256
              ltac:(unfold init_frame_ok; rewrite Husp; lia)
              with "Hcg Hobs Hpc").
  Qed.

End UProofInit.

(* sentinel: the whole init verification -- the printf cone, both unbounded
   loops, and every branch of every syscall test -- rests on nothing but the
   platform axioms and functional extensionality. *)
Print Assumptions wp_init_start.
