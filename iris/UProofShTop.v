(* UProofShTop.v -- the VERIFIED-EXECUTION proofs of the `sh` program's two
   FORK/EXEC functions (claude-notes/projects/user-sh.md):

     wp_sh_fork1    fork1()      @0x68   frame; jal fork; test -1; unframe
     wp_sh_runcmd   runcmd(cmd)  @0x8e   frame; switch (jump table); EXEC arm

   [fork1] is the small one: the `panic("fork")' arm at 0x82 is UNREACHABLE
   because [UmodeIo]'s [IoFork] arm hands back `uint ret = 0 \/ 0 < sint
   ret' -- so the `beq a0,a5' at 0x76 is a FALL-THROUGH and the 335
   instructions of fprintf/vprintf behind it never enter the catalog.

   [runcmd] is stated for the EXEC case only, the one the input reaches.
   Its `switch (cmd->type)' compiles to a JUMP TABLE at 0x1398 in .rodata:

       9c  lw   a4,0(a0)          a4 := cmd->type                = 1
       a0  bltu a5,a4,c2          5 <u 1?  no -- fall through
       a4  lwu  a5,0(a0)          a5 := (unsigned) cmd->type     = 1
       a8  slli a5,a5,2           a5 := 4
       aa  auipc a4,0x1           a4 := 0xaa + 0x1000            = 0x10aa
       ae  addi a4,a4,750         a4 := the table base           = 0x1398
       b2  add  a5,a5,a4          a5 := &table[1]                = 0x139c
       b4  lw   a5,0(a5)          a5 := table[1]  (a BYTE OFFSET, signed)
       b6  add  a5,a5,a4          a5 := 0x1398 + table[1]        = 0xce
       b8  jr   a5               -> the EXEC arm

   The four bytes at 0x139c are read off the DUMPED IMAGE ([ShData.sh_data],
   through [sh_data_sub]) -- the table is data, not code, so no [ui_sh_*]
   fact covers it and [sh_img_sub] is the premise that reaches it.  The arm
   then loads argv[0], finds it non-null, and reaches `exec(argv[0], cmd->
   argv)' at 0xd6, which DOES NOT RETURN: [IoExec]'s arm has no continuation
   and consumes the caller's [Q path args].  That is the theorem's payload.

   ------------------------------------------------------------------------
   CONTRACT DRIFT -- REPORTED, AND NOW ADOPTED IN USpecSh.v.  All three
   defects below are FIXED in the contracts; this note is kept as the
   record of what was wrong and why, because each one is a premise whose
   absence is invisible until a proof is attempted.

   (D1) Both [wp_sh_fork1_body] and [wp_sh_runcmd_exec_body] are MISSING the
   frame-height premise [sh_frame_ok] that every other frame-carving
   contract in USpecSh.v carries (sbrk/strlen/strchr/memset/free/malloc at
   16, gets at 96, execcmd at 128, main/start as [Hstkhi]).  [uv_stack]
   alone guarantees only `4096 <= uint sp0 - n' (UmodeAbi.us_lo), while sh's
   TEXT keys run to 8192 and its DATA keys to 12288 (UCodeSh.sh_bytes_key_lt
   / sh_data_key_lt), so without it a prologue spill may legally land on the
   program image and NEITHER [sh_text_sub] NOR [sh_data_sub] survives the
   frame carve -- i.e. no [ui_sh_*] fact and, for runcmd, no jump-table byte
   is available after 0x90.

   (D2) [wp_sh_runcmd_exec_body] does not say [cmd] is ALIGNED.  The switch
   reads `lw a4,0(cmd)' and `lwu a5,0(cmd)' and the EXEC arm reads
   `ld a0,8(cmd)', so the node must be 4- and 8-aligned; nothing in
   [Htype]/[Hp0]/[Hrd] implies it ([uM_bytes] and [uv_rd] are byte-wise).
   The real node is [malloc]'s, hence 16-aligned, which is what is assumed
   here.

   (D3) [wp_sh_runcmd_exec_body]'s [Hexec] does not say WHERE the exec
   picture lives, and it cannot: the string pointers inside [uargv_at] are
   EXISTENTIAL, so no premise stated beside it can bound them.  runcmd
   spills ra/s0/s1 into its frame BEFORE reading argv[0], so unless the
   picture is known to sit below the frame, [uexec_args] does not survive
   the prologue.  [USpecSh.sh_exec_below] is [uexec_args] plus exactly those
   bounds, at the bound `hbase + hlen' -- which, with (D1), is the frame's
   floor.  It SUBSUMES [Hexec], so adopting it lets [Hexec] be dropped.

   [wp_sh_fork1_body] now carries [Hfr]; [wp_sh_runcmd_exec_body] carries
   [Hal], [Hchi], [Hbel] and [Hfr], and its old [Hexec] is GONE ([Hbel]
   subsumes it, via [USpecSh.sh_exec_below_args]).  [sh_exec_below] and its
   three lemmas live in USpecSh.v §0c, so nothing about them is restated
   here.
   ------------------------------------------------------------------------ *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh UProofShLib.
(* for [wp_sh_spill], the frame-generic c.sdsp -- protocol- and
   program-generic already, so runcmd's 48-byte frame is an instance. *)
Require Import UProofShIo.
(* re-imported LAST on purpose: WpUmodeStep.v's funnel names its optional
   gpr write [uv_wr], which otherwise shadows UmodeAbi's writable-window
   record of the same name. *)
Require Import UmodeAbi.
Require User.ShSyms User.ShInstrs User.ShData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The image-preservation shims.                                       *)
(*                                                                        *)
(* UProofShLib.v's [sh_text_sub_store8] is [Local], so its twin is proved  *)
(* here -- and this file needs the DATA half as well, because runcmd reads *)
(* its jump table out of .rodata AFTER carving its frame.                 *)
(* ===================================================================== *)

Local Lemma sht_text_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma sht_data_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_data_sub M -> 12288 <= a -> sh_data_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_data_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Local Lemma sht_img_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_img_sub M -> 12288 <= a -> sh_img_sub (uM_store8 M a v).
Proof.
  intros [Ht Hd] Ha. split.
  - apply sht_text_store8; [ exact Ht | lia ].
  - apply sht_data_store8; [ exact Hd | lia ].
Qed.

Local Lemma sht_store8_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (k < a \/ a + 8 <= k) -> uM_store8 M a v !! k = M !! k.
Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

(* [-1] as a 64-bit word, in the two readings the [beq a0,a5] arm needs.
   [IoFork]'s arm hands back `uint ret = 0 \/ 0 < sint ret'; both disjuncts
   refute `ret = -1', but through DIFFERENT projections. *)
Local Lemma sht_uint_m1 : uint (mword_of_int (-1) : mword 64) = Z64 - 1.
Proof. rewrite uint_unsigned moi_unsigned. vm_compute. reflexivity. Qed.

Local Lemma sht_sint_m1 : sint (mword_of_int (-1) : mword 64) = -1.
Proof.
  change (sint (mword_of_int (-1) : mword 64))
    with (bv_signed (mword_of_int (-1) : mword 64)).
  unfold bv_signed, bv_swrap, bv_wrap.
  rewrite moi_unsigned. vm_compute. reflexivity.
Qed.

Local Lemma sht_only_store8 (M : gmap Z (bv 8)) (lo n a : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n -> uM_only M (uM_store8 M a v) lo n.
Proof.
  intros H1 H2. split.
  - intros k Hk. exact (uM_store8_is_Some _ _ _ k Hk).
  - intros k Hk. apply sht_store8_ne. lia.
Qed.

Local Lemma upd_read (m : regfile) (i j : mword 5) (v w : mword 64) :
  Regidx j <> Regidx i -> m !!! Regidx j = w ->
  <[Regidx i := v]> m !!! Regidx j = w.
Proof. intros Hne Hm. rewrite (upd_ne m (Regidx i) (Regidx j) v Hne). exact Hm. Qed.

Section UProofShTop.
  Context `{!riscvGS Σ} `{!uioG Σ}.
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


  (* ------------------------------------------------------------------- *)
  (* §1 fork1 @0x68 -- frame; jal fork; test -1; frame restore.           *)
  (*                                                                      *)
  (*   68..6e  the shared 16-byte gcc prologue (UmodeFrame.v)             *)
  (*   70      jal ra, c7e <fork>                                         *)
  (*   74      c.li a5,-1                                                 *)
  (*   76      beq a0,a5,82   -- NOT TAKEN: [IoFork]'s arm hands back     *)
  (*                             `uint ret = 0 \/ 0 < sint ret', so the   *)
  (*                             panic at 0x82 is unreachable             *)
  (*   7a..80  the shared 16-byte gcc epilogue                            *)
  (*                                                                      *)
  (* [sh_frame_ok] is the MISSING premise (see the file header): without   *)
  (* it [uv_stack] permits a frame at 4096 and the prologue's two [sd]s    *)
  (* may land on the program TEXT, after which no [ui_sh_*] fact holds.    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_fork1 (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_sh_fork1_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0.
  Proof.
    intros Hlay Htext Hsp Hst Hfr Hret2.
    unfold sh_frame_ok in Hfr.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & Hsfork1 & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & Hsfork & _ & _ & _ & _).
    pose proof (shl_text pt hbase hlen Hlay) as Hltext.
    pose proof (shl_hlo pt hbase hlen Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom pt hbase hlen Hlay) as Hhroom.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    assert (Habove : 8192 <= uint sp0 - 16) by lia.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsfork1) in "Hpc".
    (* ---- 0x68..0x6e  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0x68 sh_text_sub 8192 M m sp0
              Htext sht_text_store8 Habove Hsp Hst
              (ui_sh_68 pt M Hltext Htext)
              (fun Mx Hx => ui_sh_6a pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_6c pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_6e pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (mp := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sht_text_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sht_text_store8; [ exact Htext1 | lia ]).
    (* the ONE image effect: the frame carve *)
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (sht_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(lia)).
        unfold M1. apply sht_store8_ne. lia. }
    (* ---- 0x70  jal ra, 0xc7e <fork> ---- *)
    assert (Htgt : (mword_of_int 0xc7e : mword 64)
                   = add_vec (mword_of_int 0x70)
                       (sign_extend' 64 (mword_of_int 3086 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlink : (mword_of_int 0x74 : mword 64)
                    = add_vec_int (mword_of_int 0x70 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh M2 mp (mword_of_int 0x70)
              (mword_of_int 3086 : mword 21) ra_idx
              (mword_of_int 0xc7e) (mword_of_int 0x74)
              (ui_sh_70 pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Htgt Hlink
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mq := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x74 : mword 64)]> mp).
    iEval (rewrite <- Hsfork) in "Hpc".
    assert (Hra_q : mq !!! Regidx ra_idx = (mword_of_int 0x74 : mword 64))
      by exact (upd_eq mp (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x74 : mword 64))).
    (* ---- the call: fork ---- *)
    iApply (wp_sh_fork C pt gin gbrk hbase hlen Q CID2 M2 mq
              ltac:(split_and!;
                    [ exact Hlay | exact Htext2
                    | rewrite Hra_q; vm_compute; reflexivity ])
              with "Hcg Hpc [Hcont]").
    iIntros (CID3 ret) "%Hpid Hcg Hpc".
    iEval (rewrite Hra_q) in "Hpc".
    set (mf := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int SYS_fork : mword 64)]> mq)).
    (* ---- 0x74  c.li a5,-1 ---- *)
    assert (Hwm1 : (mword_of_int (-1) : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh M2 mf (mword_of_int 0x74)
              (mword_of_int 63 : mword 6) a5_idx (mword_of_int (-1) : mword 64)
              (ui_sh_74 pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Hwm1
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (mr := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (-1) : mword 64)]> mf).
    assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2
                  = mword_of_int 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E74) in "Hpc".
    (* ---- 0x76  beq a0,a5,0x82 -- the panic arm, NOT taken ---- *)
    assert (Ha0_r : mr !!! Regidx a0_idx = ret).
    { exact (eq_trans
               (upd_ne mf (Regidx a5_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_eq _ (Regidx a0_idx) ret)). }
    assert (Ha5_r : mr !!! Regidx a5_idx = (mword_of_int (-1) : mword 64))
      by exact (upd_eq mf (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (-1) : mword 64))).
    assert (Hntaken : false = uv_btaken BEQ (mr !!! Regidx a0_idx)
                                            (mr !!! Regidx a5_idx)).
    { rewrite Ha0_r Ha5_r. cbn [uv_btaken]. symmetry.
      apply eq_vec_false_iff. intro Heq.
      destruct Hpid as [H0 | Hs].
      - rewrite Heq sht_uint_m1 in H0. unfold Z64 in H0. lia.
      - rewrite Heq sht_sint_m1 in Hs. lia. }
    assert (Htgt76 : (mword_of_int 0x82 : mword 64)
                     = add_vec (mword_of_int 0x76)
                         (sign_extend' 64 (mword_of_int 12 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_btype C pt Psh M2 mr (mword_of_int 0x76)
              (mword_of_int 12 : mword 13) a5_idx a0_idx BEQ
              false (mword_of_int 0x82)
              (ui_sh_76 pt M2 Hltext Htext2)
              Hntaken Htgt76 ltac:(intro Hc; discriminate Hc)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 4
                  = mword_of_int 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E76) in "Hpc".
    (* ---- 0x7a..0x80  the epilogue ---- *)
    assert (Hst2 : uv_stack pt M2 sp0 16)
      by exact (uM_only_stack pt M M2 sp0 16 (uint sp0 - 16) 16 Honly Hst).
    assert (HbyR : uM_bytes M2 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. unfold M2.
      rewrite (sht_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      unfold M1.
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (HbyS : uM_bytes M2 (uint sp0 - 16) 8 (m !!! Regidx s0_idx)).
    { intros j Hj. unfold M2.
      exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx) j Hj). }
    assert (HwR : uM_word M2 (uint sp0 - 8) 8 = m !!! Regidx ra_idx).
    { apply (uM_bytes_inj M2 (uint sp0 - 8)); [ | exact HbyR ].
      exact (uM_word_bytes M2 (uint sp0 - 8) 8 ltac:(lia)
               (uM_bytes_exists M2 (uint sp0 - 8) 8 _ HbyR)). }
    assert (HwS : uM_word M2 (uint sp0 - 16) 8 = m !!! Regidx s0_idx).
    { apply (uM_bytes_inj M2 (uint sp0 - 16)); [ | exact HbyS ].
      exact (uM_word_bytes M2 (uint sp0 - 16) 8 ltac:(lia)
               (uM_bytes_exists M2 (uint sp0 - 16) 8 _ HbyS)). }
    assert (HspF : mr !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne mf (Regidx a5_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne _ (Regidx a0_idx) (Regidx sp_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mq (Regidx a7_idx) (Regidx sp_idx) _
                        ltac:(vm_compute; discriminate))
                     (eq_trans
                        (upd_ne mp (Regidx ra_idx) (Regidx sp_idx) _
                           ltac:(vm_compute; discriminate))
                        (eq_trans
                           (upd_ne _ (Regidx s0_idx) (Regidx sp_idx) _
                              ltac:(vm_compute; discriminate))
                           (upd_eq m (Regidx sp_idx) _)))))). }
    iApply (wp_uv_epilogue16 C pt CID5 Psh 0x7a M2 mr sp0
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
              Hst2 Hret2 HspF HwR HwS
              (ui_sh_7a pt M2 Hltext Htext2)
              (ui_sh_7c pt M2 Hltext Htext2)
              (ui_sh_7e pt M2 Hltext Htext2)
              (ui_sh_80 pt M2 Hltext Htext2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros (CID6 m') "%HA %HB %HC Hcg Hpc".
    (* ---- the register postcondition ---- *)
    assert (Hcs : ucallee_saved m m').
    { intros r Hr. unfold ucallee_saved_idx in Hr.
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
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HC r Nra Nsp Ns0). unfold mr, mf, mq, mp.
      exact (eq_trans
               (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5)
               (eq_trans
                  (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0)
                  (eq_trans
                     (upd_ne _ (Regidx a7_idx) (Regidx r) _ Na7)
                     (eq_trans
                        (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra)
                        (eq_trans
                           (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0)
                           (upd_ne m (Regidx sp_idx) (Regidx r) _ Nsp)))))). }
    assert (Hreta : m' !!! Regidx a0_idx = ret).
    { rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Ha0_r. }
    iApply ("Hcont" $! CID6 m' M2 ret with "[] [] [] [] Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Hreta.
    - iPureIntro. exact Hpid.
    - iPureIntro. exact Honly.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 runcmd @0x8e -- the EXEC arm, ending at the exec that never        *)
  (* returns.                                                             *)
  (*                                                                      *)
  (*   8e..94   a 48-byte frame: c.addi16sp -48, ra@40, s0@32, s0:=sp+48   *)
  (*   96       c.beqz a0,ba   -- cmd != 0, NOT taken                      *)
  (*   98..9a   s1@24; s1 := cmd                                           *)
  (*   9c..b8   the switch: type <= 5, then the jump table at 0x1398       *)
  (*   ce..d6   the EXEC arm: argv[0] != 0; exec(argv[0], &cmd->argv)      *)
  (*                                                                      *)
  (* THREE premises beyond [wp_sh_runcmd_exec_body] (header's drift note): *)
  (* the frame height, [cmd]'s 16-alignment (every load in the switch is   *)
  (* aligned, which nothing in the body implies), and the exec picture's   *)
  (* address bounds.                                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_runcmd_exec (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd p0 : Z)
      (path : list (bv 8)) (args : list (list (bv 8))) :
    wp_sh_runcmd_exec_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 cmd p0 path args.
  Proof.
    intros Hlay Himg Hsp Hst Hcmd Hnn Htype Hp0 Hp0nz Hal Hchi Hbel Hfr Hrd.
    unfold sh_frame_ok in Hfr. unfold SH_EXECCMD_SZ in Hchi.
    destruct sh_syms_pins as (_ & _ & _ & _ & Hsruncmd & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & Hsexec & _ & _).
    pose proof (shl_text pt hbase hlen Hlay) as Hltext.
    pose proof (shl_hlo pt hbase hlen Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom pt hbase hlen Hlay) as Hhroom.
    pose proof (shl_hhi pt hbase hlen Hlay) as Hhhi.
    change (2 ^ 38) with 274877906944 in Hhhi.
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (sh_img_data M Himg) as Hdata.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_lo _ _ _ _ Hrd) as Hcmd0.
    pose proof (proj1 Hbel) as Hp00.
    pose proof (proj1 (proj2 Hbel)) as Hpathb.
    pose proof (Nat2Z.is_nonneg (length path)) as Hplen.
    (* the aligned readings of [cmd] *)
    assert (Halm : cmd mod 16 = 0).
    { rewrite <- Hal. symmetry. apply Z.rem_mod_nonneg; lia. }
    assert (Hal4 : cmd mod 4 = 0).
    { rewrite (Znumtheory.Zmod_div_mod 4 16 cmd ltac:(lia) ltac:(lia)
                 ltac:(exists 4; lia)). rewrite Halm. apply Zmod_0_l. }
    assert (Hal8 : (cmd + 8) mod 8 = 0).
    { rewrite Zplus_mod.
      rewrite (Znumtheory.Zmod_div_mod 8 16 cmd ltac:(lia) ltac:(lia)
                 ltac:(exists 2; lia)). rewrite Halm.
      vm_compute (0 mod 8). vm_compute (8 mod 8). reflexivity. }
    (* the frame sits ABOVE the whole image and the heap *)
    assert (Habove : 12288 <= uint sp0 - 48) by lia.
    (* the load/ALU immediates, normalised once ([rewrite X by tac] does not
       parse under ssreflect, so each is a named equation) *)
    assert (Ez0_5 : (sign_extend' 64 (zero_extend' 12
                       (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64)
                    = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ez1_5 : (sign_extend' 64 (zero_extend' 12
                       (concat_vec (mword_of_int 1 : mword 5) ('b"000"))) : mword 64)
                    = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ei0_12 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                     = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ei8_12 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                     = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ei750_12 : (sign_extend' 64 (mword_of_int 750 : mword 12) : mword 64)
                       = mword_of_int 750)
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros "Hcg HQ Hpc".
    iEval (rewrite Hsruncmd) in "Hpc".
    (* ---- 0x8e  c.addi16sp sp,sp,-48 ---- *)
    assert (Hspc : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
    assert (Hi16 : (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))
                    : mword 64) = mword_of_int (-48))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hspw : (mword_of_int (uint sp0 - 48) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    { rewrite Hspc Hi16 moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x8e)
              (mword_of_int 61 : mword 6) (mword_of_int (uint sp0 - 48))
              (ui_sh_8e pt M Hltext Htext) Hspw with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 48) : mword 64)]> m).
    assert (E8e : add_vec_int (mword_of_int 0x8e : mword 64) 2 = mword_of_int 0x90)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8e) in "Hpc".
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 48) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 48) : mword 64))).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (unfold m1; apply upd_read; [ vm_compute; discriminate | exact Hcmd ]).
    (* ---- 0x90  c.sdsp ra,40(sp) ---- *)
    iApply (wp_sh_spill C pt CID1 Psh 0x90 0x92 48 40 (mword_of_int 5 : mword 6)
              ra_idx M m1 sp0 Hst Hsp1 ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_90 pt M Hltext Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (Ma := uM_store8 M (uint sp0 - 48 + 40) (m1 !!! Regidx ra_idx)).
    assert (HtextA : sh_text_sub Ma)
      by (unfold Ma; apply sht_text_store8; [ exact Htext | lia ]).
    assert (HdataA : sh_data_sub Ma)
      by (unfold Ma; apply sht_data_store8; [ exact Hdata | lia ]).
    assert (HstA : uv_stack pt Ma sp0 48).
    { apply (uv_stack_dom pt M Ma sp0 48); [ | exact Hst ].
      intros k Hk. unfold Ma. exact (uM_store8_is_Some _ _ _ k Hk). }
    (* ---- 0x92  c.sdsp s0,32(sp) ---- *)
    iApply (wp_sh_spill C pt CID2 Psh 0x92 0x94 48 32 (mword_of_int 4 : mword 6)
              s0_idx Ma m1 sp0 HstA Hsp1 ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_92 pt Ma Hltext HtextA)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (Mb := uM_store8 Ma (uint sp0 - 48 + 32) (m1 !!! Regidx s0_idx)).
    assert (HtextB : sh_text_sub Mb)
      by (unfold Mb; apply sht_text_store8; [ exact HtextA | lia ]).
    assert (HdataB : sh_data_sub Mb)
      by (unfold Mb; apply sht_data_store8; [ exact HdataA | lia ]).
    assert (HstB : uv_stack pt Mb sp0 48).
    { apply (uv_stack_dom pt Ma Mb sp0 48); [ | exact HstA ].
      intros k Hk. unfold Mb. exact (uM_store8_is_Some _ _ _ k Hk). }
    (* ---- 0x94  c.addi4spn s0,sp,48 ---- *)
    assert (Hi4spn : (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))
                      : mword 64) = mword_of_int 48)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hs0w : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))).
    { rewrite Hsp1 Hi4spn moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh Mb m1 (mword_of_int 0x94)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              (mword_of_int (uint sp0))
              (ui_sh_94 pt Mb Hltext HtextB)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hs0w
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (E94 : add_vec_int (mword_of_int 0x94 : mword 64) 2 = mword_of_int 0x96)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E94) in "Hpc".
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 48) : mword 64))
      by (unfold m2; apply upd_read; [ vm_compute; discriminate | exact Hsp1 ]).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (unfold m2; apply upd_read; [ vm_compute; discriminate | exact Ha0_1 ]).
    (* ---- 0x96  c.beqz a0,0xba -- cmd != 0, NOT taken ---- *)
    assert (Hcmdz : eq_vec (m2 !!! Regidx a0_idx) zero_reg = false).
    { rewrite Ha0_2. rewrite (moi_eq_zero cmd ltac:(unfold Z64; lia)).
      apply Z.eqb_neq. exact Hnn. }
    iApply (wp_uv_cbeqz C pt Psh Mb m2 (mword_of_int 0x96)
              (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (add_vec (mword_of_int 0x96)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 18 : mword 8) ('b"0")))))
              (ui_sh_96 pt Mb Hltext HtextB)
              ltac:(vm_compute; reflexivity)
              ltac:(symmetry; exact Hcmdz) eq_refl
              ltac:(intro Hc; discriminate Hc)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    assert (E96 : add_vec_int (mword_of_int 0x96 : mword 64) 2 = mword_of_int 0x98)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E96) in "Hpc".
    (* ---- 0x98  c.sdsp s1,24(sp) ---- *)
    iApply (wp_sh_spill C pt CID5 Psh 0x98 0x9a 48 24 (mword_of_int 3 : mword 6)
              s1_idx Mb m2 sp0 HstB Hsp2 ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_98 pt Mb Hltext HtextB)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    set (Mc := uM_store8 Mb (uint sp0 - 48 + 24) (m2 !!! Regidx s1_idx)).
    assert (HtextC : sh_text_sub Mc)
      by (unfold Mc; apply sht_text_store8; [ exact HtextB | lia ]).
    assert (HdataC : sh_data_sub Mc)
      by (unfold Mc; apply sht_data_store8; [ exact HdataB | lia ]).
    (* THE image effect of the whole prologue: three doublewords inside the
       48-byte frame, and nothing else *)
    assert (Honly : uM_only M Mc (uint sp0 - 48) 48).
    { apply (uM_only_trans M Mb Mc).
      - apply (uM_only_trans M Ma Mb).
        + unfold Ma. apply sht_only_store8; lia.
        + unfold Mb. apply sht_only_store8; lia.
      - unfold Mc. apply sht_only_store8; lia. }
    assert (HrdC : uv_rd pt Mc cmd 168).
    { apply (uM_only_rd pt M Mc cmd 168 (uint sp0 - 48) 48 Honly
               ltac:(right; lia)). exact Hrd. }
    assert (HtypeC : uM_bytes Mc cmd 4 (mword_of_int 1 : mword 32))
      by exact (sh_bytes_below M Mc cmd 4 _ (uint sp0 - 48) 48 Honly
                  ltac:(lia) Htype).
    assert (Hp0C : uM_bytes Mc (cmd + 8) 8 (mword_of_int p0 : mword 64))
      by exact (sh_bytes_below M Mc (cmd + 8) 8 _ (uint sp0 - 48) 48 Honly
                  ltac:(lia) Hp0).
    assert (HbelC : sh_exec_below Mc p0 (cmd + 8) path args (hbase + hlen))
      by exact (sh_exec_below_only M Mc p0 (cmd + 8) (hbase + hlen)
                  (uint sp0 - 48) 48 path args Honly ltac:(lia) Hbel).
    (* ---- 0x9a  c.mv s1,a0 ---- *)
    assert (Hmvw : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (m2 !!! Regidx a0_idx)).
    { rewrite Ha0_2. symmetry. apply moi_add_zero_l. }
    iApply (wp_uv_cmv C pt Psh Mc m2 (mword_of_int 0x9a)
              s1_idx a0_idx (mword_of_int cmd)
              (ui_sh_9a pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Hmvw
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    set (m3 := <[Regidx s1_idx := regval_into_reg (mword_of_int cmd : mword 64)]> m2).
    assert (E9a : add_vec_int (mword_of_int 0x9a : mword 64) 2 = mword_of_int 0x9c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E9a) in "Hpc".
    assert (Hs1_3 : m3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq m2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int cmd : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      by (unfold m3; apply upd_read; [ vm_compute; discriminate | exact Ha0_2 ]).
    (* the cmd node's own slot facts *)
    destruct (uv_slot4_facts cmd (mword_of_int cmd) ltac:(lia) Hal4
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Hcu & Hccan & Hcpg & Hcalg).
    destruct (uv_rd_leaf_at pt Mc cmd 168 cmd HrdC ltac:(lia))
      as (wc & Hwc & Hwcok).
    (* ---- 0x9c  c.lw a4,0(a0)  --  a4 := cmd->type = 1 ---- *)
    assert (Hva9c : (mword_of_int cmd : mword 64)
                    = add_vec (m3 !!! Regidx a0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))).
    { rewrite Ha0_3 Ez0_5 moi_add. f_equal; lia. }
    iApply (wp_uv_clw C pt Psh Mc m3 (mword_of_int 0x9c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx
              wc (mword_of_int cmd) (mword_of_int 1) (mword_of_int 1 : mword 32)
              (ui_sh_9c pt Mc Hltext HtextC)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              Hva9c Hwc Hwcok Hccan
              Hcpg
              Hcalg
              ltac:(rewrite Hcu; exact HtypeC)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    set (m4 := <[Regidx a4_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m3).
    assert (E9c : add_vec_int (mword_of_int 0x9c : mword 64) 2 = mword_of_int 0x9e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E9c) in "Hpc".
    (* ---- 0x9e  c.li a5,5 ---- *)
    iApply (wp_uv_cli C pt Psh Mc m4 (mword_of_int 0x9e)
              (mword_of_int 5 : mword 6) a5_idx (mword_of_int 5 : mword 64)
              (ui_sh_9e pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    set (m5 := <[Regidx a5_idx := regval_into_reg (mword_of_int 5 : mword 64)]> m4).
    assert (E9e : add_vec_int (mword_of_int 0x9e : mword 64) 2 = mword_of_int 0xa0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E9e) in "Hpc".
    assert (Ha5_5 : m5 !!! Regidx a5_idx = (mword_of_int 5 : mword 64))
      by exact (upd_eq m4 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 5 : mword 64))).
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { unfold m5. apply upd_read; [ vm_compute; discriminate | ].
      exact (upd_eq m3 (Regidx a4_idx)
               (regval_into_reg (mword_of_int 1 : mword 64))). }
    assert (Ha0_5 : m5 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { unfold m5. apply upd_read; [ vm_compute; discriminate | ].
      unfold m4. apply upd_read; [ vm_compute; discriminate | exact Ha0_3 ]. }
    (* ---- 0xa0  bltu a5,a4,0xc2 -- 5 <u 1 is FALSE ---- *)
    assert (Hbltu : false = uv_btaken BLTU (m5 !!! Regidx a5_idx)
                                           (m5 !!! Regidx a4_idx)).
    { rewrite Ha5_5 Ha4_5. cbn [uv_btaken]. symmetry.
      rewrite (moi_lt_u 5 1 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uv_btype C pt Psh Mc m5 (mword_of_int 0xa0)
              (mword_of_int 34 : mword 13) a4_idx a5_idx BLTU
              false (add_vec (mword_of_int 0xa0)
                       (sign_extend' 64 (mword_of_int 34 : mword 13)))
              (ui_sh_a0 pt Mc Hltext HtextC)
              Hbltu eq_refl ltac:(intro Hc; discriminate Hc)
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    assert (Ea0 : add_vec_int (mword_of_int 0xa0 : mword 64) 4 = mword_of_int 0xa4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea0) in "Hpc".
    (* ---- 0xa4  lwu a5,0(a0)  --  a5 := (unsigned) cmd->type = 1 ---- *)
    assert (Hvaa4 : (mword_of_int cmd : mword 64)
                    = add_vec (m5 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha0_5 Ei0_12 moi_add. f_equal; lia. }
    iApply (wp_uv_lwu C pt Psh Mc m5 (mword_of_int 0xa4)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              wc (mword_of_int cmd) (mword_of_int 1) (mword_of_int 1 : mword 32)
              (ui_sh_a4 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate)
              Hvaa4 Hwc Hwcok Hccan
              Hcpg
              Hcalg
              ltac:(rewrite Hcu; exact HtypeC)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    set (m6 := <[Regidx a5_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m5).
    assert (Ea4 : add_vec_int (mword_of_int 0xa4 : mword 64) 4 = mword_of_int 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea4) in "Hpc".
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 1 : mword 64))
      by exact (upd_eq m5 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 1 : mword 64))).
    (* ---- 0xa8  c.slli a5,a5,2  --  a5 := 4 ---- *)
    assert (Hsllw : (mword_of_int 4 : mword 64)
                    = shift_bits_left (m6 !!! Regidx a5_idx)
                        (subrange_vec_dec (mword_of_int 2 : mword 6)
                           (Z.sub log2_xlen 1) 0)).
    { rewrite Ha5_6. apply bv_eq. vm_compute. reflexivity. }
    iApply (wp_uv_cslli C pt Psh Mc m6 (mword_of_int 0xa8)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 4)
              (ui_sh_a8 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Hsllw
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    set (m7 := <[Regidx a5_idx := regval_into_reg (mword_of_int 4 : mword 64)]> m6).
    assert (Ea8 : add_vec_int (mword_of_int 0xa8 : mword 64) 2 = mword_of_int 0xaa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea8) in "Hpc".
    (* ---- 0xaa  auipc a4,0x1  --  a4 := 0x10aa ---- *)
    iApply (wp_uv_auipc C pt Psh Mc m7 (mword_of_int 0xaa)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 0x10aa)
              (ui_sh_aa pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x10aa : mword 64)]> m7).
    assert (Eaa : add_vec_int (mword_of_int 0xaa : mword 64) 4 = mword_of_int 0xae)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eaa) in "Hpc".
    assert (Ha4_8 : m8 !!! Regidx a4_idx = (mword_of_int 0x10aa : mword 64))
      by exact (upd_eq m7 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x10aa : mword 64))).
    (* ---- 0xae  addi a4,a4,750  --  a4 := THE JUMP TABLE, 0x1398 ---- *)
    assert (Haddw : (mword_of_int 0x1398 : mword 64)
                    = add_vec (m8 !!! Regidx a4_idx)
                        (sign_extend' 64 (mword_of_int 750 : mword 12))).
    { rewrite Ha4_8 Ei750_12 moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh Mc m8 (mword_of_int 0xae)
              (mword_of_int 750 : mword 12) a4_idx a4_idx (mword_of_int 0x1398)
              (ui_sh_ae pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Haddw
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x1398 : mword 64)]> m8).
    assert (Eae : add_vec_int (mword_of_int 0xae : mword 64) 4 = mword_of_int 0xb2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eae) in "Hpc".
    assert (Ha4_9 : m9 !!! Regidx a4_idx = (mword_of_int 0x1398 : mword 64))
      by exact (upd_eq m8 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 0x1398 : mword 64))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = (mword_of_int 4 : mword 64)).
    { unfold m9. apply upd_read; [ vm_compute; discriminate | ].
      unfold m8. apply upd_read; [ vm_compute; discriminate | ].
      exact (upd_eq m6 (Regidx a5_idx)
               (regval_into_reg (mword_of_int 4 : mword 64))). }
    (* ---- 0xb2  c.add a5,a5,a4  --  a5 := &table[1] = 0x139c ---- *)
    assert (Haddb2 : (mword_of_int 0x139c : mword 64)
                     = add_vec (m9 !!! Regidx a5_idx) (m9 !!! Regidx a4_idx)).
    { rewrite Ha5_9 Ha4_9 moi_add. f_equal; lia. }
    iApply (wp_uv_cadd C pt Psh Mc m9 (mword_of_int 0xb2)
              a5_idx a4_idx (mword_of_int 0x139c)
              (ui_sh_b2 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Haddb2
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    set (m10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0x139c : mword 64)]> m9).
    assert (Eb2 : add_vec_int (mword_of_int 0xb2 : mword 64) 2 = mword_of_int 0xb4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb2) in "Hpc".
    assert (Ha5_10 : m10 !!! Regidx a5_idx = (mword_of_int 0x139c : mword 64))
      by exact (upd_eq m9 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0x139c : mword 64))).
    assert (Ha4_10 : m10 !!! Regidx a4_idx = (mword_of_int 0x1398 : mword 64))
      by (unfold m10; apply upd_read; [ vm_compute; discriminate | exact Ha4_9 ]).
    (* ---- 0xb4  c.lw a5,0(a5) -- THE JUMP TABLE ENTRY, out of .rodata --- *)
    assert (Hget : forall (k : Z) (b : bv 8),
              ShData.sh_data !! k = Some b -> Mc !! k = Some b) by exact HdataC.
    (* table[1] = 0xffffed36 = -4810, the four bytes at 0x139c..0x139f.  The
       image's own byte is [Z_to_bv 8 0x36] and the window's is
       [nth_byte w 0]: the same VALUE with a different well-formedness
       proof, so the two only meet through [bv_eq] -- a bare
       [vm_compute; reflexivity] fails with "Unable to unify Some 54%bv
       with Some 54%bv". *)
    assert (D0 : Mc !! (0x139c + Z.of_nat 0) = Some (Z_to_bv 8 0x36))
      by (apply Hget; vm_compute; reflexivity).
    assert (D1 : Mc !! (0x139c + Z.of_nat 1) = Some (Z_to_bv 8 0xed))
      by (apply Hget; vm_compute; reflexivity).
    assert (D2 : Mc !! (0x139c + Z.of_nat 2) = Some (Z_to_bv 8 0xff))
      by (apply Hget; vm_compute; reflexivity).
    assert (D3 : Mc !! (0x139c + Z.of_nat 3) = Some (Z_to_bv 8 0xff))
      by (apply Hget; vm_compute; reflexivity).
    assert (Htab : uM_bytes Mc 0x139c 4 (mword_of_int 4294962486 : mword 32)).
    { intros j Hj.
      assert (Hj4 : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
      destruct_or! Hj4; subst j;
        [ rewrite D0 | rewrite D1 | rewrite D2 | rewrite D3 ];
        f_equal; apply bv_eq; vm_compute; reflexivity. }
    destruct (uv_slot4_facts 0x139c (mword_of_int 0x139c) ltac:(lia)
                ltac:(vm_compute; reflexivity)
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Htu & Htcan & Htpg & Htalg).
    destruct (sh_text_layout_load pt 0x139c Hltext ltac:(lia)) as (wt & Hwt & Hwtok).
    assert (Hvab4 : (mword_of_int 0x139c : mword 64)
                    = add_vec (m10 !!! Regidx a5_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))).
    { rewrite Ha5_10 Ez0_5 moi_add. f_equal; lia. }
    iApply (wp_uv_clw C pt Psh Mc m10 (mword_of_int 0xb4)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx
              wt (mword_of_int 0x139c) (mword_of_int (-4810))
              (mword_of_int 4294962486 : mword 32)
              (ui_sh_b4 pt Mc Hltext HtextC)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              Hvab4 Hwt Hwtok Htcan
              Htpg
              Htalg
              ltac:(rewrite Htu; exact Htab)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (-4810) : mword 64)]> m10).
    assert (Eb4 : add_vec_int (mword_of_int 0xb4 : mword 64) 2 = mword_of_int 0xb6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb4) in "Hpc".
    assert (Ha5_11 : m11 !!! Regidx a5_idx = (mword_of_int (-4810) : mword 64))
      by exact (upd_eq m10 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (-4810) : mword 64))).
    assert (Ha4_11 : m11 !!! Regidx a4_idx = (mword_of_int 0x1398 : mword 64))
      by (unfold m11; apply upd_read; [ vm_compute; discriminate | exact Ha4_10 ]).
    (* ---- 0xb6  c.add a5,a5,a4  --  a5 := 0x1398 - 4810 = 0xce ---- *)
    assert (Haddb6 : (mword_of_int 0xce : mword 64)
                     = add_vec (m11 !!! Regidx a5_idx) (m11 !!! Regidx a4_idx)).
    { rewrite Ha5_11 Ha4_11 moi_add. f_equal; lia. }
    iApply (wp_uv_cadd C pt Psh Mc m11 (mword_of_int 0xb6)
              a5_idx a4_idx (mword_of_int 0xce)
              (ui_sh_b6 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Haddb6
              with "Hcg Hpc").
    iIntros (CID17) "Hcg Hpc".
    set (m12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 0xce : mword 64)]> m11).
    assert (Eb6 : add_vec_int (mword_of_int 0xb6 : mword 64) 2 = mword_of_int 0xb8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eb6) in "Hpc".
    assert (Ha5_12 : m12 !!! Regidx a5_idx = (mword_of_int 0xce : mword 64))
      by exact (upd_eq m11 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 0xce : mword 64))).
    assert (Ha0_12 : m12 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { unfold m12. apply upd_read; [ vm_compute; discriminate | ].
      unfold m11. apply upd_read; [ vm_compute; discriminate | ].
      unfold m10. apply upd_read; [ vm_compute; discriminate | ].
      unfold m9. apply upd_read; [ vm_compute; discriminate | ].
      unfold m8. apply upd_read; [ vm_compute; discriminate | ].
      unfold m7. apply upd_read; [ vm_compute; discriminate | ].
      unfold m6. apply upd_read; [ vm_compute; discriminate | exact Ha0_5 ]. }
    assert (Hs1_12 : m12 !!! Regidx s1_idx = (mword_of_int cmd : mword 64)).
    { unfold m12. apply upd_read; [ vm_compute; discriminate | ].
      unfold m11. apply upd_read; [ vm_compute; discriminate | ].
      unfold m10. apply upd_read; [ vm_compute; discriminate | ].
      unfold m9. apply upd_read; [ vm_compute; discriminate | ].
      unfold m8. apply upd_read; [ vm_compute; discriminate | ].
      unfold m7. apply upd_read; [ vm_compute; discriminate | ].
      unfold m6. apply upd_read; [ vm_compute; discriminate | ].
      unfold m5. apply upd_read; [ vm_compute; discriminate | ].
      unfold m4. apply upd_read; [ vm_compute; discriminate | exact Hs1_3 ]. }
    (* ---- 0xb8  jr a5  --  the indexed jump lands on the EXEC arm ---- *)
    assert (Hjt : (mword_of_int 0xce : mword 64)
                  = ret_pc (m12 !!! Regidx a5_idx))
      by (rewrite Ha5_12; apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cjr C pt Psh Mc m12 (mword_of_int 0xb8)
              a5_idx (mword_of_int 0xce)
              (ui_sh_b8 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Hjt
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    (* ---- 0xce  ld a0,8(a0)  --  a0 := cmd->argv[0] ---- *)
    destruct (uv_slot8_facts (cmd + 8) (mword_of_int (cmd + 8)) ltac:(lia) Hal8
                ltac:(change (2 ^ 38) with 274877906944; lia) eq_refl)
      as (Hau & Hacan & Hapg & Halg8).
    destruct (uv_rd_leaf_at pt Mc cmd 168 (cmd + 8) HrdC ltac:(lia))
      as (wa & Hwa & Hwaok).
    assert (Hvace : (mword_of_int (cmd + 8) : mword 64)
                    = add_vec (m12 !!! Regidx a0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 1 : mword 5) ('b"000"))))).
    { rewrite Ha0_12 Ez1_5 moi_add. reflexivity. }
    iApply (wp_uv_cld C pt Psh Mc m12 (mword_of_int 0xce)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx
              wa (mword_of_int (cmd + 8)) (mword_of_int p0)
              (ui_sh_ce pt Mc Hltext HtextC)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              Hvace Hwa Hwaok Hacan
              Hapg
              Halg8
              ltac:(rewrite Hau; exact Hp0C)
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    set (m13 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p0 : mword 64)]> m12).
    assert (Ece : add_vec_int (mword_of_int 0xce : mword 64) 2 = mword_of_int 0xd0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ece) in "Hpc".
    assert (Ha0_13 : m13 !!! Regidx a0_idx = (mword_of_int p0 : mword 64))
      by exact (upd_eq m12 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int p0 : mword 64))).
    assert (Hs1_13 : m13 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by (unfold m13; apply upd_read; [ vm_compute; discriminate | exact Hs1_12 ]).
    (* ---- 0xd0  c.beqz a0,0xf0 -- argv[0] != 0, NOT taken ---- *)
    assert (Hp0z : eq_vec (m13 !!! Regidx a0_idx) zero_reg = false).
    { rewrite Ha0_13. rewrite (moi_eq_zero p0 ltac:(unfold Z64; lia)).
      apply Z.eqb_neq. exact Hp0nz. }
    iApply (wp_uv_cbeqz C pt Psh Mc m13 (mword_of_int 0xd0)
              (mword_of_int 16 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (add_vec (mword_of_int 0xd0)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 16 : mword 8) ('b"0")))))
              (ui_sh_d0 pt Mc Hltext HtextC)
              ltac:(vm_compute; reflexivity)
              ltac:(symmetry; exact Hp0z) eq_refl
              ltac:(intro Hc; discriminate Hc)
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    assert (Ed0 : add_vec_int (mword_of_int 0xd0 : mword 64) 2 = mword_of_int 0xd2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ed0) in "Hpc".
    (* ---- 0xd2  addi a1,s1,8  --  a1 := &cmd->argv ---- *)
    assert (Ha1w : (mword_of_int (cmd + 8) : mword 64)
                   = add_vec (m13 !!! Regidx s1_idx)
                       (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite Hs1_13 Ei8_12 moi_add. reflexivity. }
    iApply (wp_uv_addi C pt Psh Mc m13 (mword_of_int 0xd2)
              (mword_of_int 8 : mword 12) s1_idx a1_idx (mword_of_int (cmd + 8))
              (ui_sh_d2 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate) Ha1w
              with "Hcg Hpc").
    iIntros (CID21) "Hcg Hpc".
    set (m14 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int (cmd + 8) : mword 64)]> m13).
    assert (Ed2 : add_vec_int (mword_of_int 0xd2 : mword 64) 4 = mword_of_int 0xd6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ed2) in "Hpc".
    (* ---- 0xd6  jal ra,0xcbe <exec> ---- *)
    iApply (wp_uv_jal C pt Psh Mc m14 (mword_of_int 0xd6)
              (mword_of_int 3048 : mword 21) ra_idx
              (mword_of_int 0xcbe) (mword_of_int 0xda)
              (ui_sh_d6 pt Mc Hltext HtextC)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID22) "Hcg Hpc".
    set (m15 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0xda : mword 64)]> m14).
    iEval (rewrite <- Hsexec) in "Hpc".
    (* ---- THE EXEC.  a0 = argv[0], a1 = &cmd->argv ---- *)
    assert (Ha0_15 : m15 !!! Regidx a0_idx = (mword_of_int p0 : mword 64)).
    { unfold m15. apply upd_read; [ vm_compute; discriminate | ].
      unfold m14. apply upd_read; [ vm_compute; discriminate | exact Ha0_13 ]. }
    assert (Ha1_15 : m15 !!! Regidx a1_idx = (mword_of_int (cmd + 8) : mword 64)).
    { unfold m15. apply upd_read; [ vm_compute; discriminate | ].
      exact (upd_eq m13 (Regidx a1_idx)
               (regval_into_reg (mword_of_int (cmd + 8) : mword 64))). }
    assert (Hargs : uexec_args Mc (uint (m15 !!! Regidx a0_idx))
                                  (uint (m15 !!! Regidx a1_idx)) path args).
    { rewrite Ha0_15 Ha1_15.
      rewrite (uint_moi p0 ltac:(unfold Z64; lia)).
      rewrite (uint_moi (cmd + 8) ltac:(unfold Z64; lia)).
      exact (sh_exec_below_args Mc p0 (cmd + 8) (hbase + hlen) path args HbelC). }
    iApply (wp_sh_exec C pt gin gbrk hbase hlen Q CID22 Mc m15 path args
              Hlay HtextC Hargs with "Hcg HQ Hpc").
  Qed.

End UProofShTop.
