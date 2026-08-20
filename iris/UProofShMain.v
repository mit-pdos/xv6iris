(* UProofShMain.v -- the VERIFIED-EXECUTION proofs of the `sh' program's LAST
   two functions (claude-notes/projects/user-sh.md):

     wp_sh_main   main  @0x8e2   64-byte frame, ra + s0..s6 spilled
     wp_sh_start  start @0x9d0   16-byte frame, jal main ; jal exit

   Both DIVERGE, so neither has an epilogue and neither hands a caller
   anything back: [main] leaves through [exit(0)] on the parent's second
   REPL iteration and through [runcmd]'s [exec] in the child.

   THE FORK IS ONE PROOF COVERING BOTH PROCESSES.  [IoFork]'s arm gives a
   SINGLE continuation carrying `uint ret = 0 \/ 0 < sint ret', so the
   `c.beqz a0' at 0x930 is proved once, by case analysis on that
   disjunction: the [true] arm is the child (0x9c0: parsecmd, runcmd) and
   the [false] arm is the parent (0x932: wait(0), then the EOF iteration
   and exit(0)).  The linear resources are spent accordingly -- the
   theorem's [Q sh_echo_path sh_echo_argv] and [ubrk gbrk hbase] go to the
   CHILD (they flow into parsecmd and thence into the exec arm), the
   now-empty [ustdin gin []] goes to the PARENT (iteration 2's EOF), and
   each side simply DROPS what it does not need, which iProp's affinity
   permits.

   CARRYING .bss ACROSS getcmd.  main holds [Hbss] over the whole
   [0x2010,0x2098), but [gets] fills the command buffer at 0x2020, so that
   claim is FALSE afterwards.  The two NARROW windows [parsecmd] actually
   wants -- [SH_FREEP] (0x2010..0x2018) and [SH_BASE+8] (0x2090..0x2098) --
   are therefore sliced out BEFORE the call and transported across
   [getcmd]'s two disturbed windows ([SH_BUF] 100 and the 128-byte frame)
   and then across [fork1]'s 16-byte frame.  Neither window contains
   either, which is exactly why those premises are narrow.

   [parsecmd] (UProofShCmd.v) is still in flight and is carried as a
   section HYPOTHESIS, so closing the section makes it an ARGUMENT of both
   lemmas -- visible in the type, discharged by a one-line [apply] when
   that lane lands, and (unlike an [Admitted]) impossible to land by
   accident.  Everything else -- [fork1] and [runcmd] (UProofShTop.v), the
   IO path (UProofShIo.v), the stubs (UProofShLib.v) -- is used directly.

   Two contract defects were found here and have since been ADOPTED into
   the specs, so nothing below works around either:

   (M1) [wp_sh_main_body] / [wp_sh_start_body] took an unconstrained
   [(input : list (bv 8))], which read universally claims sh is safe on ANY
   stdin -- unprovable, and not the theorem.  The parameter is gone; both
   now name [sh_echo_input].

   (M2) [UProofShLib.wp_sh_wait] was VACUOUS: it proved
   [wp_sh_pureret_body ShSyms.wait SYS_wait], whose premise
   [xv6_io_sem SYS_wait = IoPureRet] is FALSE ([xv6_io_sem_wait] says
   [IoWaitNull]), so [main] -- its only caller -- had no usable contract
   for [wait] at all.  It is replaced by [UProofShLib.wp_sh_wait0], whose
   extra premise [uint a0 = 0] main discharges with `c.li a0,0' at 0x932. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import RiscvModelBytes.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh USpecShParse UProofShLib UProofShIo UProofShInput.
Require Import UProofShTop.
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
(* §0 The pure shims: image survival, window bookkeeping, the input.      *)
(* ===================================================================== *)

(* [ShData.sh_data]'s keys stop at 0x2010 -- the .bss above it is ALLOC-only
   and carries no dumped byte.  [UCodeSh.sh_data_key_lt]'s 12288 is too
   coarse here: `freep' (0x2010), `base' (0x2088) and `buf.0' (0x2020) all
   sit below it, and they are exactly the windows [parsecmd] disturbs. *)
Lemma sh_data_key_lt' (k : Z) (b : bv 8) :
  ShData.sh_data !! k = Some b -> k < 0x2010.
Proof. intro Hk. exact (proj2 (ShData.sh_data_range k b Hk)). Qed.

(* the whole image survives any set of windows that misses [0, 0x2010) *)
Lemma sh_img_only_in (M M' : gmap Z (bv 8)) (ws : list (Z * Z)) :
  uM_only_in M M' ws ->
  (forall k : Z, k < 0x2010 -> ~ uM_in_windows ws k) ->
  sh_img_sub M -> sh_img_sub M'.
Proof.
  intros Honly Hdisj [Ht Hd]. split.
  - refine (uM_only_in_img ShInstrs.sh_bytes M M' ws 0x2010 _ Hdisj Honly Ht).
    intros k b Hk. pose proof (sh_bytes_key_lt k b Hk) as Hlt. lia.
  - exact (uM_only_in_img ShData.sh_data M M' ws 0x2010
             sh_data_key_lt' Hdisj Honly Hd).
Qed.

(* ... and the one-store version a prologue needs *)
Lemma sh_img_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_img_sub M -> 0x2010 <= a -> sh_img_sub (uM_store8 M a v).
Proof.
  intros [Ht Hd] Ha. split.
  - intros k b Hk. rewrite (uM_store8_lookup_ne M a v k).
    + exact (Ht k b Hk).
    + intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
      pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
  - intros k b Hk. rewrite (uM_store8_lookup_ne M a v k).
    + exact (Hd k b Hk).
    + intros j Hj. pose proof (sh_data_key_lt' k b Hk) as Hlt.
      pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

Lemma sh_zeroed_store8 (M : gmap Z (bv 8)) (a lo hi b : Z) (v : mword 64) :
  sh_zeroed M a lo hi -> a + hi <= b ->
  sh_zeroed (uM_store8 M b v) a lo hi.
Proof.
  intros Hz Hb j Hj. rewrite (uM_store8_lookup_ne M b v (a + j)).
  - exact (Hz j Hj).
  - intros i Hi. lia.
Qed.

Lemma sh_zeroed_only_in (M M' : gmap Z (bv 8)) (ws : list (Z * Z))
    (a lo hi : Z) :
  uM_only_in M M' ws ->
  (forall k : Z, a + lo <= k < a + hi -> ~ uM_in_windows ws k) ->
  sh_zeroed M a lo hi -> sh_zeroed M' a lo hi.
Proof.
  intros [_ E] Hdisj Hz j Hj.
  rewrite (E (a + j) (Hdisj (a + j) ltac:(lia))). exact (Hz j Hj).
Qed.

Lemma ustr_at_only_in (M M' : gmap Z (bv 8)) (ws : list (Z * Z))
    (a : Z) (bs : list (bv 8)) :
  uM_only_in M M' ws ->
  (forall k : Z, a <= k <= a + Z.of_nat (length bs) -> ~ uM_in_windows ws k) ->
  ustr_at M a bs -> ustr_at M' a bs.
Proof.
  intros [_ E] Hdisj [Hb Hn]. split.
  - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj) as Hlt.
    rewrite (E (a + Z.of_nat j) (Hdisj (a + Z.of_nat j) ltac:(lia))).
    exact (Hb j b Hj).
  - rewrite (E (a + Z.of_nat (length bs))
               (Hdisj (a + Z.of_nat (length bs)) ltac:(lia))).
    exact Hn.
Qed.

(* the eliminator, as a tactic: a key is outside a CONCRETE window list.
   Doing this by hand is an [elem_of_cons] chase at every site. *)
Ltac sh_notin :=
  let w := fresh "w" in
  let Hw := fresh "Hw" in
  let Hin := fresh "Hin" in
  intros [w [Hw Hin]];
  apply elem_of_list_In in Hw; cbn [In] in Hw;
  cbv [sh_win] in Hw, Hin;
  destruct_or! Hw; try contradiction; subst w;
  cbn [fst snd] in Hin; lia.

(* ===================================================================== *)
(* §1 The concrete input, as [gets] and [getcmd] describe it.             *)
(* ===================================================================== *)

Lemma sh_echo_gets_taken : sh_gets_taken sh_echo_input [].
Proof.
  left. exists (sh_bytes [101; 99; 104; 111; 32; 72; 101; 108; 108; 111; 32;
                          119; 111; 114; 108; 100; 33]).
  split; [ vm_compute; reflexivity | ].
  intros j b Hj.
  repeat (destruct j as [|j];
          [ vm_compute in Hj; injection Hj as <-;
            split; vm_compute; discriminate | ]).
  vm_compute in Hj. discriminate.
Qed.

Lemma sh_echo_head (b : bv 8) : sh_echo_input !! 0%nat = Some b -> b <> ubyte0.
Proof. exact (sh_echo_no_nul 0%nat b). Qed.

Lemma sh_echo_nonnil : sh_echo_input <> [].
Proof. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(* §2 The "console" literal, read off the dumped data image.              *)
(*                                                                        *)
(* The two static lexer tables are the same kind of fact and are derived   *)
(* once in UProofShInput.sh_img_tables -- used here rather than restated.  *)
(* ===================================================================== *)

(* main's `open("console", O_RDWR)': the literal is at 0x1378 in .rodata,
   which shares text page 1 -- so the LOAD leaf comes off [sh_text_layout]
   and the bytes off [sh_data_sub]. *)
Definition SH_CONSOLE : Z := 0x1378.

Lemma sh_console_arg (pt : uptd) (M : gmap Z (bv 8)) :
  sh_text_layout pt -> sh_data_sub M -> uio_str_arg pt M SH_CONSOLE.
Proof.
  intros Hl Hd.
  assert (Hget : forall (k : Z) (b : bv 8),
            ShData.sh_data !! k = Some b -> M !! k = Some b) by exact Hd.
  exists 7. split.
  - constructor.
    + lia.
    + intros j Hj.
      assert (Hj7 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6)
        by lia.
      destruct_or! Hj7; subst j;
        [ exists (Z_to_bv 8 0x63) | exists (Z_to_bv 8 0x6f)
        | exists (Z_to_bv 8 0x6e) | exists (Z_to_bv 8 0x73)
        | exists (Z_to_bv 8 0x6f) | exists (Z_to_bv 8 0x6c)
        | exists (Z_to_bv 8 0x65) ];
        (split; [ apply Hget; vm_compute; reflexivity
                | vm_compute; discriminate ]).
    + apply Hget. vm_compute. reflexivity.
  - constructor.
    + unfold SH_CONSOLE. lia.
    + lia.
    + unfold SH_CONSOLE. change (2 ^ 38) with 274877906944. lia.
    + intros j Hj.
      exact (sh_text_layout_load pt (SH_CONSOLE + j) Hl
               ltac:(unfold SH_CONSOLE; lia)).
    + intros j Hj.
      assert (Hj8 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
                    j = 6 \/ j = 7) by lia.
      destruct_or! Hj8; subst j;
        [ exists (Z_to_bv 8 0x63) | exists (Z_to_bv 8 0x6f)
        | exists (Z_to_bv 8 0x6e) | exists (Z_to_bv 8 0x73)
        | exists (Z_to_bv 8 0x6f) | exists (Z_to_bv 8 0x6c)
        | exists (Z_to_bv 8 0x65) | exists (Z_to_bv 8 0x0) ];
        (apply Hget; vm_compute; reflexivity).
Qed.

(* The .bss window is READABLE: [sh_layout]'s data page permits Load Data,
   and the bytes are present because the same window is writable.  main's
   contract carries only [uv_wr]; [getcmd] and the `lbu a5,0(s2)' at 0x944
   both need the load side. *)
Lemma sh_bss_rd (pt : uptd) (M : gmap Z (bv 8)) (hbase hlen a n : Z) :
  sh_layout pt hbase hlen ->
  uv_wr pt M (SH_DATA_PG + 0x10) 0x88 ->
  SH_DATA_PG + 0x10 <= a -> 0 <= n -> a + n <= SH_DATA_PG + 0x98 ->
  uv_rd pt M a n.
Proof.
  intros Hlay Hwr Ha Hn Hhi.
  destruct (shl_data pt hbase hlen Hlay) as (w & Hw & Hld & _).
  unfold SH_DATA_PG in *.
  constructor.
  - lia.
  - lia.
  - change (2 ^ 38) with 274877906944. lia.
  - intros j Hj. exists w. split; [ | exact Hld ].
    rewrite (sh_svpn_page (a + j) ltac:(change (2 ^ 38) with 274877906944; lia)).
    replace ((a + j) / 4096) with 2
      by (apply (Z.div_unique_pos (a + j) 4096 2 (a + j - 8192)); lia).
    change (4096 * 2) with 8192. exact Hw.
  - intros j Hj.
    replace (a + j) with (0x2000 + 0x10 + (a + j - (0x2000 + 0x10))) by lia.
    apply (uwr_bytes _ _ _ _ Hwr (a + j - (0x2000 + 0x10))). lia.
Qed.

(* one 8-byte frame store, carrying the three facts a prologue threads:
   the image's domain only grows, nothing outside the frame moves, and the
   dumped image survives (the frame is far above 0x2010). *)
Lemma sh_pro_step (M Mx : gmap Z (bv 8)) (lo hi a : Z) (v : mword 64) :
  0x2010 <= lo -> lo <= a -> a + 8 <= hi ->
  (forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k)) ->
  (forall k : Z, k < lo \/ hi <= k -> Mx !! k = M !! k) ->
  sh_img_sub Mx ->
  (forall k : Z, is_Some (M !! k) -> is_Some (uM_store8 Mx a v !! k)) /\
  (forall k : Z, k < lo \/ hi <= k -> uM_store8 Mx a v !! k = M !! k) /\
  sh_img_sub (uM_store8 Mx a v).
Proof.
  intros Hlo Ha1 Ha2 Hdom Hne Himg. split_and!.
  - intros k Hk. apply uM_store8_is_Some. exact (Hdom k Hk).
  - intros k Hk. rewrite (uM_store8_lookup_ne Mx a v k ltac:(intros j Hj; lia)).
    exact (Hne k Hk).
  - apply sh_img_store8; [ exact Himg | lia ].
Qed.

Section UProofShMain.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).
  Local Notation UVG m M := (uv_cap_gpr C pt Psh M m).

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

  (* ------------------------------------------------------------------- *)
  (* THE ONE CALLEE THIS FILE CANNOT [Require] YET.                        *)
  (*                                                                       *)
  (* [fork1] and [runcmd] have landed (UProofShTop.v) and are used          *)
  (* directly.  [parsecmd] (UProofShCmd.v) is still in flight, so it is a   *)
  (* section HYPOTHESIS: closing the section makes it an ARGUMENT of        *)
  (* [wp_sh_main] / [wp_sh_start], visible in the type and impossible to    *)
  (* land unnoticed -- unlike an [Admitted].                                *)
  (* ------------------------------------------------------------------- *)
  Hypothesis Hparsecmd : forall (CIDp : CpuId) (M : gmap Z (bv 8))
      (m : regfile) (sp0 : mword 64) (s0 : Z) (bs : list (bv 8))
      (toks : list (nat * nat)),
    wp_sh_parsecmd_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 s0 bs toks.



  (* ------------------------------------------------------------------- *)
  (* main() @0x8e2.  DIVERGES: the child leaves through [runcmd]'s [exec]  *)
  (* and the parent through [exit(0)] after the EOF iteration.            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_main (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_sh_main_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0.
  Proof.
    intros Hlay Himg Hsp Hst Hbss Hbssw Htab Hstkhi Hstk.
    change (64 + (64 + 48 + 48 + 128 + 112 + 64 + 16)) with 544 in Hst, Hstkhi.
    destruct sh_syms_pins
      as (_ & Hsmain & Hsgetcmd & _ & Hsruncmd & Hsfork1 & _ & Hsparsecmd &
          _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          Hsopen & Hsclose & _ & Hswait & _ & Hsexit & _).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (sh_img_data M Himg) as Hdata.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan, Hhhi, Hstk.
    (* the frame sits far above the image and the heap *)
    assert (Hsphi : 77824 <= uint sp0 - 544) by lia.
    (* main's own frame, and the 480 bytes its callees get *)
    assert (Hst64 : uv_stack pt M sp0 64)
      by exact (proj1 (uv_stack_split pt M sp0 544 64 480 ltac:(lia) ltac:(lia)
                         ltac:(vm_compute; reflexivity) ltac:(lia) Hst)).
    assert (Hst480 : uv_stack pt M (mword_of_int (uint sp0 - 64)) 480).
    { pose proof (proj2 (uv_stack_split pt M sp0 544 64 480 ltac:(lia)
                           ltac:(lia) ltac:(vm_compute; reflexivity)
                           ltac:(lia) Hst)) as HS.
      rewrite (uv_stack_sp_moi pt M sp0 64 Hst64) in HS. exact HS. }
    assert (Husp : uint (mword_of_int (uint sp0 - 64) : mword 64)
                   = uint sp0 - 64) by (apply uint_moi; unfold Z64; lia).
    (* the eight frame slots, as absolute addresses *)
    assert (E64_56 : uint sp0 - 64 + 56 = uint sp0 - 8) by lia.
    assert (E64_48 : uint sp0 - 64 + 48 = uint sp0 - 16) by lia.
    assert (E64_40 : uint sp0 - 64 + 40 = uint sp0 - 24) by lia.
    assert (E64_32 : uint sp0 - 64 + 32 = uint sp0 - 32) by lia.
    assert (E64_24 : uint sp0 - 64 + 24 = uint sp0 - 40) by lia.
    assert (E64_16 : uint sp0 - 64 + 16 = uint sp0 - 48) by lia.
    assert (E64_8  : uint sp0 - 64 + 8  = uint sp0 - 56) by lia.
    assert (E64_0  : uint sp0 - 64 + 0  = uint sp0 - 64) by lia.
    (* the pc ticks of the prologue *)
    assert (E8e2 : add_vec_int (mword_of_int 0x8e2 : mword 64) 2 = mword_of_int 0x8e4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8e4 : add_vec_int (mword_of_int 0x8e4 : mword 64) 2 = mword_of_int 0x8e6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8e6 : add_vec_int (mword_of_int 0x8e6 : mword 64) 2 = mword_of_int 0x8e8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8e8 : add_vec_int (mword_of_int 0x8e8 : mword 64) 2 = mword_of_int 0x8ea)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8ea : add_vec_int (mword_of_int 0x8ea : mword 64) 2 = mword_of_int 0x8ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8ec : add_vec_int (mword_of_int 0x8ec : mword 64) 2 = mword_of_int 0x8ee)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8ee : add_vec_int (mword_of_int 0x8ee : mword 64) 2 = mword_of_int 0x8f0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8f0 : add_vec_int (mword_of_int 0x8f0 : mword 64) 2 = mword_of_int 0x8f2)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8f2 : add_vec_int (mword_of_int 0x8f2 : mword 64) 2 = mword_of_int 0x8f4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8f4 : add_vec_int (mword_of_int 0x8f4 : mword 64) 2 = mword_of_int 0x8f6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8f6 : add_vec_int (mword_of_int 0x8f6 : mword 64) 2 = mword_of_int 0x8f8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8f8 : add_vec_int (mword_of_int 0x8f8 : mword 64) 4 = mword_of_int 0x8fc)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E8fc : add_vec_int (mword_of_int 0x8fc : mword 64) 4 = mword_of_int 0x900)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E900 : add_vec_int (mword_of_int 0x900 : mword 64) 2 = mword_of_int 0x902)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E902 : add_vec_int (mword_of_int 0x902 : mword 64) 2 = mword_of_int 0x904)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hdom0 : forall k : Z, is_Some (M !! k) -> is_Some (M !! k))
      by (intros k Hk; exact Hk).
    assert (Hne0 : forall k : Z, k < uint sp0 - 64 \/ uint sp0 <= k ->
                     M !! k = M !! k) by (intros k _; reflexivity).
    assert (Himg0 : sh_img_sub M) by exact Himg.
    iIntros "Hcg Hin Hbrk HQ Hpc".
    iEval (rewrite Hsmain) in "Hpc".
    (* ---- 0x8e2  c.addi16sp sp,sp,-64 ---- *)
    assert (Hwsp : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { assert (Hs : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
      rewrite Hs.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x8e2)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_sh_8e2 pt M Hl Htext) Hwsp
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    iEval (rewrite E8e2) in "Hpc".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64))).
    assert (Hpre1 : forall r : mword 5, Regidx r <> Regidx sp_idx ->
              m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx sp_idx) (Regidx r) _ Hr)).
    (* ---- 0x8e4  c.sdsp ra,56(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID1 Psh M m1 sp0 (mword_of_int 0x8e4)
              (mword_of_int 7 : mword 6) ra_idx 64 56
              (ui_sh_8e4 pt M Hl (sh_img_text M Himg0))
              ltac:(exact (uv_stack_dom pt M M sp0 64 Hdom0 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite E64_56 (Hpre1 ra_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8e4) in "Hpc".
    set (MA1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    destruct (sh_pro_step M M (uint sp0 - 64) (uint sp0) (uint sp0 - 8)
                (m !!! Regidx ra_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom0 Hne0 Himg0) as (Hdom1 & Hne1 & Himg1).
    (* ---- 0x8e6  c.sdsp s0,48(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID2 Psh MA1 m1 sp0 (mword_of_int 0x8e6)
              (mword_of_int 6 : mword 6) s0_idx 64 48
              (ui_sh_8e6 pt MA1 Hl (sh_img_text MA1 Himg1))
              ltac:(exact (uv_stack_dom pt M MA1 sp0 64 Hdom1 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iEval (rewrite E64_48 (Hpre1 s0_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8e6) in "Hpc".
    set (MA2 := uM_store8 MA1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    destruct (sh_pro_step M MA1 (uint sp0 - 64) (uint sp0) (uint sp0 - 16)
                (m !!! Regidx s0_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom1 Hne1 Himg1) as (Hdom2 & Hne2 & Himg2).
    (* ---- 0x8e8  c.sdsp s1,40(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID3 Psh MA2 m1 sp0 (mword_of_int 0x8e8)
              (mword_of_int 5 : mword 6) s1_idx 64 40
              (ui_sh_8e8 pt MA2 Hl (sh_img_text MA2 Himg2))
              ltac:(exact (uv_stack_dom pt M MA2 sp0 64 Hdom2 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    iEval (rewrite E64_40 (Hpre1 s1_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8e8) in "Hpc".
    set (MA3 := uM_store8 MA2 (uint sp0 - 24) (m !!! Regidx s1_idx)).
    destruct (sh_pro_step M MA2 (uint sp0 - 64) (uint sp0) (uint sp0 - 24)
                (m !!! Regidx s1_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom2 Hne2 Himg2) as (Hdom3 & Hne3 & Himg3).
    (* ---- 0x8ea  c.sdsp s2,32(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID4 Psh MA3 m1 sp0 (mword_of_int 0x8ea)
              (mword_of_int 4 : mword 6) s2_idx 64 32
              (ui_sh_8ea pt MA3 Hl (sh_img_text MA3 Himg3))
              ltac:(exact (uv_stack_dom pt M MA3 sp0 64 Hdom3 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    iEval (rewrite E64_32 (Hpre1 s2_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8ea) in "Hpc".
    set (MA4 := uM_store8 MA3 (uint sp0 - 32) (m !!! Regidx s2_idx)).
    destruct (sh_pro_step M MA3 (uint sp0 - 64) (uint sp0) (uint sp0 - 32)
                (m !!! Regidx s2_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom3 Hne3 Himg3) as (Hdom4 & Hne4 & Himg4).
    (* ---- 0x8ec  c.sdsp s3,24(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID5 Psh MA4 m1 sp0 (mword_of_int 0x8ec)
              (mword_of_int 3 : mword 6) s3_idx 64 24
              (ui_sh_8ec pt MA4 Hl (sh_img_text MA4 Himg4))
              ltac:(exact (uv_stack_dom pt M MA4 sp0 64 Hdom4 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    iEval (rewrite E64_24 (Hpre1 s3_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8ec) in "Hpc".
    set (MA5 := uM_store8 MA4 (uint sp0 - 40) (m !!! Regidx s3_idx)).
    destruct (sh_pro_step M MA4 (uint sp0 - 64) (uint sp0) (uint sp0 - 40)
                (m !!! Regidx s3_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom4 Hne4 Himg4) as (Hdom5 & Hne5 & Himg5).
    (* ---- 0x8ee  c.sdsp s4,16(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID6 Psh MA5 m1 sp0 (mword_of_int 0x8ee)
              (mword_of_int 2 : mword 6) s4_idx 64 16
              (ui_sh_8ee pt MA5 Hl (sh_img_text MA5 Himg5))
              ltac:(exact (uv_stack_dom pt M MA5 sp0 64 Hdom5 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID7) "Hcg Hpc".
    iEval (rewrite E64_16 (Hpre1 s4_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8ee) in "Hpc".
    set (MA6 := uM_store8 MA5 (uint sp0 - 48) (m !!! Regidx s4_idx)).
    destruct (sh_pro_step M MA5 (uint sp0 - 64) (uint sp0) (uint sp0 - 48)
                (m !!! Regidx s4_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom5 Hne5 Himg5) as (Hdom6 & Hne6 & Himg6).
    (* ---- 0x8f0  c.sdsp s5,8(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID7 Psh MA6 m1 sp0 (mword_of_int 0x8f0)
              (mword_of_int 1 : mword 6) s5_idx 64 8
              (ui_sh_8f0 pt MA6 Hl (sh_img_text MA6 Himg6))
              ltac:(exact (uv_stack_dom pt M MA6 sp0 64 Hdom6 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID8) "Hcg Hpc".
    iEval (rewrite E64_8 (Hpre1 s5_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8f0) in "Hpc".
    set (MA7 := uM_store8 MA6 (uint sp0 - 56) (m !!! Regidx s5_idx)).
    destruct (sh_pro_step M MA6 (uint sp0 - 64) (uint sp0) (uint sp0 - 56)
                (m !!! Regidx s5_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom6 Hne6 Himg6) as (Hdom7 & Hne7 & Himg7).
    (* ---- 0x8f2  c.sdsp s6,0(sp) ---- *)
    iApply (wp_uv_frame_store C pt CID8 Psh MA7 m1 sp0 (mword_of_int 0x8f2)
              (mword_of_int 0 : mword 6) s6_idx 64 0
              (ui_sh_8f2 pt MA7 Hl (sh_img_text MA7 Himg7))
              ltac:(exact (uv_stack_dom pt M MA7 sp0 64 Hdom7 Hst64))
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID9) "Hcg Hpc".
    iEval (rewrite E64_0 (Hpre1 s6_idx ltac:(vm_compute; discriminate))) in "Hcg".
    iEval (rewrite E8f2) in "Hpc".
    set (MA8 := uM_store8 MA7 (uint sp0 - 64) (m !!! Regidx s6_idx)).
    destruct (sh_pro_step M MA7 (uint sp0 - 64) (uint sp0) (uint sp0 - 64)
                (m !!! Regidx s6_idx) ltac:(lia) ltac:(lia) ltac:(lia)
                Hdom7 Hne7 Himg7) as (Hdom8 & Hne8 & Himg8).
    (* the whole prologue's effect, as the rest of main sees it *)
    assert (Hstk8 : uv_stack pt MA8 (mword_of_int (uint sp0 - 64)) 480)
      by exact (uv_stack_dom pt M MA8 _ 480 Hdom8 Hst480).
    assert (Hbss8 : sh_zeroed MA8 (SH_DATA_PG + 0x10) 0 0x88).
    { intros j Hj. rewrite (Hne8 (SH_DATA_PG + 0x10 + j) ltac:(unfold SH_DATA_PG; lia)).
      exact (Hbss j Hj). }
    assert (Hbssw8 : uv_wr pt MA8 (SH_DATA_PG + 0x10) 0x88)
      by exact (uv_wr_dom pt M MA8 _ _ Hdom8 Hbssw).
    assert (Htext8 : sh_text_sub MA8) by exact (sh_img_text MA8 Himg8).
    assert (Hdata8 : sh_data_sub MA8) by exact (sh_img_data MA8 Himg8).
    (* ---- 0x8f4  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_uv_caddi4spn C pt Psh MA8 m1 (mword_of_int 0x8f4)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_8f4 pt MA8 Hl Htext8)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1;
                    assert (Hc : (sign_extend' 64
                                    (caddi4spn_imm (mword_of_int 16 : mword 8))
                                  : mword 64) = mword_of_int 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Hc moi_add; f_equal; lia)
              with "Hcg Hpc").
    iIntros (CID10) "Hcg Hpc".
    iEval (rewrite E8f4) in "Hpc".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> m1).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
              m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    (* ---- 0x8f6  c.li s1,2 ---- *)
    iApply (wp_uv_cli C pt Psh MA8 m2 (mword_of_int 0x8f6)
              (mword_of_int 2 : mword 6) s1_idx (mword_of_int 2 : mword 64)
              (ui_sh_8f6 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID11) "Hcg Hpc".
    iEval (rewrite E8f6) in "Hpc".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_3 : m3 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by exact (upd_eq m2 (Regidx s1_idx) _).
    assert (Hsp3 : m3 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp2).
    (* ---- 0x8f8  auipc s2,0x1 ---- *)
    iApply (wp_uv_auipc C pt Psh MA8 m3 (mword_of_int 0x8f8)
              (mword_of_int 1 : mword 20) s2_idx (mword_of_int 0x18f8)
              (ui_sh_8f8 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID12) "Hcg Hpc".
    iEval (rewrite E8f8) in "Hpc".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int 0x18f8 : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs2_4 : m4 !!! Regidx s2_idx = (mword_of_int 0x18f8 : mword 64))
      by exact (upd_eq m3 (Regidx s2_idx) _).
    assert (Hsp4 : m4 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp3).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    (* ---- 0x8fc  addi s2,s2,-1408   (-> 0x1378, "console") ---- *)
    iApply (wp_uv_addi C pt Psh MA8 m4 (mword_of_int 0x8fc)
              (mword_of_int 2688 : mword 12) s2_idx s2_idx
              (mword_of_int SH_CONSOLE)
              (ui_sh_8fc pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_4; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID13) "Hcg Hpc".
    iEval (rewrite E8fc) in "Hpc".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int SH_CONSOLE : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs2_5 : m5 !!! Regidx s2_idx
                    = (mword_of_int SH_CONSOLE : mword 64))
      by exact (upd_eq m4 (Regidx s2_idx) _).
    assert (Hsp5 : m5 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp4).
    assert (Hs1_5 : m5 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm5 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_4).
    (* ---- 0x900  c.mv a1,s1 ---- *)
    iApply (wp_uv_cmv C pt Psh MA8 m5 (mword_of_int 0x900)
              a1_idx s1_idx (mword_of_int 2)
              (ui_sh_900 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_5 moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (CID14) "Hcg Hpc".
    iEval (rewrite E900) in "Hpc".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs2_6 : m6 !!! Regidx s2_idx
                    = (mword_of_int SH_CONSOLE : mword 64))
      by (rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_5).
    assert (Hsp6 : m6 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp5).
    assert (Hs1_6 : m6 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm6 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_5).
    (* ---- 0x902  c.mv a0,s2 ---- *)
    iApply (wp_uv_cmv C pt Psh MA8 m6 (mword_of_int 0x902)
              a0_idx s2_idx (mword_of_int SH_CONSOLE)
              (ui_sh_902 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_6 moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (CID15) "Hcg Hpc".
    iEval (rewrite E902) in "Hpc".
    set (m7 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int SH_CONSOLE : mword 64)]> m6).
    assert (Hm7 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hsp7 : m7 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp6).
    assert (Hs1_7 : m7 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_6).
    assert (Ha0_7 : m7 !!! Regidx a0_idx
                    = (mword_of_int SH_CONSOLE : mword 64))
      by exact (upd_eq m6 (Regidx a0_idx) _).
    (* ---- 0x904  jal ra,0xcc6 <open> ---- *)
    iApply (wp_uv_jal C pt Psh MA8 m7 (mword_of_int 0x904)
              (mword_of_int 962 : mword 21) ra_idx
              (mword_of_int 0xcc6) (mword_of_int 0x908)
              (ui_sh_904 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID16) "Hcg Hpc".
    iEval (rewrite <- Hsopen) in "Hpc".
    set (m8 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x908 : mword 64)]> m7).
    assert (Hm8 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra8 : m8 !!! Regidx ra_idx = (mword_of_int 0x908 : mword 64))
      by exact (upd_eq m7 (Regidx ra_idx) _).
    assert (Hsp8 : m8 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp7).
    assert (Hs1_8 : m8 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_7).
    assert (Ha0_8 : m8 !!! Regidx a0_idx
                    = (mword_of_int SH_CONSOLE : mword 64))
      by (rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_7).
    (* ---- the call: open("console", O_RDWR) ---- *)
    assert (Hucons : uint (mword_of_int SH_CONSOLE : mword 64) = SH_CONSOLE)
      by (apply uint_moi; unfold Z64, SH_CONSOLE; lia).
    iApply (wp_sh_open C pt gin gbrk hbase hlen Q CID16 MA8 m8
              ltac:(split_and!;
                    [ exact Hlay | exact Htext8
                    | rewrite Hra8; vm_compute; reflexivity ])
              ltac:(rewrite Ha0_8 Hucons; exact (sh_console_arg pt MA8 Hl Hdata8))
              with "Hcg Hpc").
    iIntros (CID17 fd) "%Hfd3 Hcg Hpc".
    iEval (rewrite Hra8) in "Hpc".
    set (m9 := <[Regidx a0_idx := fd]>
                 (<[Regidx a7_idx := (mword_of_int SYS_open : mword 64)]> m8)).
    assert (Ha0_9 : m9 !!! Regidx a0_idx = fd)
      by exact (upd_eq _ (Regidx a0_idx) _).
    assert (Hm9 : forall r : mword 5,
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a7_idx ->
              m9 !!! Regidx r = m8 !!! Regidx r).
    { intros r Hr Hr'.
      exact (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hr)
               (upd_ne m8 (Regidx a7_idx) (Regidx r) _ Hr')). }
    assert (Hsp9 : m9 !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp8).
    assert (Hs1_9 : m9 !!! Regidx s1_idx = (mword_of_int 2 : mword 64))
      by (rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs1_8).
    (* ---- 0x908  bltz a0,0x914   (NOT taken: open returned fd >= 3) ---- *)
    assert (Hz0s : sint (zero_reg : mword 64) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_uv_btype0 C pt Psh MA8 m9 (mword_of_int 0x908)
              (mword_of_int 12 : mword 13) a0_idx BLT
              false (mword_of_int 0x914)
              (ui_sh_908 pt MA8 Hl Htext8)
              ltac:(cbn [uv_btaken]; rewrite Ha0_9; unfold zopz0zI_s;
                    rewrite Hz0s; symmetry; apply Z.ltb_ge; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID18) "Hcg Hpc".
    assert (E908 : (if false then (mword_of_int 0x914 : mword 64)
                    else add_vec_int (mword_of_int 0x908 : mword 64) 4)
                   = mword_of_int 0x90c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E908) in "Hpc".
    (* ---- 0x90c  bge s1,a0,0x900   (NOT taken: 2 < fd) ---- *)
    iApply (wp_uv_btype C pt Psh MA8 m9 (mword_of_int 0x90c)
              (mword_of_int 8180 : mword 13) a0_idx s1_idx BGE
              false (mword_of_int 0x900)
              (ui_sh_90c pt MA8 Hl Htext8)
              ltac:(cbn [uv_btaken]; rewrite Hs1_9 Ha0_9;
                    unfold zopz0zKzJ_s;
                    assert (Hs2v : sint (mword_of_int 2 : mword 64) = 2)
                      by (vm_compute; reflexivity);
                    rewrite Hs2v Z.geb_leb; symmetry; apply Z.leb_gt; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID19) "Hcg Hpc".
    assert (E90c : (if false then (mword_of_int 0x900 : mword 64)
                    else add_vec_int (mword_of_int 0x90c : mword 64) 4)
                   = mword_of_int 0x910)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E90c) in "Hpc".
    (* ---- 0x910  jal ra,0xcae <close> ---- *)
    iApply (wp_uv_jal C pt Psh MA8 m9 (mword_of_int 0x910)
              (mword_of_int 926 : mword 21) ra_idx
              (mword_of_int 0xcae) (mword_of_int 0x914)
              (ui_sh_910 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID20) "Hcg Hpc".
    iEval (rewrite <- Hsclose) in "Hpc".
    set (m10 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x914 : mword 64)]> m9).
    assert (Hm10 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              m10 !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra10 : m10 !!! Regidx ra_idx = (mword_of_int 0x914 : mword 64))
      by exact (upd_eq m9 (Regidx ra_idx) _).
    assert (Hsp10 : m10 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm10 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp9).
    (* ---- the call: close(fd) ---- *)
    iApply (wp_sh_close C pt gin gbrk hbase hlen Q CID20 MA8 m10
              ltac:(split_and!;
                    [ exact Hlay | exact Htext8
                    | rewrite Hra10; vm_compute; reflexivity ])
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID21 rc) "Hcg Hpc".
    iEval (rewrite Hra10) in "Hpc".
    set (m11 := <[Regidx a0_idx := rc]>
                  (<[Regidx a7_idx := (mword_of_int SYS_close : mword 64)]> m10)).
    assert (Hm11 : forall r : mword 5,
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a7_idx ->
              m11 !!! Regidx r = m10 !!! Regidx r).
    { intros r Hr Hr'.
      exact (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hr)
               (upd_ne m10 (Regidx a7_idx) (Regidx r) _ Hr')). }
    assert (Hsp11 : m11 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm11 csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp10).

    (* --- the pc ticks of the setup block and the REPL --- *)
    assert (E914 : add_vec_int (mword_of_int 0x914 : mword 64) 4 = mword_of_int 0x918)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E918 : add_vec_int (mword_of_int 0x918 : mword 64) 4 = mword_of_int 0x91c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E91c : add_vec_int (mword_of_int 0x91c : mword 64) 4 = mword_of_int 0x920)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E920 : add_vec_int (mword_of_int 0x920 : mword 64) 2 = mword_of_int 0x922)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E922 : add_vec_int (mword_of_int 0x922 : mword 64) 4 = mword_of_int 0x926)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E926 : add_vec_int (mword_of_int 0x926 : mword 64) 4 = mword_of_int 0x92a)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E938 : add_vec_int (mword_of_int 0x938 : mword 64) 2 = mword_of_int 0x93a)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E93a : add_vec_int (mword_of_int 0x93a : mword 64) 2 = mword_of_int 0x93c)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x914  li s3,100 ---- *)
    iApply (wp_uv_li C pt Psh MA8 m11 (mword_of_int 0x914)
              (mword_of_int 100 : mword 12) s3_idx (mword_of_int 100)
              (ui_sh_914 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID22) "Hcg Hpc".
    iEval (rewrite E914) in "Hpc".
    set (m12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int 100 : mword 64)]> m11).
    assert (Hm12 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
              m12 !!! Regidx r = m11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m11 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hs3_12 : m12 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by exact (upd_eq m11 (Regidx s3_idx) _).
    assert (Hsp12 : m12 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm12 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp11).
    (* ---- 0x918  auipc s2,0x1 ---- *)
    iApply (wp_uv_auipc C pt Psh MA8 m12 (mword_of_int 0x918)
              (mword_of_int 1 : mword 20) s2_idx (mword_of_int 0x1918)
              (ui_sh_918 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID23) "Hcg Hpc".
    iEval (rewrite E918) in "Hpc".
    set (m13 := <[Regidx s2_idx
                  := regval_into_reg (mword_of_int 0x1918 : mword 64)]> m12).
    assert (Hm13 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m13 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs2_13 : m13 !!! Regidx s2_idx = (mword_of_int 0x1918 : mword 64))
      by exact (upd_eq m12 (Regidx s2_idx) _).
    assert (Hs3_13 : m13 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_12).
    assert (Hsp13 : m13 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp12).
    (* ---- 0x91c  addi s2,s2,1800   (-> 0x2020, buf.0) ---- *)
    iApply (wp_uv_addi C pt Psh MA8 m13 (mword_of_int 0x91c)
              (mword_of_int 1800 : mword 12) s2_idx s2_idx
              (mword_of_int SH_BUF)
              (ui_sh_91c pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_13; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID24) "Hcg Hpc".
    iEval (rewrite E91c) in "Hpc".
    set (m14 := <[Regidx s2_idx
                  := regval_into_reg (mword_of_int SH_BUF : mword 64)]> m13).
    assert (Hm14 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
              m14 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs2_14 : m14 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by exact (upd_eq m13 (Regidx s2_idx) _).
    assert (Hs3_14 : m14 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm14 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_13).
    assert (Hsp14 : m14 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm14 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp13).
    (* ---- 0x920  c.li s4,10 ---- *)
    iApply (wp_uv_cli C pt Psh MA8 m14 (mword_of_int 0x920)
              (mword_of_int 10 : mword 6) s4_idx (mword_of_int 10 : mword 64)
              (ui_sh_920 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID25) "Hcg Hpc".
    iEval (rewrite E920) in "Hpc".
    set (m15 := <[Regidx s4_idx
                  := regval_into_reg (mword_of_int 10 : mword 64)]> m14).
    assert (Hm15 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
              m15 !!! Regidx r = m14 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m14 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hs4_15 : m15 !!! Regidx s4_idx = (mword_of_int 10 : mword 64))
      by exact (upd_eq m14 (Regidx s4_idx) _).
    assert (Hs2_15 : m15 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (Hm15 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_14).
    assert (Hs3_15 : m15 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm15 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_14).
    assert (Hsp15 : m15 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm15 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp14).
    (* ---- 0x922  li s5,99 ---- *)
    iApply (wp_uv_li C pt Psh MA8 m15 (mword_of_int 0x922)
              (mword_of_int 99 : mword 12) s5_idx (mword_of_int 99)
              (ui_sh_922 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID26) "Hcg Hpc".
    iEval (rewrite E922) in "Hpc".
    set (m16 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 99 : mword 64)]> m15).
    assert (Hm16 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
              m16 !!! Regidx r = m15 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m15 (Regidx s5_idx) (Regidx r) _ Hr)).
    assert (Hs5_16 : m16 !!! Regidx s5_idx = (mword_of_int 99 : mword 64))
      by exact (upd_eq m15 (Regidx s5_idx) _).
    assert (Hs4_16 : m16 !!! Regidx s4_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hm16 s4_idx ltac:(vm_compute; discriminate)); exact Hs4_15).
    assert (Hs2_16 : m16 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (Hm16 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_15).
    assert (Hs3_16 : m16 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm16 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_15).
    assert (Hsp16 : m16 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm16 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp15).
    (* ---- 0x926  li s6,32 ---- *)
    iApply (wp_uv_li C pt Psh MA8 m16 (mword_of_int 0x926)
              (mword_of_int 32 : mword 12) s6_idx (mword_of_int 32)
              (ui_sh_926 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID27) "Hcg Hpc".
    iEval (rewrite E926) in "Hpc".
    set (m17 := <[Regidx s6_idx
                  := regval_into_reg (mword_of_int 32 : mword 64)]> m16).
    assert (Hm17 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
              m17 !!! Regidx r = m16 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m16 (Regidx s6_idx) (Regidx r) _ Hr)).
    assert (Hs6_17 : m17 !!! Regidx s6_idx = (mword_of_int 32 : mword 64))
      by exact (upd_eq m16 (Regidx s6_idx) _).
    assert (Hs5_17 : m17 !!! Regidx s5_idx = (mword_of_int 99 : mword 64))
      by (rewrite (Hm17 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_16).
    assert (Hs4_17 : m17 !!! Regidx s4_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hm17 s4_idx ltac:(vm_compute; discriminate)); exact Hs4_16).
    assert (Hs2_17 : m17 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (Hm17 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_16).
    assert (Hs3_17 : m17 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm17 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_16).
    assert (Hsp17 : m17 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm17 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp16).
    (* ---- 0x92a  c.j 0x938  (into the REPL) ---- *)
    iApply (wp_uv_cj C pt Psh MA8 m17 (mword_of_int 0x92a)
              (mword_of_int 7 : mword 11) (mword_of_int 0x938)
              (ui_sh_92a pt MA8 Hl Htext8)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID28) "Hcg Hpc".

    (* ------------------------------------------------------------------ *)
    (* REPL ITERATION 1: getcmd(buf,100) reads `echo Hello world!\n'.       *)
    (* ------------------------------------------------------------------ *)
    assert (Hlen18 : Z.of_nat (length sh_echo_input) = 18)
      by (rewrite sh_echo_input_len; reflexivity).
    assert (Hbufv : SH_BUF = 8224) by (vm_compute; reflexivity).
    assert (Hdpg : SH_DATA_PG = 8192) by (vm_compute; reflexivity).
    assert (Hst128 : forall Mx : gmap Z (bv 8),
              (forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k)) ->
              uv_stack pt Mx (mword_of_int (uint sp0 - 64)) 128).
    { intros Mx Hd.
      exact (proj1 (uv_stack_split pt Mx (mword_of_int (uint sp0 - 64)) 480
                      128 352 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                      ltac:(lia) (uv_stack_dom pt M Mx _ 480 Hd Hst480))). }
    assert (Hst16 : forall Mx : gmap Z (bv 8),
              (forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k)) ->
              uv_stack pt Mx (mword_of_int (uint sp0 - 64)) 16).
    { intros Mx Hd.
      exact (proj1 (uv_stack_split pt Mx (mword_of_int (uint sp0 - 64)) 480
                      16 464 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                      ltac:(lia) (uv_stack_dom pt M Mx _ 480 Hd Hst480))). }
    assert (Hst48 : forall Mx : gmap Z (bv 8),
              (forall k : Z, is_Some (M !! k) -> is_Some (Mx !! k)) ->
              uv_stack pt Mx (mword_of_int (uint sp0 - 64)) 48).
    { intros Mx Hd.
      exact (proj1 (uv_stack_split pt Mx (mword_of_int (uint sp0 - 64)) 480
                      48 432 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                      ltac:(lia) (uv_stack_dom pt M Mx _ 480 Hd Hst480))). }
    assert (Hfr128 : sh_frame_ok hbase hlen (mword_of_int (uint sp0 - 64)) 128)
      by (unfold sh_frame_ok; rewrite Husp; lia).
    assert (Hdisjb : SH_BUF + 100 <= uint (mword_of_int (uint sp0 - 64) : mword 64) - 128
                     \/ uint (mword_of_int (uint sp0 - 64) : mword 64) <= SH_BUF)
      by (rewrite Husp; left; lia).
    assert (Hfit1 : Z.of_nat (length sh_echo_input) + 1 < 100 /\ 100 < 2 ^ 31)
      by (split; [ lia | change (2 ^ 31) with 2147483648; lia ]).
    assert (Hfit0 : Z.of_nat (length (@nil (bv 8))) + 1 < 100 /\ 100 < 2 ^ 31)
      by (split; [ cbn [length]; lia | change (2 ^ 31) with 2147483648; lia ]).
    assert (Hbufhi : 8192 <= SH_BUF) by lia.
    assert (Hnil0 : forall b : bv 8, (@nil (bv 8)) !! 0%nat = Some b ->
                      b <> ubyte0) by (intros b Hb; discriminate Hb).
    assert (Hwrbuf : forall Mx : gmap Z (bv 8),
              uv_wr pt Mx (SH_DATA_PG + 0x10) 0x88 -> uv_wr pt Mx SH_BUF 100).
    { intros Mx H.
      apply (uv_wr_sub pt Mx (SH_DATA_PG + 0x10) 0x88 SH_BUF 100 H); lia. }
    assert (Hrdbuf : forall Mx : gmap Z (bv 8),
              uv_wr pt Mx (SH_DATA_PG + 0x10) 0x88 -> uv_rd pt Mx SH_BUF 100).
    { intros Mx H.
      apply (sh_bss_rd pt Mx hbase hlen SH_BUF 100 Hlay H); lia. }
    (* ---- 0x938  c.mv a1,s3 ---- *)
    iApply (wp_uv_cmv C pt Psh MA8 m17 (mword_of_int 0x938)
              a1_idx s3_idx (mword_of_int 100)
              (ui_sh_938 pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_17 moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (CID29) "Hcg Hpc".
    iEval (rewrite E938) in "Hpc".
    set (m18 := <[Regidx a1_idx
                  := regval_into_reg (mword_of_int 100 : mword 64)]> m17).
    assert (Hm18 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
              m18 !!! Regidx r = m17 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m17 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x93a  c.mv a0,s2 ---- *)
    iApply (wp_uv_cmv C pt Psh MA8 m18 (mword_of_int 0x93a)
              a0_idx s2_idx (mword_of_int SH_BUF)
              (ui_sh_93a pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm18 s2_idx ltac:(vm_compute; discriminate)) Hs2_17
                            moi_add_zero_l; reflexivity)
              with "Hcg Hpc").
    iIntros (CID30) "Hcg Hpc".
    iEval (rewrite E93a) in "Hpc".
    set (m19 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int SH_BUF : mword 64)]> m18).
    assert (Hm19 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              m19 !!! Regidx r = m18 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m18 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x93c  jal ra,0x0 <getcmd> ---- *)
    iApply (wp_uv_jal C pt Psh MA8 m19 (mword_of_int 0x93c)
              (mword_of_int 2094788 : mword 21) ra_idx
              (mword_of_int 0x0) (mword_of_int 0x940)
              (ui_sh_93c pt MA8 Hl Htext8)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID31) "Hcg Hpc".
    iEval (rewrite <- Hsgetcmd) in "Hpc".
    set (m20 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x940 : mword 64)]> m19).
    assert (Hm20 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              m20 !!! Regidx r = m19 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m19 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra20 : m20 !!! Regidx ra_idx = (mword_of_int 0x940 : mword 64))
      by exact (upd_eq m19 (Regidx ra_idx) _).
    assert (Ha0_20 : m20 !!! Regidx a0_idx = (mword_of_int SH_BUF : mword 64)).
    { rewrite (Hm20 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m18 (Regidx a0_idx) _). }
    assert (Ha1_20 : m20 !!! Regidx a1_idx = (mword_of_int 100 : mword 64)).
    { rewrite (Hm20 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m17 (Regidx a1_idx) _). }
    assert (Hsp20 : m20 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hm20 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm19 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm18 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp17. }
    assert (Hret20 : is_aligned_vaddr
                       (Virtaddr (m20 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra20; vm_compute; reflexivity).
    (* ---- the call: getcmd(buf, 100) ---- *)
    iEval (rewrite <- (app_nil_r sh_echo_input)) in "Hin".
    iApply (wp_sh_getcmd C pt gin gbrk hbase hlen Q CID31 MA8 m20
              (mword_of_int (uint sp0 - 64)) SH_BUF 100 sh_echo_input []
              Hlay Himg8 Hsp20 (Hst128 MA8 Hdom8) Ha0_20 Ha1_20
              sh_echo_gets_taken Hfit1 (Hwrbuf MA8 Hbssw8) (Hrdbuf MA8 Hbssw8)
              Hfr128 Hbufhi sh_echo_head Hdisjb Hret20
              with "Hcg Hin Hpc").
    iIntros (CID32 mR MR) "%HRcs %HRa0 %HRstr %HRz %HRonly Hin Hcg Hpc".
    iEval (rewrite Hra20) in "Hpc".
    cbv [sh_win] in HRonly. rewrite Husp in HRonly.

    (* --- what the run keeps across [getcmd] --- *)
    assert (HdomR : forall k : Z, is_Some (M !! k) -> is_Some (MR !! k))
      by (intros k Hk; exact (proj1 HRonly k (Hdom8 k Hk))).
    assert (HbsswR : uv_wr pt MR (SH_DATA_PG + 0x10) 0x88)
      by exact (uv_wr_dom pt M MR _ _ HdomR Hbssw).
    assert (HimgR : sh_img_sub MR).
    { refine (sh_img_only_in MA8 MR _ HRonly _ Himg8). intros k Hk. sh_notin. }
    assert (HtextR : sh_text_sub MR) by exact (sh_img_text MR HimgR).
    (* the two NARROW .bss windows [parsecmd] needs -- sliced out of the
       whole-.bss claim BEFORE [gets] filled the buffer, and transported
       across [getcmd]'s two disturbed windows, neither of which contains
       [SH_FREEP] (0x2010) or [SH_BASE]+8 (0x2090). *)
    assert (Hfreep8 : sh_zeroed MA8 SH_FREEP 0 8)
      by (intros j Hj; unfold SH_FREEP; apply Hbss8; lia).
    assert (Hbasesz8 : sh_zeroed MA8 (SH_BASE + 8) 0 8).
    { intros j Hj.
      assert (Eb : SH_BASE + 8 + j = SH_DATA_PG + 0x10 + (0x80 + j))
        by (unfold SH_BASE, SH_DATA_PG; lia).
      rewrite Eb. apply Hbss8. lia. }
    assert (Hfreepv : SH_FREEP = 8208) by (vm_compute; reflexivity).
    assert (Hbasev : SH_BASE = 8328) by (vm_compute; reflexivity).
    assert (HfreepR : sh_zeroed MR SH_FREEP 0 8).
    { refine (sh_zeroed_only_in MA8 MR _ SH_FREEP 0 8 HRonly _ Hfreep8).
      intros k Hk. sh_notin. }
    assert (HbaseszR : sh_zeroed MR (SH_BASE + 8) 0 8).
    { refine (sh_zeroed_only_in MA8 MR _ (SH_BASE + 8) 0 8 HRonly _ Hbasesz8).
      intros k Hk. sh_notin. }
    (* the callee-saved registers, read back through [ucallee_saved] *)
    assert (Hs2_20 : m20 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64)).
    { rewrite (Hm20 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm18 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_17. }
    assert (Hs3_20 : m20 !!! Regidx s3_idx = (mword_of_int 100 : mword 64)).
    { rewrite (Hm20 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm18 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_17. }
    assert (Hs4_20 : m20 !!! Regidx s4_idx = (mword_of_int 10 : mword 64)).
    { rewrite (Hm20 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm18 s4_idx ltac:(vm_compute; discriminate)). exact Hs4_17. }
    assert (Hs5_20 : m20 !!! Regidx s5_idx = (mword_of_int 99 : mword 64)).
    { rewrite (Hm20 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm18 s5_idx ltac:(vm_compute; discriminate)). exact Hs5_17. }
    assert (Hs6_20 : m20 !!! Regidx s6_idx = (mword_of_int 32 : mword 64)).
    { rewrite (Hm20 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm19 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm18 s6_idx ltac:(vm_compute; discriminate)). exact Hs6_17. }
    assert (HRsp : mR !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HRcs csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp20).
    assert (HRs2 : mR !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (HRcs s2_idx ltac:(vm_compute; reflexivity)); exact Hs2_20).
    assert (HRs3 : mR !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (HRcs s3_idx ltac:(vm_compute; reflexivity)); exact Hs3_20).
    assert (HRs4 : mR !!! Regidx s4_idx = (mword_of_int 10 : mword 64))
      by (rewrite (HRcs s4_idx ltac:(vm_compute; reflexivity)); exact Hs4_20).
    assert (HRs5 : mR !!! Regidx s5_idx = (mword_of_int 99 : mword 64))
      by (rewrite (HRcs s5_idx ltac:(vm_compute; reflexivity)); exact Hs5_20).
    assert (HRs6 : mR !!! Regidx s6_idx = (mword_of_int 32 : mword 64))
      by (rewrite (HRcs s6_idx ltac:(vm_compute; reflexivity)); exact Hs6_20).
    (* getcmd returned 0: the line is non-empty *)
    assert (Hbd : bool_decide (sh_echo_input = []) = false)
      by (apply bool_decide_eq_false_2; exact sh_echo_nonnil).
    assert (HRa0' : mR !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
      by (rewrite HRa0 Hbd; reflexivity).
    (* --- the pc ticks of the command-dispatch block --- *)
    assert (E944 : add_vec_int (mword_of_int 0x944 : mword 64) 4 = mword_of_int 0x948)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E948 : add_vec_int (mword_of_int 0x948 : mword 64) 4 = mword_of_int 0x94c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E94e : add_vec_int (mword_of_int 0x94e : mword 64) 4 = mword_of_int 0x952)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E952 : add_vec_int (mword_of_int 0x952 : mword 64) 4 = mword_of_int 0x956)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E956 : add_vec_int (mword_of_int 0x956 : mword 64) 4 = mword_of_int 0x95a)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x940  bltz a0,0x9ca   (NOT taken: getcmd returned 0) ---- *)
    iApply (wp_uv_btype0 C pt Psh MR mR (mword_of_int 0x940)
              (mword_of_int 138 : mword 13) a0_idx BLT
              false (mword_of_int 0x9ca)
              (ui_sh_940 pt MR Hl HtextR)
              ltac:(cbn [uv_btaken]; rewrite HRa0'; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID33) "Hcg Hpc".
    assert (E940 : (if false then (mword_of_int 0x9ca : mword 64)
                    else add_vec_int (mword_of_int 0x940 : mword 64) 4)
                   = mword_of_int 0x944)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E940) in "Hpc".
    (* ---- 0x944  lbu a5,0(s2)   (buf[0] = 'e') ---- *)
    assert (HrdR : uv_rd pt MR SH_BUF 100) by exact (Hrdbuf MR HbsswR).
    destruct (uv_rd_leaf_at pt MR SH_BUF 100 SH_BUF HrdR ltac:(lia))
      as (wbuf & Hwbufl & Hwbufok).
    assert (Hubuf : uint (mword_of_int SH_BUF : mword 64) = SH_BUF)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hcanbuf : uva_canon (mword_of_int SH_BUF : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hbyte0 : MR !! (uint (mword_of_int SH_BUF : mword 64))
                     = Some (Z_to_bv 8 101)).
    { rewrite Hubuf. destruct HRstr as (Hb & _).
      assert (E0 : SH_BUF + Z.of_nat 0 = SH_BUF) by lia.
      rewrite <- E0. apply Hb. vm_compute. reflexivity. }
    iApply (wp_uv_lbu C pt Psh MR mR (mword_of_int 0x944)
              (mword_of_int 0 : mword 12) s2_idx a5_idx
              wbuf (mword_of_int SH_BUF) (mword_of_int 101) (Z_to_bv 8 101)
              (ui_sh_944 pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HRs2;
                    assert (Hz : (sign_extend' 64 (mword_of_int 0 : mword 12)
                                  : mword 64) = mword_of_int 0)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Hz moi_add; f_equal; lia)
              Hwbufl Hwbufok Hcanbuf Hbyte0
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID34) "Hcg Hpc".
    iEval (rewrite E944) in "Hpc".
    set (m21 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 101 : mword 64)]> mR).
    assert (Hm21 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              m21 !!! Regidx r = mR !!! Regidx r)
      by (intros r Hr; exact (upd_ne mR (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha5_21 : m21 !!! Regidx a5_idx = (mword_of_int 101 : mword 64))
      by exact (upd_eq mR (Regidx a5_idx) _).
    (* ---- 0x948  addi a4,a5,-32 ---- *)
    iApply (wp_uv_addi C pt Psh MR m21 (mword_of_int 0x948)
              (mword_of_int 4064 : mword 12) a5_idx a4_idx (mword_of_int 69)
              (ui_sh_948 pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_21; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID35) "Hcg Hpc".
    iEval (rewrite E948) in "Hpc".
    set (m22 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int 69 : mword 64)]> m21).
    assert (Hm22 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              m22 !!! Regidx r = m21 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m21 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_22 : m22 !!! Regidx a4_idx = (mword_of_int 69 : mword 64))
      by exact (upd_eq m21 (Regidx a4_idx) _).
    (* ---- 0x94c  c.beqz a4,0x95c   (NOT taken: buf[0] is not ' ') ---- *)
    iApply (wp_uv_cbeqz C pt Psh MR m22 (mword_of_int 0x94c)
              (mword_of_int 8 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              false (mword_of_int 0x95c)
              (ui_sh_94c pt MR Hl HtextR)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha4_22; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID36) "Hcg Hpc".
    assert (E94c : (if false then (mword_of_int 0x95c : mword 64)
                    else add_vec_int (mword_of_int 0x94c : mword 64) 2)
                   = mword_of_int 0x94e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E94c) in "Hpc".
    (* ---- 0x94e  addi a4,a5,-9 ---- *)
    assert (Ha5_22 : m22 !!! Regidx a5_idx = (mword_of_int 101 : mword 64))
      by (rewrite (Hm22 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_21).
    iApply (wp_uv_addi C pt Psh MR m22 (mword_of_int 0x94e)
              (mword_of_int 4087 : mword 12) a5_idx a4_idx (mword_of_int 92)
              (ui_sh_94e pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_22; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID37) "Hcg Hpc".
    iEval (rewrite E94e) in "Hpc".
    set (m23 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int 92 : mword 64)]> m22).
    assert (Hm23 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              m23 !!! Regidx r = m22 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m22 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_23 : m23 !!! Regidx a4_idx = (mword_of_int 92 : mword 64))
      by exact (upd_eq m22 (Regidx a4_idx) _).
    (* ---- 0x952  auipc s1,0x1 ---- *)
    iApply (wp_uv_auipc C pt Psh MR m23 (mword_of_int 0x952)
              (mword_of_int 1 : mword 20) s1_idx (mword_of_int 0x1952)
              (ui_sh_952 pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID38) "Hcg Hpc".
    iEval (rewrite E952) in "Hpc".
    set (m24 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int 0x1952 : mword 64)]> m23).
    assert (Hm24 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              m24 !!! Regidx r = m23 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m23 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_24 : m24 !!! Regidx s1_idx = (mword_of_int 0x1952 : mword 64))
      by exact (upd_eq m23 (Regidx s1_idx) _).
    (* ---- 0x956  addi s1,s1,1742   (-> 0x2020, cmd = buf) ---- *)
    iApply (wp_uv_addi C pt Psh MR m24 (mword_of_int 0x956)
              (mword_of_int 1742 : mword 12) s1_idx s1_idx
              (mword_of_int SH_BUF)
              (ui_sh_956 pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_24; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID39) "Hcg Hpc".
    iEval (rewrite E956) in "Hpc".
    set (m25 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int SH_BUF : mword 64)]> m24).
    assert (Hm25 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
              m25 !!! Regidx r = m24 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m24 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_25 : m25 !!! Regidx s1_idx = (mword_of_int SH_BUF : mword 64))
      by exact (upd_eq m24 (Regidx s1_idx) _).
    assert (Ha4_25 : m25 !!! Regidx a4_idx = (mword_of_int 92 : mword 64)).
    { rewrite (Hm25 a4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm24 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_23. }
    assert (Ha5_25 : m25 !!! Regidx a5_idx = (mword_of_int 101 : mword 64)).
    { rewrite (Hm25 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm24 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm23 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_22. }
    assert (Hmb : forall r : mword 5,
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> m25 !!! Regidx r = mR !!! Regidx r).
    { intros r H1 H2 H3.
      rewrite (Hm25 r H1) (Hm24 r H1) (Hm23 r H2) (Hm22 r H2) (Hm21 r H3).
      reflexivity. }
    assert (Hsp25 : m25 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hmb csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HRsp).
    assert (Hs4_25 : m25 !!! Regidx s4_idx = (mword_of_int 10 : mword 64))
      by (rewrite (Hmb s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HRs4).
    assert (Hs5_25 : m25 !!! Regidx s5_idx = (mword_of_int 99 : mword 64))
      by (rewrite (Hmb s5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HRs5).
    (* ---- 0x95a  c.bnez a4,0x976   (TAKEN: buf[0] is not '\t') ---- *)
    iApply (wp_uv_cbnez C pt Psh MR m25 (mword_of_int 0x95a)
              (mword_of_int 14 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              true (mword_of_int 0x976)
              (ui_sh_95a pt MR Hl HtextR)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha4_25; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID40) "Hcg Hpc".
    (* ---- 0x976  beq a5,s4,0x938   (NOT taken: 'e' is not '\n') ---- *)
    iApply (wp_uv_btype C pt Psh MR m25 (mword_of_int 0x976)
              (mword_of_int 8130 : mword 13) s4_idx a5_idx BEQ
              false (mword_of_int 0x938)
              (ui_sh_976 pt MR Hl HtextR)
              ltac:(cbn [uv_btaken]; rewrite Ha5_25 Hs4_25;
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CID41) "Hcg Hpc".
    assert (E976 : (if false then (mword_of_int 0x938 : mword 64)
                    else add_vec_int (mword_of_int 0x976 : mword 64) 4)
                   = mword_of_int 0x97a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E976) in "Hpc".
    (* ---- 0x97a  bne a5,s5,0x92c   (TAKEN: 'e' is not 'c') ---- *)
    iApply (wp_uv_btype C pt Psh MR m25 (mword_of_int 0x97a)
              (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE
              true (mword_of_int 0x92c)
              (ui_sh_97a pt MR Hl HtextR)
              ltac:(cbn [uv_btaken]; rewrite Ha5_25 Hs5_25;
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID42) "Hcg Hpc".

    (* ---- 0x92c  jal ra,0x68 <fork1> ---- *)
    iApply (wp_uv_jal C pt Psh MR m25 (mword_of_int 0x92c)
              (mword_of_int 2094908 : mword 21) ra_idx
              (mword_of_int 0x68) (mword_of_int 0x930)
              (ui_sh_92c pt MR Hl HtextR)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID43) "Hcg Hpc".
    iEval (rewrite <- Hsfork1) in "Hpc".
    set (m26 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x930 : mword 64)]> m25).
    assert (Hm26 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              m26 !!! Regidx r = m25 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m25 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra26 : m26 !!! Regidx ra_idx = (mword_of_int 0x930 : mword 64))
      by exact (upd_eq m25 (Regidx ra_idx) _).
    assert (Hsp26 : m26 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hm26 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp25).
    assert (Hs1_26 : m26 !!! Regidx s1_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (Hm26 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_25).
    assert (Hs2_26 : m26 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (Hm26 s2_idx ltac:(vm_compute; discriminate));
          rewrite (Hmb s2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HRs2).
    assert (Hs3_26 : m26 !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (Hm26 s3_idx ltac:(vm_compute; discriminate));
          rewrite (Hmb s3_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact HRs3).
    (* ---- the call: fork1() ---- *)
    iApply (wp_sh_fork1 C pt gin gbrk hbase hlen Q CID43 MR m26
              (mword_of_int (uint sp0 - 64))
              Hlay HtextR Hsp26 (Hst16 MR HdomR)
              ltac:(unfold sh_frame_ok; rewrite Husp; lia)
              ltac:(rewrite Hra26; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID44 mF MF ret) "%HFcs %HFa0 %HFret %HFonly Hcg Hpc".
    iEval (rewrite Hra26) in "Hpc".
    rewrite Husp in HFonly.
    assert (HFonly' : uM_only_in MR MF [sh_win (uint sp0 - 64 - 16) 16])
      by (cbv [sh_win]; apply uM_only_in_one; exact HFonly).
    assert (HdomF : forall k : Z, is_Some (M !! k) -> is_Some (MF !! k))
      by (intros k Hk; exact (proj1 HFonly' k (HdomR k Hk))).
    assert (HimgF : sh_img_sub MF).
    { refine (sh_img_only_in MR MF _ HFonly' _ HimgR). intros k Hk. sh_notin. }
    assert (HtextF : sh_text_sub MF) by exact (sh_img_text MF HimgF).
    assert (HbsswF : uv_wr pt MF (SH_DATA_PG + 0x10) 0x88)
      by exact (uv_wr_dom pt M MF _ _ HdomF Hbssw).
    assert (HfreepF : sh_zeroed MF SH_FREEP 0 8).
    { refine (sh_zeroed_only_in MR MF _ SH_FREEP 0 8 HFonly' _ HfreepR).
      intros k Hk. sh_notin. }
    assert (HbaseszF : sh_zeroed MF (SH_BASE + 8) 0 8).
    { refine (sh_zeroed_only_in MR MF _ (SH_BASE + 8) 0 8 HFonly' _ HbaseszR).
      intros k Hk. sh_notin. }
    assert (HstrF : ustr_at MF SH_BUF sh_echo_input).
    { refine (ustr_at_only_in MR MF _ SH_BUF sh_echo_input HFonly' _ HRstr).
      intros k Hk. rewrite Hlen18 in Hk. sh_notin. }
    assert (HzF : sh_zeroed MF SH_BUF (Z.of_nat (length sh_echo_input) + 1) 100).
    { refine (sh_zeroed_only_in MR MF _ SH_BUF _ 100 HFonly' _ HRz).
      intros k Hk. rewrite Hlen18 in Hk. sh_notin. }
    assert (HFsp : mF !!! Regidx csp_rs1
                   = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (HFcs csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp26).
    assert (HFs1 : mF !!! Regidx s1_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (HFcs s1_idx ltac:(vm_compute; reflexivity)); exact Hs1_26).
    assert (HFs2 : mF !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64))
      by (rewrite (HFcs s2_idx ltac:(vm_compute; reflexivity)); exact Hs2_26).
    assert (HFs3 : mF !!! Regidx s3_idx = (mword_of_int 100 : mword 64))
      by (rewrite (HFcs s3_idx ltac:(vm_compute; reflexivity)); exact Hs3_26).
    (* ---- 0x930  c.beqz a0,0x9c0.  ONE proof, BOTH processes: the arm is
       taken in the child (fork returned 0) and not in the parent. ---- *)
    destruct HFret as [ Hchild | Hparent ].
    - (* ================= THE CHILD: fork1() returned 0 ================= *)
      assert (Hret0 : ret = (mword_of_int 0 : mword 64))
        by (apply moi_of_uint_eq; exact Hchild).
      (* ---- 0x930  c.beqz a0,0x9c0  (TAKEN) ---- *)
      iApply (wp_uv_cbeqz C pt Psh MF mF (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x9c0)
                (ui_sh_930 pt MF Hl HtextF)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite HFa0 Hret0; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID45) "Hcg Hpc".
      (* ---- 0x9c0  c.mv a0,s1 ---- *)
      iApply (wp_uv_cmv C pt Psh MF mF (mword_of_int 0x9c0)
                a0_idx s1_idx (mword_of_int SH_BUF)
                (ui_sh_9c0 pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HFs1 moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (CID46) "Hcg Hpc".
      assert (E9c0 : add_vec_int (mword_of_int 0x9c0 : mword 64) 2
                     = mword_of_int 0x9c2)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E9c0) in "Hpc".
      set (m27 := <[Regidx a0_idx
                    := regval_into_reg (mword_of_int SH_BUF : mword 64)]> mF).
      assert (Hm27 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                m27 !!! Regidx r = mF !!! Regidx r)
        by (intros r Hr; exact (upd_ne mF (Regidx a0_idx) (Regidx r) _ Hr)).
      (* ---- 0x9c2  jal ra,0x86e <parsecmd> ---- *)
      iApply (wp_uv_jal C pt Psh MF m27 (mword_of_int 0x9c2)
                (mword_of_int 2096812 : mword 21) ra_idx
                (mword_of_int 0x86e) (mword_of_int 0x9c6)
                (ui_sh_9c2 pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID47) "Hcg Hpc".
      iEval (rewrite <- Hsparsecmd) in "Hpc".
      set (m28 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x9c6 : mword 64)]> m27).
      assert (Hm28 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                m28 !!! Regidx r = m27 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m27 (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hra28 : m28 !!! Regidx ra_idx = (mword_of_int 0x9c6 : mword 64))
        by exact (upd_eq m27 (Regidx ra_idx) _).
      assert (Ha0_28 : m28 !!! Regidx a0_idx = (mword_of_int SH_BUF : mword 64)).
      { rewrite (Hm28 a0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq mF (Regidx a0_idx) _). }
      assert (Hsp28 : m28 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (Hm28 csp_rs1 ltac:(vm_compute; discriminate)).
        rewrite (Hm27 csp_rs1 ltac:(vm_compute; discriminate)). exact HFsp. }
      (* ---- the call: parsecmd(cmd) ---- *)
      assert (Hpre28 : sh_parse_pre pt hbase hlen MF SH_BUF sh_echo_input
                         (mword_of_int (uint sp0 - 64))
                         (64 + 48 + 48 + 128 + 112 + 64 + 16)).
      { unfold sh_parse_pre, sh_buf_ok, sh_frame_ok. rewrite Husp.
        change (64 + 48 + 48 + 128 + 112 + 64 + 16) with 480.
        rewrite Hlen18. split_and!.
        - exact Hlay.
        - exact HimgF.
        - exact (sh_img_tables MF (sh_img_data MF HimgF)).
        - exact HstrF.
        - exact sh_echo_no_nul.
        - exact sh_echo_no_symbols.
        - exact (uv_rd_sub pt MF SH_BUF 100 SH_BUF 19 (Hrdbuf MF HbsswF)
                   ltac:(lia) ltac:(lia) ltac:(lia)).
        - exact (uv_wr_sub pt MF SH_BUF 100 SH_BUF 19 (Hwrbuf MF HbsswF)
                   ltac:(lia) ltac:(lia) ltac:(lia)).
        - lia.
        - change (2 ^ 38) with 274877906944. lia.
        - lia.
        - lia. }
      iApply (Hparsecmd CID47 MF m28 (mword_of_int (uint sp0 - 64)) SH_BUF
                sh_echo_input sh_echo_toks
                Hpre28 Hsp28
                ltac:(exact (uv_stack_dom pt M MF _ 480 HdomF Hst480))
                Ha0_28
                (* sh_buf_clear's third conjunct is no longer an sh_disj:
                   it is the plain [s0 + len <= hbase], so there is no arm
                   to pick, only an inequality to close. *)
                ltac:(unfold sh_buf_clear, sh_disj; rewrite Hlen18;
                      split_and!; [ right | left | idtac ]; lia)
                sh_echo_tokens sh_echo_toks_ne
                ltac:(rewrite Hlen18; change (2 ^ 31) with 2147483648; lia)
                HfreepF HbaseszF HbsswF
                ltac:(rewrite Hra28; vm_compute; reflexivity)
                with "Hcg Hbrk Hpc").
      iIntros (CID48 mP MP cmd p0)
        "%HPcs %HPa0 %HPcmd %HPtype %HPp0 %HPp0nz %HPbel %HPrd %HPonly Hbrk Hcg Hpc".
      iEval (rewrite Hra28) in "Hpc".
      cbv [sh_win] in HPonly. rewrite Husp in HPonly.
      change (64 + 48 + 48 + 128 + 112 + 64 + 16) with 480 in HPonly.
      rewrite sh_echo_path_eq sh_echo_argv_eq in HPbel.
      assert (Hnu : sh_nunits SH_EXECCMD_SZ = 12) by (vm_compute; reflexivity).
      assert (Hcmdv : cmd = hbase + 65360) by (rewrite HPcmd Hnu; lia).
      assert (HimgP : sh_img_sub MP).
      { refine (sh_img_only_in MF MP _ HPonly _ HimgF).
        intros k Hk. sh_notin. }
      assert (HtextP : sh_text_sub MP) by exact (sh_img_text MP HimgP).
      assert (HdomP : forall k : Z, is_Some (M !! k) -> is_Some (MP !! k))
        by (intros k Hk; exact (proj1 HPonly k (HdomF k Hk))).
      (* ---- 0x9c6  jal ra,0x8e <runcmd> ---- *)
      assert (HPsp : mP !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (HPcs csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp28).
      iApply (wp_uv_jal C pt Psh MP mP (mword_of_int 0x9c6)
                (mword_of_int 2094792 : mword 21) ra_idx
                (mword_of_int 0x8e) (mword_of_int 0x9ca)
                (ui_sh_9c6 pt MP Hl HtextP)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID49) "Hcg Hpc".
      iEval (rewrite <- Hsruncmd) in "Hpc".
      set (m29 := <[Regidx ra_idx
                    := regval_into_reg (mword_of_int 0x9ca : mword 64)]> mP).
      assert (Hm29 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                m29 !!! Regidx r = mP !!! Regidx r)
        by (intros r Hr; exact (upd_ne mP (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hsp29 : m29 !!! Regidx csp_rs1
                      = (mword_of_int (uint sp0 - 64) : mword 64))
        by (rewrite (Hm29 csp_rs1 ltac:(vm_compute; discriminate)); exact HPsp).
      assert (Ha0_29 : m29 !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
        by (rewrite (Hm29 a0_idx ltac:(vm_compute; discriminate)); exact HPa0).
      (* [cmd] is malloc's node: 16-aligned, because [hbase] is page-aligned *)
      assert (Hhb : Z.rem hbase 4096 = 0) by exact (shl_hbase _ _ _ Hlay).
      rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
      assert (Hk : exists k : Z, hbase = 4096 * k)
        by (exists (hbase / 4096);
            pose proof (Z.div_mod hbase 4096 ltac:(lia)) as Hdm; lia).
      destruct Hk as (kk & Hkk).
      assert (Hal16 : Z.rem cmd 16 = 0).
      { rewrite Hcmdv Hkk. rewrite Z.rem_mod_nonneg; [ | lia | lia ].
        replace (4096 * kk + 65360) with ((256 * kk + 4085) * 16) by lia.
        apply Z.mod_mul. lia. }
      (* ---- the call: runcmd(cmd) -- DOES NOT RETURN ---- *)
      iApply (wp_sh_runcmd_exec C pt gin gbrk hbase hlen Q CID49 MP m29
                (mword_of_int (uint sp0 - 64)) cmd p0
                sh_echo_path sh_echo_argv
                Hlay HimgP Hsp29
                ltac:(exact (uv_stack_dom pt M MP _ 48 HdomP (Hst48 M Hdom0)))
                Ha0_29
                ltac:(lia)
                HPtype HPp0 HPp0nz
                Hal16
                ltac:(unfold SH_EXECCMD_SZ; lia)
                HPbel
                ltac:(unfold sh_frame_ok; rewrite Husp; lia)
                HPrd
                with "Hcg HQ Hpc").

    - (* ============ THE PARENT: fork1() returned a positive pid ========= *)
      assert (Hnz : eq_vec ret (zero_reg : mword 64) = false).
      { apply eq_vec_false_iff. intro He. rewrite He in Hparent.
        rewrite Hz0s in Hparent. lia. }
      (* ---- 0x930  c.beqz a0,0x9c0  (NOT taken) ---- *)
      iApply (wp_uv_cbeqz C pt Psh MF mF (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x9c0)
                (ui_sh_930 pt MF Hl HtextF)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite HFa0 Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CID45) "Hcg Hpc".
      assert (E930 : (if false then (mword_of_int 0x9c0 : mword 64)
                      else add_vec_int (mword_of_int 0x930 : mword 64) 2)
                     = mword_of_int 0x932)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E930) in "Hpc".
      (* ---- 0x932  c.li a0,0 ---- *)
      iApply (wp_uv_cli C pt Psh MF mF (mword_of_int 0x932)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (ui_sh_932 pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID46) "Hcg Hpc".
      assert (E932 : add_vec_int (mword_of_int 0x932 : mword 64) 2
                     = mword_of_int 0x934)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E932) in "Hpc".
      set (n1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mF).
      assert (Hn1 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                n1 !!! Regidx r = mF !!! Regidx r)
        by (intros r Hr; exact (upd_ne mF (Regidx a0_idx) (Regidx r) _ Hr)).
      (* ---- 0x934  jal ra,0xc8e <wait> ---- *)
      iApply (wp_uv_jal C pt Psh MF n1 (mword_of_int 0x934)
                (mword_of_int 858 : mword 21) ra_idx
                (mword_of_int 0xc8e) (mword_of_int 0x938)
                (ui_sh_934 pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID47) "Hcg Hpc".
      iEval (rewrite <- Hswait) in "Hpc".
      set (n2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x938 : mword 64)]> n1).
      assert (Hn2 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                n2 !!! Regidx r = n1 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n1 (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hra_n2 : n2 !!! Regidx ra_idx = (mword_of_int 0x938 : mword 64))
        by exact (upd_eq n1 (Regidx ra_idx) _).
      assert (Hn21 : forall r : mword 5,
                Regidx r <> Regidx ra_idx -> Regidx r <> Regidx a0_idx ->
                n2 !!! Regidx r = mF !!! Regidx r)
        by (intros r H1 H2; rewrite (Hn2 r H1) (Hn1 r H2); reflexivity).
      (* ---- the call: wait(0) ---- *)
      iApply (wp_sh_wait0 C pt gin gbrk hbase hlen Q CID47 MF n2
                ltac:(split_and!;
                      [ exact Hlay | exact HtextF
                      | rewrite Hra_n2; vm_compute; reflexivity ])
                ltac:(rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate));
                      rewrite (upd_eq mF (Regidx a0_idx)
                                 (regval_into_reg (mword_of_int 0 : mword 64)));
                      vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID48 rw) "Hcg Hpc".
      iEval (rewrite Hra_n2) in "Hpc".
      set (n3 := <[Regidx a0_idx := rw]>
                   (<[Regidx a7_idx := (mword_of_int SYS_wait : mword 64)]> n2)).
      assert (Hn3 : forall r : mword 5,
                Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a7_idx ->
                n3 !!! Regidx r = n2 !!! Regidx r).
      { intros r Hr Hr'.
        exact (eq_trans (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hr)
                 (upd_ne n2 (Regidx a7_idx) (Regidx r) _ Hr')). }
      assert (Hsp_n3 : n3 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (Hn21 csp_rs1 ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact HFsp. }
      assert (Hs2_n3 : n3 !!! Regidx s2_idx = (mword_of_int SH_BUF : mword 64)).
      { rewrite (Hn3 s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (Hn21 s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact HFs2. }
      assert (Hs3_n3 : n3 !!! Regidx s3_idx = (mword_of_int 100 : mword 64)).
      { rewrite (Hn3 s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (Hn21 s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact HFs3. }
      (* ------------------------------------------------------------------ *)
      (* REPL ITERATION 2: getcmd hits EOF and returns -1.                   *)
      (* ------------------------------------------------------------------ *)
      (* ---- 0x938  c.mv a1,s3 ---- *)
      iApply (wp_uv_cmv C pt Psh MF n3 (mword_of_int 0x938)
                a1_idx s3_idx (mword_of_int 100)
                (ui_sh_938 pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_n3 moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (CID49) "Hcg Hpc".
      iEval (rewrite E938) in "Hpc".
      set (n4 := <[Regidx a1_idx
                   := regval_into_reg (mword_of_int 100 : mword 64)]> n3).
      assert (Hn4 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                n4 !!! Regidx r = n3 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n3 (Regidx a1_idx) (Regidx r) _ Hr)).
      (* ---- 0x93a  c.mv a0,s2 ---- *)
      iApply (wp_uv_cmv C pt Psh MF n4 (mword_of_int 0x93a)
                a0_idx s2_idx (mword_of_int SH_BUF)
                (ui_sh_93a pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hn4 s2_idx ltac:(vm_compute; discriminate))
                              Hs2_n3 moi_add_zero_l; reflexivity)
                with "Hcg Hpc").
      iIntros (CID50) "Hcg Hpc".
      iEval (rewrite E93a) in "Hpc".
      set (n5 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int SH_BUF : mword 64)]> n4).
      assert (Hn5 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                n5 !!! Regidx r = n4 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n4 (Regidx a0_idx) (Regidx r) _ Hr)).
      (* ---- 0x93c  jal ra,0x0 <getcmd> ---- *)
      iApply (wp_uv_jal C pt Psh MF n5 (mword_of_int 0x93c)
                (mword_of_int 2094788 : mword 21) ra_idx
                (mword_of_int 0x0) (mword_of_int 0x940)
                (ui_sh_93c pt MF Hl HtextF)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID51) "Hcg Hpc".
      iEval (rewrite <- Hsgetcmd) in "Hpc".
      set (n6 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x940 : mword 64)]> n5).
      assert (Hn6 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                n6 !!! Regidx r = n5 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n5 (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hra_n6 : n6 !!! Regidx ra_idx = (mword_of_int 0x940 : mword 64))
        by exact (upd_eq n5 (Regidx ra_idx) _).
      assert (Ha0_n6 : n6 !!! Regidx a0_idx = (mword_of_int SH_BUF : mword 64)).
      { rewrite (Hn6 a0_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq n4 (Regidx a0_idx) _). }
      assert (Ha1_n6 : n6 !!! Regidx a1_idx = (mword_of_int 100 : mword 64)).
      { rewrite (Hn6 a1_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn5 a1_idx ltac:(vm_compute; discriminate)).
        exact (upd_eq n3 (Regidx a1_idx) _). }
      assert (Hsp_n6 : n6 !!! Regidx csp_rs1
                       = (mword_of_int (uint sp0 - 64) : mword 64)).
      { rewrite (Hn6 csp_rs1 ltac:(vm_compute; discriminate)).
        rewrite (Hn5 csp_rs1 ltac:(vm_compute; discriminate)).
        rewrite (Hn4 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_n3. }
      (* ---- the call: getcmd(buf, 100) at EOF ---- *)
      iApply (wp_sh_getcmd C pt gin gbrk hbase hlen Q CID51 MF n6
                (mword_of_int (uint sp0 - 64)) SH_BUF 100 [] []
                Hlay HimgF Hsp_n6 (Hst128 MF HdomF) Ha0_n6 Ha1_n6
                ltac:(right; split; reflexivity)
                Hfit0 (Hwrbuf MF HbsswF) (Hrdbuf MF HbsswF)
                Hfr128 Hbufhi Hnil0 Hdisjb
                ltac:(rewrite Hra_n6; vm_compute; reflexivity)
                with "Hcg Hin Hpc").
      iIntros (CID52 mS MS) "%HScs %HSa0 %HSstr %HSz %HSonly Hin Hcg Hpc".
      iEval (rewrite Hra_n6) in "Hpc".
      cbv [sh_win] in HSonly. rewrite Husp in HSonly.
      assert (HdomS : forall k : Z, is_Some (M !! k) -> is_Some (MS !! k))
        by (intros k Hk; exact (proj1 HSonly k (HdomF k Hk))).
      assert (HimgS : sh_img_sub MS).
      { refine (sh_img_only_in MF MS _ HSonly _ HimgF). intros k Hk. sh_notin. }
      assert (HtextS : sh_text_sub MS) by exact (sh_img_text MS HimgS).
      assert (Hbdnil : bool_decide (@nil (bv 8) = []) = true)
        by (apply bool_decide_eq_true_2; reflexivity).
      assert (HSa0' : mS !!! Regidx a0_idx = (mword_of_int (-1) : mword 64))
        by (rewrite HSa0 Hbdnil; reflexivity).
      (* ---- 0x940  bltz a0,0x9ca   (TAKEN: getcmd returned -1) ---- *)
      iApply (wp_uv_btype0 C pt Psh MS mS (mword_of_int 0x940)
                (mword_of_int 138 : mword 13) a0_idx BLT
                true (mword_of_int 0x9ca)
                (ui_sh_940 pt MS Hl HtextS)
                ltac:(cbn [uv_btaken]; rewrite HSa0'; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID53) "Hcg Hpc".
      (* ---- 0x9ca  c.li a0,0 ---- *)
      iApply (wp_uv_cli C pt Psh MS mS (mword_of_int 0x9ca)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (ui_sh_9ca pt MS Hl HtextS)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID54) "Hcg Hpc".
      assert (E9ca : add_vec_int (mword_of_int 0x9ca : mword 64) 2
                     = mword_of_int 0x9cc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E9ca) in "Hpc".
      set (n7 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mS).
      (* ---- 0x9cc  jal ra,0xc86 <exit>  -- DOES NOT RETURN ---- *)
      iApply (wp_uv_jal C pt Psh MS n7 (mword_of_int 0x9cc)
                (mword_of_int 698 : mword 21) ra_idx
                (mword_of_int 0xc86) (mword_of_int 0x9d0)
                (ui_sh_9cc pt MS Hl HtextS)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID55) "Hcg Hpc".
      iEval (rewrite <- Hsexit) in "Hpc".
      iApply (wp_sh_exit C pt gin gbrk hbase hlen Q CID55 MS
                (<[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x9d0 : mword 64)]> n7)
                Hlay HtextS with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* start() @0x9d0 -- the ELF entry point: the 16-byte gcc prologue,      *)
  (* `jal main', `jal exit'.  main DIVERGES, so the two instructions       *)
  (* after the call are dead and the `jal exit' is never reached.          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_start (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :
    wp_sh_start_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0.
  Proof.
    intros Hlay Himg Hsp Hst Hbss Hbssw Hstk Hstkhi.
    destruct sh_syms_pins
      as (Hsstart & Hsmain & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan, Hstk.
    assert (Hsphi : 77824 <= uint sp0 - 576) by lia.
    assert (Hst16 : uv_stack pt M sp0 16)
      by exact (proj1 (uv_stack_split pt M sp0 576 16 560 ltac:(lia) ltac:(lia)
                         ltac:(vm_compute; reflexivity) ltac:(lia) Hst)).
    assert (Hst544 : uv_stack pt M (mword_of_int (uint sp0 - 16)) 544).
    { pose proof (proj2 (uv_stack_split pt M sp0 576 16 560 ltac:(lia)
                           ltac:(lia) ltac:(vm_compute; reflexivity)
                           ltac:(lia) Hst)) as HS.
      rewrite (uv_stack_sp_moi pt M sp0 16 Hst16) in HS.
      exact (proj1 (uv_stack_split pt M (mword_of_int (uint sp0 - 16)) 560
                      544 16 ltac:(lia) ltac:(lia)
                      ltac:(vm_compute; reflexivity) ltac:(lia) HS)). }
    assert (Husp : uint (mword_of_int (uint sp0 - 16) : mword 64)
                   = uint sp0 - 16) by (apply uint_moi; unfold Z64; lia).
    iIntros "Hcg Hin Hbrk HQ Hpc".
    iEval (rewrite Hsstart) in "Hpc".
    (* ---- 0x9d0..0x9d6  the shared 16-byte prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0x9d0 sh_img_sub 0x2010 M m sp0
              Himg (fun Mx a v HT Hle => sh_img_store8 Mx a v HT Hle)
              ltac:(lia) Hsp Hst16
              (ui_sh_9d0 pt M Hl Htext)
              (fun Mx Hx => ui_sh_9d2 pt Mx Hl (sh_img_text Mx Hx))
              (fun Mx Hx => ui_sh_9d4 pt Mx Hl (sh_img_text Mx Hx))
              (fun Mx Hx => ui_sh_9d6 pt Mx Hl (sh_img_text Mx Hx))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (mp := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx
                    := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Himg2 : sh_img_sub M2).
    { unfold M2, M1. apply sh_img_store8; [ | lia ].
      apply sh_img_store8; [ exact Himg | lia ]. }
    assert (Htext2 : sh_text_sub M2) by exact (sh_img_text M2 Himg2).
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k))
      by (intros k Hk; unfold M2, M1;
          exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk))).
    assert (Hbss2 : sh_zeroed M2 (SH_DATA_PG + 0x10) 0 0x88).
    { unfold M2, M1.
      apply sh_zeroed_store8; [ apply sh_zeroed_store8; [ exact Hbss | ] | ];
        unfold SH_DATA_PG; lia. }
    assert (Hbssw2 : uv_wr pt M2 (SH_DATA_PG + 0x10) 0x88)
      by exact (uv_wr_dom pt M M2 _ _ Hdom2 Hbssw).
    (* ---- 0x9d8  jal ra,0x8e2 <main> ---- *)
    iApply (wp_uv_jal C pt Psh M2 mp (mword_of_int 0x9d8)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int 0x8e2) (mword_of_int 0x9dc)
              (ui_sh_9d8 pt M2 Hl Htext2)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite <- Hsmain) in "Hpc".
    set (mq := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x9dc : mword 64)]> mp).
    assert (Hspq : mq !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 16) : mword 64)).
    { rewrite (upd_ne mp (Regidx ra_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx sp_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx sp_idx) _). }
    (* ---- the call: main() -- DOES NOT RETURN ---- *)
    iApply (wp_sh_main CID2 M2 mq (mword_of_int (uint sp0 - 16))
              Hlay Himg2 Hspq
              ltac:(change (64 + (64 + 48 + 48 + 128 + 112 + 64 + 16)) with 544;
                    exact (uv_stack_dom pt M M2 _ 544 Hdom2 Hst544))
              Hbss2 Hbssw2
              (sh_img_tables M2 (sh_img_data M2 Himg2))
              ltac:(change (64 + (64 + 48 + 48 + 128 + 112 + 64 + 16)) with 544;
                    rewrite Husp; lia)
              ltac:(rewrite Husp; change (2 ^ 38) with 274877906944; lia)
              with "Hcg Hin Hbrk HQ Hpc").
  Qed.

End UProofShMain.
