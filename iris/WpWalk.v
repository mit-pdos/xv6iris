(* WpWalk.v -- the whole-function WP for xv6's walk() (kernel/vm.c): the
   3-level Sv39 page-table walk with allocation, proved ONCE over the
   abstract translation regime [R : s_regime] (boot instantiates
   [bare_regime], the user-table callers [kpt_regime kroot]).

   Spec of record: KvmSpec.v's [walk_spec] (this lemma concludes it).
   Decode catalog: WpWalkInstr.v (the wi_* facts; its header holds the
   instruction table and path structure).  Pure/Iris substrate:
   PtBuild.v (pt_rep0 / grafting / the address-arithmetic bridges /
   the V-bit dichotomy) and the ptree accessors (PtTree.v + PtBuild §5).

   PATH STRUCTURE (premises kill the panic arm [va < 2^38] and the
   alloc=0 arm [a2 = 1]): the two unrolled loop iterations each either
   DESCEND (slot V=1) or ALLOCATE (kalloc + memset + pointer-PTE store),
   and kalloc's null return exits through the shared epilogue with
   a0 = 0.  [pt_rep0 t m]'s per-vpn totality drives the branch:
     m !! vpn = Some w  ->  maps: descend, descend, w0 = the leaf word;
     None + blocks0 arm 1 -> graft2 {null-exit}, graft1 {null-exit};
     None + arm 2         -> descend, graft1 {null-exit};
     None + arm 3         -> descend, descend, w0 = 0.                  *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpMycpu.
Require Import WpLock.
Require Import WpKalloc WpMemsetPage.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import CommonWalk PtTree.
Require Import PtBuild KvmSpec.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMemWrap.
Require Import WpWalkInstr UserBits.
Require Export WpSmodeLeafBase.
From Kernel Require KernelSyms.
Import Defs.

Section Walk.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.walk.

  (* Fast register-map lookup discharge.  The intermediate maps [M1..M9],
     [L1..L9], [W1..W9], ... are deep [set]-chains of single-key inserts over
     the caller's [mm].  The old idiom [rewrite /M9 .. /W1; repeat rewrite
     lookup_total_insert_ne] unfolds the WHOLE ~27-layer chain into one giant
     term FIRST and then peels it, so every peel re-traverses a huge goal
     (O(depth^2), ~17 s per lookup).  [peel_reg] instead unfolds ONE layer at a
     time and peels it immediately, keeping the goal a single insert deep the
     whole way down (O(depth), sub-second).  Handles both the all-miss case
     (bottoms out at [mm !!! r = mm !!! r]) and a final hit. *)
  (* Discharge a register-key disequality [Regidx i <> Regidx j] fast, AND fail
     fast when i = j.  The naive [vm_compute; discriminate] proves i<>j fine but
     when handed the FALSE goal i<>i (which happens at a peel's terminating hit
     layer, and at the last, failing, iteration of every hand-written
     [repeat (rewrite lookup_total_insert_ne; [| ...])]) it burns ~4-8 s letting
     [discriminate] hunt in vain for a discriminating position in two equal
     [mword]/[bv] records.  Guard it: [unify i j] settles convertible-or-not
     cheaply (a miss fails on the syntactically-distinct index arg without ever
     reducing the [mword]), so we only reach [discriminate] on a genuine miss. *)
  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* Try the HIT lemma [lookup_total_insert] BEFORE the miss lemma at every
     layer, so a peel whose key is in the chain resolves at the hit instantly
     rather than attempting (and slowly failing) the miss lemma there.  Miss
     layers pay only one cheap failed unification before falling through. *)
  Ltac peel_reg :=
    repeat first
      [ rewrite lookup_total_insert
      | rewrite lookup_total_insert_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    reflexivity.

  (* the +64/-64 c.addi16sp frame cancel (walk's frame; clone of
     WpWakeup's wakeup_sp_cancel -- a whole-function file we do not
     import) *)
  Lemma walk_sp_cancel (X : mword 64) :
    add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
            (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = X.
  Proof.
    assert (add_vec_unsigned : forall x y : mword 64,
              bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
    { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
        SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned. reflexivity. }
    apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
    assert (HA : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64) = 18446744073709551552) by (vm_compute; reflexivity).
    assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64) = 64) by (vm_compute; reflexivity).
    rewrite HA HB. rewrite <- Z.add_assoc.
    replace (18446744073709551552 + 64) with (bv_modulus 64) by (vm_compute; reflexivity).
    rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
  Qed.

  (* ================================================================= *)
  (* THE SHARED EPILOGUE (+0x52..+0x64): every exit path funnels here    *)
  (* with the loop-exit register file [Mf], the eight frame cells still  *)
  (* holding the entry values, and the result payload already decided.   *)
  (* Qed-sealed once so the four paths do not each re-pay its ~30        *)
  (* sentences (CLAUDE.md chunk-lemma rule).                             *)
  (* ================================================================= *)
  Lemma wp_walk_epilogue (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    ((Mf !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0)
     \/ (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
          /\ Mf !!! Regidx (mword_of_int 10 : mword 5) = pt_addr0 p1 vpn)) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x52)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt Hn Hsp Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hpay.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (wi_52 with "Htext") as "Hi52".
    iPoseProof (wi_54 with "Htext") as "Hi54".
    iPoseProof (wi_56 with "Htext") as "Hi56".
    iPoseProof (wi_58 with "Htext") as "Hi58".
    iPoseProof (wi_5a with "Htext") as "Hi5a".
    iPoseProof (wi_5c with "Htext") as "Hi5c".
    iPoseProof (wi_5e with "Htext") as "Hi5e".
    iPoseProof (wi_60 with "Htext") as "Hi60".
    iPoseProof (wi_62 with "Htext") as "Hi62".
    iPoseProof (wi_64 with "Htext") as "Hi64".
    (* +0x52 c.ldsp x1,56(sp) *)
    pose proof Hsp as HspMf.
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x52)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              Mf (mm !!! Regidx (mword_of_int 1 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi52 [Hc56] [-]").
    { iEval (rewrite HspMf Hb1). iExact "Hc56". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
    iEval (rewrite HspMf Hb1) in "Hc56".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hpp52n : add_vec_int (mword_of_int (WK + 0x52) : mword 64) 2 = mword_of_int (WK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52n) in "Hpc".
    (* +0x54 c.ldsp x8,48(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspMf. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x54)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (mm !!! Regidx (mword_of_int 8 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi54 [Hc48] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc48". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
    iEval (rewrite HspE1 Hb2) in "Hc48".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpp54n : add_vec_int (mword_of_int (WK + 0x54) : mword 64) 2 = mword_of_int (WK + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54n) in "Hpc".
    (* +0x56 c.ldsp x9,40(sp) *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE1. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x56)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (mm !!! Regidx (mword_of_int 9 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi56 [Hc40] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc40". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
    iEval (rewrite HspE2 Hb3) in "Hc40".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpp56n : add_vec_int (mword_of_int (WK + 0x56) : mword 64) 2 = mword_of_int (WK + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56n) in "Hpc".
    (* +0x58 c.ldsp x18,32(sp) *)
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr).
    { rewrite /E3. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE2. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x58)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (mm !!! Regidx (mword_of_int 18 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi58 [Hc32] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc32". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
    iEval (rewrite HspE3 Hb4) in "Hc32".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hpp58n : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58n) in "Hpc".
    (* +0x5a c.ldsp x19,24(sp) *)
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr).
    { rewrite /E4. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE3. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (mm !!! Regidx (mword_of_int 19 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5a [Hc24] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
    iEval (rewrite HspE4 Hb5) in "Hc24".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hpp5an : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5an) in "Hpc".
    (* +0x5c c.ldsp x20,16(sp) *)
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr).
    { rewrite /E5. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE4. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (mm !!! Regidx (mword_of_int 20 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5c [Hc16] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
    iEval (rewrite HspE5 Hb6) in "Hc16".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hpp5cn : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5cn) in "Hpc".
    (* +0x5e c.ldsp x21,8(sp) *)
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr).
    { rewrite /E6. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE5. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x5e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (mm !!! Regidx (mword_of_int 21 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi5e [Hc08] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc08". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
    iEval (rewrite HspE6 Hb7) in "Hc08".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hpp5en : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5en) in "Hpc".
    (* +0x60 c.ldsp x22,0(sp) *)
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr).
    { rewrite /E7. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE6. }
    iApply (wp_cldsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x60)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              E7 (mm !!! Regidx (mword_of_int 22 : mword 5)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi60 [Hc00] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc00". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc00".
    iEval (rewrite HspE7 Hb8) in "Hc00".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hpp60n : add_vec_int (mword_of_int (WK + 0x60) : mword 64) 2 = mword_of_int (WK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60n) in "Hpc".
    (* +0x62 c.addi16sp sp,+64 *)
    iApply (wp_caddi16sp_gpr_s_r R γc Φ (mword_of_int (WK + 0x62)) (mword_of_int 4 : mword 6) E8 1%Qp
              with "Hcfg Htlbinv Hpc Hfile Hi62 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (E9 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
    assert (Hpp64 : add_vec_int (mword_of_int (WK + 0x62) : mword 64) 2 = mword_of_int (WK + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr).
    { rewrite /E8. rewrite lookup_total_insert_ne; [| reg_neq].
      exact HspE7. }
    assert (HspE9 : E9 !!! Regidx csp_rs1 = sp0).
    { rewrite /E9 lookup_total_insert. rewrite HspE8.
      unfold spr. apply walk_sp_cancel. }
    (* +0x64 ret *)
    assert (HE9ra : E9 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { peel_reg. }
    assert (Hrt : update_vec_dec (add_vec (E9 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = ret_tgt).
    { rewrite HE9ra.
      replace (sign_extend' 64 (zeros' 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite kv_addv_zero. reflexivity. }
    iApply (wp_cret_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x64)) (mword_of_int 1 : mword 5) E9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrt; exact (bit0_update0_64 (mm !!! Regidx (mword_of_int 1))))
              with "Hcfg Htlbinv Hpc Hfile Hi64 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite Hrt) in "Hpc".
    (* ---- rebundle the stack and conclude ---- *)
    iAssert (stack_own sp0 8)%I with "[Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Htop".
    { iEval (rewrite stack_own_slots; cbn [seq]).
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc08". }
      iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc00". }
      done. }
    iEval (rewrite -Hsprstk) in "Hdeep".
    iDestruct (stack_own_split_2 sp0 8 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! E9 tf with "Hcfg Htoken Htlbinv Hpc Hfile Hstk Hptree Henv [%] [%] [%]").
    { (* callee_saved mm E9 *)
      unfold callee_saved.
      split.
      { rewrite /E9 lookup_total_insert. rewrite HspE8.
        unfold spr. apply walk_sp_cancel. }
      split.
      { (* tp *)
        rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        exact Htp. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        peel_reg. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        peel_reg. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        peel_reg. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        peel_reg. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        peel_reg. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /E8.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. reflexivity. }
      split.
      { rewrite /E9. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /E8 lookup_total_insert. reflexivity. }
      (* s7..s11 *)
      repeat split;
        (rewrite /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1;
         repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
         first [ exact Hx23 | exact Hx24 | exact Hx25 | exact Hx26 | exact Hx27 ]). }
    { exact Hsame. }
    { (* the payload: a0 is untouched by the epilogue *)
      assert (HE9a0 : E9 !!! Regidx (mword_of_int 10 : mword 5)
                      = Mf !!! Regidx (mword_of_int 10 : mword 5)).
      { peel_reg. }
      rewrite HE9a0. exact Hpay. }
  Qed.

  (* ================================================================= *)
  (* THE SHARED TAIL (+0x46..+0x50): a0 := &level-0 slot, then the       *)
  (* epilogue.  All four success paths funnel here with s1 = the L0      *)
  (* node's page base [b0] and the level0 path fact.                     *)
  (* ================================================================= *)
  Lemma wp_walk_tail (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree) (b0 : mword 44) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    uint va < 274877906944 ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 19 : mword 5) = va ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12)) ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    (exists p2 p1 w0, ptree_level0 tf vpn p2 p1 w0
       /\ pt_addr0 p1 vpn = u_pte_addr b0 (vpn_idx 0 vpn)) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x46)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt Hn Hva' Hsp Hs3 Hs1 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hlvl.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hcont".
    iPoseProof (wi_46 with "Htext") as "Hi46".
    iPoseProof (wi_4a with "Htext") as "Hi4a".
    iPoseProof (wi_4e with "Htext") as "Hi4e".
    iPoseProof (wi_50 with "Htext") as "Hi50".
    (* +0x46 srli a0,s3,12 *)
    iApply (wp_srli4_s_scfg_r R γc Φ (mword_of_int (WK + 0x46)) (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              Mf (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi46 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (T1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_right (Mf !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> Mf).
    assert (Hpp4a : add_vec_int (mword_of_int (WK + 0x46) : mword 64) 4 = mword_of_int (WK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a andi a0,a0,511 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x4a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              T1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /T1 lookup_total_insert; rewrite Hs3; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi4a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> T1).
    assert (Hpp4e : add_vec_int (mword_of_int (WK + 0x4a) : mword 64) 4 = mword_of_int (WK + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.slli a0,3 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x4e)) (mword_of_int 10 : mword 5) (mword_of_int 3 : mword 6)
              (shift_bits_left
                 (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                          (sign_extend' 64 (mword_of_int 511 : mword 12)))
                 (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
              T2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /T2 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (T3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (shift_bits_left
           (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (mword_of_int 511 : mword 12)))
           (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> T2).
    assert (Hpp50 : add_vec_int (mword_of_int (WK + 0x4e) : mword 64) 2 = mword_of_int (WK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.add a0,s1 *)
    iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              T3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi50 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (T4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (T3 !!! Regidx (mword_of_int 10 : mword 5)) (T3 !!! Regidx (mword_of_int 9 : mword 5)))]> T3).
    assert (Hpp52 : add_vec_int (mword_of_int (WK + 0x50) : mword 64) 2 = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    assert (HT3s1 : T3 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12))).
    { rewrite /T3 /T2 /T1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      exact Hs1. }
    assert (HT4a0 : T4 !!! Regidx (mword_of_int 10 : mword 5)
                    = u_pte_addr b0 (vpn_idx 0 vpn)).
    { rewrite /T4 lookup_total_insert.
      rewrite {1}/T3 lookup_total_insert.
      rewrite HT3s1.
      replace (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
        with (subrange_vec_dec (mword_of_int 12 : mword 64) (Z.sub log2_xlen 1) 0)
        by (apply bv_eq; vm_compute; reflexivity).
      exact (walk_slot_addr0 b0 va Hva'). }
    (* funnel into the shared epilogue *)
    iApply (wp_walk_epilogue R Φ γ γc bsie mm T4 t tf n Hn
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hsp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Htp)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hx23)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hx24)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hx25)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hx26)
              ltac:(rewrite /T4 /T3 /T2 /T1;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    exact Hx27)
              Hsame
              ltac:(destruct Hlvl as (p2 & p1 & w0 & Hl0 & Heq);
                    right; exists p2, p1, w0; split;
                    [exact Hl0 | rewrite HT4a0 Heq; reflexivity])
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                    Hdeep Hptree Henv Hcont").
  Qed.

  (* ================================================================= *)
  (* THE SHARED ALLOCATION ARM (+0x72..+0x94): kalloc, memset(0), the    *)
  (* pointer-PTE store through the caller's GRAFT interface, and the     *)
  (* c.j rejoin -- or kalloc's null exit straight through the epilogue.  *)
  (* Used by arm 1 (twice: graft2 then graft1) and arm 2 (graft1).       *)
  (* ================================================================= *)
  Lemma wp_walk_alloc (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm Mf : gmap regidx (mword 64)) (t tf : ptree)
      (tG : mword 44 -> ptree) (clvl : nat)
      (cellA : mword 64) (w0 : bv 64) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 18 : mword 5) = cellA ->
    eq_vec (Mf !!! Regidx (mword_of_int 22 : mword 5)) zero_reg = false ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    ptree_same_rep0 t tf ->
    (ptree_own 2 (DfracOwn 1) tf ⊢
       cellA ↦₈ w0 ∗
       (∀ b : mword 44,
          cellA ↦₈ pt_ptr_pte b -∗
          ptree_own clvl (DfracOwn 1) (pt_empty_node b) -∗
          ptree_own 2 (DfracOwn 1) (tG b))) ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x72)) -∗
    gpr_file Mf -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    stack_own spr (n - 8) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (Mo : gmap regidx (mword 64)) (b : mword 44),
      ⌜forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
         Mo !!! Regidx c = Mf !!! Regidx c⌝ -∗
      ⌜Mo !!! Regidx (mword_of_int 9 : mword 5)
         = zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))⌝ -∗
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is (mword_of_int (WK + 0x40)) -∗
      gpr_file Mo -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
      pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
      pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
      pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
      pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
      stack_own spr (n - 8) -∗
      ptree_own 2 (DfracOwn 1) (tG b) -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
        sr_inv R -∗
        pc_is ret_tgt -∗
        gpr_file mr -∗ stack_own sp0 n -∗
        ptree_own 2 (DfracOwn 1) t' -∗
        kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜ptree_same_rep0 t t'⌝ -∗
        ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
          \/ (exists p2 p1 w1,
               ptree_level0 t' vpn p2 p1 w1 /\
               mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w1,
             ptree_level0 t' vpn p2 p1 w1 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 spr ret_tgt Hn Hsp Hs2c Hs6 Htp Hx23 Hx24 Hx25 Hx26 Hx27 Hsame Hacc.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hdeep Hptree Henv Hok Hcont".
    iPoseProof (wi_72 with "Htext") as "Hi72".
    iPoseProof (wi_76 with "Htext") as "Hi76".
    iPoseProof (wi_7a with "Htext") as "Hi7a".
    iPoseProof (wi_7c with "Htext") as "Hi7c".
    (* +0x72 beqz s6 FALLS (alloc = 1) *)
    iApply (wp_beqz_x0_fall_s_scfg_r R γc Φ (mword_of_int (WK + 0x72)) (mword_of_int 36 : mword 13) (mword_of_int 22 : mword 5)
              Mf (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) Hs6
              with "Hcfg Htlbinv Hpc Hfile Hi72 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp76 : add_vec_int (mword_of_int (WK + 0x72) : mword 64) 4 = mword_of_int (WK + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 jal kalloc *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (WK + 0x76)) (mword_of_int 1 : mword 5) (mword_of_int 2095964 : mword 21)
              Mf 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi76 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x76) : mword 64) 4)]> Mf).
    assert (Htgtk : add_vec (mword_of_int (WK + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 2095964 : mword 21)) = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    (* ---- kalloc() through the env bundle ---- *)
    iDestruct "Henv" as (qint qcpu) "(%Hqne & %H0ne & #Hlock & Hnoff & Hint & Hqcpu)".
    assert (HspJ : J !!! Regidx csp_rs1 = spr).
    { rewrite /J. rewrite lookup_total_insert_ne; [| reg_neq].
      exact Hsp. }
    iApply (wp_kalloc_r R Φ γ J qcpu (zeros' 32) qint
              (mycpu_ret (mm !!! Regidx (mword_of_int 4)))
              (mword_of_int (KernelSyms.kmem + 24)) γc bsie (n - 8)%nat
              ltac:(lia)
              ltac:(repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    rewrite Htp; exact Hqne)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              ltac:(reflexivity)
              ltac:(repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    rewrite Htp; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(replace (eq_vec (sign_extend' 64 (zeros' 32 : mword 32)) zero_reg) with true
                      by (vm_compute; reflexivity);
                    vm_compute; reflexivity)
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile [Hdeep] [Hnoff] [Hint] [Hlock] [Hqcpu] [-]").
    { iEval (rewrite HspJ). iExact "Hdeep". }
    { iExact "Hnoff". }
    { iExact "Hint". }
    { match goal with |- environments.envs_entails _ (is_lock _ ?a _) =>
        replace a with (mword_of_int KernelSyms.kmem : mword 64) end.
      2:{ rewrite lookup_total_insert_ne; [| reg_neq].
          rewrite lookup_total_insert.
          rewrite lookup_total_insert.
          apply bv_eq; vm_compute; reflexivity. }
      iExact "Hlock". }
    { match goal with |- environments.envs_entails _ (word_pointsto (add_vec ?a _) _ _) =>
        replace a with (mword_of_int KernelSyms.kmem : mword 64) end.
      2:{ rewrite lookup_total_insert_ne; [| reg_neq].
          rewrite lookup_total_insert.
          rewrite lookup_total_insert.
          apply bv_eq; vm_compute; reflexivity. }
      iExact "Hqcpu". }
    iIntros (mr) "Hcfg Htoken Htlbinv Hpc Hfile %Hkcs Hkpost Hstk Hqcpu Hnoff Hint".
    (* normalize the returned lock-cpu cell's address to the concrete kmem *)
    iEval (rewrite lookup_total_insert_ne; [| reg_neq];
           rewrite lookup_total_insert;
           rewrite lookup_total_insert;
           rewrite /regval_into_reg) in "Hqcpu".
    assert (Hqaddr : add_vec (add_vec (add_vec (mword_of_int (KernelSyms.kalloc + 10) : mword 64)
                        (auipc_off (mword_of_int 17 : mword 20)))
                        (sign_extend' 64 (mword_of_int 0x7f0 : mword 12)))
                        (sign_extend' 64 (mword_of_int 16 : mword 12))
                     = add_vec (mword_of_int KernelSyms.kmem : mword 64)
                        (sign_extend' 64 (mword_of_int 16 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hqaddr) in "Hqcpu".
    (* the return pc: +0x7a *)
    match goal with |- context [pc_is ?tgt] => idtac end.
    assert (Hret7a : update_vec_dec (add_vec (J !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x7a)).
    { rewrite /J lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7a) in "Hpc".
    (* +0x7a c.mv s1,a0 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x7a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi7a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5)))]> mr).
    assert (Hpp7c : add_vec_int (mword_of_int (WK + 0x7a) : mword 64) 2 = mword_of_int (WK + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* the kalloc-env repack (both branches restore the quiescent state) *)
    assert (Hqnr : (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (sign_extend' 64 ((autocast (T := mword) (subrange_vec_dec
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (sign_extend' 64 (zeros' 32 : mword 32))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
              (Z.sub (Z.mul 4 8) 0x1) 0) : mword 32)))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 0x1) 0) : mword 32) = (zeros' 32 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    iAssert (kalloc_env γ (mm !!! Regidx (mword_of_int 4)))
      with "[Hqcpu Hnoff Hint]" as "Henv".
    { iExists (if eq_vec (sign_extend' 64 (zeros' 32 : mword 32)) zero_reg
               then (zeros' 32 : mword 32) else qint), (zero_reg : mword 64).
      iSplitR. { iPureIntro. exact H0ne. }
      iSplitR. { iPureIntro. exact H0ne. }
      iFrame "Hlock".
      iSplitL "Hnoff".
      { iEval (rewrite Hqnr) in "Hnoff". iExact "Hnoff". }
      iSplitL "Hint". { iExact "Hint". }
      iExact "Hqcpu". }
    (* +0x7c c.beqz a0: the null/success split *)
    iDestruct "Hkpost" as "[%Hnull | [%Hpv Hpage]]".
    { (* ---- NULL: exit through the epilogue with a0 = 0 ---- *)
      assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
      { rewrite /N1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                N1 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HN1a0 Hnull; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi7c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt52 : add_vec (mword_of_int (WK + 0x7c) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 235 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt52) in "Hpc".
      iEval (rewrite HspJ) in "Hstk".
      iApply (wp_walk_epilogue R Φ γ γc bsie mm N1 t tf n Hn
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                                 ltac:(vm_compute; reflexivity));
                      exact HspJ)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 4)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Htp)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 23)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hx23)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 24)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hx24)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 25)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hx25)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 26)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hx26)
                ltac:(rewrite /N1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (callee_saved_lookup Hkcs (mword_of_int 27)
                                 ltac:(vm_compute; reflexivity));
                      rewrite /J; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hx27)
                Hsame
                ltac:(left; rewrite HN1a0 Hnull; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hstk Hptree Henv Hcont"). }
    (* ---- SUCCESS: page p, memset(0), graft, store, rejoin ---- *)
    iPoseProof (wi_7e with "Htext") as "Hi7e".
    iPoseProof (wi_80 with "Htext") as "Hi80".
    iPoseProof (wi_82 with "Htext") as "Hi82".
    iPoseProof (wi_86 with "Htext") as "Hi86".
    iPoseProof (wi_8a with "Htext") as "Hi8a".
    iPoseProof (wi_8c with "Htext") as "Hi8c".
    iPoseProof (wi_90 with "Htext") as "Hi90".
    iPoseProof (wi_94 with "Htext") as "Hi94".
    assert (HN1a0 : N1 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /N1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    (* the allocated page's bounds and its ppn *)
    pose proof Hpv as Hpv'.
    destruct Hpv' as [Hal Hrange]. unfold page_in_range, kmem_lo, kmem_hi in Hrange.
    unfold page_aligned, PGSIZE in Hal.
    assert (Hlt56 : uint (mr !!! Regidx (mword_of_int 10 : mword 5)) < 72057594037927936) by lia.
    set (bppn := (autocast (T := mword) (subrange_vec_dec (mr !!! Regidx (mword_of_int 10 : mword 5)) 55 12) : mword 44)).
    assert (Hpb : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))
                  = mr !!! Regidx (mword_of_int 10 : mword 5))
      by (exact (walk_alloc_page_base _ Hal Hlt56)).
    (* +0x7c c.beqz a0 FALLS (p <> 0) *)
    iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x7c)) (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              N1 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HN1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hcfg Htlbinv Hpc Hfile Hi7c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp7e : add_vec_int (mword_of_int (WK + 0x7c) : mword 64) 2 = mword_of_int (WK + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.lui a2,1 *)
    iApply (wp_clui_s_r R γc Φ (mword_of_int (WK + 0x7e)) (mword_of_int 12 : mword 5)
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              N1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi7e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> N1).
    assert (Hpp80 : add_vec_int (mword_of_int (WK + 0x7e) : mword 64) 2 = mword_of_int (WK + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.li a1,0 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x80)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              N2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi80 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> N2).
    assert (Hpp82 : add_vec_int (mword_of_int (WK + 0x80) : mword 64) 2 = mword_of_int (WK + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    (* +0x82 jal memset *)
    iApply (wp_jal_gpr_s_zca_r R γc Φ (mword_of_int (WK + 0x82)) (mword_of_int 1 : mword 5) (mword_of_int 2096362 : mword 21)
              N3 1%Qp
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi82 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (N4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (WK + 0x82) : mword 64) 4)]> N3).
    assert (Htgtm : add_vec (mword_of_int (WK + 0x82) : mword 64) (sign_extend' 64 (mword_of_int 2096362 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(p, 0, 4096) keeping the zero bytes *)
    assert (HN4a0 : N4 !!! Regidx (mword_of_int 10 : mword 5) = mr !!! Regidx (mword_of_int 10 : mword 5)).
    { peel_reg. }
    iApply (wp_memset_page_zero_r R Φ N4 (mword_of_int 0 : mword 64) (n - 8)%nat γc (dq:=DfracOwn 1)
              ltac:(lia)
              ltac:(rewrite HN4a0; exact Hpv)
              ltac:(rewrite /N4; rewrite lookup_total_insert_ne; [| reg_neq];
                    rewrite /N3 lookup_total_insert; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /N4 /N3;
                    repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                    rewrite lookup_total_insert; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile [Hstk] [Hpage] [-]").
    { iEval (rewrite HspJ) in "Hstk".
      match goal with |- environments.envs_entails _ (stack_own ?a _) =>
        replace a with spr end.
      2:{ symmetry. rewrite /N4 /N3 /N2 /N1.
          repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
          rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                     ltac:(vm_compute; reflexivity)).
          exact HspJ. }
      iExact "Hstk". }
    { iEval (rewrite HN4a0). iExact "Hpage". }
    iIntros (mfin) "Hcfg Htlbinv Hpc Hstk Hbytes Hfile %Hmcs".
    assert (Hret86 : update_vec_dec (add_vec (N4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0" : mword 1) = mword_of_int (WK + 0x86)).
    { rewrite /N4 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret86) in "Hpc".
    (* the zero page as a description node *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (mword_of_int 0 : mword 64) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb HN4a0 -Hpb) in "Hbytes".
    iDestruct (zero_page_to_node clvl (DfracOwn 1) bppn with "Hbytes") as "Hchild".
    (* +0x86 srli a5,s1,12 *)
    assert (Hmfs1 : mfin !!! Regidx (mword_of_int 9 : mword 5)
                    = add_vec zero_reg (mr !!! Regidx (mword_of_int 10 : mword 5))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite /N1 lookup_total_insert. reflexivity. }
    iApply (wp_srli4_s_scfg_r R γc Φ (mword_of_int (WK + 0x86)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
              mfin (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi86 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (mfin !!! Regidx (mword_of_int 9 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> mfin).
    assert (Hpp8a : add_vec_int (mword_of_int (WK + 0x86) : mword 64) 4 = mword_of_int (WK + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* +0x8a c.slli a5,10 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x8a)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 6)
              (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
              P1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi8a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (P1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> P1).
    assert (Hpp8c : add_vec_int (mword_of_int (WK + 0x8a) : mword 64) 2 = mword_of_int (WK + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* +0x8c ori a5,a5,1 *)
    iApply (wp_ori_s_r R γc Φ (mword_of_int (WK + 0x8c)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 12)
              (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
              P2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi8c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (or_vec (P2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> P2).
    assert (Hpp90 : add_vec_int (mword_of_int (WK + 0x8c) : mword 64) 4 = mword_of_int (WK + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp90) in "Hpc".
    assert (HP3a5 : P3 !!! Regidx (mword_of_int 15 : mword 5) = pt_ptr_pte bppn).
    { rewrite /P3 lookup_total_insert.
      rewrite {1}/P2 lookup_total_insert.
      rewrite {1}/P1 lookup_total_insert.
      rewrite Hmfs1 add_vec_zero_l.
      exact (walk_alloc_pte _ Hal Hlt56). }
    (* +0x90 sd a5,0(s2): the pointer-PTE store through the graft cell *)
    assert (HP3s2 : P3 !!! Regidx (mword_of_int 18 : mword 5) = cellA).
    { rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite (callee_saved_lookup Hmcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /N4 /N3 /N2 /N1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite (callee_saved_lookup Hkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /J. rewrite lookup_total_insert_ne; [| reg_neq].
      exact Hs2c. }
    assert (Hea0' : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iDestruct (Hacc with "Hptree") as "[Hcell Hgw]".
    iApply (wp_sd_s_scfg_r R γc Φ (mword_of_int (WK + 0x90)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              P3 w0 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi90 [Hcell] [-]").
    { iEval (rewrite Hea0' HP3s2). iExact "Hcell". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcell".
    iEval (rewrite Hea0' HP3s2 HP3a5) in "Hcell".
    iDestruct ("Hgw" $! bppn with "Hcell Hchild") as "Hptree".
    assert (Hpp94 : add_vec_int (mword_of_int (WK + 0x90) : mword 64) 4 = mword_of_int (WK + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* +0x94 c.j back to the loop decrement at +0x40 *)
    iApply (wp_cj_s_scfg_r R γc Φ (mword_of_int (WK + 0x94))
              (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")))
              P3 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi94 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Htgt40 : add_vec (mword_of_int (WK + 0x94) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0"))))
            = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt40) in "Hpc".
    (* hand off to the success continuation *)
    iApply ("Hok" $! P3 bppn with "[%] [%] Hcfg Htoken Htlbinv Hpc Hfile
            Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 [Hstk] Hptree Henv Hcont").
    { (* the callee-saved-except-s1 transport back to Mf *)
      intros c Hcs Hc9.
      rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite (callee_saved_lookup Hmcs c Hcs).
      rewrite /N4 /N3 /N2.
      repeat (rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate]).
      rewrite /N1.
      rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; exact (Hc9 (eq_sym Habs2))].
      rewrite (callee_saved_lookup Hkcs c Hcs).
      rewrite /J.
      rewrite lookup_total_insert_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hcs; discriminate].
      reflexivity. }
    { (* s1 = the new page's base *)
      rewrite /P3 /P2 /P1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite Hmfs1 add_vec_zero_l.
      symmetry. exact Hpb. }
    { (* the deep stack, back at spr *)
      match goal with |- environments.envs_entails _ (stack_own ?a _) => idtac end.
      iEval (rewrite /N4 /N3 /N2 /N1;
             repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
             rewrite (callee_saved_lookup Hkcs (csp_rs1 : mword 5)
                        ltac:(vm_compute; reflexivity));
             rewrite HspJ) in "Hstk".
      iExact "Hstk". }
  Qed.

  (* ================================================================= *)
  (* THE LOOP BODY'S STRAIGHT-LINE CORE (+0x26..+0x36): compute the slot *)
  (* address s2 = &node[PX(lvl,va)], load the PTE into s1, and extract   *)
  (* its valid bit into a5 -- i.e. the C `pte = &pt[PX(level,va)]` and    *)
  (* the `*pte & PTE_V` test operand.  The machine code here is a single  *)
  (* physical loop body (the +0x42 bne branches back to +0x26); the walk  *)
  (* proof unrolls it per level and per control-flow path.  Factoring the  *)
  (* single-exit straight-line prefix into ONE Qed-sealed lemma proves    *)
  (* these six instructions ONCE instead of ~5 times.  The caller then    *)
  (* runs the +0x3a beqz (valid -> descend/bne, zero -> alloc), which is   *)
  (* the genuinely level/outcome-dependent loop control.  Level-agnostic:  *)
  (* the caller supplies the slot-address equation (walk_slot_addr2/1) and  *)
  (* the slot's byte ownership at u_pte_addr.  s2's four writes collapse    *)
  (* to one insert (insert_insert), so the returned map is 3 inserts deep. *)
  (* ================================================================= *)
  Lemma wp_walk_probe (R : s_regime) (Φ : mval -> iProp Σ) (γc : gname)
      (M : gmap regidx (mword 64)) (va shift : mword 64) (slotaddr pte : mword 64) {dq dqm : dfrac} :
    M !!! Regidx (mword_of_int 19 : mword 5) = va ->
    M !!! Regidx (mword_of_int 20 : mword 5) = shift ->
    add_vec
      (shift_bits_left
         (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                  (sign_extend' 64 (mword_of_int 511 : mword 12)))
         (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
      (M !!! Regidx (mword_of_int 9 : mword 5)) = slotaddr ->
    smode_config γc dq -∗ sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int (WK + 0x26)) -∗ gpr_file M -∗
    slotaddr ↦₈{dqm} pte -∗
    ( smode_config γc dq -∗ sr_inv R -∗
      pc_is (mword_of_int (WK + 0x3a)) -∗
      gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))]>
                (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]>
                 (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M))) -∗
      slotaddr ↦₈{dqm} pte -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hs3 Hs4 Hslot.
    iIntros "Hcfg Htlbinv #Htext Hpc Hfile Hown Hcont".
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_r R γc Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
              M (dq:=dq)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3 Hs4; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))]> M).
    assert (Hpp2a : add_vec_int (mword_of_int (WK + 0x26) : mword 64) 4 = mword_of_int (WK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 (dq:=dq)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L1 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    assert (Hpp2e : add_vec_int (mword_of_int (WK + 0x2a) : mword 64) 4 = mword_of_int (WK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x2e)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              (shift_bits_left
                 (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                          (sign_extend' 64 (mword_of_int 511 : mword 12)))
                 (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
              L2 (dq:=dq)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L2 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left
           (and_vec (shift_bits_right va (subrange_vec_dec shift (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (mword_of_int 511 : mword 12)))
           (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    assert (Hpp30 : add_vec_int (mword_of_int (WK + 0x2e) : mword 64) 2 = mword_of_int (WK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 (dq:=dq)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp32 : add_vec_int (mword_of_int (WK + 0x30) : mword 64) 2 = mword_of_int (WK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* collapse s2's four writes (L1..L4, all reg18) to ONE insert over M *)
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg slotaddr]> M).
    assert (HL4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3 = L4).
    { rewrite /L4 /L3 /L2 /L1 !insert_insert. do 2 f_equal.
      rewrite lookup_total_insert.
      rewrite lookup_total_insert_ne; [| reg_neq].
      exact Hslot. }
    iEval (rewrite HL4c) in "Hfile".
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5) = slotaddr)
      by (rewrite /L4 lookup_total_insert; reflexivity).
    (* the [sext 0] effective-address collapse for the ld at 0(s2) *)
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x32 ld s1,0(s2) *)
    iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
              L4 pte (dq:=dq) (dqm:=dqm)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi32 [Hown] [-]").
    { iEval (rewrite Hea0 HL4s2). iExact "Hown". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hown".
    iEval (rewrite Hea0 HL4s2) in "Hown".
    set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg pte]> L4).
    assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 andi a5,s1,1 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
              (and_vec pte (sign_extend' 64 (mword_of_int 1 : mword 12)))
              L5 (dq:=dq)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L5 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    iApply ("Hcont" with "Hcfg Htlbinv Hpc Hfile Hown").
  Qed.



  Lemma wp_walk_r (R : s_regime) (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (bsie : mword 1)
      (mm : gmap regidx (mword 64)) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (n : nat) :
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn := svpn_of va in
    let sp0 := mm !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
    (22 <= n)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    mm !!! Regidx (mword_of_int 12) = mword_of_int 1 ->
    (uint va < 2 ^ 38)%Z ->
    pt_rep0 t m ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
    sr_inv R -∗ kernel_text -∗
    pc_is (mword_of_int WK) -∗
    gpr_file mm -∗ stack_own sp0 n -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (mr : gmap regidx (mword 64)) (t' : ptree),
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗ stack_own sp0 n -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜ptree_same_rep0 t t'⌝ -∗
      ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
        \/ (exists p2 p1 w0,
             ptree_level0 t' vpn p2 p1 w0 /\
             mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros va vpn sp0 ret_tgt Hn Ha0 Ha2 Hva Hrep.
    (* the entry map after the prologue: W1 (sp) .. W9 (s5) *)
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile Hstk Hptree Henv Hcont".
    (* ---- peel walk's own 8-slot frame [spr, sp0) ---- *)
    iDestruct (stack_own_split_1 sp0 8 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v56) "Hc56". iDestruct "S2" as (v48) "Hc48".
    iDestruct "S3" as (v40) "Hc40". iDestruct "S4" as (v32) "Hc32".
    iDestruct "S5" as (v24) "Hc24". iDestruct "S6" as (v16) "Hc16".
    iDestruct "S7" as (v08) "Hc08". iDestruct "S8" as (v00) "Hc00".
    (* slot-address bridges: spr + 8u = pa_stk sp0 (8-u) *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hsprstk) in "Hdeep".
    (* the catalog facts for the prologue *)
    iPoseProof (wi_00 with "Htext") as "Hi00".
    iPoseProof (wi_02 with "Htext") as "Hi02".
    iPoseProof (wi_04 with "Htext") as "Hi04".
    iPoseProof (wi_06 with "Htext") as "Hi06".
    iPoseProof (wi_08 with "Htext") as "Hi08".
    iPoseProof (wi_0a with "Htext") as "Hi0a".
    iPoseProof (wi_0c with "Htext") as "Hi0c".
    iPoseProof (wi_0e with "Htext") as "Hi0e".
    iPoseProof (wi_10 with "Htext") as "Hi10".
    iPoseProof (wi_12 with "Htext") as "Hi12".
    iPoseProof (wi_14 with "Htext") as "Hi14".
    iPoseProof (wi_16 with "Htext") as "Hi16".
    iPoseProof (wi_18 with "Htext") as "Hi18".
    iPoseProof (wi_1a with "Htext") as "Hi1a".
    iPoseProof (wi_1c with "Htext") as "Hi1c".
    iPoseProof (wi_1e with "Htext") as "Hi1e".
    iPoseProof (wi_20 with "Htext") as "Hi20".
    iPoseProof (wi_22 with "Htext") as "Hi22".
    (* +0x00 c.addi16sp sp,-64 *)
    iApply (wp_caddi16sp_gpr_s_r R γc Φ (mword_of_int WK) (mword_of_int 60 : mword 6) mm 1%Qp
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1; rewrite lookup_total_insert; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int WK : mword 64) 2 = mword_of_int (WK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp x1,56(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              W1 v56 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc56". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc56".
    assert (Hpp04 : add_vec_int (mword_of_int (WK + 0x02) : mword 64) 2 = mword_of_int (WK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp x8,48(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              W1 v48 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc48". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc48".
    assert (Hpp06 : add_vec_int (mword_of_int (WK + 0x04) : mword 64) 2 = mword_of_int (WK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp x9,40(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              W1 v40 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi06 [Hc40] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc40". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc40".
    assert (Hpp08 : add_vec_int (mword_of_int (WK + 0x06) : mword 64) 2 = mword_of_int (WK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp x18,32(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              W1 v32 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [Hc32] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc32". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc32".
    assert (Hpp0a : add_vec_int (mword_of_int (WK + 0x08) : mword 64) 2 = mword_of_int (WK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp x19,24(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              W1 v24 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [Hc24] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc24".
    assert (Hpp0c : add_vec_int (mword_of_int (WK + 0x0a) : mword 64) 2 = mword_of_int (WK + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp x20,16(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              W1 v16 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [Hc16] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc16".
    assert (Hpp0e : add_vec_int (mword_of_int (WK + 0x0c) : mword 64) 2 = mword_of_int (WK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp x21,8(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              W1 v08 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi0e [Hc08] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc08". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc08".
    assert (Hpp10 : add_vec_int (mword_of_int (WK + 0x0e) : mword 64) 2 = mword_of_int (WK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.sdsp x22,0(sp) *)
    iApply (wp_csdsp_gpr_s_scfg_r R γc Φ (mword_of_int (WK + 0x10)) (mword_of_int 0 : mword 6) (mword_of_int 22 : mword 5)
              W1 v00 (dq:=DfracOwn 1)
              with "Hcfg Htlbinv Hpc Hfile Hi10 [Hc00] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc00". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hc00".
    assert (Hpp12 : add_vec_int (mword_of_int (WK + 0x10) : mword 64) 2 = mword_of_int (WK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              W1 (dq:=DfracOwn 1)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> W1).
    assert (Hpp14 : add_vec_int (mword_of_int (WK + 0x12) : mword 64) 2 = mword_of_int (WK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.mv x9,x10 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              W2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hpp16 : add_vec_int (mword_of_int (WK + 0x14) : mword 64) 2 = mword_of_int (WK + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.mv x19,x11 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x16)) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              W3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W4 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (W3 !!! Regidx (mword_of_int 11 : mword 5)))]> W3).
    assert (Hpp18 : add_vec_int (mword_of_int (WK + 0x16) : mword 64) 2 = mword_of_int (WK + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.mv x22,x12 *)
    iApply (wp_cmv_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x18)) (mword_of_int 22 : mword 5) (mword_of_int 12 : mword 5)
              W4 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W5 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg
        (add_vec zero_reg (W4 !!! Regidx (mword_of_int 12 : mword 5)))]> W4).
    assert (Hpp1a : add_vec_int (mword_of_int (WK + 0x18) : mword 64) 2 = mword_of_int (WK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.li a5,-1 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              W5 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> W5).
    assert (Hpp1c : add_vec_int (mword_of_int (WK + 0x1a) : mword 64) 2 = mword_of_int (WK + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.srli a5,26 *)
    iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 26 : mword 6)
              (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))
              W6 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi1c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (W6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0))]> W6).
    assert (Hpp1e : add_vec_int (mword_of_int (WK + 0x1c) : mword 64) 2 = mword_of_int (WK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s4,30 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 30 : mword 6)
              W7 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W8 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 30 : mword 6))))]> W7).
    assert (Hpp20 : add_vec_int (mword_of_int (WK + 0x1e) : mword 64) 2 = mword_of_int (WK + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.li s5,12 *)
    iApply (wp_cli_gpr_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x20)) (mword_of_int 21 : mword 5) (mword_of_int 12 : mword 6)
              W8 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi20 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (W9 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> W8).
    assert (Hpp22 : add_vec_int (mword_of_int (WK + 0x20) : mword 64) 2 = mword_of_int (WK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* the register-value facts the loop needs *)
    assert (Hva' : uint va < 274877906944) by (change 274877906944 with (2 ^ 38); exact Hva).
    assert (HW9va : W9 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { peel_reg. }
    assert (HW6a5 : W6 !!! Regidx (mword_of_int 15 : mword 5)
                    = (mword_of_int 18446744073709551615 : mword 64)).
    { rewrite /W6 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9a5 : W9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 274877906943).
    { rewrite /W9 /W8.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite /W7 lookup_total_insert. rewrite HW6a5.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x22 bltu a5,a1 FALLS: va <= MAXVA-1 *)
    iApply (wp_bltu_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x22)) (mword_of_int 68 : mword 13) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9a5 HW9va; unfold zopz0zI_u; apply Z.ltb_ge;
                    replace (uint (mword_of_int 274877906943 : mword 64)) with 274877906943 by (vm_compute; reflexivity);
                    lia)
              with "Hcfg Htlbinv Hpc Hfile Hi22 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp26 : add_vec_int (mword_of_int (WK + 0x22) : mword 64) 4 = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ================= LOOP ITERATION 1 (s4 = 30, level 2) ============ *)
    iPoseProof (wi_26 with "Htext") as "Hi26".
    iPoseProof (wi_2a with "Htext") as "Hi2a".
    iPoseProof (wi_2e with "Htext") as "Hi2e".
    iPoseProof (wi_30 with "Htext") as "Hi30".
    iPoseProof (wi_32 with "Htext") as "Hi32".
    iPoseProof (wi_36 with "Htext") as "Hi36".
    iPoseProof (wi_3a with "Htext") as "Hi3a".
    assert (HW9s3 : W9 !!! Regidx (mword_of_int 19 : mword 5) = va).
    { rewrite /W9 /W8 /W7 /W6 /W5.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite /W4 lookup_total_insert.
      rewrite /W3 /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite add_vec_zero_l. reflexivity. }
    assert (HW9s4 : W9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
    { rewrite /W9. rewrite lookup_total_insert_ne; [| reg_neq].
      rewrite /W8 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HW9s1 : W9 !!! Regidx (mword_of_int 9 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W9 /W8 /W7 /W6 /W5 /W4.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite /W3 lookup_total_insert.
      rewrite /W2 /W1.
      repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
      rewrite add_vec_zero_l. rewrite Ha0. reflexivity. }
    (* PC-advance facts for the +0x26..+0x32 block, shared by the (still-inline)
       level-1 and alloc slot blocks downstream *)
    assert (Hpp2a : add_vec_int (mword_of_int (WK + 0x26) : mword 64) 4 = mword_of_int (WK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp2e : add_vec_int (mword_of_int (WK + 0x2a) : mword 64) 4 = mword_of_int (WK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp30 : add_vec_int (mword_of_int (WK + 0x2e) : mword 64) 2 = mword_of_int (WK + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpp32 : add_vec_int (mword_of_int (WK + 0x30) : mword 64) 2 = mword_of_int (WK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    (* +0x26 srl s2,s3,s4 *)
    iApply (wp_srl_s_r R γc Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
              (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
              W9 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HW9s3 HW9s4; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))]> W9).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a andi s2,s2,511 *)
    iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
              (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                       (sign_extend' 64 (mword_of_int 511 : mword 12)))
              L1 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L1 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (mword_of_int 511 : mword 12)))]> L1).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.slli s2,3 *)
    iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x2e)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
              (shift_bits_left
                 (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                          (sign_extend' 64 (mword_of_int 511 : mword 12)))
                 (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
              L2 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /L2 lookup_total_insert; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (L3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (shift_bits_left
           (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 30 : mword 64) (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (mword_of_int 511 : mword 12)))
           (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> L2).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.add s2,s1 *)
    iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
              L3 (dq:=DfracOwn 1)
              ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite Hpp32) in "Hpc".
    (* s2's four writes (L1..L4, all reg18) collapse to ONE insert over W9 *)
    set (L4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (u_pte_addr (pt_base t) (vpn_idx 2 vpn))]> W9).
    assert (HL4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec (L3 !!! Regidx (mword_of_int 18 : mword 5)) (L3 !!! Regidx (mword_of_int 9 : mword 5)))]> L3 = L4).
    { rewrite /L4 /L3 /L2 /L1 !insert_insert. do 2 f_equal.
      rewrite lookup_total_insert.
      rewrite lookup_total_insert_ne; [| reg_neq].
      rewrite HW9s1; exact (walk_slot_addr2 (pt_base t) va Hva'). }
    iEval (rewrite HL4c) in "Hfile".
    assert (HL4s2 : L4 !!! Regidx (mword_of_int 18 : mword 5)
                    = u_pte_addr (pt_base t) (vpn_idx 2 vpn))
      by (rewrite /L4 lookup_total_insert; reflexivity).
    (* the [sext 0] effective-address collapse for the ld/sd at 0(s2) *)
    assert (Hea0 : forall X : mword 64, add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* ---- +0x32 ld s1,0(s2): the slot read; [pt_rep0]'s totality drives
       the V-bit branch ---- *)
    destruct (m !! vpn) as [w|] eqn:Hmv.
    - (* ============ MAPPED vpn: descend, descend ============ *)
      destruct (proj1 Hrep vpn w Hmv) as (p2 & p1 & Hmaps).
      pose proof Hmaps as (c1 & c0 & Hk2 & Hk1 & He2 & He1 & He0 & Hch2 & Hch1 &
                           Hv2 & Hp2c & Hv1 & Hp1c & Hv0 & Hl0c & Hnap0 & Hpb0).
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (pt_ents t (vpn_idx 2 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: the mapped root slot has V = 1 *)
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - rewrite He2. exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: the DESCEND -- s1 := (w >> 10) << 12 *)
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /L5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                L7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* the descended base: s1 = the level-1 node's page base *)
      assert (Hb1c : u_next_base (pt_ents t (vpn_idx 2 vpn)) = pt_base c1)
        by (rewrite He2; exact Hch2).
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn))
                   ltac:(rewrite He2; exact Hv2) ltac:(rewrite He2; exact Hp2c)).
        rewrite Hb1c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 lookup_total_insert. rewrite HL8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite lookup_total_insert_ne; [| reg_neq]. exact HL8s1. }
      (* ---- factored straight-line body (+0x26..+0x36) via wp_walk_probe ---- *)
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe R Φ γc L9 va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hcfg Htlbinv Htext Hpc Hfile Hslot1 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 lookup_total_insert; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      (* +0x3a c.beqz a5 FALLS: the mapped L1 slot has V = 1 *)
      assert (Hvbit1 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents c1 (vpn_idx 1 vpn))).
        - rewrite He1. exact Hv1.
        - exact (pte_invalid_bit0 _ E). }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: descend to the level-0 node *)
      assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents c1 (vpn_idx 1 vpn)).
      { rewrite /M6. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /M5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                M7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      iEval (rewrite Hpp40) in "Hpc".
      assert (Hb0c : u_next_base (pt_ents c1 (vpn_idx 1 vpn)) = pt_base c0)
        by (rewrite He1; exact Hch1).
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents c1 (vpn_idx 1 vpn))
                   ltac:(rewrite He1; exact Hv1) ltac:(rewrite He1; exact Hp1c)).
        rewrite Hb0c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 lookup_total_insert. rewrite HM8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                M9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* ---- funnel into the shared tail with b0 := pt_base c0 ---- *)
      assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
      { peel_reg. }
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M9. rewrite lookup_total_insert_ne; [| reg_neq].
        exact HM8s1. }
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      unshelve iApply (wp_walk_tail R Φ γ γc bsie mm M9 t t (pt_base c0) n Hn Hva'
                HspM9 HM9s3 HM9s1
                _ _ _ _ _ _
                (ptree_same_rep0_refl t)
                _
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv Hcont").
      all: first
        [ peel_reg
        | (exists p2, p1, w; split;
           [exact (ptree_maps_level0 t vpn p2 p1 w Hmaps)
           | unfold pt_addr0; rewrite Hch1; reflexivity]) ].
    - (* ============ UNMAPPED vpn: the blocks0 dichotomy ============ *)
      pose proof (proj2 Hrep vpn Hmv) as Hblk.
      destruct Hblk as [ (Hk2n & He2z)
                       | [ (c1 & Hk2 & Hk1 & Hv2 & Hp2c & Hch2 & He1z)
                         | (c1 & c0 & Hk2 & Hk1 & Hv2 & Hp2c & Hv1 & Hp1c & Hch2 & Hch1 & He0z) ] ].
      3:{ (* ---- arm 3: descend, descend, zero L0 word ---- *)
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (pt_ents t (vpn_idx 2 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: the mapped root slot has V = 1 *)
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: the DESCEND -- s1 := (w >> 10) << 12 *)
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /L5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                L7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* the descended base: s1 = the level-1 node's page base *)
      pose proof Hch2 as Hb1c.
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn)) Hv2 Hp2c).
        rewrite Hb1c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 lookup_total_insert. rewrite HL8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite lookup_total_insert_ne; [| reg_neq]. exact HL8s1. }
      (* ---- factored straight-line body (+0x26..+0x36) via wp_walk_probe ---- *)
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe R Φ γc L9 va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hcfg Htlbinv Htext Hpc Hfile Hslot1 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 lookup_total_insert; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      (* +0x3a c.beqz a5 FALLS: the mapped L1 slot has V = 1 *)
      assert (Hvbit1 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents c1 (vpn_idx 1 vpn))).
        - exact Hv1.
        - exact (pte_invalid_bit0 _ E). }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: descend to the level-0 node *)
      assert (HM6s1 : M6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents c1 (vpn_idx 1 vpn)).
      { rewrite /M6. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /M5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> M6).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                M7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /M7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents c1 (vpn_idx 1 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
      iEval (rewrite Hpp40) in "Hpc".
      pose proof Hch1 as Hb0c.
      assert (HM8s1 : M8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents c1 (vpn_idx 1 vpn)) Hv1 Hp1c).
        rewrite Hb0c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                M8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (M9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (M8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> M8).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HM8s4 : M8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HM9s4 : M9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 lookup_total_insert. rewrite HM8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HM9s5 : M9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                M9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HM9s4 HM9s5; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* ---- funnel into the shared tail with b0 := pt_base c0 ---- *)
      assert (HspM9 : M9 !!! Regidx csp_rs1 = spr).
      { peel_reg. }
      assert (HM9s3 : M9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /M9 /M8 /M7 /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c0) (zeros' 12 : mword 12))).
      { rewrite /M9. rewrite lookup_total_insert_ne; [| reg_neq].
        exact HM8s1. }
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      unshelve iApply (wp_walk_tail R Φ γ γc bsie mm M9 t t (pt_base c0) n Hn Hva'
                HspM9 HM9s3 HM9s1
                _ _ _ _ _ _
                (ptree_same_rep0_refl t)
                _
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv Hcont").
      all: first
        [ peel_reg
        | (pose proof (ptree_level0_intro t c1 c0 vpn Hk2 Hk1 Hv2 Hp2c Hv1 Hp1c Hch2 Hch1) as Hl0;
           rewrite He0z in Hl0;
           eexists _, _, _; split;
           [exact Hl0 | unfold pt_addr0; rewrite Hch1; reflexivity]) ].
      }
      2:{ (* ---- arm 2: descend, then ALLOCATE at level 1 ---- *)
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (pt_ents t (vpn_idx 2 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 andi a5,s1,1 *)
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 FALLS: the mapped root slot has V = 1 *)
      assert (Hvbit2 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = true).
      { destruct (Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0) eqn:E;
          [reflexivity | exfalso].
        apply (pte_valid_invalid_excl (pt_ents t (vpn_idx 2 vpn))).
        - exact Hv2.
        - exact (pte_invalid_bit0 _ E). }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit2; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp3c : add_vec_int (mword_of_int (WK + 0x3a) : mword 64) 2 = mword_of_int (WK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c / +0x3e: the DESCEND -- s1 := (w >> 10) << 12 *)
      iPoseProof (wi_3c with "Htext") as "Hi3c".
      iPoseProof (wi_3e with "Htext") as "Hi3e".
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      assert (HL6s1 : L6 !!! Regidx (mword_of_int 9 : mword 5) = pt_ents t (vpn_idx 2 vpn)).
      { rewrite /L6. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite /L5 lookup_total_insert. reflexivity. }
      iApply (wp_csrli_s_r R γc Φ (mword_of_int (WK + 0x3c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 6)
                (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6s1; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> L6).
      assert (Hpp3e : add_vec_int (mword_of_int (WK + 0x3c) : mword 64) 2 = mword_of_int (WK + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x3e)) (mword_of_int 9 : mword 5) (mword_of_int 12 : mword 6)
                (shift_bits_left
                   (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
                L7 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L7 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
          (shift_bits_left
             (shift_bits_right (pt_ents t (vpn_idx 2 vpn)) (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))
             (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> L7).
      assert (Hpp40 : add_vec_int (mword_of_int (WK + 0x3e) : mword 64) 2 = mword_of_int (WK + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* the descended base: s1 = the level-1 node's page base *)
      pose proof Hch2 as Hb1c.
      assert (HL8s1 : L8 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L8 lookup_total_insert.
        rewrite (walk_descend_base (pt_ents t (vpn_idx 2 vpn)) Hv2 Hp2c).
        rewrite Hb1c. reflexivity. }
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                L8 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L9 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (L8 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> L8).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HL8s4 : L8 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /L8 /L7 /L6 /L5 /L4 /W9.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s4 : L9 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /L9 lookup_total_insert. rewrite HL8s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HL9s5 : L9 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                L9 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HL9s4 HL9s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ================= LOOP ITERATION 2 (s4 = 21, level 1) ============ *)
      assert (HL9s3 : L9 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      assert (HL9s1 : L9 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec (pt_base c1) (zeros' 12 : mword 12))).
      { rewrite /L9. rewrite lookup_total_insert_ne; [| reg_neq]. exact HL8s1. }
      (* ---- factored straight-line body (+0x26..+0x36) via wp_walk_probe ---- *)
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) t c1 vpn Hk2 Hb1c with "Hptree") as "[Hslot1 Hcl1]".
      iEval (rewrite /pt_addr1 Hb1c) in "Hslot1".
      iApply (wp_walk_probe R Φ γc L9 va (mword_of_int 21 : mword 64)
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn)) (pt_ents c1 (vpn_idx 1 vpn))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HL9s3 HL9s4
                ltac:(rewrite HL9s1; exact (walk_slot_addr1 (pt_base c1) va Hva'))
                with "Hcfg Htlbinv Htext Hpc Hfile Hslot1 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot1".
      set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))]> L9).
      set (M5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents c1 (vpn_idx 1 vpn))]> M4).
      set (M6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> M5).
      assert (HM4s2 : M4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
        by (rewrite /M4 lookup_total_insert; reflexivity).
      iEval (rewrite /pt_addr1 Hb1c) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      (* +0x3a c.beqz a5 TAKEN: the L1 slot is the ZERO stop word *)
      assert (Hvbit0 : Z.testbit (bv_unsigned (pt_ents c1 (vpn_idx 1 vpn))) 0 = false).
      { rewrite He1z.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HM6a5 : M6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents c1 (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /M6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                M6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt72 : add_vec (mword_of_int (WK + 0x3a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      (* the allocation arm, grafting at level 1 *)
      pose proof (ptree_own_graft1 (DfracOwn 1) t c1 vpn Hk2 Hk1 Hb1c) as Hacc2.
      unfold pt_addr1 in Hacc2. rewrite Hb1c in Hacc2.
      iApply (wp_walk_alloc R Φ γ γc bsie mm M6 t t
                (fun b => pt_graft1 t vpn b) 0
                (u_pte_addr (pt_base c1) (vpn_idx 1 vpn))
                (pt_ents c1 (vpn_idx 1 vpn)) n Hn
                ltac:(peel_reg)
                ltac:(rewrite /M6 /M5;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      exact HM4s2)
                ltac:(rewrite /M6 /M5 /M4 /L9 /L8 /L7 /L6;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite lookup_total_insert;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                (ptree_same_rep0_refl t) Hacc2
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv [Hi40 Hi42] Hcont").
      (* the SUCCESS continuation: rejoin at +0x40, then the tail *)
      iIntros (Mo b) "%Htrans %Hs1b Hcfg Htoken Htlbinv Hpc Hfile
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hdeep Hptree Henv Hcont".
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      assert (HMos4 : Mo !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite (Htrans (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /M6 /M5 /M4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        exact HL9s4. }
      assert (HMos5 : Mo !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /M6 /M5 /M4 /L9 /L8 /L7 /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (G1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG1s4 : G1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1 lookup_total_insert. rewrite HMos4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HG1s5 : G1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1. rewrite lookup_total_insert_ne; [| reg_neq].
        exact HMos5. }
      iApply (wp_bne_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s4 HG1s5; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* the tail with b0 := b, tf := the L1-grafted tree *)
      iApply (wp_walk_tail R Φ γ γc bsie mm G1 t (pt_graft1 t vpn b) b n Hn Hva'
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /M6 /M5 /M4;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite lookup_total_insert;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite add_vec_zero_l; reflexivity)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hs1b)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G1; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (pt_graft1_same_rep0 t c1 vpn b Hk2 Hk1 He1z)
                ltac:(pose proof (pt_graft1_level0 t c1 vpn b Hk2
                        ltac:(exact Hv2) ltac:(exact Hp2c) Hb1c) as Hl0;
                      eexists _, _, _; split;
                      [exact Hl0
                      | unfold pt_addr0; rewrite pt_ptr_pte_base; reflexivity])
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv Hcont").
      }

      (* ---- arm 1: ZERO ROOT slot: allocate at L2, loop, allocate at L1 ---- *)
      iPoseProof (wi_40 with "Htext") as "Hi40".
      iPoseProof (wi_42 with "Htext") as "Hi42".
      iDestruct (ptree_own_slot2_ro (DfracOwn 1) t vpn with "Hptree") as "[Hslot Hcl2]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                L4 (pt_ents t (vpn_idx 2 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot] [-]").
      { iEval (rewrite Hea0 HL4s2). iExact "Hslot". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot".
      iEval (rewrite Hea0 HL4s2) in "Hslot".
      iDestruct ("Hcl2" with "Hslot") as "Hptree".
      set (L5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents t (vpn_idx 2 vpn))]> L4).
      assert (Hpp36 : add_vec_int (mword_of_int (WK + 0x32) : mword 64) 4 = mword_of_int (WK + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                L5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /L5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (L6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> L5).
      assert (Hpp3a : add_vec_int (mword_of_int (WK + 0x36) : mword 64) 4 = mword_of_int (WK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 TAKEN: the ROOT slot is the ZERO stop word *)
      assert (Hvbit0 : Z.testbit (bv_unsigned (pt_ents t (vpn_idx 2 vpn))) 0 = false).
      { rewrite He2z.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HL6a5 : L6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents t (vpn_idx 2 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /L6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                L6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HL6a5 walk_vbit_eq Hvbit0; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgt72 : add_vec (mword_of_int (WK + 0x3a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
              = mword_of_int (WK + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt72) in "Hpc".
      assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r1) in "Hc56".
      iEval (rewrite HspW1 Hb1) in "Hc56".
      assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r8) in "Hc48".
      iEval (rewrite HspW1 Hb2) in "Hc48".
      assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r9) in "Hc40".
      iEval (rewrite HspW1 Hb3) in "Hc40".
      assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r18) in "Hc32".
      iEval (rewrite HspW1 Hb4) in "Hc32".
      assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r19) in "Hc24".
      iEval (rewrite HspW1 Hb5) in "Hc24".
      assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r20) in "Hc16".
      iEval (rewrite HspW1 Hb6) in "Hc16".
      assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r21) in "Hc08".
      iEval (rewrite HspW1 Hb7) in "Hc08".
      assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)).
      { rewrite /W1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
      iEval (rewrite HW1r22) in "Hc00".
      iEval (rewrite HspW1 Hb8) in "Hc00".
      (* alloc #1: graft an empty L1 node at the root *)
      pose proof (ptree_own_graft2 (DfracOwn 1) t vpn Hk2n) as Hacc1.
      unfold pt_addr2 in Hacc1.
      iApply (wp_walk_alloc R Φ γ γc bsie mm L6 t t
                (fun b => pt_graft2 t vpn b) 1
                (u_pte_addr (pt_base t) (vpn_idx 2 vpn))
                (pt_ents t (vpn_idx 2 vpn)) n Hn
                ltac:(peel_reg)
                ltac:(rewrite /L6 /L5;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      exact HL4s2)
                ltac:(rewrite /L6 /L5 /L4;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite lookup_total_insert;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                ltac:(peel_reg)
                (ptree_same_rep0_refl t) Hacc1
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv [Hi40 Hi42] Hcont").
      (* ---- SUCCESS of alloc #1: rejoin at +0x40 with the L1 page grafted ---- *)
      iIntros (Mo1 b1) "%Htrans1 %Hs1b1 Hcfg Htoken Htlbinv Hpc Hfile
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hdeep Hptree Henv Hcont".
      (* +0x40 c.addiw s4,-9 : 30 -> 21 *)
      assert (HMo1s4 : Mo1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite (Htrans1 (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HMo1s5 : Mo1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans1 (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (G1 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo1 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo1).
      assert (Hpp42 : add_vec_int (mword_of_int (WK + 0x40) : mword 64) 2 = mword_of_int (WK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG1s4 : G1 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite /G1 lookup_total_insert. rewrite HMo1s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HG1s5 : G1 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G1. rewrite lookup_total_insert_ne; [| reg_neq].
        exact HMo1s5. }
      (* +0x42 bne s4,s5 TAKEN (21 <> 12): back to +0x26 *)
      iApply (wp_bne_taken_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s4 HG1s5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hbk26 : add_vec (mword_of_int (WK + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 8164 : mword 13)) = mword_of_int (WK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hbk26) in "Hpc".
      (* ===== LOOP ITERATION 2 on the grafted tree (s4 = 21, level 1) ===== *)
      assert (HG1s3 : G1 !!! Regidx (mword_of_int 19 : mword 5) = va).
      { rewrite /G1. rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite (Htrans1 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /L6 /L5 /L4.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite add_vec_zero_l. reflexivity. }
      iApply (wp_srl_s_r R γc Φ (mword_of_int (WK + 0x26)) (mword_of_int 18 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 20 : mword 5)
                (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                G1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HG1s3 HG1s4; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi26 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (K1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))]> G1).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x2a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 511 : mword 12)
                (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                         (sign_extend' 64 (mword_of_int 511 : mword 12)))
                K1 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /K1 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (K2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                   (sign_extend' 64 (mword_of_int 511 : mword 12)))]> K1).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_cslli_s_r R γc Φ (mword_of_int (WK + 0x2e)) (mword_of_int 18 : mword 5) (mword_of_int 3 : mword 6)
                (shift_bits_left
                   (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                            (sign_extend' 64 (mword_of_int 511 : mword 12)))
                   (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))
                K2 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /K2 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (K3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (shift_bits_left
             (and_vec (shift_bits_right va (subrange_vec_dec (mword_of_int 21 : mword 64) (Z.sub log2_xlen 1) 0))
                      (sign_extend' 64 (mword_of_int 511 : mword 12)))
             (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> K2).
      iEval (rewrite Hpp30) in "Hpc".
      iApply (wp_cadd_s_scfg_r R γc Φ (mword_of_int (WK + 0x30)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                K3 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Hpp32) in "Hpc".
      (* collapse the four s2-writes (K1..K4, all reg18) into ONE insert over G1 *)
      assert (HG1s1 : G1 !!! Regidx (mword_of_int 9 : mword 5)
                      = zero_extend' 64 (concat_vec b1 (zeros' 12 : mword 12))).
      { first [ exact Hs1b1
              | (rewrite /G1; repeat (rewrite lookup_total_insert_ne; [| reg_neq]); exact Hs1b1) ]. }
      set (K4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (u_pte_addr b1 (vpn_idx 1 vpn))]> G1).
      assert (HK4c : <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
          (add_vec (K3 !!! Regidx (mword_of_int 18 : mword 5)) (K3 !!! Regidx (mword_of_int 9 : mword 5)))]> K3 = K4).
      { rewrite /K4 /K3 /K2 /K1 !insert_insert. do 2 f_equal.
        rewrite lookup_total_insert.
        rewrite lookup_total_insert_ne; [| reg_neq].
        rewrite HG1s1; exact (walk_slot_addr1 b1 va Hva'). }
      iEval (rewrite HK4c) in "Hfile".
      assert (HK4s2 : K4 !!! Regidx (mword_of_int 18 : mword 5)
                      = u_pte_addr b1 (vpn_idx 1 vpn))
        by (rewrite /K4 lookup_total_insert; reflexivity).
      (* +0x32 ld s1,0(s2): the ZERO L1 slot of the freshly grafted node *)
      pose proof (pt_graft2_kid t vpn b1) as Hk2g.
      assert (Hb1cg : u_next_base (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)) = b1)
        by (rewrite pt_graft2_ent pt_ptr_pte_base; reflexivity).
      assert (Hch2g : u_next_base (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)) = pt_base (pt_empty_node b1))
        by (rewrite pt_graft2_ent pt_ptr_pte_base pt_empty_node_base; reflexivity).
      assert (He1zg : pt_ents (pt_empty_node b1) (vpn_idx 1 vpn) = mword_of_int 0) by reflexivity.
      iDestruct (ptree_own_slot1_ro (DfracOwn 1) (pt_graft2 t vpn b1) (pt_empty_node b1) vpn Hk2g Hch2g with "Hptree") as "[Hslot1 Hcl1]".
      iApply (wp_ld_s_scfg_r R γc Φ (mword_of_int (WK + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0 : mword 12)
                K4 (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [Hslot1] [-]").
      { iEval (rewrite Hea0 HK4s2). iEval (rewrite /pt_addr1 Hb1cg) in "Hslot1". iExact "Hslot1". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hslot1".
      iEval (rewrite Hea0 HK4s2) in "Hslot1".
      iEval (rewrite /pt_addr1 Hb1cg) in "Hcl1".
      iDestruct ("Hcl1" with "Hslot1") as "Hptree".
      set (K5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn))]> K4).
      iEval (rewrite Hpp36) in "Hpc".
      iApply (wp_andi_s_r R γc Φ (mword_of_int (WK + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 1 : mword 12)
                (and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
                K5 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /K5 lookup_total_insert; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (K6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))]> K5).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.beqz a5 TAKEN again: the fresh L1 slot is zero *)
      assert (Hvbit0g : Z.testbit (bv_unsigned (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn))) 0 = false).
      { rewrite He1zg.
        replace (bv_unsigned (mword_of_int 0 : mword 64)) with 0 by (vm_compute; reflexivity).
        apply Z.bits_0. }
      assert (HK6a5 : K6 !!! Regidx (mword_of_int 15 : mword 5)
                      = and_vec (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) (sign_extend' 64 (mword_of_int 1 : mword 12)))
        by (rewrite /K6 lookup_total_insert; reflexivity).
      iApply (wp_cbeqz_taken_s_zca_scfg_r R γc Φ (mword_of_int (WK + 0x3a)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                K6 (dq:=DfracOwn 1)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HK6a5 walk_vbit_eq Hvbit0g; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite Htgt72) in "Hpc".
      (* alloc #2: graft the level-0 page into the grafted tree *)
      pose proof (ptree_own_graft1 (DfracOwn 1) (pt_graft2 t vpn b1) (pt_empty_node b1) vpn Hk2g ltac:(reflexivity) Hch2g) as Hacc2.
      unfold pt_addr1 in Hacc2. rewrite Hb1cg in Hacc2.
      iApply (wp_walk_alloc R Φ γ γc bsie mm K6 t (pt_graft2 t vpn b1)
                (fun b2 => pt_graft1 (pt_graft2 t vpn b1) vpn b2) 0
                (u_pte_addr b1 (vpn_idx 1 vpn))
                (pt_ents (pt_empty_node b1) (vpn_idx 1 vpn)) n Hn
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      exact HK4s2)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /L6 /L5 /L4;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite lookup_total_insert;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite Ha2 add_vec_zero_l; vm_compute; reflexivity)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (pt_graft2_same_rep0 t vpn b1 Hk2n He2z) Hacc2
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv [Hi40 Hi42] Hcont").
      (* ---- SUCCESS of alloc #2: rejoin at +0x40 with the full path grafted ---- *)
      iIntros (Mo2 b2) "%Htrans2 %Hs1b2 Hcfg Htoken Htlbinv Hpc Hfile
               Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hdeep Hptree Henv Hcont".
      (* +0x40 c.addiw s4,-9 : 21 -> 12; +0x42 bne FALLS *)
      assert (HMo2s4 : Mo2 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 21 : mword 64)).
      { rewrite (Htrans2 (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /K6 /K5 /K4 /K3 /K2 /K1.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        rewrite lookup_total_insert. rewrite HMo1s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HMo2s5 : Mo2 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite (Htrans2 (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite /K6 /K5 /K4 /K3 /K2 /K1.
        repeat (rewrite lookup_total_insert_ne; [| reg_neq]).
        exact HMo1s5. }
      iApply (wp_caddiw_s_scfg_r R γc Φ (mword_of_int (WK + 0x40)) (mword_of_int 20 : mword 5) (mword_of_int 55 : mword 6)
                Mo2 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (G2 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (Mo2 !!! Regidx (mword_of_int 20 : mword 5))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 55 : mword 6)))) 31 0))]> Mo2).
      iEval (rewrite Hpp42) in "Hpc".
      assert (HG2s4 : G2 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G2 lookup_total_insert. rewrite HMo2s4.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HG2s5 : G2 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 12 : mword 64)).
      { rewrite /G2. rewrite lookup_total_insert_ne; [| reg_neq].
        exact HMo2s5. }
      iApply (wp_bne_fall_s_config_scfg_r R γc Φ (mword_of_int (WK + 0x42)) (mword_of_int 8164 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 20 : mword 5)
                G2 (dq:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HG2s4 HG2s5; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp46 : add_vec_int (mword_of_int (WK + 0x42) : mword 64) 4 = mword_of_int (WK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* the tail with b0 := b2, tf := the doubly-grafted tree *)
      assert (Hv2g : pte_valid (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)))
        by (rewrite pt_graft2_ent; exact (pt_ptr_pte_valid b1)).
      assert (Hp2g : pte_ptr (pt_ents (pt_graft2 t vpn b1) (vpn_idx 2 vpn)))
        by (rewrite pt_graft2_ent; exact (pt_ptr_pte_ptr b1)).
      iApply (wp_walk_tail R Φ γ γc bsie mm G2 t (pt_graft1 (pt_graft2 t vpn b1) vpn b2) b2 n Hn Hva'
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (csp_rs1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /L6 /L5 /L4;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite lookup_total_insert;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite add_vec_zero_l; reflexivity)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      exact Hs1b2)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 4) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                ltac:(rewrite /G2; rewrite lookup_total_insert_ne; [| reg_neq];
                      rewrite (Htrans2 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      rewrite /K6 /K5 /K4 /K3 /K2 /K1;
                      repeat (rewrite lookup_total_insert_ne; [| reg_neq]);
                      rewrite (Htrans1 (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate));
                      peel_reg)
                (ptree_same_rep0_trans t (pt_graft2 t vpn b1) (pt_graft1 (pt_graft2 t vpn b1) vpn b2)
                   (pt_graft2_same_rep0 t vpn b1 Hk2n He2z)
                   (pt_graft1_same_rep0 (pt_graft2 t vpn b1) (pt_empty_node b1) vpn b2 Hk2g ltac:(reflexivity) ltac:(reflexivity)))
                ltac:(pose proof (pt_graft1_level0 (pt_graft2 t vpn b1) (pt_empty_node b1) vpn b2 Hk2g Hv2g Hp2g Hch2g) as Hl0;
                      eexists _, _, _; split;
                      [exact Hl0
                      | unfold pt_addr0; rewrite pt_ptr_pte_base; reflexivity])
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
                      Hdeep Hptree Henv Hcont").
  Qed.


  (* the record spec is exactly wp_walk_r's statement *)
  Lemma walk_spec_holds (R : s_regime) : ⊢ walk_spec R.
  Proof.
    iIntros (Φ γ γc bsie mm t m n) "%Hn %Ha0 %Ha2 %Hva %Hrep".
    iApply (wp_walk_r R Φ γ γc bsie mm t m n Hn Ha0 Ha2 Hva Hrep).
  Qed.

End Walk.
