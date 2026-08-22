(* UserMemAccess.v -- the U-mode vmem_read_addr / vmem_write_addr layer:
   the LOAD / STORE / LR / SC memory accesses over the ptree bundle, just
   below execute_*.  This is where instruction ALIGNMENT and the LR/SC
   reservation live; it sits on top of the physical composers of
   UserMemPt.v.

   §0 the reservation platform-effect COROLLARIES.  [load_reservation] and
      [cancel_reservation] are OPAQUE monadic platform axioms (the LR/SC
      reservation set is NOT part of [mstate]).  What is assumed about them
      lives in [ResvAxioms.v], at the TERM level ([load_reservation a n =
      returnm tt]) -- read that file's header for why the exec-level
      assumption this section used to make is not enough under per-node
      stepping.  The two [exec_*] facts below are one-line corollaries and
      keep their exact statements, so no consumer moved.  Nothing about a
      particular reservation content is assumed (match_reservation stays
      opaque and is destructed both ways in SC).

   §1 the aligned vmem_read_addr reduction (LOAD res=false / LR res=true):
      a single aligned access, translation absorbed, value from the pages.
   §2 the aligned vmem_write_addr reduction (STORE res=false / SC res=true
      -- SC destructs [match_reservation] into write-succeeds / write-fails).
   §3 LR/SC MISALIGNED: the platform faults them (AccessFault) before any
      access.                                                             *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import CommonWalk.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserMemPt.
Require Import SmodePte.
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Require Import ResvAxioms.
Require Import HartMemRun HartMemAsm PtWalkCert.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 Reservation platform-effect corollaries of ResvAxioms.v (see the    *)
(*    file header, and ResvAxioms.v's, for why the axioms are TERM-level). *)
(* ===================================================================== *)

Lemma exec_load_reservation :
  forall (a : mword (if 64 =? 32 then 34 else 64)) (w : Z) (s : mstate),
    exec (load_reservation a w) s = Some (tt, s).
Proof. intros a w s. rewrite load_reservation_term. apply exec_returnm. Qed.

Lemma goodmb_load_reservation (Dr Dw : register -> bool) :
  forall (a : mword (if 64 =? 32 then 34 else 64)) (w : Z) (s : mstate) mm,
    goodmb Dr Dw (load_reservation a w) s mm = true.
Proof. intros a w s mm. rewrite load_reservation_term. apply goodmb_returnm. Qed.

Lemma exec_cancel_reservation :
  forall (s : mstate), exec (cancel_reservation tt) s = Some (tt, s).
Proof. intros s. rewrite cancel_reservation_term. apply exec_returnm. Qed.

Lemma goodmb_cancel_reservation (Dr Dw : register -> bool) :
  forall (s : mstate) mm, goodmb Dr Dw (cancel_reservation tt) s mm = true.
Proof. intros s mm. rewrite cancel_reservation_term. apply goodmb_returnm. Qed.

(* ===================================================================== *)
(* §0b THE CERTIFICATE HELPERS THIS FILE'S TWINS SHARE.                   *)
(*                                                                        *)
(*   Package P4 of the user-tier port: every [exec_X] of this file has a   *)
(*   twin [goodmb_X] immediately after it, with the SAME binders and the   *)
(*   SAME hypotheses, generic in [(Dr Dw : register -> bool)] with one     *)
(*   [Dr r = true] per register the stretch reads, and stated at an        *)
(*   ARBITRARY byte map [mm] (written BARE -- re-elaborating the map type  *)
(*   under this file's [SailStdpp.Values] import set gives a DIFFERENT     *)
(*   [Countable Arch.pa] instance).  Where a sub-fact of the exec lemma is *)
(*   itself an [exec ... = Some ...] hypothesis the twin takes BOTH it and *)
(*   its own [goodmb ... = true] companion, which is what keeps this layer *)
(*   independent of the translation certificates below it.                 *)
(*                                                                        *)
(*   NOTHING HERE OWES A MEMORY OBLIGATION.  [vmem_read_addr] /            *)
(*   [vmem_write_addr] / [pmaCheck] / [pmpCheck] / [memory_exception] have *)
(*   no memory node of their OWN: every byte access sits inside            *)
(*   [translateAddr] / [mem_read] / [mem_write_ea] / [mem_write_value],    *)
(*   i.e. inside a hypothesis-supplied certificate.  So the                *)
(*   [dev_addr pa = false] / [bytes_owned mm pa n = true] pair that        *)
(*   [PtWalkCert]'s PTE families carry is discharged one layer DOWN        *)
(*   (UserMemPt / PtWalkCert) and never appears here.                      *)
(*                                                                        *)
(*   The three helpers below are the shared shapes: the page split (which  *)
(*   is event-free but NOT unconditionally certified -- its off-page arm   *)
(*   is an [assert_exp'] that can [fail], so the twin takes the exec fact  *)
(*   that rules that out), and the three [MemAccessGen] intra-page         *)
(*   reductions the aligned/misaligned families are instances of.          *)
(* ===================================================================== *)

Lemma goodmb_split_on_page_boundary (Dr Dw : register -> bool) {n : Z}
    (addr : mword n) (width : Z) (s s' : mstate) (p : Z * Z) mm :
  exec (split_on_page_boundary addr width) s = Some (p, s') ->
  goodmb Dr Dw (split_on_page_boundary addr width) s mm = true.
Proof.
  intros He. unfold split_on_page_boundary in He |- *. cbn zeta in He |- *.
  match goal with |- context[if ?b then _ else _] => destruct b end.
  - apply goodmb_returnm.
  - unfold Defs.assert_exp' in He |- *.
    match goal with |- context[if ?b then _ else _] => destruct b end.
    + erewrite gm_bind; [ | apply goodmb_returnm | apply exec_returnm ].
      apply goodmb_returnm.
    + rewrite exec_bind in He. unfold Defs.fail in He. cbn [exec] in He.
      discriminate He.
Qed.

(* [MemAccessGen.exec_translate_and_read_value_gen]'s twin *)
Lemma goodmb_translate_and_read_value_gen (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (pbmt : page_based_mem_type) (v : mword (8*width)) (s s1 s2 : mstate) mm :
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, pbmt, init_ext_ptw), s1) ->
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (mem_read acc pbmt (Physaddr pa) width aq rl res) s1 = Some (Ok v, s2) ->
  goodmb Dr Dw (mem_read acc pbmt (Physaddr pa) width aq rl res) s1 mm = true ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros Htr Htrg Hmr Hmrg.
  unfold translate_and_read_value.
  gmm_peel Htrg Htr. cbn match beta.
  gmm_peel Hmrg Hmr. cbn match beta.
  apply goodmb_returnm.
Qed.

(* [MemAccessGen.exec_vmem_read_addr_intra]'s twin: the region RETIRES, so the
   [catch_early_return] wrapper comes off with [goodmb_cer] and the chain is
   peeled in the plain early-return monad. *)
Lemma goodmb_vmem_read_addr_intra (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (v : mword (8*width)) (acc : MemoryAccessType mem_payload)
    (aq rl res : bool) (ep : Privilege) (md : SATPMode) (s s2 : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Ok (Physaddr pa, v), s2) ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) width acc aq rl res) s mm = true ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros HDm HDcp Hpos Hsplit Hsplitg Hguard Heff Heffg Htm Htmg Htrv Htrvg.
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  unfold vmem_read_addr. apply goodmb_cer.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s));
    [ | assert (Hgg : goodmb Dr Dw G s mm = true) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply goodmb_returnm. }
  erewrite gm_bind0R; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpg (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s));
    [ | assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn beta.
  gmm_lift Htrvg Htrv. cbn match beta.
  replace (Z.eqb width width) with true by (symmetry; apply Z.eqb_refl).
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hif : execR IF s2 = Some (inr tt, s2));
    [ | assert (Hifg : goodmb Dr Dw IF s2 mm = true) ] end.
  { destruct res.
    - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s2)). cbn beta.
      rewrite execR_liftR. rewrite exec_load_reservation. reflexivity.
    - apply execR_returnR_fwd. }
  { destruct res.
    - match goal with |- context[Defs.assert_exp' true ?msg] =>
        gmm_lift (goodmb_assert_exp'_true Dr Dw msg s2 mm)
                 (exec_assert_exp'_true msg s2) end.
      cbn beta. apply goodmb_liftR. apply goodmb_load_reservation.
    - apply goodmb_returnm. }
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseq : execR (Defs.bind0 IF rr) s2
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * width))
                                  (8 * width - 1) 0 (autocast (T := mword) v)), s2));
    [ | assert (Hseqg : goodmb Dr Dw (Defs.bind0 IF rr) s2 mm = true) ] end.
  { rewrite (execR_bind0_Some _ _ _ _ Hif). apply execR_returnR_fwd. }
  { erewrite gm_bind0R; [ | exact Hifg | exact Hif ]. apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hseqg | exact Hseq ]. cbn beta.
  rewrite (usvd_zeros_full_gen (8 * width) v ltac:(lia)).
  rewrite andb_false_r. cbn match beta.
  apply goodmb_returnm.
Qed.

(* ...and [MemAccessGen.exec_vmem_read_addr_intra_err]'s twin.  Here the region
   THROWS, so [goodmb_cer] is unavailable ([goodmb] refuses an [ExtraOutcome]
   node): the wrapper stays ON and the chain is peeled with the [gm_cer_*]
   family, ending at [mcer_early_return_nest]. *)
Lemma goodmb_vmem_read_addr_intra_err (Dr Dw : register -> bool) (width : Z)
    (va : mword 64) (er : ExecutionResult) (acc : MemoryAccessType mem_payload)
    (aq rl res : bool) (ep : Privilege) (md : SATPMode) (s s2 : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Err er, s2) ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) width acc aq rl res) s mm = true ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros HDm HDcp Hpos Hsplit Hsplitg Hguard Heff Heffg Htm Htmg Htrv Htrvg.
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  unfold vmem_read_addr.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s));
    [ | assert (Hgg : goodmb Dr Dw G s mm = true) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply goodmb_returnm. }
  erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpg (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s));
    [ | assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_cer_bind; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn beta.
  gmm_lift Htrvg Htrv. cbn match beta.
  unfold Defs.bind0. rewrite mcer_early_return_nest. apply goodmb_returnm.
Qed.

(* [MemAccessGen.exec_vmem_write_addr_intra]'s twin (the plain STORE). *)
Lemma goodmb_vmem_write_addr_intra (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (dat : mword (8*width)) (ep : Privilege) (md : SATPMode)
    (s s' sfin : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception (Store Data) false = None) ->
  exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) (Store Data)) s mm
    = true ->
  exec (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false) s'
    = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false) s' mm
    = true ->
  exec (mem_write_value (Physaddr pa) width
          (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
          (Store Data) PBMT_PMA false false false) s' = Some (Ok true, sfin) ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width
          (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
          (Store Data) PBMT_PMA false false false) s' mm = true ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) s mm
    = true.
Proof.
  intros HDm HDcp Hpos Hsplit Hsplitg Hguard Heff Heffg Htm Htmg Htr Htrg
         Hea Heag Hwv Hwvg.
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  unfold vmem_write_addr. apply goodmb_cer.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s));
    [ | assert (Hgg : goodmb Dr Dw G s mm = true) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply goodmb_returnm. }
  erewrite gm_bind0R; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpg (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s));
    [ | assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn beta zeta.
  gmm_lift Htrg Htr. cbn match beta.
  match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
    assert (Hsc : execR (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s'
                  = Some (inr tt, s')) by (rewrite execR_liftR; reflexivity);
    assert (Hscg : goodmb Dr Dw (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s' mm
                   = true) by (apply goodmb_liftR; apply goodmb_returnm) end.
  match goal with
  | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
      assert (Hwr : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s' = Some (inr true, sfin));
      [ | assert (Hwrg : goodmb Dr Dw (Defs.bind0 (Defs.liftR asrt) Nbody) s' mm = true) ]
  end.
  { rewrite (execR_bind0_Some _ _ _ _ Hsc).
    (* the [if andb res (...)] guard: [res] is [false] here, so it may already
       have iota-reduced -- take the else-branch only if it has not *)
    try match goal with
    | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
        change (execR B ss = R)
    end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match. apply execR_returnR_fwd. }
  { erewrite gm_bind0R; [ | exact Hscg | exact Hsc ].
    try match goal with
    | |- goodmb ?dr ?dw (match _ as x in bool return @?P x with
                         | true => _ | false => ?B end) ?ss ?mm0 = ?R =>
        change (goodmb dr dw B ss mm0 = R)
    end.
    gmm_lift Heag Hea. cbn match beta.
    gmm_lift Hwvg Hwv. cbn match beta.
    apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hwrg | exact Hwr ]. cbn beta.
  apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §1 The aligned vmem_read_addr reduction, WIDTH-GENERIC and premise-     *)
(*    shaped and res-generic: LOAD (res=false) and LR (res=true) both go   *)
(*    through it.  The align guard needs [0 < width] (so split gives one   *)
(*    chunk); the [width|4096] etc. constraints are not needed here.       *)
(* ===================================================================== *)


Lemma exec_vmem_read_addr_aligned (width : Z) (va pa : mword 64) (v : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (s s' : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' = Some (Ok v, s') ->
  exists dvv : mword (8 * width),
    exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s = Some (Ok dvv, s').
Proof.
  intros Hw Halign Heff Htm Htr Hmr.
  exists v.
  apply (exec_vmem_read_addr_aligned_gen width va pa v acc aq rl res ep md s s'
           Hw Halign Heff Htm).
  - exact (exec_translate_and_read_value_gen width va pa acc aq rl res PBMT_PMA v
             s s' s' Htr Hmr).
  - intros _. apply exec_load_reservation.
Qed.

Lemma goodmb_vmem_read_addr_aligned (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (v : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (s s' : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' = Some (Ok v, s') ->
  goodmb Dr Dw (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' mm = true ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros HDm HDcp Hw Halign Heff Heffg Htm Htmg Htr Htrg Hmr Hmrg.
  pose proof (exec_split_on_page_boundary_aligned va width s Hw Halign) as Hsplit.
  exact (goodmb_vmem_read_addr_intra Dr Dw width va pa v acc aq rl res ep md s s' mm
           HDm HDcp (vmem_width_pos _ Hw) Hsplit
           (goodmb_split_on_page_boundary Dr Dw va width s s (width, 0) mm Hsplit)
           (or_introl Halign) Heff Heffg Htm Htmg
           (exec_translate_and_read_value_gen width va pa acc aq rl res PBMT_PMA v
              s s' s' Htr Hmr)
           (goodmb_translate_and_read_value_gen Dr Dw width va pa acc aq rl res
              PBMT_PMA v s s' s' mm Htr Htrg Hmr Hmrg)).
Qed.

(* the LOAD bundle composer (width 8, res=false): aligned load at a
   user-mapped load-permitted va reduces vmem_read_addr to Ok of the
   width-8 value, the translation absorbed. *)
(* ===================================================================== *)
(* §1b The aligned vmem_write_addr reduction (STORE), width-generic.  The  *)
(*     write-value is the model's own subrange extraction [wv]; udata_own  *)
(*     absorbs whatever value lands (contents existential).                *)
(* ===================================================================== *)



(* ===================================================================== *)
(* §1c The aligned vmem_write_addr reduction for STORECONDITIONAL, width-  *)
(*     generic and premise-shaped.  The [match_reservation] outcome        *)
(*     decides: true -> the write lands (Ok true, write_bytes state);      *)
(*     false -> the reservation was lost, no write (Ok false, state at     *)
(*     the translated s').  Both re-establish the invariant.  aq/rl are    *)
(*     whatever the SC instruction passed (execute_STORECON uses aq&&rl /  *)
(*     rl); res = true throughout.                                         *)
(* ===================================================================== *)

(* THE POST-WRITE STATE IS A PARAMETER, NOT A [write_bytes] LITERAL.  The
   width-generic conditional RAM leaf ([UserMemCert.exec_write_ram_cond_gen])
   cannot NAME the bytes it wrote -- its post map is [write_bytes .. v] at an
   EXISTENTIAL [v] -- so a composer built on it can never produce the literal
   form.  Taking [sw] opaquely is the same discipline the plain-store arm's
   [exec_vmem_write_addr_intra] already follows, and it is what lets
   [UserMemCert.u_sc_pure] feed this lemma directly. *)
Lemma exec_vmem_write_addr_sc (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (aq rl maq mrl : bool) (ep ep' : Privilege) (md : SATPMode) (plan : Phys_Mem_Access_Info)
    (s s' sw : mstate) :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  (* success (match_reservation = true): ea + write with the SC flags *)
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (Ok true, sw) ->
  (* fail (match_reservation = false): the access is still CHECKED -- and the
     check now answers with a splitting plan, not with [None] -- and no write
     happens *)
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some (Ok plan, s') ->
  exec (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s
    = Some (Ok (match_reservation (bits_of_physaddr (Physaddr pa))),
            if match_reservation (bits_of_physaddr (Physaddr pa))
            then sw else s').
Proof.
  intros acc wv Hw Halign Heff Htm Htr Hea Hwv Heff' Hpac.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_split_on_page_boundary_aligned va width s Hw Halign)).
  cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
  (* the res/is_store_conditional agreement assert, then the reservation
     branch: held -> ea + write; lost -> the access is still CHECKED (the
     check answers with a plan now) and nothing is written *)
  match goal with |- context[Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?IF) ?k] =>
    assert (Hsc : execR (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s'
                  = Some (inr tt, s'))
      by (rewrite execR_liftR; reflexivity);
    assert (Hbr : execR (Defs.bind0 (Defs.liftR asrt) IF) s'
                  = Some (inr (match_reservation (bits_of_physaddr (Physaddr pa))),
                          if match_reservation (bits_of_physaddr (Physaddr pa))
                          then sw else s')) end.
  { rewrite (execR_bind0_Some _ _ _ _ Hsc).
    destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match beta.
      apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Heff'). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpac). cbn match beta.
      apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hbr). cbn beta.
  rewrite andb_false_r. cbn match beta.
  rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_vmem_write_addr_sc (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (dat : mword (8*width)) (aq rl maq mrl : bool)
    (ep ep' : Privilege) (md : SATPMode) (plan : Phys_Mem_Access_Info)
    (s s' sw : mstate) mm :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  Dr mstatus = true -> Dr cur_privilege = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s mm = true ->
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (Ok true, sw) ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' mm = true ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some (Ok plan, s') ->
  goodmb Dr Dw (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s' mm = true ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s mm = true.
Proof.
  intros acc wv HDm HDcp Hw Halign Heff Heffg Htm Htmg Htr Htrg Hea Heag
         Hwv Hwvg Heff' Heff'g Hpac Hpacg.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  assert (Hms' : goodmb Dr Dw (Defs.read_reg mstatus : M _) s' mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg' : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s' mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  unfold vmem_write_addr. apply goodmb_cer.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn [bits_of_virtaddr]. cbn zeta.
  pose proof (exec_split_on_page_boundary_aligned va width s Hw Halign) as Hsplit.
  gmm_lift (goodmb_split_on_page_boundary Dr Dw va width s s (width, 0) mm Hsplit) Hsplit.
  cbn beta zeta match.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpg (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s));
    [ | assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn beta zeta.
  gmm_lift Htrg Htr. cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?IF) ?k] =>
    assert (Hsc : execR (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s'
                  = Some (inr tt, s')) by (rewrite execR_liftR; reflexivity);
    assert (Hscg : goodmb Dr Dw (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s' mm
                   = true) by (apply goodmb_liftR; apply goodmb_returnm);
    assert (Hbr : execR (Defs.bind0 (Defs.liftR asrt) IF) s'
                  = Some (inr (match_reservation (bits_of_physaddr (Physaddr pa))),
                          if match_reservation (bits_of_physaddr (Physaddr pa))
                          then sw else s'));
    [ | assert (Hbrg : goodmb Dr Dw (Defs.bind0 (Defs.liftR asrt) IF) s' mm = true) ] end.
  { rewrite (execR_bind0_Some _ _ _ _ Hsc).
    destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match beta.
      apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Heff'). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpac). cbn match beta.
      apply execR_returnR_fwd. }
  { erewrite gm_bind0R; [ | exact Hscg | exact Hsc ].
    destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr.
    - cbn [Riscv.rv64d.not negb andb].
      gmm_lift Heag Hea. cbn match beta.
      gmm_lift Hwvg Hwv. cbn match beta.
      apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb andb].
      gmm_lift Hms' (exec_read_reg mstatus s'). cbn beta.
      gmm_lift Hcpg' (exec_read_reg cur_privilege s'). cbn beta.
      gmm_lift Heff'g Heff'. cbn beta.
      gmm_lift Hpacg Hpac. cbn match beta.
      apply goodmb_returnm. }
  erewrite gm_bindR; [ | exact Hbrg | exact Hbr ]. cbn beta.
  rewrite andb_false_r. cbn match beta.
  apply goodmb_returnm.
Qed.


(* ===================================================================== *)
(* §2 The WIDTH-GENERIC bundle composers: LOAD and STORE at an aligned,    *)
(*    user-mapped, check-passing va, threading the physical composers      *)
(*    (UserMemPt.v) through the aligned vmem reductions.  Section over the  *)
(*    width [k] + the two width-typed plain-RAM bricks (same shape as      *)
(*    UserMemPt §5); the width instances are the trivial derivations at    *)
(*    the end.                                                             *)
(* ===================================================================== *)

Section UserMemAccessGeneric.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  (* the vmem level splits on a PAGE boundary now, which needs the width to be
     one of the four the ISA allows there *)
  Context (Hkvw : vmem_width k).
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_plain : forall (addr : mword 64) (data : mword (8 * k)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  Lemma user_pt_vmem_read_addr_load (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (dvv : mword (8 * k)) (σ' : mstate),
      ⌜exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false) σ
        = Some (Ok dvv, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    (* the mode fact must be taken BEFORE the walk moves the state *)
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (user_pt_load_data_g k Hk Hk8 Hkdvd Huintk Hread_plain
            uroot tfp um data w va σ
            Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
            with "Hri Hgh Hinv Hdata")
      as (dv σ') "(%Htr & %Hmr & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
    assert (Htr' : exec (translateAddr (Virtaddr va) (Load Data)) σ
                   = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')).
    { exact Htr. }
    destruct (exec_vmem_read_addr_aligned k va (u_walk_pa w va) dv (Load Data)
                false false false User Sv39 σ σ' Hkvw Hal
                ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv)
                Htm Htr' Hmr) as (dvv & Hvr).
    iModIntro. iExists dvv, σ'.
    iSplit; [ iPureIntro; exact Hvr | ].
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

  Lemma user_pt_vmem_write_addr_store (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (dat : mword (8 * k)) (σ : mstate) :
    let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*k-1) (8*0*k))
              : mword (8 * k) in
    um !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ' : mstate,
      ⌜exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false) σ
        = Some (Ok true, MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) wv) σ'.(mdev))⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗
      gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) wv) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros wv Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (user_pt_store_data_g k Hk Hk8 Hkdvd Huintk Hwrite_plain
            uroot tfp um data w va wv σ
            Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
            with "Hri Hgh Hinv Hdata")
      as (σ') "(%Htr & %Hwv & %Hea & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
    iModIntro. iExists σ'.
    iSplit; [ iPureIntro | ].
    { apply (exec_vmem_write_addr_aligned_store k va (u_walk_pa w va) dat
               User Sv39 σ σ' _ Hkvw Hal
               ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv)
               Htm).
      - exact Htr.
      - exact Hea.
      - exact Hwv. }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserMemAccessGeneric.

(* the width instances -- the names the memory arms consume *)
Section UserMemAccessInstances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.



End UserMemAccessInstances.

(* ===================================================================== *)
(* §3 Building blocks for the MISALIGNED-access faults.  A misaligned      *)
(*    LR/SC faults BEFORE any access: the platform delivers AccessFault    *)
(*    (plat_misaligned_access.lrsc), surfacing as E_Load_Access_Fault      *)
(*    (LR) / E_SAMO_Access_Fault (SC), state unchanged.  (Plain load/store *)
(*    misalignment does NOT fault -- the hardware splits it; AMO           *)
(*    misalignment is checked inside execute_AMO.)                         *)
(*    [exec_memory_exception] and [exec_plat_misaligned_lrsc] are the two  *)
(*    exec bricks; the reductions built on them are                        *)
(*    [exec_vmem_read_addr_misaligned_lr] / [_write_addr_misaligned_sc]    *)
(*    below (width-generic).  The technique for the model's DEPENDENT      *)
(*    align guard ([if not is_aligned return MR ... then fault else tt]    *)
(*    inside catch_early_return) is to keep the bind/liftR structure the   *)
(*    execR_* lemmas match on intact -- never cbn through it.              *)
(* ===================================================================== *)

Lemma exec_memory_exception (va pc : mword 64) (exc : ExceptionType)
    (priv : Privilege) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = priv ->
  register_lookup PC s.(sregs) = pc ->
  exec (memory_exception (Virtaddr va) exc) s
    = Some (Trap (priv, make_sync_exception exc va, pc), s).
Proof.
  intros Hcp Hpc.
  unfold memory_exception, trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite Hpc. cbn [bits_of_virtaddr]. apply exec_returnm.
Qed.

Lemma goodmb_memory_exception (Dr Dw : register -> bool) (va pc : mword 64)
    (exc : ExceptionType) (priv : Privilege) (s : mstate) mm :
  Dr cur_privilege = true -> Dr PC = true ->
  register_lookup cur_privilege s.(sregs) = priv ->
  register_lookup PC s.(sregs) = pc ->
  goodmb Dr Dw (memory_exception (Virtaddr va) exc) s mm = true.
Proof.
  intros HDcp HDpc Hcp Hpc.
  unfold memory_exception, trap.
  gmm_rr cur_privilege HDcp. rewrite Hcp.
  gmm_rr PC HDpc. rewrite Hpc. cbn [bits_of_virtaddr]. apply goodmb_returnm.
Qed.

(* [plat_misaligned_exception] is a PURE function now, not a monadic one. *)
Lemma plat_misaligned_lrsc (acc : MemoryAccessType mem_payload) :
  is_amo_access acc = false ->
  plat_misaligned_exception acc true = Some AccessFault.
Proof.
  intro Hamo. unfold plat_misaligned_exception. rewrite Hamo.
  vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §3c The MISALIGNED LR/SC fault reductions.  plat/memory_exception       *)
(*     Opaque; [cbn [not negb]] takes the fault branch (leaving plat       *)
(*     folded); then peel the enclosing bind / bind0 (the fault block is   *)
(*     [bind (bind0 FAULT split) loop]) down to the fault block, whose     *)
(*     early_return short-circuits.                                        *)
(* ===================================================================== *)

Lemma execR_early_ret {R X} (r : R) (s : mstate) :
  execR (Defs.early_return r : Defs.monadR R exception X) s = Some (inl r, s).
Proof. reflexivity. Qed.

Section MisalignedFaults.
  Local Opaque plat_misaligned_exception memory_exception.

  Ltac peel_b := match goal with |- context [execR (Defs.bind ?m ?f) ?st] => rewrite (execR_bind m f st) end.
  Ltac peel_b0 := match goal with |- context [execR (Defs.bind0 ?m ?n) ?st] => rewrite (execR_bind0 m n st) end.
  Ltac peel_l := match goal with |- context [execR (Defs.liftR ?m) ?st] => rewrite (execR_liftR m st) end.

  Lemma exec_vmem_read_addr_misaligned_lr (va pc : mword 64) (width : Z)
      (aq rl maq mrl : bool) (priv : Privilege) (s : mstate) :
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    exec (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) maq mrl true) s
      = Some (Err (Trap (priv, make_sync_exception (E_Load_Access_Fault tt) va, pc)), s).
  Proof.
    intros Hnal Hcp Hpc.
    unfold vmem_read_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (plat_misaligned_lrsc (LoadReserved (aq, rl, Data)) eq_refl). cbn match.
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_memory_exception va pc (E_Load_Access_Fault tt) priv s Hcp Hpc). cbn match.
    rewrite execR_early_ret. cbn match. reflexivity.
  Qed.

  Lemma goodmb_vmem_read_addr_misaligned_lr (Dr Dw : register -> bool)
      (va pc : mword 64) (width : Z) (aq rl maq mrl : bool) (priv : Privilege)
      (s : mstate) mm :
    Dr cur_privilege = true -> Dr PC = true ->
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    goodmb Dr Dw
      (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) maq mrl true) s mm
      = true.
  Proof.
    intros HDcp HDpc Hnal Hcp Hpc.
    unfold vmem_read_addr.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    rewrite (plat_misaligned_lrsc (LoadReserved (aq, rl, Data)) eq_refl). cbn match.
    unfold Defs.bind0.
    gmm_lift (goodmb_memory_exception Dr Dw va pc (E_Load_Access_Fault tt) priv s mm
                HDcp HDpc Hcp Hpc)
             (exec_memory_exception va pc (E_Load_Access_Fault tt) priv s Hcp Hpc).
    rewrite mcer_early_return. apply goodmb_returnm.
  Qed.

  Lemma exec_vmem_write_addr_misaligned_sc (va pc : mword 64) (width : Z)
      (dat : mword (8 * width)) (aq rl maq mrl : bool) (priv : Privilege) (s : mstate) :
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional (aq, rl, Data)) maq mrl true) s
      = Some (Err (Trap (priv, make_sync_exception (E_SAMO_Access_Fault tt) va, pc)), s).
  Proof.
    intros Hnal Hcp Hpc.
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (plat_misaligned_lrsc (StoreConditional (aq, rl, Data)) eq_refl). cbn match.
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_memory_exception va pc (E_SAMO_Access_Fault tt) priv s Hcp Hpc). cbn match.
    rewrite execR_early_ret. cbn match. reflexivity.
  Qed.

  Lemma goodmb_vmem_write_addr_misaligned_sc (Dr Dw : register -> bool)
      (va pc : mword 64) (width : Z) (dat : mword (8 * width))
      (aq rl maq mrl : bool) (priv : Privilege) (s : mstate) mm :
    Dr cur_privilege = true -> Dr PC = true ->
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    goodmb Dr Dw
      (vmem_write_addr (Virtaddr va) width dat (StoreConditional (aq, rl, Data)) maq mrl true)
      s mm = true.
  Proof.
    intros HDcp HDpc Hnal Hcp Hpc.
    unfold vmem_write_addr.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    rewrite (plat_misaligned_lrsc (StoreConditional (aq, rl, Data)) eq_refl). cbn match.
    unfold Defs.bind0.
    gmm_lift (goodmb_memory_exception Dr Dw va pc (E_SAMO_Access_Fault tt) priv s mm
                HDcp HDpc Hcp Hpc)
             (exec_memory_exception va pc (E_SAMO_Access_Fault tt) priv s Hcp Hpc).
    rewrite mcer_early_return. apply goodmb_returnm.
  Qed.

  Local Transparent plat_misaligned_exception memory_exception.
End MisalignedFaults.

(* ===================================================================== *)
(* §4 The MISALIGNED plain load/store SPLIT.  When the address is not     *)
(*     aligned to [width] the model does not fault (plat_misaligned_      *)
(*     access.load_store = None); instead it splits the access into       *)
(*     [n = width / 2^ctz(addr)] chunks of [bytes = 2^ctz(addr)] each and *)
(*     runs an [untilMT] loop, translating+accessing each chunk           *)
(*     independently.  We must handle this for TOTALITY: arbitrary user   *)
(*     code can issue any misaligned plain load/store.                    *)
(*                                                                        *)
(* §4a The generic [untilMT'] loop reductions.  The split loop uses a     *)
(*     CONSTANT measure [fun _ => n], so the accessibility limit starts   *)
(*     at [n] and decrements once per iteration; termination is driven    *)
(*     by the [finished] flag in [cond], reached exactly at the last      *)
(*     chunk.  We destruct the [Acc] witness to unfold one loop step      *)
(*     (axiom-free, no proof-irrelevance), giving [_step] (cond false ->  *)
(*     recurse at [limit-1]) and [_last] (cond true -> return); [_chain]  *)
(*     composes [N] iterations by induction.                              *)
(* ===================================================================== *)


(* ===================================================================== *)
(* §4b The MISALIGNED plain-LOAD split reduction, generic in the chunk    *)
(*     count N.  [split_var k] is the loop state after k chunks:          *)
(*     [(data_seq k, finished?, offset)] with [data_seq] the running      *)
(*     byte-assembly.  [split_body_step] reduces one loop iteration       *)
(*     (translate+read+assemble) generically in k; [split_loop] composes  *)
(*     N of them via [execR_untilMT'_chain]; the top lemma glues on the   *)
(*     align-guard (plat load_store = None -> no fault) and the split.    *)
(*     res=false: the split fires only for plain load/store, never LR.    *)
(* ===================================================================== *)


Lemma plat_misaligned_loadstore_none (acc : MemoryAccessType mem_payload) :
  is_amo_access acc = false -> is_vector_access acc = false ->
  plat_misaligned_exception acc false = None.
Proof.
  intros Hamo Hvec. unfold plat_misaligned_exception.
  rewrite Hamo. cbn match. rewrite Hvec. cbn match.
  vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §4b/§4c THE MISALIGNED ACCESS, restated where the bump put it.          *)
(*                                                                        *)
(*   These two lemmas used to describe a misaligned access as N chunks AT  *)
(*   THE VMEM LEVEL, each with its OWN [translateAddr] -- [data_seq],      *)
(*   [split_body], the N-iteration [split_loop].  The model no longer does *)
(*   that.  [vmem_read_addr]/[vmem_write_addr] split only across a PAGE    *)
(*   boundary; the MAG/alignment split moved DOWN into                     *)
(*   [checked_mem_read]/[checked_mem_write], under a SINGLE translation.   *)
(*   So an in-page misaligned access is one full-width translate-and-      *)
(*   access, and these are instances of the intra-page lemmas that also    *)
(*   serve the aligned case ([MemAccessGen.exec_vmem_{read,write}_addr_    *)
(*   intra]).  The chunk sequence has not disappeared -- it lives inside   *)
(*   [mem_read]/[mem_write_value] now, which is where the caller supplies  *)
(*   it.                                                                   *)
(* ===================================================================== *)

Lemma exec_vmem_read_addr_misaligned (width : Z) (va pa : mword 64)
    (v : mword (8 * width)) (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) (s s' : mstate) :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  plat_misaligned_exception acc false = None ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl false) s' = Some (Ok v, s') ->
  exists dvv : mword (8 * width),
    exec (vmem_read_addr (Virtaddr va) width acc aq rl false) s = Some (Ok dvv, s').
Proof.
  intros Hpos Hsplit Hpme Heff Htm Htr Hmr.
  exists v.
  apply (exec_vmem_read_addr_intra width va pa v acc aq rl false ep md s s'
           Hpos Hsplit (or_intror Hpme) Heff Htm).
  - exact (exec_translate_and_read_value_gen width va pa acc aq rl false PBMT_PMA v
             s s' s' Htr Hmr).
  - discriminate.
Qed.

Lemma goodmb_vmem_read_addr_misaligned (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (v : mword (8 * width)) (acc : MemoryAccessType mem_payload)
    (aq rl : bool) (ep : Privilege) (md : SATPMode) (s s' : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  plat_misaligned_exception acc false = None ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl false) s' = Some (Ok v, s') ->
  goodmb Dr Dw (mem_read acc PBMT_PMA (Physaddr pa) width aq rl false) s' mm = true ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width acc aq rl false) s mm = true.
Proof.
  intros HDm HDcp Hpos Hsplit Hsplitg Hpme Heff Heffg Htm Htmg Htr Htrg Hmr Hmrg.
  exact (goodmb_vmem_read_addr_intra Dr Dw width va pa v acc aq rl false ep md s s' mm
           HDm HDcp Hpos Hsplit Hsplitg (or_intror Hpme) Heff Heffg Htm Htmg
           (exec_translate_and_read_value_gen width va pa acc aq rl false PBMT_PMA v
              s s' s' Htr Hmr)
           (goodmb_translate_and_read_value_gen Dr Dw width va pa acc aq rl false
              PBMT_PMA v s s' s' mm Htr Htrg Hmr Hmrg)).
Qed.

Lemma exec_vmem_write_addr_misaligned (width : Z) (va pa : mword 64)
    (dat : mword (8 * width)) (ep : Privilege) (md : SATPMode) (s s' sfin : mstate) :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  plat_misaligned_exception (Store Data) false = None ->
  exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false) s'
    = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width
          (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
          (Store Data) PBMT_PMA false false false) s'
    = Some (Ok true, sfin) ->
  exec (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) s
    = Some (Ok true, sfin).
Proof.
  intros Hpos Hsplit Hpme Heff Htm Htr Hea Hwv.
  exact (exec_vmem_write_addr_intra width va pa dat ep md s s' sfin
           Hpos Hsplit (or_intror Hpme) Heff Htm Htr Hea Hwv).
Qed.

Lemma goodmb_vmem_write_addr_misaligned (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (dat : mword (8 * width)) (ep : Privilege) (md : SATPMode)
    (s s' sfin : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  plat_misaligned_exception (Store Data) false = None ->
  exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) (Store Data)) s mm
    = true ->
  exec (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false) s'
    = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width (Store Data) PBMT_PMA false false false)
    s' mm = true ->
  exec (mem_write_value (Physaddr pa) width
          (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
          (Store Data) PBMT_PMA false false false) s'
    = Some (Ok true, sfin) ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width
          (autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0))
          (Store Data) PBMT_PMA false false false) s' mm = true ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) s mm
    = true.
Proof.
  intros HDm HDcp Hpos Hsplit Hsplitg Hpme Heff Heffg Htm Htmg Htr Htrg
         Hea Heag Hwv Hwvg.
  exact (goodmb_vmem_write_addr_intra Dr Dw width va pa dat ep md s s' sfin mm
           HDm HDcp Hpos Hsplit Hsplitg (or_intror Hpme) Heff Heffg Htm Htmg
           Htr Htrg Hea Heag Hwv Hwvg).
Qed.

(* ===================================================================== *)
(* §5 The LR/SC RETIRE-OR-FAULT disjunction.  [pma_allows_all] pins       *)
(*    readable/writable/atomic but NOT [PMA_reservability], and the       *)
(*    LoadReserved/StoreConditional pma arms gate on                      *)
(*    [reservability <> RsrvNone].  So on a user-mapped, aligned, R/W     *)
(*    address LR/SC either RETIRE (reservability set: the reserved        *)
(*    read/conditional write lands) or take a delegated ACCESS FAULT      *)
(*    (reservability = RsrvNone: pma denies).  Both outcomes are total    *)
(*    and safe; we prove the disjunction rather than assuming a value.    *)
(*                                                                        *)
(* §5a The reserved-RAM read atoms.  Identical to the plain read atoms    *)
(*    (read_ram is AK-agnostic for RAM); the reserved read_kind only      *)
(*    swaps the access-kind constructor (AV_exclusive vs AV_plain).       *)
(* ===================================================================== *)





(* ===================================================================== *)
(* §5b The reserved pmaCheck, branching on reservability.  On the RAM     *)
(*    region [pma_allows_all] gives readable/writable=true but leaves     *)
(*    [PMA_reservability] free, so the LR/SC pma arm                       *)
(*    [andb R/W (reservability<>RsrvNone)] resolves to the reservability  *)
(*    bit: [<>None] -> allowed (None fault), [=None] -> the delegated      *)
(*    access fault (E_Load/E_SAMO).  This is the branch point of the      *)
(*    retire-or-fault disjunction.                                        *)
(* ===================================================================== *)

Lemma exec_pmaCheck_ram_lr_g (aq rl : bool) (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok pma_ok_aligned else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros Hmatch Halign HRead.
  unfold pmaCheck. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in HRead |- *.
  cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)). cbn beta.
  rewrite execR_returnR. cbn match beta.
  rewrite HRead. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_mag_pma_check_aligned _ _ _ _ _ _ (exec_is_mag_applicable_lr aq rl k s) Halign)).
    cbn beta. cbn match. rewrite execR_returnR. reflexivity.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_returnM (E_Load_Access_Fault tt) _)). cbn beta.
    rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_pmaCheck_ram_lr_g (Dr Dw : register -> bool) (aq rl : bool) (k : Z)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s mm
    = true.
Proof.
  intros HD Hmatch Halign HRead.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in HRead |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite HRead. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
                (LoadReserved (aq, rl, Data)) (Physaddr addr) k false s mm
                (goodmb_returnm Dr Dw false s mm) (exec_is_mag_applicable_lr aq rl k s) Halign)
             (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
                (LoadReserved (aq, rl, Data)) (Physaddr addr) k false s
                (exec_is_mag_applicable_lr aq rl k s) Halign).
    cbn beta. cbn match. apply goodmb_returnm.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    gmm_lift (goodmb_returnm (E := exception) Dr Dw (E_Load_Access_Fault tt) s mm)
             (exec_returnM (E_Load_Access_Fault tt) s). cbn beta.
    apply goodmb_returnm.
Qed.

Lemma exec_pmaCheck_ram_sc_g (aq rl : bool) (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok pma_ok_aligned else Err (E_SAMO_Access_Fault tt)), s).
Proof.
  intros Hmatch Halign HWrite.
  unfold pmaCheck. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in HWrite |- *.
  cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)). cbn beta.
  rewrite execR_returnR. cbn match beta.
  rewrite HWrite. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_mag_pma_check_aligned _ _ _ _ _ _ (exec_is_mag_applicable_sc aq rl k s) Halign)).
    cbn beta. cbn match. rewrite execR_returnR. reflexivity.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_returnM (E_SAMO_Access_Fault tt) _)). cbn beta.
    rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_pmaCheck_ram_sc_g (Dr Dw : register -> bool) (aq rl : bool) (k : Z)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s mm
    = true.
Proof.
  intros HD Hmatch Halign HWrite.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in HWrite |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite HWrite. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
                (StoreConditional (aq, rl, Data)) (Physaddr addr) k false s mm
                (goodmb_returnm Dr Dw false s mm) (exec_is_mag_applicable_sc aq rl k s) Halign)
             (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
                (StoreConditional (aq, rl, Data)) (Physaddr addr) k false s
                (exec_is_mag_applicable_sc aq rl k s) Halign).
    cbn beta. cbn match. apply goodmb_returnm.
  - cbn [Riscv.rv64d.not negb]. cbn match.
    gmm_lift (goodmb_returnm (E := exception) Dr Dw (E_SAMO_Access_Fault tt) s mm)
             (exec_returnM (E_SAMO_Access_Fault tt) s). cbn beta.
    apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §5c The reserved pmpCheck grants.  pmpCheckRWX treats LoadReserved/     *)
(*    StoreConditional exactly like Load/Store (R resp. W), so these are   *)
(*    the load/store grants verbatim with the access constructor swapped.  *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant_lr (aq rl : bool) (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (LoadReserved (aq, rl, Data)) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (LoadReserved (aq, rl, Data))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma goodmb_pmpCheck_user_grant_lr (Dr Dw : register -> bool) (aq rl : bool)
    (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (LoadReserved (aq, rl, Data)) User) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HR.
  apply (goodmb_pmpCheck_grant Dr Dw a width (LoadReserved (aq, rl, Data)) User
           s mm HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

Lemma exec_pmpCheck_user_grant_sc (aq rl : bool) (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (StoreConditional (aq, rl, Data)) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HW.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (StoreConditional (aq, rl, Data))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma goodmb_pmpCheck_user_grant_sc (Dr Dw : register -> bool) (aq rl : bool)
    (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (StoreConditional (aq, rl, Data)) User) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HW.
  apply (goodmb_pmpCheck_grant Dr Dw a width (StoreConditional (aq, rl, Data)) User
           s mm HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §5d The LR checked_mem_read RETIRE-OR-FAULT disjunction (widths 4, 8). *)
(*    Ties the pieces together: on a user-mapped, aligned, readable,      *)
(*    PMP-granted RAM address the reserved read either RETIRES with the   *)
(*    bytes ([reservability<>RsrvNone]) or takes the delegated            *)
(*    E_Load_Access_Fault ([reservability=RsrvNone]); a single [if] on    *)
(*    the (unpinned) reservability captures both total outcomes.          *)
(* ===================================================================== *)



(* ===================================================================== *)
(* §5e The LR mem_read wrap (widths 4, 8): threads the mem_read-level      *)
(*    reads (mstatus/cur_privilege/effectivePrivilege, MPRV=0, User) and   *)
(*    the mem_read_priv_meta guard (aligned paddr -> no addr-align fault)  *)
(*    over §5d, giving the retire-or-fault disjunction at mem_read.        *)
(* ===================================================================== *)



(* ===================================================================== *)
(* §5f The aligned vmem_read_addr FAULT path (width-generic): translate    *)
(*    Ok but mem_read Err e -> the loop raises memory_exception (a Trap)   *)
(*    and early-returns, so vmem_read_addr returns Err (Trap ...).  The    *)
(*    complement of exec_vmem_read_addr_aligned (the retire path); the LR  *)
(*    disjunction picks between them on the reserved read's outcome.       *)
(*    (The fault carries the loop's chunk address add_vec_int va (0*w),    *)
(*    matching the retire lemma's translate-premise address form.)         *)
(* ===================================================================== *)

Lemma exec_vmem_read_addr_aligned_err (width : Z) (va pa epa pc : mword 64)
    (e : ExceptionType) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (priv : Privilege) (s s' : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  (* the Err now carries the FAULTING physaddr, and the reported vaddr is
     offset by however far it sits from the access base *)
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s'
    = Some (Err (Physaddr epa, e), s') ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr epa) = Virtaddr va ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e va, pc)), s').
Proof.
  intros Hw Halign Heff Htm Htr Hmr Hoff Hcp Hpc.
  apply (exec_vmem_read_addr_intra_err width va _ acc aq rl res ep md s s'
           (vmem_width_pos _ Hw)
           (exec_split_on_page_boundary_aligned va width s Hw Halign)
           (or_introl Halign) Heff Htm).
  unfold translate_and_read_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hmr). cbn match beta.
  rewrite Hoff.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_memory_exception va pc e priv s' Hcp Hpc)).
  cbn match. apply exec_returnM.
Qed.

Lemma goodmb_vmem_read_addr_aligned_err (Dr Dw : register -> bool) (width : Z)
    (va pa epa pc : mword 64) (e : ExceptionType)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (priv : Privilege) (s s' : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true -> Dr PC = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s'
    = Some (Err (Physaddr epa, e), s') ->
  goodmb Dr Dw (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' mm = true ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr epa) = Virtaddr va ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg Htr Htrg Hmr Hmrg Hoff Hcp Hpc.
  pose proof (exec_split_on_page_boundary_aligned va width s Hw Halign) as Hsplit.
  apply (goodmb_vmem_read_addr_intra_err Dr Dw width va
           (Trap (priv, make_sync_exception e va, pc)) acc aq rl res ep md s s' mm
           HDm HDcp (vmem_width_pos _ Hw) Hsplit
           (goodmb_split_on_page_boundary Dr Dw va width s s (width, 0) mm Hsplit)
           (or_introl Halign) Heff Heffg Htm Htmg).
  - unfold translate_and_read_value.
    rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hmr). cbn match beta.
    rewrite Hoff.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_memory_exception va pc e priv s' Hcp Hpc)).
    cbn match. apply exec_returnM.
  - unfold translate_and_read_value.
    gmm_peel Htrg Htr. cbn match beta.
    gmm_peel Hmrg Hmr. cbn match beta.
    rewrite Hoff.
    gmm_peel (goodmb_memory_exception Dr Dw va pc e priv s' mm HDcp HDpc Hcp Hpc)
             (exec_memory_exception va pc e priv s' Hcp Hpc).
    cbn match. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §5g The vmem-level LR RETIRE-OR-FAULT disjunction (width-generic) --    *)
(*    the instruction-facing statement.  Given the translate (the bundle   *)
(*    absorption supplies it) and the §5e mem_read disjunction, LR either  *)
(*    RETIRES (exists a loaded value) or takes the delegated               *)
(*    E_Load_Access_Fault Trap, selected by the unpinned reservability.    *)
(*    A trivial case-split combining exec_vmem_read_addr_aligned (retire)  *)
(*    and §5f (fault); res=true, aq/rl-generic.                            *)
(* ===================================================================== *)

(* THE ACCESS TYPE'S aq/rl AND THE MEM LEVEL'S ARE NOT THE SAME PAIR.  [LOADRES]
   builds [LoadReserved (aq, rl, Data)] and then calls [vmem_read] with
   [aq, aq & rl]; tying the two together would state a fact about an access the
   model never builds.  So this takes both. *)
Lemma exec_vmem_read_addr_lr_disj (width : Z) (va pa pc : mword 64) (w : mword (8 * width))
    (aq rl maq mrl : bool) (ep : Privilege) (md : SATPMode) (priv : Privilege) (resv : bool)
    (s s' : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege (LoadReserved (aq, rl, Data)) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) (LoadReserved (aq, rl, Data))) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA (Physaddr pa) width maq mrl true) s'
    = Some ((if resv then Ok w else Err (Physaddr pa, E_Load_Access_Fault tt)), s') ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr pa) = Virtaddr va ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  (exists dvv : mword (8 * width),
     exec (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) maq mrl true) s
       = Some (Ok dvv, s'))
  \/ exec (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) maq mrl true) s
       = Some (Err (Trap (priv, make_sync_exception (E_Load_Access_Fault tt) va, pc)), s').
Proof.
  intros Hw Halign Heff Htm Htr Hmr Hoff Hcp Hpc.
  destruct resv.
  - left. exact (exec_vmem_read_addr_aligned width va pa w (LoadReserved (aq, rl, Data))
                   maq mrl true ep md s s' Hw Halign Heff Htm Htr Hmr).
  - right. exact (exec_vmem_read_addr_aligned_err width va pa pa pc (E_Load_Access_Fault tt)
                    (LoadReserved (aq, rl, Data)) maq mrl true ep md priv s s'
                    Hw Halign Heff Htm Htr Hmr Hoff Hcp Hpc).
Qed.

(* the twin is UNCONDITIONAL: the certificate does not depend on which of the
   two total outcomes the (unpinned) reservability selects. *)
Lemma goodmb_vmem_read_addr_lr_disj (Dr Dw : register -> bool) (width : Z)
    (va pa pc : mword 64) (w : mword (8 * width)) (aq rl maq mrl : bool)
    (ep : Privilege) (md : SATPMode) (priv : Privilege) (resv : bool)
    (s s' : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true -> Dr PC = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege (LoadReserved (aq, rl, Data)) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege (LoadReserved (aq, rl, Data))
          (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr va) (LoadReserved (aq, rl, Data))) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr va) (LoadReserved (aq, rl, Data))) s mm = true ->
  exec (mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA (Physaddr pa) width maq mrl true) s'
    = Some ((if resv then Ok w else Err (Physaddr pa, E_Load_Access_Fault tt)), s') ->
  goodmb Dr Dw (mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA (Physaddr pa) width maq mrl true)
    s' mm = true ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr pa) = Virtaddr va ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) maq mrl true)
    s mm = true.
Proof.
  intros HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg Htr Htrg Hmr Hmrg Hoff Hcp Hpc.
  destruct resv.
  - exact (goodmb_vmem_read_addr_aligned Dr Dw width va pa w (LoadReserved (aq, rl, Data))
             maq mrl true ep md s s' mm HDm HDcp Hw Halign Heff Heffg Htm Htmg
             Htr Htrg Hmr Hmrg).
  - exact (goodmb_vmem_read_addr_aligned_err Dr Dw width va pa pa pc
             (E_Load_Access_Fault tt) (LoadReserved (aq, rl, Data)) maq mrl true
             ep md priv s s' mm HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg
             Htr Htrg Hmr Hmrg Hoff Hcp Hpc).
Qed.

(* ===================================================================== *)
(* §5h The SC checked_mem_write RETIRE-OR-FAULT disjunction (widths 4, 8). *)
(*    The write mirror of §5d: on a user-mapped, aligned, writable,        *)
(*    PMP-granted RAM address the conditional write LANDS (Ok true, bytes  *)
(*    written) when reservability<>RsrvNone, else takes the delegated      *)
(*    E_SAMO_Access_Fault (state unchanged) -- one [if] on the unpinned    *)
(*    reservability over both the result AND the post-state.  Uses         *)
(*    MemAmo4's exec_write_ram_cond_4 and the new exec_write_ram_cond_8    *)
(*    (the width-8 conditional write atom -- the value-projection needs an  *)
(*    extra [cbn [Mem_write_request_value]] + [iMon_bind] vs the width-4). *)
(* ===================================================================== *)




(* ===================================================================== *)
(* §5i The SC mem_write_value wrap (widths 4, 8): the write mirror of §5e  *)
(*    -- threads mstatus/cur_privilege/effectivePrivilege (MPRV=0, User)   *)
(*    and the mem_write_value_priv_meta paddr-alignment guard over §5h,     *)
(*    giving the retire-or-fault disjunction at mem_write_value (Ok true +  *)
(*    write-state / Err E_SAMO_Access_Fault + unchanged state).            *)
(* ===================================================================== *)



(* ===================================================================== *)
(* §5j The vmem-level SC FAULT path (reservability = RsrvNone).  BOTH      *)
(*    match_reservation branches fault: mr=true takes the write branch     *)
(*    where mem_write_value returns Err E_SAMO (§5i =None), mr=false takes  *)
(*    the check branch where phys_access_check denies (§5b =None); each     *)
(*    raises memory_exception and early-returns, so vmem_write_addr returns *)
(*    Err (Trap E_SAMO).  The complement of exec_vmem_write_addr_sc.        *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_sc_fault (width : Z) (va pa epa pc : mword 64)
    (dat : mword (8*width)) (aq rl maq mrl : bool) (ep ep' : Privilege) (md : SATPMode)
    (s s' : mstate) :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  (* mr = true: the ea lands, the write faults *)
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (Err (Physaddr epa, E_SAMO_Access_Fault tt), s') ->
  (* mr = false: the re-check denies *)
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some (Err (E_SAMO_Access_Fault tt), s') ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr epa) = Virtaddr va ->
  exec (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s
    = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) va, pc)), s').
Proof.
  intros acc wv Hw Halign Heff Htm Htr Hcp Hpc Hea Hwv Heff' Hpac Hoff.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_split_on_page_boundary_aligned va width s Hw Halign)).
  cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?IF) ?k] =>
    assert (Hsc : execR (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s'
                  = Some (inr tt, s'))
      by (rewrite execR_liftR; reflexivity);
    assert (Hbr : execR (Defs.bind0 (Defs.liftR asrt) IF) s'
                  = Some (inl (Err (Trap (User,
                            make_sync_exception (E_SAMO_Access_Fault tt) va, pc))), s')) end.
  { rewrite (execR_bind0_Some _ _ _ _ Hsc).
    destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match beta.
      rewrite Hoff.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_memory_exception va pc (E_SAMO_Access_Fault tt) User s' Hcp Hpc)).
      cbn match. reflexivity.
    - cbn [Riscv.rv64d.not negb andb].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Heff'). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpac). cbn match beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_memory_exception va pc (E_SAMO_Access_Fault tt) User s' Hcp Hpc)).
      cbn match. reflexivity. }
  rewrite execR_bind. rewrite Hbr. reflexivity.
Qed.

Lemma goodmb_vmem_write_addr_sc_fault (Dr Dw : register -> bool) (width : Z)
    (va pa epa pc : mword 64) (dat : mword (8*width)) (aq rl maq mrl : bool)
    (ep ep' : Privilege) (md : SATPMode) (s s' : mstate) mm :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  Dr mstatus = true -> Dr cur_privilege = true -> Dr PC = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s mm = true ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (Err (Physaddr epa, E_SAMO_Access_Fault tt), s') ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' mm = true ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some (Err (E_SAMO_Access_Fault tt), s') ->
  goodmb Dr Dw (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s' mm = true ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr epa) = Virtaddr va ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s mm = true.
Proof.
  intros acc wv HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg Htr Htrg Hcp Hpc
         Hea Heag Hwv Hwvg Heff' Heff'g Hpac Hpacg Hoff.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  assert (Hms' : goodmb Dr Dw (Defs.read_reg mstatus : M _) s' mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpg' : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s' mm = true)
    by (rewrite goodmb_read_reg; exact HDcp).
  pose proof (goodmb_memory_exception Dr Dw va pc (E_SAMO_Access_Fault tt) User s' mm
                HDcp HDpc Hcp Hpc) as Hmeg.
  pose proof (exec_memory_exception va pc (E_SAMO_Access_Fault tt) User s' Hcp Hpc) as Hme.
  unfold vmem_write_addr.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  erewrite gm_cer_bind0; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn [bits_of_virtaddr]. cbn zeta.
  pose proof (exec_split_on_page_boundary_aligned va width s Hw Halign) as Hsplit.
  gmm_lift (goodmb_split_on_page_boundary Dr Dw va width s s (width, 0) mm Hsplit) Hsplit.
  cbn beta zeta match.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpg (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s));
    [ | assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_cer_bind; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn beta zeta.
  gmm_lift Htrg Htr. cbn match beta.
  match goal with |- context[Defs.assert_exp (Bool.eqb ?r ?x) ?msg] =>
    set (b := Bool.eqb r x);
    assert (Hae : exec (Defs.assert_exp b msg) s' = Some (tt, s'))
      by (subst b; apply exec_returnm);
    assert (Haeg : goodmb Dr Dw (Defs.assert_exp b msg : M unit) s' mm = true)
      by (subst b; apply goodmb_returnm)
  end.
  subst b.
  unfold Defs.bind0.
  gmm_lift Haeg Hae.
  destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr.
  - cbn [Riscv.rv64d.not negb andb].
    gmm_lift Heag Hea. cbn match beta.
    gmm_lift Hwvg Hwv. cbn match beta.
    rewrite Hoff.
    gmm_lift Hmeg Hme. cbn match beta.
    rewrite mcer_early_return_nest. apply goodmb_returnm.
  - cbn [Riscv.rv64d.not negb andb].
    gmm_lift Hms' (exec_read_reg mstatus s'). cbn beta.
    gmm_lift Hcpg' (exec_read_reg cur_privilege s'). cbn beta.
    gmm_lift Heff'g Heff'. cbn beta.
    gmm_lift Hpacg Hpac. cbn match beta.
    gmm_lift Hmeg Hme. cbn match beta.
    rewrite mcer_early_return_nest. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §5k The vmem-level SC RETIRE-OR-FAULT disjunction (width-generic) --    *)
(*    the instruction-facing SC statement.  Given the translate and the    *)
(*    §5i/§5b physical disjunctions, SC either RETIRES (Ok of              *)
(*    match_reservation: the write lands iff the reservation is still      *)
(*    valid) or takes the delegated E_SAMO_Access_Fault Trap, selected by  *)
(*    the unpinned reservability.  A case-split combining                  *)
(*    exec_vmem_write_addr_sc (retire) and §5j (fault).                    *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_sc_disj (width : Z) (va pa pc : mword 64) (dat : mword (8*width))
    (aq rl maq mrl : bool) (ep ep' : Privilege) (md : SATPMode) (plan : Phys_Mem_Access_Info)
    (resv : bool) (s s' : mstate) :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (if resv
            then (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev))
            else (Err (Physaddr pa, E_SAMO_Access_Fault tt), s')) ->
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some ((if resv then Ok plan else Err (E_SAMO_Access_Fault tt)), s') ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr pa) = Virtaddr va ->
  (exec (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s
     = Some (Ok (match_reservation (bits_of_physaddr (Physaddr pa))),
             if match_reservation (bits_of_physaddr (Physaddr pa))
             then MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)
             else s'))
  \/ exec (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s
       = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) va, pc)), s').
Proof.
  intros acc wv Hw Halign Heff Htm Htr Hmprv Hcp Hpc Hea Hwv Heff' Hpac Hoff.
  destruct resv; cbn match in Hwv, Hpac.
  - left. exact (exec_vmem_write_addr_sc width va pa dat aq rl maq mrl ep ep' md plan s s'
                   (MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev))
                   Hw Halign Heff Htm Htr Hea Hwv Heff' Hpac).
  - right. exact (exec_vmem_write_addr_sc_fault width va pa pa pc dat aq rl maq mrl ep ep' md s s'
                    Hw Halign Heff Htm Htr Hcp Hpc Hea Hwv Heff' Hpac Hoff).
Qed.

(* the twin is UNCONDITIONAL: the certificate does not depend on which of the
   two total outcomes the (unpinned) reservability selects. *)
Lemma goodmb_vmem_write_addr_sc_disj (Dr Dw : register -> bool) (width : Z)
    (va pa pc : mword 64) (dat : mword (8*width)) (aq rl maq mrl : bool)
    (ep ep' : Privilege) (md : SATPMode) (plan : Phys_Mem_Access_Info)
    (resv : bool) (s s' : mstate) mm :
  let acc := StoreConditional (aq, rl, Data) in
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*width-1) 0)
            : mword (8 * width) in
  Dr mstatus = true -> Dr cur_privilege = true -> Dr PC = true ->
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (bits_of_virtaddr (Virtaddr va))) acc) s mm = true ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s'
    = Some (if resv
            then (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev))
            else (Err (Physaddr pa, E_SAMO_Access_Fault tt), s')) ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width wv acc PBMT_PMA maq mrl true) s' mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' mm = true ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some ((if resv then Ok plan else Err (E_SAMO_Access_Fault tt)), s') ->
  goodmb Dr Dw (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s' mm = true ->
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr pa) = Virtaddr va ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat acc maq mrl true) s mm = true.
Proof.
  intros acc wv HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg Htr Htrg Hmprv Hcp Hpc
         Hea Heag Hwv Hwvg Heff' Heff'g Hpac Hpacg Hoff.
  destruct resv; cbn match in Hwv, Hpac.
  - exact (goodmb_vmem_write_addr_sc Dr Dw width va pa dat aq rl maq mrl ep ep' md
             plan s s'
             (MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev))
             mm HDm HDcp Hw Halign Heff Heffg Htm Htmg Htr Htrg
             Hea Heag Hwv Hwvg Heff' Heff'g Hpac Hpacg).
  - exact (goodmb_vmem_write_addr_sc_fault Dr Dw width va pa pa pc dat aq rl maq mrl
             ep ep' md s s' mm HDm HDcp HDpc Hw Halign Heff Heffg Htm Htmg Htr Htrg
             Hcp Hpc Hea Heag Hwv Hwvg Heff' Heff'g Hpac Hpacg Hoff).
Qed.

(* ===================================================================== *)
(* §6 The iris BUNDLE COMPOSERS over the user invariant (utlb_inv_pt +     *)
(*    udata_own).  These thread the translate through the                 *)
(*    utlb_inv_pt_translateAddr_u absorption and the reserved physical     *)
(*    access through §5, re-establishing the invariant, and expose the     *)
(*    instruction-facing retire-or-fault DISJUNCTION for LR/SC.  Same      *)
(*    shape as §2's aligned LOAD/STORE composers.  Widths 4/8 (LR.W/LR.D,  *)
(*    SC.W/SC.D); the reserved physical bricks are per-width (§5).         *)
(*                                                                        *)
(* §6a LR (LoadReserved, aq=rl=false): absorb the translate, read the      *)
(*    reserved word (§5e disjunction), and apply §5g -- LR either retires  *)
(*    with a value or takes E_Load_Access_Fault, per the region's          *)
(*    (unpinned) reservability.                                            *)
(* ===================================================================== *)

Section UserMemAccessBundle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.



End UserMemAccessBundle.

(* ===================================================================== *)
(* §6b SC (StoreConditional, aq=rl=false): absorb the translate, run the   *)
(*    §5i mem_write_value disjunction + the phys_access_check disjunction   *)
(*    through §5k.  The write is conditional on the opaque match_reservation *)
(*    so the GHOST write (udata_own_store_g) fires only on the mr=true      *)
(*    retire sub-case; mr=false retires without writing, and reservability  *)
(*    =RsrvNone faults to E_SAMO.  The post-state's memory is threaded per  *)
(*    case (write_bytes iff the write landed).                             *)
(* ===================================================================== *)

(* width-8 conditional mem_write_ea, for the SC.D bundle composer *)

Section UserMemAccessBundleSC.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.



End UserMemAccessBundleSC.

(* ===================================================================== *)
(* §7 The MISALIGNED-SPLIT bundle composer over the user invariant.       *)
(*    The last memory-layer piece: threads the N chunk translates through *)
(*    the utlb_inv_pt_translateAddr_u absorption (looping                 *)
(*    user_pt_load_data_g at width [bytes] and the chunk address), then    *)
(*    feeds the collected per-chunk translate/read facts to §4b to reduce *)
(*    the misaligned plain LOAD.  [sst] is the deterministic per-chunk     *)
(*    state (a fixpoint over the exec), [spa]/[sval] the closed-form       *)
(*    physical address / read value; [split_load_fold] is the N-fold      *)
(*    absorption induction (config_ok preserved across each absorption;    *)
(*    data bytes are A/D-stable so reads are consistent).  Within-page     *)
(*    coverage: the caller supplies um !! svpn_of (chunk k) = Some w for   *)
(*    every chunk.  This is the single-absorption §6 pattern generalized   *)
(*    to N chunks.                                                         *)
(* ===================================================================== *)

Section SplitLoadBundle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)).
  Context (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hread_plain : forall (addr : mword 64) (ww : mword (8 * bytes)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N bytes)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte ww j)) ->
      exec (read_ram Read_plain (Physaddr addr) bytes false) s = Some ((ww, default_meta), s)).
  Context (Hwrite_plain : forall (addr : mword 64) (dd : mword (8 * bytes)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) bytes dd tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N bytes) dd) s.(mdev))).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
          (data : gset Arch.pa) (w va : mword 64).




  Context (σ0 : mstate).





End SplitLoadBundle.

(* ===================================================================== *)
(* §8 The MISALIGNED-SPLIT STORE bundle composer.  The write analog of §7: *)
(*    split_store_fold loops user_pt_store_data_g per chunk, threading the *)
(*    invariant + udata + config across N chunk translates AND ghost       *)
(*    writes (two-level per-chunk state: [sttS k] post-translate,          *)
(*    [sstS (S k)] post-write; each chunk's write updates udata via         *)
(*    udata_own_store_g inside user_pt_store_data_g).  [wv] is the abstract *)
(*    per-chunk write value; the composer relates it to the model's own    *)
(*    subrange slices of the full store data [dat] (Hwvdef), matching §4c's *)
(*    internal wv, and derives mem_write_ea via exec_mem_write_ea_g.  The   *)
(*    per-chunk successes are all [true] (RAM), so ws_seq N = true.  This   *)
(*    completes the misaligned-split bundle layer for BOTH directions --    *)
(*    the memory layer is now wired end-to-end to the user invariant.      *)
(*    (Locals suffixed S to avoid clash with §7's section-global defs.)     *)
(* ===================================================================== *)

Section SplitStoreBundle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)).
  Context (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hwrite_plain : forall (addr : mword 64) (dd : mword (8 * bytes)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) bytes dd tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N bytes) dd) s.(mdev))).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
          (data : gset Arch.pa) (w va : mword 64) (wv : nat -> mword (8 * bytes)).




  Context (σ0 : mstate).




End SplitStoreBundle.

(* ===================================================================== *)
(* §9 The U-mode data-address transform (memory-arm foundation).  Every   *)
(*    U-mode data access (execute_LOAD/STORE/AMO/LR/SC via vmem_read /     *)
(*    vmem_write) first runs transform_effective_address on the           *)
(*    rs1+offset effective address.  At User with MPRV=0 and pointer       *)
(*    masking disabled (pmlen=0), the transform is the IDENTITY (Sv39 ->   *)
(*    pm_transform_VA_0, or Bare -> pm_transform_PA_0), so the va the      *)
(*    §2/§6/§7/§8 composers consume is exactly rs1+offset.  U-mode analog  *)
(*    of SRegime.exec_transform_effective_address_mode (Supervisor).       *)
(* ===================================================================== *)

Lemma exec_transform_effective_address_u (acc : MemoryAccessType mem_payload)
    (md : SATPMode) (ea : mword 64) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s
    = Some (User, s) ->
  exec (get_pmlen acc User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  exec (transform_effective_address (Virtaddr ea) acc) s = Some (Virtaddr ea, s).
Proof.
  intros Hcp Heff Hpml Htm.
  unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ Heff).
  rewrite (exec_bind_Some _ _ _ _ _ Hpml).
  rewrite (exec_bind_Some _ _ _ _ _ Htm).
  destruct (generic_eq md Bare);
    [ rewrite pm_transform_PA_0 | rewrite pm_transform_VA_0 ];
    apply exec_returnM.
Qed.

Lemma goodmb_transform_effective_address_u (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (md : SATPMode) (ea : mword 64)
    (s : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s
    = Some (User, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s mm
    = true ->
  exec (get_pmlen acc User) s = Some (0, s) ->
  goodmb Dr Dw (get_pmlen acc User) s mm = true ->
  exec (translationMode User) s = Some (md, s) ->
  goodmb Dr Dw (translationMode User) s mm = true ->
  goodmb Dr Dw (transform_effective_address (Virtaddr ea) acc) s mm = true.
Proof.
  intros HDm HDcp Hcp Heff Heffg Hpml Hpmlg Htm Htmg.
  unfold transform_effective_address.
  gmm_rr mstatus HDm.
  gmm_rr cur_privilege HDcp.
  rewrite Hcp.
  gmm_peel Heffg Heff.
  gmm_peel Hpmlg Hpml.
  gmm_peel Htmg Htm.
  destruct (generic_eq md Bare);
    [ rewrite pm_transform_PA_0 | rewrite pm_transform_VA_0 ];
    apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §5b THE LR/SC PMA BRICKS, restated for the bump.  [pmaCheck] answers a   *)
(*     PLAN now, and the LR/SC arms are the ones that gate on               *)
(*     [PMA_reservability]: on a user-mapped, aligned, R/W address the       *)
(*     access either RETIRES (reservability set -- the plan is the aligned   *)
(*     one, since the whole splitting axis is inert for an aligned access)   *)
(*     or takes an ACCESS FAULT (reservability = RsrvNone).  The access      *)
(*     type carries the instruction's aq/rl now; nothing in the PMA path     *)
(*     inspects them, so these are generic in both.                          *)
(* ===================================================================== *)

Lemma exec_pmaCheck_ram_lr_ok (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (aq rl : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = true ->
  exec (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Hfield Halign.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Halign (exec_is_mag_applicable_lr aq rl k s) Hfield.
Qed.

Lemma goodmb_pmaCheck_ram_lr_ok (Dr Dw : register -> bool) (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (aq rl : bool) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s mm = true.
Proof.
  intros HD Hmatch Hfield Halign.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Halign |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite Halign. cbn [Riscv.rv64d.not negb]. cbn match.
  gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
              (LoadReserved (aq, rl, Data)) (Physaddr addr) k false s mm
              (goodmb_returnm Dr Dw false s mm) (exec_is_mag_applicable_lr aq rl k s) Hfield)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (LoadReserved (aq, rl, Data)) (Physaddr addr) k false s
              (exec_is_mag_applicable_lr aq rl k s) Hfield).
  cbn beta. cbn match. apply goodmb_returnm.
Qed.

Lemma exec_pmaCheck_ram_sc_ok (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (aq rl : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = true ->
  exec (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Hfield Halign.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Halign (exec_is_mag_applicable_sc aq rl k s) Hfield.
Qed.

Lemma goodmb_pmaCheck_ram_sc_ok (Dr Dw : register -> bool) (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (aq rl : bool) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s mm = true.
Proof.
  intros HD Hmatch Hfield Halign.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Halign |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite Halign. cbn [Riscv.rv64d.not negb]. cbn match.
  gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
              (StoreConditional (aq, rl, Data)) (Physaddr addr) k false s mm
              (goodmb_returnm Dr Dw false s mm) (exec_is_mag_applicable_sc aq rl k s) Hfield)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (StoreConditional (aq, rl, Data)) (Physaddr addr) k false s
              (exec_is_mag_applicable_sc aq rl k s) Hfield).
  cbn beta. cbn match. apply goodmb_returnm.
Qed.

(* ...and the DENIAL arm: reservability = RsrvNone, so [pmaCheck] answers the
   access fault its access type maps to.  (This is the peel [pma_ok_peel] does
   not do -- it takes the [canAccess] branch instead of the [mag_pma_check]
   one.) *)
Lemma exec_pmaCheck_ram_lr_deny (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (aq rl : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = false ->
  exec (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s
    = Some (Err (E_Load_Access_Fault tt), s).
Proof.
  intros Hmatch Hfield.
  destruct region as [rbase rsize rattr rdtree].
  unfold pmaCheck. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)). cbn beta.
  rewrite Hmatch.
  cbn [PMA_Region_attributes] in Hfield |- *.
  cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)). cbn beta.
  rewrite execR_returnR. cbn match beta.
  rewrite Hfield. cbn [Riscv.rv64d.not negb]. cbn match zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (accessFaultFromAccessType (LoadReserved (aq, rl, Data))) s
                  = Some (E_Load_Access_Fault tt, s))).
  2:{ unfold accessFaultFromAccessType. cbn match. apply exec_returnM. }
  cbn beta. rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_pmaCheck_ram_lr_deny (Dr Dw : register -> bool) (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (aq rl : bool) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = false ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (LoadReserved (aq, rl, Data)) pbmt true) s mm = true.
Proof.
  intros HD Hmatch Hfield.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  destruct region as [rbase rsize rattr rdtree].
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  cbn [PMA_Region_attributes] in Hfield |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite Hfield. cbn [Riscv.rv64d.not negb]. cbn match zeta.
  gmm_lift (goodmb_returnm (E := exception) Dr Dw (E_Load_Access_Fault tt) s mm)
           (exec_returnM (E_Load_Access_Fault tt) s). cbn beta.
  apply goodmb_returnm.
Qed.

Lemma exec_pmaCheck_ram_sc_deny (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (aq rl : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = false ->
  exec (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s
    = Some (Err (E_SAMO_Access_Fault tt), s).
Proof.
  intros Hmatch Hfield.
  destruct region as [rbase rsize rattr rdtree].
  unfold pmaCheck. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)). cbn beta.
  rewrite Hmatch.
  cbn [PMA_Region_attributes] in Hfield |- *.
  cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)). cbn beta.
  rewrite execR_returnR. cbn match beta.
  rewrite Hfield. cbn [Riscv.rv64d.not negb]. cbn match zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (accessFaultFromAccessType (StoreConditional (aq, rl, Data))) s
                  = Some (E_SAMO_Access_Fault tt, s))).
  2:{ unfold accessFaultFromAccessType. cbn match. apply exec_returnM. }
  cbn beta. rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_pmaCheck_ram_sc_deny (Dr Dw : register -> bool) (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (aq rl : bool) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = false ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (StoreConditional (aq, rl, Data)) pbmt true) s mm = true.
Proof.
  intros HD Hmatch Hfield.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  destruct region as [rbase rsize rattr rdtree].
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  cbn [PMA_Region_attributes] in Hfield |- *.
  cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' true ?msg] =>
    gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end.
  cbn beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite Hfield. cbn [Riscv.rv64d.not negb]. cbn match zeta.
  gmm_lift (goodmb_returnm (E := exception) Dr Dw (E_SAMO_Access_Fault tt) s mm)
           (exec_returnM (E_SAMO_Access_Fault tt) s). cbn beta.
  apply goodmb_returnm.
Qed.

(* the exception vaddr an access-fault at the access's OWN base reports is the
   access's own vaddr: [offset_virtaddr_by] adds the paddr difference, which is
   zero.  (The bump gave [MemoryOpResult]'s [Err] an address, and this is what
   the vmem level does with it.) *)
Lemma offset_virtaddr_by_self (va pa : mword 64) :
  offset_virtaddr_by (Virtaddr va) (Physaddr pa) (Physaddr pa) = Virtaddr va.
Proof.
  unfold offset_virtaddr_by.
  assert (Hz : sub_vec pa pa = (zeros' 64 : mword 64)).
  { apply bv_eq. rewrite sub_vec64_unsigned. rewrite Z.sub_diag.
    change (bv_unsigned (zeros' 64 : mword 64)) with 0.
    apply bv_wrap_small. rewrite bv_modulus64. lia. }
  rewrite Hz.
  assert (Hs : subrange_vec_dec (zeros' 64 : mword 64) (Z.sub xlen 1) 0 = (zeros' 64 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hs. f_equal.
  change (add_vec va (zeros' 64 : mword 64)) with (add_vec_int va 0).
  apply avi0.
Qed.

(* THE AMO PMA BRICK -- PORT PENDING.  Same shape as the LR/SC pair:
 *
 *   Lemma exec_pmaCheck_ram_amo_ok (k : Z) (addr : mword 64) (pbmt) (region)
 *       (op : amoop) (aq rl : bool) s :
 *     matching_pma_region … = Some region ->
 *     is_aligned_paddr (Physaddr addr) k = true ->
 *     andb readable (andb writable (pma_allows_atomic_op atomic_support op k)) = true ->
 *     exec (pmaCheck (Physaddr addr) k (Atomic (op, aq, rl, Data, Data)) pbmt true) s
 *       = Some (Ok pma_ok_aligned, s).
 *
 * [pma_allows_all] pins all three conjuncts for every op and width, so the
 * hypothesis is dischargeable at every call site.  What does NOT work is
 * closing it with [pma_ok_peel]: the tactic's assert-arm fires (the AMO arm of
 * [pmaCheck] does open with [assert_exp' res_or_con]) but its
 * [rewrite execR_bind; rewrite (execR_liftR_seq … (exec_assert_exp'_true …))]
 * then reports "does not match any subterm", so the AMO arm reaches that point
 * in a different shape than the LR/SC ones.  Print the goal after
 * [pma_ok_peel]'s [cbn match] and adjust the arm peel -- most likely
 * [pma_allows_atomic_op] needs holding back from the [cbn].
 *)
