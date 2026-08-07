(* MemAccessGen.v -- privilege-agnostic, width-generic memory-access
   reductions shared by the user-mode and S-mode stacks.  These lemmas take the
   access type / privilege as parameters, so they belong to neither regime;
   they previously lived in UserMemAccess / UserMemPt, which forced the S-mode
   stack (WpSmodeMemGen) to depend on user-mode files.  Hosted here, before both
   the user-mode and S-mode memory layers. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpLoad.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.   (* vmem_width, the page-split kit, pma_ok_aligned *)
Local Open Scope Z_scope.
Import Defs.

(* [vmem_write_addr] is a straight-line body now: the vmem level splits on a
   PAGE boundary (the MAG split moved down into [checked_mem_write]), and an
   aligned in-page access takes neither split arm.  [do_split_access] is false
   because the page split leaves no next-page bytes -- which is why this lemma
   needs no fact about the translation mode, only that the effective privilege
   and its translation mode are DEFINED at [s] (the and_boolM evaluates its left
   operand before short-circuiting on the right). *)
(* ...and the write's TRANSLATE-fault path. *)
Lemma exec_vmem_write_addr_intra_terr (width : Z) (va : mword 64) (dat : mword (8*width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (e : ExceptionType)
    (er : ExecutionResult) (ep : Privilege) (md : SATPMode) s s2 :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s2) ->
  exec (memory_exception (Virtaddr va) e) s2 = Some (er, s2) ->
  exec (vmem_write_addr (Virtaddr va) width dat acc aq rl res) s = Some (Err er, s2).
Proof.
  intros Hpos Hsplit Hguard Heff Htm Htr Hme.
  unfold vmem_write_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
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
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hme). cbn match beta.
  reflexivity.
Qed.

(* THE VMEM WRITE, aligned or not -- the store counterpart of
   [exec_vmem_read_addr_intra], and the same two premises replace the
   alignment requirement. *)
Lemma exec_vmem_write_addr_intra (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (ep : Privilege) (md : SATPMode) (s s' sfin : mstate) :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception (Store Data) false = None) ->
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
  intros Hpos Hsplit Hguard Heff Htm Htr Hea Hwv.
  set (sw := sfin).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit).
  cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  (* do_split_access: the page split left zero next-page bytes *)
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); [ apply execR_returnR_fwd | apply execR_returnR_fwd ]. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
  match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
    assert (Hsc : execR (Defs.liftR asrt
                         : Defs.monadR (result bool ExecutionResult) exception unit) s'
                  = Some (inr tt, s'))
      by (rewrite execR_liftR; reflexivity) end.
  match goal with
  | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
      assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s' = Some (inr true, sw))
  end.
  { match goal with |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody) end.
    rewrite (execR_bind0_Some _ _ _ _ Hsc).
    unfold NN; clear NN.
    match goal with
    | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
        change (execR B ss = R)
    end.
    rewrite (execR_liftR_seq _ _ _ _ _ Hea).
    cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
    cbn match. apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
  cbn. reflexivity.
Qed.

Lemma exec_vmem_write_addr_aligned_store (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (ep : Privilege) (md : SATPMode) (s s' sfin : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
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
  intros Hw Halign Heff Htm Htr Hea Hwv.
  apply (exec_vmem_write_addr_intra width va pa dat ep md s s' sfin
           (vmem_width_pos _ Hw)
           (exec_split_on_page_boundary_aligned va width s Hw Halign)
           (or_introl Halign) Heff Htm Htr Hea Hwv).
Qed.

(* The READ counterpart of [exec_vmem_write_addr_aligned_store], and the brick
   it is built from.  [translate_and_read_value] is just translate-then-read;
   [vmem_read_addr] wraps it in the page split, which an aligned in-page access
   does not take, so the accumulator [zeros'] is overwritten in full and the
   result is the value itself ([usvd_zeros_full_gen]). *)
Lemma exec_translate_and_read_value_gen (width : Z) (va pa : mword 64)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (pbmt : page_based_mem_type) (v : mword (8*width)) s s1 s2 :
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, pbmt, init_ext_ptw), s1) ->
  exec (mem_read acc pbmt (Physaddr pa) width aq rl res) s1 = Some (Ok v, s2) ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Ok (Physaddr pa, v), s2).
Proof.
  intros Htr Hmr.
  unfold translate_and_read_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hmr). cbn match beta.
  apply exec_returnM.
Qed.

Lemma exec_translate_and_read_value_g (width : Z) (va pa : mword 64)
    (pbmt : page_based_mem_type) (v : mword (8*width)) s s1 s2 :
  exec (translateAddr (Virtaddr va) (Load Data)) s
    = Some (Ok (Physaddr pa, pbmt, init_ext_ptw), s1) ->
  exec (mem_read (Load Data) pbmt (Physaddr pa) width false false false) s1
    = Some (Ok v, s2) ->
  exec (translate_and_read_value (Virtaddr va) width (Load Data) false false false) s
    = Some (Ok (Physaddr pa, v), s2).
Proof.
  intros Htr Hmr.
  unfold translate_and_read_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hmr). cbn match beta.
  apply exec_returnM.
Qed.

(* THE VMEM READ, aligned or not.  The bump moved the misalignment split OUT
   of this layer: [vmem_read_addr] splits only across a PAGE boundary, and the
   MAG/alignment split moved down into [checked_mem_read].  So an IN-PAGE
   access -- aligned or misaligned -- performs exactly ONE
   [translate_and_read_value] of the full width, and this one lemma covers
   both.  The two premises that replace the old alignment requirement:

     [Hsplit]  the page split leaves no next-page bytes (the access is
               within one page), and
     [Hguard]  either the access IS aligned, or the platform raises no
               misalignment exception for it (true for plain load/store,
               false for LR/SC/AMO -- which is why those stay aligned). *)
Lemma exec_vmem_read_addr_intra (width : Z) (va pa : mword 64)
    (v : mword (8*width)) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) s s2 :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Ok (Physaddr pa, v), s2) ->
  (res = true ->
   exec (load_reservation (bits_of_physaddr (Physaddr pa)) width) s2 = Some (tt, s2)) ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s = Some (Ok v, s2).
Proof.
  intros Hpos Hsplit Hguard Heff Htm Htrv Hlr.
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit).
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
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * width)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv). cbn match beta.
  replace (Z.eqb width width) with true by (symmetry; apply Z.eqb_refl).
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hif : execR IF s2 = Some (inr tt, s2)) end.
  { destruct res.
    - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s2)). cbn beta.
      rewrite execR_liftR. rewrite (Hlr eq_refl). reflexivity.
    - apply execR_returnR_fwd. }
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseq : execR (Defs.bind0 IF rr) s2
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * width))
                                  (8 * width - 1) 0 (autocast (T := mword) v)), s2)) end.
  { rewrite (execR_bind0_Some _ _ _ _ Hif). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta.
  rewrite (usvd_zeros_full_gen (8 * width) v ltac:(lia)).
  rewrite andb_false_r. cbn match beta.
  reflexivity.
Qed.

(* ...and its FAULT complement: the read faults, the loop raises the exception
   and early-returns, so the whole vmem read is that Err.  Same two premises
   in place of alignment. *)
Lemma exec_vmem_read_addr_intra_err (width : Z) (va : mword 64)
    (er : ExecutionResult) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) s s2 :
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Err er, s2) ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s = Some (Err er, s2).
Proof.
  intros Hpos Hsplit Hguard Heff Htm Htrv.
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit).
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
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * width)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv). cbn match beta.
  reflexivity.
Qed.

(* The res-GENERIC aligned vmem read: LOAD (res=false) and LR (res=true) both
   go through it.  On the LR side the model asserts [width = access_width]
   (trivial once the page split is inert) and then takes the reservation, which
   is a platform effect the caller supplies. *)
Lemma exec_vmem_read_addr_aligned_gen (width : Z) (va pa : mword 64)
    (v : mword (8*width)) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) s s2 :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Ok (Physaddr pa, v), s2) ->
  (res = true ->
   exec (load_reservation (bits_of_physaddr (Physaddr pa)) width) s2 = Some (tt, s2)) ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s = Some (Ok v, s2).
Proof.
  intros Hw Halign Heff Htm Htrv Hlr.
  apply (exec_vmem_read_addr_intra width va pa v acc aq rl res ep md s s2
           (vmem_width_pos _ Hw)
           (exec_split_on_page_boundary_aligned va width s Hw Halign)
           (or_introl Halign) Heff Htm Htrv Hlr).
Qed.

Lemma exec_vmem_read_addr_aligned_load (width : Z) (va pa : mword 64)
    (v : mword (8*width)) (ep : Privilege) (md : SATPMode) s s' :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translate_and_read_value (Virtaddr va) width (Load Data) false false false) s
    = Some (Ok (Physaddr pa, v), s') ->
  exec (vmem_read_addr (Virtaddr va) width (Load Data) false false false) s
    = Some (Ok v, s').
Proof.
  intros Hw Halign Heff Htm Htrv.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_on_page_boundary_aligned va width s Hw Halign)).
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
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * width)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv). cbn match beta.
  rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s')). cbn beta zeta.
  rewrite (usvd_zeros_full_gen (8 * width) v ltac:(lia)).
  reflexivity.
Qed.

(* [mem_write_ea] resolves the effective privilege, runs the PMA/PMP check and
   walks the same one-iteration split loop as [checked_mem_write], announcing the
   write address per split ([write_ram_ea], a state no-op).  Width-generic, with
   the two checks taken abstractly. *)
Lemma exec_mem_write_ea_g (width : Z) (addr : mword 64) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (ep : Privilege) s :
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width false) s
    = Some (Ok pma_ok_aligned, s) ->
  exec (pmpCheck (Physaddr addr) width acc ep) s = Some (None, s) ->
  exec (mem_write_ea (Physaddr addr) width acc pbmt false false false) s = Some (Ok tt, s).
Proof.
  intros Heff Hcp Hpmpchk.
  unfold mem_write_ea. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (write_kind_of_flags false false false) s
                  = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * width) = addr)
      by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _ Hpmpchk). cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. reflexivity.
Qed.

Lemma exec_pmaCheck_ram_load_g (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) k (Load Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hread.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hread (exec_is_mag_applicable_load_data k s) Halign.
Qed.

Lemma exec_pmaCheck_ram_store_g (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) k (Store Data) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_data k s) Halign.
Qed.

Lemma exec_write_ram_plain_1 (addr : mword 64) (data : bv 8) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 1 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_write_ram_plain_2 (addr : mword 64) (data : bv 16) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 2 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 2 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.
