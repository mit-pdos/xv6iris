(* UserMemAccess.v -- the U-mode vmem_read_addr / vmem_write_addr layer:
   the LOAD / STORE / LR / SC memory accesses over the ptree bundle, just
   below execute_*.  This is where instruction ALIGNMENT and the LR/SC
   reservation live; it sits on top of the physical composers of
   UserMemPt.v.

   §0 the reservation platform-effect axioms.  [load_reservation] and
      [cancel_reservation] are OPAQUE monadic platform axioms (the LR/SC
      reservation set is NOT part of [mstate]); we assume they leave the
      modeled architectural state (sregs / mem / mdev) unchanged -- the
      exec analogues of the pure [match_reservation] / [valid_reservation]
      platform axioms.  This extends the reservation platform-axiom
      family; nothing about a particular reservation content is assumed
      (match_reservation stays opaque and is destructed both ways in SC).

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
Require Import SmodePte.
Require Import CommonWalk.
Require Import UserBits.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserMemPt.
Require Import MemAmo4.
Require Import SmodeCore.
Require Import WpLoad.
Require Import WpMmodeLeafBase.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 Reservation platform-effect axioms (see the file header).           *)
(* ===================================================================== *)

Axiom exec_load_reservation :
  forall (a : mword (if 64 =? 32 then 34 else 64)) (w : Z) (s : mstate),
    exec (load_reservation a w) s = Some (tt, s).

Axiom exec_cancel_reservation :
  forall (s : mstate), exec (cancel_reservation tt) s = Some (tt, s).

(* ===================================================================== *)
(* §1 The aligned vmem_read_addr reduction, WIDTH-GENERIC and premise-     *)
(*    shaped and res-generic: LOAD (res=false) and LR (res=true) both go   *)
(*    through it.  The align guard needs [0 < width] (so split gives one   *)
(*    chunk); the [width|4096] etc. constraints are not needed here.       *)
(* ===================================================================== *)

Lemma exec_split_misaligned_aligned_g (width : Z) (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr width = true ->
  exec (split_misaligned vaddr width) s = Some ((1, width), s).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
Qed.

Lemma exec_vmem_read_addr_aligned (width : Z) (va pa : mword 64) (v : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (s s' : mstate) :
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' = Some (Ok v, s') ->
  exists dvv : mword (8 * width),
    exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s = Some (Ok dvv, s').
Proof.
  intros Halign Htr Hmr.
  eexists.
  set (data2 := update_subrange_vec_dec (zeros' (8*1*width)) (8*(0+1)*width-1) (8*0*width) (autocast (T := mword) v)
                : mword (8*1*width)).
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * width)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s'))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s' = _ =>
        assert (Hmrm : execR mrm s' = Some (inr data2, s'))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hmr).
        cbn match.
        (* the res side effect: load_reservation (res=true) or tt (res=false) *)
        assert (Hres : execR (if res return Defs.monadR _ _ unit
                              then liftR (load_reservation (bits_of_physaddr (Physaddr pa)) width)
                              else returnR (result (mword (8*width)) ExecutionResult) tt) s'
                       = Some (inr tt, s')).
        { destruct res.
          - rewrite execR_liftR. rewrite exec_load_reservation. reflexivity.
          - apply execR_returnR_fwd. }
        rewrite (execR_bind0_Some _ _ _ _ Hres).
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.

(* the LOAD bundle composer (width 8, res=false): aligned load at a
   user-mapped load-permitted va reduces vmem_read_addr to Ok of the
   width-8 value, the translation absorbed. *)
(* ===================================================================== *)
(* §1b The aligned vmem_write_addr reduction (STORE), width-generic.  The  *)
(*     write-value is the model's own subrange extraction [wv]; udata_own  *)
(*     absorbs whatever value lands (contents existential).                *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_aligned_store (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (s s' : mstate) :
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*width-1) (8*0*width))
            : mword (8 * width) in
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_write_ea (Physaddr pa) width false false false) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv (Store Data) PBMT_PMA false false false) s'
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)) ->
  exec (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)).
Proof.
  intros wv Halign Htr Hea Hwv.
  set (sw := MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (true, 0%Z, true), sw))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data)))
                            "sys/vmem_utils.sail:197.50-197.51") s' = Some (tt, s')) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data)))
                              "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s'
                     = Some (inr tt, s'))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s' = Some (inr true, sw))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
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
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.


(* ===================================================================== *)
(* §1c The aligned vmem_write_addr reduction for STORECONDITIONAL, width-  *)
(*     generic and premise-shaped.  The [match_reservation] outcome        *)
(*     decides: true -> the write lands (Ok true, write_bytes state);      *)
(*     false -> the reservation was lost, no write (Ok false, state at     *)
(*     the translated s').  Both re-establish the invariant.  aq/rl are    *)
(*     whatever the SC instruction passed (execute_STORECON uses aq&&rl /  *)
(*     rl); res = true throughout.                                         *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_sc (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (aq rl : bool) (s s' : mstate) :
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*width-1) (8*0*width))
            : mword (8 * width) in
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (StoreConditional Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s'.(sregs) = User ->
  (* success (match_reservation = true): ea + write with the SC flags *)
  exec (mem_write_ea (Physaddr pa) width aq rl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv (StoreConditional Data) PBMT_PMA aq rl true) s'
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)) ->
  (* fail (match_reservation = false): the access is still granted, no write *)
  exec (phys_access_check (StoreConditional Data) PBMT_PMA User (Physaddr pa) width true) s'
    = Some (None, s') ->
  exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) aq rl true) s
    = Some (Ok (match_reservation (bits_of_physaddr (Physaddr pa))),
            if match_reservation (bits_of_physaddr (Physaddr pa))
            then MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)
            else s').
Proof.
  intros wv Halign Htr Hmprv Hcp Hea Hwv Hpac.
  set (sw := MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)).
  set (mr := match_reservation (bits_of_physaddr (Physaddr pa))).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, mr), if mr then sw else s'))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data)))
                            "sys/vmem_utils.sail:197.50-197.51") s' = Some (tt, s')) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data)))
                              "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s'
                     = Some (inr tt, s'))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s'
                            = Some (inr mr, if mr then sw else s'))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        unfold mr; destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr; cbn [Riscv.rv64d.not negb andb].
        - (* mr = true: andb true (not true) = false -> WRITE branch *)
          rewrite (execR_liftR_seq _ _ _ _ _ Hea).
          cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
          cbn match. apply execR_returnR_fwd.
        - (* mr = false: andb true (not false) = true -> FAIL branch (no write) *)
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')).
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')).
          rewrite Hcp.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_effectivePrivilege_mprv0 (StoreConditional Data)
               (register_lookup mstatus s'.(sregs)) User s' Hmprv)).
          rewrite (execR_liftR_seq _ _ _ _ _ Hpac).
          cbn match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.

Lemma exec_mem_write_ea_g (width : Z) (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) width false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
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
  Context `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
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
    iMod (user_pt_load_data_g k Hk Hk8 Hkdvd Huintk Hread_plain
            uroot tfp um data w va σ
            Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
            with "Hri Hgh Hinv Hdata")
      as (dv σ') "(%Htr & %Hmr & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * k))) (Load Data)) σ
                   = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * k)) with (add_vec_int va (0 * k)).
      rewrite avi0. exact Htr. }
    destruct (exec_vmem_read_addr_aligned k va (u_walk_pa w va) dv (Load Data)
                false false false σ σ' Hal Htr' Hmr) as (dvv & Hvr).
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
    iMod (user_pt_store_data_g k Hk Hk8 Hkdvd Huintk Hwrite_plain
            uroot tfp um data w va wv σ
            Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
            with "Hri Hgh Hinv Hdata")
      as (σ') "(%Htr & %Hwv & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
    iModIntro. iExists σ'.
    iSplit; [ iPureIntro | ].
    { apply (exec_vmem_write_addr_aligned_store k va (u_walk_pa w va) dat σ σ' Hal).
      - change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * k)) with (add_vec_int va (0 * k)).
        rewrite avi0. exact Htr.
      - exact (exec_mem_write_ea_g k (u_walk_pa w va) σ').
      - exact Hwv. }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserMemAccessGeneric.

(* the width instances -- the names the memory arms consume *)
Section UserMemAccessInstances.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition user_pt_vmem_read_addr_load_8 :=
    user_pt_vmem_read_addr_load 8 ltac:(lia) ltac:(lia)
      ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity) exec_read_ram_plain_8.
  Definition user_pt_vmem_read_addr_load_4 :=
    user_pt_vmem_read_addr_load 4 ltac:(lia) ltac:(lia)
      ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity) exec_read_ram_plain_4.
  Definition user_pt_vmem_read_addr_load_2 :=
    user_pt_vmem_read_addr_load 2 ltac:(lia) ltac:(lia)
      ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity) exec_read_ram_plain_2.
  Definition user_pt_vmem_read_addr_load_1 :=
    user_pt_vmem_read_addr_load 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) exec_read_ram_plain_1.

  Definition user_pt_vmem_write_addr_store_8 :=
    user_pt_vmem_write_addr_store 8 ltac:(lia) ltac:(lia)
      ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity) exec_write_ram_plain_8.
  Definition user_pt_vmem_write_addr_store_4 :=
    user_pt_vmem_write_addr_store 4 ltac:(lia) ltac:(lia)
      ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity) exec_write_ram_plain_4.
  Definition user_pt_vmem_write_addr_store_2 :=
    user_pt_vmem_write_addr_store 2 ltac:(lia) ltac:(lia)
      ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity) exec_write_ram_plain_2.
  Definition user_pt_vmem_write_addr_store_1 :=
    user_pt_vmem_write_addr_store 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) exec_write_ram_plain_1.

End UserMemAccessInstances.

(* ===================================================================== *)
(* §3 Building blocks for the MISALIGNED-access faults.  A misaligned      *)
(*    LR/SC faults BEFORE any access: the platform delivers AccessFault    *)
(*    (plat_misaligned_access.lrsc), surfacing as E_Load_Access_Fault      *)
(*    (LR) / E_SAMO_Access_Fault (SC), state unchanged.  (Plain load/store *)
(*    misalignment does NOT fault -- the hardware splits it; AMO           *)
(*    misalignment is checked inside execute_AMO.)                         *)
(*    [exec_memory_exception] and [exec_plat_misaligned_lrsc] are the two  *)
(*    exec bricks; the vmem_read_addr / vmem_write_addr misaligned         *)
(*    reductions built on them are worklisted (see iris/CLAUDE.md) -- the  *)
(*    open point is reducing the model's DEPENDENT align guard             *)
(*    [if not is_aligned return MR ... then fault else tt] inside          *)
(*    catch_early_return without cbn unfolding the bind/liftR structure    *)
(*    the execR_* lemmas match on.                                         *)
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

Lemma exec_plat_misaligned_lrsc (acc : MemoryAccessType mem_payload) (s : mstate) :
  is_amo_access acc = false ->
  exec (plat_misaligned_exception acc true) s = Some (Some AccessFault, s).
Proof.
  intro Hamo.
  unfold plat_misaligned_exception.
  rewrite (exec_bind0_Some _ _ _ _ _ (_ : exec (assert_exp (not (is_amo_access acc)) _%string) s = Some (tt, s))).
  2:{ rewrite Hamo. unfold assert_exp. cbn match. apply exec_returnm. }
  apply exec_returnm.
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
      (aq rl : bool) (priv : Privilege) (s : mstate) :
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    exec (vmem_read_addr (Virtaddr va) width (LoadReserved Data) aq rl true) s
      = Some (Err (Trap (priv, make_sync_exception (E_Load_Access_Fault tt) va, pc)), s).
  Proof.
    intros Hnal Hcp Hpc.
    unfold vmem_read_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_plat_misaligned_lrsc (LoadReserved Data) s eq_refl). cbn match.
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_memory_exception va pc (E_Load_Access_Fault tt) priv s Hcp Hpc). cbn match.
    rewrite execR_early_ret. cbn match. reflexivity.
  Qed.

  Lemma exec_vmem_write_addr_misaligned_sc (va pc : mword 64) (width : Z)
      (dat : mword (8 * width)) (aq rl : bool) (priv : Privilege) (s : mstate) :
    is_aligned_vaddr (Virtaddr va) width = false ->
    register_lookup cur_privilege s.(sregs) = priv ->
    register_lookup PC s.(sregs) = pc ->
    exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) aq rl true) s
      = Some (Err (Trap (priv, make_sync_exception (E_SAMO_Access_Fault tt) va, pc)), s).
  Proof.
    intros Hnal Hcp Hpc.
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_plat_misaligned_lrsc (StoreConditional Data) s eq_refl). cbn match.
    repeat (peel_b0 || peel_b || peel_l).
    rewrite (exec_memory_exception va pc (E_SAMO_Access_Fault tt) priv s Hcp Hpc). cbn match.
    rewrite execR_early_ret. cbn match. reflexivity.
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

Lemma execR_untilMT'_last {R Vars} (limit : Z) (vars vars' : Vars)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars)
   s s' (acc : Acc (Zwf 0) limit) :
  (limit >= 0)%Z ->
  execR (body vars) s = Some (inr vars', s') ->
  execR (cond vars') s' = Some (inr true, s') ->
  execR (Defs.untilMT' limit vars cond body acc) s = Some (inr vars', s').
Proof.
  intros Hlim Hb Hc. destruct acc as [acc_fn]. cbn [Defs.untilMT'].
  destruct (Z_ge_dec limit 0) as [Hge|Hge]; [| lia].
  rewrite (execR_bind_Some _ _ _ _ _ Hb).
  rewrite (execR_bind_Some _ _ _ _ _ Hc). cbn match. apply execR_returnR_fwd.
Qed.

Lemma execR_untilMT'_step {R Vars} (limit : Z) (vars vars' : Vars)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars)
   s s' (acc : Acc (Zwf 0) limit) :
  (limit >= 0)%Z ->
  execR (body vars) s = Some (inr vars', s') ->
  execR (cond vars') s' = Some (inr false, s') ->
  exists acc' : Acc (Zwf 0) (limit-1),
    execR (Defs.untilMT' limit vars cond body acc) s
    = execR (Defs.untilMT' (limit-1) vars' cond body acc') s'.
Proof.
  intros Hlim Hb Hc. destruct acc as [acc_fn]. cbn [Defs.untilMT'].
  destruct (Z_ge_dec limit 0) as [Hge|Hge]; [| lia].
  rewrite (execR_bind_Some _ _ _ _ _ Hb).
  rewrite (execR_bind_Some _ _ _ _ _ Hc). cbn match. eexists. reflexivity.
Qed.

Lemma execR_untilMT'_chain {R Vars}
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars) :
   forall (N : nat) (v : nat -> Vars) (st : nat -> mstate) (limit0 : Z) (acc : Acc (Zwf 0) limit0),
   (1 <= N)%nat ->
   (limit0 >= Z.of_nat N - 1)%Z ->
   (forall k, (k < N)%nat -> execR (body (v k)) (st k) = Some (inr (v (S k)), st (S k))) ->
   (forall k, (S k < N)%nat -> execR (cond (v (S k))) (st (S k)) = Some (inr false, st (S k))) ->
   execR (cond (v N)) (st N) = Some (inr true, st N) ->
   execR (Defs.untilMT' limit0 (v 0%nat) cond body acc) (st 0%nat) = Some (inr (v N), st N).
Proof.
  intros N. induction N as [|N' IH]; [ lia | ].
  intros v st limit0 acc HN Hlim Hbody Hcondf Hcondt.
  destruct (Nat.eq_dec N' 0) as [->|Hn0].
  - apply (execR_untilMT'_last limit0 (v 0%nat) (v 1%nat) cond body (st 0%nat) (st 1%nat) acc).
    + lia.
    + apply (Hbody 0%nat). lia.
    + apply Hcondt.
  - edestruct (execR_untilMT'_step limit0 (v 0%nat) (v 1%nat) cond body (st 0%nat) (st 1%nat) acc)
      as [acc' Hstep].
    + lia.
    + apply (Hbody 0%nat). lia.
    + apply (Hcondf 0%nat). lia.
    + rewrite Hstep.
      apply (IH (fun k => v (S k)) (fun k => st (S k)) (limit0 - 1) acc').
      * lia.
      * lia.
      * intros k Hk. apply (Hbody (S k)). lia.
      * intros k Hk. apply (Hcondf (S k)). lia.
      * apply Hcondt.
Qed.

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

Lemma misaligned_order_split (n : Z) : misaligned_order n = (0, n - 1, 1).
Proof. reflexivity. Qed.

Lemma exec_plat_misaligned_loadstore_none (acc : MemoryAccessType mem_payload) (s : mstate) :
  is_amo_access acc = false ->
  is_vector_access acc = false ->
  exec (plat_misaligned_exception acc false) s = Some (None, s).
Proof.
  intros Hamo Hvec. unfold plat_misaligned_exception.
  assert (Ha : exec (assert_exp (Riscv.rv64d.not (is_amo_access acc)) "sys/vmem_utils.sail:85.35-85.36") s = Some (tt, s)).
  { rewrite Hamo. reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Ha). rewrite Hvec. apply exec_returnm.
Qed.

Section MisalignedSplitRead.
  Context (width bytes : Z) (va : mword 64) (acc : MemoryAccessType mem_payload) (aq rl : bool).
  Context (N : nat) (pa : nat -> mword 64) (val : nat -> mword (8*bytes)) (st : nat -> mstate).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes) (Hwidth : Z.of_nat N * bytes = width).

  Notation n := (Z.of_nat N).
  Notation vbits := (bits_of_virtaddr (Virtaddr va)).
  Notation RES := (result (mword (8*width)) ExecutionResult).

  Fixpoint data_seq (k : nat) : mword (8 * n * bytes) :=
    match k with
    | O => zeros' (8 * n * bytes)
    | S k' => update_subrange_vec_dec (data_seq k')
                (8*(Z.of_nat k'+1)*bytes-1) (8*Z.of_nat k'*bytes)
                (autocast (T:=mword) (val k'))
    end.

  Definition split_var (k : nat) : (mword (8 * n * bytes) * bool * Z) :=
    (data_seq k, Nat.eqb k N, Z.of_nat (Nat.min k (N-1))).

  Definition split_body : (mword (8*n*bytes) * bool * Z) -> Defs.monadR RES exception (mword (8*n*bytes) * bool * Z) :=
    (fun '(data, finished, i) =>
       (liftR (assert_exp' true "loop dummy assert") >>= fun _ =>
        let offset := i in
        let vaddr := add_vec_int vbits (Z.mul offset bytes) in
        liftR (translateAddr (Virtaddr vaddr) acc) >>= fun w__3 =>
        match w__3 with
        | Err (e, _) =>
           liftR (memory_exception (Virtaddr vaddr) e) >>= fun w__4 =>
           (early_return (Err w__4 : RES)) >> returnR RES data
        | Ok (paddr, pbmt, _) =>
           liftR (mem_read acc pbmt paddr bytes aq rl false) >>= fun w__5 =>
           match w__5 with
           | Err e =>
              liftR (memory_exception (Virtaddr vaddr) e) >>= fun w__6 =>
              (early_return (Err w__6 : RES)) >> returnR RES data
           | Ok v =>
              returnR RES tt >>
              let data := update_subrange_vec_dec data
                            (Z.sub (Z.mul (Z.mul 8 (Z.add offset 1)) bytes) 1)
                            (Z.mul (Z.mul 8 offset) bytes) (autocast (T:=mword) v) in
              returnR RES data
           end
        end >>= fun data =>
        let '(finished, i) :=
          (if Z.eqb offset (n-1) then (true, i) else (finished, Z.add offset 1)) in
        returnR RES (data, finished, i))).

  Hypothesis Htr : forall k, (k < N)%nat ->
    exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat k * bytes))) acc) (st k)
      = Some (Ok (Physaddr (pa k), PBMT_PMA, init_ext_ptw), st (S k)).
  Hypothesis Hmr : forall k, (k < N)%nat ->
    exec (mem_read acc PBMT_PMA (Physaddr (pa k)) bytes aq rl false) (st (S k))
      = Some (Ok (val k), st (S k)).

  Lemma split_body_step (k : nat) : (k < N)%nat ->
    execR (split_body (split_var k)) (st k) = Some (inr (split_var (S k)), st (S k)).
  Proof.
    intros Hk. unfold split_body, split_var.
    replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min k (N-1)) with k by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st k) = Some (@eq_refl bool true, st k)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr k Hk)).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mrm ?post) (st (S k)) = _ =>
      assert (Hmrm : execR mrm (st (S k)) = Some (inr (data_seq (S k)), st (S k)))
    end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (Hmr k Hk)). cbn match.
      rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt (st (S k)))).
      cbn [data_seq]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
    destruct (Z.eqb (Z.of_nat k) (n-1)) eqn:Eq; cbn match;
      rewrite execR_returnR_fwd; do 3 f_equal; unfold split_var.
    - apply Z.eqb_eq in Eq.
      replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
      replace (Nat.min (S k) (N-1)) with k by lia. reflexivity.
    - apply Z.eqb_neq in Eq.
      replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.min (S k) (N-1)) with (S k) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
  Qed.

  Lemma split_cond_false (k : nat) : (S k < N)%nat ->
    execR ((fun '(data, finished, i) => returnR RES finished) (split_var (S k))) (st (S k))
      = Some (inr false, st (S k)).
  Proof.
    intros Hk. unfold split_var. cbn match.
    replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
    apply execR_returnR_fwd.
  Qed.

  Lemma split_cond_true :
    execR ((fun '(data, finished, i) => returnR RES finished) (split_var N)) (st N)
      = Some (inr true, st N).
  Proof.
    unfold split_var. cbn match. rewrite Nat.eqb_refl. apply execR_returnR_fwd.
  Qed.

  Lemma split_var0 : split_var 0%nat = (zeros' (8 * n * bytes), false, 0%Z).
  Proof.
    unfold split_var. cbn [data_seq].
    replace (Nat.eqb 0 N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min 0 (N-1)) with 0%nat by lia. reflexivity.
  Qed.

  Lemma split_loop :
    execR (Defs.untilMT (zeros' (8 * n * bytes), false, 0%Z) (fun '(data, finished, i) => n)
             (fun '(data, finished, i) => returnR RES finished) split_body) (st 0%nat)
      = Some (inr (split_var N), st N).
  Proof.
    rewrite <- split_var0.
    unfold Defs.untilMT.
    set (L := (fun '(data, finished, i) => n) (split_var 0%nat)).
    assert (HL : L = n) by (unfold L; rewrite split_var0; reflexivity).
    clearbody L. rewrite HL.
    apply (execR_untilMT'_chain (fun '(data, finished, i) => returnR RES finished)
                                split_body N split_var st n).
    - exact HN.
    - lia.
    - intros k Hk. apply split_body_step; assumption.
    - intros k Hk. apply split_cond_false; assumption.
    - apply split_cond_true.
  Qed.

  Lemma exec_vmem_read_addr_misaligned_split :
    is_aligned_vaddr (Virtaddr va) width = false ->
    is_amo_access acc = false ->
    is_vector_access acc = false ->
    exec (split_misaligned (Virtaddr va) width) (st 0%nat) = Some ((n, bytes), st 0%nat) ->
    exists dvv : mword (8 * width),
      exec (vmem_read_addr (Virtaddr va) width acc aq rl false) (st 0%nat) = Some (Ok dvv, st N).
  Proof.
    intros Hnal Hamo Hvec Hsplit. eexists.
    unfold vmem_read_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    match goal with
    | |- context [ Defs.bind0 ?g (Defs.liftR (split_misaligned (Virtaddr va) width)) ] =>
        set (GRD := g)
    end.
    assert (Hg : execR GRD (st 0%nat) = Some (inr tt, st 0%nat)).
    { unfold GRD.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_plat_misaligned_loadstore_none acc (st 0%nat) Hamo Hvec)).
      cbn match. apply execR_returnR_fwd. }
    assert (Hinner : execR (Defs.bind0 GRD (liftR (split_misaligned (Virtaddr va) width))) (st 0%nat)
                     = Some (inr (n, bytes), st 0%nat)).
    { rewrite (execR_bind0_Some _ _ _ _ Hg).
      rewrite execR_liftR. rewrite Hsplit. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_split. cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ split_loop).
    cbn match. reflexivity.
  Qed.

End MisalignedSplitRead.

(* ===================================================================== *)
(* §4c The MISALIGNED plain-STORE split reduction, generic in N.  Same    *)
(*     shape as §4b: the loop var is [(finished, offset, write_success)]  *)
(*     and [write_success] accumulates [andb] of the per-chunk store      *)
(*     outcomes ([ws_seq]).  Each chunk threads state through translate    *)
(*     ([stt k]) then mem_write_ea + mem_write_value ([st (S k)]); the     *)
(*     write-value is the model's own [subrange_vec_dec dat] slice.        *)
(* ===================================================================== *)

Section MisalignedSplitWrite.
  Context (width bytes : Z) (va : mword 64) (dat : mword (8*width)) (aq rl : bool).
  Context (N : nat) (pa : nat -> mword 64) (sk : nat -> bool)
          (stt : nat -> mstate) (st : nat -> mstate).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes) (Hwidth : Z.of_nat N * bytes = width).

  Notation n := (Z.of_nat N).
  Notation vbits := (bits_of_virtaddr (Virtaddr va)).
  Notation RES := (result bool ExecutionResult).

  Fixpoint ws_seq (k : nat) : bool :=
    match k with O => true | S k' => andb (ws_seq k') (sk k') end.

  Definition wv (k : nat) : mword (8*bytes) :=
    autocast (T:=mword) (subrange_vec_dec dat (8*(Z.of_nat k+1)*bytes-1) (8*Z.of_nat k*bytes)).

  Definition write_var (k : nat) : (bool * Z * bool) :=
    (Nat.eqb k N, Z.of_nat (Nat.min k (N-1)), ws_seq k).

  Definition write_body : (bool * Z * bool) -> Defs.monadR RES exception (bool * Z * bool) :=
    (fun '(finished, i, write_success) =>
       (liftR (assert_exp' true "loop dummy assert") >>= fun _ =>
        let offset := i in
        let vaddr := add_vec_int vbits (Z.mul offset bytes) in
        liftR (translateAddr (Virtaddr vaddr) (Store Data)) >>= fun w__3 =>
        match w__3 with
        | Err (e, _) =>
           liftR (memory_exception (Virtaddr vaddr) e) >>= fun w__4 =>
           (early_return (Err w__4 : RES)) >> returnR RES write_success
        | Ok (paddr, pbmt, _) =>
           liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") >>
           (liftR (mem_write_ea paddr bytes false false false) >>= fun w__9 =>
            match w__9 with
            | Err e =>
               liftR (memory_exception (Virtaddr vaddr) e) >>= fun w__10 =>
               (early_return (Err w__10 : RES)) >> returnR RES write_success
            | Ok tt =>
               let write_value := subrange_vec_dec dat
                     (Z.sub (Z.mul (Z.mul 8 (Z.add offset 1)) bytes) 1)
                     (Z.mul (Z.mul 8 offset) bytes) in
               liftR (mem_write_value paddr bytes (autocast (T:=mword) write_value)
                        (Store Data) pbmt false false false) >>= fun w__11 =>
               match w__11 with
               | Err e =>
                  liftR (memory_exception (Virtaddr vaddr) e) >>= fun w__12 =>
                  (early_return (Err w__12 : RES)) >> returnR RES write_success
               | Ok s => returnR RES (andb write_success s)
               end
            end)
        end >>= fun write_success =>
        let '(finished, i) :=
          (if Z.eqb offset (n-1) then (true, i) else (finished, Z.add offset 1)) in
        returnR RES (finished, i, write_success))).

  Hypothesis Htr : forall k, (k < N)%nat ->
    exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat k * bytes))) (Store Data)) (st k)
      = Some (Ok (Physaddr (pa k), PBMT_PMA, init_ext_ptw), stt k).
  Hypothesis Hea : forall k, (k < N)%nat ->
    exec (mem_write_ea (Physaddr (pa k)) bytes false false false) (stt k) = Some (Ok tt, stt k).
  Hypothesis Hwv : forall k, (k < N)%nat ->
    exec (mem_write_value (Physaddr (pa k)) bytes (wv k) (Store Data) PBMT_PMA false false false) (stt k)
      = Some (Ok (sk k), st (S k)).

  Lemma write_body_step (k : nat) : (k < N)%nat ->
    execR (write_body (write_var k)) (st k) = Some (inr (write_var (S k)), st (S k)).
  Proof.
    intros Hk. unfold write_body, write_var.
    replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min k (N-1)) with k by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st k) = Some (@eq_refl bool true, st k)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr k Hk)).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mrm ?post) (stt k) = _ =>
      assert (Hmrm : execR mrm (stt k) = Some (inr (ws_seq (S k)), st (S k)))
    end.
    { assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") (stt k) = Some (tt, stt k)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") : Defs.monadR RES exception unit) (stt k) = Some (inr tt, stt k))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      rewrite (execR_bind0_Some _ _ _ _ Hscm).
      rewrite (execR_liftR_seq _ _ _ _ _ (Hea k Hk)). cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ (Hwv k Hk)). cbn match.
      cbn [ws_seq]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
    destruct (Z.eqb (Z.of_nat k) (n-1)) eqn:Eq; cbn match;
      rewrite execR_returnR_fwd; do 3 f_equal; unfold write_var.
    - apply Z.eqb_eq in Eq.
      replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
      replace (Nat.min (S k) (N-1)) with k by lia. reflexivity.
    - apply Z.eqb_neq in Eq.
      replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.min (S k) (N-1)) with (S k) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
  Qed.

  Lemma write_cond_false (k : nat) : (S k < N)%nat ->
    execR ((fun '(finished, i, write_success) => returnR RES finished) (write_var (S k))) (st (S k))
      = Some (inr false, st (S k)).
  Proof.
    intros Hk. unfold write_var. cbn match.
    replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
    apply execR_returnR_fwd.
  Qed.

  Lemma write_cond_true :
    execR ((fun '(finished, i, write_success) => returnR RES finished) (write_var N)) (st N)
      = Some (inr true, st N).
  Proof. unfold write_var. cbn match. rewrite Nat.eqb_refl. apply execR_returnR_fwd. Qed.

  Lemma write_var0 : write_var 0%nat = (false, 0%Z, true).
  Proof.
    unfold write_var. cbn [ws_seq].
    replace (Nat.eqb 0 N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min 0 (N-1)) with 0%nat by lia. reflexivity.
  Qed.

  Lemma write_loop :
    execR (Defs.untilMT (false, 0%Z, true) (fun '(finished, i, write_success) => n)
             (fun '(finished, i, write_success) => returnR RES finished) write_body) (st 0%nat)
      = Some (inr (write_var N), st N).
  Proof.
    rewrite <- write_var0. unfold Defs.untilMT.
    set (L := (fun '(finished, i, write_success) => n) (write_var 0%nat)).
    assert (HL : L = n) by (unfold L; rewrite write_var0; reflexivity).
    clearbody L. rewrite HL.
    apply (execR_untilMT'_chain (fun '(finished, i, write_success) => returnR RES finished)
                                write_body N write_var st n).
    - exact HN.
    - lia.
    - intros k Hk. apply write_body_step; assumption.
    - intros k Hk. apply write_cond_false; assumption.
    - apply write_cond_true.
  Qed.

  Lemma exec_vmem_write_addr_misaligned_split :
    is_aligned_vaddr (Virtaddr va) width = false ->
    exec (split_misaligned (Virtaddr va) width) (st 0%nat) = Some ((n, bytes), st 0%nat) ->
    exec (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) (st 0%nat)
      = Some (Ok (ws_seq N), st N).
  Proof.
    intros Hnal Hsplit.
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    match goal with
    | |- context [ Defs.bind0 ?g (Defs.liftR (split_misaligned (Virtaddr va) width)) ] =>
        set (GRD := g)
    end.
    assert (Hg : execR GRD (st 0%nat) = Some (inr tt, st 0%nat)).
    { unfold GRD.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_plat_misaligned_loadstore_none (Store Data) (st 0%nat) eq_refl eq_refl)).
      cbn match. apply execR_returnR_fwd. }
    assert (Hinner : execR (Defs.bind0 GRD (liftR (split_misaligned (Virtaddr va) width))) (st 0%nat)
                     = Some (inr (n, bytes), st 0%nat)).
    { rewrite (execR_bind0_Some _ _ _ _ Hg).
      rewrite execR_liftR. rewrite Hsplit. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_split. cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ write_loop).
    cbn match. reflexivity.
  Qed.

End MisalignedSplitWrite.

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

Lemma run_read_ram_resv_4_pin (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_RISCV_reserved (Physaddr addr) 4 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_resv_4 (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_RISCV_reserved (Physaddr addr) 4 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_resv_4_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

Lemma run_read_ram_resv_8_pin (addr : mword 64) (w : bv 64) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_RISCV_reserved (Physaddr addr) 8 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_resv_8 (addr : mword 64) (w : bv 64) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_RISCV_reserved (Physaddr addr) 8 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_resv_8_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 8) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* ===================================================================== *)
(* §5b The reserved pmaCheck, branching on reservability.  On the RAM     *)
(*    region [pma_allows_all] gives readable/writable=true but leaves     *)
(*    [PMA_reservability] free, so the LR/SC pma arm                       *)
(*    [andb R/W (reservability<>RsrvNone)] resolves to the reservability  *)
(*    bit: [<>None] -> allowed (None fault), [=None] -> the delegated      *)
(*    access fault (E_Load/E_SAMO).  This is the branch point of the      *)
(*    retire-or-fault disjunction.                                        *)
(* ===================================================================== *)

Lemma exec_pmaCheck_ram_lr_g (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) k (LoadReserved Data) pbmt true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then None else Some (E_Load_Access_Fault tt)), s).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:111.56-111.57" >>=
          (fun _ : true = true => returnM (andb (PMA_readable (override_PMA rattr pbmt))
                                             (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone))))
    with (returnM (andb (PMA_readable (override_PMA rattr pbmt))
                    (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn match. apply exec_returnM.
  - cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (E_Load_Access_Fault tt) s)).
    apply exec_returnM.
Qed.

Lemma exec_pmaCheck_ram_sc_g (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) k (StoreConditional Data) pbmt true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then None else Some (E_SAMO_Access_Fault tt)), s).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:112.56-112.57" >>=
          (fun _ : true = true => returnM (andb (PMA_writable (override_PMA rattr pbmt))
                                             (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone))))
    with (returnM (andb (PMA_writable (override_PMA rattr pbmt))
                    (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn [andb].
  destruct (generic_neq (PMA_reservability (override_PMA rattr pbmt)) RsrvNone) eqn:Hr.
  - cbn match. apply exec_returnM.
  - cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (E_SAMO_Access_Fault tt) s)).
    apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §5c The reserved pmpCheck grants.  pmpCheckRWX treats LoadReserved/     *)
(*    StoreConditional exactly like Load/Store (R resp. W), so these are   *)
(*    the load/store grants verbatim with the access constructor swapped.  *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant_lr (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (LoadReserved Data) User) s = Some (None, s).
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
                            (LoadReserved Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_pmpCheck_user_grant_sc (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (StoreConditional Data) User) s = Some (None, s).
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
                            (StoreConditional Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §5d The LR checked_mem_read RETIRE-OR-FAULT disjunction (widths 4, 8). *)
(*    Ties the pieces together: on a user-mapped, aligned, readable,      *)
(*    PMP-granted RAM address the reserved read either RETIRES with the   *)
(*    bytes ([reservability<>RsrvNone]) or takes the delegated            *)
(*    E_Load_Access_Fault ([reservability=RsrvNone]); a single [if] on    *)
(*    the (unpinned) reservability captures both total outcomes.          *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_lr_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (LoadReserved Data) pbmt User (Physaddr addr) 4 false false true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  unfold checked_mem_read.
  assert (Hrk : exec (read_kind_of_flags false false true) s = Some (rv64d_types.Read_RISCV_reserved, s))
    by (unfold read_kind_of_flags; apply exec_returnM).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 4 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 4 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 4 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    rewrite (exec_bind_Some _ _ _ _ _ Hrk).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resv_4 addr w s Hdev Hbytes)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 4 true) s
                   = Some (Some (E_Load_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 4 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 4 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_lr_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (LoadReserved Data) pbmt User (Physaddr addr) 8 false false true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  unfold checked_mem_read.
  assert (Hrk : exec (read_kind_of_flags false false true) s = Some (rv64d_types.Read_RISCV_reserved, s))
    by (unfold read_kind_of_flags; apply exec_returnM).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 8 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 8 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 8 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    rewrite (exec_bind_Some _ _ _ _ _ Hrk).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resv_8 addr w s Hdev Hbytes)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 8 true) s
                   = Some (Some (E_Load_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 8 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 8 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §5e The LR mem_read wrap (widths 4, 8): threads the mem_read-level      *)
(*    reads (mstatus/cur_privilege/effectivePrivilege, MPRV=0, User) and   *)
(*    the mem_read_priv_meta guard (aligned paddr -> no addr-align fault)  *)
(*    over §5d, giving the retire-or-fault disjunction at mem_read.        *)
(* ===================================================================== *)

Lemma exec_mem_read_lr_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (LoadReserved Data) pbmt (Physaddr addr) 4 false false true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_4 pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved Data) pbmt User (Physaddr addr) 4 false false true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s)).
  { unfold mem_read_priv_meta.
    rewrite Halign. cbn [Riscv.rv64d.not negb orb andb]. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Hcmr).
    destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
      cbn match; apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
    cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
Qed.

Lemma exec_mem_read_lr_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (LoadReserved Data) pbmt (Physaddr addr) 8 false false true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_8 pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved Data) pbmt User (Physaddr addr) 8 false false true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s)).
  { unfold mem_read_priv_meta.
    rewrite Halign. cbn [Riscv.rv64d.not negb orb andb]. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Hcmr).
    destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
      cbn match; apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
    cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §5f The aligned vmem_read_addr FAULT path (width-generic): translate    *)
(*    Ok but mem_read Err e -> the loop raises memory_exception (a Trap)   *)
(*    and early-returns, so vmem_read_addr returns Err (Trap ...).  The    *)
(*    complement of exec_vmem_read_addr_aligned (the retire path); the LR  *)
(*    disjunction picks between them on the reserved read's outcome.       *)
(*    (The fault carries the loop's chunk address add_vec_int va (0*w),    *)
(*    matching the retire lemma's translate-premise address form.)         *)
(* ===================================================================== *)

Lemma exec_vmem_read_addr_aligned_err (width : Z) (va pa pc : mword 64) (e : ExceptionType)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (priv : Privilege) (s s' : mstate) :
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read acc PBMT_PMA (Physaddr pa) width aq rl res) s' = Some (Err e, s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros Halign Htr Hmr Hcp Hpc.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * width)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite (misaligned_order_split 1).
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s'))
  end.
  { unfold Defs.untilMT. destruct (Defs.Zwf_guarded _) as [accf]. cbn [Defs.untilMT'].
    destruct (Z_ge_dec _ 0) as [Hge|Hge]; [| cbn in Hge; exfalso; lia ].
    (* the loop body at (zeros, false, 0): assert_exp' -> translate -> mem_read Err -> memory_exception -> early_return *)
    match goal with |- context [ Defs.bind ?bd ?k ] =>
      assert (Hbody : execR bd s = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
    { cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn [bits_of_virtaddr] in *. cbn match.
      match goal with |- execR (Defs.bind ?mm ?post) s' = _ =>
        assert (Hmrm : execR mm s' = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hmr). cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _
                  (exec_memory_exception (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))
                     pc e priv s' Hcp Hpc)). cbn match.
        rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
      rewrite execR_bind. rewrite Hmrm. reflexivity. }
    rewrite execR_bind. rewrite Hbody. reflexivity. }
  rewrite execR_bind. rewrite Hu. reflexivity.
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

Lemma exec_vmem_read_addr_lr_disj (width : Z) (va pa pc : mword 64) (w : mword (8 * width))
    (aq rl : bool) (priv : Privilege) (resv : bool) (s s' : mstate) :
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (LoadReserved Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_read (LoadReserved Data) PBMT_PMA (Physaddr pa) width aq rl true) s'
    = Some ((if resv then Ok w else Err (E_Load_Access_Fault tt)), s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  (exists dvv : mword (8 * width),
     exec (vmem_read_addr (Virtaddr va) width (LoadReserved Data) aq rl true) s = Some (Ok dvv, s'))
  \/ exec (vmem_read_addr (Virtaddr va) width (LoadReserved Data) aq rl true) s
       = Some (Err (Trap (priv, make_sync_exception (E_Load_Access_Fault tt)
                          (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros Halign Htr Hmr Hcp Hpc.
  destruct resv.
  - left. exact (exec_vmem_read_addr_aligned width va pa w (LoadReserved Data) aq rl true s s' Halign Htr Hmr).
  - right. exact (exec_vmem_read_addr_aligned_err width va pa pc (E_Load_Access_Fault tt)
                    (LoadReserved Data) aq rl true priv s s' Halign Htr Hmr Hcp Hpc).
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

Lemma exec_write_ram_cond_8 (addr : mword 64) (data : bv 64) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_RISCV_conditional (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn [Mem_write_request_value]. cbn match. cbn [Interface.iMon_bind].
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_checked_mem_write_sc_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (StoreConditional Data) pbmt User tt false false true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  unfold checked_mem_write.
  assert (Hwk : exec (write_kind_of_flags false false true) s = Some (rv64d_types.Write_RISCV_conditional, s))
    by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 4 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 4 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 4 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    rewrite (exec_bind_Some _ _ _ _ _ Hwk).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_4 addr data s Hdev)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 4 true) s
                   = Some (Some (E_SAMO_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 4 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 4 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_sc_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (StoreConditional Data) pbmt User tt false false true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  unfold checked_mem_write.
  assert (Hwk : exec (write_kind_of_flags false false true) s = Some (rv64d_types.Write_RISCV_conditional, s))
    by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 8 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 8 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 8 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    rewrite (exec_bind_Some _ _ _ _ _ Hwk).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_8 addr data s Hdev)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 8 true) s
                   = Some (Some (E_SAMO_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 8 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 8 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §5i The SC mem_write_value wrap (widths 4, 8): the write mirror of §5e  *)
(*    -- threads mstatus/cur_privilege/effectivePrivilege (MPRV=0, User)   *)
(*    and the mem_write_value_priv_meta paddr-alignment guard over §5h,     *)
(*    giving the retire-or-fault disjunction at mem_write_value (Ok true +  *)
(*    write-state / Err E_SAMO_Access_Fault + unchanged state).            *)
(* ===================================================================== *)

Lemma exec_mem_write_value_sc_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 4 data (StoreConditional Data) pbmt false false true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (StoreConditional Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [Riscv.rv64d.not negb orb andb]. cbn match.
  assert (Hcmw := exec_checked_mem_write_sc_4 pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr;
    cbn match in Hcmw;
    rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM.
Qed.

Lemma exec_mem_write_value_sc_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 8 data (StoreConditional Data) pbmt false false true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (StoreConditional Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [Riscv.rv64d.not negb orb andb]. cbn match.
  assert (Hcmw := exec_checked_mem_write_sc_8 pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr;
    cbn match in Hcmw;
    rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §5j The vmem-level SC FAULT path (reservability = RsrvNone).  BOTH      *)
(*    match_reservation branches fault: mr=true takes the write branch     *)
(*    where mem_write_value returns Err E_SAMO (§5i =None), mr=false takes  *)
(*    the check branch where phys_access_check denies (§5b =None); each     *)
(*    raises memory_exception and early-returns, so vmem_write_addr returns *)
(*    Err (Trap E_SAMO).  The complement of exec_vmem_write_addr_sc.        *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_sc_fault (width : Z) (va pa pc : mword 64) (dat : mword (8*width))
    (aq rl : bool) (s s' : mstate) :
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*width-1) (8*0*width))
            : mword (8 * width) in
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (StoreConditional Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  (* match_reservation=true path: ea ok, then write faults *)
  exec (mem_write_ea (Physaddr pa) width aq rl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv (StoreConditional Data) PBMT_PMA aq rl true) s'
    = Some (Err (E_SAMO_Access_Fault tt), s') ->
  (* match_reservation=false path: access denied *)
  exec (phys_access_check (StoreConditional Data) PBMT_PMA User (Physaddr pa) width true) s'
    = Some (Some (E_SAMO_Access_Fault tt), s') ->
  exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) aq rl true) s
    = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt)
                       (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros wv Halign Htr Hmprv Hcp Hpc Hea Hwv Hpac.
  set (A := add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite (misaligned_order_split 1).
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inl (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) A, pc))), s'))
  end.
  { unfold Defs.untilMT. destruct (Defs.Zwf_guarded _) as [accf]. cbn [Defs.untilMT'].
    destruct (Z_ge_dec _ 0) as [Hge|Hge]; [| cbn in Hge; exfalso; lia ].
    match goal with |- context [ Defs.bind ?bd ?k ] =>
      assert (Hbody : execR bd s = Some (inl (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) A, pc))), s')) end.
    { cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data)))
                            "sys/vmem_utils.sail:197.50-197.51") s' = Some (tt, s')) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb true (is_store_conditional (StoreConditional Data)))
                              "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s'
                     = Some (inr tt, s'))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- execR (Defs.bind ?mm ?post) s' = _ =>
          assert (Hwrblk : execR mm s' = Some (inl (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) A, pc))), s')) end.
      { rewrite (execR_bind0_Some _ _ _ _ Hscm).
        destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr; cbn [Riscv.rv64d.not negb andb].
        - (* mr=true -> WRITE branch, mem_write_value faults *)
          rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception A pc (E_SAMO_Access_Fault tt) User s' Hcp Hpc)). cbn match.
          rewrite execR_bind0. rewrite execR_early_ret. reflexivity.
        - (* mr=false -> FAIL branch, phys_access_check denies *)
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s')).
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s')). rewrite Hcp.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_effectivePrivilege_mprv0 (StoreConditional Data)
               (register_lookup mstatus s'.(sregs)) User s' Hmprv)).
          rewrite (execR_liftR_seq _ _ _ _ _ Hpac). cbn match.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception A pc (E_SAMO_Access_Fault tt) User s' Hcp Hpc)). cbn match.
          rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
      rewrite execR_bind. rewrite Hwrblk. reflexivity. }
    rewrite execR_bind. rewrite Hbody. reflexivity. }
  rewrite execR_bind. rewrite Hu. reflexivity.
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
    (aq rl : bool) (resv : bool) (s s' : mstate) :
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*width-1) (8*0*width))
            : mword (8 * width) in
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (StoreConditional Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  exec (mem_write_ea (Physaddr pa) width aq rl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv (StoreConditional Data) PBMT_PMA aq rl true) s'
    = Some (if resv then (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s')) ->
  exec (phys_access_check (StoreConditional Data) PBMT_PMA User (Physaddr pa) width true) s'
    = Some ((if resv then None else Some (E_SAMO_Access_Fault tt)), s') ->
  (exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) aq rl true) s
     = Some (Ok (match_reservation (bits_of_physaddr (Physaddr pa))),
             if match_reservation (bits_of_physaddr (Physaddr pa))
             then MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)
             else s'))
  \/ exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) aq rl true) s
       = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt)
                          (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros wv Halign Htr Hmprv Hcp Hpc Hea Hwv Hpac.
  destruct resv; cbn match in Hwv, Hpac.
  - left. exact (exec_vmem_write_addr_sc width va pa dat aq rl s s' Halign Htr Hmprv Hcp Hea Hwv Hpac).
  - right. exact (exec_vmem_write_addr_sc_fault width va pa pc dat aq rl s s' Halign Htr Hmprv Hcp Hpc Hea Hwv Hpac).
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
  Context `{CID : CpuId}.

  Lemma user_pt_vmem_read_addr_lr_4 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
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
      ⌜(exists dvv : mword 32,
          exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved Data) false false true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved Data) false false true) σ
            = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved Data) σ
               (or_intror (or_intror (or_intror (or_introl eq_refl))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 4 ltac:(lia) ltac:(exists 1024; reflexivity) um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4)
      as (region & Hpmam & _ & Hrd & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 4 (Z.to_nat 4 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmio : exec (within_mmio_readable (Physaddr pa) 4) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 4 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 4 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa 4 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmr := exec_mem_read_lr_4 PBMT_PMA pa region dv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
             Hpmam (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal) Hrd
             Hmmio (addr_is_ram_not_dev _ Hram0) Hbytes
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4))) (LoadReserved Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)).
      rewrite avi0. exact Htr. }
    destruct (exec_vmem_read_addr_lr_disj 4 va pa (register_lookup PC σ'.(sregs)) dv
                false false User (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr' Hmr
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl)
      as [Hret | Hflt].
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; left; exact Hret | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

  Lemma user_pt_vmem_read_addr_lr_8 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
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
      ⌜(exists dvv : mword 64,
          exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved Data) false false true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved Data) false false true) σ
            = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved Data) σ
               (or_intror (or_intror (or_intror (or_introl eq_refl))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 8 ltac:(lia) ltac:(exists 512; reflexivity) um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8)
      as (region & Hpmam & _ & Hrd & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 8 (Z.to_nat 8 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmio : exec (within_mmio_readable (Physaddr pa) 8) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 8 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 8 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa 8 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmr := exec_mem_read_lr_8 PBMT_PMA pa region dv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
             Hpmam (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal) Hrd
             Hmmio (addr_is_ram_not_dev _ Hram0) Hbytes
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8))) (LoadReserved Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)).
      rewrite avi0. exact Htr. }
    destruct (exec_vmem_read_addr_lr_disj 8 va pa (register_lookup PC σ'.(sregs)) dv
                false false User (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr' Hmr
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl)
      as [Hret | Hflt].
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; left; exact Hret | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End UserMemAccessBundle.
