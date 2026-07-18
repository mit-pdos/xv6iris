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
Require Import PtTree.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import UserMem.
Require Import UserMemPt.
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
