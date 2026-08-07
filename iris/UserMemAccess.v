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
Require Import UptTree.
Require Import UserPtTree.
Require Import UserMemPt.
Require Import SmodePte.
Require Import SRegime.
Require Import WpLoad.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
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

Lemma exec_vmem_write_addr_sc (width : Z) (va pa : mword 64) (dat : mword (8*width))
    (aq rl : bool) (ep ep' : Privilege) (md : SATPMode) (plan : Phys_Mem_Access_Info)
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
  (* success (match_reservation = true): ea + write with the SC flags *)
  exec (mem_write_ea (Physaddr pa) width acc PBMT_PMA aq rl true) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv acc PBMT_PMA aq rl true) s'
    = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)) ->
  (* fail (match_reservation = false): the access is still CHECKED -- and the
     check now answers with a splitting plan, not with [None] -- and no write
     happens *)
  exec (effectivePrivilege acc (register_lookup mstatus s'.(sregs))
          (register_lookup cur_privilege s'.(sregs))) s' = Some (ep', s') ->
  exec (phys_access_check acc PBMT_PMA ep' (Physaddr pa) width true) s'
    = Some (Ok plan, s') ->
  exec (vmem_write_addr (Virtaddr va) width dat acc aq rl true) s
    = Some (Ok (match_reservation (bits_of_physaddr (Physaddr pa))),
            if match_reservation (bits_of_physaddr (Physaddr pa))
            then MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)
            else s').
Proof.
  intros acc wv Hw Halign Heff Htm Htr Hea Hwv Heff' Hpac.
  assert (Hpos : 0 < width) by (apply vmem_width_pos; exact Hw).
  set (sw := MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N width) wv) s'.(mdev)).
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
