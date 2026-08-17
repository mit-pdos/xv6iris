(* HartSTrans.v -- the S-mode translation at the [swp] layer.

   THE POINT OF THIS FILE IS HOW LITTLE IS IN IT.  The page-table proofs
   (PtTree / KptTree / CommonWalk / Pt4kWalk) already establish what the walk
   does; what the per-node port needs is the same facts in FOOTPRINTED form --
   reads confined to a declared set, writes named, and the file the walk lands
   on spelled out -- because under per-node stepping another hart steps
   between this walk's nodes, so a successor computed from the whole state is
   stale.

   Those proofs are NOT restated.  Two seams carry them across:

   - [PtTree.hval_translate_TLB_hit_pt] (spliced in beside its exec twin):
     the hit path makes NO events, so [WpDecodeBridge.goodb] certifies the
     footprint along the same chain the exec proof walks and
     [HartGoodb.hval_of_goodb] pairs it with the exec lemma.

   - the [tlb] read below, which the bridge CANNOT carry: [goodb] transports
     only reads whose values are pinned in the reference state, and the TLB's
     contents are whatever this hart's frame says.  So the lookup is a real
     footprinted node, and it is the only new walk here.

   The MISS path is different in kind and is not bridged: it reads PTEs from
   memory and writes the [tlb] register, so it needs the [swp] event rules --
   which is also why [HartRunGen]'s fetch obligation lets the fetch land on a
   different file than it started from. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb.
Require Import WpDecodeBridge Pt4kWalk CommonWalk PtTree.
Local Open Scope Z_scope.

(* the lookup, as a footprinted walk: one register read and a pure match.
   [Pt4kWalk.exec_lookup_TLB_hit_ent]'s twin, and stated with exactly its
   premises. *)
Lemma hfrun_lookup_TLB_hit_ent (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (ent : TLB_Entry) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = true ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn)
  = Some (Some (tlb_hash (__id 39) vpn, ent), rs).
Proof.
  intros HD Htlb Hvec Hm. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec Hm.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Section strans.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* [translate] on a TLB HIT whose cached leaf needs no A/D update: the
     lookup is one node at the frame, the rest is the bridged exec fact. *)
  Lemma swp_translate_hit (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (vpn : mword 27) (asid : mword 16) (root : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (p2 p1 q0 : mword 64) :
    Drw ## Dro ->
    (tlb : register) ∈ Drw ∪ Dro ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
      = Some (u_walk_entry vpn p2 p1 q0 asid) ->
    match_TLB_Entry (u_walk_entry vpn p2 p1 q0 asid) asid
      (sign_extend' (57 - 12) vpn) = true ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    pte_check_ok acc p mxr do_sum q0 ->
    pte_check_pure acc p mxr do_sum Db q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : mword 64) acc = None ->
    pte_pbmt0 q0 ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Ok (autocast (T := mword)
                           ((autocast (T := mword) (PPN_of_PTE q0)) : mword 44),
                         PBMT_PMA, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDtlb Htlb Hvec Hm HDb Hag Hchk Hpure Hupd Hpb.
    iIntros "#Hcert Hrw Hro".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_lookup_TLB_hit_ent (Drw ∪ Dro) Drw rs vpn asid tlbvec _
                   HDtlb Htlb Hvec Hm)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
              (hval_translate_TLB_hit_pt acc p mxr do_sum Db (Drw ∪ Dro) Drw rs
                 dst vpn p2 p1 q0 asid (tlb_hash (__id 39) vpn)
                 HDb Hag Hchk Hpure Hupd Hpb)
              with "Hcert Hrw Hro").
  Qed.

End strans.
