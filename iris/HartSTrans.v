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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras
        RiscvFetchExec RiscvTryStep.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb.
Require Import WpDecodeBridge Pt4kWalk CommonWalk PtTree PtTreeAdue.
Require Import HartMFetch HartMPmp SmodePte.
Local Open Scope Z_scope.

(* the same spelling [HartMFetch] uses for the misalignment tests *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

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

(* the lookup's MISS cases, footprinted.  Like the hit
   ([HartSTrans.hfrun_lookup_TLB_hit_ent]) these cannot go through the
   [goodb] bridge: the [tlb] register's value is whatever this hart's frame
   says, not what the reference state says.  One read, then a pure match --
   [SmodePte.exec_lookup_TLB_nomatch_s]'s twin, stated with its premises. *)
Lemma hfrun_lookup_TLB_nomatch (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16) (ent' : TLB_Entry)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' asid (sign_extend' (57 - 12) vpn) = false ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn) = Some (None, rs).
Proof.
  intros HD Htlb Hvec Hnm. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec Hnm.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* ...and the EMPTY slot, which the model treats identically. *)
Lemma hfrun_lookup_TLB_empty (D Drw : gset register) (rs : regstate)
    (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (tlb : register) ∈ D ->
  register_lookup tlb rs = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  hfrun 2 D Drw rs (lookup_TLB 39 asid vpn) = Some (None, rs).
Proof.
  intros HD Htlb Hvec. unfold lookup_TLB.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  rewrite Htlb Hvec.
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* THE SUPERVISOR PMP CHECK, FOOTPRINTED.                                  *)
(*                                                                        *)
(* [HartMPmp.mpmp_hval] cannot serve here and the reason is not the        *)
(* privilege argument, it is the DEFAULT.  At Machine a walk that matches  *)
(* no entry falls through to ALLOW, so that proof is a 16-entry loop        *)
(* induction whose every exit is [Ret None].  At Supervisor the fall-      *)
(* through is DENY, so a granting walk must actually MATCH -- and the      *)
(* xv6 configuration grants through entry 0 (TOR, base 0, R/W/X set),      *)
(* which the exec side already states as                                  *)
(* [SmodePte.exec_pmpCheck_supervisor_grant_load].                        *)
(*                                                                        *)
(* That makes this the SHORTER proof of the two: entry 0 matches, so the   *)
(* walk early-returns on the FIRST iteration and no loop invariant is      *)
(* needed at all.  What it costs instead is that the walk cannot go        *)
(* through the [goodb] bridge -- [goodb] rejects [ExtraOutcome], which is  *)
(* exactly the node an early return is -- so the reads are peeled at the   *)
(* [hspan] level, the way the M-mode walk peels its own.                   *)
(* ====================================================================== *)

Local Ltac spmp_red H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.read_reg
     pmpReadAddrReg Defs.early_return Defs.throw sys_pmp_grain Z.geb
     Z.compare andb not negb pmpCheckRWX Defs.or_boolM] in H.

Local Ltac spmp_peel_any reg H Hstop v rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep) as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

Local Ltac spmp_peel_D reg H Hstop HD rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_D_inv _ _ reg _ _ _ Hat HD Hstep) as (rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* [SmodePte.exec_pmpMatchAddr_TOR_match] with the state dropped: its proof
   is three rewrites and never touches [s], so the PURE equation is what a
   footprint peel can actually rewrite with. *)
Lemma pmpMatchAddr_TOR_match_pure (addr width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4)
    (uint addr) (uint width) = PMP_Match ->
  pmpMatchAddr (Physaddr addr) width ent pmpaddr prev = returnM PMP_Match.
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. reflexivity.
Qed.

Lemma spmp_hval_grant (D Drw : gset register)
    (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
    (addr : SailStdpp.Values.mword 64) (rs : regstate) (wd : Z)
    (acc : MemoryAccessType mem_payload) :
  (pmpcfg_n : register) ∈ D ->
  (pmpaddr_n : register) ∈ D ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup pmpaddr_n rs = paddr ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec paddr 0)) 4)
    (uint addr) (uint (to_bits 64 wd)) = PMP_Match ->
  (* the entry GRANTS this access class.  Pure: [pmpCheckRWX] only reads the
     entry's permission bits, so the caller supplies it as an equation and no
     state reaches this premise. *)
  pmpCheckRWX (vec_access_dec pcfg 0) acc = returnM true ->
  hval D Drw rs (pmpCheck (Physaddr addr) wd acc Supervisor) None rs.
Proof.
  intros HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx rs0 l Hag0 Hchain Hstop.
  unfold pmpCheck in Hchain.
  replace (Z.eqb sys_pmp_count 0) with false in Hchain
    by (vm_compute; reflexivity).
  replace (Z.sub sys_pmp_count 1) with 15 in Hchain
    by (vm_compute; reflexivity).
  unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  spmp_red Hchain.
  (* ONE iteration: entry 0 matches, so the walk never reaches entry 1 *)
  cbn [Defs.foreach_ZM_up'] in Hchain.
  spmp_red Hchain.
  (* the entry's cfg byte, pinned *)
  spmp_peel_D pmpcfg_n Hchain Hstop HDcfg rs1 Hag1.
  rewrite (Hag0 _ HDcfg) Hpcfg in Hchain.
  spmp_red Hchain.
  (* [pmpReadAddrReg 0] reads cfg again (value-dead: the grain adjustment is
     [false] at [sys_pmp_grain = 0] whatever the entry says) then pmpaddr *)
  spmp_peel_any pmpcfg_n Hchain Hstop w2 rs2 Hag2. spmp_red Hchain.
  (* the peel substitutes the value read from the file it was AT, so the
     agreement that transports it is the one for the PRE-peel file *)
  assert (Hag12 : reg_agree_on D rs2 rs).
  { intros r Hr. rewrite (Hag2 r Hr) (Hag1 r Hr). exact (Hag0 r Hr). }
  spmp_peel_D pmpaddr_n Hchain Hstop HDaddr rs3 Hag3.
  rewrite (Hag12 _ HDaddr) Hpaddr in Hchain.
  assert (Hag13 : reg_agree_on D rs3 rs).
  { intros r Hr. rewrite (Hag3 r Hr). exact (Hag12 r Hr). }
  spmp_red Hchain.
  (* the address match is now on concrete values: TOR + in range = Match *)
  rewrite (pmpMatchAddr_TOR_match_pure addr (to_bits 64 wd)
             (vec_access_dec pcfg 0) (vec_access_dec paddr 0) (zeros' 64)
             HA Hord Hrange) in Hchain.
  spmp_red Hchain.
  (* granted by the entry's permission bit -- at Supervisor the second
     disjunct of [or_boolM] (Machine and unlocked) is unavailable, and this
     is the whole difference from the M-mode walk *)
  rewrite Hrwx in Hchain.
  spmp_red Hchain.
  assert (Hl : l = (Interface.Ret None, rs3))
    by (apply (hspan_stop_refl D Drw _ rs3 l); [reflexivity | exact Hchain]).
  rewrite Hl. cbn. split; [reflexivity | exact Hag13].
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

  (* ------------------------------------------------------------------ *)
  (* [translate] on a MISS.  Assembly only: the lookup is the footprinted  *)
  (* node above, the walk and the install are CommonWalk's converted        *)
  (* chain.  The walk's per-PTE hypotheses are threaded positionally, the   *)
  (* same way KptTree threads them on the exec side.                       *)
  (*                                                                      *)
  (* This is the first rule in the S-mode translation whose POST-FILE       *)
  (* differs from its pre-file: the miss installs a TLB entry.             *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translate_miss (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate)
      (vpn : mword 27) (root : mword 44) (asid : mword 16)
      (pte2 pte1 pte0 : mword 64) (menvcfg0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (slot : option TLB_Entry) :
    (* the walk's own hypotheses, in the section's order *)
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                      (ext_bits_of_PTE pte2)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                      (ext_bits_of_PTE pte1)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
    (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                      (ext_bits_of_PTE pte0)) s = Some (false, s)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
    (forall s, exec (check_PTE_permission acc p mxr do_sum
                       (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                       (ext_bits_of_PTE pte0) tt) s
               = Some (PTE_Check_Success tt, s)) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s = true) ->
    (forall Db s, goodb Db (pte_is_invalid
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s = true) ->
    (forall Db s, goodb Db (check_PTE_permission acc p mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s = true) ->
    (* the lookup misses: the slot is empty, or holds a foreign entry *)
    Drw ## Dro ->
    (tlb : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    register_lookup tlb rs = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = slot ->
    match slot with
    | None => True
    | Some e => match_TLB_Entry e asid (sign_extend' (57 - 12) vpn) = false
    end ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = None ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
         (fun r => ⌜r = Values.Ok pte2⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte2)
                        (subrange_vec_dec vpn 17 9))) 8)
         (fun r => ⌜r = Values.Ok pte1⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (read_pte (Physaddr (u_pte_addr (u_next_base pte1)
                        (subrange_vec_dec vpn 8 0))) 8)
         (fun r => ⌜r = Values.Ok pte0⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (translate 39 asid root vpn acc p mxr do_sum tt)
      (fun r => ⌜r = Values.Ok (autocast (T := mword)
                       ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44),
                     PBMT_PMA, tt)⌝ ∗
                hreg_frame (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 pte0 asid))) rs) Drw ∗
                hreg_frame_ro Df (register_set tlb
                    (vec_update_dec (register_lookup tlb rs)
                       (tlb_hash (__id 39) vpn)
                       (Some (u_walk_entry vpn pte2 pte1 pte0 asid))) rs) Dro).
  Proof.
    intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
      Hdisj HDtlb HWtlb Htlb Hvec Hslot HD Hag Hmisa Hmenv HPBMTE Hnoupd.
    iIntros "#Hcert Hrw Hro Hrd2 Hrd1 Hrd0".
    unfold translate.
    iApply (swp_bind_use (lookup_TLB 39 asid vpn) _ _ _ with "[Hrw Hro] [-]").
    { destruct slot as [e |].
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_nomatch (Drw ∪ Dro) Drw rs vpn asid e tlbvec
                     HDtlb Htlb Hvec Hslot)
                  with "Hcert Hrw Hro").
      - iApply (swp_hfrun 2 Drw Dro Df rs rs _ _ Hdisj
                  (hfrun_lookup_TLB_empty (Drw ∪ Dro) Drw rs vpn asid tlbvec
                     HDtlb Htlb Hvec)
                  with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    iApply (swp_translate_TLB_miss_user vpn root pte2 pte1 pte0 acc p mxr do_sum
              H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N H1ig H2ig H0ig Hchk0g
              Drw Dro Df rs dst asid menvcfg0 Hdisj HD Hag HWtlb Hmisa Hmenv
              HPBMTE Hnoupd with "Hcert Hrw Hro Hrd2 Hrd1 Hrd0").
  Qed.


  (* ------------------------------------------------------------------ *)
  (* [fetch_bytes] AT SUPERVISOR.  Structurally the M-mode twin           *)
  (* ([HartMFetch.swp_fetch_bytes_M]) and it takes the same shape of        *)
  (* obligation, but the address the READ uses is the TRANSLATED one:       *)
  (* M-mode reads at [Physaddr pc] only because Bare translation is the     *)
  (* identity.  The translation is an obligation because it may WRITE (the  *)
  (* TLB fill), which is why the read runs at a different file [rsf].       *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_fetch_bytes_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rsf = Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes pc pc 4)
      (fun r => ⌜r = @FetchBytes_Success 4 w⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr pc) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M Drw Dro Df rsf (Physaddr pa) w Supervisor Hdisj
                HDmst HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 4 w)). by iFrame.
  Qed.


  (* ==================================================================== *)
  (* THE S-MODE FETCH.  This is [HartRunGen]'s outstanding obligation, and  *)
  (* it needed no new fetch rule: [HartMFetch.swp_fetch] was already        *)
  (* privilege-generic, and once its LANDING FILE became a parameter it     *)
  (* serves both modes.  What is S-mode-specific is entirely below it --    *)
  (* the translation walks and may fill the TLB, which is what [rsf] is.    *)
  (* ==================================================================== *)
  Lemma swp_fetch_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (w : mword 32) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rsf = Supervisor ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 4 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = (if isRVC (subrange_vec_dec w 15 0)
                      then F_RVC (subrange_vec_dec w 15 0)
                      else F_Base w)⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmst HDpriv Hpc Hpriv Hb0 Hb1 Hal.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (swp_fetch Drw Dro Df rs rsf pc w Hdisj HDpc Hpc Hb0 Hb1 Hal
              with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_S Drw Dro Df rs rsf pc pa w Hdisj HDmst HDpriv
              Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.


  (* the HALFWORD fetch_bytes at Supervisor, [swp_fetch_bytes_S]'s twin one
     width down: the model translates and reads at [granule_start], and a
     base instruction's second halfword is fetched at [pc+2] while
     [fetch_start] stays [pc] -- so the two addresses are separate here for
     the same reason they are in [HartMFetch.swp_fetch_bytes_M2]. *)
  Lemma swp_fetch_bytes_S2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (fs gs pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rsf = Supervisor ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr gs) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch_bytes fs gs 2)
      (fun r => ⌜r = @FetchBytes_Success 2 h⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv Hpriv.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold fetch_bytes.
    cbn beta iota zeta delta [ext_fetch_check_pc].
    rewrite mbind0_ret.
    iApply (swp_use_cer (translateAddr (Virtaddr gs) (InstructionFetch tt))
              _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer
              (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2
                 false false false) _ _ C HC with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_mem_read_M2 Drw Dro Df rsf (Physaddr pa) h Supervisor Hdisj
                HDmst HDpriv Hpriv with "Hcert Hrw Hro Hcmr"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite autocast_id mcer_ret.
    iApply ("Hcont" $! (@FetchBytes_Success 2 h)). by iFrame.
  Qed.

  (* the 2-mod-4 COMPRESSED shape at Supervisor *)
  Lemma swp_fetch_S_rvc2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf : regstate) (pc pa : mword 64) (h : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup cur_privilege rsf = Supervisor ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    (hreg_frame rsf Drw -∗ hreg_frame_ro Df rsf Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa) 2 false false false false)
         (fun r => ⌜r = Values.Ok (h, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_RVC h⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpriv HmisaC Hb0 Hb1 Hal4 Hrvc.
    iIntros "#Hcert Hrw Hro Htr Hcmr".
    iApply (swp_fetch_rvc2 Drw Dro Df rs rsf pc h Hdisj HDpc HDmisa Hpc Hb0
              Hb1 Hal4 HmisaC Hrvc with "Hcert Hrw Hro [Htr Hcmr]").
    iIntros "Hrw Hro".
    iApply (swp_fetch_bytes_S2 Drw Dro Df rs rsf pc pc pa h Hdisj HDmst
              HDpriv Hpriv with "Hcert Hrw Hro Htr Hcmr").
  Qed.


  (* the 2-mod-4 BASE shape at Supervisor: TWO halfword fetches, so TWO
     translations -- and the first may already have filled the TLB, which is
     why [swp_fetch_base2] threads an intermediate file.  The second
     translation therefore starts at [rsf1], and the PC the model re-reads
     between them is pinned there. *)
  Lemma swp_fetch_S_base2 (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rsf1 rsf2 : regstate) (pc pa1 pa2 : mword 64)
      (ilo ihi : mword 16) :
    Drw ## Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup (R_bitvector_64 PC) rsf1 = pc ->
    register_lookup cur_privilege rsf1 = Supervisor ->
    register_lookup cur_privilege rsf2 = Supervisor ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    neq_vec (access_vec_dec pc 0) zerobit = false ->
    neq_vec (access_vec_dec pc 1) zerobit = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC ilo = false ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (* the low halfword: translate pc, read there *)
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr pc) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf1 Drw ∗ hreg_frame_ro Df rsf1 Dro)) -∗
    (hreg_frame rsf1 Drw -∗ hreg_frame_ro Df rsf1 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa1) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ilo, tt)⌝ ∗
                   hreg_frame rsf1 Drw ∗ hreg_frame_ro Df rsf1 Dro)) -∗
    (* the high halfword: translate pc+2, read there *)
    (hreg_frame rsf1 Drw -∗ hreg_frame_ro Df rsf1 Dro -∗
       swp (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt))
         (fun r => ⌜r = Values.Ok (Physaddr pa2, PBMT_PMA, init_ext_ptw)⌝ ∗
                   hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro)) -∗
    (hreg_frame rsf2 Drw -∗ hreg_frame_ro Df rsf2 Dro -∗
       swp (checked_mem_read (InstructionFetch tt) PBMT_PMA Supervisor
              (Physaddr pa2) 2 false false false false)
         (fun r => ⌜r = Values.Ok (ihi, tt)⌝ ∗
                   hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro)) -∗
    swp (fetch tt)
      (fun r => ⌜r = F_Base (concat_vec ihi ilo)⌝ ∗
                hreg_frame rsf2 Drw ∗ hreg_frame_ro Df rsf2 Dro).
  Proof.
    intros Hdisj HDpc HDmisa HDmst HDpriv Hpc Hpc1 Hpriv1 Hpriv2 HmisaC
      Hb0 Hb1 Hal4 Hnrvc.
    iIntros "#Hcert Hrw Hro Htr1 Hcmr1 Htr2 Hcmr2".
    iApply (swp_fetch_base2 Drw Dro Df rs rsf1 rsf2 pc ilo ihi Hdisj HDpc
              HDmisa Hpc Hb0 Hb1 Hal4 HmisaC Hnrvc Hpc1
              with "Hcert Hrw Hro [Htr1 Hcmr1] [Htr2 Hcmr2]").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_S2 Drw Dro Df rs rsf1 pc pc pa1 ilo Hdisj HDmst
                HDpriv Hpriv1 with "Hcert Hrw Hro Htr1 Hcmr1").
    - iIntros "Hrw Hro".
      iApply (swp_fetch_bytes_S2 Drw Dro Df rsf1 rsf2 pc (add_vec_int pc 2)
                pa2 ihi Hdisj HDmst HDpriv Hpriv2
                with "Hcert Hrw Hro Htr2 Hcmr2").
  Qed.


  (* the [swp] face of [spmp_hval_grant] -- one [swp_span], as with
     [HartMPmp]'s M-mode instances. *)
  Lemma swp_pmpCheck_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (addr : SailStdpp.Values.mword 64) (wd : Z) :
    Drw ## Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint addr) (uint (to_bits 64 wd)) = PMP_Match ->
    pmpCheckRWX (vec_access_dec pcfg 0) acc = returnM true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (pmpCheck (Physaddr addr) wd acc Supervisor)
      (fun r => ⌜r = None⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx.
    exact (swp_span Drw Dro Df rs rs _ None Hdisj
             (spmp_hval_grant (Drw ∪ Dro) Drw pcfg paddr addr rs wd acc
                HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx)).
  Qed.

End strans.
