(** * WeakWalkStale.v — the S-mode page-table walk with a RACY LEAF READ

    THE ONE PLACE THE STALE MIRROR HAS TO MEET THE MODEL.  [WeakStale] is
    generic; this file is the walk.  It states the miss-path translation at
    [WeakStale.exec_stale la 8 pv] — the mirror in which the walk's PLAIN
    leaf read returns the racy word [pv] while the CAS's exclusive re-read
    returns the memory's [p0] — and proves it WITHOUT mirroring
    [WeakWalkEff] / [WeakUpdEff], by the two transfers:

      - the WALK ([pt_walk], three plain reads, one of them the window):
        no PINNED read, so [WeakStale.exec_stale_of_patch_id] turns
        [WeakWalkEff.exec_eff_pt_walk_user] AT THE PATCHED STATE into the
        [exec_stale] fact.  The existing walk library applies verbatim, with
        the leaf slot holding [pv];
      - the CAS ([read_pte_exclusive] + [write_pte_conditional]) and the TLB
        fill: no UNPINNED read, so [WeakStale.exec_stale_of_exec_eff] turns
        [WeakUpdEff]'s arms AT THE REAL STATE into [exec_stale] facts.  Those
        arms already take the STALE word as a parameter separate from the
        freshly-read one — that is the sail fork's atomic recheck, and it is
        why the two-valued statement needs no new model reasoning.

    THE SIXTH OUTCOME.  At [exec_eff] the miss path's O-FRESH arm is
    unreachable: "in a single [exec_eff] run the fresh word IS the walked
    word" ([WeakUpdEff]'s header).  Under a racy plain read it is REACHABLE —
    the stale word lacks a bit the latest already has, so the gate fires, the
    CAS re-reads a word that needs nothing, and the run ends READ-ONLY with
    the adjacent pair's write half missing.  §3's dispatch has three arms
    where the [exec_eff] one has two, and that is the whole observable
    difference the raciness makes.

    Design: claude-notes/design/weak-memory-walk-bridge.md §8. *)
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakCert WeakEff WeakRacy WeakStale.
Require Import WeakFetchEff.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree UserPtTree PtTreeAdue.
Require Import WeakWalkEff WeakUpdEff.
Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The two kinds, and the trace side conditions they make trivial *)

Definition wak_excl : akinfo := AkInfo false true false.

Lemma ak_pins_plain : ak_pins wak_plain = false.
Proof. reflexivity. Qed.

Lemma ak_pins_excl : ak_pins wak_excl = true.
Proof. reflexivity. Qed.

(** A trace of PLAIN reads has no pinned read, so [trace_pin_win] is vacuous
    — which is what lets the whole walk ride the patched memory. *)
Lemma trace_pin_win_plain (ra : Arch.pa) (rn : N) (es : list weff) :
  Forall (fun e => match e with
                   | WEread ak _ _ => ak_pins ak = false
                   | _ => True end) es ->
  trace_pin_win ra rn es.
Proof.
  intros Hall ak pa n Hin Hpin.
  rewrite Forall_forall in Hall.
  specialize (Hall _ (proj1 (elem_of_list_In _ _) Hin)).
  simpl in Hall. congruence.
Qed.

(** ... and a trace with no unpinned read makes [trace_off_win] vacuous,
    which is what lets the CAS ride the real memory. *)
Lemma trace_off_win_pinned (ra : Arch.pa) (rn : N) (es : list weff) :
  Forall (fun e => match e with
                   | WEread ak _ _ => ak_pins ak = true
                   | _ => True end) es ->
  trace_off_win ra rn es.
Proof.
  intros Hall ak pa n Hin Hnp.
  rewrite Forall_forall in Hall.
  specialize (Hall _ (proj1 (elem_of_list_In _ _) Hin)).
  simpl in Hall. congruence.
Qed.

Ltac plain_trace :=
  repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil; exact I.

Ltac pinned_trace :=
  repeat (apply Forall_cons; [try reflexivity; try exact I|]);
  apply Forall_nil; exact I.

(* ====================================================================== *)
(** ** 2. The walk, at the stale mirror

    [WeakWalkEff.exec_eff_pt_walk_user] transferred.  Everything it needs at
    the patched state is a register lookup (which the patch does not touch)
    or one of the three read facts, which the caller supplies AT THE PATCHED
    STATE — where the leaf slot holds the racy word. *)

Section StaleWalk.
  Context (vpn : mword 27) (root : mword 44).
  Context (pte2 pte1 pv : mword 64).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Let addr2 : mword 64 := u_pte_addr root (subrange_vec_dec vpn 26 18).
  Let addr1 : mword 64 := u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9).
  Let addr0 : mword 64 := u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0).

  Hypothesis H2i : wpte_valid pte2.
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : wpte_valid pte1.
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  Hypothesis H0i : wpte_valid pv.
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pv 7 0)) = false.
  Hypothesis Hchk0 : wpte_check_ok acc p mxr do_sum pv.
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pv)) ('b"1") = false.

  Lemma exec_stale_pt_walk_user (menvcfg0 : mword 64) (s : mstate) :
    acc_wf addr0 8 ->
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr addr2) 8) (mpatch addr0 8 pv s)
      = Some (Ok pte2, mpatch addr0 8 pv s, [WEread wak_plain addr2 8]) ->
    exec_eff (read_pte (Physaddr addr1) 8) (mpatch addr0 8 pv s)
      = Some (Ok pte1, mpatch addr0 8 pv s, [WEread wak_plain addr1 8]) ->
    exec_eff (read_pte (Physaddr addr0) 8) (mpatch addr0 8 pv s)
      = Some (Ok pv, mpatch addr0 8 pv s, [WEread wak_plain addr0 8]) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_stale addr0 8 pv (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pv)) : mword 44);
                     PTW_Output_pte := autocast (T := mword) pv;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := u_global pte2 pte1 pv |}, tt), s,
              [WEread wak_plain addr2 8; WEread wak_plain addr1 8;
               WEread wak_plain addr0 8]).
  Proof.
    intros Hracc Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    apply (exec_stale_of_patch_id addr0 8 pv _ s _ _ Hracc).
    - exact (exec_eff_pt_walk_user vpn root pte2 pte1 pv acc p mxr do_sum
               H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N menvcfg0
               [WEread wak_plain addr2 8] [WEread wak_plain addr1 8]
               [WEread wak_plain addr0 8] (mpatch addr0 8 pv s)
               Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
    - rewrite /nowrite_trace. plain_trace.
    - apply trace_pin_win_plain. plain_trace.
  Qed.

End StaleWalk.

(** The quiet transfer, used at every register-only step of the composite. *)
Lemma exec_stale_of_eff_quiet (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    {X} (m : M X) (s t : mstate) (x : X) :
  acc_wf ra rn ->
  exec_eff m s = Some (x, t, []) ->
  exec_stale ra rn w m s = Some (x, t, []).
Proof.
  intros Hracc Hex.
  apply (exec_stale_of_exec_eff ra rn w m Hracc s x t [] Hex).
  intros ak pa n Hin. by apply elem_of_nil in Hin.
Qed.

(* ====================================================================== *)
(** ** 3. THE MISS-PATH TRANSLATION, at the stale mirror

    [WeakWalkEff.exec_eff_translate_TLB_miss_user] and
    [WeakUpdEff.exec_eff_translate_TLB_miss_user_upd], with the walk taken at
    the racy word [pv] and the CAS at the memory's [p0].  THREE arms where
    those two have two: the gate is decided by [pv] and the write by [p0],
    and the case they cannot both agree on — gate fires, memory needs
    nothing — is the sixth outcome. *)

Section StaleMiss.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (** A: the GATE DOES NOT FIRE on the racy word — the walk fills cleanly and
      the CAS is never entered.  ([WeakUpdEff]'s O-UNCHANGED.) *)
  Lemma exec_stale_translate_TLB_miss_none (vpn : mword 27) (root : mword 44)
        (p2 p1 pv : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
        (s : mstate) :
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    acc_wf la 8 ->
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid pv ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pv 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum pv ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pv)) ('b"1") = false ->
    update_PTE_Bits (pv : mword 64) acc = None ->
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p2, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p1, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8]) ->
    exec_eff (read_pte (Physaddr la) 8) (mpatch la 8 pv s)
      = Some (Ok pv, mpatch la 8 pv s, [WEread wak_plain la 8]) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_stale la 8 pv (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44),
                PBMT_PMA, tt),
            set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                             (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn p2 p1 pv asid))),
            [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
             WEread wak_plain la 8]).
  Proof.
    intros la Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N Hnoupd Hmisa
           Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_stale_bind_Some la 8 pv _ _ _ _ _ _
               (exec_stale_pt_walk_user vpn root p2 p1 pv acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N menvcfg0 s
                  Hracc Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec_stale la 8 pv
                       (update_and_write_pte w vp a pv0 lv ac pr mx ds e) s
                     = Some (Ok (None, tt), s, [])) end.
    { apply (exec_stale_of_eff_quiet la 8 pv _ s s _ Hracc).
      exact (exec_eff_update_and_write_pte_none acc p mxr do_sum vpn
               (Physaddr la) pv 0 s Hnoupd). }
    rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s _ _ Hracc
                  (exec_eff_add_to_TLB_pt asid vpn
                     (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                     (autocast (T := mword) pv) (Physaddr la)
                     (u_global p2 p1 pv) s))).
    rewrite exec_stale_returnm. cbn match.
    destruct (pte_set_ad_refl pv) as (av & dv & Hself).
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn p2 p1 pv asid)
        by exact (pt_fill_ent_uwe vpn p2 p1 pv pv asid av dv Hself) end.
    rewrite Hent. by rewrite ?app_nil_r.
  Qed.

  (** B: THE SIXTH OUTCOME.  The gate fires on the racy word, the CAS
      re-reads a word that needs nothing — so the step READS the leaf slot
      twice and writes nothing.  Unreachable at [exec_eff] on the miss path
      (there the fresh word IS the walked word); this is what the raciness
      adds, and the reason the absorption theorem's enumeration grows. *)
  Lemma exec_stale_translate_TLB_miss_fresh (vpn : mword 27) (root : mword 44)
        (p2 p1 pv p0 g : mword 64) (a1 d1 : mword 1)
        (menvcfg0 : mword 64) (asid : mword 16) (s : mstate) :
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    acc_wf la 8 ->
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid pv ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pv 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum pv ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pv)) ('b"1") = false ->
    (* the FRESH word is an A/D variant of the racy one, and needs no bits *)
    p0 = pte_set_ad pv a1 d1 ->
    wpte_valid p0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p0 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum p0 ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE p0)) ('b"1") = false ->
    update_PTE_Bits (pv : mword 64) acc = Some g ->
    update_PTE_Bits (p0 : mword 64) acc = None ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    (* the CAS's re-read, at the REAL state: it returns the memory's word *)
    exec_eff (read_pte_exclusive (Physaddr la) 8) s
      = Some (Ok p0, s, [WEread wak_excl la 8]) ->
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p2, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p1, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8]) ->
    exec_eff (read_pte (Physaddr la) 8) (mpatch la 8 pv s)
      = Some (Ok pv, mpatch la 8 pv s, [WEread wak_plain la 8]) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_stale la 8 pv (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44),
                PBMT_PMA, tt),
            set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                             (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn p2 p1 p0 asid))),
                [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
             WEread wak_plain la 8] ++ [WEread wak_excl la 8]).
  Proof.
    intros la Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N
           Hvar Hfv Hfl Hfchk HfN Hgate Hnoupd HADUE Hrdx Hmisa
           Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_stale_bind_Some la 8 pv _ _ _ _ _ _
               (exec_stale_pt_walk_user vpn root p2 p1 pv acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N menvcfg0 s
                  Hracc Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec_stale la 8 pv
                       (update_and_write_pte w vp a pv0 lv ac pr mx ds e) s
                     = Some (Ok (Some p0, tt), s, [WEread wak_excl la 8])) end.
    { apply (exec_stale_of_exec_eff la 8 pv _ Hracc).
      - exact (exec_eff_update_and_write_pte_fresh acc p mxr do_sum vpn la
                 pv g p0 0 (autocast (T := mword) (PPN_of_PTE p0)) PBMT_PMA
                 menvcfg0 [WEread wak_excl la 8] s
                 Hgate Hmenv HADUE Hrdx
                 (exec_eff_check_leaf_pte_leaf0 vpn p0 acc p mxr do_sum
                    Hfv Hfl Hfchk HfN (Physaddr la) menvcfg0 s
                    Hmisa Hmenv HPBMTE)
                 Hnoupd).
      - apply trace_off_win_pinned. pinned_trace. }
    rewrite (exec_stale_bind_Some la 8 pv _ _ _ _ _ _ Hupd).
    cbn match.
    rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s _ _ Hracc
                  (exec_eff_add_to_TLB_pt asid vpn
                     (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                     (autocast (T := mword) p0) (Physaddr la)
                     (u_global p2 p1 pv) s))).
    rewrite exec_stale_returnm.
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn p2 p1 p0 asid)
        by exact (pt_fill_ent_uwe vpn p2 p1 pv p0 asid a1 d1 Hvar) end.
    rewrite Hent. by rewrite ?app_nil_r.
  Qed.

  (** C: the write-back.  The gate fires on the racy word AND the fresh one
      still needs bits, so the CAS pair lands — and the value written is
      computed from the FRESH word, never from the racy one.  That is the
      atomic recheck, and it is why a stale walk cannot clobber a D bit. *)
  Lemma exec_stale_translate_TLB_miss_written (vpn : mword 27) (root : mword 44)
        (p2 p1 pv p0 p0' g : mword 64) (a1 d1 : mword 1)
        (menvcfg0 : mword 64) (asid : mword 16) (sw s : mstate) :
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    acc_wf la 8 ->
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid pv ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pv 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum pv ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pv)) ('b"1") = false ->
    p0 = pte_set_ad pv a1 d1 ->
    wpte_valid p0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p0 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum p0 ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE p0)) ('b"1") = false ->
    update_PTE_Bits (pv : mword 64) acc = Some g ->
    update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr la) 8) s
      = Some (Ok p0, s, [WEread wak_excl la 8]) ->
    exec_eff (write_pte_conditional (Physaddr la) 8 (p0' : mword 64)) s
      = Some (Ok true, sw, [WEwrite wak_excl la 8 (p0' : mword 64)]) ->
    sw.(sregs) = s.(sregs) ->
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p2, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8)
      (mpatch la 8 pv s)
      = Some (Ok p1, mpatch la 8 pv s,
              [WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8]) ->
    exec_eff (read_pte (Physaddr la) 8) (mpatch la 8 pv s)
      = Some (Ok pv, mpatch la 8 pv s, [WEread wak_plain la 8]) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_stale la 8 pv (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44),
                PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs))
                             (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn p2 p1 p0' asid))),
                [WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
             WEread wak_plain la 8]
            ++ [WEread wak_excl la 8; WEwrite wak_excl la 8 (p0' : mword 64)]).
  Proof.
    intros la Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N
           Hvar Hfv Hfl Hfchk HfN Hgate Hupdf HADUE Hrdx Hwrite Hswregs Hmisa
           Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_stale_bind_Some la 8 pv _ _ _ _ _ _
               (exec_stale_pt_walk_user vpn root p2 p1 pv acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N menvcfg0 s
                  Hracc Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec_stale la 8 pv
                       (update_and_write_pte w vp a pv0 lv ac pr mx ds e) s
                     = Some (Ok (Some p0', tt), sw,
                             ([WEread wak_excl la 8]
                              ++ [WEwrite wak_excl la 8 (p0' : mword 64)])%list)) end.
    { apply (exec_stale_of_exec_eff la 8 pv _ Hracc).
      - exact (exec_eff_update_and_write_pte_written acc p mxr do_sum vpn la
                 pv g p0 p0' 0 (autocast (T := mword) (PPN_of_PTE p0)) PBMT_PMA
                 menvcfg0 [WEread wak_excl la 8]
                 [WEwrite wak_excl la 8 (p0' : mword 64)] sw s
                 Hgate Hmenv HADUE Hrdx
                 (exec_eff_check_leaf_pte_leaf0 vpn p0 acc p mxr do_sum
                    Hfv Hfl Hfchk HfN (Physaddr la) menvcfg0 s
                    Hmisa Hmenv HPBMTE)
                 Hupdf Hwrite).
      - apply trace_off_win_pinned. pinned_trace. }
    rewrite (exec_stale_bind_Some la 8 pv _ _ _ _ _ _ Hupd).
    cbn match.
    rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ sw _ _ Hracc
                  (exec_eff_add_to_TLB_pt asid vpn
                     (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                     (autocast (T := mword) p0') (Physaddr la)
                     (u_global p2 p1 pv) sw))).
    rewrite exec_stale_returnm. rewrite Hswregs.
    destruct (update_PTE_Bits_set_ad _ _ _ Hupdf) as (a2 & d2 & Hq).
    assert (Hvar' : p0' = pte_set_ad pv a2 d2)
      by (rewrite Hq Hvar; exact (pte_set_ad_absorb pv a1 d1 a2 d2)).
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn p2 p1 p0' asid)
        by exact (pt_fill_ent_uwe vpn p2 p1 pv p0' asid a2 d2 Hvar') end.
    rewrite Hent. by rewrite ?app_nil_r.
  Qed.

End StaleMiss.

(* ====================================================================== *)
(** ** 4. The early-return interpreter, at the stale mirror

    [WeakEffSkel.execR_eff]'s twin.  It has to be its own fixpoint for the
    same reason [execR_eff] does — an early return is a VALUE, not a stuck
    program — and it is what the [translateAddr] front is written over.

    Everything here is [WeakEffSkel] §§1–3 with the one changed RAM-read arm
    and, at [_bind_eq], a direct induction where [WeakEffSkel] goes through
    [RiscvTryStep.execR] (the mirror has no such bridge, exactly as in
    [WeakStale] §2). *)

Section StaleR.
  Context (ra : Arch.pa) (rn : N) (w : bv (8 * rn)).

  Fixpoint execR_stale {R X} (m : Defs.monadR R exception X) (s : mstate)
      {struct m} : option (((R + X) * mstate) * list weff) :=
    match m with
    | Interface.Ret y => Some (inr y, s, [])
    | Interface.Next oc k =>
        (match oc in Interface.outcome _ T
               return (T -> Defs.monadR R exception X) ->
                      option (((R + X) * mstate) * list weff) with
         | Interface.RegRead r _ =>
             fun k => execR_stale (k (register_lookup r s.(sregs))) s
         | Interface.RegWrite r _ v =>
             fun k => execR_stale (k tt) (set_reg s r v)
         | Interface.MemRead n req =>
             fun k =>
               if dev_addr (Interface.ReadReq.pa req) then
                 match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
                 | Some (v, d') =>
                     execR_stale (k (inl (v, None))) (MState s.(sregs) s.(mem) d')
                 | None => None
                 end
               else
                 match read_bytes
                         (stale_mem ra rn w
                            (classify (Interface.ReadReq.access_kind req)) s)
                         (Interface.ReadReq.pa req) n with
                 | Some v =>
                     match execR_stale (k (inl (v, None))) s with
                     | Some (y, s', es) =>
                         Some (y, s',
                               WEread (classify (Interface.ReadReq.access_kind req))
                                      (Interface.ReadReq.pa req) n :: es)
                     | None => None
                     end
                 | None => None
                 end
         | Interface.MemWrite n req =>
             fun k =>
               if dev_addr (Interface.WriteReq.pa req) then
                 match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                                 (Interface.WriteReq.value req) with
                 | Some d' =>
                     execR_stale (k (inl None)) (MState s.(sregs) s.(mem) d')
                 | None => None
                 end
               else
                 match execR_stale (k (inl None))
                         (MState s.(sregs)
                            (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                         (Interface.WriteReq.value req))
                            s.(mdev)) with
                 | Some (y, s', es) =>
                     Some (y, s',
                           WEwrite (classify (Interface.WriteReq.access_kind req))
                                   (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req) :: es)
                 | None => None
                 end
         | Interface.InstrAnnounce _    => fun k => execR_stale (k tt) s
         | Interface.BranchAnnounce _ _ => fun k => execR_stale (k tt) s
         | Interface.Barrier b          =>
             fun k => match execR_stale (k tt) s with
                      | Some (y, s', es) => Some (y, s', WEbar b :: es)
                      | None => None
                      end
         | Interface.CacheOp _          => fun k => execR_stale (k tt) s
         | Interface.TlbOp _            => fun k => execR_stale (k tt) s
         | Interface.TakeException _    => fun k => execR_stale (k tt) s
         | Interface.ReturnException _  => fun k => execR_stale (k tt) s
         | Interface.TranslationStart _ => fun k => execR_stale (k tt) s
         | Interface.TranslationEnd _   => fun k => execR_stale (k tt) s
         | Interface.CycleCount         => fun k => execR_stale (k tt) s
         | Interface.Message _          => fun k => execR_stale (k tt) s
         | Interface.GetCycleCount      => fun k => execR_stale (k 0%Z) s
         | Interface.ExtraOutcome e =>
             fun _ => match e with
                      | inl r => Some (inl r, s, [])
                      | inr _ => None
                      end
         | _ => fun _ => None
         end) k
    end.

  Lemma execR_stale_returnR {R X} (x : X) s :
    execR_stale (Defs.returnR R x) s = Some (inr x, s, []).
  Proof. reflexivity. Qed.

  Lemma execR_stale_bind {R X Y} (m : Defs.monadR R exception Y)
      (f : Y -> Defs.monadR R exception X) :
    forall s r st es, execR_stale m s = Some (r, st, es) ->
      execR_stale (Defs.bind m f) s =
        match r with
        | inl e => Some (inl e, st, es)
        | inr a =>
            match execR_stale (f a) st with
            | Some (y, s', es') => Some (y, s', (es ++ es')%list)
            | None => None
            end
        end.
  Proof.
    induction m as [a0 | T oc k IH]; intros s r st es Hm.
    - rewrite bindR_Ret. simpl in Hm. injection Hm as <- <- <-.
      by destruct (execR_stale (f a0) s) as [[[y s'] es']|].
    - rewrite bindR_Next. destruct oc; simpl in Hm |- *; try discriminate;
        try (exact (IH _ _ _ _ _ Hm)).
      + (* MemRead *)
        destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [|discriminate].
          exact (IH _ _ _ _ _ Hm).
        * destruct (read_bytes _ _ _) as [v0|]; [|discriminate].
          destruct (execR_stale (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
          by destruct x0; [|destruct (execR_stale (f _) _) as [[[??]?]|]].
      + (* MemWrite *)
        destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [|discriminate].
          exact (IH _ _ _ _ _ Hm).
        * destruct (execR_stale (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
            [|discriminate].
          injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
          by destruct x0; [|destruct (execR_stale (f _) _) as [[[??]?]|]].
      + (* Barrier *)
        destruct (execR_stale (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hm as <- <- <-. rewrite (IH _ _ _ _ _ Hee).
        by destruct x0; [|destruct (execR_stale (f _) _) as [[[??]?]|]].
      + (* ExtraOutcome: the early return short-circuits the bind *)
        match goal with
        | He : (_ + exception)%type |- _ => destruct He; [|discriminate]
        end. by injection Hm as <- <- <-.
  Qed.

  Lemma execR_stale_bind_None {R X Y} (m : Defs.monadR R exception Y)
      (f : Y -> Defs.monadR R exception X) :
    forall s, execR_stale m s = None -> execR_stale (Defs.bind m f) s = None.
  Proof.
    induction m as [a0 | T oc k IH]; intros s Hm.
    - simpl in Hm. discriminate.
    - rewrite bindR_Next. destruct oc; simpl in Hm |- *; try reflexivity;
        try (exact (IH _ _ Hm)).
      + (* MemRead *)
        destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [|reflexivity].
          exact (IH _ _ Hm).
        * destruct (read_bytes _ _ _) as [v0|]; [|reflexivity].
          destruct (execR_stale (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
            [discriminate|]. by rewrite (IH _ _ Hee).
      + (* MemWrite *)
        destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [|reflexivity].
          exact (IH _ _ Hm).
        * destruct (execR_stale (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
            [discriminate|]. by rewrite (IH _ _ Hee).
      + (* Barrier *)
        destruct (execR_stale (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
          [discriminate|]. by rewrite (IH _ _ Hee).
      + match goal with
        | He : (_ + exception)%type |- _ => by destruct He
        end.
  Qed.

  Lemma execR_stale_bind_eq {R X Y} (m : Defs.monadR R exception Y)
      (f : Y -> Defs.monadR R exception X) s :
    execR_stale (Defs.bind m f) s =
      match execR_stale m s with
      | Some (inl e, st, es) => Some (inl e, st, es)
      | Some (inr a, st, es) =>
          match execR_stale (f a) st with
          | Some (y, s', es') => Some (y, s', (es ++ es')%list)
          | None => None
          end
      | None => None
      end.
  Proof.
    destruct (execR_stale m s) as [[[r st] es]|] eqn:Hm.
    - rewrite (execR_stale_bind m f s r st es Hm). by destruct r.
    - exact (execR_stale_bind_None m f s Hm).
  Qed.

  Lemma execR_stale_bind_cat {R X Y} (m : Defs.monadR R exception Y)
      (f : Y -> Defs.monadR R exception X) s a st es :
    execR_stale m s = Some (inr a, st, es) ->
    execR_stale (Defs.bind m f) s =
      match execR_stale (f a) st with
      | Some (y, s', es') => Some (y, s', (es ++ es')%list)
      | None => None
      end.
  Proof. intros H. exact (execR_stale_bind m f s (inr a) st es H). Qed.

  Lemma execR_stale_bind_nil {R X Y} (m : Defs.monadR R exception Y)
      (f : Y -> Defs.monadR R exception X) s a st :
    execR_stale m s = Some (inr a, st, []) ->
    execR_stale (Defs.bind m f) s = execR_stale (f a) st.
  Proof.
    intros H. rewrite (execR_stale_bind_cat m f s a st [] H).
    by destruct (execR_stale (f a) st) as [[[y s'] es']|].
  Qed.

  (** A lifted base computation never early-returns: its [execR_stale] is its
      [exec_stale] with an [inr] on the value. *)
  Lemma execR_stale_liftR {R X} (m : M X) :
    forall s, execR_stale (Defs.liftR (R:=R) m) s =
      match exec_stale ra rn w m s with
      | Some (x, s', es) => Some (inr x, s', es)
      | None => None
      end.
  Proof.
    unfold Defs.liftR. induction m as [x0 | T oc k IH]; intros s.
    - reflexivity.
    - destruct oc; cbn [Defs.try_catch execR_stale exec_stale Defs.throw];
        try (apply IH); try reflexivity.
      + destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [apply IH|reflexivity].
        * destruct (read_bytes _ _ _) as [v0|]; [|reflexivity].
          rewrite IH. by destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|].
      + destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [apply IH|reflexivity].
        * rewrite IH. by destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|].
      + rewrite IH. by destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|].
  Qed.

  Lemma execR_stale_liftR_cat {R X Y} (m : M Y)
      (f : Y -> Defs.monadR R exception X) (s st : mstate) (x : Y) es :
    exec_stale ra rn w m s = Some (x, st, es) ->
    execR_stale (Defs.bind (Defs.liftR m) f) s =
      match execR_stale (f x) st with
      | Some (y, s', es') => Some (y, s', (es ++ es')%list)
      | None => None
      end.
  Proof.
    intros Hm. apply (execR_stale_bind_cat _ f s x st es).
    by rewrite execR_stale_liftR Hm.
  Qed.

  Lemma execR_stale_liftR_seq {R X Y} (m : M Y)
      (f : Y -> Defs.monadR R exception X) (s st : mstate) (x : Y) :
    exec_stale ra rn w m s = Some (x, st, []) ->
    execR_stale (Defs.bind (Defs.liftR m) f) s = execR_stale (f x) st.
  Proof.
    intros Hm. apply (execR_stale_bind_nil _ f s x st).
    by rewrite execR_stale_liftR Hm.
  Qed.

  Lemma exec_stale_catch_early_return {X} (body : Defs.monadR X exception X) :
    forall s, exec_stale ra rn w (Defs.catch_early_return body) s =
      match execR_stale body s with
      | Some (inl r, s', es) => Some (r, s', es)
      | Some (inr r, s', es) => Some (r, s', es)
      | None => None
      end.
  Proof.
    unfold Defs.catch_early_return.
    induction body as [a0 | T oc k IH]; intros s.
    - reflexivity.
    - destruct oc; cbn [Defs.try_catch exec_stale execR_stale Defs.throw Defs.returnm];
        try (apply IH); try reflexivity.
      + destruct (dev_addr _).
        * destruct (dev_read _ _ _) as [[v0 d']|]; [apply IH|reflexivity].
        * destruct (read_bytes _ _ _) as [v0|]; [|reflexivity].
          rewrite IH. by destruct (execR_stale (k _) s) as [[[[?|?] t0] es0]|].
      + destruct (dev_addr _).
        * destruct (dev_write _ _ _ _) as [d'|]; [apply IH|reflexivity].
        * rewrite IH. by destruct (execR_stale (k _) _) as [[[[?|?] t0] es0]|].
      + rewrite IH. by destruct (execR_stale (k tt) s) as [[[[?|?] t0] es0]|].
      + match goal with
        | He : (_ + exception)%type |- _ => by destruct He
        end.
  Qed.

End StaleR.

(* ====================================================================== *)
(** ** 5. THE [translateAddr] FRONT, at the stale mirror

    [WeakWalkEff.exec_eff_translateAddr_pt_front] replayed.  The front itself
    performs NO memory access — its whole trace is the [translate]'s — so
    every step of the script is either a register read (identical in the two
    interpreters) or an empty-trace sub-run that §3's transfer carries. *)

Section StaleFront.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma exec_stale_translateAddr_pt_front (la : Arch.pa) (pv : mword 64)
        (vpn : mword 27) (root : mword 44) (ppnv : mword 44)
        (satp0 va pa : mword 64) (es_tr : list weff) (s s' : mstate) :
    acc_wf la 8 ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)
      (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec_stale la 8 pv
         (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt) s
       = Some (Ok (ppnv, PBMT_PMA, tt), s', es_tr)) ->
    zero_extend' 64 (concat_vec ppnv
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    exec_stale la 8 pv (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s', es_tr).
  Proof.
    intros Hracc Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Htr Hident.
    unfold translateAddr.
    rewrite (exec_stale_catch_early_return la 8 pv).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_read_reg la 8 pv mstatus s)).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_read_reg la 8 pv cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s s _ Hracc Heff)).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s s _ Hracc Htm)).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s s _ Hracc Hss)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite (execR_stale_bind_eq la 8 pv). rewrite (execR_stale_returnR la 8 pv).
    cbn match.
    assert (Hwidth : exec_stale la 8 pv (satp_mode_width_forwards Sv39) s
                     = Some (39, s, []))
      by (cbn; apply (exec_stale_returnm la 8 pv)).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _ Hwidth).
    assert (Hgs : exec_stale la 8 pv (get_satp 39) s
                  = Some (autocast (T := mword) satp0, s, [])).
    { unfold get_satp.
      assert (Hae : exec_stale la 8 pv
                      (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                         "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s, [])).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
          by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply (exec_stale_returnm la 8 pv). }
      rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _
                 (exec_stale_read_reg la 8 pv satp s)).
      rewrite Hsatp. apply (exec_stale_returnm la 8 pv). }
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _ Hgs).
    assert (Hae2 : exec_stale la 8 pv
                     (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                        "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s, [])).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true
        by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply (exec_stale_returnm la 8 pv). }
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_read_reg la 8 pv mstatus s)).
    rewrite (execR_stale_liftR_seq la 8 pv _ _ _ _ _
               (exec_stale_read_reg la 8 pv mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_stale_liftR_cat la 8 pv _ _ _ _ _ _ (Htr _ _)).
    cbn match.
    rewrite (execR_stale_returnR la 8 pv). cbn match.
    match goal with |- context[Physaddr ?e] =>
      replace e with pa by (symmetry; exact Hident) end.
    by rewrite ?app_nil_r.
  Qed.

  (** The [translate] head: a TLB miss is register-only, so the dispatch
      transfers and the whole trace is the miss path's. *)
  Lemma exec_stale_translate_miss (la : Arch.pa) (pv : mword 64)
        (vpn : mword 27) (root : mword 44) (asid : mword 16)
        (mxr do_sum : bool)
        (r : result (mword 44 * page_based_mem_type * unit) (PTW_Error * unit))
        (s s' : mstate) (es : list weff) :
    acc_wf la 8 ->
    exec_eff (lookup_TLB 39 asid vpn) s = Some (None, s, []) ->
    exec_stale la 8 pv (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (r, s', es) ->
    exec_stale la 8 pv (translate 39 asid root vpn acc p mxr do_sum tt) s
      = Some (r, s', es).
  Proof.
    intros Hracc Hlk Hmiss.
    unfold translate.
    rewrite (exec_stale_bind_nil la 8 pv _ _ _ _ _
               (exec_stale_of_eff_quiet la 8 pv _ s s _ Hracc Hlk)).
    cbn match. exact Hmiss.
  Qed.

End StaleFront.

(* ====================================================================== *)
(** ** 6. THE RACY WALK, END TO END

    [WeakUpdEff.exec_eff_translateAddr_pt_miss_upd]'s racy twin, and the
    theorem this file exists for: ONE [translateAddr] fact at the stale
    mirror, covering every outcome a TLB-miss walk can take when its plain
    leaf read returns a variant [pv] of the memory's word [p0].

    THREE outcomes where the [exec_eff] statement has two:

      - the gate does not fire on [pv] — clean fill, three plain reads;
      - it fires but the FRESH word needs nothing — the CAS re-reads and
        stops: FOUR reads, NO write.  This is the arm raciness adds, and it
        is why the absorption theorem's trace enumeration grows;
      - it fires and the fresh word still needs bits — the CAS pair lands,
        and the word written is computed from the FRESH read.

    In all three the translated address [pa] is the SAME: it is a function of
    the walked word's PPN, and every variant of a leaf shares it.  That is
    what makes the racy walk absorbable at all. *)

Section StaleCases.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma exec_stale_translateAddr_pt_miss_cases
        (vpn : mword 27) (root : mword 44)
        (p2 p1 pv p0 : mword 64) (a1 d1 : mword 1)
        (satp0 va pa menvcfg0 : mword 64) (s : mstate) :
    let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
    let e2 := WEread wak_plain (u_pte_addr root (subrange_vec_dec vpn 26 18)) 8 in
    let e1 := WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8 in
    let e0 := WEread wak_plain la 8 in
    acc_wf la 8 ->
    (* the front *)
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)
      (Z.sub 39 1) pagesize_bits) = vpn ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    zero_extend' 64 (concat_vec
      (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44) : mword 44)
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (* the walk *)
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid pv ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pv 7 0)) = false ->
    (forall mxr do_sum, wpte_check_ok acc p mxr do_sum pv) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pv)) ('b"1") = false ->
    (* the FRESH word: an A/D variant of the racy one, and a leaf too *)
    p0 = pte_set_ad pv a1 d1 ->
    wpte_valid p0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p0 7 0)) = false ->
    (forall mxr do_sum, wpte_check_ok acc p mxr do_sum p0) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE p0)) ('b"1") = false ->
    (* the reads: the walk's at the PATCHED memory, the CAS's at the REAL one *)
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      (mpatch la 8 pv s) = Some (Ok p2, mpatch la 8 pv s, [e2]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8)
      (mpatch la 8 pv s) = Some (Ok p1, mpatch la 8 pv s, [e1]) ->
    exec_eff (read_pte (Physaddr la) 8) (mpatch la 8 pv s)
      = Some (Ok pv, mpatch la 8 pv s, [e0]) ->
    exec_eff (read_pte_exclusive (Physaddr la) 8) s
      = Some (Ok p0, s, [WEread wak_excl la 8]) ->
    (* the conditional write, wherever the fresh word still needs bits *)
    (forall p0' : mword 64, update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
       exec_eff (write_pte_conditional (Physaddr la) 8 (p0' : mword 64)) s
       = Some (Ok true,
               MState s.(sregs) (write_bytes s.(mem) la 8 (p0' : mword 64)) s.(mdev),
               [WEwrite wak_excl la 8 (p0' : mword 64)])) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exists (sg' : mstate) (es : list weff),
      exec_stale la 8 pv (translateAddr (Virtaddr va) acc) s
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es) /\
      mdev sg' = s.(mdev) /\
      (exists tv, sregs sg' = register_set tlb tv s.(sregs)) /\
      ( (* the two READ-ONLY outcomes *)
        (mem sg' = s.(mem) /\ (es = [e2; e1; e0] \/
                               es = [e2; e1; e0] ++ [WEread wak_excl la 8]))
        \/
        (* the write-back *)
        (exists p0' : mword 64,
           update_PTE_Bits (p0 : mword 64) acc = Some p0' /\
           mem sg' = write_bytes s.(mem) la 8 (p0' : mword 64) /\
           es = [e2; e1; e0] ++ [WEread wak_excl la 8;
                                 WEwrite wak_excl la 8 (p0' : mword 64)]) ).
  Proof.
    intros la e2 e1 e0 Hracc Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def
           Hlk Hident Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchkall H0N
           Hvar Hfv Hfl Hfchkall HfN Hrd2 Hrd1 Hrd0 Hrdx Hwrite
           Hmisa Hmenv HPBMTE HADUE.
    (* the gate is decided by the RACY word, the write by the FRESH one *)
    destruct (update_PTE_Bits (pv : mword 64) acc) as [g|] eqn:Hgate.
    - destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupdf.
      + (* O-WRITTEN *)
        eexists _, _. split_and!.
        * apply (exec_stale_translateAddr_pt_front acc p la pv vpn root
                   (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                   satp0 va pa _ s _ Hracc Heff Hss Hcp Htm Hsatp Hppn Hasid
                   Hcanon Hvpn_def); [|exact Hident].
          intros mxr do_sum.
          apply (exec_stale_translate_miss acc p la pv vpn root
                   (mword_of_int 0) mxr do_sum _ s _ _ Hracc Hlk).
          exact (exec_stale_translate_TLB_miss_written acc p mxr do_sum vpn root
                   p2 p1 pv p0 p0' g a1 d1 menvcfg0 (mword_of_int 0)
                   (MState s.(sregs) (write_bytes s.(mem) la 8 (p0' : mword 64)) s.(mdev))
                   s Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchkall mxr do_sum) H0N
                   Hvar Hfv Hfl (Hfchkall mxr do_sum) HfN Hgate Hupdf HADUE
                   Hrdx (Hwrite p0' eq_refl) eq_refl Hmisa Hrd2 Hrd1 Hrd0
                   Hmenv HPBMTE).
        * by rewrite mdev_set_reg.
        * eexists. by rewrite sregs_set_reg.
        * right. exists p0'. split_and!; [reflexivity| |reflexivity].
          by rewrite mem_set_reg.
      + (* O-FRESH — the sixth outcome *)
        eexists _, _. split_and!.
        * apply (exec_stale_translateAddr_pt_front acc p la pv vpn root
                   (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                   satp0 va pa _ s _ Hracc Heff Hss Hcp Htm Hsatp Hppn Hasid
                   Hcanon Hvpn_def); [|exact Hident].
          intros mxr do_sum.
          apply (exec_stale_translate_miss acc p la pv vpn root
                   (mword_of_int 0) mxr do_sum _ s _ _ Hracc Hlk).
          exact (exec_stale_translate_TLB_miss_fresh acc p mxr do_sum vpn root
                   p2 p1 pv p0 g a1 d1 menvcfg0 (mword_of_int 0) s
                   Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchkall mxr do_sum) H0N
                   Hvar Hfv Hfl (Hfchkall mxr do_sum) HfN Hgate Hupdf HADUE
                   Hrdx Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
        * by rewrite mdev_set_reg.
        * eexists. by rewrite sregs_set_reg.
        * left. split; [by rewrite mem_set_reg|]. by right.
    - (* O-UNCHANGED: the gate does not fire on the racy word *)
      eexists _, _. split_and!.
      + apply (exec_stale_translateAddr_pt_front acc p la pv vpn root
                 (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (pv : mword 64))) : mword 44))
                 satp0 va pa _ s _ Hracc Heff Hss Hcp Htm Hsatp Hppn Hasid
                 Hcanon Hvpn_def); [|exact Hident].
        intros mxr do_sum.
        apply (exec_stale_translate_miss acc p la pv vpn root
                 (mword_of_int 0) mxr do_sum _ s _ _ Hracc Hlk).
        exact (exec_stale_translate_TLB_miss_none acc p mxr do_sum vpn root
                 p2 p1 pv menvcfg0 (mword_of_int 0) s
                 Hracc Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchkall mxr do_sum) H0N
                 Hgate Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
      + by rewrite mdev_set_reg.
      + eexists. by rewrite sregs_set_reg.
      + left. split; [by rewrite mem_set_reg|]. by left.
  Qed.

End StaleCases.
