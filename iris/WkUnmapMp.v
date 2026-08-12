(** * WkUnmapMp.v — THE UNMAP-SIDE PROTOTYPE: pinnedness from delivery,
    and the fault it licenses

    THE EXPERIMENT (claude-notes/projects/weak-memory.md, the CHECKPOINT's
    NEXT item 2 — "the USER page tables").  [WkClipAdvance] was step 0: it
    showed the clipped variant layer survives an ADVANCING cut, so that
    after [uvmunmap]'s [*pte = 0] every RACILY observable value of the slot
    is an A/D variant of the zero word.  That is the pessimistic story —
    the one that holds even when the reader has NOT synchronised with the
    unmapping hart.

    THIS FILE IS THE OPTIMISTIC HALF, and it is the one the real xv6
    argument runs on.  The observation, in one sentence:

        ONCE THE ZERO STORE HAS BEEN *DELIVERED* TO A HART — i.e. that
        hart's read floor [w_vrNew] covers the store's timestamp — AND
        NOTHING HAS WRITTEN THE SLOT SINCE, THE SLOT IS *PINNED* FOR THAT
        HART, AND THE WALK OF IT NEEDS NO RACY MACHINERY AT ALL.

    Why: [WeakBridge.pinned_read s a] is [latest_ts (wm_log s) a ≤
    max (w_vrNew (wm_ws s)) (coh (wm_ws s) a)].  Under the log SHAPE
    [log ++ [wwrite_msg … la 8 z] ++ rest] with [rest] writing no byte of
    the window, the unmap write IS [latest_ts] of every window byte — it
    is the last index that writes them — so the floor premise
    [S (length log) ≤ w_vrNew] is literally [pinned_read].  §1.

    A pinned byte has exactly ONE admissible timestamp
    ([WeakBridge.wread_pinned_ts]), so the leaf read is not racy: it
    returns the flat value, and the ORDINARY certification path
    ([WeakCert.wstep_eff_confined_pin], whose side condition is
    [WeakCert.trace_pin]) applies unchanged.  §3 states and proves that
    side condition for the fault walk's trace — this is the "no racy
    machinery" claim, made checkable.

    And the walk of the zeroed slot FAULTS: every value the slot can hold
    is an A/D variant of zero ([WkClipAdvance.wclip_unmap_faults]), and
    those are invalid PTEs ([WkClipAdvance.pte_set_ad_zero_invalid]), so
    the walker takes the [PTW_Invalid_PTE] arm.  §2 assembles that at the
    SC interpreter, at the [translateAddr] altitude, over an abstract
    [sg : mstate] with [PtTree.pt_slot_mem] premises — mirroring
    [WeakKpt.wptree_translateAddr_eff_cases]'s shape, but on the Err path.

    THE POINT, for the xv6 story: this is WHY [uvmunmap] needs no [sfence]
    at the mutation site.  The TLB is flushed at the [satp] switch (a
    register write, [WeakUpdEff]/TLB-register territory, not memory), and
    the handoff synchronisation (the lock release / the scheduler's
    context switch) is what raises the resuming hart's floor over the
    store.  Flush + floor is the whole story; nothing about the store
    itself has to be ordered by a barrier.

    WHAT IS *NOT* HERE, deliberately: the Iris MP handoff — the ghost
    reasoning that turns "the unmapping hart released, the resuming hart
    acquired" into the floor premise [S (length log) ≤ w_vrNew (wm_ws σ)].
    That is the remaining piece; this file supplies its consumer.

    Nothing here is admitted and nothing new is axiomatised; §2 inherits
    the sail platform axioms the walk heads carry ([plat_term_write] and
    the reservation quartet), exactly as [WeakWalkEff] does. *)

(* the import block is [WkClipAdvance]'s, extended with the walk-eff and
   certification vocabulary §§2–3 name *)
From Stdlib.ssr Require Import ssreflect.
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakCert WeakEff WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree KptPt.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt.
Require Import WkClipAdvance.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. PINNEDNESS FROM DELIVERY

    The side condition on [rest] is spelled exactly as
    [WkClipAdvance.wclip_unmap_collapse_ext]'s: "no message at index
    [length log + 1] or beyond writes any byte of the window".  (Indices,
    not timestamps: index [i] carries timestamp [S i], and the unmap write
    itself sits at index [length log].)

    The one new fact is §1a: under that shape the unmap write IS the
    latest writer of every window byte, i.e. [latest_ts] of the byte is
    the write's timestamp [S (length log)].  It is proved from the LOG
    SHAPE — there is no ghost element to appeal to here — via
    [WeakMem.latest_ts_eq], whose two obligations are
      (i) the timestamp does hold a value for the byte: that is exactly
          [WeakKpt.wwin_install]'s content at the fresh cut, i.e.
          [WkClipAdvance.wreinstall_install] transported along the prefix
          by [WeakKpt.wwin_install_prefix]; and
     (ii) nothing above it writes the byte: that is the [rest] side
          condition, unpacked through [WeakMem.writes_in]. *)

(** *** 1a. The unmap write is the latest writer of each window byte. *)
Lemma wunmap_latest_ts (σ : wmstate) (la : Arch.pa) (log rest : list wmsg)
    (tid : option nat) (kcls : wm_class) (z : bv (8 * 8)%N) (j : nat) :
  wm_log σ = ((log ++ [wwrite_msg tid kcls la 8 z]) ++ rest)%list ->
  (forall (i : nat) (m : wmsg),
     wm_log σ !! i = Some m -> (length log + 1 <= i)%nat ->
     forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None) ->
  (j < 8)%nat ->
  latest_ts (wm_log σ) (acc_addr la j) = S (length log).
Proof.
  intros Hlog Hno Hj.
  apply (latest_ts_eq (wimg σ) (wm_log σ) (acc_addr la j) (S (length log))).
  split.
  - (* (i) the write's timestamp holds a value for byte [j] *)
    apply (wwin_install_log_byte (wimg σ) (wm_log σ) (S (length log)) la j Hj).
    apply (wwin_install_prefix (log ++ [wwrite_msg tid kcls la 8 z]) (wm_log σ)
             (S (length log)) la (wreinstall_install tid kcls la log z)).
    rewrite Hlog. by exists rest.
  - (* (ii) nothing strictly above it writes byte [j] *)
    intros (t & Hlo & _ & m & Hm & Hs).
    destruct t as [|i]; [lia|].
    replace (S i - 1)%nat with i in Hm by lia.
    rewrite (Hno i m Hm ltac:(lia) j Hj) in Hs. by destruct Hs.
Qed.

(** *** 1b. THE PINNEDNESS ITSELF.

    [pinned_read] wants [latest_ts ≤ max (w_vrNew) (coh)]; §1a computes the
    left-hand side and the DELIVERY premise [S (length log) ≤ w_vrNew]
    covers it through the [max]'s left branch.  Note what is NOT needed:
    no [wlog_wf], no [acc_wf], no coherence fact, nothing about the
    pre-existing [log] — delivery plus "nobody wrote since" is the whole
    hypothesis. *)
Lemma wunmap_pinned (σ : wmstate) (la : Arch.pa) (log rest : list wmsg)
    (tid : option nat) (kcls : wm_class) (z : bv (8 * 8)%N) :
  wm_log σ = ((log ++ [wwrite_msg tid kcls la 8 z]) ++ rest)%list ->
  (forall (i : nat) (m : wmsg),
     wm_log σ !! i = Some m -> (length log + 1 <= i)%nat ->
     forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None) ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr la j).
Proof.
  intros Hlog Hno Hcov j Hj.
  rewrite /pinned_read (wunmap_latest_ts σ la log rest tid kcls z j Hlog Hno Hj).
  lia.
Qed.

(** The [rest = []] instance, i.e. the read happening immediately after
    delivery, in the exact shape [WkClipAdvance.wclip_unmap_collapse]
    takes its log premise. *)
Lemma wunmap_pinned_last (σ : wmstate) (la : Arch.pa) (log : list wmsg)
    (tid : option nat) (kcls : wm_class) (z : bv (8 * 8)%N) :
  wm_log σ = (log ++ [wwrite_msg tid kcls la 8 z])%list ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr la j).
Proof.
  intros Hlog Hcov.
  apply (wunmap_pinned σ la log [] tid kcls z);
    [by rewrite Hlog app_nil_r| |exact Hcov].
  intros i m Hi Hge j Hj. exfalso.
  apply lookup_lt_Some in Hi. rewrite Hlog length_app /= in Hi. lia.
Qed.

(** THE HEADLINE OF §1, in one statement: after delivery the slot is
    pinned AND every admissible read of it is an invalid PTE.  The second
    conjunct is [WkClipAdvance.wclip_unmap_faults] under the same
    hypotheses; put next to the first it says the walk's leaf read is both
    NON-RACY and FAULTING. *)
Lemma wunmap_pinned_and_faults (σ : wmstate) (rak : akinfo) (la : Arch.pa)
    (log : list wmsg) (tid : option nat) (kcls : wm_class)
    (z : bv (8 * 8)%N) :
  (z : mword 64) = mword_of_int 0 ->
  wm_log σ = (log ++ [wwrite_msg tid kcls la 8 z])%list ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr la j)) /\
  (forall w : bv (8 * 8)%N, wadm σ rak la 8 w -> wpte_invalid (w : mword 64)).
Proof.
  intros Hz Hlog Hcov. split.
  - exact (wunmap_pinned_last σ la log tid kcls z Hlog Hcov).
  - intros w Hadm.
    exact (wclip_unmap_faults σ rak la log tid kcls z w Hz Hlog Hcov Hadm).
Qed.

(* ====================================================================== *)
(** ** 2. THE FAULT AT THE SC INTERPRETER

    The abstract-[sg] form, mirroring [WeakKpt.wptree_translateAddr_eff_cases]:
    the three slots are given by [PtTree.pt_slot_mem] premises, the two
    pointer slots hold valid non-leaf words, and the LEAF slot holds
    [pte_set_ad (mword_of_int 0) a d] — an arbitrary A/D variant of the
    zero word, which is exactly the set §1 (via [WkClipAdvance]) says the
    slot can hold after the unmap.

    The register / PMP / PMA premises are the dispatch's, MINUS the two the
    fault path never reaches: [misa] (the Svnapot gate sits past the leaf
    check) and [menvcfg] (the PBMTE/ADUE tests likewise), and minus the
    write-side PMP/PMA pair (a fault walk performs no A/D write-back).
    That trimming is itself a finding: the fault arm is cheaper in premises
    than the success arm.

    ALTITUDE REACHED: [translateAddr].  The Err propagation through the
    front needed NO new infrastructure —
    [WeakWalkEff.exec_eff_translateAddr_pt_front_err] already exists as the
    Ok front's twin (§8 of that file), and takes the PTW error's mapping
    through [translationException] as a caller premise exactly as the SC
    side does ([UserPtTree]'s fault heads).  So this file only has to
    supply the [translate]-level Err, which is
    [WeakWalkEff.exec_eff_translate_pt_blocks_l0]. *)

Section WkUnmapWalk.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (** *** 2a. The [translate]-level fault, over an abstract [sg].

      Trace: the three plain PTE reads, in walk order.  State: UNCHANGED
      (a fault walk writes nothing — no TLB fill, no A/D write-back). *)
  Lemma wunmap_translate_faults_eff (root_ppn : mword 44) (vpn : mword 27)
        (p2 p1 : mword 64) (a0 d0 : mword 1) (mxr do_sum : bool)
        (sg : mstate) :
    wpte_valid p2 -> pte_ptr p2 ->
    wpte_valid p1 -> pte_ptr p1 ->
    pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2 ->
    pt_slot_mem sg (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) p1 ->
    pt_slot_mem sg (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
      (pte_set_ad (mword_of_int 0) a0 d0) ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg, []) ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    exec_eff (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc p mxr do_sum tt) sg
    = Some (Err (PTW_Invalid_PTE tt, tt), sg,
            [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]).
  Proof.
    intros Hv2 Hn2 Hv1 Hn1 Hsm2 Hsm1 Hsm0 Hlk Hhtif HA Hord HR Hcov Hpmar.
    destruct (Hpmar _ (pt_slot_ram_access _ _ _ Hsm2)) as (region2 & Hm2 & Hs2).
    destruct (Hpmar _ (pt_slot_ram_access _ _ _ Hsm1)) as (region1 & Hm1 & Hs1).
    destruct (Hpmar _ (pt_slot_ram_access _ _ _ Hsm0)) as (region0 & Hm0 & Hs0).
    pose proof (wpt_read_pte_slot sg _ p2 region2 Hsm2 HA Hord HR Hcov Hm2 Hs2 Hhtif)
      as Hrd2.
    pose proof (wpt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif)
      as Hrd1.
    pose proof (wpt_read_pte_slot sg _ _ region0 Hsm0 HA Hord HR Hcov Hm0 Hs0 Hhtif)
      as Hrd0.
    exact (exec_eff_translate_pt_blocks_l0 acc p mxr do_sum vpn root_ppn p2 p1
             (pte_set_ad (mword_of_int 0) a0 d0) _ _ _ sg
             Hrd2 Hv2 Hn2 Hrd1 Hv1 Hn1 Hrd0 (pte_set_ad_zero_invalid a0 d0) Hlk).
  Qed.

  (** *** 2b. ... and the same at the [translateAddr] front.

      [vpn] is [RiscvPtsto.svpn_of va], the spelling the front computes, so
      the front's [Hvpn_def] premise is [eq_refl] (as it is in
      [WeakKpt.wptree_translateAddr_eff_cases]).  The exception word [e] is
      whatever [translationException acc (PTW_Invalid_PTE tt)] yields for
      this access class — a caller premise, as on the SC side. *)
  Lemma wunmap_walk_faults_eff (root_ppn : mword 44) (va satp0 : mword 64)
        (p2 p1 : mword 64) (a0 d0 : mword 1) (e : ExceptionType)
        (sg : mstate) :
    let vpn := svpn_of va in
    wpte_valid p2 -> pte_ptr p2 ->
    wpte_valid p1 -> pte_ptr p1 ->
    pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2 ->
    pt_slot_mem sg (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) p1 ->
    pt_slot_mem sg (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
      (pte_set_ad (mword_of_int 0) a0 d0) ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg, []) ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = p ->
    exec_eff (translationMode p) sg = Some (Sv39, sg, []) ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) p) sg
      = Some (p, sg, []) ->
    exec_eff (is_shadow_stack_access acc) sg = Some (false, sg, []) ->
    register_lookup satp sg.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0))
      = false ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    exec_eff (translationException acc (PTW_Invalid_PTE tt)) sg = Some (e, sg, []) ->
    exec_eff (translateAddr (Virtaddr va) acc) sg
    = Some (Err (e, tt), sg,
            [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
             WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]).
  Proof.
    intros vpn Hv2 Hn2 Hv1 Hn1 Hsm2 Hsm1 Hsm0 Hlk Hhtif Hcp Htm Heff Hss
           Hsatp Hppn Hasid Hcanon HA Hord HR Hcov Hpmar Hte.
    apply (exec_eff_translateAddr_pt_front_err acc p vpn root_ppn
             (PTW_Invalid_PTE tt) e satp0 va _ sg
             Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon eq_refl); [|exact Hte].
    intros mxr do_sum.
    exact (wunmap_translate_faults_eff root_ppn vpn p2 p1 a0 d0 mxr do_sum sg
             Hv2 Hn2 Hv1 Hn1 Hsm2 Hsm1 Hsm0 Hlk Hhtif HA Hord HR Hcov Hpmar).
  Qed.

End WkUnmapWalk.

(* ====================================================================== *)
(** ** 3. THE PINNED-READS COROLLARY — "no racy machinery needed"

    §2's trace is three PLAIN reads ([wak_plain = AkInfo false false false],
    so [WeakBridge.ak_pins wak_plain = false]: the walker's PTE reads are
    NOT self-pinning in this model, which is precisely why the racy layer
    exists at all).  [WeakCert.trace_pin] asks for [pinned_read] on every
    byte of every such read — and §1 supplies it for the leaf window, while
    the two pointer slots come in as premises, since in the real setting
    they are PERSISTENT, kvminit-timestamped elements whose pinnedness is
    already in hand (nothing ever rewrites a user table's upper levels
    while a walk is in flight).

    [trace_pin] is exactly the side condition of
    [WeakCert.wstep_eff_confined_pin], the ORDINARY (non-racy)
    certification theorem.  So the statements below ARE the claim "the
    resuming hart's faulting walk needs no racy machinery", in the
    vocabulary that consumes it. *)

(** [wak_plain] does not pin itself — recorded because it is the reason §3
    has any content. *)
Lemma wak_plain_not_pinning : ak_pins wak_plain = false.
Proof. reflexivity. Qed.

(** *** 3a. The trace-shaped fact: three plain 8-byte reads at pinned
    windows satisfy [trace_pin]. *)
Lemma wtrace_pin_three_reads (σ : wmstate) (b2 b1 b0 : Arch.pa) :
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr b2 j)) ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr b1 j)) ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr b0 j)) ->
  trace_pin σ [WEread wak_plain b2 8; WEread wak_plain b1 8; WEread wak_plain b0 8].
Proof.
  intros Hb2 Hb1 Hb0 ak pa n Hin _ j Hj.
  (* one generic arm: the trace element's fields are read off by inversion,
     and [N.to_nat 8] is [8%nat] by conversion *)
  assert (Hgen : forall b : Arch.pa,
            (forall k : nat, (k < 8)%nat -> pinned_read σ (acc_addr b k)) ->
            WEread ak pa n = WEread wak_plain b 8 ->
            pinned_read σ (acc_addr pa j)).
  { intros b Hb Heq. inversion Heq. subst. apply Hb. exact Hj. }
  rewrite !elem_of_cons in Hin.
  destruct Hin as [Heq|[Heq|[Heq|Hnil]]].
  - exact (Hgen b2 Hb2 Heq).
  - exact (Hgen b1 Hb1 Heq).
  - exact (Hgen b0 Hb0 Heq).
  - by apply elem_of_nil in Hnil.
Qed.

(** *** 3b. THE COROLLARY, tying §1 to §2's trace.

    Read it as: at a weak state whose log ends with the unmap's zero store
    to [la] (nothing having written the window since) and whose read floor
    covers that store, with the two pointer slots pinned, the fault walk of
    §2 — whose trace is the three plain reads at [b2], [b1] and the leaf
    window [la] — satisfies the ORDINARY certification's pinnedness side
    condition.  No [WeakRacy] obligation is generated anywhere. *)
Lemma wunmap_no_racy_needed (σ : wmstate) (b2 b1 la : Arch.pa)
    (log rest : list wmsg) (tid : option nat) (kcls : wm_class)
    (z : bv (8 * 8)%N) :
  wm_log σ = ((log ++ [wwrite_msg tid kcls la 8 z]) ++ rest)%list ->
  (forall (i : nat) (m : wmsg),
     wm_log σ !! i = Some m -> (length log + 1 <= i)%nat ->
     forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None) ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr b2 j)) ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr b1 j)) ->
  trace_pin σ [WEread wak_plain b2 8; WEread wak_plain b1 8; WEread wak_plain la 8].
Proof.
  intros Hlog Hno Hcov Hp2 Hp1.
  apply wtrace_pin_three_reads; [exact Hp2|exact Hp1|].
  exact (wunmap_pinned σ la log rest tid kcls z Hlog Hno Hcov).
Qed.

(** The same, spelled at §2's slot addresses, so that the two halves
    visibly compose: [b2]/[b1] are the walk's level-2 / level-1 slots and
    the leaf slot IS the unmapped window. *)
Lemma wunmap_walk_trace_pin (σ : wmstate) (root_ppn : mword 44)
    (vpn : mword 27) (p2 p1 : mword 64)
    (log rest : list wmsg) (tid : option nat) (kcls : wm_class)
    (z : bv (8 * 8)%N) :
  wm_log σ = ((log ++ [wwrite_msg tid kcls
                        (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
                        8 z]) ++ rest)%list ->
  (forall (i : nat) (m : wmsg),
     wm_log σ !! i = Some m -> (length log + 1 <= i)%nat ->
     forall j : nat, (j < 8)%nat ->
       msg_byte m (acc_addr (u_pte_addr (u_next_base p1)
                               (subrange_vec_dec vpn 8 0)) j) = None) ->
  (S (length log) <= w_vrNew (wm_ws σ))%nat ->
  (forall j : nat, (j < 8)%nat ->
     pinned_read σ (acc_addr (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) j)) ->
  (forall j : nat, (j < 8)%nat ->
     pinned_read σ (acc_addr (u_pte_addr (u_next_base p2)
                                (subrange_vec_dec vpn 17 9)) j)) ->
  trace_pin σ
    [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
     WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
     WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8].
Proof.
  intros Hlog Hno Hcov Hp2 Hp1.
  exact (wunmap_no_racy_needed σ _ _ _ log rest tid kcls z Hlog Hno Hcov Hp2 Hp1).
Qed.

Print Assumptions wunmap_pinned.
Print Assumptions wunmap_pinned_and_faults.
Print Assumptions wunmap_walk_faults_eff.
Print Assumptions wunmap_no_racy_needed.
Print Assumptions wunmap_walk_trace_pin.
