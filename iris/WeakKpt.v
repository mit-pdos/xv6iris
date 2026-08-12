(** * WeakKpt.v — batch-6 P4: the weak kernel-page-table invariant and the
    weak absorption theorem

    THE MIRROR of [KptShare.v] over the weak memory model: the shared
    kernel-page-table invariant [wkpt_inv] (the [kpt_inv] mirror with
    [ptree_own] split by role over the [γlat] latest-write elements), the
    per-hart residue [wtlb_res_pt] (the [tlb_res_pt] mirror), and the weak
    ABSORPTION THEOREM [wtlb_res_pt_translateAddr_at] — the
    [tlb_res_pt_translateAddr_at] mirror with [gen_heap_interp] swapped for
    [WeakGhost.wlat_interp] and [RiscvExec.exec] for the instrumented
    [WeakCert.exec_eff] at the coherent flat projection
    [WeakBridge.wflat_st σ].

    THE INVARIANT, per mapped vpn of the kmap auth's map M (design:
    claude-notes/projects/weak-memory.md, BATCH 6 block):

      - the two POINTER slot words as kvminit-timestamped, DISCARDED
        (persistent) [wlat8] element bundles ([wptr8]): pointer words are
        single-message — nothing ever stores to a PT page but the leaf
        write-back — so their latest-write elements can be persisted, and
        the stored bound [ts ≤ T_kpt] is what lets a consumer holding the
        per-hart receipt (pure shadow: [T_kpt ≤ w_vrNew]) derive
        [pinned_read] for the walk's two pointer reads;
      - the LEAF window as an EXCLUSIVE [∃ ts a d, wlat8 la 1 ts
        (pte_set_ad w0 a d)] ([wleaf_res]) — a write-back retargets it at
        the appended message ([wlat8_store_prim]), the lock-release shape;
      - the VALUE-CLOSURE and FRESH-DERIVED discipline conjuncts, CLIPPED
        AT THE WINDOW'S INSTALL TIMESTAMP [T0] and stored against a log
        SNAPSHOT ([wlog_lb log0]): see the DESIGN CORRECTION below;
      - [kmap_auth M] + [kpt_lb t] + the tree spec
        [kpt_tree_spec_gen root M t], verbatim from the SC invariant.

    DESIGN CORRECTION (vs the batch-6 block's un-clipped [wlog_variants]):
    the closure and discipline conjuncts CANNOT be stated over the whole
    log.  The era log of a real boot contains pre-kvminit messages into the
    leaf windows (freerange/kalloc memset the PT pages with 0x01/0x05
    junk before kvmmake writes the canonical PTEs), so "every log message
    at the window writes a variant" is FALSE and the invariant would be
    unmintable.  The honest form clips at the INSTALL write [T0] (kvmmake's
    store of the leaf), and the collapse still goes through because the
    receipt's cover bars every admissible read below [T0]
    ([wbyte_ok_ge]: a read floor covering the install write forces
    [t ≥ T0] — the same [readable]-coherence argument that bars the
    era-initial image, one timestamp higher).  A whole-log fact cannot sit
    in an invariant anyway; the stored shape is
    [wlog_lb log0 ∗ ⌜closure-of log0⌝] plus the leaf element, and the
    extension to the CURRENT log is derived at the absorption from the
    element's [latest_ts] (no message above the element's timestamp writes
    the window — [wwin_no_write_above]).  This is also why the theorem
    consumes [wlog_auth] alongside [wlat_interp]: the log-prefix tie
    ([wlog_valid]) and the fresh snapshot at the write-back re-close
    ([wlog_snapshot]) both need the authority.

    THE ABSORPTION THEOREM: keyed on the caller's [kmap_at] claim, opens
    [wkptN] mask-carrying (the [sr_absorb] unshelve call form), and
    produces
      - the pure [exec_eff (translateAddr va acc) (wflat_st σ) = Ok pa]
        fact with the EXACT per-outcome trace (O1 hit: []; O2 fill: the
        three plain walk reads; O2' refresh: the lone CAS read; O3
        write-back: walk reads + the adjacent CAS pair, or the CAS pair
        alone on the hit path) — [pa] variant-independent;
      - the racy-leaf COLLAPSE facts for the 6a bridge: every admissible
        read of the leaf window ([WeakRacy.wadm]) is a variant of the
        canonical leaf AND [pte_ad_le]-below the latest word (so by
        [WeakVariant.update_PTE_Bits_fires_latest] the write-back EVENT is
        decided by the latest word alone);
      - [pinned_read] for every byte of the two pointer slots (the
        [trace_pin] discharge for the walk's plain pointer reads);
      - the ghost re-establishment: [reg_interp] at the successor's
        registers, [wlog_auth]/[wlat_interp] unchanged on the quiet arms
        and AT THE APPENDED LOG on the write-back arm (the message identity
        [wwrite_msg tid la 8 lw'] matches [WeakUpdEff.wcert_ptw_upd]'s
        [wQ_store_w 8]), and the residue + invariant re-closed
        ([kpt_lb] survives by [ptree_canon_set_leaf] exactly as SC).

    Sections:
      §1  the CLIPPED closure layer: [wlog_variants_from] /
          [wfresh_from] and their extension / write-back / collapse kit
          (the [T0]-clipped mirrors of [WeakVariant] §§2–4)
      §2  the kperm eff twins: [wkperm_variant_valid] /
          [wkperm_variant_check] (the [KptTree] §2c dischargers at
          [exec_eff] — the batch-6b items P4 needs today)
      §3  the invariant: [wptr8] / [wleaf_res] / [wvpn_res] / [wkpt_body] /
          [wkpt_inv] and the residue [wtlb_res_pt]
      §4  the pure dispatch [wptree_translateAddr_eff_cases] — the
          [KptTree.ptree_translateAddr_cases] mirror at [exec_eff], with
          the per-outcome traces
      §5  THE ABSORPTION THEOREM [wtlb_res_pt_translateAddr_at]

    Everything here that does not mention [riscv_step] is expected closed
    under the global context up to the sail platform axioms the walk heads
    carry ([plat_term_write] + the reservation quartet). *)
From Stdlib Require Import ZArith Bool Lia Wf_nat.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakFetchEff WeakLeafEffCommon WeakLeafEff8.
Require Import WeakStore WeakRacy WeakWord8.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree UserPtTree PtTreeAdue.
Require Import KptPt KMap SmodeCore KptTree KptGhost KptShare.
Require Import WeakWalkEff WeakUpdEff.
Require Import WeakVariant.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. The clipped closure layer

    [WeakVariant] §§2–4 state the closure ([wlog_variants]) and the CAS
    discipline ([wbyte_fresh_derived]) over the WHOLE log; the invariant
    stores the [T0]-clipped forms below (see the header's design
    correction).  The collapse lemmas replay [WeakVariant]'s with the
    stronger exclusion [wbyte_ok_ge] in place of [wbyte_ok_not_init]. *)

(** The closure, clipped: every message at timestamp [T0] or later that
    touches the window writes variant bytes.  (Timestamp of index [i] is
    [S i]; the install write at timestamp [T0] is INCLUDED — it writes a
    variant, kvmmake's A/D-clear leaf.) *)
Definition wlog_variants_from (T0 : nat) (log : list wmsg) (a8 : Z)
    (w0 : mword 64) : Prop :=
  forall (i : nat) (m : wmsg),
    log !! i = Some m -> (T0 <= S i)%nat -> wmsg_variant a8 w0 m.

(** The discipline, clipped: every message STRICTLY after the install that
    writes byte [a] derived its value from the latest value at its own
    append time with A/D bits only ORed.  (The install itself is exempt —
    it overwrites pre-install junk arbitrarily.) *)
Definition wfresh_from (T0 : nat) (img : image) (log : list wmsg) (a : Z)
    : Prop :=
  forall (i : nat) (m : wmsg) (b : bv 8),
    log !! i = Some m -> (T0 < S i)%nat -> msg_byte m a = Some b ->
    exists bf : bv 8,
      log_byte img (take i log) (latest_ts (take i log) a) a = Some bf /\
      ad_bits_le bf b.

(** The install fact: the message at timestamp [T0] writes every byte of
    the window.  ([1 ≤ T0] makes the timestamp a message, not the image.) *)
Definition wwin_install (log : list wmsg) (T0 : nat) (ra : Arch.pa) : Prop :=
  (1 <= T0)%nat /\
  exists m : wmsg,
    log !! (T0 - 1)%nat = Some m /\
    forall j : nat, (j < 8)%nat -> is_Some (msg_byte m (acc_addr ra j)).

(** *** 1a. Plumbing *)

(** [log_byte] at a message timestamp does not consult the image. *)
Lemma log_byte_img_irrel (img img' : image) (log : list wmsg) (t : nat)
    (a : Z) :
  (1 <= t)%nat -> log_byte img log t a = log_byte img' log t a.
Proof. destruct t as [|i]; [lia|reflexivity]. Qed.

(** The install writes byte [j] at timestamp [T0]. *)
Lemma wwin_install_log_byte (img : image) (log : list wmsg) (T0 : nat)
    (ra : Arch.pa) (j : nat) :
  (j < 8)%nat -> wwin_install log T0 ra ->
  is_Some (log_byte img log T0 (acc_addr ra j)).
Proof.
  intros Hj (HT0 & m & Hm & Hw).
  destruct T0 as [|i]; [lia|].
  rewrite log_byte_S.
  replace i with (S i - 1)%nat by lia. rewrite Hm /=.
  exact (Hw j Hj).
Qed.

(** The install survives a log extension. *)
Lemma wwin_install_prefix (log0 log : list wmsg) (T0 : nat) (ra : Arch.pa) :
  wwin_install log0 T0 ra -> log0 `prefix_of` log -> wwin_install log T0 ra.
Proof.
  intros (HT0 & m & Hm & Hw) [rest ->].
  split; [exact HT0|]. exists m. split; [|exact Hw].
  rewrite lookup_app_l; [exact Hm|].
  apply lookup_lt_Some in Hm. exact Hm.
Qed.

(** No message at or above the element's timestamp writes the window: the
    element IS the latest write per byte. *)
Lemma wwin_no_write_above (s : wmstate) (ra : Arch.pa) (ts : nat) :
  (forall j : nat, (j < 8)%nat -> latest_ts (wm_log s) (acc_addr ra j) = ts) ->
  forall (i : nat) (m : wmsg),
    wm_log s !! i = Some m -> (ts <= i)%nat ->
    forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr ra j) = None.
Proof.
  intros Hlat i m Hm Hge j Hj.
  destruct (msg_byte m (acc_addr ra j)) as [b|] eqn:Hb; [exfalso|reflexivity].
  assert (Hlb : log_byte (wimg s) (wm_log s) (S i) (acc_addr ra j) = Some b).
  { rewrite log_byte_S Hm /=. exact Hb. }
  pose proof (writes_le_latest_ts (wimg s) (wm_log s) (acc_addr ra j) (S i)
                ltac:(by exists b; exact Hlb)) as Hle.
  rewrite (Hlat j Hj) in Hle. lia.
Qed.

(** *** 1b. Extension to the current log *)

Lemma wlog_variants_from_ext (T0 : nat) (log0 log : list wmsg) (a8 : Z)
    (w0 : mword 64) :
  wlog_variants_from T0 log0 a8 w0 ->
  log0 `prefix_of` log ->
  (forall (i : nat) (m : wmsg),
     log !! i = Some m -> (length log0 <= i)%nat ->
     forall j : nat, (j < 8)%nat -> msg_byte m (a8 + Z.of_nat j) = None) ->
  wlog_variants_from T0 log a8 w0.
Proof.
  intros Hv Hpref Hno i m Hm HT0.
  destruct (decide (i < length log0)%nat) as [Hlt|Hge].
  - destruct Hpref as [rest ->].
    rewrite (lookup_app_l _ _ _ Hlt) in Hm. exact (Hv i m Hm HT0).
  - apply wmsg_variant_untouched. intros j Hj.
    exact (Hno i m Hm ltac:(lia) j Hj).
Qed.

Lemma wfresh_from_ext (T0 : nat) (img : image) (log0 log : list wmsg)
    (a : Z) :
  wfresh_from T0 img log0 a ->
  log0 `prefix_of` log ->
  (forall (i : nat) (m : wmsg),
     log !! i = Some m -> (length log0 <= i)%nat -> msg_byte m a = None) ->
  wfresh_from T0 img log a.
Proof.
  intros Hf Hpref Hno i m b Hm HT0 Hb.
  destruct (decide (i < length log0)%nat) as [Hlt|Hge];
    [|rewrite (Hno i m Hm ltac:(lia)) in Hb; discriminate].
  destruct Hpref as [rest Hlog]. subst log.
  rewrite (lookup_app_l _ _ _ Hlt) in Hm.
  destruct (Hf i m b Hm HT0 Hb) as (bf & Hbf & Hle).
  exists bf. split; [|exact Hle].
  rewrite (take_app_le log0 rest i ltac:(lia)). exact Hbf.
Qed.

(** *** 1c. The exclusion: a covered install bars everything below it *)

(** If the hart's read floor covers a write at timestamp [tc], no
    admissible read — at ANY access kind — returns a timestamp below [tc].
    ([WeakVariant.wbyte_ok_not_init] is the [tc]-writes-something instance
    at [t = 0]; this is the same coherence argument one timestamp up.) *)
Lemma wbyte_ok_ge (s : wmstate) (ak : akinfo) (a : Z) (t tc : nat)
    (b : bv 8) :
  (1 <= tc)%nat ->
  (tc <= w_vrNew (wm_ws s))%nat ->
  is_Some (log_byte (wimg s) (wm_log s) tc a) ->
  wbyte_ok s ak a t b ->
  (tc <= t)%nat.
Proof.
  intros Htc1 Htcv Htcw [Hb Hadm].
  destruct (decide (tc <= t)%nat) as [?|Hlt]; [assumption|exfalso].
  assert (Hwin : forall hi : nat, (tc <= hi)%nat -> writes_in (wm_log s) a t hi).
  { intros hi Hhi. apply (writes_in_log_byte (wimg s)).
    exists tc. split_and!; [lia|lia|exact Htcw]. }
  assert (Hlen : (tc <= length (wm_log s))%nat)
    by (apply (log_byte_bounded (wimg s) _ tc a); exact Htcw).
  destruct (ak_coh ak).
  - exact (Hadm (Hwin _ Hlen)).
  - destruct Hadm as [[_ Hrd] _].
    apply Hrd. apply Hwin.
    etrans; [exact Htcv|]. etrans; [apply load_vpre_vrNew|].
    apply Nat.le_max_l.
Qed.

(** *** 1d. The clipped collapse at the window *)

Lemma wbyte_ok_variant_from (s : wmstate) (ak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (T0 j t : nat) (b : bv 8) :
  (j < 8)%nat ->
  wlog_variants_from T0 (wm_log s) (pa_z ra) w0 ->
  wwin_install (wm_log s) T0 ra ->
  (T0 <= w_vrNew (wm_ws s))%nat ->
  wbyte_ok s ak (acc_addr ra j) t b ->
  exists a d : mword 1, b = nth_byte (pte_set_ad w0 a d) j.
Proof.
  intros Hj Hvar Hinst Hcov Hok.
  pose proof (proj1 Hinst) as HT01.
  pose proof (wbyte_ok_ge s ak (acc_addr ra j) t T0 b HT01 Hcov
                (wwin_install_log_byte (wimg s) (wm_log s) T0 ra j Hj Hinst)
                Hok) as Hge.
  destruct Hok as [Hb _].
  destruct t as [|i]; [lia|].
  rewrite log_byte_S in Hb.
  destruct (wm_log s !! i) as [m|] eqn:Hm; simpl in Hb; [|discriminate].
  destruct (Hvar i m Hm ltac:(lia)) as (a & d & Hv).
  exists a, d.
  refine (Hv j _ b _); [lia|].
  rewrite /acc_addr in Hb |- *. exact Hb.
Qed.

(** THE [wadm] COLLAPSE, clipped: every admissible read of the window is a
    variant of the canonical leaf. *)
Lemma wadm_variant_from (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (T0 : nat) (w : bv (8 * 8)%N) :
  wlog_variants_from T0 (wm_log s) (pa_z ra) w0 ->
  wwin_install (wm_log s) T0 ra ->
  (T0 <= w_vrNew (wm_ws s))%nat ->
  wadm s rak ra 8 w ->
  exists a d : mword 1, (w : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hvar Hinst Hcov Hadm.
  apply pte_variant_mix. intros j Hj.
  destruct (Hadm j ltac:(vm_compute; lia)) as (t & Hok).
  exact (wbyte_ok_variant_from s rak ra w0 T0 j t _ Hj Hvar Hinst Hcov Hok).
Qed.

(** The latest window word is a variant (its byte sources are messages at
    or above the install: the install writes each byte, so each byte's
    [latest_ts] is at least [T0]). *)
Lemma wwin_latest_variant_from (s : wmstate) (ra : Arch.pa) (w0 : mword 64)
    (T0 : nat) (wl : bv (8 * 8)%N) :
  wlog_variants_from T0 (wm_log s) (pa_z ra) w0 ->
  wwin_install (wm_log s) T0 ra ->
  wwin_latest s ra wl ->
  exists a d : mword 1, (wl : mword 64) = pte_set_ad w0 a d.
Proof.
  intros Hvar Hinst Hlat.
  apply pte_variant_mix. intros j Hj.
  destruct (Hlat j Hj) as (t & Hlv).
  pose proof (latest_val_ts _ _ _ _ _ Hlv) as Hts.
  pose proof (writes_le_latest_ts (wimg s) (wm_log s) (acc_addr ra j) T0
                (wwin_install_log_byte (wimg s) (wm_log s) T0 ra j Hj Hinst))
    as HgeT0.
  rewrite Hts in HgeT0.
  destruct Hlv as [Hb _].
  destruct t as [|i]; [pose proof (proj1 Hinst); lia|].
  rewrite log_byte_S in Hb.
  destruct (wm_log s !! i) as [m|] eqn:Hm; simpl in Hb; [|discriminate].
  destruct (Hvar i m Hm ltac:(lia)) as (a & d & Hv).
  exists a, d.
  refine (Hv j _ _ _); [lia|].
  rewrite /acc_addr in Hb |- *. exact Hb.
Qed.

(** *** 1e. The clipped discipline: monotone above the install *)

(* [log_byte] on a prefix agrees with the full log below the cut.  This was
   a verbatim copy of [WeakVariant]'s lemma, which was [Local]; it is
   exported now, so the copy is gone and the three uses below name it
   directly. *)

(** BIT-MONOTONICITY above the install: with the discipline clipped at
    [T0] and the install writing [a] at [T0], any two writers at or above
    [T0] are [ad_bits_le]-ordered by timestamp.
    ([WeakVariant.wbyte_fresh_derived_mono] with the [T0] bound carried
    through the descent — the recursion only ever visits prefix-latest
    timestamps, and every such prefix contains the install.) *)
Lemma wfresh_from_mono (T0 : nat) (img : image) (log : list wmsg) (a : Z) :
  (1 <= T0)%nat ->
  is_Some (log_byte img log T0 a) ->
  wfresh_from T0 img log a ->
  forall (t' t : nat) (b b' : bv 8),
    (T0 <= t)%nat -> (t <= t')%nat ->
    log_byte img log t a = Some b ->
    log_byte img log t' a = Some b' ->
    ad_bits_le b b'.
Proof.
  intros HT01 Hinst Hf t'.
  induction t' as [t' IH] using lt_wf_ind.
  intros t b b' HT0t Hle Hb Hb'.
  destruct (decide (t = t')) as [->|Hne].
  { rewrite Hb in Hb'. injection Hb' as <-. apply ad_bits_le_refl. }
  assert (Hlt : (t < t')%nat) by lia.
  destruct t' as [|i']; [lia|].
  rewrite log_byte_S in Hb'.
  destruct (log !! i') as [m'|] eqn:Hm'; simpl in Hb'; [|discriminate].
  destruct (Hf i' m' b' Hm' ltac:(lia) Hb') as (bf & Hbf & Hfb').
  assert (Hi' : (i' < length log)%nat) by (apply lookup_lt_Some in Hm'; lia).
  set (L := latest_ts (take i' log) a) in *.
  assert (HLle : (L <= i')%nat)
    by (pose proof (latest_ts_le (take i' log) a) as H;
        rewrite length_take in H; lia).
  (* the install is inside the prefix, so the prefix latest is ≥ T0 *)
  assert (HinstP : is_Some (log_byte img (take i' log) T0 a)).
  { rewrite (log_byte_take img log i' T0 a ltac:(lia) ltac:(lia)).
    exact Hinst. }
  assert (HT0L : (T0 <= L)%nat)
    by exact (writes_le_latest_ts img (take i' log) a T0 HinstP).
  (* the prefix latest, read at the full log *)
  assert (Hbf' : log_byte img log L a = Some bf)
    by (rewrite -(log_byte_take img log i' L a HLle ltac:(lia));
        exact Hbf).
  (* [t] is a writer inside the prefix, hence below its latest *)
  assert (Hbp : log_byte img (take i' log) t a = Some b)
    by (rewrite (log_byte_take img log i' t a ltac:(lia) ltac:(lia));
        exact Hb).
  assert (HtL : (t <= L)%nat)
    by (apply (writes_le_latest_ts img (take i' log) a t); by exists b).
  apply (ad_bits_le_trans b bf b'); [|exact Hfb'].
  exact (IH L ltac:(lia) t b bf HT0t HtL Hb Hbf').
Qed.

(** *** 1f. Preservation across the CAS write-back *)

(** The closure extends by an appended write whose value is a variant. *)
Lemma wlog_variants_from_snoc (T0 : nat) (log : list wmsg) (a8 : Z)
    (w0 : mword 64) (m : wmsg) :
  wlog_variants_from T0 log a8 w0 ->
  wmsg_variant a8 w0 m ->
  wlog_variants_from T0 (log ++ [m]) a8 w0.
Proof.
  intros Hv Hm i m0 Hi HT0.
  destruct (decide (i < length log)%nat) as [Hlt|Hge].
  - rewrite (lookup_app_l _ _ _ Hlt) in Hi. exact (Hv i m0 Hi HT0).
  - assert (Hieq : i = length log).
    { apply lookup_lt_Some in Hi. rewrite length_app /= in Hi. lia. }
    subst i.
    rewrite (lookup_app_r log [m] (length log) (Nat.le_refl _)) Nat.sub_diag /=
      in Hi.
    injection Hi as <-. exact Hm.
Qed.

(** ... and the discipline by a write derived from the current latest
    value with bits only ORed ([WeakVariant.wbyte_fresh_derived_writeback]
    clipped: the new index is above the install by construction). *)
Lemma wfresh_from_writeback (T0 : nat) (img : image) (log : list wmsg)
    (tid : option nat) k (pa : Arch.pa) (acc : MemoryAccessType mem_payload)
    (fresh w' : mword 64) (v : bv (8 * 8)%N) :
  log_byte img log (latest_ts log (pa_z pa)) (pa_z pa)
    = Some (nth_byte fresh 0) ->
  update_PTE_Bits (fresh : mword 64) acc = Some w' ->
  (v : mword 64) = w' ->
  wfresh_from T0 img log (pa_z pa) ->
  wfresh_from T0 img (log ++ [wwrite_msg tid k pa 8 v]) (pa_z pa).
Proof.
  intros Hlat Hup Hv Hf i m b Hi HT0 Hb.
  destruct (decide (i < length log)%nat) as [Hlt|Hge].
  - rewrite (lookup_app_l _ _ _ Hlt) in Hi.
    destruct (Hf i m b Hi HT0 Hb) as (bf & Hbf & Hle).
    exists bf. split; [|exact Hle].
    rewrite (take_app_le log [wwrite_msg tid k pa 8 v] i ltac:(lia)). exact Hbf.
  - assert (Hieq : i = length log).
    { apply lookup_lt_Some in Hi. rewrite length_app /= in Hi. lia. }
    subst i.
    rewrite (lookup_app_r log [wwrite_msg tid k pa 8 v] (length log)
               (Nat.le_refl _)) Nat.sub_diag /= in Hi.
    injection Hi as <-.
    assert (Hb0 : msg_byte (wwrite_msg tid k pa 8 v) (pa_z pa)
                  = Some (nth_byte v 0)).
    { rewrite -(acc_addr_0 pa).
      apply (wwrite_msg_byte tid k pa 8 v 0%nat). lia. }
    rewrite Hb0 in Hb. injection Hb as <-.
    exists (nth_byte fresh 0). split.
    + rewrite (take_app_le log [wwrite_msg tid k pa 8 v] (length log)
                 (Nat.le_refl _)).
      rewrite (take_ge log (length log) (Nat.le_refl _)). exact Hlat.
    + assert (Hle : ad_bits_le (nth_byte fresh 0) (nth_byte w' 0))
        by (apply pte_ad_le_byte0, (update_PTE_Bits_ad_ge fresh w' acc Hup)).
      assert (Hnb : nth_byte v 0 = nth_byte w' 0)
        by (exact (f_equal (fun x : mword 64 => nth_byte x 0%nat) Hv)).
      rewrite Hnb. exact Hle.
Qed.

(** *** 1g. The clipped capstone *)

(** Every admissible read of the window is a variant BELOW the latest
    word ([WeakVariant.wadm_pte_ad_le_latest], clipped). *)
Lemma wadm_pte_ad_le_latest_from (s : wmstate) (rak : akinfo) (ra : Arch.pa)
    (w0 : mword 64) (T0 : nat) (w wl : bv (8 * 8)%N) :
  wlog_variants_from T0 (wm_log s) (pa_z ra) w0 ->
  wfresh_from T0 (wimg s) (wm_log s) (pa_z ra) ->
  wwin_install (wm_log s) T0 ra ->
  (T0 <= w_vrNew (wm_ws s))%nat ->
  wwin_latest s ra wl ->
  wadm s rak ra 8 w ->
  pte_ad_le (w : mword 64) (wl : mword 64).
Proof.
  intros Hvar Hfd Hinst Hcov Hlat Hadm.
  pose proof (proj1 Hinst) as HT01.
  destruct (wadm_variant_from s rak ra w0 T0 w Hvar Hinst Hcov Hadm)
    as (aw & dw & Hw).
  destruct (wwin_latest_variant_from s ra w0 T0 wl Hvar Hinst Hlat)
    as (al & dl & Hwl).
  (* byte 0's order, through the discipline *)
  destruct (Hadm 0%nat ltac:(vm_compute; lia)) as (t0 & Hok0).
  pose proof (wbyte_ok_ge s rak (acc_addr ra 0) t0 T0 _ HT01 Hcov
                (wwin_install_log_byte (wimg s) (wm_log s) T0 ra 0 ltac:(lia)
                   Hinst) Hok0) as Ht0T0.
  destruct Hok0 as [Hb0 _].
  destruct (Hlat 0%nat ltac:(lia)) as (tl & Hlv).
  assert (Htl : latest_ts (wm_log s) (acc_addr ra 0) = tl)
    by exact (latest_val_ts _ _ _ _ _ Hlv).
  rewrite acc_addr_0 in Hb0 Htl.
  destruct Hlv as [Hbl _]. rewrite acc_addr_0 in Hbl.
  assert (Hinst0 : is_Some (log_byte (wimg s) (wm_log s) T0 (pa_z ra))).
  { rewrite -(acc_addr_0 ra).
    exact (wwin_install_log_byte (wimg s) (wm_log s) T0 ra 0 ltac:(lia)
             Hinst). }
  assert (Hble : ad_bits_le (nth_byte w 0) (nth_byte wl 0)).
  { refine (wfresh_from_mono T0 (wimg s) (wm_log s) (pa_z ra) HT01 Hinst0 Hfd
              tl t0 _ _ Ht0T0 _ Hb0 Hbl).
    rewrite -Htl. apply (writes_le_latest_ts (wimg s)).
    by exists (nth_byte w 0). }
  refine (pte_ad_le_of_byte0 w0 _ _ _ _ Hble).
  - by exists aw, dw.
  - by exists al, dl.
Qed.

(* ====================================================================== *)
(** ** 2. The kperm eff twins

    [KptTree] §2c's class-keyed dischargers at [exec_eff]: the walk heads
    take [WeakWalkEff.wpte_valid] / [wpte_check_ok] (empty-trace eff
    facts), which do NOT transport from the SC ∀-state predicates; for the
    kernel's class-keyed leaves they are re-proved here by the same
    concrete-flag [vm_compute] dispatch ([kperm_variant_flags] /
    [kperm_variant_ext] close the words, and the check programs are
    register- and memory-free on the success paths, so [exec_eff] reduces
    to the empty trace exactly as [exec] reduces to the unchanged state).
    These are the batch-6b "[kperm_variant_*] twins stated at [wpte_*]"
    that P4 needs today; 6b inherits them from here. *)

Lemma wkperm_inv_red (pc : kperm) (ad : bool * bool) : forall s,
  exec_eff (pte_is_invalid (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad)))
              (Mk_PTE_Ext (mword_of_int 0))) s
  = Some (false, s, []).
Proof.
  intro s. destruct pc; destruct ad as [a d]; destruct a, d;
    vm_compute; reflexivity.
Qed.

Lemma wkperm_check_fetch (ad : bool * bool) : forall (mxr do_sum : bool) s,
  exec_eff (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
              (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rx ad)))
              (Mk_PTE_Ext (mword_of_int 0)) tt) s
  = Some (PTE_Check_Success tt, s, []).
Proof.
  intros mxr do_sum s. destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma wkperm_check_load (pc : kperm) (ad : bool * bool) :
  forall (mxr do_sum : bool) s,
  exec_eff (check_PTE_permission (Load Data) Supervisor mxr do_sum
              (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad)))
              (Mk_PTE_Ext (mword_of_int 0)) tt) s
  = Some (PTE_Check_Success tt, s, []).
Proof.
  intros mxr do_sum s.
  destruct pc; destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma wkperm_check_store (ad : bool * bool) : forall (mxr do_sum : bool) s,
  exec_eff (check_PTE_permission (Store Data) Supervisor mxr do_sum
              (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rw ad)))
              (Mk_PTE_Ext (mword_of_int 0)) tt) s
  = Some (PTE_Check_Success tt, s, []).
Proof.
  intros mxr do_sum s. destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma wkperm_check_amo (ad : bool * bool) (aq rl : bool) :
  forall (mxr do_sum : bool) s,
  exec_eff (check_PTE_permission (Atomic (AMOSWAP, aq, rl, Data, Data))
              Supervisor mxr do_sum
              (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rw ad)))
              (Mk_PTE_Ext (mword_of_int 0)) tt) s
  = Some (PTE_Check_Success tt, s, []).
Proof.
  intros mxr do_sum s.
  destruct ad as [a d]; destruct a, d, aq, rl, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

(** Every A/D variant of a class-keyed leaf is eff-valid. *)
Lemma wkperm_variant_valid (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  wpte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply wkperm_inv_red.
Qed.

(** The class-keyed eff check dispatcher ([KptTree.kperm_variant_check]'s
    twin). *)
Lemma wkperm_variant_check (ppn : mword 44) (pc : kperm)
    (acc : MemoryAccessType mem_payload) (a d : mword 1) (mxr do_sum : bool) :
  (acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
   (exists aq rl, acc = Atomic (AMOSWAP, aq, rl, Data, Data))) ->
  kperm_allows pc acc ->
  wpte_check_ok acc Supervisor mxr do_sum
    (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  intros Hacc Hall s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  destruct Hacc as [-> | [-> | [-> | (aq & rl & ->)]]].
  - cbn in Hall. subst pc. apply wkperm_check_fetch.
  - apply wkperm_check_load.
  - cbn in Hall. subst pc. apply wkperm_check_store.
  - cbn in Hall. subst pc. apply wkperm_check_amo.
Qed.

(* ====================================================================== *)
(** ** 3. The invariant and the per-hart residue *)

(** The namespace ([KptGhost.kptN]'s sibling; batch-6c consumers carry the
    mask premise [↑wkptN ⊆ E], the [sr_absorb] shape). *)
Definition wkptN : namespace := nroot .@ "weakkpt".

(** The pure per-slot geometry the SC tier derived from the physical-tier
    points-to; the weak elements carry no address classification, so the
    invariant stores it ([PtTree.pt_slot_mem]'s non-byte half). *)
Definition wslot_geom (a : Arch.pa) : Prop :=
  addr_is_ram a /\ addr_is_ram (pa_add a 7) /\
  is_aligned_paddr (Physaddr a) 8 = true.

(** An in-RAM 8-byte window does not wrap. *)
Lemma wslot_geom_acc_wf (a : Arch.pa) : wslot_geom a -> acc_wf a 8.
Proof.
  intros (Hram & _ & _). destruct Hram as [_ Hhi].
  rewrite /acc_wf /pa_z. unfold ram_base, ram_size in Hhi. lia.
Qed.

Section WeakKptInv.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** *** 3a. The POINTER-slot resource: persistent, kvminit-timestamped

      Pointer words are single-message (only leaf words are ever stored
      to), so the eight elements are DISCARDED — persistent, freely
      duplicable — and the timestamp bound [ts ≤ T_kpt] is the pure half
      of "pinned via the per-hart receipt".  [wpte_valid] is stored
      because the eff walk needs it and it does not transport from
      [ptree_maps]' SC classification (the words are abstract here). *)
  Definition wptr8 (T_kpt : nat) (a : Arch.pa) (w : mword 64) : iProp Σ :=
    (∃ ts : nat,
       ⌜(ts <= T_kpt)%nat⌝ ∗ ⌜wslot_geom a⌝ ∗ ⌜wpte_valid w⌝ ∗
       wlat8 a DfracDiscarded ts w)%I.

  Global Instance wlat8_discarded_persistent a t w :
    Persistent (wlat8 a DfracDiscarded t w).
  Proof. rewrite /wlat8. apply _. Qed.

  Global Instance wptr8_persistent T_kpt a w : Persistent (wptr8 T_kpt a w).
  Proof. rewrite /wptr8. apply _. Qed.

  Global Instance wptr8_timeless T_kpt a w : Timeless (wptr8 T_kpt a w).
  Proof. rewrite /wptr8. apply _. Qed.

  (** *** 3b. The LEAF-window resource: exclusive, closure-carrying

      The eight elements at one shared timestamp holding SOME A/D variant
      of the canonical leaf [w0], plus the clipped closure facts against a
      log snapshot [log0] (see the header's design correction):
        - [T0] is the window's INSTALL timestamp (kvmmake's store);
        - the element's timestamp is at or above the install and inside
          the snapshot, so "no message above the snapshot touches the
          window" is derivable from the element at any later log;
        - the closure and the CAS discipline hold of the snapshot;
        - the discipline is stored ∀-image (it only ever reads message
          timestamps — [log_byte_img_irrel]). *)
  Definition wleaf_res (T_kpt : nat) (la : Arch.pa) (w0 : mword 64)
      (a d : mword 1) : iProp Σ :=
    (∃ (ts T0 : nat) (log0 : list wmsg),
       ⌜wslot_geom la⌝ ∗
       ⌜(1 <= T0)%nat /\ (T0 <= T_kpt)%nat /\ (T0 <= ts)%nat /\
        (ts <= length log0)%nat⌝ ∗
       ⌜wwin_install log0 T0 la⌝ ∗
       ⌜wlog_variants_from T0 log0 (pa_z la) w0⌝ ∗
       ⌜forall img : image, wfresh_from T0 img log0 (pa_z la)⌝ ∗
       wlog_lb log0 ∗
       wlat8 la (DfracOwn 1) ts (pte_set_ad w0 a d))%I.

  Global Instance wleaf_res_timeless T_kpt la w0 a d :
    Timeless (wleaf_res T_kpt la w0 a d).
  Proof. rewrite /wleaf_res /wlog_lb. apply _. Qed.

  (** *** 3c. The per-vpn bundle: the walk path of one mapped vpn

      [ptree_maps] ties the elements' words to the (existential) tree,
      exactly as [ptree_own] tied the heap words to it; the element
      variant (a, d) IS the tree's resident leaf variant. *)
  Definition wvpn_res (T_kpt : nat) (t : ptree) (vpn : mword 27)
      (e : mword 44 * kperm) : iProp Σ :=
    (∃ (p2 p1 : mword 64) (a d : mword 1),
       ⌜ptree_maps t vpn p2 p1 (pte_set_ad (kpt_leaf_pte_of vpn e) a d)⌝ ∗
       wptr8 T_kpt (pt_addr2 t vpn) p2 ∗
       wptr8 T_kpt (pt_addr1 p2 vpn) p1 ∗
       wleaf_res T_kpt (pt_addr0 p1 vpn) (kpt_leaf_pte_of vpn e) a d)%I.

  Global Instance wvpn_res_timeless T_kpt t vpn e :
    Timeless (wvpn_res T_kpt t vpn e).
  Proof. rewrite /wvpn_res. apply _. Qed.

  (** *** 3d. The body and the invariant *)

  Definition wkpt_body (root_ppn : mword 44) (T_kpt : nat) : iProp Σ :=
    (∃ (t : ptree) (M : gmap (mword 27) (mword 44 * kperm)),
       kpt_lb t ∗
       kmap_auth M ∗
       ⌜kpt_tree_spec_gen root_ppn M t⌝ ∗
       ([∗ map] vpn ↦ e ∈ M, wvpn_res T_kpt t vpn e))%I.

  Global Instance wkpt_body_timeless root_ppn T_kpt :
    Timeless (wkpt_body root_ppn T_kpt).
  Proof. rewrite /wkpt_body. apply _. Qed.

  Definition wkpt_inv (root_ppn : mword 44) (T_kpt : nat) : iProp Σ :=
    inv wkptN (wkpt_body root_ppn T_kpt).

  Global Instance wkpt_inv_persistent root_ppn T_kpt :
    Persistent (wkpt_inv root_ppn T_kpt).
  Proof. apply _. Qed.

  Lemma wkpt_inv_alloc (root_ppn : mword 44) (T_kpt : nat) (E : coPset) :
    wkpt_body root_ppn T_kpt ={E}=∗ wkpt_inv root_ppn T_kpt.
  Proof.
    iIntros "Hbody".
    iMod (inv_alloc wkptN _ (wkpt_body root_ppn T_kpt) with "[Hbody]")
      as "#Hinv"; [by iNext|].
    iModIntro. iExact "Hinv".
  Qed.

  (** *** 3e. The per-hart residue: [KptShare.tlb_res_pt]'s mirror.  The
      satp cell + facts, the tlb cell, the [kpt_lb]-keyed snapshot
      coherence ([KptShare.tlb_snap_ok], reused verbatim — it is register-
      and ghost-side only) and the pmp cells transfer UNCHANGED (the M3a
      config-tower verdict); only the table invariant is the weak one. *)
  Definition wtlb_res_pt (root_ppn : mword 44) (T_kpt : nat) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜_get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4)⌝ ∗
       ⌜zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16)⌝ ∗
       ⌜autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn⌝ ∗
       tlb ↦ᵣ tlbvec ∗ tlb_snap_ok tlbvec ∗
       pmp_config root_ppn ∗
       wkpt_inv root_ppn T_kpt)%I.

  Lemma wtlb_res_pt_intro (root_ppn : mword 44) (T_kpt : nat)
      (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (t0 : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_ok_pt (mword_of_int 0) t0 tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_lb t0 -∗
    pmp_config root_ppn -∗ wkpt_inv root_ppn T_kpt -∗
    wtlb_res_pt root_ppn T_kpt.
  Proof.
    intros Hmode Hasid Hppn Hok. iIntros "Hsatp Htlb Hlb Hpmp Hinv".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpmp Hinv".
    iSplitR; [iPureIntro; exact Hmode |].
    iSplitR; [iPureIntro; exact Hasid |].
    iSplitR; [iPureIntro; exact Hppn |].
    iExists t0. iFrame "Hlb". iPureIntro. exact Hok.
  Qed.

End WeakKptInv.

(* ====================================================================== *)
(** ** 4. The pure dispatch: [KptTree.ptree_translateAddr_cases] at
    [exec_eff]

    The total translation case analysis over the walk-path facts, at an
    abstract SC state [sg] (§5 instantiates [sg := wflat_st σ]).  Same
    premises as the SC original plus the eff-level classification
    ([wpte_valid] for the two pointer words and the ∀-variant leaf family)
    — and the conclusion additionally pins the EXACT per-outcome trace.

    Outcomes (and their traces):
      O1  TLB hit, cached variant needs no bits          — []
      O2  miss, walk + fill, leaf needs no bits          — the 3 plain reads
      O2' hit, cached variant needs bits, memory doesn't — the CAS read
      O3  write-back + fill (miss) / refresh (hit)       — reads + CAS pair *)

Section WeakKptDispatch.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (* shared miss path: the TLB slot misses (empty or foreign), so the walk
     runs -- filling cleanly (O2) or writing the A/D update back (O3) *)
  Lemma wptree_translate_miss_eff_core (root_ppn : mword 44)
        (va w : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (sg : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    (forall a d : mword 1, wpte_valid (pte_set_ad w a d)) ->
    wpte_valid p2 -> pte_ptr p2 ->
    wpte_valid p1 -> pte_ptr p1 ->
    pte_leaf p0 -> pte_no_napot p0 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    exec_eff (read_pte (Physaddr (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))) 8) sg
      = Some (Ok p2, sg, [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) sg
      = Some (Ok p1, sg, [WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8]) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) sg
      = Some (Ok p0, sg, [WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]) ->
    exec_eff (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) sg
      = Some (Ok p0, sg, [WEread (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]) ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg, []) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    exists (sg' : mstate) (es : list weff),
      (forall mxr do_sum,
         exec_eff (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc p mxr do_sum tt) sg
         = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44), PBMT_PMA, tt), sg', es))
      /\ ( (sg' = set_reg sg tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                    (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
           /\ es = [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                    WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                    WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8])
         \/ (exists (a1 d1 : mword 1),
               update_PTE_Bits (p0 : mword 64) acc = Some (pte_set_ad p0 a1 d1)
               /\ sg' = set_reg (MState sg.(sregs)
                               (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8
                                  (pte_set_ad p0 a1 d1))
                               sg.(mdev))
                      tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0))))
               /\ es = [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                        WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                        WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8;
                        WEread (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8;
                        WEwrite (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8
                          (pte_set_ad p0 a1 d1 : mword 64)])).
  Proof.
    intros vpn p0 Hchk Hval Hwv2 Hn2 Hwv1 Hn1 Hl0 Hnap Hsm0
           Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlbv Hlk
           HA Hord HW Hcov Hpmaw.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hup.
    - (* O3: the walk writes the A/D-updated leaf back *)
      pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
      destruct (Hpmaw (pt_addr0 p1 vpn)
            (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
               eq_refl eq_refl)) as (region0 & Hm0 & Hw0).
      assert (Hwr : exec_eff (write_pte_conditional
                 (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                 (p0' : mword 64)) sg
               = Some (Ok true, MState sg.(sregs)
                          (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev),
                       [WEwrite (AkInfo false true false) (pt_addr0 p1 vpn) 8 p0'])).
      { exact (exec_eff_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' region0 sg
                 Hram0 Hram0' Hal0 HA Hord HW Hcov Hm0 Hw0 Hhtif). }
      destruct (update_PTE_Bits_set_ad _ _ _ Hup) as (a1 & d1 & Hq).
      do 2 eexists. split.
      + intros mxr do_sum.
        apply (exec_eff_translate_miss_user vpn root_ppn (mword_of_int 0)
                 acc p mxr do_sum _ sg _ _ Hlk).
        apply (exec_eff_translate_TLB_miss_user_upd acc p mxr do_sum vpn root_ppn
                 p2 p1 p0 p0' MENVCFG_S (mword_of_int 0) _ _ _ _ _
                 (MState sg.(sregs) (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev)) sg
                 Hwv2 Hn2 Hwv1 Hn1 (Hval a0 d0) Hl0
                 (Hchk a0 d0 mxr do_sum) Hnap Hup
                 Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv HPBMTE HADUE Hwr eq_refl).
      + right. exists a1, d1.
        split; [rewrite <- Hq; reflexivity|].
        split; [rewrite <- Hq; rewrite Htlbv; reflexivity|].
        rewrite <- Hq. reflexivity.
    - (* O2: clean fill *)
      assert (Hupd : update_PTE_Bits (autocast (T := mword) p0 : mword 64) acc = None)
        by exact Hup.
      do 2 eexists. split.
      + intros mxr do_sum.
        apply (exec_eff_translate_miss_user vpn root_ppn (mword_of_int 0)
                 acc p mxr do_sum _ sg _ _ Hlk).
        apply (exec_eff_translate_TLB_miss_user vpn root_ppn p2 p1 p0 acc p mxr do_sum
                 Hwv2 Hn2 Hwv1 Hn1 (Hval a0 d0) Hl0
                 (Hchk a0 d0 mxr do_sum) Hnap
                 (mword_of_int 0) MENVCFG_S _ _ _ sg Hmisa Hupd Hrd2 Hrd1 Hrd0
                 Hmenv HPBMTE).
      + left. split; [rewrite Htlbv; reflexivity|reflexivity].
  Qed.

End WeakKptDispatch.

Section WeakKptDispatchCases.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma wptree_translateAddr_eff_cases (root_ppn : mword 44)
        (va w pa satp0 : mword 64) (t : ptree)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (sg : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    (forall a d : mword 1, wpte_valid (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    wpte_valid p2 -> wpte_valid p1 ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    pt_slot_mem sg (pt_addr2 t vpn) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = p ->
    exec_eff (translationMode p) sg = Some (Sv39, sg, []) ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) p) sg
      = Some (p, sg, []) ->
    exec_eff (is_shadow_stack_access acc) sg = Some (false, sg, []) ->
    register_lookup satp sg.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    exists (sg' : mstate) (es : list weff),
      exec_eff (translateAddr (Virtaddr va) acc) sg
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)
      /\ ( (sg' = sg /\ es = [])
         \/ (sg' = set_reg sg tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                     (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
             /\ (es = [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                       WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                       WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]
                 \/ es = [WEread (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8]))
         \/ (exists (a1 d1 : mword 1),
               update_PTE_Bits (p0 : mword 64) acc = Some (pte_set_ad p0 a1 d1)
               /\ sg' = set_reg (MState sg.(sregs)
                               (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8
                                  (pte_set_ad p0 a1 d1))
                               sg.(mdev))
                      tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0))))
               /\ (es = [WEread wak_plain (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8;
                         WEread wak_plain (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) 8;
                         WEread wak_plain (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8;
                         WEread (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8;
                         WEwrite (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8
                           (pte_set_ad p0 a1 d1 : mword 64)]
                   \/ es = [WEread (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8;
                            WEwrite (AkInfo false true false) (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) 8
                              (pte_set_ad p0 a1 d1 : mword 64)]))).
  Proof.
    intros vpn p0 Hchk Hval Hcanon Hout Hvarp Hwv2 Hwv1 Hbase Hmaps Htlbok
           Hsm2 Hsm1 Hsm0 Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatp Hppn Hasid
           Htlbv HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    (* the three PTE reads, at the walk's canonical slot spellings *)
    assert (Hsm2' : pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hsm1' : pt_slot_mem sg (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) p1)
      by exact Hsm1.
    assert (Hsm0' : pt_slot_mem sg (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) p0)
      by exact Hsm0.
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
           (pt_slot_ram_access _ _ _ Hsm2'))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))
           (pt_slot_ram_access _ _ _ Hsm1'))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
           (pt_slot_ram_access _ _ _ Hsm0'))
      as (region0 & Hm0r & Hs0).
    pose proof (wpt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (wpt_read_pte_slot sg _ p1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (wpt_read_pte_slot sg _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    pose proof (wpt_read_pte_exclusive_slot sg _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    (* identity geometry *)
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - (* resident entry *)
      destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* HIT on this vpn's own (A/D-variant) entry *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  wpte_check_ok acc p mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d')).
        { assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. exact Hid. }
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* the CACHED word wants A/D bits: split on whether MEMORY does *)
          assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
          { exists a0, d0. rewrite pte_set_ad_absorb.
            unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
          destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back (O3, hit path) *)
             pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             destruct (Hpmaw (pt_addr0 p1 vpn)
               (pma_access_ram _ _ _ Hram0 Hram0' (pma_width_ok 8 eq_refl eq_refl)
                  eq_refl eq_refl)) as (regionw & Hmw & Hww).
             assert (Hwr : exec_eff (write_pte_conditional
                        (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                        (p0' : mword 64)) sg
                      = Some (Ok true, MState sg.(sregs)
                                 (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev),
                              [WEwrite (AkInfo false true false) (pt_addr0 p1 vpn) 8 p0']))
               by exact (exec_eff_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
             destruct (update_PTE_Bits_set_ad _ _ _ Hupm) as (a1 & d1 & Hq).
             do 2 eexists. split.
             { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa _ sg _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                        (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                           (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               apply (exec_eff_translate_TLB_hit_pt_upd acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ _
                        (MState sg.(sregs) (write_bytes sg.(mem) (pt_addr0 p1 vpn) 8 p0') sg.(mdev)) sg
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx (Hval a0 d0) Hl0 (Hchk a0 d0 mxr do_sum) Hnap Hmisa HPBMTE
                        Hvarm Hupm Hwr eq_refl). }
             right. right. exists a1, d1.
             split; [rewrite <- Hq; reflexivity|].
             split; [rewrite <- Hq; rewrite Htlbv; reflexivity|].
             rewrite <- Hq. right. reflexivity.
          -- (* memory ALREADY has them: refresh only (O2', trace = the CAS read) *)
             do 2 eexists. split.
             { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                        (autocast (T := mword) ((autocast (T := mword)
                           (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                        satp0 va pa _ sg _
                        Heff Hss Hcp Htm Hsatp Hppn Hasid
                        Hcanon eq_refl).
               2:{ exact Hidc. }
               intros mxr do_sum.
               apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                        (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                           (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
               apply (exec_eff_translate_TLB_hit_pt_refresh acc p mxr do_sum
                        vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S (mword_of_int 0)
                        (tlb_hash (__id 39) vpn) _ sg
                        (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                        Hrdx (Hval a0 d0) Hl0 (Hchk a0 d0 mxr do_sum) Hnap Hmisa HPBMTE
                        Hvarm Hupm). }
             right. left.
             split; [rewrite Htlbv; reflexivity|].
             right. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          do 2 eexists. split.
          { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa _ sg _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            apply (exec_eff_translate_hit_user vpn root_ppn (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) _ acc p mxr do_sum _ sg _ _
                     (exec_eff_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlbv Hslot
                        (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            apply (exec_eff_translate_TLB_hit_pt acc p mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) sg
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. split; reflexivity.
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg, []))
          by exact (exec_eff_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec sg Htlbv Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                         (mword_of_int 0) Hne)).
        destruct (wptree_translate_miss_eff_core acc p root_ppn va w tlbvec p2 p1 a0 d0 sg
                    Hchk Hval Hwv2 Hn2 Hwv1 Hn1 Hl0 Hnap Hsm0
                    Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlbv Hlk
                    HA Hord HW Hcov Hpmaw)
          as (sg' & es & Htr & Hshape).
        exists sg', es. split.
        { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (p0 : mword 64))) : mword 44))
                   satp0 va pa es sg sg'
                   Heff Hss Hcp Htm Hsatp Hppn Hasid
                   Hcanon eq_refl Htr Hid). }
        destruct Hshape as [[Ho2 Hes] | (a1 & d1 & Hu & Ho3 & Hes)].
        * right. left. split; [exact Ho2 | left; exact Hes].
        * right. right. exists a1, d1.
          split; [exact Hu|]. split; [exact Ho3|]. left. exact Hes.
    - (* empty slot: the walk runs *)
      assert (Hlk : exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg, []))
        by exact (exec_eff_lookup_TLB_miss vpn (mword_of_int 0) tlbvec sg Htlbv Hslot).
      destruct (wptree_translate_miss_eff_core acc p root_ppn va w tlbvec p2 p1 a0 d0 sg
                  Hchk Hval Hwv2 Hn2 Hwv1 Hn1 Hl0 Hnap Hsm0
                  Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv Hhtif Htlbv Hlk
                  HA Hord HW Hcov Hpmaw)
        as (sg' & es & Htr & Hshape).
      exists sg', es. split.
      { apply (exec_eff_translateAddr_pt_front acc p vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va pa es sg sg'
                 Heff Hss Hcp Htm Hsatp Hppn Hasid
                 Hcanon eq_refl Htr Hid). }
      destruct Hshape as [[Ho2 Hes] | (a1 & d1 & Hu & Ho3 & Hes)].
      * right. left. split; [exact Ho2 | left; exact Hes].
      * right. right. exists a1, d1.
        split; [exact Hu|]. split; [exact Ho3|]. left. exact Hes.
  Qed.

End WeakKptDispatchCases.

(* ====================================================================== *)
(** ** 5. THE ABSORPTION THEOREM *)

(** A slot's [pt_slot_mem] at the flat state, from the invariant's stored
    geometry + the elements' flat lookups. *)
Lemma wslot_mem_of_flat (σ : wmstate) (a : Arch.pa) (w : mword 64) :
  wslot_geom a ->
  (forall j : nat, (j < 8)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) ->
  pt_slot_mem (wflat_st σ) a w.
Proof.
  intros (Hram & Hram7 & Hal) Hb.
  split_and!; [|exact Hram|exact Hram7|exact Hal].
  intros j Hj. apply Hb. lia.
Qed.

Section WeakKptAbsorb.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** The per-vpn bundle transports along a maps-preserving, base-preserving
      tree change — the frame step for the OTHER vpns at a write-back. *)
  Lemma wvpn_res_maps_mono (T_kpt : nat) (t t2 : ptree) (vpn' : mword 27)
      (e' : mword 44 * kperm) :
    (forall p2 p1 q0 : mword 64,
       ptree_maps t vpn' p2 p1 q0 -> ptree_maps t2 vpn' p2 p1 q0) ->
    pt_base t2 = pt_base t ->
    wvpn_res T_kpt t vpn' e' ⊢ wvpn_res T_kpt t2 vpn' e'.
  Proof.
    intros Hmono Hb. iIntros "H".
    iDestruct "H" as (p2 p1 a d) "(%Hm & H2 & H1 & HL)".
    iExists p2, p1, a, d.
    assert (Ha2 : pt_addr2 t2 vpn' = pt_addr2 t vpn')
      by (unfold pt_addr2; rewrite Hb; reflexivity).
    rewrite Ha2. iFrame "H2 H1 HL".
    iPureIntro. exact (Hmono _ _ _ Hm).
  Qed.

  Context (acc : MemoryAccessType mem_payload).

  Lemma wtlb_res_pt_translateAddr_at (root_ppn : mword 44) (T_kpt : nat)
      (tid : option nat) (va pa : mword 64) (ppn : mword 44) (pc : kperm)
      (σ : wmstate) (E : coPset) :
    ↑wkptN ⊆ E ->
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    (forall a d : mword 1,
       wpte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    wlog_wf (wm_log σ) ->
    register_lookup misa (wm_regs σ) = MISA_C ->
    register_lookup menvcfg (wm_regs σ) = MENVCFG_S ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup cur_privilege (wm_regs σ) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus (wm_regs σ)) = 'b"10" ->
    exec_eff (effectivePrivilege acc (register_lookup mstatus (wm_regs σ)) Supervisor)
      (wflat_st σ) = Some (Supervisor, wflat_st σ, []) ->
    exec_eff (is_shadow_stack_access acc) (wflat_st σ)
      = Some (false, wflat_st σ, []) ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    (* the per-hart receipt's pure shadow: the hart's read floor covers the
       kvminit horizon *)
    (T_kpt <= w_vrNew (wm_ws σ))%nat ->
    kmap_at (svpn_of va) ppn pc -∗
    reg_interp (wm_regs σ) -∗
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wtlb_res_pt root_ppn T_kpt
    ={E}=∗
    ∃ (sg' : mstate) (es : list weff) (p2 p1 lw : mword 64),
      let vpn := svpn_of va in
      let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
      let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
      let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
      ⌜exec_eff (translateAddr (Virtaddr va) acc) (wflat_st σ)
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', es)⌝ ∗
      ⌜mdev sg' = wm_dev σ⌝ ∗
      ⌜(sregs sg' = wm_regs σ \/
        exists tv, sregs sg' = register_set tlb tv (wm_regs σ))%type⌝ ∗
      ⌜exists a d : mword 1, lw = pte_set_ad (mk_pte ppn (kperm_flags pc)) a d⌝ ∗
      ⌜pt_slot_mem (wflat_st σ) a2 p2 /\ pt_slot_mem (wflat_st σ) a1 p1 /\
       pt_slot_mem (wflat_st σ) la lw⌝ ∗
      ⌜forall j : nat, (j < 8)%nat ->
         pinned_read σ (acc_addr a2 j) /\ pinned_read σ (acc_addr a1 j)⌝ ∗
      ⌜forall (rak : akinfo) (wv : bv (8 * 8)%N),
         wadm σ rak la 8 wv ->
         (exists a d : mword 1,
            (wv : mword 64) = pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
         pte_ad_le (wv : mword 64) lw⌝ ∗
      reg_interp (sregs sg') ∗
      wtlb_res_pt root_ppn T_kpt ∗
      ( (⌜mem sg' = wflat (wm_img σ) (wm_log σ) /\
          (es = [] \/
           es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                 WEread wak_plain la 8] \/
           es = [WEread (AkInfo false true false) la 8])⌝ ∗
         wlog_auth (wm_log σ) ∗ wlat_interp (wm_img σ) (wm_log σ))
        ∨
        (∃ (lw' : mword 64) (kcls : wm_class),
           ⌜update_PTE_Bits (lw : mword 64) acc = Some lw'⌝ ∗
           ⌜mem sg' = write_bytes (wflat (wm_img σ) (wm_log σ)) (la : Arch.pa) 8 lw'⌝ ∗
           ⌜es = [WEread wak_plain a2 8; WEread wak_plain a1 8;
                  WEread wak_plain la 8;
                  WEread (AkInfo false true false) la 8;
                  WEwrite (AkInfo false true false) la 8 (lw' : mword 64)] \/
            es = [WEread (AkInfo false true false) la 8;
                  WEwrite (AkInfo false true false) la 8 (lw' : mword 64)]⌝ ∗
           wlog_auth (wm_log σ ++ [wwrite_msg tid kcls (la : Arch.pa) 8 (lw' : mword 64)]) ∗
           wlat_interp (wm_img σ)
             (wm_log σ ++ [wwrite_msg tid kcls (la : Arch.pa) 8 (lw' : mword 64)]))).
  Proof.
    intros HE Hchk Hval Hcanon Hid4k Hwlog Hmisa Hmenv Hhtif Hcp HSXL Heff Hss
           Hall Hrcpt.
    iIntros "Hat Hri Hla Hi Hres".
    iDestruct "Hres" as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & Hsnap & Hpmp & #Hkinv)".
    iDestruct "Hsnap" as (t0) "(%Htlbok0 & #Hlb0)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    pose proof (pma_allows_all_pte_write _ Hall) as Hpmaw.
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n (wm_regs σ)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (HW' : eq_vec (_get_Pmpcfg_ent_W
      (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HW).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n (wm_regs σ)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    assert (Htm : exec_eff (translationMode Supervisor) (wflat_st σ)
                  = Some (Sv39, wflat_st σ, []))
      by exact (exec_eff_translationMode_S_sv39 satp0 (wflat_st σ) HSXL Hsatpv Hmode).
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags pc) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn pc ('b"1") ('b"1")) in Hid4k.
      rewrite pte_set_ad_ppn in Hid4k. exact Hid4k. }
    assert (Hvarp : forall a d : mword 1,
       pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d))
      by (intros a d; apply kperm_variant_pbmt0).
    (* ---- open the shared table ---- *)
    iInv "Hkinv" as ">Hbody" "Hclose".
    iEval (rewrite /wkpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(#Hlbt & HM & %Hspec & Hmap)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan0.
    assert (Htlbok : tlb_ok_pt (mword_of_int 0) t tlbvec)
      by exact (tlb_ok_pt_canon (mword_of_int 0) t0 t tlbvec Hcan0 Htlbok0).
    set (vpn := svpn_of va) in *.
    pose proof Hspec as (Hbase & Hmapspec).
    (* ---- the vpn's bundle ---- *)
    iDestruct (big_sepM_delete _ M vpn _ HMlk with "Hmap") as "[Hvpn Hrest]".
    iDestruct "Hvpn" as (p2 p1 a0 d0) "(%Hmaps & #Hptr2 & #Hptr1 & Hleaf)".
    assert (Hlf : kpt_leaf_pte_of vpn (ppn, pc) = mk_pte ppn (kperm_flags pc))
      by reflexivity.
    rewrite Hlf in Hmaps.
    iEval (rewrite Hlf) in "Hleaf".
    set (w0 := mk_pte ppn (kperm_flags pc)) in *.
    set (lw := pte_set_ad w0 a0 d0) in *.
    iDestruct "Hptr2" as (ts2) "(%Hts2 & %Hg2 & %Hwv2 & #Hel2)".
    iDestruct "Hptr1" as (ts1) "(%Hts1 & %Hg1 & %Hwv1 & #Hel1)".
    iDestruct "Hleaf" as (ts T0 log0)
      "(%Hg0 & %Hbnds & %Hinst0 & %Hvars0 & %Hfresh0 & #Hlblog & Hel0)".
    destruct Hbnds as (HT01 & HT0K & HT0ts & Htslen).
    (* ---- the slots at the flat state ---- *)
    pose proof (wslot_geom_acc_wf _ Hg2) as Hwf2.
    pose proof (wslot_geom_acc_wf _ Hg1) as Hwf1.
    pose proof (wslot_geom_acc_wf _ Hg0) as Hwf0.
    iDestruct (wlat8_flat_gen σ (pt_addr2 t vpn) DfracDiscarded ts2 p2
                 Hwlog Hwf2 with "Hi Hel2") as %[Hfl2 Hlat2].
    iDestruct (wlat8_flat_gen σ (pt_addr1 p2 vpn) DfracDiscarded ts1 p1
                 Hwlog Hwf1 with "Hi Hel1") as %[Hfl1 Hlat1].
    iDestruct (wlat8_flat_gen σ (pt_addr0 p1 vpn) (DfracOwn 1) ts lw
                 Hwlog Hwf0 with "Hi Hel0") as %[Hfl0 Hlat0].
    pose proof (wslot_mem_of_flat σ (pt_addr2 t vpn) p2 Hg2 Hfl2) as Hsm2.
    pose proof (wslot_mem_of_flat σ (pt_addr1 p2 vpn) p1 Hg1 Hfl1) as Hsm1.
    pose proof (wslot_mem_of_flat σ (pt_addr0 p1 vpn) lw Hg0 Hfl0) as Hsm0.
    (* ---- the clipped closure, extended to the current log ---- *)
    iDestruct (wlog_valid with "Hla Hlblog") as %Hpref.
    pose proof (prefix_length _ _ Hpref) as Hlen0.
    set (la := pt_addr0 p1 vpn) in *.
    assert (Hnw : forall (i : nat) (m : wmsg),
              wm_log σ !! i = Some m -> (ts <= i)%nat ->
              forall j : nat, (j < 8)%nat -> msg_byte m (acc_addr la j) = None)
      by exact (wwin_no_write_above σ la ts Hlat0).
    assert (Hvars : wlog_variants_from T0 (wm_log σ) (pa_z la) w0).
    { refine (wlog_variants_from_ext T0 log0 (wm_log σ) (pa_z la) w0
                Hvars0 Hpref _).
      intros i m Hm Hge j Hj. exact (Hnw i m Hm ltac:(lia) j Hj). }
    assert (Hfresh : forall img : image, wfresh_from T0 img (wm_log σ) (pa_z la)).
    { intros img.
      refine (wfresh_from_ext T0 img log0 (wm_log σ) (pa_z la)
                (Hfresh0 img) Hpref _).
      intros i m Hm Hge.
      rewrite -(acc_addr_0 la). exact (Hnw i m Hm ltac:(lia) 0%nat ltac:(lia)). }
    assert (Hinst : wwin_install (wm_log σ) T0 la)
      by exact (wwin_install_prefix log0 (wm_log σ) T0 la Hinst0 Hpref).
    assert (Hcovg : (T0 <= w_vrNew (wm_ws σ))%nat) by lia.
    (* ---- the racy-leaf collapse facts ---- *)
    iDestruct (wlat8_win_latest σ la (DfracOwn 1) ts lw with "Hi Hel0")
      as %Hwlat.
    assert (Hcoll : forall (rak : akinfo) (wv : bv (8 * 8)%N),
              wadm σ rak la 8 wv ->
              (exists a d : mword 1, (wv : mword 64) = pte_set_ad w0 a d) /\
              pte_ad_le (wv : mword 64) (lw : mword 64)).
    { intros rak wv Hadm. split.
      - exact (wadm_variant_from σ rak la w0 T0 wv Hvars Hinst Hcovg Hadm).
      - exact (wadm_pte_ad_le_latest_from σ rak la w0 T0 wv lw
                 Hvars (Hfresh (wimg σ)) Hinst Hcovg Hwlat Hadm). }
    (* ---- pointer pinnedness for the caller's trace_pin ---- *)
    assert (Hpin : forall j : nat, (j < 8)%nat ->
              pinned_read σ (acc_addr (pt_addr2 t vpn) j) /\
              pinned_read σ (acc_addr (pt_addr1 p2 vpn) j)).
    { intros j Hj. split; rewrite /pinned_read.
      - rewrite (Hlat2 j Hj). lia.
      - rewrite (Hlat1 j Hj). lia. }
    (* ---- the leaf's byte-0 latest value, for the write-back arm ---- *)
    iDestruct (wlat_lookup with "Hi [Hel0]") as %Hlv0;
      [iDestruct "Hel0" as "(E0 & _)"; iExact "E0"|].
    (* ---- run the dispatch at the flat state ---- *)
    destruct (wptree_translateAddr_eff_cases acc Supervisor root_ppn va w0 pa
                satp0 t tlbvec p2 p1 a0 d0 (wflat_st σ)
                Hchk Hval Hcanon Hout Hvarp Hwv2 Hwv1 Hbase Hmaps Htlbok
                Hsm2 Hsm1 Hsm0 Hmisa Hmenv Hhtif Hcp Htm Heff Hss
                Hsatpv Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (sg' & es & Htrans & Harm).
    (* the walk-spelled slot facts for the conclusion *)
    assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
      by (unfold pt_addr2; rewrite Hbase; reflexivity).
    destruct Harm as [[Hsg' Hes] | [ [Hsg' Hes] | (a1 & d1 & Hupd & Hsg' & Hes) ]].
    - (* O1: nothing moved *)
      iMod ("Hclose" with "[HM Hrest Hel0]") as "_".
      { iNext. iExists t, M. iFrame "Hlbt HM".
        iSplitR; [iPureIntro; exact Hspec|].
        iApply (big_sepM_delete _ M vpn _ HMlk). iFrame "Hrest".
        iExists p2, p1, a0, d0.
        iSplitR; [iPureIntro; exact Hmaps|].
        iSplitR; [iExists ts2; iFrame "Hel2"; iPureIntro; tauto|].
        iSplitR; [iExists ts1; iFrame "Hel1"; iPureIntro; tauto|].
        iExists ts, T0, log0. iFrame "Hlblog Hel0". iPureIntro. tauto. }
      iModIntro.
      iExists sg', es, p2, p1, lw.
      iSplitR; [iPureIntro; exact Htrans|].
      iSplitR; [iPureIntro; rewrite Hsg'; reflexivity|].
      iSplitR; [iPureIntro; left; rewrite Hsg'; reflexivity|].
      iSplitR; [iPureIntro; exists a0, d0; reflexivity|].
      iSplitR; [iPureIntro; rewrite -Ha2; auto|].
      iSplitR; [iPureIntro; rewrite -Ha2; exact Hpin|].
      iSplitR; [iPureIntro; exact Hcoll|].
      rewrite Hsg'. iFrame "Hri".
      iSplitL "Hsatp Htlb Hpc Hpa".
      { iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 tlbvec t
                  Hmode Hasid Hppn Htlbok with "Hsatp Htlb Hlbt [Hpc Hpa] Hkinv").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA Hord HX HW HR Hcov with "Hpc Hpa"). }
      iLeft. iFrame "Hla Hi". iPureIntro.
      split; [reflexivity|]. left. exact Hes.
    - (* O2: TLB fill (walk) or in-place refresh (hit whose memory word
         already has the bits) *)
      iMod (reg_update (wm_regs σ) tlb tlbvec
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 lw (mword_of_int 0))))
              with "Hri Htlb") as "[Hri Htlb]".
      assert (Htlbok' : tlb_ok_pt (mword_of_int 0) t
                (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                   (Some (u_walk_entry vpn p2 p1 lw (mword_of_int 0)))))
        by exact (tlb_ok_pt_fill_self (mword_of_int 0) t tlbvec vpn p2 p1 lw
                    Hmaps Htlbok).
      iMod ("Hclose" with "[HM Hrest Hel0]") as "_".
      { iNext. iExists t, M. iFrame "Hlbt HM".
        iSplitR; [iPureIntro; exact Hspec|].
        iApply (big_sepM_delete _ M vpn _ HMlk). iFrame "Hrest".
        iExists p2, p1, a0, d0.
        iSplitR; [iPureIntro; exact Hmaps|].
        iSplitR; [iExists ts2; iFrame "Hel2"; iPureIntro; tauto|].
        iSplitR; [iExists ts1; iFrame "Hel1"; iPureIntro; tauto|].
        iExists ts, T0, log0. iFrame "Hlblog Hel0". iPureIntro. tauto. }
      iModIntro.
      iExists sg', es, p2, p1, lw.
      iSplitR; [iPureIntro; exact Htrans|].
      iSplitR; [iPureIntro; rewrite Hsg' mdev_set_reg; reflexivity|].
      iSplitR; [iPureIntro; right; eexists; rewrite Hsg' sregs_set_reg; reflexivity|].
      iSplitR; [iPureIntro; exists a0, d0; reflexivity|].
      iSplitR; [iPureIntro; rewrite -Ha2; auto|].
      iSplitR; [iPureIntro; rewrite -Ha2; exact Hpin|].
      iSplitR; [iPureIntro; exact Hcoll|].
      rewrite Hsg' sregs_set_reg. iFrame "Hri".
      iSplitL "Hsatp Htlb Hpc Hpa".
      { iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 _ t
                  Hmode Hasid Hppn Htlbok' with "Hsatp Htlb Hlbt [Hpc Hpa] Hkinv").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA Hord HX HW HR Hcov with "Hpc Hpa"). }
      iLeft. iFrame "Hla Hi". iPureIntro.
      split; [rewrite mem_set_reg; reflexivity|]. right. exact Hes.
    - (* O3: the write-back, absorbed *)
      set (lw' := pte_set_ad lw a1 d1) in *.
      assert (Habs : lw' = pte_set_ad w0 a1 d1)
        by exact (pte_set_ad_absorb w0 a0 d0 a1 d1).
      assert (Hv' : pte_valid lw')
        by (rewrite Habs; exact (kperm_variant_valid ppn pc a1 d1)).
      assert (Hl' : pte_leaf lw')
        by (rewrite Habs; exact (kperm_variant_leaf ppn pc a1 d1)).
      assert (Hn' : pte_no_napot lw')
        by (rewrite Habs; exact (kperm_variant_no_napot ppn pc a1 d1)).
      assert (Hp' : pte_pbmt0 lw')
        by (rewrite Habs; exact (kperm_variant_pbmt0 ppn pc a1 d1)).
      (* the tree moves by the leaf write; the canonical table does not *)
      assert (Hcan' : ptree_canon t = ptree_canon (ptree_set_leaf t vpn lw')).
      { rewrite Habs.
        rewrite <- (pte_set_ad_absorb w0 a0 d0 a1 d1).
        symmetry.
        exact (ptree_canon_set_leaf t vpn p2 p1 lw a1 d1 Hmaps). }
      iDestruct (kpt_lb_canon t (ptree_set_leaf t vpn lw') Hcan' with "Hlbt")
        as "#Hlb'".
      assert (Hspec' : kpt_tree_spec_gen root_ppn M (ptree_set_leaf t vpn lw')).
      { rewrite Habs.
        rewrite <- (pte_set_ad_absorb w0 a0 d0 a1 d1).
        apply (kpt_tree_spec_gen_set_leaf root_ppn M t vpn (ppn, pc) p2 p1
                 lw a1 d1 Hspec Hmaps HMlk).
        exists a0, d0. rewrite Hlf. reflexivity. }
      pose proof Hspec' as (Hbase' & _).
      assert (Hmaps' : ptree_maps (ptree_set_leaf t vpn lw') vpn p2 p1 lw')
        by exact (ptree_set_leaf_maps_self t vpn p2 p1 lw lw' Hmaps Hv' Hl' Hn' Hp').
      assert (Htlbok' : tlb_ok_pt (mword_of_int 0) (ptree_set_leaf t vpn lw')
                (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                   (Some (u_walk_entry vpn p2 p1 lw' (mword_of_int 0))))).
      { apply (tlb_ok_pt_fill_self (mword_of_int 0) (ptree_set_leaf t vpn lw')
                 tlbvec vpn p2 p1 lw' Hmaps').
        exact (tlb_ok_pt_set_leaf (mword_of_int 0) t tlbvec vpn p2 p1 lw a1 d1
                 Hmaps Hv' Hl' Hn' Hp' Htlbok). }
      (* ghost: append the message, retarget the leaf element *)
      iMod (wlog_update (wm_log σ) [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)]
              with "Hla") as "Hla".
      iDestruct (wlog_snapshot with "Hla") as "[Hla #Hlb'']".
      iEval (rewrite /wlat8) in "Hel0".
      iDestruct "Hel0" as "(E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7)".
      iMod (wlat8_store_prim tid WCexcl σ (la : Arch.pa) (lw' : mword 64)
              ts ts ts ts ts ts ts ts
              with "Hi E0 E1 E2 E3 E4 E5 E6 E7") as "[Hi Hel0']".
      (* the new leaf bundle's clipped facts *)
      assert (Hlatbyte : forall img : image,
                log_byte img (wm_log σ) (latest_ts (wm_log σ) (pa_z la)) (pa_z la)
                = Some (nth_byte lw 0)).
      { intros img.
        pose proof (Hlat0 0%nat ltac:(lia)) as Hlt0.
        rewrite acc_addr_0 in Hlt0. rewrite Hlt0.
        rewrite (log_byte_img_irrel img (wimg σ) (wm_log σ) ts (pa_z la)
                   ltac:(lia)).
        pose proof (proj1 Hlv0) as Hlb.
        rewrite acc_addr_0 in Hlb. exact Hlb. }
      assert (Hvars' : wlog_variants_from T0
                (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                (pa_z la) w0).
      { apply (wlog_variants_from_snoc T0 (wm_log σ) (pa_z la) w0 _ Hvars).
        apply (wmsg_variant_write tid WCexcl (la : Arch.pa) (lw' : mword 64) (pa_z la) w0
                 eq_refl).
        exists a1, d1. exact Habs. }
      assert (Hfresh' : forall img : image,
                wfresh_from T0 img
                  (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                  (pa_z la)).
      { intros img.
        exact (wfresh_from_writeback T0 img (wm_log σ) tid WCexcl (la : Arch.pa) acc
                 lw lw' (lw' : mword 64) (Hlatbyte img) Hupd eq_refl (Hfresh img)). }
      assert (Hinst' : wwin_install
                (wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])
                T0 la).
      { refine (wwin_install_prefix (wm_log σ) _ T0 la Hinst _).
        by eexists. }
      (* the register update *)
      iMod (reg_update (wm_regs σ) tlb tlbvec
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 lw' (mword_of_int 0))))
              with "Hri Htlb") as "[Hri Htlb]".
      (* re-close the invariant at the new tree *)
      iMod ("Hclose" with "[HM Hrest Hel0']") as "_".
      { iNext. iExists (ptree_set_leaf t vpn lw'), M. iFrame "Hlb' HM".
        iSplitR; [iPureIntro; exact Hspec'|].
        iApply (big_sepM_delete _ M vpn _ HMlk).
        assert (Haddr2 : pt_addr2 (ptree_set_leaf t vpn lw') vpn = pt_addr2 t vpn)
          by (unfold pt_addr2; rewrite Hbase' Hbase; reflexivity).
        assert (Hmaps'' : ptree_maps (ptree_set_leaf t vpn lw') vpn p2 p1
                            (pte_set_ad w0 a1 d1))
          by (rewrite -Habs; exact Hmaps').
        iEval (rewrite Habs) in "Hel0'".
        iSplitL "Hel0'".
        { iExists p2, p1, a1, d1.
          iSplitR; [iPureIntro; exact Hmaps''|].
          iEval (rewrite Haddr2).
          iSplitR.
          { iExists ts2.
            iSplitR; [iPureIntro; exact Hts2|].
            iSplitR; [iPureIntro; exact Hg2|].
            iSplitR; [iPureIntro; exact Hwv2|].
            iExact "Hel2". }
          iSplitR.
          { iExists ts1.
            iSplitR; [iPureIntro; exact Hts1|].
            iSplitR; [iPureIntro; exact Hg1|].
            iSplitR; [iPureIntro; exact Hwv1|].
            iExact "Hel1". }
          iExists (S (length (wm_log σ))), T0,
            ((wm_log σ ++ [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : mword 64)])%list).
          iSplitR; [iPureIntro; exact Hg0|].
          iSplitR.
          { iPureIntro. split_and!; [lia|lia|lia|].
            rewrite length_app /=. lia. }
          iSplitR; [iPureIntro; exact Hinst'|].
          iSplitR; [iPureIntro; exact Hvars'|].
          iSplitR; [iPureIntro; exact Hfresh'|].
          iSplitR; [iExact "Hlb''"|].
          iExact "Hel0'". }
        iApply (big_sepM_mono with "Hrest").
        intros vpn' e' Hlk'.
        apply lookup_delete_Some in Hlk' as [Hne' _].
        apply (wvpn_res_maps_mono T_kpt t (ptree_set_leaf t vpn lw') vpn' e').
        - intros q2 q1 q0 Hm'.
          exact (ptree_set_leaf_maps_other t vpn vpn' q2 q1 q0 lw'
                   (fun He => Hne' (eq_sym He)) Hm').
        - rewrite Hbase' Hbase. reflexivity. }
      iModIntro.
      iExists sg', es, p2, p1, lw.
      iSplitR; [iPureIntro; exact Htrans|].
      iSplitR; [iPureIntro; rewrite Hsg' mdev_set_reg; reflexivity|].
      iSplitR; [iPureIntro; right; eexists; rewrite Hsg' sregs_set_reg; reflexivity|].
      iSplitR; [iPureIntro; exists a0, d0; reflexivity|].
      iSplitR; [iPureIntro; rewrite -Ha2; auto|].
      iSplitR; [iPureIntro; rewrite -Ha2; exact Hpin|].
      iSplitR; [iPureIntro; exact Hcoll|].
      rewrite Hsg' sregs_set_reg. iFrame "Hri".
      iSplitL "Hsatp Htlb Hpc Hpa".
      { iApply (wtlb_res_pt_intro root_ppn T_kpt satp0 _ (ptree_set_leaf t vpn lw')
                  Hmode Hasid Hppn Htlbok' with "Hsatp Htlb Hlb' [Hpc Hpa] Hkinv").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA Hord HX HW HR Hcov with "Hpc Hpa"). }
      iRight. iExists (lw' : mword 64), _.
      iSplitR; [iPureIntro; exact Hupd|].
      iSplitR; [iPureIntro; rewrite mem_set_reg /=; reflexivity|].
      iSplitR; [iPureIntro; exact Hes|].
      iFrame "Hla Hi".
  Qed.

End WeakKptAbsorb.

(* ====================================================================== *)
(** ** 6. Soundness checks *)

Print Assumptions wadm_pte_ad_le_latest_from.
Print Assumptions wkperm_variant_check.
Print Assumptions wptree_translateAddr_eff_cases.
Print Assumptions wtlb_res_pt_translateAddr_at.
