(* HartMemRunX.v -- THE PAYLOAD-INDEXED BYTE MAP AND THE WALKER'S COROLLARY
   (claude-notes/projects/icache.md, "The verified tier: text OUTSIDE the
   walker").

   A verified process holds its TEXT as stamped bytes
   ([TsoCtx.ctx_phys_xpointsto ξ IK a 1 b]: latest write at or below the
   instruction-view position [IK]) and everything else as plain
   [ctx_phys_pointsto] bytes -- one map, one big-op, the payload chosen per
   address by [F : Arch.pa -> option nat].  The walker never sees a stamped
   byte: [swp_hmrun_of_exec_p] runs [HartMemRun.swp_hmrun_of_exec] on the
   UNSTAMPED submap ([goodmb] certifies against that submap's domain, so a
   walk that reads or writes a stamped byte simply has no certificate) and
   frames the stamped submap around it.  So a stamp survives every walk by
   construction, and [swp_hmrun] itself does not move.

   Why not a payload that rides THROUGH the walker: the walker's pure
   interface bounds a walk's writes by the map's domain and nothing finer,
   and no endpoint-only post can say a text byte was not written and
   written back (see the project note).                                    *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import TsoMemPa.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents.
Require Import TsoCtx HartMemRun.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. The two submaps of a payload-indexed map.                            *)
(* ===================================================================== *)

Definition uf_none (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    : gmap Arch.pa (bv 8) :=
  filter (fun kv : Arch.pa * bv 8 => F kv.1 = None) mm.

Definition uf_some (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    : gmap Arch.pa (bv 8) :=
  filter (fun kv : Arch.pa * bv 8 => ~ (F kv.1 = None)) mm.

Lemma uf_union (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  uf_none F mm ∪ uf_some F mm = mm.
Proof. apply map_filter_union_complement. Qed.

Lemma uf_disj (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  uf_none F mm ##ₘ uf_some F mm.
Proof. apply map_disjoint_filter_complement. Qed.

Lemma uf_none_sub (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  uf_none F mm ⊆ mm.
Proof. apply map_filter_subseteq. Qed.

Lemma uf_some_sub (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  uf_some F mm ⊆ mm.
Proof. apply map_filter_subseteq. Qed.

Lemma uf_none_lookup (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    (a : Arch.pa) (b : bv 8) :
  uf_none F mm !! a = Some b <-> mm !! a = Some b /\ F a = None.
Proof. rewrite /uf_none map_lookup_filter_Some. reflexivity. Qed.

Lemma uf_some_lookup (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    (a : Arch.pa) (b : bv 8) :
  uf_some F mm !! a = Some b <-> mm !! a = Some b /\ ~ (F a = None).
Proof. rewrite /uf_some map_lookup_filter_Some. reflexivity. Qed.

Lemma uf_none_dom (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    (a : Arch.pa) :
  a ∈ dom (uf_none F mm) <-> a ∈ dom mm /\ F a = None.
Proof.
  rewrite !elem_of_dom. split.
  - intros [b Hb]. apply uf_none_lookup in Hb as [Hb HF]. split; [by exists b | exact HF].
  - intros [[b Hb] HF]. exists b. apply uf_none_lookup. by split.
Qed.

Lemma uf_some_dom (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8))
    (a : Arch.pa) :
  a ∈ dom (uf_some F mm) <-> a ∈ dom mm /\ ~ (F a = None).
Proof.
  rewrite !elem_of_dom. split.
  - intros [b Hb]. apply uf_some_lookup in Hb as [Hb HF]. split; [by exists b | exact HF].
  - intros [[b Hb] HF]. exists b. apply uf_some_lookup. by split.
Qed.

(* the unstamped submap's domain is a function of the domain *)
Lemma uf_none_dom_eq (F : Arch.pa -> option nat) (mm1 mm2 : gmap Arch.pa (bv 8)) :
  (dom mm1 : gset Arch.pa) = dom mm2 ->
  (dom (uf_none F mm1) : gset Arch.pa) = dom (uf_none F mm2).
Proof.
  intros Hd. apply set_eq. intros a.
  rewrite !uf_none_dom Hd. reflexivity.
Qed.

(* a map whose every key is unstamped IS its own unstamped submap *)
Lemma uf_none_all (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  (forall a, a ∈ dom mm -> F a = None) -> uf_none F mm = mm.
Proof.
  intros HF. apply map_eq. intros a.
  destruct (mm !! a) as [b|] eqn:Hb.
  - apply uf_none_lookup. split; [exact Hb |]. apply HF. by apply elem_of_dom.
  - apply map_lookup_filter_None. by left.
Qed.

(* ... and a map whose every key is unstamped has NO stamped submap *)
Lemma uf_some_empty (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
  (forall a, a ∈ dom mm -> F a = None) -> uf_some F mm = ∅.
Proof.
  intros HF. apply map_eq. intros a. rewrite lookup_empty.
  apply map_lookup_filter_None.
  destruct (mm !! a) as [b|] eqn:Hb; [right | by left].
  intros b' Hb'. injection Hb' as <-. cbn.
  intros Hn. apply Hn. apply HF. by apply elem_of_dom.
Qed.

(* ===================================================================== *)
(* 2. The payload-indexed byte map.                                        *)
(* ===================================================================== *)

Definition xbyte `{!riscvGS Σ} `{XI : TsoCtx.CurCtx} (o : option nat)
    (a : Arch.pa) (b : bv 8) : iProp Σ :=
  match o with
  | None => TsoCtx.ctx_phys_pointsto XI a (DfracOwn 1) b
  | Some IK => TsoCtx.ctx_phys_xpointsto XI IK a (DfracOwn 1) b
  end.

Definition bytes_own_p `{!riscvGS Σ} `{XI : TsoCtx.CurCtx}
    (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) : iProp Σ :=
  ([∗ map] a ↦ b ∈ mm, xbyte (F a) a b)%I.

Section bytes_own_p_facts.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma bytes_own_p_none (mm : gmap Arch.pa (bv 8)) :
    bytes_own_p (fun _ => None) mm ⊣⊢ bytes_own mm.
  Proof. reflexivity. Qed.

  (* every key unstamped: the plain map *)
  Lemma bytes_own_p_of_none (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    (forall a, a ∈ dom mm -> F a = None) ->
    bytes_own_p F mm ⊣⊢ bytes_own mm.
  Proof.
    intros HF. rewrite /bytes_own_p /bytes_own.
    apply big_sepM_proper. intros a b Hb.
    rewrite (HF a); [reflexivity |]. by apply elem_of_dom.
  Qed.

  (* the payload function matters pointwise only *)
  Lemma bytes_own_p_ext (F F' : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    (forall a, F a = F' a) -> bytes_own_p F mm ⊣⊢ bytes_own_p F' mm.
  Proof.
    intros HF. rewrite /bytes_own_p. apply big_sepM_proper. intros a b _.
    rewrite (HF a). reflexivity.
  Qed.

  Lemma bytes_own_p_union (F : Arch.pa -> option nat) (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 ->
    bytes_own_p F (m1 ∪ m2) ⊣⊢ bytes_own_p F m1 ∗ bytes_own_p F m2.
  Proof. intros Hd. rewrite /bytes_own_p. by apply big_sepM_union. Qed.

  (* THE SPLIT: the unstamped submap as a plain [bytes_own], the stamped
     one framed *)
  Lemma bytes_own_p_split (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    bytes_own_p F mm ⊣⊢ bytes_own (uf_none F mm) ∗ bytes_own_p F (uf_some F mm).
  Proof.
    rewrite -{1}(uf_union F mm) (bytes_own_p_union F _ _ (uf_disj F mm)).
    rewrite (bytes_own_p_of_none F (uf_none F mm)); [reflexivity |].
    intros a Ha. by apply uf_none_dom in Ha as [_ HF].
  Qed.

  (* ... and the JOIN after the unstamped half was walked to [mm1], a map
     of the same domain *)
  Lemma bytes_own_p_join (F : Arch.pa -> option nat)
      (mm mm1 : gmap Arch.pa (bv 8)) :
    (dom mm1 : gset Arch.pa) = dom (uf_none F mm) ->
    bytes_own mm1 -∗ bytes_own_p F (uf_some F mm) -∗
    bytes_own_p F (mm1 ∪ uf_some F mm).
  Proof.
    intros Hdom. iIntros "H1 H2".
    assert (Hd : mm1 ##ₘ uf_some F mm).
    { apply map_disjoint_dom. rewrite Hdom. apply map_disjoint_dom.
      apply uf_disj. }
    rewrite (bytes_own_p_union F _ _ Hd).
    iFrame "H2".
    rewrite (bytes_own_p_of_none F mm1); [iFrame "H1" |].
    intros a Ha. rewrite Hdom in Ha. by apply uf_none_dom in Ha as [_ HF].
  Qed.

  Lemma bytes_own_p_forget (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    bytes_own_p F mm ⊢ bytes_own mm.
  Proof.
    rewrite /bytes_own_p /bytes_own. apply big_sepM_mono. intros a b _.
    rewrite /xbyte. destruct (F a) as [IK|]; [apply ctx_phys_xpointsto_forget | done].
  Qed.

  (* the stamps only ever move UP, with the instruction view *)
  Lemma bytes_own_p_mono (F F' : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    (forall a IK, F a = Some IK -> exists IK', F' a = Some IK' /\ (IK <= IK')%nat) ->
    (forall a, F a = None -> F' a = None) ->
    bytes_own_p F mm ⊢ bytes_own_p F' mm.
  Proof.
    intros Hs Hn. rewrite /bytes_own_p. apply big_sepM_mono. intros a b _.
    rewrite /xbyte. destruct (F a) as [IK|] eqn:HF.
    - destruct (Hs a IK HF) as (IK' & -> & Hle). by apply ctx_phys_xpointsto_mono.
    - rewrite (Hn a HF). done.
  Qed.

  (* THE FETCH PAYER: a window of stamped bytes reads its value through the
     icache agent at every view from the instruction view up, once that
     view has passed the stamp -- [HartMFetch.fobl_ifetch]'s shape, at the
     leaf's currency ([tso_interp_of]), so that a read node's interp wand can
     discharge it directly.  [TsoCtx.ctx_phys_xfetch_ok] byte by byte. *)
  Lemma bytes_own_p_ifetch_of (img mem : gmap Arch.pa (bv 8))
      (log : list pwmsg) (V : agent -> nat) (rs : regstate) (d : dev_state)
      (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) (IK : nat)
      (pa : Arch.pa) (n : N) (w : bv (8 * n)) :
    (forall j : nat, (N.of_nat j < n)%N ->
       mm !! pa_add pa j = Some (nth_byte w j) /\ F (pa_add pa j) = Some IK) ->
    gen_heap_interp (hG := riscv_memGS) mem -∗
    tso_interp_of riscv_eraGS img mem log V -∗
    bytes_own_p F mm -∗
    ⌜forall itv tv' : nat, (IK <= itv)%nat -> (itv <= tv')%nat ->
       tso_read_bytes img log (ifetch_agent (hart_agent cpu_id)) tv' pa n w⌝.
  Proof.
    intros Hwin. iIntros "Hgh Htso Hown".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    rewrite (tso_interp_of_at_gs riscv_eraGS img mem log V rs d Hpin).
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall itv tv' : nat, (IK <= itv)%nat -> (itv <= tv')%nat ->
                 tso_read img log (ifetch_agent (hart_agent cpu_id)) tv'
                   (pa_add pa j) = Some (nth_byte w j)⌝)%I
      with "[Hgh Htso Hown]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      rewrite bi.pure_forall. iIntros (itv). rewrite bi.pure_forall. iIntros (tv').
      rewrite bi.pure_impl. iIntros (HIK). rewrite bi.pure_impl. iIntros (Htv).
      destruct (Hwin j Hj) as [Hmm HF].
      rewrite /bytes_own_p.
      iDestruct (big_sepM_lookup _ _ _ _ Hmm with "Hown") as "Ha".
      rewrite /xbyte HF.
      iDestruct (TsoCtx.ctx_phys_xfetch_ok (gs_of img mem log V rs d) XI IK itv
                   (pa_add pa j) (DfracOwn 1) (nth_byte w j) HIK
                   with "Hgh Htso Ha") as %Hrd.
      iPureIntro. cbn [gimg glog gs_of] in Hrd. exact (Hrd tv' Htv). }
    iPureIntro. intros itv tv' HIK Htv j Hj. exact (HH j Hj itv tv' HIK Htv).
  Qed.

End bytes_own_p_facts.

(* ===================================================================== *)
(* 3. THE WALKER'S COROLLARY.  [HartMemRun.swp_hmrun_of_exec] on the       *)
(* unstamped submap, the stamped submap framed.  The certificate is at the  *)
(* unstamped submap -- that is the whole content of the rule -- and the     *)
(* stamped bytes are asked to still be in the landing state's memory,       *)
(* which a caller has for free (its image is literally the same map).      *)
(* ===================================================================== *)
Section memrun_exec_p.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_hmrun_of_exec_p (Dr Dw : register -> bool) (Drw Dro : gset register)
      (Df : register -> dfrac) {X : Type} (m : M X) (s s' : mstate) (x : X)
      (rs : regstate) (F : Arch.pa -> option nat) (mm : gmap Arch.pa (bv 8)) :
    Drw ## Dro ->
    (forall r, Dr r = true -> r ∈ Drw ∪ Dro) ->
    (forall r, Dw r = true -> r ∈ Drw) ->
    reg_agree_on (Drw ∪ Dro) rs s.(sregs) ->
    uf_none F mm ⊆ s.(mem) ->
    goodmb Dr Dw m s (uf_none F mm) = true ->
    exec m s = Some (x, s') ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    TsoCtx.own_context XI -∗
    bytes_own_p F mm -∗
    swp m (fun v => ⌜v = x⌝ ∗
             ∃ (rs' : regstate) (mm1 : gmap Arch.pa (bv 8)),
               ⌜reg_agree_on (Drw ∪ Dro) rs' s'.(sregs)⌝ ∗
               ⌜mm1 ⊆ s'.(mem)⌝ ∗ ⌜dom mm1 = dom (uf_none F mm)⌝ ∗
               hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗
               TsoCtx.own_context XI ∗
               bytes_own_p F (mm1 ∪ uf_some F mm) ∗ resv_any cpu_id).
  Proof.
    intros Hdisj Hdr Hdw Hag Hsub Hg He.
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    rewrite bytes_own_p_split. iDestruct "Hown" as "[Hown Hx]".
    iApply (swp_mono with "[Hx] [Hany Hrw Hro Hrun Hown]").
    2:{ iApply (swp_hmrun_of_exec Dr Dw Drw Dro Df m s s' x rs (uf_none F mm)
                  Hdisj Hdr Hdw Hag Hsub Hg He
                  with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost"
      as (rs2 mm2) "(%Hag2 & %Hsub2 & %Hdom2 & Hrw & Hro & Hrun & Hown & Hany)".
    iSplitR; [done|].
    iExists rs2, mm2.
    iDestruct (bytes_own_p_join F mm mm2 Hdom2 with "Hown Hx") as "Hown".
    iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!; [exact Hag2 | exact Hsub2 | exact Hdom2].
  Qed.

  (* the join's domain, for the callers that pin the landing map *)
  Lemma uf_join_dom (F : Arch.pa -> option nat) (mm mm1 : gmap Arch.pa (bv 8)) :
    (dom mm1 : gset Arch.pa) = dom (uf_none F mm) ->
    (dom (mm1 ∪ uf_some F mm) : gset Arch.pa) = dom mm.
  Proof. intros Hd. rewrite dom_union_L Hd -dom_union_L uf_union. reflexivity. Qed.

End memrun_exec_p.
