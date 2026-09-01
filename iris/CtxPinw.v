(* CtxPinw.v -- A6.143's STORE ROUTE: the word-set pin's member store.

   The rpay author-store pattern verbatim ([TsoCtx.ledger_store_rel_map_ok]),
   one arm over and SIMPLER: the pinw window's floor and member predicate do
   not move across a member store (rel extends its history; the pinw claim
   is history-free), so the sequence is

     extract the pure [pinw_ok1]s  (they survive the append by
                                    [TsoMemPa.pinw_ok1_app_member])
     drop the arms                 ([TsoCtx.ledger_pinw_drop], to plain
                                    ledger cells)
     the generic at-tier store     ([TsoCtx.ledger_store_win_at_ok] --
                                    no store-gate clone, the whole point)
     re-mint at the SAME window    ([TsoCtx.ledger_pinw_mint1] at the
                                    transported pure claim).

   WHY ITS OWN FILE: the CtxValues.v/CtxPinMint.v precedent -- everything
   here is off TsoCtx's public exports, so TsoCtx (under the whole tree)
   is not rebuilt. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost TsoCtx.
Require Import RiscvExec.  (* [tso_interp_of]/[gs_of]/[vstep]: the leaf-
   obligation face of the member store ([pinw_write_c] below) *)

Local Open Scope Z_scope.

(* the wrap-cancel chain, copied Local-for-Local from TsoCtx.v (they are
   [Local] there and this file cannot see them) *)
Local Lemma cpw_add_vec_unsigned (a b : SailStdpp.Values.mword 64) :
  bv_unsigned (add_vec a b)
  = bv_wrap 64 (bv_unsigned a + bv_unsigned b).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Local Lemma cpw_moi_unsigned (k : Z) :
  bv_unsigned (SailStdpp.Values.mword_of_int k : SailStdpp.Values.mword 64)
  = bv_wrap 64 k.
Proof.
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Local Lemma cpw_pa_add_unsigned (a : Arch.pa) (j : nat) :
  bv_unsigned (pa_add a j : SailStdpp.Values.mword 64)
  = bv_wrap 64 (bv_unsigned (a : SailStdpp.Values.mword 64) + Z.of_nat j).
Proof.
  unfold pa_add, add_vec_int.
  rewrite cpw_add_vec_unsigned cpw_moi_unsigned bv_wrap_add_idemp_r.
  reflexivity.
Qed.

Local Lemma cpw_mod64 : bv_modulus 64 = 18446744073709551616%Z.
Proof. vm_compute. reflexivity. Qed.

Local Lemma cpw_wrap_cancel (u i j : Z) :
  (0 <= i < 18446744073709551616)%Z -> (0 <= j < 18446744073709551616)%Z ->
  ((u + i) `mod` 18446744073709551616 = (u + j) `mod` 18446744073709551616)%Z ->
  i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hd : ((i - j) `mod` 18446744073709551616 = 0)%Z).
  { replace (i - j)%Z with ((u + i) - (u + j))%Z by lia.
    rewrite Zminus_mod Heq Z.sub_diag. reflexivity. }
  apply Z.mod_divide in Hd; [| lia ].
  destruct Hd as [k Hk]. nia.
Qed.

Local Lemma cpw_pa_add_inj (a : Arch.pa) (i j : nat) :
  (Z.of_nat i < 18446744073709551616)%Z ->
  (Z.of_nat j < 18446744073709551616)%Z ->
  pa_add a i = pa_add a j -> i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hu : bv_unsigned (pa_add a i : SailStdpp.Values.mword 64)
               = bv_unsigned (pa_add a j : SailStdpp.Values.mword 64))
    by (by rewrite Heq).
  rewrite !cpw_pa_add_unsigned in Hu. unfold bv_wrap in Hu.
  rewrite cpw_mod64 in Hu.
  assert (Hz : Z.of_nat i = Z.of_nat j)
    by (apply (cpw_wrap_cancel (bv_unsigned (a : SailStdpp.Values.mword 64)));
        [ lia | lia | exact Hu ]).
  lia.
Qed.

Section CtxPinw.
  Context `{!riscvGS Σ}.

  (* ---- the runs over a list of offsets (the rpay runs, one arm over) --- *)

  Local Lemma ledger_pinw_mint_run (g : gstate) (base : Arch.pa)
      (f : nat -> bv 8) (tf : nat -> nat) (Wf : nat -> ts_pinw)
      (l : list nat) :
    (forall j, j ∈ l -> pinw_ok1 g.(gimg) g.(glog) (pa_add base j) (Wf j)) ->
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ l, phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) (tf j)) ==∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ l,
       phys_ledger_pinw (pa_add base j) (DfracOwn 1) (f j) (tf j) (Wf j)).
  Proof.
    induction l as [|j l IH]; intros Hok.
    - iIntros "Hint _". iModIntro. iFrame "Hint". done.
    - iIntros "Hint Hb".
      rewrite !big_sepL_cons. iDestruct "Hb" as "[Hbj Hbl]".
      assert (Hj : j ∈ j :: l) by set_solver.
      iMod (ledger_pinw_mint1 g (pa_add base j) (f j) (tf j) (Wf j) (Hok j Hj)
              with "Hint Hbj") as "(Hint & Hbj)".
      assert (Hok' : forall k, k ∈ l ->
                pinw_ok1 g.(gimg) g.(glog) (pa_add base k) (Wf k))
        by (intros k Hk; apply Hok; set_solver).
      iMod (IH Hok' with "Hint Hbl") as "(Hint & Hbl)".
      iModIntro. iFrame "Hint Hbj Hbl".
  Qed.

  Local Lemma ledger_pinw_drop_run (g : gstate) (base : Arch.pa)
      (f : nat -> bv 8) (Wf : nat -> ts_pinw) (l : list nat) :
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ l, ∃ t : nat,
       phys_ledger_pinw (pa_add base j) (DfracOwn 1) (f j) t (Wf j)) ==∗
    tso_interp_at riscv_eraGS g ∗
    ([∗ list] j ∈ l, phys_ledger (pa_add base j) (DfracOwn 1) (f j)).
  Proof.
    induction l as [|j l IH].
    - iIntros "Hint _". iModIntro. iFrame "Hint". done.
    - iIntros "Hint Hb".
      rewrite !big_sepL_cons. iDestruct "Hb" as "[(%t & Hbj) Hbl]".
      iMod (ledger_pinw_drop g (pa_add base j) (f j) t (Wf j) with "Hint Hbj")
        as "(Hint & Hbj)".
      iMod (IH with "Hint Hbl") as "(Hint & Hbl)".
      iModIntro. iFrame "Hint Hbl". by iApply phys_ledger_at_ledger.
  Qed.

  (* ---- THE MEMBER STORE: the window's cells ride the append and come
     back pinned at the SAME floor and member predicate ---- *)
  Lemma ledger_store_pinw_ok `{CID : CpuId} (g g' : gstate)
      (base : Arch.pa) (n : N) {m : N} (vold vnew : bv m)
      (lo : nat) (Sw : (nat -> bv 8) -> Prop) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    Sw (nth_byte vnew) ->
    g'.(gimg) = g.(gimg) ->
    g'.(glog) = (g.(glog) ++
                 [TsoMemPa.PWMsg (snap_of base n vnew)
                    (hart_agent cpu_id)])%list ->
    g'.(gmem) = write_bytes g.(gmem) base n vnew ->
    (forall c : CPU, (g.(gtv) c <= g'.(gtv) c)%nat) ->
    (forall c : CPU, (g'.(gtv) c <= length g'.(glog))%nat) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       phys_ledger_pinw (pa_add base j) (DfracOwn 1) (nth_byte vold j) t
         (TsPinw base (N.to_nat n) j lo Sw)) ==∗
    gen_heap_interp (hG := riscv_memGS) g'.(gmem) ∗
    tso_interp_at riscv_eraGS g' ∗
    ledger_msg_at (length g.(glog))
      (TsoMemPa.PWMsg (snap_of base n vnew) (hart_agent cpu_id)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       ⌜(t <= length g'.(glog))%nat⌝ ∗
       phys_ledger_pinw (pa_add base j) (DfracOwn 1) (nth_byte vnew j) t
         (TsPinw base (N.to_nat n) j lo Sw)).
  Proof.
    intros Hn HSw Himg Hlog Hmem Htv Htvok'.
    iIntros "Hgh Hint Hpw".
    (* the pure claims, pre-append *)
    iAssert (⌜forall j, (j < N.to_nat n)%nat ->
               pinw_ok1 g.(gimg) g.(glog) (pa_add base j)
                 (TsPinw base (N.to_nat n) j lo Sw)⌝)%I as %Hcov.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hpw")
        as (tj) "Hej".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_pinw_ok g (pa_add base j) (DfracOwn 1) (nth_byte vold j)
                tj _ with "Hint Hej"). }
    (* the message's window bytes *)
    assert (Hsnap : forall j : nat, (j < N.to_nat n)%nat ->
              TsoMemPa.msg_byte
                (TsoMemPa.PWMsg (snap_of base n vnew) (hart_agent cpu_id))
                (pa_add base j)
              = Some (nth_byte vnew j)).
    { intros j Hj. rewrite /TsoMemPa.msg_byte /=.
      assert (Hin : pa_add base j ∈ dom (snap_of base n vnew)).
      { rewrite dom_snap_of. apply elem_of_footprint. exists j.
        split; [lia | reflexivity]. }
      apply elem_of_dom in Hin as [b Hb].
      destruct (snap_of_lookup_Some _ _ _ _ _ Hb) as (j' & Hj' & Heq & ->).
      assert (Hjj : j = j')
        by (apply (cpw_pa_add_inj base j j'); [lia | lia | exact Heq]).
      subst j'. exact Hb. }
    (* drop the arms *)
    iMod (ledger_pinw_drop_run g base (nth_byte vold)
            (fun j => TsPinw base (N.to_nat n) j lo Sw) (seq 0 (N.to_nat n))
            with "Hint Hpw") as "(Hint & Hwin)".
    (* the generic at-tier store *)
    iMod (ledger_store_win_at_ok g g' base n vold vnew Hn Himg Hlog Hmem
            Htv Htvok' with "Hgh Hint Hwin") as "($ & Hint & $ & Hnew)".
    (* re-mint at the same window: the pure claims survive the append *)
    iMod (ledger_pinw_mint_run g' base (nth_byte vnew)
            (fun _ => S (length g.(glog)))
            (fun j => TsPinw base (N.to_nat n) j lo Sw) (seq 0 (N.to_nat n))
            with "Hint Hnew") as "(Hint & Hnew)".
    { intros j Hj. apply elem_of_seq in Hj.
      rewrite Hlog Himg.
      apply (pinw_ok1_app_member g.(gimg) g.(glog)
               (TsoMemPa.PWMsg (snap_of base n vnew) (hart_agent cpu_id))
               (pa_add base j) (TsPinw base (N.to_nat n) j lo Sw)
               (nth_byte vnew)).
      - apply Hcov. lia.
      - exact HSw.
      - intros k Hk. cbn in Hk. exact (Hsnap k Hk). }
    iModIntro. iFrame "Hint".
    iApply (big_sepL_impl with "Hnew").
    iIntros "!>" (k j Hkj) "H". iExists (S (length g.(glog))).
    iFrame "H". iPureIntro. rewrite Hlog length_app /=. lia.
  Qed.

  (* ---- THE EXACT READ, for a receipt that covers the stamps: a LOCK
     HOLDER's read.  All writes to a pinw window happen under its guarding
     lock; the A6.144 floor row hands the holder [ctx_floor ξ tl] with
     every stamp ≤ tl (the γ-stamp tie), and the cash-in
     ([TsoCtx.own_context_floor_view]) gives the view receipt this lemma
     takes.  Conclusion: the read is the LATEST value, exactly. ---- *)
  Lemma ledger_read_pinw_latest `{CID : CpuId} (g : gstate) (base : Arch.pa)
      (nn tl : nat) (dq : dfrac) (f : nat -> bv 8) (Wf : nat -> ts_pinw) :
    tso_interp_at riscv_eraGS g -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) tl -∗
    ([∗ list] j ∈ seq 0 nn, ∃ t : nat, ⌜(t <= tl)%nat⌝ ∗
       phys_ledger_pinw (pa_add base j) dq (f j) t (Wf j)) -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat -> forall j, (j < nn)%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
       = Some (f j)⌝.
  Proof.
    iIntros "Hint Hgh #Htl Hb".
    iAssert (⌜forall j, (j < nn)%nat -> exists t, (t <= tl)%nat /\
               TsoMemPa.latest g.(gimg) g.(glog) (pa_add base j) t (f j)⌝)%I
      as %Hlat.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 nn) j j with "Hb")
        as (t) "(%Htl' & Hpw)".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      rewrite /phys_ledger_pinw. iDestruct "Hpw" as "[Hpt Hts]".
      iDestruct "Hint"
        as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
      iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
      destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat0).
      cbn in Hlat0.
      rewrite /phys_pointsto. iDestruct "Hpt" as "[Hp %Hram]".
      iDestruct (gen_heap_valid with "Hgh Hp") as %Hgm.
      rewrite Hgm in Hgm0. injection Hgm0 as <-.
      iPureIntro. exists t. split; [exact Htl' | exact Hlat0]. }
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct (view_auth_valid with "Hv Htl") as %Htlv.
    rewrite avf_hart in Htlv.
    iPureIntro. intros tv Htv j Hj.
    destruct (Hlat j Hj) as (t & Htl' & Hl).
    apply (TsoMemPa.tso_read_of_latest _ _ _ _ _ t); [exact Hl|].
    apply TsoMemPa.visibleb_below. lia.
  Qed.

  (* ---- THE LEAF-OBLIGATION FACE (the [wp_store_s_sconf_au_dat] shape):
     the member store at [tso_interp_of], with the vstep bookkeeping done
     here once.  A plain store does not advance the writer's view
     ([vstep] at [V h]); the message and the new top's log-length receipt
     come out for the A6.144 floor row. ---- *)
  Lemma pinw_write_c `{CID : CpuId} (img : bytemap) (σ : mstate)
      (log : list pwmsg) (V : agent -> nat) (pa : Arch.pa)
      {mw : N} (vold vnew : bv mw) (n : N)
      (lo : nat) (Sw : (nat -> bv 8) -> Prop) :
    (Z.of_nat (N.to_nat n) <= 18446744073709551616)%Z ->
    Sw (nth_byte vnew) ->
    gen_heap_interp (hG := riscv_memGS) σ.(mem) -∗
    tso_interp_of riscv_eraGS img σ.(mem) log V -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       phys_ledger_pinw (pa_add pa j) (DfracOwn 1) (nth_byte vold j) t
         (TsPinw pa (N.to_nat n) j lo Sw)) ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes σ.(mem) pa n vnew) ∗
    tso_interp_of riscv_eraGS img (write_bytes σ.(mem) pa n vnew)
      (log ++ [TsoMemPa.PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list
      (vstep (hart_agent cpu_id) (V (hart_agent cpu_id))
         (log ++ [TsoMemPa.PWMsg (snap_of pa n vnew) (hart_agent cpu_id)])%list
         V) ∗
    ledger_msg_at (length log)
      (TsoMemPa.PWMsg (snap_of pa n vnew) (hart_agent cpu_id)) ∗
    TsoGhost.llb loglen_name (S (length log)) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), ∃ t : nat,
       ⌜(t <= S (length log))%nat⌝ ∗
       phys_ledger_pinw (pa_add pa j) (DfracOwn 1) (nth_byte vnew j) t
         (TsPinw pa (N.to_nat n) j lo Sw)).
  Proof.
    intros Hn HSw. iIntros "Hgh Htso Hpw".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    iDestruct (tso_interp_of_bound with "Htso") as %Hb.
    set (msg := TsoMemPa.PWMsg (snap_of pa n vnew) (hart_agent cpu_id)).
    set (log' := (log ++ [msg])%list).
    set (V' := vstep (hart_agent cpu_id) (V (hart_agent cpu_id)) log' V).
    assert (Hlen' : length log' = S (length log))
      by (rewrite /log' length_app /=; lia).
    assert (Hpin' : forall h, (NCPU <= h)%nat -> V' h = length log').
    { intros h Hh. rewrite /V' /vstep. case_decide as Hd.
      - exfalso. subst h. pose proof (fin_to_nat_lt cpu_id).
        rewrite /hart_agent in Hh. lia.
      - destruct (lt_dec h NCPU); [lia | reflexivity]. }
    assert (Htvmono : forall c : CPU,
              (V (hart_agent c) <= V' (hart_agent c))%nat).
    { intros c. rewrite /V' /vstep. case_decide as Hd; [by rewrite Hd | ].
      destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; first reflexivity.
      exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    assert (Htvtop : forall c : CPU,
              (V' (hart_agent c) <= length log')%nat).
    { intros c. rewrite /V' /vstep. case_decide as Hd.
      - pose proof (Hb (hart_agent cpu_id)) as Hb1. lia.
      - destruct (lt_dec (hart_agent c) NCPU).
        + pose proof (Hb (hart_agent c)) as Hb1. lia.
        + lia. }
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log V
               σ.(sregs) σ.(mdev) Hpin).
    iMod (ledger_store_pinw_ok
            (gs_of img σ.(mem) log V σ.(sregs) σ.(mdev))
            (gs_of img (write_bytes σ.(mem) pa n vnew) log' V'
               σ.(sregs) σ.(mdev))
            pa n vold vnew lo Sw Hn HSw eq_refl eq_refl eq_refl
            (fun c => Htvmono c) (fun c => Htvtop c)
            with "Hgh Htso Hpw") as "(Hgh & Htso & #Hmsg & Hpw)".
    iDestruct (tso_interp_loglen_llb with "Htso") as "[Htso #Hllb]".
    cbn [glog gs_of] in *.
    iModIntro.
    rewrite -(tso_interp_of_at_gs riscv_eraGS img
                (write_bytes σ.(mem) pa n vnew) log' V'
                σ.(sregs) σ.(mdev) Hpin').
    iFrame "Hgh Htso Hmsg".
    iSplitR.
    { iApply (TsoGhost.llb_le with "Hllb"). rewrite Hlen'. lia. }
    iApply (big_sepL_impl with "Hpw").
    iIntros "!>" (i j Hij) "H". iDestruct "H" as (t) "[%Ht H]".
    iExists t. iFrame "H". iPureIntro.
    rewrite /log' length_app /= in Ht. lia.
  Qed.

End CtxPinw.
