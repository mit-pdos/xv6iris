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
    iIntros "!>" (k j Hkj) "H". by iExists (S (length g.(glog))).
  Qed.

End CtxPinw.
