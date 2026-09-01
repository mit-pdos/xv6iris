(* ======================================================================= *)
(*  BioBox: the bcache transit box (Phase 5, A6.142/A6.147).                *)
(*                                                                          *)
(*  The successor to [BioInv.buf_escrow]'s cell-owning invariant.  The      *)
(*  A6.147 measurement: the escrow is never OPENED in the lock-free         *)
(*  windows -- it is storage ACROSS them; every transition happens inside   *)
(*  bcache.lock or b->lock.  So the box holds ONE uniform bundle (the old   *)
(*  [buf_parked] minus the recycle token) at a PARKED context, custodied    *)
(*  by [CtxAnchor.anchor]:                                                  *)
(*                                                                          *)
(*    - deposited at bget's refcnt 0->1 bump (under bcache.lock) and at     *)
(*      brelse's park (under b->lock, before releasesleep);                 *)
(*    - withdrawn at the checkout (the acquiresleep winner, under b->lock)  *)
(*      and at brelse's refcnt 1->0 drop (under bcache.lock, folding the    *)
(*      content back into the payload's refcnt-0 arm).                      *)
(*                                                                          *)
(*  Both arms below are closed propositions (the box context ξb is BOUND),  *)
(*  so [buf_box] is fork-movable -- the whole point (§0.47').               *)
(*                                                                          *)
(*  The guard: the box body carries the deposit's [astamp]/[llb] receipt    *)
(*  persistently; a withdrawer mints its [aguard] by cashing the llb at     *)
(*  its own acquire's drained point (the A6.147-refinement export) and      *)
(*  withdraws with [anchor_withdraw].  Freshness -- the guard's generation  *)
(*  matching the box's -- is by [astamp_agree] against the body's witness.  *)
(* ======================================================================= *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.
Require Import TsoCtxPark.
Require Import CtxAnchor.
Require Import SleepLock.
Require Import BufOwn.
Require Import DiskPtsto.
Require Import BcacheInv.
Require Export BioDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SepThread.
Require Import Xv6G.
Require Import BioInv.

Section BioBox.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !anchorG Σ, !presG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The two box arms, as context-λs                                     *)
  (* ------------------------------------------------------------------ *)

  (* the travelling content: [BioInv.buf_parked] minus [bmid], stated at
     an explicit context.  (bmid dies with the recycle window: the
     recycler works entirely inside bcache.lock's payload now.) *)
  Definition buf_bundle (bn : bio_names) (V : bio_view Σ) (k : nat)
      (ξ : CtxId) : iProp Σ :=
    (∃ (v : bool) (dev bno : mword 32) (bs : list (bv 8)),
       ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
         (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
       ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn (1/2)) dev ∗
       buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
       buf_pay (XI := ξ) bn V k v dev bno bs)%I.

  (* the chain residue: GHOST-ONLY (A6.148 revision).  The checkout's
     dev/blockno fractions stay with the chain thread -- the C code uses
     them -- so the OUT arm is context-free: no anchor traffic to enter
     or leave it, and the park needs no freshness premise. *)
  Definition buf_chain_res (bn : bio_names) (k : nat) : iProp Σ :=
    (∃ q : Qp, bref_tok bn k q ∗ bown bn k)%I.

  (* cross-context exclusivity of a FULL word cell: the bump/park refute
     the PARKED arm with the full valid cell in hand, and the arm's copy
     lives at the (different) box context. *)
  Lemma ctx_word4_excl_x (ξ1 ξ2 : CtxId) (a : Arch.pa) (dq : dfrac)
      (w1 w2 : bv 32) :
    ctx_word4_pointsto ξ1 a (DfracOwn 1) w1 -∗
    ctx_word4_pointsto ξ2 a dq w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as "[%Hal1 H1]". iDestruct "H2" as "[%Hal2 H2]".
    cbn [seq]. rewrite !big_sepL_cons.
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (TsoCtx.ctx_pointsto_ne with "Hb1 Hb2") as %Hne. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The box                                                             *)
  (* ------------------------------------------------------------------ *)

  Definition bioxN : namespace := nroot .@ "xv6biox".

  Definition buf_box_body (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    (∃ (n T : nat) (ξb : CtxId),
       anchor (bn_anc bn k) n ξb T ∗
       astamp (bn_anc bn k) n T ∗
       llb loglen_name T ∗
       (buf_bundle bn V k ξb ∨ buf_chain_res bn k ∨ pres_none bn k))%I.

  Definition buf_box (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    inv bioxN (buf_box_body bn V k).

  (* ------------------------------------------------------------------ *)
  (*  Morphability of the arms (what deposit/withdraw transport)          *)
  (* ------------------------------------------------------------------ *)

  Global Instance buf_bundle_morph bn V k : CtxMorph (buf_bundle bn V k).
  Proof.
    rewrite /buf_bundle. apply ctx_morph_exist => v.
    apply ctx_morph_exist => dev. apply ctx_morph_exist => bno.
    apply ctx_morph_exist => bs.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep.
    - rewrite /buf_own.
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
    - rewrite /buf_pay.
      case_decide; [|apply ctx_morph_const].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      destruct v.
      + apply ctx_morph_exist => bsd. apply ctx_morph_exist => d.
        apply ctx_morph_sep; [apply ctx_morph_const|].
        rewrite /bio_pay. destruct d.
        * apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_exist => q.
          rewrite /bref.
          apply ctx_morph_sep; [apply ctx_morph_const|].
          apply ctx_morph_sep; apply ctx_morph_word4.
        * apply ctx_morph_const.
      + apply ctx_morph_const.
  Qed.


  (* ================================================================== *)
  (*  The four transitions (A6.147's legs), as ghost cores over an opened *)
  (*  [buf_box].  The freshness premise on the two bundle WITHDRAWS is    *)
  (*  the per-site obligation (A6.149 §3): the caller's context floor     *)
  (*  covers the box's CURRENT stamp.                                     *)
  (* ================================================================== *)

  (* refs 0->1, under bcache.lock: content leaves the payload for the box;
     the presence authority comes out for the payload's Some-arm. *)
  Lemma box_swap_bump `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (M : gmap nat (Qp * positive)) (ξ : CtxId) :
    M !! k = None ->
    TsoCtx.own_context ξ -∗
    own (bn_auth bn) (● M) -∗
    buf_bundle bn V k ξ -∗
    buf_box_body bn V k ==∗
    TsoCtx.own_context ξ ∗ own (bn_auth bn) (● M) ∗
    pres_none bn k ∗ buf_box_body bn V k.
  Proof.
    iIntros (HMk) "Hrun Hauth Hbdl Hbody".
    iDestruct "Hbody" as (n T ξb) "(Hanc & #Hst & #Hll & [Harm | [Harm | Harm]])".
    - (* PARKED refuted: two full valid cells *)
      iDestruct "Hbdl" as (v dev bno bs) "(Hv1 & _)".
      iDestruct "Harm" as (v' dev' bno' bs') "(Hv2 & _)".
      iDestruct (ctx_word4_excl_x with "Hv1 Hv2") as %[].
    - (* OUT refuted: a count fragment against the None auth *)
      iDestruct "Harm" as (q) "[Htok _]".
      iDestruct (own_valid_2 with "Hauth Htok") as %Hv. exfalso.
      apply auth_both_valid_discrete in Hv as [Hincl _].
      apply singleton_included_l in Hincl as (y & Hy & _).
      rewrite HMk in Hy. inversion Hy.
    - (* IDLE: deposit; the presence authority comes out *)
      iMod (anchor_deposit (buf_bundle bn V k) (bn_anc bn k) n ξ ξb T
              with "Hrun Hanc Hbdl")
        as "(Hrun & %T' & %HTT' & Hanc & Hbdl & #Hst' & #Hll')".
      iModIntro. iFrame "Hrun Hauth Harm".
      iExists (S n), T', ξb. iFrame "Hanc Hst' Hll'".
      iLeft. iExact "Hbdl".
  Qed.

  (* the checkout, under b->lock: the winner withdraws the bundle and
     leaves its ghost residue.  Guard: floor past the current stamp. *)
  Lemma box_swap_checkout `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) (Kfl : nat) (q : Qp) :
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Kfl -∗
    □ (∀ n T, astamp (bn_anc bn k) n T -∗ ⌜(T <= Kfl)%nat⌝) -∗
    pres_frag bn k -∗
    bref_tok bn k q -∗ bown bn k -∗
    buf_box_body bn V k ==∗
    TsoCtx.own_context ξ ∗ pres_frag bn k ∗
    buf_bundle bn V k ξ ∗ buf_box_body bn V k.
  Proof.
    iIntros "Hrun #Hfl #Hfr Hpf Htok Hown Hbody".
    iDestruct "Hbody" as (n T ξb) "(Hanc & #Hst & #Hll & [Harm | [Harm | Harm]])".
    - (* PARKED: the withdraw *)
      iDestruct ("Hfr" with "Hst") as %HTK.
      iDestruct (aguard_intro (bn_anc bn k) n T ξ Kfl HTK with "Hst Hfl") as "#Hg".
      iMod (anchor_withdraw (buf_bundle bn V k) (bn_anc bn k) n ξ ξb T
              with "Hrun Hg Hanc Harm") as "(Hrun & Hanc & Hbdl)".
      iModIntro. iFrame "Hrun Hpf Hbdl".
      iExists n, T, ξb. iFrame "Hanc Hst Hll".
      iRight. iLeft. iExists q. iFrame "Htok Hown".
    - (* OUT refuted: two checkout tokens *)
      iDestruct "Harm" as (q') "[_ Hown2]".
      iDestruct (bown_exclusive with "Hown Hown2") as %[].
    - (* IDLE refuted: the fragment against the None authority *)
      iDestruct (pres_frag_none_absurd with "Hpf Harm") as %[].
  Qed.

  (* the park, under b->lock, before releasesleep: the chain returns the
     bundle and takes its residue back.  No guard: deposits are free. *)
  Lemma box_swap_park `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (ξ : CtxId) :
    TsoCtx.own_context ξ -∗
    pres_frag bn k -∗
    buf_bundle bn V k ξ -∗
    buf_box_body bn V k ==∗
    TsoCtx.own_context ξ ∗ pres_frag bn k ∗
    (∃ q : Qp, bref_tok bn k q ∗ bown bn k) ∗
    buf_box_body bn V k.
  Proof.
    iIntros "Hrun Hpf Hbdl Hbody".
    iDestruct "Hbody" as (n T ξb) "(Hanc & #Hst & #Hll & [Harm | [Harm | Harm]])".
    - iDestruct "Hbdl" as (v dev bno bs) "(Hv1 & _)".
      iDestruct "Harm" as (v' dev' bno' bs') "(Hv2 & _)".
      iDestruct (ctx_word4_excl_x with "Hv1 Hv2") as %[].
    - (* OUT: the swap *)
      iMod (anchor_deposit (buf_bundle bn V k) (bn_anc bn k) n ξ ξb T
              with "Hrun Hanc Hbdl")
        as "(Hrun & %T' & %HTT' & Hanc & Hbdl & #Hst' & #Hll')".
      iModIntro. iFrame "Hrun Hpf Harm".
      iExists (S n), T', ξb. iFrame "Hanc Hst' Hll'".
      iLeft. iExact "Hbdl".
    - iDestruct (pres_frag_none_absurd with "Hpf Harm") as %[].
  Qed.

  (* refs 1->0, under bcache.lock: the content folds back into the
     payload; the presence authority returns to the box. *)
  Lemma box_swap_drop `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ)
      (k : nat) (M : gmap nat (Qp * positive)) (ξ : CtxId) (Kfl : nat)
      (q : Qp) :
    M !! k = Some (q, 1%positive) ->
    TsoCtx.own_context ξ -∗
    TsoCtx.ctx_floor ξ Kfl -∗
    □ (∀ n T, astamp (bn_anc bn k) n T -∗ ⌜(T <= Kfl)%nat⌝) -∗
    own (bn_auth bn) (● M) -∗
    bref_tok bn k q -∗
    pres_auth bn k 1%positive -∗ pres_frag bn k -∗
    buf_box_body bn V k ==∗
    TsoCtx.own_context ξ ∗ own (bn_auth bn) (● M) ∗ bref_tok bn k q ∗
    buf_bundle bn V k ξ ∗ buf_box_body bn V k.
  Proof.
    iIntros (HMk) "Hrun #Hfl #Hfr Hauth Htok Hpa Hpf Hbody".
    iDestruct "Hbody" as (n T ξb) "(Hanc & #Hst & #Hll & [Harm | [Harm | Harm]])".
    - (* PARKED: the withdraw + the presence fold *)
      iDestruct ("Hfr" with "Hst") as %HTK.
      iDestruct (aguard_intro (bn_anc bn k) n T ξ Kfl HTK with "Hst Hfl") as "#Hg".
      iMod (anchor_withdraw (buf_bundle bn V k) (bn_anc bn k) n ξ ξb T
              with "Hrun Hg Hanc Harm") as "(Hrun & Hanc & Hbdl)".
      iMod (pres_last_drop with "Hpa Hpf") as "Hpn".
      iModIntro. iFrame "Hrun Hauth Htok Hbdl".
      iExists n, T, ξb. iFrame "Hanc Hst Hll".
      iRight. iRight. iExact "Hpn".
    - (* OUT refuted: the count overflows *)
      iDestruct "Harm" as (q') "[Htok2 _]".
      iCombine "Htok Htok2" as "Htoks".
      iDestruct (own_valid_2 with "Hauth Htoks")
        as %[Hincl _]%auth_both_valid_discrete. exfalso.
      apply singleton_included_l in Hincl as (y & Hy & Hle).
      apply leibniz_equiv in Hy. rewrite HMk in Hy.
      injection Hy as <-.
      apply Some_included in Hle as [Heq | Hlt].
      + destruct Heq as [_ Hn]; cbn in Hn.
        apply leibniz_equiv in Hn. discriminate.
      + apply pair_included in Hlt as [_ Hp].
        apply pos_included in Hp. lia.
    - (* IDLE refuted: two authorities *)
      iDestruct (pres_auth_auth_absurd with "Hpa Harm") as %[].
  Qed.

  (* ================================================================== *)
  (*  The payload side (v2, A6.142): refs-0 custody in bcache.lock.       *)
  (*  Stated as context-λs -- the lock payload re-indexes at each acquire. *)
  (* ================================================================== *)

  Definition bio_slot_res2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (k : nat) (dev bno : mword 32)
      (ξ : CtxId) : iProp Σ :=
    match M !! k with
    | None =>
        (ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1) (mword_of_int 0 : mword 32) ∗
         (∃ (v : bool) (bs : list (bv 8)),
            ctx_word4_pointsto ξ (b_valid (bpa k)) (DfracOwn 1)
              (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)) ∗
            ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn 1) dev ∗
            buf_own (XI := ξ) (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
            ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn (1/2)) bno ∗
            buf_pay (XI := ξ) bn V k v dev bno bs))%I
    | Some (q, n) =>
        (⌜(Z.pos n < 2 ^ 31)%Z⌝ ∗
         ctx_word4_pointsto ξ (brefcnt k) (DfracOwn 1)
           (mword_of_int (Z.pos n) : mword 32) ∗
         bslots (Pos.to_nat n) ∗
         pres_auth bn k n ∗
         ∃ qr : Qp, ⌜(q + qr)%Qp = (1/2)%Qp⌝ ∗
           ctx_word4_pointsto ξ (b_dev (bpa k)) (DfracOwn qr) dev ∗
           ctx_word4_pointsto ξ (b_blockno (bpa k)) (DfracOwn qr) bno)%I
    end.

  Definition bcache_scan2 (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (ord : list nat)
      (devs bnos : nat -> mword 32) (ξ : CtxId) : iProp Σ :=
    (own (bn_auth bn) (● M) ∗
     bslots_auth ∗
     ⌜∀ k, is_Some (M !! k) -> (k < NBUF)%nat⌝ ∗
     ⌜ord ≡ₚ seq 0 NBUF⌝ ∗
     ⌜∀ k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
        uint (bnos k1) ∈ bv_cov V ->
        uint (bnos k1) = uint (bnos k2) -> k1 = k2⌝ ∗
     ⌜∀ k, (k < NBUF)%nat -> uint (bnos k) ∈ bv_cov V ->
        devs k = bv_dev V⌝ ∗
     bcache_lru (XI := ξ) bhead (map bnode ord) ∗
     bio_pool V bnos ∗
     [∗ list] k ∈ seq 0 NBUF, bio_slot_res2 bn V M k (devs k) (bnos k) ξ)%I.

  Definition bcache_res2 (bn : bio_names) (V : bio_view Σ) (ξ : CtxId) : iProp Σ :=
    (∃ (M : gmap nat (Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32),
       bcache_scan2 bn V M ord devs bnos ξ)%I.

  (* ---- morphability ------------------------------------------------- *)

  Lemma bseg_morph (h : mword 64) :
    forall (l : list (mword 64)) (prev : mword 64),
      CtxMorph (fun ξ => bseg (XI := ξ) h prev l).
  Proof.
    induction l as [|a l' IH]; intros prev; cbn [bseg].
    - apply ctx_morph_const.
    - apply ctx_morph_sep; [apply ctx_morph_word|].
      apply ctx_morph_sep; [apply ctx_morph_word|].
      apply IH.
  Qed.

  Global Instance bcache_lru_morph h l :
    CtxMorph (fun ξ => bcache_lru (XI := ξ) h l).
  Proof.
    rewrite /bcache_lru.
    apply ctx_morph_sep; [apply ctx_morph_word|].
    apply ctx_morph_sep; [apply ctx_morph_word|].
    apply bseg_morph.
  Qed.

  Local Instance buf_pay_morph bn V k v dev bno bs :
    CtxMorph (fun ξ => buf_pay (XI := ξ) bn V k v dev bno bs).
  Proof.
    rewrite /buf_pay.
    case_decide; [|apply ctx_morph_const].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    destruct v.
    - apply ctx_morph_exist => bsd. apply ctx_morph_exist => d.
      apply ctx_morph_sep; [apply ctx_morph_const|].
      rewrite /bio_pay. destruct d.
      + apply ctx_morph_sep; [apply ctx_morph_const|].
        apply ctx_morph_exist => q.
        rewrite /bref.
        apply ctx_morph_sep; [apply ctx_morph_const|].
        apply ctx_morph_sep; apply ctx_morph_word4.
      + apply ctx_morph_const.
    - apply ctx_morph_const.
  Qed.

  Local Instance buf_own_morph b bno dsk bs :
    CtxMorph (fun ξ => buf_own (XI := ξ) b bno dsk bs).
  Proof.
    rewrite /buf_own.
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_word4|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepL. intros i x. apply ctx_morph_pointsto.
  Qed.

  Global Instance bio_slot_res2_morph bn V M k dev bno :
    CtxMorph (bio_slot_res2 bn V M k dev bno).
  Proof.
    rewrite /bio_slot_res2.
    destruct (M !! k) as [[q n]|].
    - apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_exist => qr.
      apply ctx_morph_sep; [apply ctx_morph_const|].
      apply ctx_morph_sep; apply ctx_morph_word4.
    - apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_exist => v. apply ctx_morph_exist => bs.
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply ctx_morph_sep; [apply buf_own_morph|].
      apply ctx_morph_sep; [apply ctx_morph_word4|].
      apply buf_pay_morph.
  Qed.

  Global Instance bcache_res2_morph bn V : CtxMorph (bcache_res2 bn V).
  Proof.
    rewrite /bcache_res2.
    apply ctx_morph_exist => M. apply ctx_morph_exist => ord.
    apply ctx_morph_exist => devs. apply ctx_morph_exist => bnos.
    rewrite /bcache_scan2.
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_sep; [apply bcache_lru_morph|].
    apply ctx_morph_sep; [apply ctx_morph_const|].
    apply ctx_morph_big_sepL. intros i x. apply bio_slot_res2_morph.
  Qed.

End BioBox.
