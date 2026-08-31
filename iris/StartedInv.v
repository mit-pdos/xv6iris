(* StartedInv.v -- the invariant on xv6's [started] flag, the one channel by
   which the boot hart's initialisation reaches the other harts.

     volatile static int started = 0;            // main.c, @ 0x8000a270

     main() {
       if (cpuid() == 0) { ...all the init...; fence; started = 1; }
       else              { while (started == 0) ; fence; ...per-hart init...; }
       scheduler();
     }

   THE SHAPE.  [started] is a plain global written by exactly one hart and read
   by all the others, with no lock -- so its cell cannot be owned by any hart.
   It belongs in an Iris invariant, and the invariant is where the boot hart's
   output is PARKED:

     started_body P  :=  ∃ v, started_addr ↦₄ v ∗ (⌜v = 0⌝ ∨ P)

   Read it as a one-shot escrow keyed on the word: while the word is still 0
   the invariant promises nothing; once it is nonzero the invariant carries
   [P], the boot hart's deposit.  So a hart that READS a nonzero word learns
   [P] ([started_inv_load_au]), and the hart that WRITES the word must pay [P]
   in ([started_inv_store_au]).  That is exactly the C code's happens-before,
   spelled in separation logic; the two [fence rw,rw]s are its machine-level
   counterpart and are no-ops in the model (WpSconfCtl.wp_fence_gen_s_sconf).

   WHY THE DEPOSIT MUST BE PERSISTENT.  Up to [NCPU - 1] harts read the flag,
   each expecting the payload, and the invariant is re-closed unchanged after
   every read -- so [P] has to be duplicable.  Every lemma below therefore
   takes [Persistent P].  That is not a limitation in practice: everything the
   boot hart produces that a secondary hart needs IS persistent -- the console
   / printk / disk device invariant, the [pr] lock, the 64 proc locks
   ([SchedCtx.procs_inv]), the kernel-mapping claims.  What is NOT persistent
   -- a hart's own satp/tlb/stvec cells, its stack carve, its [cpu_own] --
   never crosses this invariant at all: each hart gets those from its own
   [_entry] -> [start] boot, not from hart 0.

   THE ONE THING A READER MUST LIVE WITH.  Opening an invariant yields its
   body under a LATER, and [P] is persistent but not timeless (it is a
   conjunction of [inv]-based facts), so the reader gets [▷ P], not [P].  The
   later has to be stripped at a program step, and on the spin loop's EXIT
   path (the fall-through of [beqz a5] at main+0x1a) none of the leaves the
   secondary arm then runs exposes one.  [started_inv_load_au] therefore hands
   back [▷ (⌜v = 0⌝ ∨ P)] honestly, and the consumer needs a later-exposing
   leaf at the acquire fence -- which is the semantically right place for it.
   See claude-notes/projects/main-boot.md.

   Kept deliberately low in the tree: [↦₄] + [inv] + [KernelSyms] only, so
   SpecMain.v can require it without dragging in any WP layer. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth dfrac.
From iris.base_logic.lib Require Import invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExec Ktier.
From Kernel Require KernelSyms.
Require Import TsoMemPa TsoGhost TsoCtx TsoCtxMove TsoCtxAbsorbLb CtxMorphTac.
Require Import HartTp WpSconfMem.
Local Open Scope Z_scope.

(* the flag's address, and the two values it ever holds *)
Definition started_addr : mword 64 := mword_of_int KernelSyms.started.
Definition started_clear : mword 32 := mword_of_int 0.
Definition started_set : mword 32 := mword_of_int 1.

(* ---------------------------------------------------------------------- *)
(* The machine-level reading of the flag.  main tests the loaded word with  *)
(* [sext.w a5,a5; beqz a5], so what the branch leaves see is                *)
(* [eq_vec (sign_extend' 64 v) zero_reg]; these two bridges are what turn   *)
(* that into a fact about [v] and back.                                     *)
(* ---------------------------------------------------------------------- *)

Lemma started_clear_sext : eq_vec (sign_extend' 64 started_clear) zero_reg = true.
Proof. vm_compute. reflexivity. Qed.

(* the fall-through of [beqz a5] proves the word is NOT the cleared value --
   which is what refutes the invariant's left disjunct. *)
Lemma started_sext_nonzero (v : mword 32) :
  eq_vec (sign_extend' 64 v) zero_reg = false -> v <> started_clear.
Proof.
  intros Hne Heq. rewrite Heq started_clear_sext in Hne. discriminate.
Qed.

Section StartedInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Definition startedN : namespace := nroot .@ "started".

  (* destructing the right arm under [iInv]'s later needs these *)
  Local Instance started_pwmsg_inhabited : Inhabited pwmsg := populate (PWMsg ∅ 0%nat).
  Local Instance started_cpu_inhabited : Inhabited CPU := populate (@cpu_id CID).

  (* ==================================================================== *)
  (* A6.132: THE BARRIER AS A RELEASE-ARMED RACY WORD (owner ruling         *)
  (* §0.45′).  [started] is written once, by the primary, and read racily  *)
  (* by every secondary until it observes the write -- the lock's shape    *)
  (* with a plain load for the acquire.  So the word is stated the way the *)
  (* lock word is: a PHYSICAL ledger window, never a stable-view cell.     *)
  (*   - BEFORE the store: the plain window at stamp 0 (the image), and a  *)
  (*     record context [ξd] parked at 0 with nothing in it yet.           *)
  (*   - AFTER the store: the window RELEASE-ARMED at floor 0 with the one  *)
  (*     history position [S i] (the store), the store's message receipt,   *)
  (*     the record [ξd] parked at a stamp below the store carrying the     *)
  (*     primary's deposit [P ξd], and the index registered in a singleton *)
  (*     set authority (the readers' agreement handle).                     *)
  (* A reader that observes [started_set] settled on the store's position  *)
  (* (the image holds [started_clear] -- [era_img], a constant of the era), *)
  (* so its view covers the record's stamp and it ABSORBS the deposit into  *)
  (* its own context ([ctx_absorb_lb]) at a second open, after the fence.   *)
  (* ==================================================================== *)

  Definition started_win_plain : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       phys_ledger_at (pa_add started_addr j) (DfracOwn 1)
         (nth_byte started_clear j) 0%nat)%I.

  (* the window after the store at index [i] (position [S i]): every byte's
     stamp IS the store, and the history is that one position *)
  Definition started_win_rel (i : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       phys_ledger_rpay (pa_add started_addr j) (DfracOwn 1)
         (nth_byte started_set j) (S i)
         (TsRel started_addr 4%nat j 0%nat 0%nat (fun _ => 0%nat)
            (nth_byte started_clear) [(S i, nth_byte started_set)]))%I.

  (* the image fact: [started] is zero in the era's image *)
  Definition started_img : Prop :=
    forall j : nat, (j < 4)%nat ->
      era_img riscv_eraGS !! pa_add started_addr j = Some (nth_byte started_clear j).

  (* the readers' agreement handle on the store's index *)
  Definition started_idx (γi : gname) (i : nat) : iProp Σ :=
    dset_in γi (S i, started_addr).
  Global Instance started_idx_persistent γi i : Persistent (started_idx γi i).
  Proof. rewrite /started_idx. apply _. Qed.

  (* THE PRIMARY'S TOKEN: half the (empty) set authority.  It refutes the
     right arm at the store (the arms' authorities disagree) and is spent
     into the registration. *)
  Definition started_prim (γi : gname) : iProp Σ := dset_auth γi (1/2) ∅.

  Definition started_right (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ) : iProp Σ :=
    (* the window itself names the author (agent 0, the zero-cid hart) and
       carries the release's bytes in its history entry, so no message
       fragment is needed (A6.126 §6.3). *)
    (∃ (i : nat) (T : nat),
       started_win_rel i ∗
       dset_auth γi 1 {[(S i, started_addr)]} ∗
       ctx_parked ξd T ∗ ⌜(T ≤ S i)%nat⌝ ∗ P ξd)%I.

  Definition started_body (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ) : iProp Σ :=
    (wordw_claim (KTR := KT0) 4 started_addr ∗ ⌜started_img⌝ ∗
     (started_win_plain ∗ dset_auth γi (1/2) ∅ ∗ ctx_parked ξd 0
      ∨ started_right γi ξd P))%I.

  Definition started_inv (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ) : iProp Σ :=
    inv startedN (started_body γi ξd P).

  Global Instance started_inv_persistent γi ξd P : Persistent (started_inv γi ξd P).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* Allocation, by the client that assembles the machine: the plain      *)
  (* window and its claim come out of the boot carve, the record context  *)
  (* is boot's stamp-0 mint (a RECORD, not a process: §0.44′), the index  *)
  (* authority is fresh.  The primary keeps half of it.                   *)
  (* ------------------------------------------------------------------- *)
  Lemma started_alloc (E : coPset) (ξd : CtxId) (P : CtxId -> iProp Σ) :
    started_img ->
    wordw_claim (KTR := KT0) 4 started_addr -∗
    started_win_plain -∗ ctx_parked ξd 0 ={E}=∗
    ∃ γi : gname, started_inv γi ξd P ∗ started_prim γi.
  Proof.
    iIntros (Himg) "#Hcl Hw Hpk".
    iMod dset_alloc as (γi) "Hauth".
    iDestruct (dset_halves with "Hauth") as "[Ha1 Ha2]".
    iMod (inv_alloc startedN E (started_body γi ξd P) with "[Hw Hpk Ha1]") as "#Hinv".
    { iNext. rewrite /started_body. iFrame "Hcl". iSplitR; [by iPureIntro|].
      iLeft. iFrame "Hw Ha1 Hpk". }
    iModIntro. iExists γi. iFrame "Hinv". iExact "Ha2".
  Qed.

  (* the claim, peeked without touching the arms *)
  (* the window's persistent address claim, named so boot can state it
     without importing the memory rules *)
  Definition started_claim : iProp Σ := wordw_claim (KTR := KT0) 4 started_addr.

  Lemma started_claim_intro (ppn : mword 44) :
    is_aligned_paddr (Physaddr started_addr) 4 = true ->
    (uint started_addr < 274877906944)%Z ->
    addr_is_ram (pa_of ppn started_addr) ->
    ktier_pin KT0 ppn started_addr ->
    kmap_at (svpn_of started_addr) ppn KP_rw -∗ started_claim.
  Proof.
    iIntros (Hal Hc Hr Hpin) "#Hk". rewrite /started_claim /wordw_claim /mem_claim.
    iSplitR; [iPureIntro; exact Hal |]. iExists ppn. iFrame "Hk".
    iPureIntro. split; [exact Hc | split; [exact Hr | exact Hpin]].
  Qed.

  Local Lemma dset_auth_excl (γ : gname) D :
    dset_auth γ 1 D -∗ dset_auth γ (1/2) ∅ -∗ False.
  Proof.
    iIntros "H1 H2". rewrite /dset_auth.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv. destruct Hv as (Hq & _ & _).
    rewrite dfrac_op_own dfrac_valid_own in Hq.
    exfalso. by apply Qp.not_add_le_l in Hq.
  Qed.

  (* THE RELEASE SIDE'S OPENING: the primary holds [started_prim], which
     excludes the armed disjunct, so what it finds is the plain window,
     the authority's other half and the deposit context still parked at
     0 -- exactly [started_store_obl]'s resource -- and closing takes the
     armed disjunct back. *)
  Lemma started_store_open (Em : coPset) (γi : gname) (ξd : CtxId)
      (P : CtxId -> iProp Σ) :
    ↑startedN ⊆ Em ->
    started_inv γi ξd P -∗ started_prim γi -∗ P cur_ctx -∗
    (|={Em, Em ∖ ↑startedN}=>
       (started_win_plain ∗ dset_auth γi (1/2) ∅ ∗ ctx_parked ξd 0 ∗
        started_prim γi ∗ P cur_ctx) ∗
       (started_right γi ξd P ={Em ∖ ↑startedN, Em}=∗ True)).
  Proof.
    iIntros (HE) "#Hinv Hprim HP".
    iMod (inv_acc Em startedN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as "(>#Hcl & >%Himg & [(>Hw & >Hda & >Hpk) | Hr])".
    - iModIntro. iFrame "Hw Hda Hpk Hprim HP".
      iIntros "Hr". iMod ("Hclose" with "[Hr]") as "_"; [| done].
      iNext. iFrame "Hcl". iSplitR; [iPureIntro; exact Himg |]. iRight. iExact "Hr".
    - iDestruct "Hr" as (i T) "(_ & >Hda & _)".
      iExFalso. iApply (dset_auth_excl with "Hda"). rewrite /started_prim. iExact "Hprim".
  Qed.

  Lemma started_inv_claim (E : coPset) (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ) :
    ↑startedN ⊆ E ->
    started_inv γi ξd P ={E}=∗ wordw_claim (KTR := KT0) 4 started_addr.
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc E startedN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as "(>#Hcl & Hrest)".
    iMod ("Hclose" with "[Hrest]") as "_"; [iNext; iFrame "Hcl Hrest"|].
    iModIntro. iExact "Hcl".
  Qed.

  (* a message receipt, cashed against the interpretation *)
  (* agent 0 IS the hart with the zero cid word, both ways *)
  Local Lemma agent_zero_cid (c : CPU) :
    hart_agent c = 0%nat -> cid_word_of c = zero_reg.
  Proof.
    intros H. unfold hart_agent in H. unfold cid_word_of. rewrite H.
    apply bv_eq. vm_compute. reflexivity.
  Qed.

  Local Lemma cid_zero_agent (c : CPU) :
    cid_word_of c = zero_reg -> hart_agent c = 0%nat.
  Proof.
    intros Hc. unfold cid_word_of in Hc. unfold hart_agent.
    pose proof (fin_to_nat_lt c) as Hlt.
    revert Hc Hlt. generalize (fin_to_nat c) as k. intros k Hc Hlt.
    destruct k as [|[|[|[|[|[|[|[|k]]]]]]]];
      try reflexivity;
      try (exfalso; apply (f_equal (fun x : mword 64 => bv_unsigned x)) in Hc;
           vm_compute in Hc; discriminate Hc).
    exfalso. cbv in Hlt. lia.
  Qed.

  Lemma started_set_clear_ne : nth_byte started_set 0 <> nth_byte started_clear 0.
  Proof. vm_compute. discriminate. Qed.

  (* ------------------------------------------------------------------- *)
  (* THE READ, a secondary's.  The client opens the invariant and hands   *)
  (* the release read ([WpSconfMem.wp_load_s_sconf_au_relr]) the window  *)
  (* in whichever arm it finds, with the arm's persistent facts beside   *)
  (* it; the obligation below turns them into the resource the           *)
  (* continuation needs: on [started_set], the store's index and         *)
  (* [S i ≤ V0] at the view the read settled on.                          *)
  (* ------------------------------------------------------------------- *)
  Local Lemma dset_auth_split (γ : gname) (q1 q2 : Qp) S :
    dset_auth γ (q1 + q2) S ⊣⊢ dset_auth γ q1 S ∗ dset_auth γ q2 S.
  Proof. rewrite /dset_auth -own_op -auth_auth_dfrac_op dfrac_op_own. done. Qed.

  Definition started_res (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ) : iProp Σ :=
    (⌜started_img⌝ ∗
     (started_win_plain ∗ dset_auth γi (1/4) ∅
      ∨ ∃ i : nat,
          started_win_rel i ∗ started_idx γi i ∗ ▷ P ξd))%I.

  Definition started_W (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ)
      (v : mword 32) (tv : nat) : iProp Σ :=
    (⌜v = started_clear⌝
     ∨ ∃ i : nat, ⌜v = started_clear \/ (v = started_set /\ (S i <= tv)%nat)⌝ ∗
                  started_idx γi i ∗ ▷ P ξd)%I.

  Lemma started_read_open (Em : coPset) (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ)
      `{!∀ ξ, Persistent (P ξ)} :
    ↑startedN ⊆ Em ->
    started_inv γi ξd P -∗
    (|={Em, Em ∖ ↑startedN}=> started_res γi ξd P ∗
       (started_res γi ξd P ={Em ∖ ↑startedN, Em}=∗ True)).
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc Em startedN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as "(>#Hcl & >%Himg & [Hl | Hr])".
    - iDestruct "Hl" as "(>Hw & >Ha & >Hpk)".
      iEval (rewrite -(Qp.quarter_quarter) dset_auth_split) in "Ha".
      iDestruct "Ha" as "[Ha1 Ha2]".
      iModIntro. iSplitL "Hw Ha1".
      { iSplitR; [by iPureIntro|]. iLeft. iFrame "Hw Ha1". }
      iIntros "(_ & [[Hw Ha1] | Hbad])".
      + iMod ("Hclose" with "[Hw Ha1 Ha2 Hpk]") as "_"; [|done].
        iNext. rewrite /started_body. iFrame "Hcl". iSplitR; [by iPureIntro|].
        iLeft. iFrame "Hw Hpk". iEval (rewrite -(Qp.quarter_quarter) dset_auth_split).
        iFrame "Ha1 Ha2".
      + iDestruct "Hbad" as (i) "(_ & Hidx & _)".
        iDestruct (dset_lookup with "Ha2 Hidx") as %Hin. set_solver.
    - iDestruct "Hr" as (i T) "(>Hw & >Ha & >Hpk & >%HT & #HP)".
      iMod (dset_get γi 1 {[(S i, started_addr)]} (S i, started_addr)
              (elem_of_singleton_2 _ _ eq_refl) with "Ha") as "[Ha #Hidx]".
      iModIntro. iSplitL "Hw".
      { iSplitR; [by iPureIntro|]. iRight. iExists i. iFrame "Hw Hidx HP". }
      iIntros "(_ & [[Hw Ha'] | Hw])".
      + iDestruct (dset_agree with "Ha Ha'") as %Hbad. set_solver.
      + iDestruct "Hw" as (i') "(Hw & #Hidx' & _)".
        iDestruct (dset_lookup with "Ha Hidx'") as %Hin.
        apply elem_of_singleton in Hin. injection Hin as Hii. subst i'.
        iMod ("Hclose" with "[Hw Ha Hpk]") as "_"; [|done].
        iNext. rewrite /started_body. iFrame "Hcl". iSplitR; [by iPureIntro|].
        iRight. iExists i, T. iFrame "Hw Ha Hpk HP". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE READ OBLIGATION -- [wp_load_s_sconf_au_relr]'s, at [started],     *)
  (* width 4, for a hart that is NOT the primary.  Left arm: the plain     *)
  (* window at stamp 0 reads [started_clear] at every view.  Right arm:    *)
  (* the release read settles on the floor (the image, which holds        *)
  (* [started_clear] -- the era's constant) or on the one history          *)
  (* position, the store; so a reader that sees [started_set] settled on   *)
  (* the store, which is visible to it and not its own message.            *)
  (* ------------------------------------------------------------------- *)
  Lemma started_read_obl (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ)
      `{!∀ ξ, Persistent (P ξ)} (p : mword 64) :
    cid_word <> zero_reg ->
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate)
           (log : list pwmsg) (V : agent -> nat) (ppn : mword 44),
      (uint started_addr < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec started_addr 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn started_addr ->
      (false = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of started_addr) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      started_res γi ξd P ==∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) ∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      started_res γi ξd P ∗
      ⌜forall tvr : nat, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
         exists v : mword (8*4),
           tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
             (pa_of ppn started_addr) (Z.to_N 4) v⌝ ∗
      (∀ (tvr : nat) (v : mword (8*4)),
         ⌜(V (hart_agent (@cpu_id CIDw)) <= tvr)%nat⌝ -∗
         ⌜tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
            (pa_of ppn started_addr) (Z.to_N 4) v⌝ -∗
         started_W γi ξd P v tvr).
  Proof.
    intros Hnz CIDw img sigma log V ppn Hcan Hoff Hid Hmig.
    rewrite (ktier_pin_id ppn started_addr Hid).
    pose proof (Hmig (or_introl eq_refl)) as HCw.
    iIntros "#Hk Hm Htso Hctx [%Himg Hres]".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    iDestruct (tso_interp_of_img with "Htso") as %Hera.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    set (g := gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev)).
    assert (Hgtv : g.(gtv) (@cpu_id CIDw) = V (hart_agent (@cpu_id CIDw))) by reflexivity.
    assert (Hgimg : g.(gimg) = img) by reflexivity.
    assert (Hglog : g.(glog) = log) by reflexivity.
    iDestruct "Hres" as "[[Hw Ha] | Hr]".
    - (* ---- the plain window: [started_clear] at every view ---- *)
      iAssert (⌜forall tv' : nat, (g.(gtv) (@cpu_id CIDw) <= tv')%nat ->
                 tso_read_bytes g.(gimg) g.(glog) (hart_agent (@cpu_id CIDw)) tv'
                   started_addr 4 started_clear⌝)%I as %Hrd.
      { iApply (ledger_read_bytes_vis_ok (CID := CIDw) g started_addr 4%N started_clear
                  (DfracOwn 1) 0%nat with "Hm Htso [] [Hw]").
        { iApply view_lb_0. }
        rewrite /started_win_plain. change (N.to_nat 4) with 4%nat.
        iApply (big_sepL_mono with "Hw"). iIntros (k j _) "H".
        iExists 0%nat. iFrame "H". iApply ledger_vis_below. lia. }
      iModIntro.
      rewrite -(tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
                  sigma.(sregs) sigma.(mdev) Hpin).
      iFrame "Hm Htso Hctx".
      iSplitL "Hw Ha". { iSplitR; [by iPureIntro|]. iLeft. iFrame "Hw Ha". }
      iSplitR.
      { iPureIntro. intros tvr Hle. exists started_clear.
        rewrite -Hgtv in Hle. specialize (Hrd tvr Hle).
        rewrite Hgimg Hglog in Hrd. exact Hrd. }
      iIntros (tvr v) "%Hle %Hrdv". iLeft. iPureIntro.
      rewrite -Hgtv in Hle. specialize (Hrd tvr Hle). rewrite Hgimg Hglog in Hrd.
      apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
      specialize (Hrdv j Hj). specialize (Hrd j Hj).
      rewrite Hrdv in Hrd. injection Hrd as Hb. apply bv_eq. exact Hb.
    - (* ---- the release-armed window ---- *)
      iDestruct "Hr" as (i) "(Hw & #Hidx & #HP)".
      (* this reader is NOT the author: its cid word is nonzero *)
      assert (Hag : hart_agent (@cpu_id CIDw) <> 0%nat).
      { intro H0. apply Hnz. rewrite /cid_word -HCw.
        apply agent_zero_cid. exact H0. }
      iAssert (⌜forall tv : nat, (g.(gtv) (@cpu_id CIDw) <= tv)%nat ->
         ((forall j, (j < 4)%nat ->
             tso_read g.(gimg) g.(glog) (hart_agent (@cpu_id CIDw)) tv
               (pa_add started_addr j) = Some (nth_byte started_clear j))
          /\ (forall q g0,
                (q, g0) ∈ [(S i, nth_byte started_set)] ->
                visibleb (hart_agent (@cpu_id CIDw)) tv g.(glog) q = false))
         \/ (exists T g0, (T, g0) ∈ [(S i, nth_byte started_set)]
               /\ visibleb (hart_agent (@cpu_id CIDw)) tv g.(glog) T = true
               /\ (hart_agent (@cpu_id CIDw) <> 0%nat -> (T <= tv)%nat)
               /\ (forall j, (j < 4)%nat ->
                     tso_read g.(gimg) g.(glog) (hart_agent (@cpu_id CIDw)) tv
                       (pa_add started_addr j) = Some (g0 j))
               /\ (forall q g1, (q, g1) ∈ [(S i, nth_byte started_set)] ->
                     visibleb (hart_agent (@cpu_id CIDw)) tv g.(glog) q = true ->
                     (q <= T)%nat))⌝)%I
        as %Hrel.
      { iApply (ledger_read_rel_ok (CID := CIDw) g started_addr 4%nat (DfracOwn 1)
                  0%nat 0%nat (fun _ => 0%nat) (nth_byte started_clear)
                  (nth_byte started_set) [(S i, nth_byte started_set)] 0%nat
                  ltac:(lia) with "Htso [] [] [Hw]").
        { iApply view_lb_0. }
        { rewrite /rel_floor_vis. iApply big_sepL_intro.
          iIntros "!>" (k j _). iApply ledger_vis_below. lia. }
        rewrite /started_win_rel /rel_cells. iApply (big_sepL_mono with "Hw").
        iIntros (k j _) "H". iExists (S i). iExact "H". }
      iModIntro.
      rewrite -(tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
                  sigma.(sregs) sigma.(mdev) Hpin).
      iFrame "Hm Htso Hctx".
      iSplitL "Hw".
      { iSplitR; [by iPureIntro|]. iRight. iExists i. iFrame "Hw Hidx HP". }
      iSplitR.
      { iPureIntro. intros tvr Hle. rewrite -Hgtv in Hle.
        destruct (Hrel tvr Hle) as [[Hfl _] | (T & g0 & Hin & _ & _ & Hrd0 & _)].
        - exists started_clear. intros j Hj. apply (Hfl j). lia.
        - apply elem_of_list_singleton in Hin. injection Hin as -> ->.
          exists started_set. intros j Hj. apply (Hrd0 j). lia. }
      iIntros (tvr v) "%Hle %Hrdv". rewrite -Hgtv in Hle.
      iRight. iExists i. iFrame "Hidx HP". iPureIntro.
      destruct (Hrel tvr Hle) as [[Hfl _] | (T & g0 & Hin & _ & HTle & Hrd0 & _)].
      + (* the floor: no history entry visible, the window reads its floor bytes *)
        left. apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
        assert (Hj4 : (j < 4)%nat) by lia.
        specialize (Hrdv j Hj). specialize (Hfl j Hj4).
        rewrite Hgimg Hglog in Hfl. rewrite Hrdv in Hfl.
        injection Hfl as Hb. apply bv_eq. exact Hb.
      + (* the hit: the one history entry, at or under this read's view *)
        apply elem_of_list_singleton in Hin. injection Hin as -> ->.
        right. split.
        * apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
          assert (Hj4 : (j < 4)%nat) by lia.
          specialize (Hrdv j Hj). specialize (Hrd0 j Hj4).
          rewrite Hgimg Hglog in Hrd0. rewrite Hrdv in Hrd0.
          injection Hrd0 as Hb. apply bv_eq. exact Hb.
        * exact (HTle Hag).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ABSORB, at a second open after the fence: the reader that        *)
  (* observed the store holds the record's stamp below its view, and the *)
  (* deposit comes into its own context; the token goes back at the same *)
  (* stamp, so the claim is repeatable by every hart.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma started_absorb (E : coPset) (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ)
      `{!CtxMorph P} `{!∀ ξ, Persistent (P ξ)} (i V0 : nat) :
    ↑startedN ⊆ E -> (S i <= V0)%nat ->
    started_inv γi ξd P -∗ started_idx γi i -∗ hart_view_lb V0 -∗
    own_context cur_ctx -∗ P ξd ={E}=∗ own_context cur_ctx ∗ P cur_ctx.
  Proof.
    iIntros (HE HiV) "#Hinv #Hidx #HK Hrun HP".
    iMod (inv_acc E startedN with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as "(>#Hcl & >%Himg & [Hl | Hr])".
    - iDestruct "Hl" as "(_ & >Ha & _)".
      iDestruct (dset_lookup with "Ha Hidx") as %Hin. set_solver.
    - iDestruct "Hr" as (i' T) "(>Hw & >Ha & >Hpk & >%HT & #HPd)".
      iDestruct (dset_lookup with "Ha Hidx") as %Hin.
      apply elem_of_singleton in Hin. injection Hin as Hii. subst i'.
      iMod (ctx_absorb_lb P ξd cur_ctx T V0 ltac:(lia) with "Hrun HK Hpk HP")
        as "(Hrun & Hpk & HP)".
      iMod ("Hclose" with "[Hw Ha Hpk]") as "_".
      { iNext. rewrite /started_body. iFrame "Hcl". iSplitR; [by iPureIntro|].
        iRight. iExists i, T. iFrame "Hw Ha Hpk HPd". by iPureIntro. }
      iModIntro. iFrame "Hrun HP".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PRIMARY'S STORE -- [wp_store_s_sconf_au_dat]'s obligation at      *)
  (* [started := started_set]: the record is deposited (at the OLD log,   *)
  (* so its stamp is below the store), the plain window is release-armed  *)
  (* at floor 0 and stored through, the index is registered.             *)
  (* ------------------------------------------------------------------- *)
  Local Lemma started_parked_llb (ξ : CtxId) (T : nat) :
    ctx_parked ξ T -∗ ctx_parked ξ T ∗ llb loglen_name T.
  Proof.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iIntros "(%D & Hat & #Hllb & %HD)". iSplitL; [| iExact "Hllb"].
    iExists D. iFrame "Hat Hllb". by iPureIntro.
  Qed.

  Lemma started_store_obl (γi : gname) (ξd : CtxId) (P : CtxId -> iProp Σ)
      `{!CtxMorph P} (p : mword 64) :
    cid_word = zero_reg ->
    forall (CIDw : CpuId) (img : bytemap) (sigma : mstate)
           (log : list pwmsg) (V : agent -> nat) (ppn : mword 44),
      (uint started_addr < 274877906944)%Z ->
      (bv_unsigned (subrange_vec_dec started_addr 11 0) + 4 <= 4096)%Z ->
      ktier_pin KT0 ppn started_addr ->
      (false = false \/ p = zero_reg -> (CIDw : CPU) = (CID : CPU)) ->
      kmap_at (svpn_of started_addr) ppn KP_rw -∗
      gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
      tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
      (started_win_plain ∗ dset_auth γi (1/2) ∅ ∗ ctx_parked ξd 0 ∗
       started_prim γi ∗ P TsoCtx.cur_ctx) ==∗
      gen_heap_interp (hG := riscv_memGS)
        (write_bytes sigma.(mem) (pa_of ppn started_addr) (Z.to_N 4) started_set) ∗
      tso_interp_of riscv_eraGS img
        (write_bytes sigma.(mem) (pa_of ppn started_addr) (Z.to_N 4) started_set)
        (log ++ [PWMsg (snap_of (pa_of ppn started_addr) (Z.to_N 4) started_set)
                   (hart_agent (@cpu_id CIDw))])%list
        (vstep (hart_agent (@cpu_id CIDw)) (V (hart_agent (@cpu_id CIDw)))
           (log ++ [PWMsg (snap_of (pa_of ppn started_addr) (Z.to_N 4) started_set)
                      (hart_agent (@cpu_id CIDw))])%list V) ∗
      TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗
      started_right γi ξd P.
  Proof.
    intros Hz CIDw img sigma log V ppn Hcan Hoff Hid Hmig.
    rewrite (ktier_pin_id ppn started_addr Hid).
    pose proof (Hmig (or_introl eq_refl)) as HCw.
    iIntros "#Hk Hm Htso Hctx (Hw & Ha1 & Hpk & Ha2 & HP)".
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    iDestruct (tso_interp_of_bound with "Htso") as %Hbd.
    rewrite (tso_interp_of_at_gs riscv_eraGS img sigma.(mem) log V
               sigma.(sregs) sigma.(mdev) Hpin).
    set (g := gs_of img sigma.(mem) log V sigma.(sregs) sigma.(mdev)).
    (* the deposit, at the old log *)
    iMod (ctx_deposit (CID := CIDw) P TsoCtx.cur_ctx ξd 0%nat with "Hctx Hpk HP")
      as "(Hctx & %T & _ & Hpk & HP)".
    iDestruct (started_parked_llb with "Hpk") as "[Hpk #Hllb]".
    iDestruct (tso_interp_llb_valid g T with "Htso Hllb") as "[Htso %HTlen]".
    (* the author is agent 0: this hart's cid word is zero *)
    assert (Hagent0 : hart_agent (@cpu_id CIDw) = 0%nat).
    { rewrite HCw. apply cid_zero_agent. exact Hz. }
    (* the release arm, per-byte floors at stamp 0 (the boot carve's) *)
    iMod (ledger_rpay_mint g started_addr 4%nat 0%nat 0%nat (fun _ => 0%nat)
            (nth_byte started_clear)
            ltac:(lia) ltac:(intros k _; cbv beta; lia)
            ltac:(exists 0%nat; split; [lia | reflexivity])
            with "Hm Htso [Hw]") as "(Hm & Htso & Hw)".
    { rewrite /started_win_plain. iApply (big_sepL_mono with "Hw").
      iIntros (k j _) "H". iExact "H". }
    (* the store *)
    set (log' := (log ++ [PWMsg (snap_of started_addr (Z.to_N 4) started_set)
                            (hart_agent (@cpu_id CIDw))])%list).
    set (V' := vstep (hart_agent (@cpu_id CIDw))
                 (V (hart_agent (@cpu_id CIDw))) log' V).
    assert (Hpin' : forall h, (NCPU <= h)%nat -> V' h = length log').
    { intros h Hh. rewrite /V' /vstep. case_decide as Hd.
      - exfalso. subst h. pose proof (fin_to_nat_lt (@cpu_id CIDw)).
        rewrite /hart_agent in Hh. lia.
      - destruct (lt_dec h NCPU); [lia | reflexivity]. }
    assert (Htvc : forall c : CPU, V' (hart_agent c) = V (hart_agent c)).
    { intros c. rewrite /V' /vstep. case_decide as Hd.
      - by rewrite Hd.
      - destruct (lt_dec (hart_agent c) NCPU) as [|Hge]; first reflexivity.
        exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hge. lia. }
    assert (Htvmono : forall c : CPU, (V (hart_agent c) <= V' (hart_agent c))%nat)
      by (intros c; rewrite Htvc; lia).
    assert (Htvtop : forall c : CPU, (V' (hart_agent c) <= length log')%nat).
    { intros c. rewrite Htvc /log' length_app /=.
      have := Hbd (hart_agent c). lia. }
    iMod (ledger_store_rel_map_ok g
            (gs_of img (write_bytes sigma.(mem) started_addr (Z.to_N 4) started_set)
               log' V' sigma.(sregs) sigma.(mdev))
            0%nat ∅ (snap_of started_addr (Z.to_N 4) started_set)
            started_addr (Z.to_N 4) started_clear started_set
            0%nat (fun _ => 0%nat) (nth_byte started_clear) []
            ltac:(cbn; lia) ltac:(reflexivity)
            ltac:(rewrite dom_empty_L !dom_snap_of; set_solver)
            eq_refl ltac:(by rewrite /log' Hagent0)
            ltac:(apply write_bytes_union) Htvmono Htvtop
            with "Hm Htso [] [Hw]") as "(Hm & Htso & #Hmsg & Hjunk & Hw)".
    { by rewrite big_sepM_empty. }
    { change (N.to_nat (Z.to_N 4)) with 4%nat. rewrite /rel_cells.
      iApply (big_sepL_mono with "Hw").
      iIntros (k j _) "H". iExists 0%nat. iExact "H". }
    rewrite -(tso_interp_of_at_gs riscv_eraGS img
                (write_bytes sigma.(mem) started_addr (Z.to_N 4) started_set)
                log' V' sigma.(sregs) sigma.(mdev) Hpin').
    (* the index *)
    iAssert (dset_auth γi 1 ∅) with "[Ha1 Ha2]" as "Ha".
    { rewrite dset_halves. iFrame "Ha1 Ha2". }
    iMod (dset_insert γi ∅ (S (length log), started_addr) with "Ha") as "[Ha #Hidx]".
    rewrite (left_id_L ∅ union).
    iModIntro. iFrame "Hm Htso Hctx".
    rewrite /started_right.
    iExists (length log), T.
    iFrame "Ha Hpk HP".
    iSplitL "Hw".
    { rewrite /started_win_rel. change (N.to_nat (Z.to_N 4)) with 4%nat.
      iApply (big_sepL_mono with "Hw"). iIntros (k j _) "H". cbn [app]. iExact "H". }
    iPureIntro. cbn in HTlen. lia.
  Qed.

End StartedInv.
