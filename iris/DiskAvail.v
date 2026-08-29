(* DiskAvail.v -- THE AVAIL-INDEX WORD'S PAYLOAD HALF (A6.124).

   [struct virtq_avail.idx] is written only by [vdisk_lock] holders and read
   only by them (the device READS it through the lease).  §0.35′(iv) case 3
   says its floor rides in the lock payload; A6.121 made [disk_res]
   context-indexed so that it can.  The split:

     - the DMA lease ([VirtioProto.virtio_proto]) keeps HALF of each of the
       word's two ledger cells, sealed ([avail_lease_half]) -- the device's
       view of the word and the publisher's full cell (halves joined inside
       the store) are both still there;
     - the payload keeps the other half with the STAMP EXPOSED and the FLOOR
       beside it ([avail_half]): a holder reads the word with its own half
       and cashes the floor against its running token ([WpLock.lk_floor_vis]
       + [TsoCtx.ledger_read_at_vis_ok]) -- no invariant opened; a publisher
       stores through the joined cell, registers its position
       ([TsoCtx.ctx_wrote_register]) and installs the right arm; the floor
       transports across release/acquire on both arms ([lk_floor_morph]).

   The boot creator's arm comes from FORGETTING the zeroed ctx bytes into
   the ledger ([TsoCtx.ctx_phys_pointsto_forget_floor]): clean is the boot
   context's bound, dirty is its own memset write, persisted. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import TsoMemPa TsoGhost TsoCtx CtxMorphTac.
Require Import KptPt KMap.
Require Import VirtioModel VirtioQueue WpVirtio VirtioProto.
Require Import WpLock.
Local Open Scope Z_scope.

Section DiskAvail.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* the payload's half of the word: per byte, the exposed stamp and the
     floor the holder cashes against its token *)
  Definition avail_half (pav : mword 64) (np : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2, ∃ t : nat,
       phys_ledger_at (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
         (nth_byte (wrap16 np) j) t ∗
       lk_floor cur_ctx t)%I.

  Lemma avail_half_ram (pav : mword 64) (np : nat) :
    avail_half pav np -∗ ⌜addr_is_ram (pa_add pav 2%nat)⌝.
  Proof.
    rewrite /avail_half. iEval (cbn [seq]). iIntros "((%t & Hc & _) & _)".
    rewrite /phys_ledger_at /phys_pointsto pa_add_0.
    iDestruct "Hc" as "[[_ %Hr] _]". by iPureIntro.
  Qed.

  (* THE HOLDER'S READ, as the datum obligation of
     [WpSconfMem.wp_load_s_sconf_au_dat]: exact, on either arm of each
     byte's floor. *)
  Lemma avail_half_read_ok `{CID : CpuId} (g : gstate) (pav : mword 64) (np : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context cur_ctx -∗
    avail_half pav np -∗
    ⌜forall tvr : nat, (g.(gtv) cpu_id <= tvr)%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tvr
         (pa_add pav 2%nat) 2 (wrap16 np)⌝.
  Proof.
    iIntros "Hgh Hint Hrun H".
    iAssert (⌜forall j, (j < 2)%nat -> forall tvr, (g.(gtv) cpu_id <= tvr)%nat ->
               tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tvr
                 (pa_add (pa_add pav 2%nat) j) = Some (nth_byte (wrap16 np) j)⌝)%I
      with "[Hgh Hint Hrun H]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ _ j j with "H") as (t) "[Hc #Hfl]";
        [apply lookup_seq; split; lia|].
      iDestruct (lk_floor_vis with "Hrun Hfl") as "[Hrun (%K & #HK & #Hvis)]".
      iApply (ledger_read_at_vis_ok with "Hgh Hint HK Hvis Hc"). }
    iPureIntro. intros tvr Htvr j Hj. apply HH; [lia | exact Htvr].
  Qed.

  (* THE BOOT SPLIT: the two zeroed ctx bytes leave the tower as halves --
     the lease's sealed half and the payload's half with its floor. *)
  Lemma avail_split_init (pd pav pu : mword 64) :
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add (pa_add pav 2%nat) j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add (pa_add pav 2%nat) j) ↦ₘ nth_byte (wrap16 0%nat) j) ==∗
    avail_lease_half (virtio_init_cfg pd pav pu) 0 ∗ avail_half pav 0.
  Proof.
    iIntros (Hs) "#Hkm H".
    assert (Havi : avail_idx_pa (virtio_init_cfg pd pav pu) = pa_add pav 2%nat)
      by reflexivity.
    rewrite /avail_lease_half /avail_half Havi.
    iAssert (|==> [∗ list] j ∈ seq 0 2,
       phys_ledger (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
         (nth_byte (wrap16 0%nat) j) ∗
       ∃ t : nat,
         phys_ledger_at (pa_add (pa_add pav 2%nat) j) (DfracOwn (1/2))
           (nth_byte (wrap16 0%nat) j) t ∗ lk_floor cur_ctx t)%I
      with "[H]" as ">H".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!>" (k j Hk) "Hb".
      apply lookup_seq in Hk. destruct Hk as [-> Hlt].
      iDestruct (ctx_pointsto_canonical with "Hb") as %Hc.
      assert (Hk2 : (0 + k < 2)%nat) by lia.
      iDestruct (kmap_static_claims_at (svpn_of (pa_add (pa_add pav 2%nat) (0 + k)%nat))
                   KP_rw (Hs _ Hk2) with "Hkm") as "#Hk0".
      iDestruct (ctx_pointsto_to_phys cur_ctx _ _ _ _
                   (pa_of_id (pa_add (pa_add pav 2%nat) (0 + k)%nat) Hc)
                   with "Hk0 Hb") as "Hb".
      iMod (ctx_phys_pointsto_forget_floor with "Hb") as (t) "[Hat Hfl]".
      iEval (rewrite phys_ledger_at_halves) in "Hat". iDestruct "Hat" as "[H1 H2]".
      iModIntro. iSplitL "H1"; [ by iApply phys_ledger_at_ledger | ].
      iExists t. iFrame "H2".
      iDestruct "Hfl" as "[Hfl | Hfl]";
        [ by iApply lk_floor_of_ctx | by iApply lk_floor_of_wrote ]. }
    iModIntro. rewrite big_sepL_sep. iDestruct "H" as "[$ $]".
  Qed.
End DiskAvail.

Section DiskAvailMorph.
  Context `{!riscvGS Σ}.
  Global Instance avail_half_morph (pav : mword 64) (np : nat) :
    CtxMorph (λ ξ, avail_half (XI := ξ) pav np).
  Proof. rewrite /avail_half. ctx_morph_solve. all: apply lk_floor_morph. Qed.
End DiskAvailMorph.
