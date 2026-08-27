(* BioInitAt.v -- [BioInv.bio_init] split at its ghost steps.

   [bio_init] mints all six [bio_names] fields itself and returns the record
   existentially.  That is too late for a client that has to PUBLISH the
   record before the buffer cache exists: [FsCfg.fscfg]'s [fsc_bio] field is
   ambient, fixed before any fupd runs, and an ambient field cannot be an
   existential (claude-notes/projects/fs-cfg-boot.md, "THE PRINCIPLE").

   So the lemma splits:

     bio_free_tok bn         -- the free state of all six fields, ONE row (a
                                boot kit carries one row per subsystem, not
                                twenty -- [FsReady.fs_ready]'s argument
                                applied to the boot side)
     bio_names_ghost_alloc   -- pick the record.  A plain [bupd]: no mask, no
                                physical premise, nothing address-shaped, so
                                the era fupd runs it before binit does
     bio_init_at bn          -- [bio_init]'s physical premises verbatim, at
                                the record the caller already published

   [bio_init] itself is left alone: it lives in [BioInv], which this file
   imports, and it has no caller in the tree.  The two bodies are duplicated
   until one appears. *)
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
Require Import SleepLock.
Require Import WpLockAt.
Require Import SleepLockAt.
Require Import BufOwn.
Require Import BcacheInv.
Require Export BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.
Local Open Scope Z_scope.

Section BioInitAt.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The free state of a [bio_names] record                              *)
  (* ------------------------------------------------------------------ *)

  (* No buffer holds a reference (the count authority is empty), the whole
     slot supply is unspent, the bcache spinlock and every buffer sleeplock
     are unbuilt, and every checkout / recycle token is idle. *)
  Definition bio_free_tok (bn : bio_names) : iProp Σ :=
    (lock_free_tok (bn_lk bn) ∗
     own (bn_auth bn) (● (∅ : gmap nat (Qp * positive)) : bioUR) ∗
     bslots_auth ∗
     bslots BSLOTS_FS ∗
     ([∗ list] k ∈ seq 0 NBUF,
        sl_free_pair (bn_slk bn k) ∗
        lock_tok_excl (bn_own bn k) ∗
        lock_tok_excl (bn_mid bn k)))%I.

  Local Lemma bio_at_seq_cons (j n : nat) : seq j (S n) = j :: seq (S j) n.
  Proof. reflexivity. Qed.

  (* the four per-buffer gnames collected into ONE function, so the induction
     updates one binder rather than three ([BioInv]'s [tok_fun_alloc] /
     [seq_fun_alloc] pay that cost per family because they run at three
     different points in [bio_init]; here everything is minted at once). *)
  Local Lemma bio_buf_ghost_alloc (n j : nat) :
    ⊢ |==> ∃ f : nat -> (gname * gname) * gname * gname,
        [∗ list] k ∈ seq j n,
          sl_free_pair (f k).1.1 ∗
          lock_tok_excl (f k).1.2 ∗
          lock_tok_excl (f k).2.
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod sl_pair_ghost_alloc as (p) "Hp".
    iMod lock_tok_excl_alloc as (γo) "Ho".
    iMod lock_tok_excl_alloc as (γm) "Hm".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun k => if decide (k = j) then (p, γo, γm) else f k).
    rewrite bio_at_seq_cons. iSplitL "Hp Ho Hm".
    { case_decide as Hd; [| congruence]. iFrame "Hp Ho Hm". }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* THE SLOT SUPPLY IS THREADED IN, not minted here: its ghost name is
     canonical ([Xv6Cameras.bioslot_name]) and therefore fixed before this
     record is picked, so [BioDefs.bslots_alloc] mints authority and
     fragments together and this lemma parks them in the free-state row. *)
  Lemma bio_names_ghost_alloc :
    bslots_auth -∗ bslots BSLOTS_FS -∗ |==> ∃ bn : bio_names, bio_free_tok bn.
  Proof.
    iIntros "Hsa Hsf".
    iMod lock_ghost_alloc as (γlk) "Hlk".
    iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iMod (bio_buf_ghost_alloc NBUF 0) as (f) "Hbufs".
    iModIntro.
    iExists (MkBioNames γlk γb (fun k => (f k).1.1) (fun k => (f k).1.2)
                        (fun k => (f k).2)).
    rewrite /bio_free_tok /bslots_auth /bslots.
    cbn [bn_lk bn_auth bn_slk bn_own bn_mid].
    iFrame "Hlk Hauth Hsa Hsf Hbufs".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PAYLOAD OF ONE ZEROED [struct buf], AS A NAMED ROW              *)
  (* ------------------------------------------------------------------ *)

  (*  Everything of buffer [k]'s 1112-byte record that binit does NOT touch
      and [bio_init_at] therefore has to be handed straight out of the .bss
      carve: the four zeroed metadata words at +0/+4/+8/+12, the reference
      count at +64, and the 1024 data bytes at +88 (contents existential --
      nothing reads them before the first [bread]).  binit writes only the
      link pair at +72/+80 and the sleeplock at +16, so this row crosses the
      binit call untouched, exactly as [IcacheInv.ientry_raw] crosses iinit.

      IT IS NAMED because it is a BOOT KIT ROW in all but location: it is
      carved by [BootCarveMain.boot_bcache_nodes], carried by
      [SpecMain.main_globals_raw] across main+0x8e, and spent here.  Three
      files spelling one six-conjunct big-op body is exactly the shape
      [FsReady.fs_ready]'s "one row per subsystem" argument rejects.       *)
  Definition buf_raw (k : nat) : iProp Σ :=
    (b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
     b_disk (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
     b_dev (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
     b_blockno (bpa k) ↦₄ (mword_of_int 0 : mword 32) ∗
     brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
     (∃ bs : list (bv 8), ⌜length bs = 1024%nat⌝ ∗
        [∗ list] j ↦ byte ∈ bs, pa_add (b_data (bpa k)) j ↦ₘ byte))%I.

  (* ------------------------------------------------------------------ *)
  (*  Construction at a published record                                  *)
  (* ------------------------------------------------------------------ *)

  (* [BioInv.bio_init]'s physical premises verbatim -- binit's postcondition
     plus the .bss-zeroed [struct buf] cells and the covered range's pool
     bundles -- against a record whose gnames are already fixed.  Two of
     [bio_init]'s three collectors disappear with them: the sleeplocks are
     built AT [bn_slk bn k] rather than gathered into a function, and the
     bcache lock needs no [newlock_delayed] because [bcache_res bn V] is
     statable before it is sealed. *)
  Lemma bio_init_at (bn : bio_names) (V : bio_view Σ) E :
    (0 ∉ bv_cov V) ->
    bio_free_tok bn -∗
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    add_vec bcache_addr (sign_extend' 64 (mword_of_int 16 : mword 12)) ↦₈
      (zero_reg : mword 64) -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF, buf_raw k) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    ([∗ set] b ∈ bv_cov V, pool_blk V b) ={E}=∗
    bio_ctx bn V ∗ bslots BSLOTS_FS.
  Proof.
    iIntros (Hnc0) "(Hlkg & Hauth & Hsa & Hsf & Hbg) Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hpool".
    assert (Hu0 : uint (mword_of_int 0 : mword 32) = 0)
      by (vm_compute; reflexivity).
    (* every buffer's sleeplock, at its published gname pair, sealing exactly
       its checkout token; the recycle tokens come back out. *)
    iDestruct (big_sepL_sep_2 with "Hfresh Hbg") as "Hsl".
    iAssert (([∗ list] k ∈ seq 0 NBUF, |={E}=>
                is_sleeplock (fst (bn_slk bn k)) (snd (bn_slk bn k))
                  (buf_lock (bnode k)) "buffer"%string (bown bn k)) ∗
             ([∗ list] k ∈ seq 0 NBUF, bmid bn k))%I
      with "[Hsl]" as "[Hsl Hmids]".
    { rewrite -big_sepL_sep. iApply (big_sepL_mono with "Hsl").
      intros i k Hk. iIntros "[Hf (Hp & Ho & Hm)]".
      iFrame "Hm".
      iApply (sl_fresh_new_at2 E (bn_slk bn k) (buf_lock (bnode k))
                "buffer"%string (bown bn k) with "Hp Hf Ho"). }
    iMod (big_sepL_fupd with "Hsl") as "#Hsls".
    (* every initial payload is empty: blockno 0 is uncovered *)
    assert (Hpay0 : forall k bs,
        buf_pay bn V k false (mword_of_int 0 : mword 32)
          (mword_of_int 0 : mword 32) bs = emp%I).
    { intros k bs. rewrite /buf_pay. case_decide as Hd; [|reflexivity].
      exfalso. apply Hnc0. rewrite -Hu0. exact Hd. }
    (* park every buffer's content in a fresh escrow, keeping the bcache half
       of dev/blockno and the refcnt cell for [bcache_res] *)
    iDestruct (big_sepL_sep_2 with "Hbufs Hmids") as "Hbm".
    iAssert (([∗ list] k ∈ seq 0 NBUF, |={E}=> buf_escrow bn V k) ∗
             ([∗ list] k ∈ seq 0 NBUF,
                bio_slot_res bn ∅ k (mword_of_int 0 : mword 32)
                  (mword_of_int 0 : mword 32)))%I
      with "[Hbm]" as "[Hesc Hslots]".
    { rewrite -big_sepL_sep. iApply (big_sepL_mono with "Hbm").
      intros i k Hk. rewrite /buf_raw.
      iIntros "[(Hv & Hdk & Hdev & Hbno & Hrc & Hdata) Hmid]".
      iDestruct (word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iDestruct "Hdata" as (bs) "[%Hlen Hdata]".
      iSplitR "Hrc Hdev2 Hbno2".
      - rewrite /buf_escrow.
        iApply (inv_alloc bioN E (buf_escrow_body bn V k)).
        iNext. iLeft. rewrite /buf_parked.
        iExists false, (mword_of_int 0 : mword 32),
                (mword_of_int 0 : mword 32), bs.
        rewrite Hpay0. cbv iota.
        iFrame "Hv Hdev1 Hmid". rewrite /buf_own.
        iFrame "Hbno1 Hdk Hdata". done.
      - rewrite /bio_slot_res lookup_empty. iFrame "Hrc Hdev2 Hbno2". }
    iMod (big_sepL_fupd with "Hesc") as "#Hescs".
    (* the initial pool covers the whole range: the zeroed slots claim only
       the uncovered 0 *)
    iAssert (bio_pool V (fun _ => (mword_of_int 0 : mword 32)))
      with "[Hpool]" as "Hpool".
    { rewrite /bio_pool.
      assert (Hc0 : bv_cov V ∖
                    bcache_cached (fun _ => (mword_of_int 0 : mword 32))
                    = bv_cov V).
      { apply set_eq. intros b. rewrite elem_of_difference. split.
        - intros [Hb _]. exact Hb.
        - intros Hb. split; [exact Hb|]. intros Hc.
          apply bcache_cached_spec in Hc as (j & Hj & ->).
          apply Hnc0. rewrite -Hu0. exact Hb. }
      rewrite Hc0. iExact "Hpool". }
    (* and seal the bcache lock, at its published gname, over the assembled
       resource *)
    iMod (newlock_at E (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V)
            with "Hlkg Hnm Hlkw Hcpu [Hauth Hsa Hslots Hlru Hpool]")
      as "#Hlock".
    { rewrite /bcache_res /bcache_scan.
      iExists ∅, (rev (seq 0 NBUF)),
        (fun _ => (mword_of_int 0 : mword 32)),
        (fun _ => (mword_of_int 0 : mword 32)).
      iFrame "Hauth Hsa".
      iSplitR.
      { iPureIntro. intros k [x Hx]. rewrite lookup_empty in Hx. done. }
      iSplitR.
      { iPureIntro. symmetry. apply Permutation_rev. }
      iSplitR.
      { iPureIntro. intros k1 k2 Hk1 Hk2 Hcov _.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      iSplitR.
      { iPureIntro. intros k1 Hk1 Hcov.
        exfalso. apply Hnc0. rewrite -Hu0. exact Hcov. }
      assert (Hml : map bnode (rev (seq 0 NBUF)) = blist 0 NBUF)
        by (rewrite /blist map_rev //).
      rewrite Hml. iFrame "Hlru Hslots Hpool". }
    (* Split STRUCTURALLY before framing: a bare [iFrame] here searches
       [bio_ctx]'s big-op for each hypothesis (25 s of [BioInv]'s 46 s,
       measured 2026-08-03). *)
    iModIntro. rewrite /bio_ctx.
    iSplitR "Hsf"; [| iExact "Hsf"].
    iSplitL "Hlock"; [iExact "Hlock" |].
    rewrite big_sepL_sep. iSplitL "Hsls"; [iExact "Hsls" | iExact "Hescs"].
  Qed.

End BioInitAt.
