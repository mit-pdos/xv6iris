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
   imports, and its one caller ([FsBoot.fs_boot_bundle]) has no consumer yet.
   The two bodies are duplicated until that caller moves over. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac ufrac numbers agree gmultiset.
From stdpp Require Import gmultiset.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import SleepLock.
Require Import WpLockAt.
Require Import SleepLockAt.
Require Import BufOwn.
Require Import BcacheInv.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtxPark.
(* CtxAnchor: dead in box v2 *)
Require Export BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SepThread.   (* A6.68: the token threaded through the NBUF *)
Require Import Xv6G.
Local Open Scope Z_scope.

Section BioInitAt.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (*  The free state of a [bio_names] record                              *)
  (* ------------------------------------------------------------------ *)

  (* No buffer holds a reference (the count authority is empty), the whole
     slot supply is unspent, the bcache spinlock and every buffer sleeplock
     are unbuilt, and every checkout / recycle token is idle. *)
  Definition bio_free_tok (bn : bio_names) : iProp Σ :=
    (lock_free_tok (bn_lk bn) ∗
     own (bn_auth bn) (● (∅ : gmap nat (option Qp * positive)) : bioUR) ∗
     bslots_auth ∗
     bslots BSLOTS_FS ∗
     ([∗ list] k ∈ seq 0 NBUF,
        sl_free_pair (bn_slk bn k) ∗
        lock_tok_excl (bn_own bn k) ∗
        lock_tok_excl (bn_mid bn k)) ∗
     (* BOX v2: the stamped-shares authority (empty), the park register's
        two halves at 0, the drop register whole at (0, closed), the count's
        two halves at 0 *)
     ([∗ list] k ∈ seq 0 NBUF,
        own (bn_pres bn k) (● (∅ : gmapUR (bio_id * nat) ufracR)) ∗
        (ghost_var (bn_regp bn k) (1/2) (L2Reg 0 None : l2_reg bio_id) ∗
         ghost_var (bn_regp bn k) (1/2) (L2Reg 0 None : l2_reg bio_id)) ∗
        ghost_var (bn_regd bn k) 1
          (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None : slot_reg bio_id bio_x) ∗
        (bcnt_var (bn_regc bn k) 0 ∗ bcnt_var (bn_regc bn k) 0)))%I.

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

  (* the box ghosts, minted as four functions by one induction *)
  Local Lemma bio_box_ghost_alloc (n j : nat) :
    ⊢ |==> ∃ fs fp fd fc : nat -> gname,
        [∗ list] k ∈ seq j n,
          own (fs k) (● (∅ : gmapUR (bio_id * nat) ufracR)) ∗
          (ghost_var (fp k) (1/2) (L2Reg 0 None : l2_reg bio_id) ∗
           ghost_var (fp k) (1/2) (L2Reg 0 None : l2_reg bio_id)) ∗
          ghost_var (fd k) 1
            (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None : slot_reg bio_id bio_x) ∗
          (bcnt_var (fc k) 0 ∗ bcnt_var (fc k) 0).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant), (fun _ => inhabitant),
        (fun _ => inhabitant), (fun _ => inhabitant). cbn [seq]. done. }
    iMod (own_alloc (● (∅ : gmapUR (bio_id * nat) ufracR))) as (γs) "Hs"; [by apply auth_auth_valid|].
    iMod (ghost_var_alloc (L2Reg 0 None : l2_reg bio_id)) as (γp) "Hp".
    iMod (ghost_var_alloc (SlotReg 0 false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None
                             : slot_reg bio_id bio_x)) as (γd) "Hd".
    iMod (ghost_var_alloc (ghost_varG0 := kalloc_count_inG) 0%nat) as (γc) "Hc".
    iMod ("IH" $! (S j)) as (fs fp fd fc) "Hf".
    iModIntro.
    iExists (fun k => if decide (k = j) then γs else fs k),
            (fun k => if decide (k = j) then γp else fp k),
            (fun k => if decide (k = j) then γd else fd k),
            (fun k => if decide (k = j) then γc else fc k).
    rewrite bio_at_seq_cons. iSplitL "Hs Hp Hd Hc".
    { case_decide as Hdd; [| congruence].
      iEval (rewrite -{1}Qp.half_half) in "Hp". iDestruct "Hp" as "[Hp1 Hp2]".
      rewrite /bcnt_var. iEval (rewrite -{1}Qp.half_half) in "Hc". iDestruct "Hc" as "[Hc1 Hc2]".
      iFrame "Hs Hp1 Hp2 Hd Hc1 Hc2". }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hdd; [exfalso; lia | done].
  Qed.

  Lemma bio_names_ghost_alloc :
    bslots_auth -∗ bslots BSLOTS_FS -∗ |==> ∃ bn : bio_names, bio_free_tok bn.
  Proof.
    iIntros "Hsa Hsf".
    iMod lock_ghost_alloc as (γlk) "Hlk".
    iMod (own_alloc (● (∅ : gmap nat (option Qp * positive)) : bioUR)) as (γb) "Hauth".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iMod (bio_buf_ghost_alloc NBUF 0) as (f) "Hbufs".
    iMod (bio_box_ghost_alloc NBUF 0) as (fstm fregp fregd fregc) "Hregs".
    iModIntro.
    (* the anchor / pile gname families are DEAD in box v2: any gname does *)
    iExists (MkBioNames γlk γb (fun k => (f k).1.1) (fun k => (f k).1.2)
                        (fun k => (f k).2) (fun k => (f k).1.2) fstm fregp fregd
                        (fun k => (f k).1.2) fregc).
    rewrite /bio_free_tok /bslots_auth /bslots.
    cbn [bn_lk bn_auth bn_slk bn_own bn_mid bn_anc bn_pres bn_regp bn_regd bn_regc bn_pile].
    iFrame "Hlk Hauth Hsa Hsf Hbufs Hregs".
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
  (* A6.68: the honest creator deposit (A6.66) wants the running token; the
     NBUF sleeplock loop threads it with [SepThread.big_sepL_fupd_thread]
     because [own_context] is EXCLUSIVE ([BioInv.bio_init]'s shape). *)
  Lemma bio_init_at `{CID : RiscvLang.CpuId} (bn : bio_names) (V : bio_view Σ) E :
    (0 ∉ bv_cov V) ->
    own_context cur_ctx -∗
    bio_free_tok bn -∗
    bcache_addr ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name bcache_addr "bcache"%string -∗
    WpLock.lk_cpu_ready bcache_addr -∗
    ([∗ list] k ∈ seq 0 NBUF, sl_fresh (buf_lock (bnode k)) "buffer"%string) -∗
    ([∗ list] k ∈ seq 0 NBUF, buf_raw k) -∗
    bcache_lru bhead (blist 0 NBUF) -∗
    ([∗ set] b ∈ bv_cov V, pool_blk V b) ={E}=∗
    own_context cur_ctx ∗ bio_ctx bn V ∗ bslots BSLOTS_FS.
  Proof.
    iIntros (Hnc0) "Hrun (Hlkg & Hauth & Hsa & Hsf & Hbg & Hregs) Hlkw #Hnm Hcpu Hfresh Hbufs Hlru Hpool".
    assert (Hu0 : uint (mword_of_int 0 : mword 32) = 0)
      by (vm_compute; reflexivity).
    iEval (rewrite !big_sepL_sep) in "Hregs".
    iDestruct "Hregs" as "[Hstm [[Hregp1 Hregp2] [Hregd [Hregc1 Hregc2]]]]".
    (* every buffer's sleeplock, at its published gname pair, over the λ
       payload at park stamp 0 (ENDGAME R1-pre / box v2) *)
    iDestruct (big_sepL_sep_2 with "Hfresh Hbg") as "Hsl".
    iDestruct (big_sepL_sep_2 with "Hsl Hregp1") as "Hsl".
    iAssert ([∗ list] idx↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗
               ((sl_fresh (buf_lock (bnode k)) "buffer"%string ∗
                 (sl_free_pair (bn_slk bn k) ∗ lock_tok_excl (bn_own bn k) ∗
                  lock_tok_excl (bn_mid bn k))) ∗
                ghost_var (bn_regp bn k) (1/2) (L2Reg 0 None : l2_reg bio_id))
               ={E}=∗ own_context cur_ctx ∗
               is_sleeplock_genl (fst (bn_slk bn k)) (snd (bn_slk bn k))
                 (buf_lock (bnode k)) "buffer"%string (bslp bn k) sl_untracked)%I
      as "Hstep".
    { iApply big_sepL_intro. iIntros "!>" (idx k Hk) "Hrun [[Hf (Hp & Ho & _)] Hrp]".
      iMod (sl_fresh_new_genl_at2 E (bn_slk bn k) (buf_lock (bnode k))
              "buffer"%string (bslp bn k) sl_untracked with "Hp Hf Hrun [Ho Hrp]") as "[Hrun Hlk]".
      { rewrite /bslp /bslp_raw. iFrame "Ho". iExists (L2Reg 0 None). iFrame "Hrp".
        iSplitR; [done|]. simpl. iApply TsoCtx.ctx_floor_0. }
      iModIntro. iFrame "Hrun Hlk". }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx)
            with "Hrun Hstep Hsl") as "[Hrun #Hsls]".
    assert (Hpay0 : forall k bs,
        buf_pay (XI := cur_ctx) bn V k false (mword_of_int 0 : mword 32)
          (mword_of_int 0 : mword 32) bs = emp%I).
    { intros k bs. rewrite /buf_pay. case_decide as Hd; [|reflexivity].
      exfalso. apply Hnc0. rewrite -Hu0. exact Hd. }
    (* every buffer: the content is deposited into its box; the slot keeps
       the bcache half of dev/blockno and the count *)
    iDestruct (big_sepL_sep_2 with "Hstm Hregp2") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregd") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hap Hregc1") as "Hap".
    iDestruct (big_sepL_sep_2 with "Hregc2 Hbufs") as "Hslr".
    iDestruct (big_sepL_sep_2 with "Hap Hslr") as "Hall".
    iAssert ([∗ list] i↦k ∈ seq 0 NBUF,
               own_context cur_ctx -∗ emp ={E}=∗
               own_context cur_ctx ∗
               (buf_box bn V k ∗
                ∃ Td : nat, llb loglen_name Td ∗
                  (reg_drop bn k (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None) ∗
                   (brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
                    reg_cnt bn k 0 ∗
                    b_dev (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) ∗
                    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32)))))%I
      with "[Hall]" as "Hstep2".
    { iApply (big_sepL_impl with "Hall").
      iIntros "!>" (i k Hk). rewrite /buf_raw.
      iIntros "[(((Hst & Hrp) & Hrd) & Hc) [Hc2 (Hv & Hdk & Hdev & Hbno & Hrc & Hdata)]] Hrun _".
      iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdev1 Hdev2]".
      iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbno1 Hbno2]".
      iMod (buf_box_alloc E bn V k with "Hrun Hst Hc Hrp [Hrd] Hv Hdev1 Hbno1 Hdk [Hdata]")
        as "(Hrun & #Hbx & Hreg)".
      { iExists _. iExact "Hrd". }
      { iDestruct "Hdata" as (bs) "[%Hlen Hdata]". iExists bs. iFrame "Hdata".
        iSplitR; [done|]. rewrite Hpay0. done. }
      iModIntro. iFrame "Hrun". iSplitR; [iExact "Hbx"|].
      iDestruct "Hreg" as (Td) "[Hrd0 #Hllb]". iExists Td. iFrame "Hllb Hrd0".
      iFrame "Hrc Hc2 Hdev2 Hbno2". }
    iAssert ([∗ list] i↦k ∈ seq 0 NBUF, emp)%I as "Hemp".
    { rewrite big_sepL_emp. iEmpIntro. }
    iMod (big_sepL_fupd_thread E (own_context cur_ctx) (fun _ _ => emp%I)
            with "Hrun Hstep2 Hemp") as "[Hrun Hboth]".
    iEval (rewrite big_sepL_sep) in "Hboth".
    iDestruct "Hboth" as "[#Hboxs Hslots0]".
    iDestruct (CtxBox.big_sepL_llb_max (seq 0 NBUF)
                 (fun k Td => reg_drop bn k (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None) ∗
                              (brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
                               reg_cnt bn k 0 ∗
                               b_dev (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32) ∗
                               b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (mword_of_int 0 : mword 32)))%I
                 with "Hslots0") as (tl) "[#Hllbtl Hslots0]".
    iAssert ([∗ list] k ∈ seq 0 NBUF,
               bio_slot_res2 bn V ∅ k (mword_of_int 0 : mword 32)
                 (mword_of_int 0 : mword 32) tl cur_ctx)%I
      with "[Hslots0]" as "Hslots".
    { iApply (big_sepL_mono with "Hslots0"). intros i k _.
      iIntros "(%Td & %Hb & #Hl & Hrd & Hslot)".
      rewrite /bio_slot_res2 lookup_empty.
      iSplitL "Hrd".
      { iExists (SlotReg Td false (mword_of_int 0 : mword 32, mword_of_int 0 : mword 32) None).
        iFrame "Hrd Hl". iPureIntro. cbn. split_and!; [done | done | done | exact Hb]. }
      iExact "Hslot". }
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
    (* the bcache lock at its published gname, minted WITH the fold at the
       boot floor slot *)
    iMod (newlock_at_llb E (bn_lk bn) bcache_addr "bcache"%string
            (fun ξ => bcache_res2 bn V ξ)
            (fun ξ => llb loglen_name tl ∗
                      bcache_scan2 bn V ∅ (rev (seq 0 NBUF))
                        (fun _ => (mword_of_int 0 : mword 32))
                        (fun _ => (mword_of_int 0 : mword 32)) tl ξ)%I tl
            (bcache_res2_fold_in bn V ∅ (rev (seq 0 NBUF))
               (fun _ => (mword_of_int 0 : mword 32))
               (fun _ => (mword_of_int 0 : mword 32)) tl)
            with "Hlkg Hnm Hrun Hlkw Hcpu Hllbtl [Hauth Hsa Hslots Hlru Hpool]")
      as "[Hrun #Hlock]".
    { iFrame "Hllbtl". rewrite /bcache_scan2.
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
    iModIntro. iSplitL "Hrun"; [iExact "Hrun" |]. rewrite /bio_ctx.
    iSplitR "Hsf"; [| iExact "Hsf"].
    iSplitL "Hlock"; [iExact "Hlock" |].
    rewrite big_sepL_sep. iSplitL "Hsls"; [iExact "Hsls" | iExact "Hboxs"].
  Qed.

End BioInitAt.
