(* SpecIunlock.v -- the public interface of iunlock, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void iunlock(struct inode *ip) {
       if (ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
         panic("iunlock");
       releasesleep(&ip->lock);
     }

   64 bytes, 25 instructions: guard, then release.  ilock's inverse, and the
   PARK half of the icache seam.

   ---- WHAT IT CONSUMES AND WHAT IT GIVES BACK -------------------------

   It consumes exactly what SpecIlock v3 produced -- the checked-out bundle,
   at whatever [(dn', bm')] the holder ended with (a writei between the two
   moves them) -- and it PARKS it, handing the entry sleeplock's variable
   back whole inside releasesleep.  What comes out is the caller's SHARE,
   entire: §13.1d's deposit run backwards, over §14.6's share layer.

   NOTHING IS EXISTENTIAL ANY MORE (v3, design §14.8).  v2 returned
   [∃ q, inode_ref …] -- [ic_swap_park] pinned the arm's [dev] and [inum] off
   the identity halves the holder handed back (§13.1e) but could say nothing
   about the fraction, exactly as [BioInv]'s brelse cannot.  Under the
   checkout DESCRIPTOR the holder carries [IcacheEscrow.ic_deposit fsc_ic k d]
   across its critical section, and one
   [ghost_var_agree] at the park pins the kind, the fraction AND the identity
   at once.  That half is a PREMISE here, and it is not bookkeeping: it is
   what tells this parker's arm from iput's window-exit parker's, which holds
   an otherwise identical bundle (§14.8's two-parkers problem).

   PARKED-MEANS-FLUSHED is the one obligation this contract adds over v1's:
   [ic_loaded] carries [InodeRegion.dinode_at γi inum dn'] at the SAME [dn']
   as the metadata cells, i.e. "park only with the region record retagged to
   the record you are parking" (§13.1d).  Every writer in this kernel ends
   with iupdate -- writei's tail, itrunc's tail -- so a holder can always
   re-establish it, and WITHOUT it iget's eviction could never conclude the
   pool's allocated shape (whose [inode_ok] is about the ON-DISK record)
   from the parked arm's (about the in-memory one).  A reader that never
   writes, like fileread, gets it straight out of ilock (§13.6).

   THE THREE PANIC TESTS ARE ALL DEAD.  [ip == 0] because the entry is slot
   [k] and [IcacheRef.ientry_unsigned] says its address is
   [itable + 24 + 136k]; [ip->ref < 1] by [IcacheInv.iref_live_load_au]
   against [itable_inv], over a LIVENESS SLICE borrowed from the escrow's
   checked-out arm for the duration of that one atomic update ([ic_open_out]
   -- the holder's FULL valid cell is what refutes the other two arms,
   §13.1d), since after ilock's deposit the holder owns nothing of its own.
   v2 borrowed the arm's whole reference; under the descriptor the arm may
   hold only a share, which has no count fragment at all -- but both shapes
   carry a liveness slice, and a slice is all the guard ever needed
   (§14.6);
   [!holdingsleep(&ip->lock)] because the holder's bundle -- the token, the
   lock's pid field and the caller's own pid cell agreeing -- is exactly what
   makes holdingsleep return 1 (SpecHoldingsleep.v is stated in that
   HOLDER's form for this reason).

   iunlock does NOT sleep, so it threads no parking bundle -- but
   releasesleep WAKES every process sleeping on the lock, so wakeup's
   resources ([procs_inv]) are threaded through, exactly as SpecBrelse.v
   does for the same call. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import SleepLock.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import LogInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* iunlock's own frame is 32 bytes (4 slots); its deepest callee is
   releasesleep (22), holdingsleep wanting 16. *)
Notation K_iunlock := (26%nat) (only parsing).
Definition wp_iunlock_dep_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname)
    (gi : gname)
    (gil gisl : gname)
    (logstart : Z)
    (k : nat) (s : Qp) (g : gname) (d : ic_dep) (dev inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlock in
  let ip : mword 64 := ientry k in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlock <= K)%nat ->
  (* THE DESCRIPTOR THE PARK RETIRES (durable-disk B''-tx3), the mirror of
     [SpecIlock.wp_ilock_dep_sconf_body]'s: the conversion back to a
     bundleless arm happens in the SAME ghost step as the park
     ([IcacheEscrow.ic_swap_park_dep]), so no bundleless out-arm stands
     between a disarm/unshed fupd and the release. *)
  ic_dep_shr d = Some (s, dev, inum, g) ->
  (* the entry is slot [k]: a0 = ip, and the null test dies here *)
  (k < NINODE)%nat ->

  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE: iunlock's own [holdingsleep] acquires and
     releases the sleeplock's inner "sleep lock" spinlock internally, so
     the caller must already hold only locks BELOW its rank. *)
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own 0 eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the [ref] words, and the entry's content escrow *)
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs gi fsc_cov logstart k -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k)
                   (slh_tok (icfg_isl k)) -∗
  (* THE HOLDER'S BUNDLE -- the third dead panic test is exactly this *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  proc_priv_bare p pidv Vpr -∗
  (* wakeup's resources (releasesleep wakes the lock's sleepers) *)
  procs_inv gs -∗
  (* THE CHECKED-OUT ENTRY, surrendered back into the escrow.  Exactly
     SpecIlock v3's postcondition, and exactly [ic_swap_park]'s input;
     [ic_loaded]'s [dinode_at] at [dn'] IS the flushed-record obligation, and
     the descriptor half is what selects this holder's own arm (§14.8). *)
  ic_deposit fsc_ic k d -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_dep_held fsc_fs gi fsc_cov logstart d k inum dn' bm' -∗
  (* THE GENERATION'S TYPE WITNESS, back where it came from (design
     fs-icache.md 17.6 (5), ratified 17.7).  [ic_payload]'s TRUE polarity is
     what this park rebuilds, so the witness for the record being parked is
     part of what the parker owes.  Every existing caller threads ilock's
     copy unchanged: none of the five (fileread, filestat, namex, ireclaim,
     iunlockput) alters [di_type], so [dn'] is ilock's [dn]. *)
  ity_shot g (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, back with the payload it rode out on
     (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- the predicate [ic_swap_park] rebuilds --
     now carries [ifreeze_off], so the parker owes it exactly as it owes the
     type witness above.  It costs no caller anything new: this IS the token
     [SpecIlock]'s post handed out, unspent (the one mover that touches it,
     [SpecIupdate.wp_iupdate_link]'s freeze-pin arm, borrows and returns it),
     so every ilock/iunlock pair threads one hypothesis through untouched. *)
  ifreeze_off (bv_unsigned inum) -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b p -∗
      cpu_own 0 eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv_bare p pidv Vpr -∗
      (* the caller's share, back whole, at ITS OWN fraction and device --
         AND AT THE GENERATION IT CAME IN ON.  The share the caller still
         holds is what denies [IcacheRef.live_gen_bump] the slot's whole
         unit, so no recycler can move the generation under it; the erased
         form was a deliberate forget at this boundary and it cost every
         caller the ability to carry an [ity_shot] across its own
         [iunlock]/re-[ilock] window.  A consumer that does not want the
         name applies [IcacheRef.inode_shr_gen_forget] here. *)
      inode_shr_gen k s dev inum g -∗
      (* ...AND WHAT THE ARM PARKED, back: the transaction share at [DepTx],
         nothing at the other two. *)
      ic_dep_side d -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ---- THE TRANSACTIONAL FORM (durable-disk B''-tx) ---------------------
   The generic body at the write arm, with [LogInv.log_tx] handed back whole.
   [ProofIunlock] proves it by DERIVATION ([wp_iunlock_tx_of_dep]): the
   descriptor is retired in the park's own ghost step, so no line of
   iunlock's own proof is re-run. *)
Definition wp_iunlock_tx_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname)
    (gi : gname)
    (gil gisl : gname)
    (logstart : Z)
    (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlock in
  let ip : mword 64 := ientry k in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlock <= K)%nat ->
  (* the entry is slot [k]: a0 = ip, and the null test dies here *)
  (k < NINODE)%nat ->

  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE: iunlock's own [holdingsleep] acquires and
     releases the sleeplock's inner "sleep lock" spinlock internally, so
     the caller must already hold only locks BELOW its rank. *)
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own 0 eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the [ref] words, and the entry's content escrow *)
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs gi fsc_cov logstart k -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k)
                   (slh_tok (icfg_isl k)) -∗
  (* THE HOLDER'S BUNDLE -- the third dead panic test is exactly this *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  proc_priv_bare p pidv Vpr -∗
  (* wakeup's resources (releasesleep wakes the lock's sleepers) *)
  procs_inv gs -∗
  (* THE CHECKED-OUT ENTRY, surrendered back into the escrow.  Exactly
     SpecIlock v3's postcondition, and exactly [ic_swap_park]'s input;
     [ic_loaded]'s [dinode_at] at [dn'] IS the flushed-record obligation, and
     the descriptor half is what selects this holder's own arm (§14.8). *)
  (* ---- THE WRITE ARM COMES HOME (durable-fs-plan.md section 3, [ilock];
     durable-disk B''-tx).  This is the ONLY difference from the generic
     body: the descriptor arrives at [DepTx] with the holder's residue beside
     it ([IcacheEscrow.ic_tx_dep]), and the postcondition hands
     [LogInv.log_tx] back whole.  The park returns exactly the share the
     descriptor recorded, which is what makes the two halves rejoin. *)
  ic_tx_dep fsc_ic k s dev inum g -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded fsc_fs gi fsc_cov logstart k inum dn' bm' -∗
  (* THE GENERATION'S TYPE WITNESS, back where it came from (design
     fs-icache.md 17.6 (5), ratified 17.7).  [ic_payload]'s TRUE polarity is
     what this park rebuilds, so the witness for the record being parked is
     part of what the parker owes.  Every existing caller threads ilock's
     copy unchanged: none of the five (fileread, filestat, namex, ireclaim,
     iunlockput) alters [di_type], so [dn'] is ilock's [dn]. *)
  ity_shot g (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, back with the payload it rode out on
     (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- the predicate [ic_swap_park] rebuilds --
     now carries [ifreeze_off], so the parker owes it exactly as it owes the
     type witness above.  It costs no caller anything new: this IS the token
     [SpecIlock]'s post handed out, unspent (the one mover that touches it,
     [SpecIupdate.wp_iupdate_link]'s freeze-pin arm, borrows and returns it),
     so every ilock/iunlock pair threads one hypothesis through untouched. *)
  ifreeze_off (bv_unsigned inum) -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b p -∗
      cpu_own 0 eb p b lks -∗
      pc_is ret_tgt -∗
      proc_priv_bare p pidv Vpr -∗
      (* the caller's share, back whole, at ITS OWN fraction and device --
         AND AT THE GENERATION IT CAME IN ON.  The share the caller still
         holds is what denies [IcacheRef.live_gen_bump] the slot's whole
         unit, so no recycler can move the generation under it; the erased
         form was a deliberate forget at this boundary and it cost every
         caller the ability to carry an [ity_shot] across its own
         [iunlock]/re-[ilock] window.  A consumer that does not want the
         name applies [IcacheRef.inode_shr_gen_forget] here. *)
      inode_shr_gen k s dev inum g -∗
      (* the transaction's token, whole again *)
      log_tx icfg_log -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE PUBLISHED READING OF THE PARK (durable-disk B''-tx3/-tx4), a
   derivation of the one generic body above. *)
Lemma wp_iunlock_tx_of_dep
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (gs : list gname)
    (gi : gname)
    (gil gisl : gname)
    (logstart : Z)
    (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64)
    (b : bool) (lks : gset string) (Vpr : pprivate) :
  (forall d : ic_dep,
     wp_iunlock_dep_sconf_body gs gi gil gisl logstart k s g d
                               dev inum dn' bm' pidv dq m K eb p b lks Vpr) ->
  wp_iunlock_tx_sconf_body gs gi gil gisl logstart k s g dev inum
                           dn' bm' pidv dq m K eb p b lks Vpr.
Proof.
  cbv beta delta [wp_iunlock_tx_sconf_body wp_iunlock_dep_sconf_body].
  intros Hgen pcE ip ret_tgt HK Hk Ha0 Hbelow.
  iIntros "Hcg Hown Htext Hpc #Hitbl #Hesc Hslk Hslkd Hppid Hprocs
           Hdep Hidev Hiinum Hivalid Hload Hshot Hfrz Hcont".
  iDestruct (ic_tx_dep_at_of_half with "Hdep") as (t) "Hdep".
  rewrite /ic_tx_dep_at. iDestruct "Hdep" as "[Hdep Ht2]".
  iApply (Hgen (DepTx s dev inum g t (1/2)) HK eq_refl Hk Ha0 Hbelow
            with "Hcg Hown Htext Hpc Hitbl Hesc Hslk Hslkd Hppid Hprocs
                  Hdep Hidev Hiinum Hivalid [Hload] Hshot Hfrz [Ht2 Hcont]").
  { rewrite /ic_dep_held /=. iExact "Hload". }
  iIntros (CIDx Hqx mf) "%Hcs Hcg Hown Hpc Hppid Hshr Ht1".
  rewrite /ic_dep_side.
  iApply ("Hcont" $! CIDx Hqx mf with
            "[%] Hcg Hown Hpc Hppid Hshr [Ht1 Ht2]"); [exact Hcs |].
  iApply (log_tx_join icfg_log t with "Ht1 Ht2").
Qed.

Module Type IUNLOCK.
  (* THE GENERIC FORM (durable-disk B''-tx3): one proof of iunlock's code, the
     park's descriptor chosen by the caller.  The published reading below is
     its [DepTx] instance; a READ-locker parks at [DepRd] through it
     directly, which is what retires [ic_unshed_rd] at those two sites. *)
  Parameter wp_iunlock_dep_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname)
      (gi : gname)
      (gil gisl : gname)
      (logstart : Z)
      (k : nat) (s : Qp) (g : gname) (d : ic_dep) (dev inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iunlock_dep_sconf_body gs gi gil gisl logstart k s g d
                                dev inum dn' bm' pidv dq m K eb p b lks Vpr.
  (* the transactional form -- [ProofIunlock] defines it by
     [wp_iunlock_tx_of_dep]. *)
  Parameter wp_iunlock_tx_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (gs : list gname)
      (gi : gname)
      (gil gisl : gname)
      (logstart : Z)
      (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iunlock_tx_sconf_body gs gi gil gisl logstart k s g dev
                               inum dn' bm' pidv dq m K eb p b lks Vpr.
End IUNLOCK.
