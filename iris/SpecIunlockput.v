(* SpecIunlockput.v -- the public interface of iunlockput.

     void iunlockput(struct inode *ip) {
       iunlock(ip);
       iput(ip);
     }

   32 bytes, 14 instructions: a 4-slot frame, [s1 := a0], two [jal]s, the
   epilogue.  NO branch, NO panic, NO memory access of its own -- the whole
   contract is the COMPOSITION of SpecIunlock's and SpecIput's, and the only
   thing this file has to get right is the seam between them.

   ---- THE SEAM: A SHARE COMES BACK, A REFERENCE GOES IN ----------------

   iunlock (v3) returns the caller's SHARE -- [IcacheRef.inode_shr k s dev
   inum] -- because that is what ilock deposited.  iput spends a canonical
   REFERENCE -- [IcacheRef.inode_ref k q dev inum], all three fractions
   equal (design §14.6(1)).  A share is deliberately not spendable, so the
   two do NOT compose on their own.

   What closes the gap is the PARENT the caller kept back when it carved the
   share off for ilock: [IcacheRef.inode_ref_short k (qi + s) qi dev inum].
   [IcacheRef.inode_ref_gather] puts the two halves together into
   [inode_ref k (qi + s) dev inum] at exactly the instruction between the two
   calls, and that is the reference iput consumes.  So the precondition here
   is

     SpecIunlock's precondition  ∗  the retained short parent
                                 ∗  SpecIput's environment,

   and the postcondition is SpecIput's verbatim -- one [iref_slot] back, the
   bitmap possibly smaller, the budget spent-at-most, and NOTHING inode-shaped
   at all: the reference is gone and the caller's pointer is dead.

   This is the shape every namex-style caller has: it ilocks a directory it
   holds a reference to (carving a share), looks a name up, and iunlockputs.
   The carve is [IcacheRef.inode_ref_shed] (or [inode_ref_carve] at a chosen
   fraction); the gather happens INSIDE this function, so a caller never has
   to name [inode_ref_short] again after the call.

   ---- WHAT IS INHERITED VERBATIM ---------------------------------------

   Every premise below is one of the two callees'.  In particular:

   - [trap_csrs_ext eb] / [cpu_claim_ext eb pj] (iput's complement,
     UNCONDITIONAL: iput may truncate and no caller can know in advance
     which arm runs -- see claude-notes/completed/eb-generic-sweep.md);
   - the whole disk/log/bitmap environment, because iput's last-close arm
     truncates;
   - the budget interval [(n - iput_units) <= n' <= n], spend-at-most,
     because iput never holds log.lock;
   - the panic credentials, which BOTH callees carry -- iunlock's three panic tests
     are dead but SpecIunlock still takes the resource, and iput's
     "sched locks" arm diverges through it (design §13.12, Route B).

   iunlockput itself adds nothing: it has no panic, no lock, no memory
   access outside its own frame.  Its stack need is 4 slots on top of iput's
   ([K_iunlockput = 64 = K_iput + 4]; iunlock's 26 is dominated). *)
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
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import FdSlots.
Require Import IcacheRef.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecIput.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.

Local Open Scope Z_scope.

(* ---- THE PARK'S OWN ARM, AS A PURE READING (durable-disk B''-tx5) ------

   iput's three windows -- [IcacheEscrow]'s [DepFrz], its mid-free park and
   its authority-side [ic_held] -- each park a SHARE of the freeing
   transaction's [LogDefs.ln_tx] element, which is what lets a commit refute
   them at an empty authority; [SpecIput.wp_iput_gen_body] therefore takes
   one.  iunlockput needs no caller to supply it: it is [iunlock] then
   [iput], and the share the WRITE ARM parked comes home at the first of the
   two ([IcacheEscrow.ic_dep_side]).  This is that observation as a pure
   equation on the descriptor, so the two generic bodies below can name the
   [(t, q)] without destructing anything. *)
Definition ic_dep_side_tx (d : ic_dep) : option (nat * Qp) :=
  match d with
  | DepTx _ _ _ _ t q => Some (t, q)
  | _ => None
  end.

Section IunlockputSide.
  Context `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, FSC : fscfg}.

  Lemma ic_dep_side_of_tx (d : ic_dep) (t : nat) (q : Qp) :
    ic_dep_side_tx d = Some (t, q) ->
    ic_dep_side d = (t ↪[ln_tx icfg_log]{#q} ())%I.
  Proof.
    destruct d; try discriminate. cbn. intro H.
    injection H as -> ->. reflexivity.
  Qed.
End IunlockputSide.

(* iunlockput's own frame is 32 bytes (4 slots: ra@24 s0@16 s1@8, one hole);
   its deepest callee is iput (60).  iunlock wants 26.

   76 -> 78, forced by [K_iput]'s 72 -> 74 (SpecIput.v's note): the walk calls
   iput at [K - 4], so [K_iput <= K - 4] needs K >= 78.  All eleven
   iunlockput call sites were re-checked and every one has slack (the
   tightest is ProofCreate/ProofSysUnlink at K - 10 / K - 30, i.e. 114). *)
Notation K_iunlockput := (78%nat) (only parsing).
(* =====================================================================  *)
(*  THE CREDITED SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 4b)        *)
(*                                                                        *)
(*  iunlockput is iunlock followed by iput, so this is [SpecIput]'s gen    *)
(*  contract threaded through one wrapper and nothing more.  It is the    *)
(*  form create's arms actually call: [CreateBudget.ip_spend crb cru      *)
(*  true = 0] at [crb = cru = true], and the post above then pins          *)
(*  [n' = n] -- the FAIL arm's freeing [iunlockput] spends nothing.        *)
(* ===================================================================== *)
(* ---- THE GENERIC FORMS (durable-disk B''-tx4) -------------------------
   iunlockput's counted and credited contracts with the park's descriptor
   chosen by the CALLER, exactly as [SpecIunlock.wp_iunlock_dep_sconf_body]
   is for iunlock.  Every published reading below is an instance of one of
   them, so the retirement side of a write lock never leaves a bundleless
   out-state standing across a program step: the descriptor is retired in
   the ghost step that parks the payload
   ([IcacheEscrow.ic_swap_park_dep]).  What the arm parked comes back in the
   post as [IcacheEscrow.ic_dep_side d]. *)
Definition wp_iunlockput_dep_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names)
    (gil gisl : gname)                                 (* ip->lock            *)
    (bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (k : nat) (qi s : Qp) (gy : gname) (d : ic_dep) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat) (tid : nat) (qtx : Qp)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlockput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlockput <= K)%nat ->
  (* THE DESCRIPTOR THE PARK RETIRES (durable-disk B''-tx4), exactly
     [SpecIunlock.wp_iunlock_dep_sconf_body]'s premise: the conversion back
     to a bundleless arm happens in the SAME ghost step as the park
     ([IcacheEscrow.ic_swap_park_dep]), so no descriptor out-state stands
     between a disarm fupd and the release. *)
  ic_dep_shr d = Some (s, dev, inum, gy) ->
  (* ENTRY BY SLOT -- iunlock's null test and iput's [ientry_inj] both *)
  (k < NINODE)%nat ->
  (* --- iput's geometry, threaded verbatim (SpecIput.v) --- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ fsc_cov ->
  ~ (bmapstart ∈ log_region_set fsc_logst) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ fsc_cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set fsc_logst) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below fsc_cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK: "itable" (2), via
     [iput]'s own requirement; iunlock's "sleep lock" (6) is higher and
     follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  (* THE AMBIENT LOG, named (durable-disk B''-tx5): the share this contract
     relays to iput is of [icfg_log]'s element -- the escrow's windows park
     it and have no [log_names] parameter -- so the two must agree.  LAST, so
     no landed positional argument list above it moved; the two published
     [_tx_] readings below already carry the very same equation. *)
  g = icfg_log ->
  (* ...AND THE PARK IS A *WRITE* ARM'S (durable-disk B''-tx5).  iunlockput
     is [iunlock] then [iput], and the share the arm parked comes home at the
     FIRST of the two -- so the share iput's three windows need is the one
     this function has just been handed, and NO CALLER HAS TO FIND ONE.  What
     the premise says is that the descriptor is the write arm, which every
     iunlockput in this kernel is: a read-locker never puts.  Non-vacuity:
     all sixteen direct call sites name a [Xv6Cameras.DepTx]. *)
  ic_dep_side_tx d = Some (tid, qtx) ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view fsc_fs gd dev fsc_cov) -∗
  log_ctx g bn fsc_fs fsc_cov fsc_logst dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst nib dev -∗
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k -∗
  ireg_inv fsc_ireg fsc_fs inodestart nib -∗
  (* THE SEALED REGIME (iclaim-ledger.md §6′, RULING G) -- [SpecIput]'s
     runtime premise verbatim, because iunlockput's whole obligation here is
     iput's.  SPECIALIZED BY SIMP-1, and here the specialization is total:
     no boot thread calls iunlockput at all, so the indexed form had no
     [rg := false] consumer on either of this file's two contracts.  The
     premise is persistent, so nothing comes back. *)
  ireg_open -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k) (slh_tok (icfg_isl k)) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  ic_deposit fsc_ic k d -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_dep_held fsc_fs fsc_ireg fsc_cov fsc_logst d k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, relayed straight to [SpecIunlock]'s
     park (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- what the parked arm holds -- now carries
     [ifreeze_off], so the parker owes it exactly as it owes the type
     witness above.  Every caller has it: it is the token its own
     [ilock] handed over, unspent. *)
  ifreeze_off (bv_unsigned inum) -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* ONE ROW (SIMP-2): the short parent AND its provenance unit.  The
     share [s] above was carved off THIS reference ([inode_refp_carve]);
     iunlock hands the share back and [inode_refp_gather] re-forms the
     canonical [inode_refp k (qi + s)] that iput then spends -- unit still
     attached, because the unit rode with the short parent and never with
     the travelling share (item 7a-wire).  Every caller already holds the
     pair in this shape: it is exactly what [IcacheRef.inode_held_shed]
     leaves behind, and [inode_held_short] is now stated over it. *)
  inode_refp_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
  proc_priv_bare pj pidv Vpr -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* THE BUDGET HALF ONLY: at a [DepTx] descriptor this caller's transaction
     token is part-parked in the escrow, so it cannot present [log_op]; the
     post hands the parked share back as [ic_dep_side d] and the caller
     rejoins it there ([LogInv.log_opb_op]). *)
  log_opb g n -∗
  (* THE CROSSING IS THE LITERAL [true]: iunlockput parks (through iput,
     down to sleep), so it can return on another hart whatever SIE was
     doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_opb g n' -∗
      iref_slot -∗
      (* ...AND WHAT THE ARM PARKED, back: the transaction share at [DepTx],
         nothing at the other descriptors. *)
      ic_dep_side d -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_iunlockput_dep_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names)
    (gil gisl : gname)                                 (* ip->lock            *)
    (bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (k : nat) (qi s : Qp) (gy : gname) (d : ic_dep) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
    (tid : nat) (qtx : Qp)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlockput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlockput <= K)%nat ->
  (* THE DESCRIPTOR THE PARK RETIRES (durable-disk B''-tx4), exactly
     [SpecIunlock.wp_iunlock_dep_sconf_body]'s premise: the conversion back
     to a bundleless arm happens in the SAME ghost step as the park
     ([IcacheEscrow.ic_swap_park_dep]), so no descriptor out-state stands
     between a disarm fupd and the release. *)
  ic_dep_shr d = Some (s, dev, inum, gy) ->
  (* ENTRY BY SLOT -- iunlock's null test and iput's [ientry_inj] both *)
  (k < NINODE)%nat ->
  (* the two absorption credits, threaded verbatim to iput *)
  (crb = true -> bmapstart ∈ Sb) ->
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
  (* --- iput's geometry, threaded verbatim (SpecIput.v) --- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ fsc_cov ->
  ~ (bmapstart ∈ log_region_set fsc_logst) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ fsc_cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set fsc_logst) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below fsc_cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK: "itable" (2), via
     [iput]'s own requirement; iunlock's "sleep lock" (6) is higher and
     follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  (* THE AMBIENT LOG, named (durable-disk B''-tx5): the share this contract
     relays to iput is of [icfg_log]'s element -- the escrow's windows park
     it and have no [log_names] parameter -- so the two must agree.  LAST, so
     no landed positional argument list above it moved; the two published
     [_tx_] readings below already carry the very same equation. *)
  g = icfg_log ->
  (* ...AND THE PARK IS A *WRITE* ARM'S (durable-disk B''-tx5).  iunlockput
     is [iunlock] then [iput], and the share the arm parked comes home at the
     FIRST of the two -- so the share iput's three windows need is the one
     this function has just been handed, and NO CALLER HAS TO FIND ONE.  What
     the premise says is that the descriptor is the write arm, which every
     iunlockput in this kernel is: a read-locker never puts.  Non-vacuity:
     all sixteen direct call sites name a [Xv6Cameras.DepTx]. *)
  ic_dep_side_tx d = Some (tid, qtx) ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view fsc_fs gd dev fsc_cov) -∗
  log_ctx g bn fsc_fs fsc_cov fsc_logst dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst nib dev -∗
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k -∗
  ireg_inv fsc_ireg fsc_fs inodestart nib -∗
  (* THE SEALED REGIME (iclaim-ledger.md §6′, RULING G) -- [SpecIput]'s
     runtime premise verbatim, because iunlockput's whole obligation here is
     iput's.  SPECIALIZED BY SIMP-1, and here the specialization is total:
     no boot thread calls iunlockput at all, so the indexed form had no
     [rg := false] consumer on either of this file's two contracts.  The
     premise is persistent, so nothing comes back. *)
  ireg_open -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k) (slh_tok (icfg_isl k)) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  ic_deposit fsc_ic k d -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_dep_held fsc_fs fsc_ireg fsc_cov fsc_logst d k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, relayed straight to [SpecIunlock]'s
     park (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- what the parked arm holds -- now carries
     [ifreeze_off], so the parker owes it exactly as it owes the type
     witness above.  Every caller has it: it is the token its own
     [ilock] handed over, unspent. *)
  ifreeze_off (bv_unsigned inum) -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* ONE ROW (SIMP-2): the short parent AND its provenance unit.  The
     share [s] above was carved off THIS reference ([inode_refp_carve]);
     iunlock hands the share back and [inode_refp_gather] re-forms the
     canonical [inode_refp k (qi + s)] that iput then spends -- unit still
     attached, because the unit rode with the short parent and never with
     the travelling share (item 7a-wire).  Every caller already holds the
     pair in this shape: it is exactly what [IcacheRef.inode_held_shed]
     leaves behind, and [inode_held_short] is now stated over it. *)
  inode_refp_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
  proc_priv_bare pj pidv Vpr -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* THE GROUP CREDIT, threaded verbatim to iput (SpecIput.v's [crz]):
     [emp] at [crz = false], the walker's [nlz_obs] plus the region's two
     ambient ties at [crz = true]. *)
  (if crz then nlz_obs (bv_unsigned inum) e0 ∗ ⌜g = icfg_log⌝ ∗
                ⌜inodestart = icfg_ist⌝
   else emp) -∗
  (* the reservation, EPOCH-NAMED: [log_opSe] in, [log_opS] out *)
  log_opSe g n Sb e0 -∗
  (* THE CROSSING IS THE LITERAL [true]: iunlockput parks (through iput,
     down to sleep), so it can return on another hart whatever SIE was
     doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      (* THE PAID-BITMAP REPORT (G-4c): [w] is "this call spent the bitmap
         unit", and it comes with the membership that makes a walker's next
         level able to claim [crb := true]. *)
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      (* ...and a CREDITED caller is never charged its own credit back
         (fs-log.md §G.25): at [crb = true] the report is [false], which is
         what makes a walk's next level FREE and not merely bounded. *)
      ⌜crb = true -> w = false⌝ -∗
      ⌜((n - ip_spend_w w cru crz)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      iref_slot -∗
      (* ...AND WHAT THE ARM PARKED, back: the transaction share at [DepTx],
         nothing at the other descriptors. *)
      ic_dep_side d -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ---- THE TRANSACTIONAL FORMS (durable-disk B''-tx) --------------------
   The generic forms with the checkout descriptor at the write arm, closed
   over the transaction id ([IcacheEscrow.ic_tx_dep]) so that no caller names
   one.  [ProofIunlockput] proves both by DERIVATION: the share the arm
   parked comes back in the post and rejoins the caller's residue, so not a
   line of iunlockput's own proof is re-run. *)
Definition wp_iunlockput_tx_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names)
    (gil gisl : gname)                                 (* ip->lock            *)
    (bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlockput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlockput <= K)%nat ->
  (* ENTRY BY SLOT -- iunlock's null test and iput's [ientry_inj] both *)
  (k < NINODE)%nat ->
  (* --- iput's geometry, threaded verbatim (SpecIput.v) --- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ fsc_cov ->
  ~ (bmapstart ∈ log_region_set fsc_logst) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ fsc_cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set fsc_logst) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below fsc_cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK: "itable" (2), via
     [iput]'s own requirement; iunlock's "sleep lock" (6) is higher and
     follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  (* THE AMBIENT LOG, named: the escrow's write arm parks a share of
     [icfg_log]'s element (the escrow has no [log_names] parameter), so a
     contract that re-forms this caller's token has to know the two agree.
     Every caller has it -- it is the walk's own [g = icfg_log] premise. *)
  g = icfg_log ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view fsc_fs gd dev fsc_cov) -∗
  log_ctx g bn fsc_fs fsc_cov fsc_logst dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst nib dev -∗
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k -∗
  ireg_inv fsc_ireg fsc_fs inodestart nib -∗
  (* THE SEALED REGIME (iclaim-ledger.md §6′, RULING G) -- [SpecIput]'s
     runtime premise verbatim, because iunlockput's whole obligation here is
     iput's.  SPECIALIZED BY SIMP-1, and here the specialization is total:
     no boot thread calls iunlockput at all, so the indexed form had no
     [rg := false] consumer on either of this file's two contracts.  The
     premise is persistent, so nothing comes back. *)
  ireg_open -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k) (slh_tok (icfg_isl k)) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  (* THE WRITE ARM COMES HOME (durable-disk B''-tx): the descriptor arrives
     at [DepTx] with the holder's residue beside it, and the disarm --
     iunlockput's own first ghost step -- returns exactly the share it
     recorded. *)
  ic_tx_dep fsc_ic k s dev inum gy -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, relayed straight to [SpecIunlock]'s
     park (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- what the parked arm holds -- now carries
     [ifreeze_off], so the parker owes it exactly as it owes the type
     witness above.  Every caller has it: it is the token its own
     [ilock] handed over, unspent. *)
  ifreeze_off (bv_unsigned inum) -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* ONE ROW (SIMP-2): the short parent AND its provenance unit.  The
     share [s] above was carved off THIS reference ([inode_refp_carve]);
     iunlock hands the share back and [inode_refp_gather] re-forms the
     canonical [inode_refp k (qi + s)] that iput then spends -- unit still
     attached, because the unit rode with the short parent and never with
     the travelling share (item 7a-wire).  Every caller already holds the
     pair in this shape: it is exactly what [IcacheRef.inode_held_shed]
     leaves behind, and [inode_held_short] is now stated over it. *)
  inode_refp_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
  proc_priv_bare pj pidv Vpr -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* THE BUDGET HALF ONLY: this caller's transaction token is HALF-PARKED
     in the escrow, so it cannot present [log_op]; the disarm re-forms the
     whole one inside.  [LogInv.log_opb_op] is the join. *)
  log_opb g n -∗
  (* THE CROSSING IS THE LITERAL [true]: iunlockput parks (through iput,
     down to sleep), so it can return on another hart whatever SIE was
     doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      iref_slot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Definition wp_iunlockput_tx_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names)
    (gil gisl : gname)                                 (* ip->lock            *)
    (bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlockput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlockput <= K)%nat ->
  (* ENTRY BY SLOT -- iunlock's null test and iput's [ientry_inj] both *)
  (k < NINODE)%nat ->
  (* the two absorption credits, threaded verbatim to iput *)
  (crb = true -> bmapstart ∈ Sb) ->
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
  (* --- iput's geometry, threaded verbatim (SpecIput.v) --- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ fsc_cov ->
  ~ (bmapstart ∈ log_region_set fsc_logst) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ fsc_cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set fsc_logst) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below fsc_cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK: "itable" (2), via
     [iput]'s own requirement; iunlock's "sleep lock" (6) is higher and
     follows by [locks_below_mono]. *)
  locks_below lks "log" ->
  (* THE AMBIENT LOG, named: the escrow's write arm parks a share of
     [icfg_log]'s element (the escrow has no [log_names] parameter), so a
     contract that re-forms this caller's token has to know the two agree.
     Every caller has it -- it is the walk's own [g = icfg_log] premise. *)
  g = icfg_log ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view fsc_fs gd dev fsc_cov) -∗
  log_ctx g bn fsc_fs fsc_cov fsc_logst dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst nib dev -∗
  itable_inv -∗
  ic_escrow fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst k -∗
  ireg_inv fsc_ireg fsc_fs inodestart nib -∗
  (* THE SEALED REGIME (iclaim-ledger.md §6′, RULING G) -- [SpecIput]'s
     runtime premise verbatim, because iunlockput's whole obligation here is
     iput's.  SPECIALIZED BY SIMP-1, and here the specialization is total:
     no boot thread calls iunlockput at all, so the indexed form had no
     [rg := false] consumer on either of this file's two contracts.  The
     premise is persistent, so nothing comes back. *)
  ireg_open -∗
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok fsc_ic k) (slh_tok (icfg_isl k)) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked_q gisl s (i_lock ip) pidv -∗
  (* THE WRITE ARM COMES HOME (durable-disk B''-tx): the descriptor arrives
     at [DepTx] with the holder's residue beside it, and the disarm --
     iunlockput's own first ghost step -- returns exactly the share it
     recorded. *)
  ic_tx_dep fsc_ic k s dev inum gy -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ...AND THE INUM'S FREEZE TOKEN, relayed straight to [SpecIunlock]'s
     park (iclaim-ledger.md §3.1 A-custody / §3.9 RULING A-prime).
     [IcacheEscrow.ic_payload] -- what the parked arm holds -- now carries
     [ifreeze_off], so the parker owes it exactly as it owes the type
     witness above.  Every caller has it: it is the token its own
     [ilock] handed over, unspent. *)
  ifreeze_off (bv_unsigned inum) -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* ONE ROW (SIMP-2): the short parent AND its provenance unit.  The
     share [s] above was carved off THIS reference ([inode_refp_carve]);
     iunlock hands the share back and [inode_refp_gather] re-forms the
     canonical [inode_refp k (qi + s)] that iput then spends -- unit still
     attached, because the unit rode with the short parent and never with
     the travelling share (item 7a-wire).  Every caller already holds the
     pair in this shape: it is exactly what [IcacheRef.inode_held_shed]
     leaves behind, and [inode_held_short] is now stated over it. *)
  inode_refp_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv fsc_fs bmapstart fsc_cov fsc_logst size -∗
  proc_priv_bare pj pidv Vpr -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots 3 -∗
  (* THE GROUP CREDIT, threaded verbatim to iput (SpecIput.v's [crz]):
     [emp] at [crz = false], the walker's [nlz_obs] plus the region's two
     ambient ties at [crz = true]. *)
  (if crz then nlz_obs (bv_unsigned inum) e0 ∗ ⌜g = icfg_log⌝ ∗
                ⌜inodestart = icfg_ist⌝
   else emp) -∗
  (* the reservation, EPOCH-NAMED: [log_opSe] in, [log_opS] out *)
  log_opSe g n Sb e0 -∗
  (* THE CROSSING IS THE LITERAL [true]: iunlockput parks (through iput,
     down to sleep), so it can return on another hart whatever SIE was
     doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      (* THE PAID-BITMAP REPORT (G-4c): [w] is "this call spent the bitmap
         unit", and it comes with the membership that makes a walker's next
         level able to claim [crb := true]. *)
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      (* ...and a CREDITED caller is never charged its own credit back
         (fs-log.md §G.25): at [crb = true] the report is [false], which is
         what makes a walk's next level FREE and not merely bounded. *)
      ⌜crb = true -> w = false⌝ -∗
      ⌜((n - ip_spend_w w cru crz)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      (* the transaction's token, whole again *)
      log_tx g -∗
      iref_slot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ---- THE TWO PUBLISHED READINGS OF THE PARK (durable-disk B''-tx4) ----
   Both are instances of the generic bodies above at [DepTx], where the share
   the arm parked comes back in the post and rejoins the caller's residue.
   No disarm fupd stands before the call any more. *)
Section IunlockputOfDep.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_iunlockput_tx_of_dep_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gil gisl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate) :
    (forall (d : ic_dep) (tid : nat) (qtx : Qp),
       wp_iunlockput_dep_sconf_body gs j gl gu gd gk pd pav pu bn g
                                    gil gisl bmapstart
                                    inodestart nib size dev k qi s gy d inum
                                    dn' bm' n tid qtx pidv dq dqb dqs m K eb b lks
                                    Vpr) ->
    wp_iunlockput_tx_sconf_body gs j gl gu gd gk pd pav pu bn g
                                gil gisl bmapstart inodestart nib
                                size dev k qi s gy inum dn' bm' n
                                pidv dq dqb dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iunlockput_tx_sconf_body wp_iunlockput_dep_sconf_body].
    intros Hgen pcE ip pj ret_tgt HK Hk Hgeom Hsz Hbm0 Hbmc Hbml Hist Hcov
      Hnlog Hinlt Hcb Hn Hj Hgl Ha0 Hbelow Hclog.
    iIntros "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hitb2 #Hitbl
             #Hesc Hireg Hropen Hslk Hslkd Hdep Hidev Hiinum Hivalid Hload
             Hshot Hfrz Hshort Hsbb Hsbi Hbmi Hppid Hprocs Hdevi Hdgeom Hdlock
             Hbs Hopb Hcont".
    iDestruct (ic_tx_dep_at_of_half with "Hdep") as (t) "Hdep".
    rewrite /ic_tx_dep_at. iDestruct "Hdep" as "[Hdep Ht2]".
    iApply (Hgen (DepTx s dev inum gy t (1/2)) t (1/2)%Qp HK eq_refl Hk Hgeom Hsz Hbm0
              Hbmc Hbml Hist Hcov Hnlog Hinlt Hcb Hn Hj Hgl Ha0 Hbelow Hclog eq_refl
              with "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hitb2
                    Hitbl Hesc Hireg Hropen Hslk Hslkd Hdep Hidev Hiinum
                    Hivalid [Hload] Hshot Hfrz Hshort Hsbb Hsbi Hbmi Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hbs Hopb [Ht2 Hcont]").
    { rewrite /ic_dep_held /=. iExact "Hload". }
    iIntros (CIDx Hqx mf n') "%Hcs Hcg Hown Hextc Hextm Hpc Hppid Hsbb Hsbi
             Hbs %Hbnd Hopb Hslot Ht1".
    rewrite /ic_dep_side.
    iDestruct (log_tx_join icfg_log t with "Ht1 Ht2") as "Htx".
    iEval (rewrite -Hclog) in "Htx".
    iApply ("Hcont" $! CIDx Hqx mf n' with
              "[%] Hcg Hown Hextc Hextm Hpc Hppid Hsbb Hsbi Hbs [%]
               [Hopb Htx] Hslot"); [exact Hcs | exact Hbnd |].
    iApply (log_opb_op with "Hopb Htx").
  Qed.

  Lemma wp_iunlockput_tx_of_dep_gen
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gil gisl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate) :
    (forall (d : ic_dep) (tid : nat) (qtx : Qp),
       wp_iunlockput_dep_gen_body gs j gl gu gd gk pd pav pu bn g
                                  gil gisl bmapstart
                                  inodestart nib size dev k qi s gy d inum
                                  dn' bm' n Sb crb cru crz e0 tid qtx
                                  pidv dq dqb dqs m K eb b lks Vpr) ->
    wp_iunlockput_tx_gen_body gs j gl gu gd gk pd pav pu bn g
                              gil gisl bmapstart inodestart nib
                              size dev k qi s gy inum dn' bm' n Sb crb cru
                              crz e0 pidv dq dqb dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iunlockput_tx_gen_body wp_iunlockput_dep_gen_body].
    intros Hgen pcE ip pj ret_tgt HK Hk Hcrb0 Hcru0 Hgeom Hsz Hbm0 Hbmc Hbml
      Hist Hcov Hnlog Hinlt Hcb Hn Hj Hgl Ha0 Hbelow Hclog.
    iIntros "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hitb2 #Hitbl
             #Hesc Hireg Hropen Hslk Hslkd Hdep Hidev Hiinum Hivalid Hload
             Hshot Hfrz Hshort Hsbb Hsbi Hbmi Hppid Hprocs Hdevi Hdgeom Hdlock
             Hbs Hcr Hops Hcont".
    iDestruct (ic_tx_dep_at_of_half with "Hdep") as (t) "Hdep".
    rewrite /ic_tx_dep_at. iDestruct "Hdep" as "[Hdep Ht2]".
    iApply (Hgen (DepTx s dev inum gy t (1/2)) t (1/2)%Qp HK eq_refl Hk Hcrb0 Hcru0 Hgeom
              Hsz Hbm0 Hbmc Hbml Hist Hcov Hnlog Hinlt Hcb Hn Hj Hgl Ha0
              Hbelow Hclog eq_refl
              with "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hitb2
                    Hitbl Hesc Hireg Hropen Hslk Hslkd Hdep Hidev Hiinum
                    Hivalid [Hload] Hshot Hfrz Hshort Hsbb Hsbi Hbmi Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hbs Hcr Hops [Ht2 Hcont]").
    { rewrite /ic_dep_held /=. iExact "Hload". }
    iIntros (CIDx Hqx mf n' Sb' w) "%Hcs Hcg Hown Hextc Hextm Hpc Hppid Hsbb
             Hsbi Hbs %Hsub %Hw %Hcrb %Hnn Hops Hslot Ht1".
    rewrite /ic_dep_side.
    iDestruct (log_tx_join icfg_log t with "Ht1 Ht2") as "Htx".
    iEval (rewrite -Hclog) in "Htx".
    iApply ("Hcont" $! CIDx Hqx mf n' Sb' w with
              "[%] Hcg Hown Hextc Hextm Hpc Hppid Hsbb Hsbi Hbs [%] [%] [%]
               [%] Hops Htx Hslot");
      [exact Hcs | exact Hsub | exact Hw | exact Hcrb | exact Hnn].
  Qed.
End IunlockputOfDep.


Module Type IUNLOCKPUT.
  (* THE GENERIC FORM (durable-disk B''-tx4): one proof of iunlockput's code,
     the park's descriptor chosen by the caller.  The two published readings
     below are its [DepTx] instances.  The sconf reading of the generic form
     is NOT published: its only application is inside [ProofIunlockput], where
     it is a [Local Lemma] discharging [wp_iunlockput_tx_sconf]. *)
  Parameter wp_iunlockput_dep_gen :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gil gisl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (qi s : Qp) (gy : gname) (d : ic_dep) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (tid : nat) (qtx : Qp)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iunlockput_dep_gen_body gs j gl gu gd gk pd pav pu bn g
                                 gil gisl bmapstart inodestart
                                 nib size dev k qi s gy d inum dn' bm' n Sb
                                 crb cru crz e0 tid qtx pidv dq dqb dqs m K eb b lks
                                 Vpr.
  (* the two TRANSACTIONAL forms (durable-disk B''-tx); [ProofIunlockput]
     defines them by [wp_iunlockput_tx_of_sconf] / [_of_gen]. *)
  Parameter wp_iunlockput_tx_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gil gisl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iunlockput_tx_sconf_body gs j gl gu gd gk pd pav pu bn g
                                  gil gisl bmapstart inodestart
                                  nib size dev k qi s gy inum dn' bm' n
                                  pidv dq dqb dqs m K eb b lks Vpr.
  Parameter wp_iunlockput_tx_gen :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, FSC : fscfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names)
      (gil gisl : gname)
      (bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iunlockput_tx_gen_body gs j gl gu gd gk pd pav pu bn g
                                gil gisl bmapstart inodestart nib
                                size dev k qi s gy inum dn' bm' n Sb crb cru
                                crz e0 pidv dq dqb dqs m K eb b lks Vpr.
End IUNLOCKPUT.
