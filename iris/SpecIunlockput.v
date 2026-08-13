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
   - [panic_wp_any], which BOTH callees carry -- iunlock's three panic tests
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
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import FdSlots.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import SchedCtx.
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
Import Defs.

Local Open Scope Z_scope.

(* iunlockput's own frame is 32 bytes (4 slots: ra@24 s0@16 s1@8, one hole);
   its deepest callee is iput (60).  iunlock wants 26. *)
Definition K_iunlockput : nat := 64%nat.

Definition wp_iunlockput_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names)                                    (* the icache's names  *)
    (gtl : gname)                                      (* itable.lock         *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlockput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlockput <= K)%nat ->
  (* ENTRY BY SLOT -- iunlock's null test and iput's [ientry_inj] both *)
  (k < NINODE)%nat ->
  (* --- iput's geometry, threaded verbatim (SpecIput.v) --- *)
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked gisl -∗
  sl_pid (i_lock ip) ↦₄ pidv -∗
  ic_deposit cn k (DepShr s dev inum gy) -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded gfs gi cov logstart k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* the share [s] above was carved off THIS reference ([inode_ref_carve]);
     iunlock hands the share back and [inode_ref_gather] re-forms the
     canonical [inode_ref k (qi + s)] that iput then spends. *)
  inode_ref_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots bn 3 -∗
  log_op g n -∗
  (* THE CROSSING IS THE LITERAL [true]: iunlockput parks (through iput,
     down to sleep), so it can return on another hart whatever SIE was
     doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      bslots bn 3 -∗
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      iref_slot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* =====================================================================  *)
(*  THE CREDITED SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 4b)        *)
(*                                                                        *)
(*  iunlockput is iunlock followed by iput, so this is [SpecIput]'s gen    *)
(*  contract threaded through one wrapper and nothing more.  It is the    *)
(*  form create's arms actually call: [CreateBudget.ip_spend crb cru      *)
(*  true = 0] at [crb = cru = true], and the post above then pins          *)
(*  [n' = n] -- the FAIL arm's freeing [iunlockput] spends nothing.        *)
(* ===================================================================== *)
Definition wp_iunlockput_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names)                                    (* the icache's names  *)
    (gtl : gname)                                      (* itable.lock         *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
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
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* the trap-CSR complement, threaded straight from iput's own precondition
     (SpecIput.v): [emp] at [eb = true], where iput's own acquire mints what
     its interior sleeps need; the real pair at [eb = false], where the
     caller holds it because the TRAP gave it to it.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* ---- THE HOLDER'S BUNDLE (SpecIunlock's precondition) ---- *)
  sleeplocked gisl -∗
  sl_pid (i_lock ip) ↦₄ pidv -∗
  ic_deposit cn k (DepShr s dev inum gy) -∗
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded gfs gi cov logstart k inum dn' bm' -∗
  (* the parked record's type witness -- SpecIunlock's new premise, threaded
     verbatim (design fs-icache.md 17.6 (5), ratified 17.7) *)
  ity_shot gy (di_type dn') -∗
  (* ---- THE RETAINED PARENT: what makes the seam close ---- *)
  (* the share [s] above was carved off THIS reference ([inode_ref_carve]);
     iunlock hands the share back and [inode_ref_gather] re-forms the
     canonical [inode_ref k (qi + s)] that iput then spends. *)
  inode_ref_short k (qi + s)%Qp qi dev inum -∗
  (* ---- iput's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  bslots bn 3 -∗
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
  ∀ (mf : regfile) (n' : nat) (used' Sb' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      bslots bn 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜((n - ip_spend_max crb cru crz)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      iref_slot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUNLOCKPUT.
  Parameter wp_iunlockput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iunlockput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                               gil gisl cov logstart bmapstart inodestart nib
                               size dev used k qi s gy inum dn' bm' n
                               pidv dq dqb dqs m K eb C b.
  (* the credited set-form contract; [wp_iunlockput_sconf] is this at
     [crb := cru := crz := false], derived at the [log_op] existential's own
     witness and at the birth epoch [LogInv.log_opS_named] opens. *)
  Parameter wp_iunlockput_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (qi s : Qp) (gy : gname) (inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iunlockput_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                             gil gisl cov logstart bmapstart inodestart nib
                             size dev used k qi s gy inum dn' bm' n Sb crb cru
                             crz e0 pidv dq dqb dqs m K eb C b.
End IUNLOCKPUT.
