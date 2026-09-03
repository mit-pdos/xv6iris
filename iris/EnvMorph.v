(* EnvMorph.v -- THE PARKED ENVIRONMENT'S TRANSPORT OBLIGATIONS.

   The kernel environment a parked process carries across a context change
   is a handful of persistent BUNDLES -- the file system's frozen
   superblock cells, the bcache and icache handles, the device complement,
   the syscall park's extras and the whole park world.  Each of them owes
   [TsoCtx.CtxMorph] for the same reason a lock payload does: a hart that
   resumes at a new context has to re-state every row of its environment
   there, and [ctx_dom] is what pays for it.

   THE ROWS ARE ALL STRUCTURAL, which is the point of this file: nothing
   here invents a law.  Each proof unfolds ONE bundle and hands the walk to
   [CtxMorphTac.ctx_morph_solve], whose head dispatch stops at the named
   pieces -- the lock handles ([SchedCtx.is_lock_morph]), the sleeplock
   handles ([SleepLock.is_sleeplock_genl_morph]), the payload λs
   ([BioInv.bslp_morph], [IcacheEscrow.ic_slp_morph],
   [DiskInv.disk_res_at_morph], [TicksInv.ticks_res_at_morph]) and the
   console/disk rows already proved in [ConsoleInv] / [DiskInv] /
   [SpecMainSecondary] -- and closes them by their own instances.  A bundle
   whose every conjunct is ξ-free closes on [ctx_morph_const] alone.

   WHY A SEPARATE FILE.  These are cross-cutting: [devintr_caps_any] is
   [UsertrapRes]', [park_world] is [SyscParkEnv]', [fs_sb_cells] is
   [FsReady]', and the pieces they need are spread over the icache, the
   bcache and the scheduler.  Stating them where they are defined would
   drag each of those files below the others; stating them here costs one
   row in [_CoqProject] and no rebuild of anybody's cone.

   THIS FILE DECLARES NO [CurCtx], deliberately (the rule the payload
   sections carry): every statement spells [X (XI := ξ)] under an explicit
   λ, and with no ambient in scope a forgotten annotation is an elaboration
   error rather than a silent capture. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap gset frac.
From iris.base_logic.lib Require Import own invariants ghost_map ghost_var.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import TsoCtx CtxMorphTac.
Require Import Xv6Cameras.
Require Import WpUart.      (* [uart_names] *)
Require Import DiskPtsto.   (* [disk_names] *)
Require Import IcacheRef.   (* [ic_names] / the [icfg] class *)
Require Import TicksInv.
Require Import Xv6G.        (* the [xv6G] bundle -- NAMED in the section
                               binders below, so it must be IMPORTED, not
                               merely required: an unresolved class name
                               inside a generalising binder becomes a fresh
                               variable instead of an error. *)
Require Import FdSlots FileInvDefs.  (* [fdslotG] / [fileG], same rule *)
Require Import IrefSlots.
Require Import ProcAvail.
Require Import UsertrapRes SyscParkEnv.

(* ===================================================================== *)
(*  1.  The single-handle rows                                            *)
(* ===================================================================== *)
Section EnvHandles.
  Context `{!riscvGS Σ, !lockG Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

  (* the ticks lock: a handle over the closed payload [ticks_res_at], so
     only the handle moves. *)
  Global Instance is_tickslock_morph (γl : gname) :
    CtxMorph (λ ξ : CtxId, (is_tickslock (XI := ξ) γl : iProp Σ)).
  Proof. rewrite /is_tickslock. ctx_morph_solve. Qed.
End EnvHandles.

(* ===================================================================== *)
(*  2.  The bcache and icache bundles                                     *)
(* ===================================================================== *)
Section EnvCaches.
  Context `{!riscvGS Σ, !lockG Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.


  (* NO [ic_sleeplocks_morph] AND NO [is_itable2_morph] ROW HERE any more
     (r25 pass 1, plan item 33): both live in [IcacheEscrow.v], beside the
     definitions they close over.  This file is registered AFTER [FsReady.v]
     and imports it, so [FsReady.fs_ready_morph] -- which needs both rows --
     could never see a copy stated here. *)

End EnvCaches.

(* ===================================================================== *)
(*  3.  The device complement and the park's world                        *)
(* ===================================================================== *)
Section EnvPark.
  Context `{!riscvGS Σ, !lockG Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.

  (* the six rows a devintr caller needs: the device invariants (ξ-free),
     the console capabilities ([SpecMainSecondary.console_caps_morph]), the
     disk geometry cells ([DiskInv.disk_geom_morph]), the vdisk lock's
     handle over [disk_res_at], the ticks lock and the process table. *)
  Global Instance devintr_caps_any_morph (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname) (γs : list gname)
      (pd pav pu : SailStdpp.Values.mword 64) :
    CtxMorph (λ ξ : CtxId,
      (devintr_caps_any (XI := ξ) γu γv γdk γtl γs pd pav pu : iProp Σ)).
  Proof. rewrite /devintr_caps_any. ctx_morph_solve. Qed.

  (* the syscall park's extras: the nextpid lock's handle under its gname
     existential, the sealed slot ledger (an invariant, ξ-free), the ticks
     lock and the console. *)
  Global Instance sysc_park_extra_morph (γtk : gname) :
    CtxMorph (λ ξ : CtxId, (sysc_park_extra (XI := ξ) γtk : iProp Σ)).
  Proof. rewrite /sysc_park_extra. ctx_morph_solve. Qed.

  (* the whole park world: [devintr_caps_any]'s six rows spelled out, the
     console, [sysc_park_extra]'s other two, the PLIC wire invariant, the
     trampoline claim (a [kmap_at], ξ-free) and the [initproc] cell. *)
  Global Instance park_world_morph (γs : list gname) :
    CtxMorph (λ ξ : CtxId, (park_world (XI := ξ) γs : iProp Σ)).
  Proof. rewrite /park_world. ctx_morph_solve. Qed.
End EnvPark.

(* ===================================================================== *)
(*  4.  The process descriptor's memory row                               *)
(* ===================================================================== *)
Section EnvProcPt.
  Context `{!riscvGS Σ}.
End EnvProcPt.
