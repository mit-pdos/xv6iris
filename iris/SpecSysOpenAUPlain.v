(* SpecSysOpenAUPlain.v -- the PLAIN half of [SpecSysOpenAU.SYSOPEN_AU],
   sealed on its own.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A leaf, and a temporary one: it exists because the campaign's
   sealed module type carries BOTH arms and the O_CREATE arm is a separate
   (and much larger) piece of work -- it needs a T_FILE-carrying create-AU,
   and [SpecCreateAU] is T_DEVICE-pinned by construction (its header,
   difference (2)).  Sealing the two arms independently is what lets the
   plain arm -- init's [open("console", O_RDWR)], the driving consumer --
   land as a theorem now rather than wait.

   NOTHING IS RESTATED.  The parameter's statement IS
   [SpecSysOpenAU.wp_sys_open_au_plain_body], byte for byte the same body
   the full seal names; [SYSOPEN_AU] is this module type plus the create
   parameter, so an implementation of the full seal implements this one and
   the two never diverge.  Delete this file when the create arm lands. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import FdSlots.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import ProcDefs.
Require Import Xv6G.
Require Import SpecSysOpenAU.
Require Import FsAbs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

Module Type SYSOPEN_AU_PLAIN.
  Parameter wp_sys_open_au_plain :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γfl γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ),
      wp_sys_open_au_plain_body γfl γf gs j gl pd pav pu ns
        dqb dqs dqbs dqn v vom pid U m K eb b lks P Pmiss Φo Φt.
End SYSOPEN_AU_PLAIN.
