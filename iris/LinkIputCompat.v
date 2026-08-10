(* LinkIputCompat.v -- THE ONE BRIDGING AXIOM, and the file C6b deletes.
   =====================================================================

   WHAT THIS ASSERTS, EXACTLY.  One [Axiom]: that iput satisfies
   [SpecIput.wp_iput_sconf_body], the FROZEN v1 statement -- the one whose
   precondition surrenders [ProcInv.cwd_ref ip] and whose postcondition
   returns the pid cell, the three buffer slots and a spend-at-most
   [log_op] interval.  Nothing else.

   WHY IT IS NOT A THEOREM.  iput IS proven, as of C6a: [ProofIput.v]
   establishes [SpecIput.wp_iput2_sconf_body] over the real inode cache,
   and [LinkIput.v] instantiates it with no axiom at all.  The v1
   statement is NOT a consequence of it, and the gap is not a matter of
   effort:

     v1 takes [cwd_ref ip] at a raw 64-bit pointer [ip], and [cwd_ref] is
     DEFINED AS [emp] (design/proc-struct.md, "holes to be honest
     about").  So the v1 precondition contains no slot index, no
     reference fraction, no (dev, inum) and no evidence that [ip] is an
     itable entry at all.  v2's [inode_ref (icn_ref cn) k q dev inum]
     cannot be built from it, because it cannot be built from [emp]:
     ex falso is the only route and there is no falsehood to hand.

   SO THE AXIOM IS NOT STRENGTHENED BY iput BEING PROVEN, and equally it
   does not strengthen anything: it is the SAME assumption the tree
   carried before C6a, at the same statement, moved from [LinkIput.v] to
   here.  A [Print Assumptions] over any of the six cones shows
   [LinkIputCompat.IputCompat.wp_iput_sconf] exactly where it used to
   show [LinkIput.Iput.wp_iput_sconf].  That substitution IS the C6b tell:
   nothing else about the axiom set changes in this cycle.

   WHO CONSUMES IT.  Six proven cones, none of whose proof files may be
   touched -- they are functors over [SpecIput.IPUT] and stay that way:

     kexit, sys_exit          (via [LinkKexit.v])
     fileclose, pipealloc,
     sys_close, sys_pipe      (via [LinkFileclose.v])

   HOW C6b RETIRES IT (claude-notes/projects/fs-icache.md, C6b -- the
   placeholder retirement).  The work is CALLER-SIDE, in this order:

     1. [FileInv.inode_ref] and [ProcInv.cwd_ref] stop being [emp] and
        become [IcacheInv.inode_ref] at an [icacheG]-carried gname
        (design §3's recorded choice); [FileInv.file_payload]'s FD_INODE
        arm gains cn/k/dev/inum and the [fc_ip C = ientry k] tie.
     2. SpecFileclose / ProofFileclose / ProofKexit thread the slot and
        the fraction, and are re-proven against [SpecIput.IPUT2].
     3. THEN, in one move: delete this file, delete
        [SpecIput.wp_iput_sconf_body], [SpecIput.IPUT], [K_iput]'s v1
        role and [SpecIput.iput_units]; rename [IPUT2] -> [IPUT] and
        [wp_iput2_sconf_body] -> [wp_iput_sconf_body] and
        [iput2_units] -> [iput_units] mechanically; repoint
        [LinkKexit.v] / [LinkFileclose.v] back at [LinkIput.Iput].
        The kexit-cone audit then comes fully clean (only the Sail
        model's primitives and functional extensionality remain).

   Written out with an explicit [Axiom] rather than a [Declare Module]:
   both are visible to [Print Assumptions], but only the keyword is
   visible to [tools/proof_coverage.py]'s textual axiom scan.           *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock FdSlots WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import SpecIput.

Module IputCompat : IPUT.
  Axiom wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (n : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iput_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart dev ip n pidv dq m K eb C b.
End IputCompat.
