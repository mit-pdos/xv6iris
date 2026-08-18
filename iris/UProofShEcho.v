(* UProofShEcho.v -- THE THEOREM.

   Everything below `sh' is stated over an ABSTRACT observation [Q].  That
   is what gives the protocol's exec arm its force: the arm demands, OF THE
   PROCESS, a description of the arguments ([uexec_args], which pins the
   BYTES of the path and of every argv element) together with [Q path args],
   and the top statement hands the program [Q sh_echo_path sh_echo_argv] to
   spend there.  To step through that ecall at all, a proof must exhibit
   path and args satisfying the description AT THE REGISTERS THE PROGRAM
   ACTUALLY HOLDS -- and the only [Q] it has is the one at echo's arguments.

   This file instantiates [Q := sh_execs_echo], whose obligation is then
   trivial, and so states the result with NO [Q] hypothesis at all:

     from sh's entry state, with `echo Hello world!\n' on fd 0, the machine
     runs safely, and the exec it performs names "echo" with the arguments
     ["echo"; "Hello"; "world!"].

   It also closes the chain: [wp_sh_parsecmd] carries [parseline] as a
   section hypothesis and [wp_sh_start] carries [parsecmd], both because
   those lemmas were proved in parallel with the ones they call.  Neither
   was ever an [Admitted] -- a section hypothesis is visible in the closed
   lemma's type, so it cannot land silently -- and both are discharged here
   by application.

   WHAT THIS IS CONDITIONAL ON (claude-notes/projects/user-sh.md has the
   full discussion; do not quote the theorem without it):

   - ONE CLASS OF EXECUTIONS.  The input is fixed.  That is not a
     convenience: it is what makes the REPL finite and stops the parser
     recursing, neither of which this tier can otherwise express.
   - THREE KERNEL PROPERTIES, one conjunct in one protocol arm each: that
     [fork] does not fail, that [open("console")] returns a descriptor >= 3,
     and that [exec] does not return.  Each avoids a failure path that is
     not what the theorem is about.
   - [sbrk] hands out slices of a heap region mapped UP FRONT, which is what
     keeps [pt] fixed.  The real [sbrk] grows the address space.
   - THE LAYOUT IS ASSUMED, NOT EXHIBITED.  [sh_layout pt hbase hlen] is a
     hypothesis, and nothing in this development constructs a [uptd]
     satisfying one -- for sh or for any other program in the tier.  So this
     reads "IF such a page table exists, then ...".  That is the right
     structure, since the layout is what [exec] would establish and the
     kernel's [exec] is not yet connected to the user tier; but it has never
     been checked to be SATISFIABLE, and an unsatisfiable layout would make
     this vacuous.  Closing it is the most valuable next work on the tier. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
Require Import UCodeSh USpecSh USpecShParse.
Require Import UProofShInput UProofShParse UProofShCmd UProofShTop UProofShMain.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UProofShEcho.
  Context `{!riscvGS Σ} `{!uioG Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).

  (* the protocol AT the observation *)
  Local Notation Pecho :=
    (xv6_io_protocol C pt gin gbrk hbase hlen sh_execs_echo).

  (* ------------------------------------------------------------------- *)
  (* §1 Closing the two section hypotheses.                               *)
  (* ------------------------------------------------------------------- *)

  Definition sh_parseline_ok :=
    UProofShParse.wp_sh_parseline C pt gin gbrk hbase hlen sh_execs_echo.

  Definition sh_parsecmd_ok :=
    UProofShCmd.wp_sh_parsecmd C pt gin gbrk hbase hlen sh_execs_echo
      sh_parseline_ok.

  (* ------------------------------------------------------------------- *)
  (* §2 THE THEOREM.                                                       *)
  (* ------------------------------------------------------------------- *)

  Theorem wp_sh_execs_echo (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64)
      (Hlay   : sh_layout pt hbase hlen)
      (Himg   : sh_img_sub M)
      (Hsp    : m !!! Regidx sp_idx = sp0)
      (Hst    : uv_stack pt M sp0 576)
      (* .bss is mapped, present and ZEROED -- what [exec] leaves behind *)
      (Hbss   : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)
      (Hbssw  : uv_wr pt M (SH_DATA_PG + 0x10) 0x88)
      (Hstk   : uint sp0 <= 2 ^ 38)
      (* the heap has not been handed out yet, and misses every frame *)
      (Hstkhi : hbase + hlen <= uint sp0 - 576) :
    uv_cap_gpr C pt Pecho M m -∗
    ustdin gin sh_echo_input -∗
    ubrk gbrk hbase -∗
    pc_is (mword_of_int ShSyms.start) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hin Hbrk Hpc".
    iApply (UProofShMain.wp_sh_start C pt gin gbrk hbase hlen sh_execs_echo
              sh_parsecmd_ok CIDp M m sp0
              Hlay Himg Hsp Hst Hbss Hbssw Hstk Hstkhi
              with "Hcg Hin Hbrk [] Hpc").
    (* the observation, at echo's arguments -- the ONLY thing the exec arm
       will accept, and what makes the run's exec the one this names *)
    iPureIntro. split; reflexivity.
  Qed.

End UProofShEcho.

Print Assumptions wp_sh_execs_echo.
