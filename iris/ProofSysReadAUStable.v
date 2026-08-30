(* ProofSysReadAUStable.v -- the stable corollary, DERIVED from the AU form
   and nothing else, and the file that SEALS [SpecSysReadAUAt.SYSREAD_AU_AT]
   whole.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the read AU
   prover).  [SpecSysReadAU]'s header is explicit that this is owed "as a
   DERIVATION from [wp_sys_read_au] + the agreement seed
   ([aread_commit_pinned_self]), never as a second walk", and this file is
   that: NO instruction is stepped, no invariant is opened, and the whole
   proof is one instantiation plus two one-line applications.

   ==== THE SHAPE, AND WHY IT NEEDS AN [Include] ========================

   [ProofSysWriteAUStable] could be a pure functor over the AU module because
   the write side has TWO module types ([SYSWRITE_AU_ERA] and
   [..._ERA_STABLE]), one field each.  [SYSREAD_AU_AT] carries BOTH fields,
   so the sealed module has to contain both proofs: [ProofSysReadAU] exports
   the walk UNSEALED as [SysReadAUWalk], this file [Include]s an application
   of it, adds the corollary beside it, and the seal is applied once at the
   end.  Nothing about either proof changes; only where the seal sits does.

   ==== HOW THE DERIVATION GOES, IN THREE MOVES =========================

   1. INSTANTIATE THE AU AT THE ENRICHED RECEIPT.  The AU form is generic in
      [Φr], so it may be taken at
      [FsAbsReadFire.arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr] -- the
      client's own receipt plus what agreement buys: the observed row IS the
      client's value, and the share comes back.

   2. BUILD THE COMMIT AT THAT RECEIPT.  [arf_pin_compose] is exactly that:
      a client holding the share AND its own commit has the commit at the
      enriched receipt, with agreement firing at the instant.  This is where
      the [nview] the stable body's EXTRA carries is spent -- once, on the
      way in -- and it is why the derivation is generic in [Φr].

   3. COLLAPSE THE ARMS.  [arf_stable_of_arms] turns [read_arms] at the
      enriched receipt into [read_stable_arms], and the [0 <= n] premise of
      the stable body is what refutes the GUARD arm -- whose refund would
      otherwise strand the wrapped share inside the returned closure.  With
      it every surviving arm carries a FIRED receipt, which is why read needs
      no escape arm where write has one.

   THE MEMORY ROW IS NOT REWRITTEN BY ANY OF THE THREE.  The window, its
   length bound and the EXACT-COUNT conjunct
   ([SpecSysReadAU]'s "...BUT THE LENGTH IS SAID, AND IT IS THE ANSWER")
   pass through untouched -- the corollary collapses ARMS, never memory --
   so the stable form carries them beside the pinned receipt.  That is what
   makes the client's reading available at all: with the row pinned to
   [MkAnode (AFile bs0) nl], [ard_ret_tie_exact_file] turns the returned
   count into [d = ard_count (Z.to_nat n) off (length bs0)].

   NOTE THE CONTRAST WITH THE WRITE LANE, because it is the whole reason this
   file is shorter than its twin: write's ok arm had to take an UN-KEYED
   escape disjunct at [off0 := 0], since chaining one chunk's offset to the
   next is not a truth of the concurrent kernel.  Read has ONE instant, so
   there is nothing to chain and nothing to escape into; both arms land at
   the client's own value.

   AND THE FORM IS STILL VACUOUS AGAINST A LIVE INUM -- the frozen header's
   own caveat ([FsAbsSeam]'s finding 3: the payload arms hold the element
   WHOLE, so a client share against a live inum is refuted).  UNLIKE write,
   though, this statement needs no re-cut when the custody seam moves: a read
   fires no retag, so the same sealed form becomes non-vacuous as it stands.

   BINDERS: [SpecSysReadAUAt]'s section list VERBATIM. *)
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
Require Export SwtchCtx.
Require Import IrefSlots.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import Xv6Cameras.
Require Import SpecArgfd SpecArgint SpecArgaddr SpecFileread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsBytesGamma.
Require Import FsCfg.
Require Import SpecSysRead.
Require Import SpecSysReadAU.
Require Import SpecSysReadAUAt.
Require Import FsAbsReadFire.
Require Import SpecFilereadAU.
Require Import ProofSysReadAU.
Require Import FsAbs.          (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

Module SysReadAUProof (Argaddr : ARGADDR) (Argint : ARGINT) (Argfd : ARGFD)
                      (FilereadAU : FILEREAD_AU) : SYSREAD_AU_AT.

(* the walk, verbatim: [ProofSysReadAU] proves [wp_sys_read_au_at] and this
   application brings it in as a field of the module being sealed. *)
Include ProofSysReadAU.SysReadAUWalk Argaddr Argint Argfd FilereadAU.

Section ProofStable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_sys_read_au_at_stable
      (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (fn : fread_names) (pidv : mword 32) (U : ustate) (v v1 v2 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (fd : nat) (fv : mword 64) (wb : bool) (i : Z)
      (q : Qp) (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ)
    : wp_sys_read_au_at_stable_body γf γs j γlp fn pidv U v v1 v2 m K eb b
        lks fd fv wb i q bs0 nl Φr.
  Proof.
    (* MOVE 1: the AU form at the ENRICHED receipt. *)
    pose proof (wp_sys_read_au_at γf γs j γlp fn pidv U v v1 v2 m K eb b lks
                  fd fv wb i
                  (arf_pin_recv (fs_gamma_L fsc_fs) i q
                     (MkAnode (AFile bs0) nl) Φr)) as HW.
    cbv beta delta [wp_sys_read_au_at_body wp_sys_read_au_frame] in HW.
    cbv beta delta [wp_sys_read_au_at_stable_body wp_sys_read_au_frame].
    intros Γfs nn Hnn pcE pj ret_tgt Hav Hj Hgs Hlens Harg0 Harg1 Harg2
           Hrp Hdq Heb Hargfd.
    iIntros "Hcg Hcpu Htext Hdata Hpc Hpenv Hpriv Hkenv Hprocs Henv Hci
             Hfdst [Hn Hcm] Hcont".
    iApply (HW Hav Hj Hgs Hlens Harg0 Harg1 Harg2 Hrp Hdq Heb Hargfd
              with "Hcg Hcpu Htext Hdata Hpc Hpenv Hpriv Hkenv Hprocs Henv
                    Hci Hfdst [Hn Hcm]").
    (* MOVE 2: the client's share is spent HERE, once, and rides inside every
       receipt from now on. *)
    { iApply (arf_pin_compose with "Hn Hcm"). }
    iIntros (CID' Hchain mf r P' d bs)
      "%Hcs %Hupt %Hdle %Hdex %Hra Hcg Hcpu Hpc Hpriv Hkenv Hout Hfdst Harms".
    iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hchain |].
    iApply ("Hcont" $! mf r P' d bs
              with "[%] [%] [%] [%] [%] Hcg Hcpu Hpc Hpriv Hkenv Hout Hfdst
                    [Harms]").
    { exact Hcs. }
    { exact Hupt. }
    (* the window and THE EXACT COUNT ride through the derivation untouched:
       the corollary rewrites only the ARMS, never the memory row.  What the
       client gains by holding them together is the reading the stable arms
       cannot state on their own -- [d] IS
       [ard_count (Z.to_nat n) off (length bs0)]
       ([SpecSysReadAU.ard_ret_tie_exact_file] at the pinned row). *)
    { exact Hdle. }
    { exact Hdex. }
    { exact Hra. }
    (* MOVE 3: THE COLLAPSE.  [Hnn] is what kills the guard arm's refund. *)
    iApply (arf_stable_of_arms (fs_gamma_L fsc_fs) i (sys_rw_count v2) q
              bs0 nl Φr r Hnn with "Harms").
  Qed.

End ProofStable.

End SysReadAUProof.
