(* SpecNameiTr.v -- N-3: namei WITH THE GHOST TRACE, the pinned-lookup
   campaign's general contract (claude-notes/projects/namei-pinned-lookup.md
   §4; rulings in its STATUS header and §11.4).

   ===== TOMBSTONE (fs-syscall-specs, THE DVIEW RETIREMENT, 2026-08-30) =====

   WHAT LEFT THIS FILE, AND WHY.  The contract itself is RETIRED with the ghost
   it fired.  [nx_hop] lent [DirViewG.dv_half d dqv ents] through the caller's
   fupd at every hop; that column is deleted (the payload arms, the movers, the
   camera and the gnames all went with it), so the statement below could not be
   restated without inventing a resource it never had.  Deleted here:

     - [nx_hop] / [nx_hops_from]  (section 1's hop and its family);
     - [wp_namei_tr_body] and [Module Type NAMEI_TR]  (section 2);
     - [nxc_P] / [nxc_Pmiss] / [nxc_hop] / [nxc_hops]  (section 3's canonical
       ghost-variable cursor).

   The proofs and seals that consumed them -- [SpecNamexTr], [ProofNamexTr],
   [ProofNameiTr], [LinkNamexTr], [LinkNameiTr] -- are OFF THE BUILD with their
   source intact (see _CoqProject's tombstone there); this file could not
   follow them, because everything ABOVE it wants the vocabulary that stays.

   WHAT STAYS, AND WHO WANTS IT.  [inode_held_at] (and [inode_held_at_held]) --
   [IcacheRef.inode_held] with the inum exposed -- is the currency of the ERA
   walk that replaced this contract as the consumed form: [SpecNameiEra],
   [SpecNamexEra], [SpecNparEra], [SpecNparWrapEra] state their pins in it,
   their provers and [ProofSysOpenAU*] / [ProofKexecPin*] read it, and
   [NameiTrDefs]'s binder list is quoted by half the era cone (understating it
   is a documented 255 GB memory bomb).  So the file stays on the build as that
   vocabulary, minus the trace.

   THE REPLACEMENT, in one line: [FsAbsEra.ex_hop] = [FsAbs.ax_hop] at
   [FsAbsEra.elend] (the era leg, which carries directory-ness and reads the
   AUTHORITY's row through [elend_astate]), sealed by [LinkNamexEra] /
   [LinkNameiEra] with a [Print Assumptions] byte-identical to the one this
   file's seal had.
   ========================================================================

   WHAT THIS WAS.  [SpecNamei.wp_namei_gen] returns [inode_held ipv] -- a
   reference to SOME inode, no relation to the path (the SpecNamex.v:113-124
   scope ruling: no path -> inode function exists across instants).  This
   file states the refinement that ruling itself recorded as the honest one:
   ONE caller-supplied atomic step per path element, fired at that hop's
   linearization instant, chaining a caller-chosen CURSOR [P k d] ("after k
   hops the walk stands at inum d").  On success the returned reference is
   pinned: [inode_held_at ipv iL] beside [P L iL].  The path -> inode
   function appears only where a CLIENT's own resources make the path
   stable (N-4, the cancellable lend -- M1, ruled 2026-08-21).

   THE HOP.  At hop k the walk holds the locked directory's payload, whose
   [DirViewG.dv_hold d ents] pins the abstract contents to the bytes
   (N-1, landed).  [nx_hop] lends that whole fragment through the caller's
   fupd at one instant: the caller sees [ents], learns the answer
   [ents !! s], steps its cursor, and hands the fragment straight back.
   The fupd is a single [={⊤}=∗]: the tree's resources are Timeless by
   culture, and the walk fires between instructions where nothing is open.
   (A two-mask ▷-form for clients with non-timeless invariants is a
   deliberate deferral, recorded here so its absence is not an accident.)

   THE HOP NAMES ARE THE ELEMENTS THEMSELVES: dirlookup searches
   [bname 14 nf] of the memmove'd buffer, and SpecNamex.v:104-111 rules
   that [bname 14 nf = e] for the element -- both memmove shapes.  So the
   caller's family is indexed by [path_elems pl] verbatim, and the bridge
   from [dir_first] to [ents !! s] is uniqueness-free
   (FsTree.dir_view_lookup; probe ZZProbeDvLookup.v, finding §9.2).

   FAILURE RETURNS THE UNCONSUMED SUFFIX.  The walk consumes hops
   0..k-1 and dies at k, either WITHOUT firing k (the cursor was not a
   directory -- the caller gets [P k d] back) or AT k (the name was
   absent -- the caller gets the [Pmiss k d] its own hop produced).
   Either way [nx_hops_from .. j] returns the hops the walk never fired,
   so a resource-carrying family is not lost to a short walk.

   SCOPE (ruled): ABSOLUTE PATHS ONLY -- [pfun 0 = SLASH], the walk
   starts at ROOTINO, and the caller's [P 0] is supplied there.  The
   relative form waits for an inum-exposed cwd (Q-c); the nameiparent
   variant rides the same machinery when a consumer appears.

   Everything below the two receipt premises and the changed
   postcondition arms is [SpecNamei.wp_namei_gen_body] VERBATIM -- same
   ambient ties, same ledger, same budget, same eb/trap-CSR threading.
   The landed contract does not move (R10); this is a NEW parallel
   contract, proven by a re-walk that reuses ProofNamexParts (charter
   §9, stage N-3). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
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
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.   (* Require Export's DirViewG *)
Require Import FsTree.         (* [fname], [dir_view]'s home *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.      (* K_namei, and the landed body this shadows *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1. The hop, the receipt family, and the pinned package               *)
(* ===================================================================== *)

Section NameiTrDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  (* THE HOP AND ITS FAMILY ([nx_hop] / [nx_hops_from]) ARE DELETED -- see the
     header's tombstone.  They lent [DirViewG.dv_half] through the caller's
     fupd, and that ghost no longer exists; [FsAbsEra.ex_hop] /
     [ex_hops_from] are the era walk's replacements. *)

  (* [IcacheRef.inode_held] with the inum EXPOSED -- the pinned package.
     Same four conjuncts, one new pure tie; [inode_held_at_held] recovers
     the landed shape so every existing consumer composes unchanged. *)
  Definition inode_held_at (v : mword 64) (z : Z) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜bv_unsigned inum = z⌝ ∗
       inode_refp k q icfg_dev inum)%I.

  Lemma inode_held_at_held (v : mword 64) (z : Z) :
    inode_held_at v z ⊢ inode_held v.
  Proof.
    iIntros "H". iDestruct "H" as (k q inum) "(%&%&%&%&Hr)".
    rewrite /inode_held. eauto 10 with iFrame.
  Qed.

End NameiTrDefs.

(* ===================================================================== *)
(*  2-3. THE CONTRACT AND ITS CANONICAL CURSOR: RETIRED                  *)
(* ===================================================================== *)

(*  [wp_namei_tr_body], [Module Type NAMEI_TR] and the ghost-variable cursor
    ([nxc_P] / [nxc_Pmiss] / [nxc_hop] / [nxc_hops]) are deleted with the hop
    they were stated over -- see the header's tombstone.  Their prover and
    seal ([ProofNameiTr], [ProofNamexTr], [LinkNameiTr], [LinkNamexTr], and
    [SpecNamexTr] one level down) are off the build with their source intact.
    The consumed form is the era walk: [SpecNameiEra]'s contract over
    [FsAbsEra.ex_hops_from], sealed by [LinkNameiEra].                     *)
