(* ProofCreate.v -- the walk of xv6's create (fs.c): the FOUND half and the
   ALLOCATE half's C-OK-FILE / A-FAIL arms.

     static struct inode*
     create(char *path, short type, short major, short minor)

   332 bytes.  The CFG is [SpecCreate.v]'s header and
   claude-notes/projects/fs-sysfile.md's verified listing; every immediate
   below is taken from [CodeCreate.v]'s own lemma statements and from
   nowhere else.

   ---- WHAT THIS FILE PROVES, AND WHAT IT PARKS -------------------------

   [cr_found_half] is create's contract on the FOUND half: the prologue,
   [nameiparent], ARM N, [ilock(dp)], the [dp->nlink == 0] guard and its
   ARM G, [dirlookup], and the two found arms F-BAD and F-OK -- with the
   whole ALLOCATE half (+0xa2 onward, reached by the [c.beqz] at +0x4c
   being TAKEN) parked behind ONE HYPOTHESIS, [cr_alloc_body].  That
   hypothesis is a PREMISE of the lemma, not an axiom and not an [admit]:
   [Print Assumptions cr_found_half] shows the standing platform six and
   nothing else, and the parked half appears in the STATEMENT.

   The cut is at +0x4c rather than at the failure family because the
   family's ARM FAIL is reached only through ialloc / ilock(ip) / three
   [sh]s / iupdate / dirlink -- i.e. through more code than everything
   before it.  The found half is the increment that stands alone.

   [cr_alloc_half] is the OTHER half, and it discharges [cr_alloc_body]:
   the eighth save at +0xa2, the fresh-type gate span (+0xa4..+0xb0,
   [ProofCreateFreshTy]), ARM A-FAIL (+0xec), the three metadata [sh]s, the
   LINK MINT at +0xc4 ([SpecIupdate.wp_iupdate_link]), the T_DIR branch at
   +0xca, the [dirlink(dp,name)] at +0xd8 and ARM C-OK-FILE (+0xe0..+0xea).
   Two of its branches leave through a PREMISE of their own -- the whole
   T_DIR sub-branch through [cr_mkdir_body] and the failing [dirlink]
   through [cr_fail_body] -- so its [Print Assumptions] is the standing six
   and nothing else.  Its conclusion is
   [wp_next]-wrapped for the reason stated at the lemma: the parked bodies
   and the contract's own continuation are anchored at the SECTION hart,
   and the allocate half runs at whatever hart the +0x4c [c.beqz] rebound
   to, so the entry hart's chain link IS the [wp_next] guard.

   ---- THE PIECES ------------------------------------------------------

   [cr_tail_body]  -- the epilogue funnel at +0x70 ([mv a0,s2], the seven
   restores, the pop, [c.ret]).  FOUR arms of this half reach it (N, G,
   F-BAD, F-OK) and two more will (C-OK, A-FAIL, FAIL), so it is
   [□]-persistent with an ABSTRACT continuation -- ProofDirlookup's shape --
   and speaks only of [cr_tregs] and the ten frame slots.

   [cr_alloc_body] -- the parked gate.  It takes the register file, the pc,
   the parent's [dn]/[bm]/[data] and the ledger triple as ARGUMENTS and
   the contract's own continuation as its last premise (ProofDirlink's
   [dl_after_body] shape), so the allocate half will discharge it as an
   ordinary block lemma and this file hands it [Hcont] unretargeted.

   NO LOOP, so no [∀ fuel] anywhere: create is the first fs whole-function
   walk that is straight-line-with-branches, which is why ProofDirlink and
   not ProofNamex is the model for everything except the guard.

   ---- THE ONE LEDGER SUBTLETY (ARM G) ---------------------------------

   [crz] is UNAVAILABLE ON ARM G BY CONSTRUCTION.  It buys itrunc's
   tail-flush unit with [InodeRegion.nlz_obs], which is minted only at an
   observation that the record's nlink is NONZERO -- and ARM G is the guard
   TAKEN, i.e. [di_nlink dn = 0] observed.  So its [iunlockput(dp)] runs at
   [crb = cru = crz = false] and spends [SpecIput.ip_spend_w w false false
   = ip_bm w + 1 <= 2].  It closes with room because nothing has been
   logged before the guard: the count is [CreateBudget.cr_uw w >= 9]
   against [iput_units = 3], which is [cr_budget_found_w]'s first two
   conjuncts.  The same figure covers ARM F-BAD's two uncredited
   [iunlockput]s.

   ---- SEAM NOTE (GR-2c FINDING 5) -------------------------------------

   Every [iunlockput] on this half reports its credited bound at
   [ip_spend_w w false false], which is STRONGER than the [iput_units = 3]
   the ledger cites.  Each seam weakens once, KEEPING the hypothesis name,
   exactly as ProofDirlink's found arm does.                            *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile HartTp.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import FdSlots.
Require Import ProcGeom.
Require Import Xv6Cameras.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import InodeRegion.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import ProcDefs.
Require Import SpecPrintk.
Require Import SpecIalloc SpecIupdate.
Require Import SpecIlock SpecIunlockput.
Require Import SpecDirlookup SpecDirlink.
Require Import SpecNameiparent.
Require Import SpecCreate.
(* THE FRESH-TYPE SPAN: the four instructions +0xa4..+0xb0 that pin
   [di_type dn = ty] across [ialloc]/[ilock].  It is a stretch of create's
   OWN body rather than a callee, so it is NOT a functor argument -- the
   statement ([create_fresh_ty_body], spliced verbatim below), the span's
   register contract ([cr_cs_but_s3]) and the proof all live in
   [ProofCreateFreshTy.v], and this file applies [create_fresh_ty] directly,
   handing it [IA]/[IL] for its two callee hypotheses. *)
Require Import ProofCreateParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Require Import TsoCtx.

(* claude-notes/optimization.md "Register maps": the leaves' premises are
   stated over [rget] (see e.g. [cri_*]'s consumers below), so with these
   three transparent every register-chain [iApply]'s unifier walks
   [rget -> tp_pin -> rf_upd] down the whole chain, and [Qed] re-walks it.
   ProofPipewrite.v is the measured instance (its own header): sealing all
   three is a net win on a file of this shape, PROVIDED no site hands a
   leaf a premise spelled with [!!!] where the leaf's statement says
   [rget] -- those used to bridge for free by delta and regress once the
   three are opaque.  Re-measure after sealing; restate any regressed
   premise in the [rget] spelling with [rget_ne] (HartTp.v) right before
   its [iApply], as ProofPipewrite's own three recoveries did. *)
Local Strategy opaque [rget].
Local Strategy opaque [tp_pin].
Local Strategy opaque [rf_upd].

(* claude-notes/durable-notes.md: a syscall-altitude goal carries
   [ProcInv.tf_page]'s 4096-conjunct big-op, and printing it turns a
   one-line mistake into a forty-minute non-answer. *)
Set Printing Depth 40.
(* ==================================================================== *)
(*  ProofCreate.v -- the seal. *)
(*                                                                      *)
(*  Split out of ProofCreate.v FOR THE BUILD DAG: create's five halves    *)
(*  take each other as PREMISES, not as callees, so only the             *)
(*  functor-free vocabulary in ProofCreateShared.v is shared and they     *)
(*  compile in parallel.                                                 *)
(* ==================================================================== *)

Require Import ProofCreateShared.
Require Import ProofCreateFound ProofCreateAlloc ProofCreateFail.
Require Import ProofCreateFailMkdir ProofCreateMkdir.

Module CreateProof (NP : NAMEIPARENT) (IL : ILOCK) (IUP : IUNLOCKPUT)
                   (DL : DIRLOOKUP) (IA : IALLOC) (IU : IUPDATE)
                   (DLK : DIRLINK) : CREATE.

  Module F  := CreateFound NP IL IUP DL.        Import F.
  Module A  := CreateAlloc IL IUP IA IU DLK.    Import A.
  Module FL := CreateFail IUP IU.               Import FL.
  Module FM := CreateFailMkdir IUP IU.          Import FM.
  Module MK := CreateMkdir IUP IU DLK.          Import MK.

Section ProofCreateMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.


  Lemma wp_create_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16) (U : ustate)
      (u : nat) (Sb : gset Z) (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    wp_create_sconf_body γs j γl pd pav pu
 γf
 plen pfun ty major minor
                         U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks.
  Proof.
    rewrite /wp_create_sconf_body.
    intros HK Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc Hbmsl
           Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3 Hnib16
           Htynz Htyw Hpkc Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb.
    (* (L5) at the fresh record is (L5) at the type word (2b-inode-3). *)
    pose proof (InodeRegion.ireg_ty_ok_of_w (ialloc_fresh ty) Htyw) as Htyk.
    destruct (cr_kb K HK)
      as (HK10 & HKnp & HKil & HKdlu & HKiup & HKia & HKiu & HKdlk & HKsum).
    iIntros "Hcg Hcnt #Htext Hpc #Hkd #Hpk #Hbio #Hlogc #Hkenv
             #Hitb2 #Hitbl #Hesc #Hslks #Hiregi #Hiopen Hsbn Hsbi Hsbs Hsbb #Hbmr
             Hpriv Hpath #Hprocs #Hdevi #Hgeom #Hdlk Hbsl Hisl Hop Htx Hcont".
    iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
    iDestruct (cr_cap_align m K b (proc_addr j) HK10 with "Hcg")
      as %[Hal10 Hal9].
    iApply (cr_found_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun ty major minor U u Sb ns pidv
              dqb dqs dqbs dqn m K eb b lks
              HK Hroot Hnib0 Hlg Hsize Hbms0 Hbmsc
              Hbmsl Hist0 Hcovb Hbmgeo Hiregb Hcstr Hplen31 Hni1 Hni2 Hni3
              Htynz Htyk Hpkc Hu Hns Hj Hgs Ha1 Ha2 Ha3 Heb
              with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hkenv
                    Hitb2 Hitbl Hesc Hslks Hiregi Hiopen Hsbn Hsbi Hsbs Hsbb Hbmr
                    Hpriv Hpath Hprocs Hdevi Hgeom Hdlk Hbsl Hisl Hop Htx
                    [] Hcont").
    iApply (cr_alloc_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun (m !!! Regidx Ra0 : mword 64)
              ty major minor U u Sb ns pidv dqb dqs dqbs dqn m
              (m !!! Regidx csp_rs1 : mword 64)
              (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
              HK Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl
              Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Htynz Htyk Hpkc
              Hu Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
              with "Htext Hkd Hpk Hbio Hlogc Hkenv Hitb2 Hitbl Hesc
                    Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk [] []").
    - iIntros (kd qd gd γil γisl dind dn bm data nf nsl t).
      iApply (cr_mkdir_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun (m !!! Regidx Ra0 : mword 64)
                ty major minor U u Sb ns pidv dqb dqs dqbs dqn m
                (m !!! Regidx csp_rs1 : mword 64)
                (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
                kd qd gd γil γisl dind dn bm data nf nsl t
                HK Hroot Hlg Hsize Hbms0 Hbmsc Hbmsl
                Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hnib16 Hpkc
                Hu Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
                with "Htext Hkd Hpk Hbio Hlogc Hkenv Hitb2 Hitbl
                      Hesc Hslks Hiregi Hiopen Hprocs Hdevi Hgeom Hdlk").
    - iIntros (kd qd gd γil γisl dind dn bm data nf nsl t).
      iApply (cr_fail_half (CID := CID) γs j γl pd pav pu
 γf
 plen pfun (m !!! Regidx Ra0 : mword 64)
                ty major minor U u Sb ns pidv dqb dqs dqbs dqn m
                (m !!! Regidx csp_rs1 : mword 64)
                (ret_pc (m !!! Regidx Rra : mword 64)) K eb b lks
                kd qd gd γil γisl dind dn bm data nf nsl t
                HK Hnib16 Hlg Hsize Hbms0 Hbmsc Hbmsl
                Hist0 Hcovb Hiregb Hns Hj Hgs eq_refl eq_refl Hal10 Hal9 Heb
                with "Htext Hkd Hpenv Hbio Hlogc Hitb2 Hitbl Hesc Hiregi Hiopen
                      Hprocs Hdevi Hgeom Hdlk").
  Qed.

End ProofCreateMain.

End CreateProof.
