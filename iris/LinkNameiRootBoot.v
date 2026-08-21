(* LinkNameiRootBoot.v -- namei("/") at the boot client, DISCHARGED.

   This file used to hold the boot cone's ONE [Axiom].  It is now what its
   own header always said it would become: a functor application over the
   PROVEN corner ([LinkNameiRoot.NameiRoot], which discharges
   [SpecNamei.NAMEI_ROOT]), supplying the four persistent inode-cache rows
   -- the itable lock, the [ref]-word invariant, the fifty escrows and the
   inode region -- and the two configuration ties.

   NOTHING ABOUT namei WAS PROVED HERE.  The four rows were the assumption's
   entire content, and they exist now because
   [FsCfgBoot.fs_cfg_alloc] mints the inode cache's configuration inside the
   boot-era fupd and [ProofMain.mn_grp_fs] runs
   [IcacheBoot.icache_boot_at] on iinit's postcondition, at main+0x92, six
   instructions before the [userinit] call that needs them
   (claude-notes/projects/fs-cfg-boot.md, stage (e)).  The two ties are
   [FsCfgBoot.fs_boot_supply]'s first two, which is why they can be premises
   at all: they used to be stuck behind [subG_fileΣ]'s [Qed].

   The premise ORDER of [SpecNameiRootBoot.wp_namei_root_boot_body] is
   [SpecNamei.wp_namei_root_body]'s exactly, and the two pure ties
   [dev = icfg_dev] / [nib = icfg_nib] are [eq_refl] here because this file
   instantiates the corner AT the ambient configuration's own fields.  So
   the proof is thirteen hypotheses passed straight through. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecNameiRootBoot] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import IrefSlots IcacheRef ProcAvail FileInvDefs FsCfg.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import SpecNameiRootBoot.
Require Import ProcDefs UserPtTree ProcGeom.  (* the dead-binder dummy: MkPPriv/UPTD/NOFILE *)
Require Import LinkNameiRoot.

Module NameiRootBoot : NAMEI_ROOT_BOOT.
  Lemma wp_namei_root_boot :
    forall `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string),
      wp_namei_root_boot_body dqp m n K eb p b lks.
  Proof.
    intros. rewrite /wp_namei_root_boot_body.
    intros HK Hn Hdev Hnib Hlks.
    iIntros "Hcg Hcpu #Htext #Hkd Hpc #Hpenv #Hitl #Hitinv #Hesc #Hireg
             Hisl Hp0 Hp1 Hcont".
    (* [Vpr] is a DEAD binder of [wp_namei_root_body] (the proc_priv_bare
       sweep gave the whole namei family the parameter for shape uniformity;
       the root corner never touches the private block), so any inhabitant
       serves.  BootCarveMain's zero record is the one other dummy in the
       tree; duplicated rather than exported -- it is one literal. *)
    iApply (NameiRoot.wp_namei_root fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov
              fsc_logst icfg_ist icfg_nib icfg_dev dqp m n K eb p b lks
              (MkPPriv (zero_reg : mword 64)
                 (UPTD (mword_of_int 0 : mword 44) (mword_of_int 0 : mword 44) ∅ ∅)
                 [] (replicate NOFILE (zero_reg : mword 64))
                 (zero_reg : mword 64) [])
              HK Hn eq_refl eq_refl Hdev Hnib Hlks
              with "Hcg Hcpu Htext Hkd Hpc Hpenv Hitl Hitinv Hesc Hireg
                    Hisl Hp0 Hp1 Hcont").
  Qed.
End NameiRootBoot.
