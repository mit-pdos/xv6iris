(* ProofSysUnlinkAU.v -- **THE SEAL.**  W1 o W2 o W3 o {W5-FILE, W5-DIR},
   and nothing else, ascribed [SpecSysUnlinkAU.SYSUNLINK_AU].

   [ProofSysUnlink.wp_sys_unlink_sconf]'s copy-adapt, and it composes
   rather than proves: every block is a landed lemma of this lane and
   every seam is the next block's premise list verbatim, so the only work
   is naming the seam's forall-bound bundle (which now carries [pl], [iL],
   the name tie, the cursor and the four commits) and handing the caller's
   exit BACK at each stage.

   ONE THING IS NOT COMPOSITION, and it is one line: the contract's own
   inlined return continuation reports the descriptor growth as
   [ProcPtOwn.uptd_ext], where the landed closer's -- and therefore every
   block's, since [ProofSysUnlinkAUParts.su_au_closer] is that closer with
   [ARMS] swapped in -- is the stronger [uptd_ext_sz].
   [ProcPtOwn.uptd_ext_sz_ext] closes the gap, ONCE, at the top of this
   proof rather than at each of the eight exits.

   The result is [SpecSysUnlinkAU]'s Module Type, SEALED: the two-instant
   AU is an unconditional theorem about the machine, given the twelve
   callees' contracts.  [LinkSysUnlinkAU.v] instantiates it against their
   proofs. *)
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
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SpecPanic.
Require Import SpecPrintk.
Require Import Xv6Cameras.
Require Import FsBytesGamma.
Require Import IrefSlots.
Require Import FsTree.
Require Import FileInvDefs.
Require Import ProcPtOwn.
Require Import ProcDefs.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIupdate.
Require Import SpecIunlockput.
Require Import SpecNamecmp.
Require Import SpecDirlookup.
Require Import SpecMemset.
Require Import SpecReadi.
Require Import SpecWritei.
Require Import SpecNparWrapEra.   (* [NPAR_WRAP_ERA]: the era walk         *)
Require Import SpecSysUnlinkAU.
Require Import ProofSysUnlinkAUParts.
Require Import ProofSysUnlinkAUW1.
Require Import ProofSysUnlinkAUW2.
Require Import ProofSysUnlinkAUW3.
Require Import ProofSysUnlinkAUW5F.
Require Import ProofSysUnlinkAUW5D.
Require Import FsAbs.
From Kernel Require KernelSyms KernelData.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Local Open Scope Z_scope.
Require Import TsoCtx.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysUnlinkAUProof (Argstr : ARGSTR) (BeginOp : BEGIN_OP)
                        (NparEra : NPAR_WRAP_ERA) (Ilock : ILOCK)
                        (Namecmp : NAMECMP) (Dirlookup : DIRLOOKUP)
                        (Memset : MEMSET) (Readi : READI) (Writei : WRITEI)
                        (Iupdate : IUPDATE) (Iunlockput : IUNLOCKPUT)
                        (EndOp : END_OP) (PN : PANIC) : SYSUNLINK_AU.

Module W1  := SysUnlinkAUW1  Argstr BeginOp NparEra Iunlockput EndOp PN.
Module W2  := SysUnlinkAUW2  Ilock Namecmp Dirlookup Iunlockput EndOp PN.
Module W3  := SysUnlinkAUW3  Ilock Readi Iunlockput EndOp PN.
Module W5F := SysUnlinkAUW5F Ilock Memset Writei Iupdate Iunlockput EndOp PN.
Module W5D := SysUnlinkAUW5D Memset Writei Iupdate Iunlockput EndOp PN.

Section ProofSysUnlinkAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Lemma wp_sys_unlink_au `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gf : gname)
      (gs : list gname) (jx : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac) (v0 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phient : aview -> Z -> fname -> Z -> iProp Σ)
      (Phitgt : aview -> Z -> iProp Σ)
      (Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phimiss : aview -> Z -> fname -> iProp Σ) :
    wp_sys_unlink_au_body gf gs jx gl pd pav
      pu
      dqb dqs dqbs v0 pid U m K eb b lks P Pmiss
      Phient Phitgt Phiex Phimiss.
  Proof.
    cbv beta zeta delta [wp_sys_unlink_au_body wp_sys_unlink_au_frame].
    intros HK HdevR Hnib0 Hgeom Hsize Hbm0 Hbmcov
           Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hnib16 Hprk Hj Hgl Heb Harg0.
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hprenv #Hbio #Hlog
             Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows
             #Hslks #Hireg #Hropen Hsbb Hsbi Hsbs #Hbmres #Hkenv #Hprocs Hir Hpriv
             Hau Hcont".
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpenv".
    (* THE CALLER'S EXIT, PUT IN THE BLOCKS' SPELLING.  [su_au_closer] is
       [SpecSysUnlink.sys_unlink_closer]'s rows with [ARMS] in place of the
       pure return disjunction, and the contract's own inlined copy differs
       from it in exactly ONE row: the descriptor report is [uptd_ext] where
       the landed closer's (and therefore every block's) is the stronger
       [uptd_ext_sz].  One [ProcPtOwn.uptd_ext_sz_ext] closes the gap, once,
       here -- rather than at each of the eight exits. *)
    iAssert (wp_next true (proc_addr jx) (fun (CIDx : CpuId) =>
               su_au_closer (CID := CIDx) gf (proc_addr jx) pid U m
                 (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64))
                 K eb b lks dqb dqs dqbs
                 (unlink_arms (fs_gamma_L fsc_fs) fsc_fs P Pmiss
                              Phient Phitgt Phiex Phimiss)))%I
      with "[Hcont]" as "Hcont".
    { rewrite /wp_next. iIntros (CIDx) "%Hq".
      iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hq |].
      rewrite /su_au_closer.
      iIntros (mf P') "%Hcs %Hupt Hcgx Hownx Htce Hcce Hpcx Hbslx Hsbbx Hsbix
                       Hsbsx Hirx Hprivx Harms".
      iApply ("Hcont" $! mf P' with "[%] [%] Hcgx Hownx Htce Hcce Hpcx Hbslx
                Hsbbx Hsbix Hsbsx Hirx Hprivx Harms").
      { exact Hcs. }
      { exact (uptd_ext_sz_ext _ _ _ Hupt). } }
    (* ---- W1, +0x00..+0x2e: the prologue, argstr, begin_op, nameiparent ---- *)
    iApply (W1.su_w1_au gf gs jx gl pd pav pu
 dqb dqs dqbs
              v0 pid U m K eb b lks P Pmiss Phient Phitgt Phiex Phimiss HK HdevR Hnib0
              Hgeom Hsize Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb
              Harg0
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv Hau []
                    Hcont").
    iIntros (CIDa Ms P1 n1 Sb1 w1 dpv nf bp bnm0 bd be w4 w5 w6 w27 w30
             pl iL).
    iIntros "%Hal %Hregs1 %Hma01 %Hupt1 %Hn1 %Hw1 %Hdpvnz
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv Hir
             Hheld %Hname1 HP Hcent Hctgt Hcex Hcmiss
             HopS Htx Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE
             H30 Hcont".
    (* ---- W2, +0x30..+0x6e: ilock(dp), the two namecmp refusals,
       dirlookup ---- *)
    iApply (W2.su_w2_au gf gs jx gl pd pav pu
 dqb dqs dqbs
              pid U P1 n1 Sb1 w1 dpv nf bnm0 bp bd be w4 w5 w6 w27 w30
              m Ms (m !!! Regidx csp_rs1 : mword 64) K eb b lks
              pl iL P Pmiss Phient Phitgt Phiex Phimiss
              HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hregs1 Hma01 Hn1
              Hupt1
              with "Hcg Hown Htext Hdata Hpc Hpenv Hbio Hlog Hseam Hgen
                    Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen
                    Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hir Hpriv Hheld
                    [%] HP Hcent Hctgt Hcex Hcmiss HopS Htx
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27 HbE H30
                    [] Hcont").
    { exact Hname1. }
    iIntros (CIDb M2 kd ks kk gild gisld gyd loyd tlyd qdi sd qs dinum dnd bmd datd lo t).
    iIntros "%Hregs2 %Hkd %Hks %Hdinb %Htydir %Hiok %Hrl_datd %Hdok %Hddix
             %Hdoc %Hduq
             %Hnotdot %Hnotdd %Hfst %Hma02 %Hal27
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             %Hname2 HP Hcent Hctgt Hcex Hcmiss
             Hslkd Hslkdq %Hleyd #Hflyd #Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS Htx
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W3, +0x72..+0x88: ilock(ip), the nlink panic, the T_DIR test
       (and, on the taken arm, the whole isdirempty loop through W4) ---- *)
    iPoseProof (printk_env_panic with "Hprenv") as "#Hpetop".
    iApply (W3.su_w3_au gf gs jx gl pd pav pu
 dqb dqs dqbs
              pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd qdi sd qs loyd tlyd
              dinum dnd bmd datd lo nf bnm0 bp bd be w5 w6 w30
              m M2 (m !!! Regidx csp_rs1 : mword 64) K eb b lks t
              pl P Pmiss Phient Phitgt Phiex Phimiss
              HK Hnib0 Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1 Hupt1 Hregs2
              Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
              Hnotdot Hnotdd
              Hfst Hma02 Hal27
              with "Hcg Hown Htext Hdata Hpetop Hpc Hbio Hlog Hseam Hgen Hdev Hgeo
                    Hdlk Hbsl Hitab Hitinv Hescrows Hslks Hireg Hropen Hsbb Hsbi
                    Hsbs Hbmres Hkenv Hprocs Hpriv Hslkd Hslkdq
                    [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd Hdiatd Hmetad
                    Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud Hchild Hruc HopS Htx
                    [%] HP Hcent Hctgt Hcex Hcmiss
                    Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                    HbE H30 [] Hcont").
    { exact Hname2. }
    iIntros (CIDc M3 s3x bex isdir gili gisli gyi si qsi loyi tlyi dni bmi dati).
    iIntros "%Hregs3 %Hnlzi %Hioki %Hrl_dati %Hdoki %Hddixi %Hdoci %Hduqi
             %Hisd
             Hcg Hown Hpc Hseam Hgen Hbsl Hsbb Hsbi Hsbs Hpriv
             Hslkd Hslkdq %Hleyd5 #Hflyd5 #Hclaimsyd5 Hdepd Hoffrd Hidevd Hiinumd Hivalidd Hdlnkd
             Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd Hfrz Hkeepd Hrud
             Hslki Hslkiq %Hleyi #Hflyi #Hclaimsyi Hdepi Hoffri Hidevi Hiinumi Hivalidi Hdlnki
             Hdiati Hmetai Haddrsi Hindi Hblocksi Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
             %Hname3 HP Hcent Hctgt Hcex Hcmiss
             Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi HbE H30
             Hcont".
    (* ---- W5, +0x8a..: the zeroing and the two tails, split on the seam's
       own index.  The FILE arm is [su_w5_file]; the T_DIR arm is
       [su_w5_dir], which since V5' increment W derives (D1) and (D2)
       internally and takes neither as a premise. ---- *)
    destruct isdir.
    - destruct Hisd as (Htyzi & Hdots & Hdead).
      iApply (W5D.su_w5_dir_au gf gs jx gl pd pav pu

                dqb dqs dqbs pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs loyd tlyd dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi loyi tlyi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks t
                pl P Pmiss Phient Phitgt Phiex Phimiss
                HK Hprk Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Htyzi Hdots Hdead
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffri Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
                      [%] HP Hcent Hctgt Hcex Hcmiss
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
      { exact Hname3. }
    - iApply (W5F.su_w5_file_au gf gs jx gl pd pav pu

                dqb dqs dqbs pid U P1 n1 Sb1 w1 kd ks kk gild gisld gyd
                qdi sd qs loyd tlyd dinum dnd bmd datd lo nf bnm0 bp bd bex w6 w30
                gili gisli gyi si qsi loyi tlyi dni bmi dati
                m M3 (m !!! Regidx csp_rs1 : mword 64) s3x K eb b lks t
                pl P Pmiss Phient Phitgt Phiex Phimiss
                HK Hprk Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hiregb Hj Hgl Heb eq_refl Hal Hn1
                Hupt1 Hkd Hks Hdinb Htydir Hiok Hrl_datd Hdok Hddix Hdoc Hduq
                Hnotdot Hnotdd Hfst Hal27 Hregs3 Hnlzi Hioki Hrl_dati Hdoki
                Hddixi
                Hdoci Hduqi Hisd
                with "Hcg Hown Htext Hdata Hprenv Hpc Hbio Hlog Hseam
                      Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hescrows Hireg Hropen
                      Hsbb Hsbi Hsbs Hbmres Hkenv Hprocs Hpriv
                      Hslkd Hslkdq [//] Hflyd Hclaimsyd Hdepd Hoffrd Hidevd Hiinumd Hivalidd
                      Hdlnkd Hdiatd Hmetad Haddrsd Hindd Hblocksd Htop Hshotd
                      Hfrz Hkeepd Hrud Hslki Hslkiq [//] Hflyi Hclaimsyi Hdepi Hoffri Hidevi Hiinumi
                      Hivalidi Hdlnki Hdiati Hmetai Haddrsi Hindi Hblocksi
                      Htopi Hshoti Hfrzi Hkeepi Hrui HopS Htx
                      [%] HP Hcent Hctgt Hcex Hcmiss
                      Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 HbD Hnm14 Hnm2 HbP H27lo H27hi
                      HbE H30 Hcont").
      { exact Hname3. }
  Qed.

End ProofSysUnlinkAU.

End SysUnlinkAUProof.
