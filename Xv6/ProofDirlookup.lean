/-
Proof of `dirlookup`'s specification (`SpecDirlookup.DIRLOOKUP`, Rocq
`ProofDirlookup.v`'s `DirlookupProof`), given `readi` (its KERNEL arm),
`namecmp`, `iget` and `panic`.

    +0x00 .. +0x14   the 12-slot frame, nine saves, s0 = sp + 96
                     (Xv6.wp_prologue_dirlookup)
    +0x16 .. +0x1c   dp->type vs T_DIR; the `bne` to `unreachable` is
                     REFUTED by the contract's `dn.diType = T_DIR`
    +0x20 .. +0x34   s2 := dp, s5 := name, s7 := poff, a5 := dp->size,
                     s1 := 0, s4 := &de, s3 := 16, s6 := &de.name, a0 := 0
    +0x36            c.bnez a5: size = 0 falls to +0x38
    +0x38            c.j +0x96 -- the EMPTY-DIRECTORY arm
    +0x46 .. +0x4e   panic("dirlookup read") -- LIVE (Xv6.dirlookup_short)
    +0x52 .. +0x58   THE LATCH (Xv6.dirlookup_latch)
    +0x5c .. +0x7c   THE BODY: readi, the read test, the free test, namecmp
                     (Xv6.dirlookup_read, Xv6.dirlookup_name)
    +0x7e .. +0x92   THE FOUND ARM: *poff, THE LICENCE, iget
                     (Xv6.dirlookup_found, Xv6.dirlookup_found_iget)
    +0x94            a0 := 0 -- the loop-exhausted arm
    +0x96 .. +0xaa   THE TAIL (Xv6.dirlookup_tail)

THE SHAPE OF THE PROOF (Rocq's, kept): the shared tail, the scan as a fuel
induction wrapped in `wpNext` (the body sleeps inside readi, so the hart
moves at every call), and this entry lemma; the stage files are
`DirlookupParts`, `DirlookupDefs`, `DirlookupTail`, `DirlookupLatch`,
`DirlookupHit`, `DirlookupName`, `DirlookupRead`.

**Deviations from Rocq** (beyond SpecDirlookup's):

1. The frame is `MachCSL.frame12` at the prologue / epilogue and
   `dirlookupFrame` + `dirlookupDe` inside (DirlookupParts deviation 2).
2. The tail, latch, found arm and record test are stage lemmas entered with
   the contract's continuation as a resource (DirlookupDefs deviation 1).
3. The fuel is `nrec + 1 - i` (DirlookupDefs deviation 2).
4. `dirlookup_iget` is a copy of `Xv6.ialloc_iget` (IallocDefs), a
   promotion candidate for `Xv6/FsCallSitesF.lean`.

Stale in Rocq, recorded: the ProofDirlookup header says BOTH panics are
dead (from the granularity premise); the body (and SpecDirlookup's header)
walk the short-read panic as LIVE, which is what is ported.  LinkDirlookup
says "panic is NOT a module here" and then takes `Panic`; it is a module
(the short-read arm calls it).  The not-DIR arm calls `unreachable` in this
kernel, not `panic`.  The header's `+0x..` offsets are Rocq's image's; the
bodies are byte-identical and the offsets above are the Lean image's.
-/
import Xv6.DirlookupRead
import MachCSL.WpSmodeLh

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- The type cell, borrowed out of `inodeMeta`. -/
theorem dirlookup_meta_type (ip : BitVec 64) (dn : Dinode) :
    inodeMeta (GF := GF) ip dn ⊢
      wordPointsTo (iType ip) 2 (DFrac.own 1) dn.diType ∗
      (wordPointsTo (iType ip) 2 (DFrac.own 1) dn.diType -∗ inodeMeta ip dn) := by
  unfold inodeMeta
  iintro ⟨Ht, Hrest⟩
  iframe Ht
  iintro Ht
  iframe Ht Hrest

theorem dirlookup_ctx_entry (c : CPU) (k : KCtx) (R : RegMap) :
    kctx (GF := GF) c ((k.pushed 12).withRegs R) ⊢
      kctx c (((k.withSpie k.spie k.spp).pushed 12).withRegs R) := .rfl

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [IregG GF] [IcacheG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]

set_option maxHeartbeats 16000000 in
/-- **`+0x16 .. +0x38`: the type test, the setup, and the dispatch** --
the empty directory to the tail, anything else into the scan at record 0. -/
theorem dirlookup_setup (RD : READI) (NC : NAMECMP) (IG : IGET) (PA : PANIC)
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (pd pav pu : BitVec 64) (j : Nat)
    (γkl : GName) (γk : KmemNames)
    (ip : BitVec 64) (dinum : BitVec 32) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (dn dr : Dinode) (fn : Nat → BitVec 8) (hasp : Bool) (pofv pidv : BitVec 32)
    (dqp dqd dqn : DFrac) (X : RegMap) (v10 : BitVec 64) (bs : List (BitVec 8))
    (hs : DirlookupStatic k j bm data dn dr fn hasp) (hpd : descPageRw pd)
    (ha0 : k.regs 10#5 = ip)
    (hX : X = (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFA0#64)).set 8#5 (k.regs 2#5)) :
    kctx cpu ((k.pushed 12).withRegs X) ∗ pcIs cpu (KA.«dirlookup» + 0x16#64) ∗
    dirlookupFrame (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5)
      (k.regs 20#5) (k.regs 21#5) (k.regs 22#5) (k.regs 23#5) v10 ∗
    dirlookupDe (k.regs 2#5) bs ∗
    trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
    dirlookupKeep k ip dinum bm data dn dr fn pidv dqp dqd dqn ∗ dirlookupIn hasp (k.regs 12#5) pofv ∗
    dirlookupEnv (hlc := hlc) Γ γl pd pav pu γkl γk ∗
    (∀ c' : CPU, dirlookupPost k ip dinum bm data dn dr fn hasp pofv pidv dqp dqd dqn c')
    ⊢ wpLoop (GF := GF) cpu := by
  subst hX
  have hmaxb := dirlookup_maxbytes
  have hsz := hs.hsz
  have hsz31 : dn.diSize.toNat < 2 ^ 31 := by omega
  have hsx := dirlookup_sext_small dn.diSize hsz31
  have hbz := dirlookup_bnez_nat dn.diSize.toNat (by omega)
  have hty : BitVec.signExtend 64 dn.diType = BitVec.signExtend 64 T_DIR := by rw [hs.htype]
  iintro ⟨Hk, Hpc, Hframe, Hde, Hte, Hce, Hkeep, Hin, #Henv, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- +0x16  lh a4,68(a0) ; +0x1a  c.li a5,1 ; +0x1c  bne a4,a5 (REFUTED)
  unfold dirlookupKeep
  icases Hkeep with ⟨Hdev, Hmeta, Hmap, Hblk, Hnm, Hpid, Hbsl, Hlk, Hdi⟩
  icases dirlookup_meta_type ip dn $$ Hmeta with ⟨Hty, Hmcl⟩
  k_step_e (wp_s_lh cpu _ (KA.«dirlookup» + 0x16#64) false 68#12 14#5 10#5 (by decide) (by decide)
      (DFrac.own 1) dn.diType)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha0, iType]
  iintro Hk Hpc Hty
  ihave Hmeta := Hmcl $$ Hty
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x1a#64) true 1#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_branch cpu _ (KA.«dirlookup» + 0x1c#64) false 30#13 14#5 15#5 (by decide) bop.BNE)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [hty, dirlookup_bne_type]
  iintro Hk Hpc
  -- +0x20  c.mv s2,a0 ; +0x22  c.mv s5,a1 ; +0x24  c.mv s7,a2
  k_step_e (wp_s_add cpu _ (KA.«dirlookup» + 0x20#64) true 18#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_add cpu _ (KA.«dirlookup» + 0x22#64) true 21#5 0#5 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_add cpu _ (KA.«dirlookup» + 0x24#64) true 23#5 0#5 12#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- +0x26  c.lw a5,76(a0)
  icases dirlookup_meta_size ip dn $$ Hmeta with ⟨Hsz, Hmcl⟩
  k_step_e (wp_s_lw cpu _ (KA.«dirlookup» + 0x26#64) true 76#12 15#5 10#5 (by decide) (by decide)
      (DFrac.own 1) dn.diSize)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha0, iSize]
  iintro Hk Hpc Hsz
  ihave Hmeta := Hmcl $$ Hsz
  -- +0x28 .. +0x34  s1 := 0, s4 := &de, s3 := 16, s6 := &de.name, a0 := 0
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x28#64) true 0#12 9#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x2a#64) false 4000#12 20#5 8#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x2e#64) true 16#12 19#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x30#64) false 4002#12 22#5 8#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_e (wp_s_addi cpu _ (KA.«dirlookup» + 0x34#64) true 0#12 10#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  ihave Hkeep : dirlookupKeep k ip dinum bm data dn dr fn pidv dqp dqd dqn
    $$ [Hdev Hmeta Hmap Hblk Hnm Hpid Hbsl Hlk Hdi]
  · unfold dirlookupKeep; iframe
  ihave Hk := dirlookup_ctx_entry _ _ _ $$ Hk
  -- +0x36  c.bnez a5,+0x5c
  by_cases hz : dn.diSize.toNat = 0
  · k_step_e (wp_s_branch cpu _ (KA.«dirlookup» + 0x36#64) true 38#13 15#5 0#5 (by decide) bop.BNE)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [hsx, hbz, decide_eq_false (fun h : dn.diSize.toNat ≠ 0 => h hz)]
    iintro Hk Hpc
    -- +0x38  c.j +0x96 : THE EMPTY DIRECTORY
    k_step_e (wp_s_j cpu _ (KA.«dirlookup» + 0x38#64) true 94#21)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    have hnone : dirFirst data (dirNrec dn.diSize.toNat) (bname 14 fn) = none := by
      rw [hz]; exact (dirFirst_None data _ _).mpr (fun j hj => absurd hj (by unfold dirNrec; omega))
    ihave Harm : dirlookupArm data dn fn hasp (k.regs 12#5) pofv false 0 0 1 0#64 $$ [Hin]
    · unfold dirlookupArm dirlookupIn
      simp only [Bool.false_eq_true, if_false]
      icases Hin with ⟨Hsl, Hpf⟩
      iframe Hsl Hpf
      ipureintro
      exact ⟨hnone, by first | rfl | trivial⟩
    iapply (dirlookup_tail cpu k k.spie k.spp _ ip dinum bm data dn dr fn hasp pofv pidv dqp dqd
        dqn false 0 0 1 v10 bs 0#64
        (by have := hs.hK; unfold dirlookupSlots at this; omega) hs.hal ?t2 ?t10 ?t24 ?t25
        ?t26 ?t27)
      $$ [$Hk $Hpc $Hframe $Hde $Hte $Hce $Hkeep $Harm $Hnext]
    all_goals (simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] <;>
      first | rfl | skip)
  · k_step_e (wp_s_branch cpu _ (KA.«dirlookup» + 0x36#64) true 38#13 15#5 0#5 (by decide) bop.BNE)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [hsx, hbz, decide_eq_true hz]
    iintro Hk Hpc
    -- into the scan at record 0
    ihave IH := dirlookup_loop RD NC IG PA Γ k j γl pd pav pu γkl γk ip dinum bm data dn dr fn
      hasp pofv pidv dqp dqd dqn hs hpd (dirNrec dn.diSize.toNat + 2) $$ Henv
    ihave IH := dirlookupLoop_elim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ IH
    iapply IH $$ %cpu %k.spie %k.spp %_ %0 %v10 %bs [] Hk Hpc Hframe Hde Hte Hce Hkeep Hin Hnext
    ipureintro
    refine ⟨?_, by omega, (dirFirst_None data 0 _).mpr (fun j hj => absurd hj (by omega)),
      by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] <;>
      first | rfl | exact ha0 | skip

set_option maxHeartbeats 16000000 in
/-- **`dirlookup` meets its specification**, at either entry `SIE`: the
whole function is a level-0 stretch (it takes no spinlock of its own), so
every step may migrate the thread at `SIE = true` (`k_step_e`), the
complement follows it, and readi (the only sleeper) takes it at its eb
contract.  The caller's continuation is a `true` crossing at a process, so it
is hart-free from the start (`dirlookup_post_of_spec`). -/
theorem dirlookup_main (RD : READI) (NC : NAMECMP) (IG : IGET) (PA : PANIC)
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (pd pav pu : BitVec 64) (j : Nat)
    (γkl : GName) (γk : KmemNames)
    (ip : BitVec 64) (dinum : BitVec 32) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (dn dr : Dinode) (fn : Nat → BitVec 8) (hasp : Bool) (pofv : BitVec 32)
    (pidv : BitVec 32) (dqp dqd dqn : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : dirlookupSlots ≤ k.avail)
    (hnoff : k.noff = 0)
    (htier : k.tier = KTier.kpt)
    (htype : dn.diType = T_DIR)
    (hgeom : logGeomOk fscCov fscLogst) (hwf : blkmapWf fscCov fscLogst bm)
    (hcov : bmCovers bm dn.diSize.toNat) (hsz : dn.diSize.toNat ≤ MAXFILE * BSIZE)
    (hholes : blkHolesZero bm data)
    (hinums : dirInumsOk data (dirNrec dn.diSize.toNat) icfgNib)
    (hdisj : dn.diNlink.toNat ≠ 0 ∨ (bname 14 fn ≠ dotName ∧ bname 14 fn ≠ dotdotName))
    (horph : dirOrphanClean dn data)
    (hdrnz : dr.diType.toNat ≠ 0) (hdrnl : dr.diNlink = dn.diNlink)
    (hpd : descPageRw pd)
    (ha0 : k.regs 10#5 = ip)
    (hpoff : if hasp then k.regs 12#5 ≠ 0#64 else k.regs 12#5 = 0#64) :
    wp_dirlookup_eb_body (hlc := hlc) (GF := GF) Γ cpu k γl pd pav pu j γkl γk ip dinum bm data
      dn dr fn hasp pofv pidv dqp dqd dqn
      hj hproc hK hnoff htier htype hgeom hwf hcov hsz hholes hinums hdisj horph
      hdrnz hdrnl hpd ha0 hpoff := by
  unfold wp_dirlookup_eb_body
  have hK12 : 12 ≤ k.avail := by unfold dirlookupSlots at hK; omega
  iintro ⟨Hk, Hpc, #Hpi, Hte, Hce, #Hpe, #Hbc, #Hdc, #Hkl, #Hav, Hdev, Hmeta, Hmap, Hblk,
    Hnm, Hpf, Hpid, Hbsl, #Hit2, #Hiti, #Hinv, Hsl, Hlk, Hdi, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hkwf, Hk⟩
  have hlocks : k.locks = [] := List.eq_nil_of_length_eq_zero (by have := hkwf.2.2.2.1; omega)
  ihave Hnext := dirlookup_post_of_spec hj cpu k hproc ip dinum bm data dn dr fn hasp pofv pidv
    dqp dqd dqn $$ Hnext
  ihave Hkeep : dirlookupKeep k ip dinum bm data dn dr fn pidv dqp dqd dqn
    $$ [Hdev Hmeta Hmap Hblk Hnm Hpid Hbsl Hlk Hdi]
  · unfold dirlookupKeep; iframe
  ihave Hin : dirlookupIn hasp (k.regs 12#5) pofv $$ [Hsl Hpf]
  · unfold dirlookupIn; iframe
  ihave #Henv : dirlookupEnv (hlc := hlc) Γ γl pd pav pu γkl γk $$ []
  · unfold dirlookupEnv; iframe #
  simp only [dirlookupAddr]
  -- +0x00 .. +0x14  the prologue
  iapply (wp_prologue_dirlookup cpu k KA.«dirlookup» hK12)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  k_next_e
  iintro Hk Hpc ⟨%w9, %w10, %w11, Hframe⟩
  icases dirlookup_frame_open _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hframe with ⟨%hal, Hframe, Hde⟩
  have hs : DirlookupStatic k j bm data dn dr fn hasp :=
    { hj := hj, hproc := hproc, hK := hK, hnoff := hnoff, hlocks := hlocks,
      htier := htier, htype := htype, hgeom := hgeom, hwf := hwf, hcov := hcov, hsz := hsz,
      hholes := hholes, hinums := hinums, hdisj := hdisj, horph := horph, hdrnz := hdrnz,
      hdrnl := hdrnl, hpoff := hpoff, hal := hal }
  k_norm_g
  iapply (dirlookup_setup RD NC IG PA Γ cpu k γl pd pav pu j γkl γk ip dinum bm data dn dr fn
      hasp pofv pidv dqp dqd dqn _ w9 _ hs hpd ha0 rfl)
    $$ [$Hk $Hpc $Hframe $Hde $Hte $Hce $Hkeep $Hin $Henv $Hnext]

end

/-- `dirlookup`'s proof, from its callees' interfaces (Rocq's
`DirlookupProof`). -/
theorem dirlookup_proof (RD : READI) (NC : NAMECMP) (IG : IGET) (PA : PANIC) : DIRLOOKUP :=
  ⟨fun Γ _ cpu k γl pd pav pu j γkl γk ip dinum bm data dn dr fn hasp pofv pidv dqp dqd dqn hj
    hproc hK hnoff htier htype hgeom hwf hcov hsz hholes hinums hdisj horph hdrnz
    hdrnl hpd ha0 hpoff =>
  dirlookup_main RD NC IG PA Γ cpu k γl pd pav pu j γkl γk ip dinum bm data dn dr fn hasp pofv pidv
    dqp dqd dqn hj hproc hK hnoff htier htype hgeom hwf hcov hsz hholes hinums hdisj
    horph hdrnz hdrnl hpd ha0 hpoff⟩

end Xv6
