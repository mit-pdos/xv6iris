/-
Weak: **the COMPRESSED width-8 STORE (`c.sdsp`) under the all-OFF boot PMP**
(M4, the `start()` prologue seam).

Rocq: `iris/WeakLeafSdspOff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `start()` opens with two `c.sdsp`s through
`sp`, executed BEFORE the `pmpcfg0` write, so the PMP is still all-OFF.
`WeakLeafSd8.wwpSd8Leaf` has the right PMP premise (`pmpAllOff`) but the wrong
fetch (`F_Base`); `WeakLeafTor.wwpSd8TorRvcLeaf` has the right fetch (`F_RVC`,
either alignment via `al4`) but wants a written TOR entry.  This file is the
missing corner: the TOR compressed store leaf with its PMP premise swapped back
to `pmpAllOff` (which implies both the fetch side, `pmpAllowsAll`, and the
data side, inside `execEffSd8At`), and no `pmpaddr_n` anywhere.  §1 reuses
`execEffSd8At` at the shifted successor `npc - 4` and folds the shift away;
§2 is the `wPEff` half; §3 the leaf.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: as `Weak/WeakLeafTor.lean` deviation 1 (GPR reads
   `s.gpr r`, stated at `(wflatSt σ).gpr` in the `wPEff` half; GPR cells
   `gpr cpu r (DFrac.own 1) v` with `rs.toNat ≠ 0`; `∀ j < 8, addr_is_ram
   (pa_add ea j)` ↦ `inRam ea 8`; `pma_allows_all` ↦ `pma_regions = bootPMA`;
   `pmp_all_off` ↦ `MachCSL.pmpAllOff`; `pmp_all_off_allows_all` ↦
   `fun i => (h i).2`; `avi_assoc`/`avi0` ↦ `BitVec.add_assoc`/`add_zero` on
   `BitVec.addInt`'s unfolding).
2. O2 (owner decision): the fetch element is
   `.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)` (Rocq
   `WEread wak_plain …`); the extra `fetchPin` premise of
   `wPEffOfLeafRvc` is discharged inside `wPEffSd8Rvc` by
   `WeakLeafTor.fetchPinRvc` from the text bytes.
3. THE CONFIG INTERFACE (owner decision Q3; WeakFunnel deviation 7): Rocq's
   `mmode_config (DfracOwn q)` ∗ `pmpcfg_n ↦ᵣ{q} pmpcfg0` ↦
   `mConf cpu (DFrac.own q) c ∗ clockCells cpu` with `pmpcfg0 := c.pmpcfg`,
   plus the premise `MConf.mok c`.  The whole `mConf` goes to the funnel (no
   halves: with the TOR grant gone, no register outside the funnel's reads is
   needed) and comes back whole, as in `WeakLeafSd8.wwpSd8Leaf`.  `GenId`/`CpuId`
   are the explicit `gen`/`cpu`, `WWP Loop` is `wwpTriv ⊤ (WExpr.loop gen cpu)`.
4. STATEMENT SHAPES: `A -∗ B -∗ C` ↦ `A ⊢ B -∗ C`; the agreement premise
   quantifies over a `RegFile`, `mword_of_int 0` ↦ `0#64`; the decode's first
   shape uses `decodeFetch`/`privMSU`/`cfgOk`/`misaC`.
5. `exec_eff_sd8_off_at`'s successor `MState (sregs s) (write_bytes …) …` is
   the literal `⟨s.regs, bmWrite s0.mem ea 8 vs, s0.dev⟩` (WeakLeafSd8
   deviation 5).
6. Rocq §4's `Print Assumptions` are not declarations.

**Rocq → Lean name map.**  `exec_eff_sd8_off_at` `execEffSd8OffAt`,
`wP_eff_sd8_rvc` `wPEffSd8Rvc`, `wwp_sd8_off_rvc_leaf` `wwpSd8OffRvcLeaf`
(none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 3 lemmas; Lean 3 theorems).
-/
import Weak.WeakLeafTor

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE `execute` MIRROR, AT A GENERIC SUCCESSOR PC -/

/-- Rocq `exec_eff_sd8_off_at` (deviations 1, 5): `execEffSd8At` at the
successor `npc - 4`, the shift folded away. -/
theorem execEffSd8OffAt (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (rs1 rs2 : BitVec 5)
    (imm : BitVec 12) (ea vs : BitVec 64) :
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    s0.gpr rs2 = vs →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)))
        ((s0.setReg .minstret_increment b).setReg .nextPC npc) =
      some (RETIRE_SUCCESS,
        ⟨((s0.setReg .minstret_increment b).setReg .nextPC npc).regs,
          bmWrite s0.mem ea 8 vs, s0.dev⟩,
        [.WEwrite wakPlain ea 8 vs]) := by
  intro lpriv lmprv lpmm lpmp lpma lhtif hea hvs hal hram
  have H := execEffSd8At s0 b (BitVec.addInt npc (-4)) rs1 rs2 imm ea vs lpriv lmprv lpmm lpmp lpma
    lhtif hea hvs hal hram
  have hz : BitVec.addInt (BitVec.addInt npc (-4)) 4 = npc := by
    unfold BitVec.addInt
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-4) + BitVec.ofInt 64 4 = 0#64 by decide,
      BitVec.add_zero]
  rw [hz] at H
  exact H

/-! ## 2. THE `wPEff` HALF -/

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_sd8_rvc` (deviations 1-2, 4): `WeakLeafTor.wPEffSd8Tor` with
the PMP pair replaced by `pmpAllOff`. -/
theorem wPEffSd8Rvc (al4 : Bool) (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (vold vs : BitVec 64)
    (cid8 : CPU) (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    (wflatSt σ).gpr rs2 = vs →
    inRam ea 8 →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      vwpHold (wpt8Own (GF := GF) cid8 ea vold) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEwrite wakPlain ea 8 vs]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lmprv lpmm lelp hal2 hal4 hea
    hvs hram hagree hDmi hgood hdec hgood0 hexp
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_RVC h) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt8OwnAlign cid8 ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hfp := wpt8OwnFlatPin cid8 σ ea vold hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨haccea, hflatpin⟩ := hfp
  obtain ⟨-, ⟨-, hrampc, w, ⟨hsub, hisRVC⟩, htext⟩⟩ := hfok
  apply wPEffOfLeafRvc al4 cid σ (wwin pc ea 8) pc h w i0 (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))
    [.WEwrite wakPlain ea 8 vs] D D0 dst hwf
    (wwinNonzero pc ea 8 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 8 j hram hj))
    (wwinPinned σ pc ea 8 haccpc haccea (fun j hj => (htp j hj).1) (fun j hj => (hflatpin j hj).2))
  · exact WeakLeafTor.fetchPinRvc al4 σ pc _ (fun ak pa n he => by cases he)
      (fun j hj => (htp j hj).2)
  · exact lpc
  · exact lpriv
  · exact fun i => (lpmp i).2
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmisaC
  · exact lmIE
  · exact lelp
  · exact hal2
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 8 w htext
  · exact hsub
  · exact hisRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · exact hgood0
  · exact hexp
  · intro b
    have hfacts := storeRegsFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2)
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hvs_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ : ExecSt).gpr rs2 = vs := by
      unfold ExecSt.gpr at hvs ⊢; exact hvs
    have hrun := execEffSd8OffAt ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 8), σ.wmDev⟩ b
      (BitVec.addInt pc 2) rs1 rs2 imm ea vs lpriv lmprv lpmm lpmp lpma lhtif hea_c hvs_c halea hram
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · exact hfacts.1.trans lhart
    · exact hfacts.2.1
    · dsimp only
      exact wwinWdom σ pc ea 8 vs

end wPEffHalf

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_sd8_off_rvc_leaf` (deviations 1-4): `WeakLeafTor.wwpSd8TorRvcLeaf`
minus the `pmpaddr_n` grant, with `pmpAllOff c.pmpcfg`. -/
theorem wwpSd8OffRvcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (h : BitVec 16)
    (rs1 rs2 : BitVec 5) (imm : BitVec 12) (i0 : instruction) (ea : PAddr) (vold : BitVec 64)
    (R : VProp GF) (q : Qp) (c : MConf) (rs1v rs2v npc0 : BitVec 64) (D D0 : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    rs2.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      ∃ i0' : instruction,
        exec (decodeFetch (.F_RVC h)) t = some (i0', t) ∧
        is_lpad_instruction i0' = false ∧
        (∀ s : ExecSt, exec (execute i0') s =
          some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s))) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s =
      some (.ExecuteAs (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)), s)) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rs2 (DFrac.own 1) rs2v -∗
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8Own (GF := GF) cpu ea vold) ws -∗
      vwpHold R ws -∗
      (∀ (ws' : Wstate) (T : Nat),
        ⌜wsLe ws ws'⌝ -∗
        ⌜∀ j : Nat, j < 8 → T ≤ flr (wsView ws') (WeakInterp.accAddr ea j)⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 2) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rs2 (DFrac.own 1) rs2v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8Own (GF := GF) cpu ea rs2v) ws' -∗
        R.monPred_at (viewScl T) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrs1nz hrs2nz hea hram hdecf hagree hDmi hgood hdec hgood0 hexp
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  have hdecW : winstrDec (.F_RVC h) (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) (.F_RVC h)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  have hcert : wstepCert cpu.val pc
      (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
        [.WEwrite wakPlain ea 8 rs2v])) (wQStore8 (some cpu.val) ea rs2v) :=
    wcertStoreW 8 cpu.val pc WeakFetchEff.wakIfetch pc (if al4 then 4 else 2) wakPlain ea rs2v
  -- THE WHOLE config goes to the funnel: it hands the reads back
  iapply wwpInstr gen cpu pc true (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) c (DFrac.own q)
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++
      [.WEwrite wakPlain ea 8 rs2v]))
    (wQFr (wQStore8 (some cpu.val) ea rs2v) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc (if al4 then 4 else 2)] ++ [.WEwrite wakPlain ea 8 rs2v]))
    hgid haccpc hmok (fun i => (hpmp i).2) (wstepCertFr _ _ _ _ hcert) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the TWO registers the funnel does not read: base and data
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs2 _ rs2v hrs2nz) $$ Hreg Hrs2c with ⟨%Lrs2a, Hreg, Hrs2c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  have Lrs2 : (wflatSt σ).gpr rs2 = rs2v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs2 (by decide)]
    exact Lrs2a
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllOff (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  -- ---- the certificate's precondition (§2) ----
  icases WeakLeafLw4.keepPure2 (wPEffSd8Rvc al4 cpu.val σ pc h rs1 rs2 imm i0 ea vold rs2v cpu D D0 dst
      hwf Lpc0 Lpriv lpmp_σ Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp hal2 hal4 hea_σ
      Lrs2 hram hag_σ hDmi hgood hdec hgood0 hexp) $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  icases keepPure1 (wpt8OwnAlign cpu ea vold σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffSd8OffAt (wflatSt σ) b (BitVec.addInt pc 2) rs1 rs2 imm ea rs2v Lpriv Lmprv Lpmm
    lpmp_σ Lpma Lhtif hea_σ Lrs2 halea hram
  obtain ⟨sE, hsE⟩ : ∃ sE : ExecSt, sE =
      ⟨(((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs,
        bmWrite (wflatSt σ).mem ea 8 rs2v, (wflatSt σ).dev⟩ := ⟨_, rfl⟩
  rw [← hsE] at hexf
  have hsEregs : sE.regs = (((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC
      (BitVec.addInt pc 2) := by rw [hsE]; rfl
  have hsEdev : sE.dev = σ.wmDev := by rw [hsE]; rfl
  have hsEnpc : sE.regs .nextPC = BitVec.addInt pc 2 := by
    rw [hsE]; exact (storeRegsFacts (wflatSt σ) b (BitVec.addInt pc 2)).2.2
  -- ---- the ONE register write the wrapper expects: nextPC ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 2))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [← hsEregs]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists sE
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt %hpost %hQ Hm' Hclk' Hpc'
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, ⟨kc, hQl, -⟩, -, hQv⟩, hQeff⟩ := hQ
  -- the release deposit: freeze R at the store's own timestamp
  ihave HRdep := wwpReleaseDeposit R σ hbnd $$ HR
  -- THE WINDOW UPDATE: retarget the eight elements at the message `wQStore8` names
  icases wpt8OwnAtElems cpu ea vold σ.wmWs $$ Hpt with
    ⟨%halea2, %haccea, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7,
      H0, S0, H1, S1, H2, S2, H3, S3, H4, S4, H5, S5, H6, S6, H7, S7⟩
  imod wlat8StorePrimOwn cpu kc σ ea rs2v t0 t1 t2 t3 t4 t5 t6 t7 _ _ _ _ _ _ _ _
      $$ Hlat H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7 with ⟨Hlat, Hl8⟩
  icases keepPure (winstrNv cpu _ _ pc _) $$ Hlat Hbs with ⟨%hnvpc, Hlat, -⟩
  icases keepPure (nvOkWlat8Own cpu _ _ ea _ rs2v) $$ Hlat Hl8 with ⟨%hnvea, Hlat, Hl8⟩
  imod wlogUpdate σ.wmLog [wwriteMsg (some cpu.val) kc ea 8 rs2v] $$ Hlogauth with Hlogauth
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS pc+2
  rw [hsEnpc]
  ihave Hpt' := wlat8OwnWpt8Own cpu ea (σ.wmLog.length + 1) rs2v σ'.wmWs halea2 haccea
    (fun j hj => hQv j hj) $$ Hl8
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact hnvpc j (WeakLeafTor.ltFetchW al4 j hj)
      · obtain ⟨j, hj, rfl⟩ := weffsTouchWrite1 _ ea _ _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hsEdev, hQl]
    iframe Hdev Hlogauth Hwsauth
  -- the config comes back WHOLE from the funnel: nothing to recombine
  iapply Hcont $$ %σ'.wmWs %(σ.wmLog.length + 1) %hwsle %(fun j hj => hQv j hj) Hm' Hclk'
    [Hpc' Hnpc] Hrs1c Hrs2c Hhws Hpt' HRdep
  unfold pcIs
  iframe Hpc' Hnpc

end leaf

end Weak
