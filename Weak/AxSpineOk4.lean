/-
Weak: **the Sv39 translation at `execA`** — the three-level walk, the TLB fill / hit / miss and the
`translateAddr` front, then THE TRANSLATION over the image tree (`execATranslateAddrImg`):
`CommonWalk` / `PtTree` / `PtTreeAdue` replayed at the path interpreter.  The PTE reads are `execA`
premises (discharged at a slot by `execAPtReadPteSlot`); every register-only probe transfers from
its SC `exec` lemma through `rfF` (`execAOfRfF`).

Rocq: `iris/AxSpineOk4.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. SPELLING (as `Weak/ExecSC9.lean` / `Weak/WeakWalkEff.lean` deviation 1): `mword n` ↦ `BitVec n`,
   `register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `vec_access_dec v i` ↦ `v[i]!`, `vec_update_dec` ↦ `vectorUpdate`, `uint` ↦ `toNat`,
   `mword_of_int 0 : mword 16` ↦ `0#16`, `tt` ↦ `()`, `MISA_C` ↦ `misaC`, `MENVCFG_S` ↦ `menvcfgS`,
   `ram_base + ram_size` ↦ `ramEnd`, `autocast (PPN_of_PTE pte0)` ↦ `ppn0 pte0`, `autocast satp` /
   `autocast pte` ↦ the word itself, `pt_base t` ↦ `t.base`.  The SC hypotheses `H2i`/`H1i`/`H0i`
   (`∀ s, exec (pte_is_invalid …) s = Some (false, s)`) are `pteValid`, `H2nl`/`H1nl` `ptePtr`, `H0nl`
   `pteLeaf`, `Hchk0` `pteCheckOk`, `H0N` `(_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false`
   (the `ExecSC9` vocabulary); the section `Let`s `addr2/1/0` are inlined (`uPteAddr …`); each
   lemma takes the section variables/hypotheses it uses as arguments.
2. THE WALK is Lean's well-founded `pt_walk` (`ExecSC9` deviation 1): no `Acc` argument
   (`execARecWalkLeaf`/`execARecWalkL1` are about `pt_walk … 0/1 …`); the leaf record is
   `uWalkOut` (Rocq's literal record with the `autocast`s).  The scripts replay `ExecSC9`'s at `execA`
   (the Lean-only tactic `ax_spine4_run`, `exec_run` with the `execA` bind kit swapped in, and the
   Lean-only `AxSpineOk4.execAIte`), not Rocq's `assert_exp'`/`and_boolM` steps (Lean's model has
   no `and_boolM`; deviation as `AxSpineOk` dropped lemmas).
3. `execARBind0`: Rocq `Defs.bind0 m n` ↦ `m >>= fun _ => n` (`AxSpineOk` deviation 4).
4. `execACurrentlyEnabledSvnapot`'s premise is `s.regs .misa = misaC` (Rocq `MISA_C`); transferred
   from `ExecSC2.execCurrentlyEnabledSvnapot`.
5. `execAAddToTLBUser` / `execATranslateTLBMissUser`: the TLB entry is `uWalkEntry` (Rocq
   `CommonWalk.u_walk_entry`, the `ExecSC9` name); `tlb_hash (__id 39) vpn` ↦ `tlb_hash 39 vpn`.
6. `execAPtReadPteSlot`: `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem` (`inRam a 8`; WeakWalkEff
   deviation 6), `ram_base + ram_size ≤ uint pmpaddr0 * 4` ↦ `ramEnd ≤ (…)[0]!.toNat * 4`; the
   no-wrap bound and the CLINT/SIG/HTIF/dev side conditions come from `inRam` (as `wptReadPteSlot`).
7. `tlbExact` / `execATranslateAddrImg`: `ptree_maps` ↦ `AxPtProt.ptreeMaps`, `pt_addr2/1/0` ↦
   `AxPtProt.ptAddr2/1/0`, `svpn_of` ↦ `WeakKpt.svpnOf`, `pma_allows_pte_read` ↦
   `WeakKpt.pmaAllowsPteRead`; the `translateAddr` front premises take `WeakWalkEff`'s §8 shapes
   (`BitVec.setWidth 44 (satp_to_ppn satp0) = root`, `zero_extend (m := 16) (satp_to_asid satp0) =
   0#16`, `(va != sign_extend (m := 64) (extractLsb va 38 0)) = false`, the vpn
   `BitVec.setWidth 27 (extractLsb (extractLsb va 38 0) 38 pagesize_bits)`, the output
   `zero_extend (m := 64) (ppnv +++ extractLsb va (pagesize_bits - 1) 0) = pa`).  The Rocq `let vpn`
   of `execA_translateAddr_img` is kept as a Lean `let`.
8. `execATranslateTLBHitPt`: Rocq's `uwe_pbmt` step is the inline `tlb_get_pbmt` unfolding
   (as `ExecSC9.execTranslateTLBHitPt`).

**Rocq → Lean name map.**  `execAR_bind0` `execARBind0`, `execA_currentlyEnabled_Svnapot`
`execACurrentlyEnabledSvnapot`, `H2iA` `h2iA`, `H1iA` `h1iA`, `H0iA` `h0iA`, `Hchk0A` `hchk0A`,
`execA_check_leaf_pte_leaf0` `execACheckLeafPteLeaf0`, `execA_rec_walk_leaf` `execARecWalkLeaf`,
`execA_rec_walk_l1` `execARecWalkL1`, `execA_pt_walk_user` `execAPtWalkUser`,
`execA_add_to_TLB_user` `execAAddToTLBUser`, `execA_translate_TLB_miss_user`
`execATranslateTLBMissUser`, `execA_translateAddr_pt_front` `execATranslateAddrPtFront`,
`execA_translate_TLB_hit_pt` `execATranslateTLBHitPt`, `execA_pt_read_pte_slot`
`execAPtReadPteSlot`, `tlb_exact` `tlbExact`, `tlb_exact_fill` `tlbExactFill`,
`execA_translateAddr_img` `execATranslateAddrImg`; the Ltac `nseip` ↦ the pin test decided by
`simp (config := { decide := true })` (AxSpineOk3 deviation 5).  None is in the duplicated-name
table.  Lean-only (file-qualified): `AxSpineOk4.execAIte`, `AxSpineOk4.execARThrow`; tactic
`ax_spine4_run`.

**Dropped:** none (the two empty Rocq comment stubs "miss via hash collision" declare nothing).
-/
import Weak.AxSpineOk3
import Weak.WeakKpt

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The bind kit additions -/

/-- Rocq `execAR_bind0` (deviation 3). -/
theorem execARBind0 {R X : Type} (m : SailME R Unit) (n : SailME R X) (s : ExecSt) :
    execAR (m >>= fun _ => n) s =
      match execAR m s with
      | some (.inl r, s') => some (.inl r, s')
      | some (.inr _, s') => execAR n s'
      | none => none := by
  rw [execARBind]
  rcases execAR m s with _ | ⟨_ | _, _⟩ <;> rfl

/-- (Lean-only) `execA` of an `if` is the `if` of the `execA`s. -/
theorem AxSpineOk4.execAIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X) (s : ExecSt) :
    execA (if c then a else b) s = if c then execA a s else execA b s := by
  split <;> rfl

/-- (Lean-only) An early return at `execAR`. -/
theorem AxSpineOk4.execARThrow {R X : Type} (r : R) (s : ExecSt) :
    execAR (PreSail.PreSailME.throw r : SailME R X) s = some (.inl r, s) := rfl

/-- (Lean-only, deviation 2) Rocq's `cbn`/`rewrite execA_bind_Some` steps: `exec_run` with the
`execA` kit. -/
syntax "ax_spine4_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ax_spine4_run) => `(tactic| simp (config := { decide := true }) only [execABind,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execA, execAReturnm,
      ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert, PreSail.assert, execARBind,
      execARLiftR, execARReturnRFwd, AxSpineOk4.execARThrow, decide_false, decide_true,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and])
  | `(tactic| ax_spine4_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only
      [execABind, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execA,
      execAReturnm, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert, PreSail.assert,
      execARBind, execARLiftR, execARReturnRFwd, AxSpineOk4.execARThrow, decide_false,
      decide_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, $ls,*])

/-- Rocq `execA_currentlyEnabled_Svnapot` (deviation 4). -/
theorem execACurrentlyEnabledSvnapot (s : ExecSt) (hm : s.regs .misa = misaC) :
    execA (currentlyEnabled .Ext_Svnapot) s = some (true, s) := by
  have h := execCurrentlyEnabledSvnapot s hm
  to_a h
  exact h

/-! # 2. The Sv39 walk at `execA` (Rocq section `UserWalkA`) -/

/-- Rocq `H2iA`. -/
theorem h2iA (pte2 : BitVec 64) (h2i : pteValid pte2) :
    ∀ s, execA (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb pte2 7 0))
      (ext_bits_of_PTE pte2)) s = some (false, s) :=
  fun s => execAOfRfF _ (rfFPteIsInvalid _ _) s _ (h2i s)

/-- Rocq `H1iA`. -/
theorem h1iA (pte1 : BitVec 64) (h1i : pteValid pte1) :
    ∀ s, execA (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb pte1 7 0))
      (ext_bits_of_PTE pte1)) s = some (false, s) :=
  fun s => execAOfRfF _ (rfFPteIsInvalid _ _) s _ (h1i s)

/-- Rocq `H0iA`. -/
theorem h0iA (pte0 : BitVec 64) (h0i : pteValid pte0) :
    ∀ s, execA (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0))
      (ext_bits_of_PTE pte0)) s = some (false, s) :=
  fun s => execAOfRfF _ (rfFPteIsInvalid _ _) s _ (h0i s)

/-- Rocq `Hchk0A`. -/
theorem hchk0A (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (pte0 : BitVec 64) (hchk0 : pteCheckOk acc p mxr dosum pte0) :
    ∀ s, execA (check_PTE_permission acc p mxr dosum (Mk_PTE_Flags (Sail.BitVec.extractLsb pte0 7 0))
      (ext_bits_of_PTE pte0) ()) s = some (.PTE_Check_Success (), s) :=
  fun s => execAOfRfF _ (rfFCheckPTEPermission _ _ _ _ _ _ _) s _ (hchk0 s)

/-- Rocq `execA_check_leaf_pte_leaf0`. -/
theorem execACheckLeafPteLeaf0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte0 : BitVec 64)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (pa : physaddr) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execA (check_leaf_pte 39 vpn acc p mxr dosum pte0 pa 0 ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()), s) := by
  unfold check_leaf_pte
  rw [execACatchEarlyReturn]
  ax_spine4_run
  erw [h0iA pte0 h0i s]
  ax_spine4_run
  erw [h0nl]
  ax_spine4_run
  erw [hchk0A acc p mxr dosum pte0 hchk0 s]
  ax_spine4_run [execACurrentlyEnabledSvnapot s hmisa]
  erw [h0N]
  ax_spine4_run [hmenv, hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `execA_rec_walk_leaf` (deviation 2): level 0, the leaf. -/
theorem execARecWalkLeaf (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte1 pte0 : BitVec 64)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execA (pt_walk 39 vpn acc p mxr dosum (uNextBase pte1) 0 g ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        (g || uGbit pte0), ()), s) := by
  rw [pt_walk]
  ax_spine4_run
  erw [hrd0]
  ax_spine4_run
  erw [h0iA pte0 h0i s]
  ax_spine4_run [Functions.not, AxSpineOk4.execAIte]
  erw [execACheckLeafPteLeaf0 vpn acc p mxr dosum pte0 h0i h0nl hchk0 h0N _ menvcfg0 s hmisa hmenv hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `execA_rec_walk_l1` (deviation 2): level 1, a pointer into the leaf. -/
theorem execARecWalkL1 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte2 pte1 pte0 : BitVec 64)
    (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execA (pt_walk 39 vpn acc p mxr dosum (uNextBase pte2) 1 g ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        ((g || uGbit pte1) || uGbit pte0), ()), s) := by
  rw [pt_walk]
  ax_spine4_run
  erw [hrd1]
  ax_spine4_run
  erw [h1iA pte1 h1i s]
  ax_spine4_run [Functions.not, AxSpineOk4.execAIte]
  erw [h1nl]
  ax_spine4_run [AxSpineOk4.execAIte]
  erw [execARecWalkLeaf vpn acc p mxr dosum pte1 pte0 h0i h0nl hchk0 h0N _ menvcfg0 s hmisa hrd0 hmenv
    hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `execA_pt_walk_user`: the full three-level walk. -/
theorem execAPtWalkUser (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s))
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execA (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        (uGlobal pte2 pte1 pte0), ()), s) := by
  rw [pt_walk]
  ax_spine4_run
  erw [hrd2]
  ax_spine4_run
  erw [h2iA pte2 h2i s]
  ax_spine4_run [Functions.not, AxSpineOk4.execAIte]
  erw [h2nl]
  ax_spine4_run [AxSpineOk4.execAIte]
  erw [execARecWalkL1 vpn acc p mxr dosum pte2 pte1 pte0 h1i h1nl h0i h0nl hchk0 h0N _ menvcfg0 s hmisa
    hrd1 hrd0 hmenv hpbmte]
  rfl

/-- Rocq `execA_add_to_TLB_user` (deviation 5). -/
theorem execAAddToTLBUser (vpn : BitVec 27) (pte2 pte1 pte0 : BitVec 64) (asid : BitVec 16)
    (s : ExecSt) :
    execA (add_to_TLB 39 asid vpn (ppn0 pte0) pte0
        (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 0
        (uGlobal pte2 pte1 pte0)) s =
      some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn)
        (some (uWalkEntry vpn pte2 pte1 pte0 asid)))) :=
  execAOfRfF _ (rfFAddToTLB _ _ _ _ _ _ _ _) s _ (execAddToTLBPt _ _ _ _ _ _ s)

/-- Rocq `execA_translate_TLB_miss_user`: success, the leaf's A (and D) bits need no update. -/
theorem execATranslateTLBMissUser (vpn : BitVec 27) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (asid : BitVec 16) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC) (hnoupd : update_PTE_Bits pte0 acc = none)
    (hrd2 : execA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s))
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execA (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn)
          (some (uWalkEntry vpn pte2 pte1 pte0 asid)))) := by
  unfold translate_TLB_miss
  ax_spine4_run
  erw [execAPtWalkUser vpn acc p mxr dosum root pte2 pte1 pte0 h2i h2nl h1i h1nl h0i h0nl hchk0 h0N
    menvcfg0 s hmisa hrd2 hrd1 hrd0 hmenv hpbmte]
  unfold uWalkOut update_and_write_pte
  ax_spine4_run
  erw [hnoupd]
  ax_spine4_run
  erw [execAAddToTLBUser]

/-! # 3. The `translateAddr` front (Rocq section `PtFrontA`) -/

/-- Rocq `execA_translateAddr_pt_front` (deviation 7). -/
theorem execATranslateAddrPtFront (acc : MemoryAccessType mem_payload) (p : Privilege)
    (vpn : BitVec 27) (root ppnv : BitVec 44) (satp0 va pa : BitVec 64) (s s' : ExecSt)
    (heff : exec (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s))
    (hss : exec (is_shadow_stack_access acc) s = some (false, s))
    (hcp : s.regs .cur_privilege = p)
    (htm : exec (translationMode p) s = some (.Sv39, s))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38
      Functions.pagesize_bits) = vpn)
    (htr : ∀ mxr dosum, execA (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Ok (ppnv, .PBMT_PMA, ()), s'))
    (hident : zero_extend (m := 64) (ppnv +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)
      = pa) :
    execA (translateAddr (.Virtaddr va) acc) s =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), s') := by
  have heffA := execAOfRfF _ (rfFEffectivePrivilege _ _ _) s _ heff
  have hssA := execAOfRfF _ (rfFIsShadowStackAccess _) s _ hss
  have htmA := execAOfRfF _ (rfFTranslationMode _) s _ htm
  have hw : execA (satp_mode_width_forwards .Sv39) s = some (39, s) := rfl
  have hgs : execA (get_satp 39) s = some (satp0, s) := by
    unfold get_satp
    ax_spine4_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [execACatchEarlyReturn]
  ax_spine4_run [hcp, heffA, htmA, hssA, hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr]
  erw [hgs]
  ax_spine4_run [hcanon]
  erw [hasid, hppn, hvpn, htr]
  ax_spine4_run
  subst hident
  rfl

/-! # 4. A TLB hit (Rocq section `PtHitA`) -/

/-- Rocq `execA_translate_TLB_hit_pt` (deviation 8). -/
theorem execATranslateTLBHitPt (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat) (s : ExecSt)
    (hchk : pteCheckOk acc p mxr dosum q0) (hupd : update_PTE_Bits q0 acc = none)
    (hpb : ptePbmt0 q0) :
    execA (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn p2 p1 q0 asid)) s =
      some (.Ok (ppn0 q0, .PBMT_PMA, ()), s) := by
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe]
  ax_spine4_run
  erw [hchk0A acc p mxr dosum q0 hchk s]
  unfold update_and_write_pte
  ax_spine4_run
  erw [hupd]
  unfold tlb_get_pbmt
  ax_spine4_run
  erw [hpb]
  rfl

/-! # 5. The PTE slot read and THE TRANSLATION (image regime), at `execA` -/

/-- Rocq `execA_pt_read_pte_slot` (deviation 6). -/
theorem execAPtReadPteSlot (sg : ExecSt) (a w : BitVec 64) (region : PMA_Region)
    (hslot : WeakWalkEff.ptSlotMem sg a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hm : matching_pma_region (sg.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hhtif : sg.regs .htif_tohost_base = none) :
    execA (read_pte (.Physaddr a) 8) sg = some (.Ok w, sg) := by
  obtain ⟨hb, hram, hal⟩ := hslot
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((sg.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match := by
    rw [hz, h8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
  have hwf : paZ a + 8 ≤ 2 ^ 64 := by
    have := hram.2
    unfold ramEnd at this
    unfold paZ
    omega
  exact execAReadPteS a region w sg hA hlt hr hR hm hal hpte (execWithinClintRam a 8 sg hram)
    (execWithinSigFalse a 8 sg) (execWithinHtifNone a 8 sg hhtif) (devAddrRam a 8 hram) hwf hb

/-- Rocq `tlb_exact` (deviation 7): the TLB holds only EXACT walk entries of the (immutable) image
tree — under D3 (A/D preset) no A/D variant is ever cached. -/
def tlbExact (t : PTree) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) : Prop :=
  ∀ (vpn' : BitVec 27) (ent : TLB_Entry),
    tlbvec[tlb_hash 39 vpn']! = some ent →
    ∃ (vpn : BitVec 27) (q2 q1 q0 : BitVec 64), AxPtProt.ptreeMaps t vpn q2 q1 q0 ∧
      tlb_hash 39 vpn = tlb_hash 39 vpn' ∧
      ent = uWalkEntry vpn q2 q1 q0 0#16

/-- Rocq `tlb_exact_fill`. -/
theorem tlbExactFill (t : PTree) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27)
    (p2 p1 p0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 → tlbExact t tlbvec →
    tlbExact t (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))) := by
  intro hmaps hok vpn' ent hget
  by_cases hh : tlb_hash 39 vpn' = tlb_hash 39 vpn
  · rw [hh, AxPtProt.vecUpdSame _ _ _ (AxPtProt.tlbHashLt vpn)] at hget
    exact ⟨vpn, p2, p1, p0, hmaps, hh.symm, (Option.some.inj hget).symm⟩
  · rw [AxPtProt.vecUpdNe _ _ _ _ hh] at hget
    exact hok vpn' ent hget

/-- Rocq `execA_translateAddr_img` (deviation 7): THE TRANSLATION over the image tree — a TLB hit
on the exact entry leaves the state, a miss (empty or foreign slot) walks and fills. -/
theorem execATranslateAddrImg (acc : MemoryAccessType mem_payload) (p : Privilege)
    (rootPpn : BitVec 44) (va w pa satp0 : BitVec 64) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 : BitVec 64) (σ : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    (∀ (mxr dosum : Bool), pteCheckOk acc p mxr dosum w) →
    update_PTE_Bits w acc = none →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    ptePbmt0 w →
    t.base = rootPpn →
    AxPtProt.ptreeMaps t vpn p2 p1 w →
    tlbExact t tlbvec →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 t vpn) p2 →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 vpn) p1 →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 vpn) w →
    σ.regs .misa = misaC →
    σ.regs .menvcfg = menvcfgS →
    σ.regs .htif_tohost_base = none →
    σ.regs .cur_privilege = p →
    exec (translationMode p) σ = some (.Sv39, σ) →
    exec (effectivePrivilege acc (σ.regs .mstatus) p) σ = some (p, σ) →
    exec (is_shadow_stack_access acc) σ = some (false, σ) →
    σ.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = rootPpn →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    σ.regs .tlb = tlbvec →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (σ.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) →
    ∃ σ',
      execA (translateAddr (.Virtaddr va) acc) σ =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), σ') ∧
      (σ' = σ ∨
        σ' = σ.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn)
          (some (uWalkEntry vpn p2 p1 w 0#16)))) := by
  intro vpn hchk hupd hcanon hout hpb hbase hmaps htlbok hsm2 hsm1 hsm0 hmisa hmenv hhtif hcp htm
    heff hss hsatp hppn hasid htlb hA hord hR hcov hpmar
  obtain ⟨c1, c0, -, -, -, -, -, -, -, hv2, hn2, hv1, hn1, hv0, hl0, hnap, -⟩ := id hmaps
  have ha2 : AxPtProt.ptAddr2 t vpn = uPteAddr rootPpn (Sail.BitVec.extractLsb vpn 26 18) := by
    unfold AxPtProt.ptAddr2; rw [hbase]; rfl
  have hsm2' : WeakWalkEff.ptSlotMem σ (uPteAddr rootPpn (Sail.BitVec.extractLsb vpn 26 18)) p2 :=
    ha2 ▸ hsm2
  obtain ⟨region2, hm2, hs2⟩ := hpmar _ hsm2'.2.1
  obtain ⟨region1, hm1, hs1⟩ := hpmar _ hsm1.2.1
  obtain ⟨region0, hm0r, hs0⟩ := hpmar _ hsm0.2.1
  have hrd2 := execAPtReadPteSlot σ _ p2 region2 hsm2' hA hord hR hcov hm2 hs2 hhtif
  have hrd1 := execAPtReadPteSlot σ (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1
    region1 hsm1 hA hord hR hcov hm1 hs1 hhtif
  have hrd0 := execAPtReadPteSlot σ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) w
    region0 hsm0 hA hord hR hcov hm0r hs0 hhtif
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  -- the miss path, shared by the empty and the foreign slot
  have hmiss : execA (lookup_TLB 39 0#16 vpn) σ = some (none, σ) →
      ∃ σ', execA (translateAddr (.Virtaddr va) acc) σ =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), σ') ∧
        σ' = σ.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn)
          (some (uWalkEntry vpn p2 p1 w 0#16))) := by
    intro hlk
    refine ⟨_, ?_, rfl⟩
    refine execATranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ heff hss hcp htm hsatp
      hppn hasid hcanon rfl (fun mxr dosum => ?_) hout
    unfold translate
    rw [execABindSome _ _ _ _ _ hlk]
    rw [← htlb]
    exact execATranslateTLBMissUser vpn rootPpn p2 p1 w acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0
      (hchk mxr dosum) hnap 0#16 menvcfgS σ hmisa hupd hrd2 hrd1 hrd0 hmenv hpbmte
  cases hslot : tlbvec[tlb_hash 39 vpn]! with
  | none =>
    have hlk := execLookupTLBMiss vpn 0#16 tlbvec σ htlb hslot
    to_a hlk
    obtain ⟨σ', htr, heq⟩ := hmiss hlk
    exact ⟨σ', htr, Or.inr heq⟩
  | some ent =>
    obtain ⟨vpn0, q2, q1, q0, hm0, -, hent⟩ := htlbok vpn ent hslot
    by_cases hne : vpn0 = vpn
    · rw [hne] at hm0 hent
      obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet t vpn q2 q1 q0 p2 p1 w hm0 hmaps
      rw [h2, h1, h0] at hent
      rw [hent] at hslot
      have hlk := execLookupTLBHitEnt vpn 0#16 tlbvec _ σ htlb hslot
        (WeakKpt.uweMatchSelf vpn p2 p1 w 0#16)
      to_a hlk
      refine ⟨σ, ?_, Or.inl rfl⟩
      refine execATranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ heff hss hcp htm
        hsatp hppn hasid hcanon rfl (fun mxr dosum => ?_) hout
      unfold translate
      rw [execABindSome _ _ _ _ _ hlk]
      exact execATranslateTLBHitPt acc p mxr dosum vpn p2 p1 w 0#16 (tlb_hash 39 vpn) σ
        (hchk mxr dosum) hupd hpb
    · have hlk := execLookupTLBNomatchS vpn 0#16 ent tlbvec σ htlb hslot
        (by rw [hent]; exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 q0 0#16 hne)
      to_a hlk
      obtain ⟨σ', htr, heq⟩ := hmiss hlk
      exact ⟨σ', htr, Or.inr heq⟩

end Weak
