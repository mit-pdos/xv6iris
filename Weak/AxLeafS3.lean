/-
Weak: **NON-VACUITY of the S-mode lock leaves (`AxLeafS` / `AxLeafS2`)** on the REAL Sail model,
at `AxSmodeProbe`-style concrete SUPERVISOR states (Sv39 over the real 3-level table `pT` of
AxSymCtl3, cold TLB, A/D preset; PMP TOR over RAM with R/W/X), with xv6's OWN instruction words
at VA = PA 0x80000000.

Rocq: `iris/AxLeafS3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The words: `fence rw,w` 0x0310000f (release), `sw zero, 0(s1)` 0x0004a023 (release),
`sd zero, 16(s1)` 0x0004b823 (release), `amoswap.w.aq a5, a5, (s1)` 0x0cf4a7af (acquire),
`lw a4, 536(s1)` 0x2184a703, `ld a5, 0(s4)` 0x000a3783 (kernel loads).
The state `σL W`: the probe's registers with s1 = s4 = 0x80001008 (the lock word, in the
second 4 KiB page of `pT`), a5 = 1, the probe's memory with the word `W` at 0x80000000.  For
each word: `rsLCtrlOk` (the data regime `ctrlOkSW` HOLDS at the boundary registers);
`text4*` (`textAt4S` holds — the 4-byte fetch premise); `dec*` (the decode fact `Hdec` of the
X leaf, for EVERY regime state); `data*` (`dataAtS` for the data address, Load / Store / Atomic);
`*Whole` (the WHOLE-INSTRUCTION certificate of the real `riscvStep`, both ticks, every pin
answer, at the concrete state, by `spineCertXT` / `spineCertX` from the leaf's own certificate
`CertXTLoadS` / `CertXTStoreS` / `CertXTAmoswapS` / `certExecuteFence`) — every PURE premise of
the X leaf is discharged at a real state and the certified step is the real one.  The remaining
X-leaf premises are the bridge's instance-level ones (`Htext`/`Hflow`/`Hloc`/`HG`/`Hmid`) and
the data-region side conditions.

## Deviations from Rocq

1. SPELLING as AxDataX8 / AxLeafS2: `mword_of_int k : mword n` ↦ `BitVec.ofNat n k` (`k#n`),
   `w64` ↦ `AxEpiProbe.w64`, `s_pc`/`s_sp` ↦ `sPc`/`AxSmodeProbe.sSp`, `nvS_rs` ↦ `nvSRs`,
   `register_set r v rs` ↦ `rs.set r v`, `register_lookup r rs` ↦ `rs r`, `regs_agree seip_reg`
   ↦ `regsAgree AxRunClose.pinReg`, `img_S` ↦ `imgS`, `ctrl_ok_SW` ↦ `ctrlOkSW`, `Cert` ↦
   `AxCert.Cert`, `CS d b r` ↦ `⟨d, b, r⟩`, `gpr_val` ↦ `gprVal`, `st_bytes` ↦ `stBytes`,
   `ow_ld` ↦ `owLd`, `ak_plain` ↦ `AxDataX.akPlain`, `ak_xc` ↦ `akXc`, `acc_amo` ↦ `accAmo`,
   `zero_extend' 5 'b"00"` ↦ `0#5`, `zreg` ↦ `.Regidx 0#5`, `BV 8 k` ↦ `k#8`.
   The words `W_*` and the byte function `wb` are over `Nat` (Rocq `Z`; all are nonnegative);
   `lk_va` is a `Nat` and `dk`'s address an `Int` (AxDataX8 deviation 2).
2. `σL W`'s memory is a function update of the probe's byte map `sMem` (Rocq: four gmap
   inserts into `s_mem`); its device state is the probe's `testDevs` (Rocq `dev0_state`;
   AxSpineOk8 deviation 1).
3. DECODE FACTS (Rocq: `rfF_dec_*` by `rfF_auto` + the SC decode lemmas `kd_*` of
   KernelDecode04/06/08/26 and `WpAmo.amodec`, combined by `EvA_of_rfF`): the Lean model has no
   such per-word lemmas for these words.  Each `dec*` goes through the decoder's READ-ONLY WALK
   at the supervisor reference map `AxLeafS3.drefS` (`cur_privilege`, `misa`, `menvcfg` — the
   registers `cfgOfCK` fixes), evaluated in the kernel (`AxLeafS3.walk*`, `ax_epi_ledger_krfl`),
   and the Lean-only `AxLeafS3.evAOfWalk` (a walk that only reads registers the map fixes, none
   a pin, is an `EvA` fact at every state agreeing with the map).  So the six `rfF_dec_*`
   lemmas are not ported (no downstream weak file uses them); statements of `dec*` unchanged.
   Rocq's `amoswap_acq_ast` (WpAmo) ↦ `AxLeafS3.insAmo`; `fence_rw_w` ↦ `fenceRwW` (AxCert4).
4. The Ltacs `vrL` / `bytL` / `slotL` / `text4L` / `dataL` are replaced by LEMMAS (reusable by
   AxSfence2): `AxLeafS3.memOff` + `AxLeafS3.slotOfNv` transfer the page-table slot facts of
   AxSymCtl3 / AxDataX8 (stated at `nvST`) to every `σL W` (the slots lie outside the text
   word); `AxLeafS3.text4Of W w` reduces `textAt4S (σL W) pT (w64 sPc) w` to the word's
   `BytesAt` and `isRVC` facts (decided per word); `AxLeafS3.dataOf` reduces `dataAtS` at the
   data page to the access's `pteCheckOk` / `update_PTE_Bits` facts and the address facts.
5. Q7 (as AxLeafS2 deviation 2): the `*Whole` proofs supply `sfAnnB 32 w = false`
   (decided per word).
6. `cfgOfCK`'s `cfg_ok` is `MachCSL`'s `cfgOk` (WeakFunnel), its misa fact `= misaC`.

**Rocq → Lean name map.** `lk_va` `lkVa`, `rsL` `rsL`, `wb` `AxLeafS3.wb`, `σL` `σL`, `rsL_ctrl_ok`
`rsLCtrlOk`, `rsL_PC` `rsLPC`, `σL_agree` `σLAgree`, `cfg_of_CK` `cfgOfCK`, `dk` `AxLeafS3.dk`
(duplicated name), `W_fence` `AxLeafS3.wFence`, `dec_fence` `decFence`, `text4_fence` `text4Fence`,
`fence_whole` `fenceWhole`, `W_sw` `AxLeafS3.wSw`, `W_sd` `AxLeafS3.wSd`, `ins_sw` `insSw`, `ins_sd`
`insSd`, `dec_sw` `decSw`, `dec_sd` `decSd`, `text4_sw` `text4Sw`, `text4_sd` `text4Sd`, `data_sw`
`dataSw`, `data_sd` `dataSd`, `sw_whole` `swWhole`, `sw_whole_rel` `swWholeRel`, `sd_whole`
`sdWhole`, `W_lw` `AxLeafS3.wLw`, `W_ld` `AxLeafS3.wLd`, `ins_lw` `insLw`, `ins_ld` `insLd`,
`dec_lw` `decLw`, `dec_ld` `decLd`, `text4_lw` `text4Lw`, `text4_ld` `text4Ld`, `data_lw` `dataLw`,
`data_ld` `dataLd`, `lw_whole` `lwWhole`, `ld_whole` `ldWhole`, `W_amo` `AxLeafS3.wAmo`, `dec_amo`
`decAmo`, `text4_amo` `text4Amo`, `data_amo` `dataAmo`, `amo_whole` `amoWhole`, `amo_whole_wbytes`
`amoWholeWbytes`. The six words `W_*` are FILE-QUALIFIED (`AxCert3`'s `w_fence`/`w_sw`/`w_amo`
camelCase to the same Lean names). Notations `imgL` / `CK` written out.
Lean-only (file-qualified): `AxLeafS3.drefS`, `AxLeafS3.rdWalk`, `AxLeafS3.evAOfWalk`,
`AxLeafS3.decOfWalk`, `AxLeafS3.insAmo`, `AxLeafS3.walkFence`/`walkSw`/`walkSd`/`walkLw`/
`walkLd`/`walkAmo`, `AxLeafS3.memOff`, `AxLeafS3.slotOfNv`, `AxLeafS3.text4Of`,
`AxLeafS3.dataOf`.

**Dropped:** `rfF_dec_fence`/`_sw`/`_sd`/`_lw`/`_ld`/`_amo` (deviation 3; unused downstream),
the Ltacs (deviation 4) and the `Print Assumptions` lines (the lint's axiom check covers them).
Rocq 50 definitions/lemmas (+ 2 notations, 5 Ltacs); Lean 44 ported + 15 Lean-only = 59.
-/
import Weak.AxLeafS2
import Weak.AxDataX8
import Weak.WeakFunnel

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The concrete states -/

/-- Rocq `lk_va`: the lock word, 0x80001008. -/
def lkVa : Nat := AxSmodeProbe.sSp + 8

/-- Rocq `rsL`: the probe's registers with s1 = s4 = `lkVa`, a5 = 1. -/
def rsL : RegFile :=
  ((nvSRs.set .x15 (AxEpiProbe.w64 1)).set .x20 (AxEpiProbe.w64 lkVa)).set .x9 (AxEpiProbe.w64 lkVa)

/-- Rocq `wb`: byte `j` of the word `W`. -/
def AxLeafS3.wb (W j : Nat) : BitVec 8 := BitVec.ofNat 8 ((W >>> (8 * j)) &&& 255)

/-- Rocq `σL`: `rsL`, the probe's memory with the word `W` at `sPc` (deviation 2). -/
def σL (W : Nat) : ExecSt :=
  ⟨rsL,
   fun a => if a = AxEpiProbe.w64 sPc then some (AxLeafS3.wb W 0)
     else if a = AxEpiProbe.w64 (sPc + 1) then some (AxLeafS3.wb W 1)
     else if a = AxEpiProbe.w64 (sPc + 2) then some (AxLeafS3.wb W 2)
     else if a = AxEpiProbe.w64 (sPc + 3) then some (AxLeafS3.wb W 3)
     else sMem a,
   (sAt sPc).dev⟩

/-- Rocq `rsL_ctrl_ok`. -/
theorem rsLCtrlOk : ctrlOkSW pT nvSSatp rsL := by
  refine ⟨?_, by unfold pmpW; decide +kernel⟩
  have hne : ∀ r ∈ ctrlRegs, r ≠ Register.x9 ∧ r ≠ Register.x20 ∧ r ≠ Register.x15 := by decide
  refine ctrlOkSAgree pT nvSSatp nvSRs _ ?_ (nvSCtrlOk pT)
  intro r hr
  obtain ⟨h9, h20, h15⟩ := hne r hr
  unfold rsL
  rw [RegFile.set_other _ _ _ _ h9, RegFile.set_other _ _ _ _ h20, RegFile.set_other _ _ _ _ h15]

/-- Rocq `rsL_PC`. -/
theorem rsLPC : rsL .PC = AxEpiProbe.w64 sPc := by decide +kernel

/-- Rocq `σL_agree`. -/
theorem σLAgree (W : Nat) : regsAgree AxRunClose.pinReg (σL W).regs rsL := fun _ _ => rfl

/-- Rocq `cfg_of_CK` (deviation 6). -/
theorem cfgOfCK (t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    t.regs .misa = misaC ∧ cfgOk t := by
  intro ⟨⟨hp, _, hm, he, _⟩, _⟩
  exact ⟨hm, Or.inr ⟨hp, he⟩⟩

/-- Rocq `dk` (duplicated name): the data region is exactly `(a, n)`. -/
def AxLeafS3.dk (a : Int) (n : Nat) : Int → Nat → Prop := fun a' n' => a' = a ∧ n' = n

/-! ## Decode facts through the read-only walk (deviation 3) -/

/-- (Lean-only) the supervisor reference map: the registers `cfgOfCK` fixes. -/
def AxLeafS3.drefS : (r : Register) → Option (RegisterType r)
  | .cur_privilege => some Privilege.Supervisor
  | .misa => some 0x8000000000141105#64
  | .menvcfg => some menvcfgS
  | _ => none

/-- (Lean-only) a register-read-only walk of a tree at a reference map. -/
def AxLeafS3.rdWalk {X : Type} (dref : (r : Register) → Option (RegisterType r)) :
    SailM X → Option X
  | .pure x => some x
  | .impure (.error _) _ => none
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k =>
      match dref r with
      | some v => AxLeafS3.rdWalk dref (k v)
      | none => none
    | _, _ => none

/-- (Lean-only) a walk reading only registers the map fixes (none a pin) is an `EvA` fact at
every state agreeing with the map. -/
theorem AxLeafS3.evAOfWalk (img : Image) (dref : (r : Register) → Option (RegisterType r))
    (hpin : ∀ r v, dref r = some v → ¬ AxRunClose.pinReg r) {X : Type} (m : SailM X) :
    ∀ (t : ExecSt) (x : X), (∀ r v, dref r = some v → t.regs r = v) →
      AxLeafS3.rdWalk dref m = some x →
      EvA img (fun (_ : Sail.Error exception) _ => False) (fun x' t' => x' = x ∧ t' = t) m t := by
  induction m with
  | pure y =>
    intro t x _ h
    simp only [AxLeafS3.rdWalk, Option.some.injEq] at h
    subst h
    exact .evRet _ _ ⟨rfl, rfl⟩
  | impure call k ih =>
    intro t x hd h
    cases call with
    | error e => simp only [AxLeafS3.rdWalk, reduceCtorEq] at h
    | ok o =>
      cases o
      case regRead r =>
        simp only [AxLeafS3.rdWalk] at h
        cases hr : dref r with
        | none => rw [hr] at h; cases h
        | some v =>
          rw [hr] at h
          dsimp only at h
          refine .evRd r k t (fun hp => absurd hp (hpin r v hr)) (fun _ => ?_)
          rw [hd r v hr]
          exact ih v t x hd h
      all_goals simp only [AxLeafS3.rdWalk, reduceCtorEq] at h

/-- (Lean-only) the decode fact of a word whose walk at `drefS` yields `ins`, at every
`ctrlOkSW` state. -/
theorem AxLeafS3.decOfWalk (w : BitVec 32) (ins : instruction)
    (hw : AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode w) = some ins) (σ t : ExecSt) :
    ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = ins ∧ t' = t) (ext_decode w) t := by
  intro Hc
  obtain ⟨Hm, Hcfg⟩ := cfgOfCK t Hc
  rcases Hcfg with ⟨hp, _⟩ | ⟨hp, he⟩
  · rw [Hc.1.1] at hp; cases hp
  refine AxLeafS3.evAOfWalk _ AxLeafS3.drefS ?_ _ t ins ?_ hw
  · intro r v hv
    unfold AxLeafS3.drefS at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;>
      exact AxSymEngine2.notPin _ (by decide) (by decide)
  · intro r v hv
    unfold AxLeafS3.drefS at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
    · exact hp
    · exact Hm
    · exact he

/-! ## Page facts at every `σL W` (deviation 4) -/

/-- (Lean-only) outside the text word, `σL W`'s memory is `nvST`'s. -/
theorem AxLeafS3.memOff (W : Nat) (a : BitVec 64)
    (h : (a == AxEpiProbe.w64 sPc || a == AxEpiProbe.w64 (sPc + 1) ||
      a == AxEpiProbe.w64 (sPc + 2) || a == AxEpiProbe.w64 (sPc + 3)) = false) :
    (σL W).mem a = nvST.mem a := by
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  show (if a = AxEpiProbe.w64 sPc then _ else if a = AxEpiProbe.w64 (sPc + 1) then _
      else if a = AxEpiProbe.w64 (sPc + 2) then _ else if a = AxEpiProbe.w64 (sPc + 3) then _
      else sMem a) =
    (if a = AxEpiProbe.w64 sPc then _ else if a = AxEpiProbe.w64 (sPc + 1) then _
      else (sAt sPc).mem a)
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h0, if_neg h1]
  rfl

/-- (Lean-only) a page-table slot of `nvST` outside the text word is one of `σL W`. -/
theorem AxLeafS3.slotOfNv (W : Nat) (a w : BitVec 64)
    (hoff : ∀ j : Nat, j < 8 →
      (a + BitVec.ofNat 64 j == AxEpiProbe.w64 sPc || a + BitVec.ofNat 64 j == AxEpiProbe.w64 (sPc + 1) ||
        a + BitVec.ofNat 64 j == AxEpiProbe.w64 (sPc + 2) ||
        a + BitVec.ofNat 64 j == AxEpiProbe.w64 (sPc + 3)) = false) :
    WeakWalkEff.ptSlotMem nvST a w → WeakWalkEff.ptSlotMem (σL W) a w := by
  intro ⟨hb, h1, h2⟩
  refine ⟨fun j hj => ?_, h1, h2⟩
  rw [AxLeafS3.memOff W _ (hoff j hj)]
  exact hb j hj

/-- (Lean-only) `textAt4S` at `sPc` in `σL W` reduces to the word's bytes and its RVC bit. -/
theorem AxLeafS3.text4Of (W : Nat) (w : BitVec 32)
    (hb : BytesAt (σL W) (AxEpiProbe.w64 sPc) 4 w)
    (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    textAt4S (σL W) pT (AxEpiProbe.w64 sPc) w := by
  refine ⟨pP2, pP1, pW, AxEpiProbe.w64 sPc, pTMaps,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) pTSlot2,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) pTSlot1,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) pTSlot0, ?_, ?_, ?_, ?_, ?_, ?_, hrvc, ?_, ?_, hb⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact AxSymCtl3.ramOkZ _ _ (by decide +kernel)
  · decide +kernel

/-- (Lean-only) `dataAtS` at the data page (VA = PA) in `σL W`. -/
theorem AxLeafS3.dataOf (W : Nat) (acc : MemoryAccessType mem_payload) (va : BitVec 64) (n : Nat)
    (hv : WeakKpt.svpnOf va = dvpn)
    (Hchk : ∀ mxr dosum : Bool, pteCheckOk acc .Supervisor mxr dosum dW)
    (Hupd : update_PTE_Bits dW acc = none)
    (hcan : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hpa : zero_extend (m := 64) (ppn0 dW +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)
      = va)
    (hram : inRam va n)
    (hal : is_aligned_vaddr (.Virtaddr va) n = true)
    (hpal : is_aligned_paddr (.Physaddr va) n = true) :
    dataAtS (σL W) pT acc va n va := by
  unfold dataAtS
  rw [hv]
  exact ⟨pP2, pP1, dW, dTMaps,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) dTSlot2,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) dTSlot1,
    AxLeafS3.slotOfNv W _ _ (by decide +kernel) dTSlot0, Hchk, Hupd,
    by unfold ptePbmt0; decide +kernel, hcan, hpa, hram, hal, hpal⟩

/-! # 2. `fence rw,w` (0x0310000f) -/

/-- Rocq `W_fence`. -/
def AxLeafS3.wFence : Nat := 0x0310000f

/-- (Lean-only) the decode walk of `fence rw,w`. -/
theorem AxLeafS3.walkFence :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wFence)) = some fenceRwW := by
  ax_epi_ledger_krfl

/-- Rocq `dec_fence` (deviation 3). -/
theorem decFence (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = fenceRwW ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wFence)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkFence σ t

/-- Rocq `text4_fence`. -/
theorem text4Fence :
    textAt4S (σL AxLeafS3.wFence) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wFence) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)

/-- Rocq `fence_whole`. -/
theorem fenceWhole (tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wFence)) (fun _ _ => False) .DKSt (fun _ _ _ => False)
      (fun s _ t' => s = ⟨.CPend, .BInf, true⟩ ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none none t'.regs)
      ⟨.CPend, .BInf, false⟩ (riscvStep tick) (σL AxLeafS3.wFence) := by
  refine spineCertX (imgS (σL AxLeafS3.wFence)) (fun _ _ => False) .DKSt (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wFence) pT) (textAt4S (σL AxLeafS3.wFence) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ fenceRwW (fun _ => none) .CPend false
    (fun s' => s' = ⟨.CPend, .BInf, true⟩)
    rsLCtrlOk rsLPC text4Fence (by decide +kernel) (decFence _) (fun _ _ => trivial)
    (fun _ h => by rw [h]) ?_ tick (σL AxLeafS3.wFence) (σLAgree _)
  intro tpc Hc _ _ _
  refine CertMono _ _ _ _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_
    (certExecuteFence _ _ _ .CPend false tpc Hc.1.1)
  rintro s x t' ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

/-! # 3. `sw zero, 0(s1)` (0x0004a023) and `sd zero, 16(s1)` (0x0004b823) -/

/-- Rocq `W_sw`. -/
def AxLeafS3.wSw : Nat := 0x0004a023
/-- Rocq `W_sd`. -/
def AxLeafS3.wSd : Nat := 0x0004b823
/-- Rocq `ins_sw`. -/
def insSw : instruction := .STORE (0#12, .Regidx 0#5, .Regidx 9#5, 4)
/-- Rocq `ins_sd`. -/
def insSd : instruction := .STORE (16#12, .Regidx 0#5, .Regidx 9#5, 8)

/-- (Lean-only) the decode walk of `sw zero, 0(s1)`. -/
theorem AxLeafS3.walkSw :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wSw)) = some insSw := by
  ax_epi_ledger_krfl
/-- (Lean-only) the decode walk of `sd zero, 16(s1)`. -/
theorem AxLeafS3.walkSd :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wSd)) = some insSd := by
  ax_epi_ledger_krfl

/-- Rocq `dec_sw` (deviation 3). -/
theorem decSw (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = insSw ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wSw)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkSw σ t
/-- Rocq `dec_sd` (deviation 3). -/
theorem decSd (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = insSd ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wSd)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkSd σ t

/-- Rocq `text4_sw`. -/
theorem text4Sw : textAt4S (σL AxLeafS3.wSw) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wSw) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)
/-- Rocq `text4_sd`. -/
theorem text4Sd : textAt4S (σL AxLeafS3.wSd) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wSd) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)

/-- Rocq `data_sw`. -/
theorem dataSw : dataAtS (σL AxLeafS3.wSw) pT (.Store .Data) (AxEpiProbe.w64 lkVa) 4 (AxEpiProbe.w64 lkVa) :=
  AxLeafS3.dataOf _ _ _ _ (by decide +kernel)
    (fun mxr dosum s => by cases mxr <;> cases dosum <;> ax_epi_ledger_krfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
/-- Rocq `data_sd`. -/
theorem dataSd : dataAtS (σL AxLeafS3.wSd) pT (.Store .Data) (AxEpiProbe.w64 (lkVa + 16)) 8
    (AxEpiProbe.w64 (lkVa + 16)) :=
  AxLeafS3.dataOf _ _ _ _ (by decide +kernel)
    (fun mxr dosum s => by cases mxr <;> cases dosum <;> ax_epi_ledger_krfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- Rocq `sw_whole`. -/
theorem swWhole (r tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wSw)) (AxLeafS3.dk (lkVa : Int) 4) .DKSt (fun _ _ _ => False)
      (fun s _ t' => s = ⟨.CSt (stBytes 4 (gprVal rsL 0#5)) (wcls AxDataX.akPlain r), .BInf, false⟩ ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none none t'.regs)
      ⟨.CPend, .BInf, r⟩ (riscvStep tick) (σL AxLeafS3.wSw) :=
  spineCertXT (imgS (σL AxLeafS3.wSw)) (AxLeafS3.dk (lkVa : Int) 4) .DKSt (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wSw) pT) (textAt4S (σL AxLeafS3.wSw) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ insSw (fun _ => none) .CPend r _
    rsLCtrlOk rsLPC text4Sw (by decide +kernel) (decSw _) (fun _ _ => trivial)
    (fun _ h => by rw [h])
    (CertXTStoreS (σL AxLeafS3.wSw) pT nvSSatp nvSSatpMode nvSSatpAsid pTBase (AxLeafS3.dk (lkVa : Int) 4)
      rsL (AxEpiProbe.w64 sPc) 0#12 0#5 9#5 4 (AxEpiProbe.w64 lkVa) (AxEpiProbe.w64 lkVa) r
      (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide) (by decide +kernel) dataSw
      ⟨by decide +kernel, rfl⟩)
    tick (σL AxLeafS3.wSw) (σLAgree _)

/-- Rocq `sw_whole_rel`: after an ARMED fence the `sw` is certified as a RELEASE store. -/
theorem swWholeRel : wcls AxDataX.akPlain true = .WCrel := by decide +kernel

/-- Rocq `sd_whole`. -/
theorem sdWhole (r tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wSd)) (AxLeafS3.dk ((lkVa : Int) + 16) 8) .DKSt (fun _ _ _ => False)
      (fun s _ t' => s = ⟨.CSt (stBytes 8 (gprVal rsL 0#5)) (wcls AxDataX.akPlain r), .BInf, false⟩ ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none none t'.regs)
      ⟨.CPend, .BInf, r⟩ (riscvStep tick) (σL AxLeafS3.wSd) :=
  spineCertXT (imgS (σL AxLeafS3.wSd)) (AxLeafS3.dk ((lkVa : Int) + 16) 8) .DKSt (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wSd) pT) (textAt4S (σL AxLeafS3.wSd) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ insSd (fun _ => none) .CPend r _
    rsLCtrlOk rsLPC text4Sd (by decide +kernel) (decSd _) (fun _ _ => trivial)
    (fun _ h => by rw [h])
    (CertXTStoreS (σL AxLeafS3.wSd) pT nvSSatp nvSSatpMode nvSSatpAsid pTBase
      (AxLeafS3.dk ((lkVa : Int) + 16) 8)
      rsL (AxEpiProbe.w64 sPc) 16#12 0#5 9#5 8 (AxEpiProbe.w64 (lkVa + 16))
      (AxEpiProbe.w64 (lkVa + 16)) r
      (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide) (by decide +kernel) dataSd
      ⟨by decide +kernel, rfl⟩)
    tick (σL AxLeafS3.wSd) (σLAgree _)

/-! # 4. `lw a4, 536(s1)` (0x2184a703) and `ld a5, 0(s4)` (0x000a3783) -/

/-- Rocq `W_lw`. -/
def AxLeafS3.wLw : Nat := 0x2184a703
/-- Rocq `W_ld`. -/
def AxLeafS3.wLd : Nat := 0x000a3783
/-- Rocq `ins_lw`. -/
def insLw : instruction := .LOAD (536#12, .Regidx 9#5, .Regidx 14#5, false, 4)
/-- Rocq `ins_ld`. -/
def insLd : instruction := .LOAD (0#12, .Regidx 20#5, .Regidx 15#5, false, 8)

/-- (Lean-only) the decode walk of `lw a4, 536(s1)`. -/
theorem AxLeafS3.walkLw :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wLw)) = some insLw := by
  ax_epi_ledger_krfl
/-- (Lean-only) the decode walk of `ld a5, 0(s4)`. -/
theorem AxLeafS3.walkLd :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wLd)) = some insLd := by
  ax_epi_ledger_krfl

/-- Rocq `dec_lw` (deviation 3). -/
theorem decLw (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = insLw ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wLw)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkLw σ t
/-- Rocq `dec_ld` (deviation 3). -/
theorem decLd (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = insLd ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wLd)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkLd σ t

/-- Rocq `text4_lw`. -/
theorem text4Lw : textAt4S (σL AxLeafS3.wLw) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wLw) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)
/-- Rocq `text4_ld`. -/
theorem text4Ld : textAt4S (σL AxLeafS3.wLd) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wLd) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)

/-- Rocq `data_lw`. -/
theorem dataLw : dataAtS (σL AxLeafS3.wLw) pT (.Load .Data) (AxEpiProbe.w64 (lkVa + 536)) 4
    (AxEpiProbe.w64 (lkVa + 536)) :=
  AxLeafS3.dataOf _ _ _ _ (by decide +kernel)
    (fun mxr dosum s => by cases mxr <;> cases dosum <;> ax_epi_ledger_krfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
/-- Rocq `data_ld`. -/
theorem dataLd : dataAtS (σL AxLeafS3.wLd) pT (.Load .Data) (AxEpiProbe.w64 lkVa) 8 (AxEpiProbe.w64 lkVa) :=
  AxLeafS3.dataOf _ _ _ _ (by decide +kernel)
    (fun mxr dosum s => by cases mxr <;> cases dosum <;> ax_epi_ledger_krfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- Rocq `lw_whole`. -/
theorem lwWhole (tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wLw)) (AxLeafS3.dk ((lkVa : Int) + 536) 4) .DKLd (fun _ _ _ => False)
      (fun s _ t' => (∃ vs, s = ⟨.CLd vs, .BInf, false⟩ ∧ vs.length = 4) ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none (owLd 14#5 false 4 s)
          t'.regs)
      ⟨.CPend, .BInf, false⟩ (riscvStep tick) (σL AxLeafS3.wLw) :=
  spineCertXT (imgS (σL AxLeafS3.wLw)) (AxLeafS3.dk ((lkVa : Int) + 536) 4) .DKLd (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wLw) pT) (textAt4S (σL AxLeafS3.wLw) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ insLw (owLd 14#5 false 4) .CPend false _
    rsLCtrlOk rsLPC text4Lw (by decide +kernel) (decLw _)
    (fun _ ⟨_, h, _⟩ => by rw [h]; exact (by decide : (14#5 : BitVec 5).toNat ≠ 0))
    (fun _ ⟨_, h, _⟩ => by rw [h])
    (CertXTAnd _ _ .DKLd (ctrlOkS pT nvSSatp) pmpW pmpWDep _ _ _ _ _ _
      (CertXTLoadS (σL AxLeafS3.wLw) pT nvSSatp nvSSatpMode nvSSatpAsid pTBase
        (AxLeafS3.dk ((lkVa : Int) + 536) 4) rsL (AxEpiProbe.w64 sPc) 536#12 9#5 14#5 false 4
        (AxEpiProbe.w64 (lkVa + 536)) (AxEpiProbe.w64 (lkVa + 536)) false
        (by decide) (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide) (by decide +kernel)
        dataLw ⟨by decide +kernel, rfl⟩))
    tick (σL AxLeafS3.wLw) (σLAgree _)

/-- Rocq `ld_whole`. -/
theorem ldWhole (tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wLd)) (AxLeafS3.dk (lkVa : Int) 8) .DKLd (fun _ _ _ => False)
      (fun s _ t' => (∃ vs, s = ⟨.CLd vs, .BInf, false⟩ ∧ vs.length = 8) ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none (owLd 15#5 false 8 s)
          t'.regs)
      ⟨.CPend, .BInf, false⟩ (riscvStep tick) (σL AxLeafS3.wLd) :=
  spineCertXT (imgS (σL AxLeafS3.wLd)) (AxLeafS3.dk (lkVa : Int) 8) .DKLd (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wLd) pT) (textAt4S (σL AxLeafS3.wLd) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ insLd (owLd 15#5 false 8) .CPend false _
    rsLCtrlOk rsLPC text4Ld (by decide +kernel) (decLd _)
    (fun _ ⟨_, h, _⟩ => by rw [h]; exact (by decide : (15#5 : BitVec 5).toNat ≠ 0))
    (fun _ ⟨_, h, _⟩ => by rw [h])
    (CertXTAnd _ _ .DKLd (ctrlOkS pT nvSSatp) pmpW pmpWDep _ _ _ _ _ _
      (CertXTLoadS (σL AxLeafS3.wLd) pT nvSSatp nvSSatpMode nvSSatpAsid pTBase
        (AxLeafS3.dk (lkVa : Int) 8) rsL (AxEpiProbe.w64 sPc) 0#12 20#5 15#5 false 8
        (AxEpiProbe.w64 lkVa) (AxEpiProbe.w64 lkVa) false
        (by decide) (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide) (by decide +kernel)
        dataLd ⟨by decide +kernel, rfl⟩))
    tick (σL AxLeafS3.wLd) (σLAgree _)

/-! # 5. `amoswap.w.aq a5, a5, (s1)` (0x0cf4a7af) -/

/-- Rocq `W_amo`. -/
def AxLeafS3.wAmo : Nat := 0x0cf4a7af
/-- (Lean-only; Rocq `WpAmo.amoswap_acq_ast`) `amoswap.w.aq a5, a5, (s1)`. -/
def AxLeafS3.insAmo : instruction :=
  .AMO (.AMOSWAP, true, false, .Regidx 15#5, .Regidx 9#5, 4, .Regidx 15#5)

/-- (Lean-only) the decode walk of `amoswap.w.aq a5, a5, (s1)`. -/
theorem AxLeafS3.walkAmo :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wAmo)) = some AxLeafS3.insAmo := by
  ax_epi_ledger_krfl

/-- Rocq `dec_amo` (deviation 3). -/
theorem decAmo (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = AxLeafS3.insAmo ∧ t' = t) (ext_decode (BitVec.ofNat 32 AxLeafS3.wAmo)) t :=
  AxLeafS3.decOfWalk _ _ AxLeafS3.walkAmo σ t

/-- Rocq `text4_amo`. -/
theorem text4Amo : textAt4S (σL AxLeafS3.wAmo) pT (AxEpiProbe.w64 sPc) (BitVec.ofNat 32 AxLeafS3.wAmo) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)

/-- Rocq `data_amo`. -/
theorem dataAmo : dataAtS (σL AxLeafS3.wAmo) pT (accAmo true) (AxEpiProbe.w64 lkVa) 4 (AxEpiProbe.w64 lkVa) :=
  AxLeafS3.dataOf _ _ _ _ (by decide +kernel)
    (fun mxr dosum s => by cases mxr <;> cases dosum <;> ax_epi_ledger_krfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- Rocq `amo_whole`. -/
theorem amoWhole (tick : Bool) :
    AxCert.Cert (imgS (σL AxLeafS3.wAmo)) (AxLeafS3.dk (lkVa : Int) 4) .DKRmw (fun _ _ _ => False)
      (fun s _ t' => (∃ vs, s = ⟨.CRmw true false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rsL 15#5)))
            (wcls akXc false), .BInf, false⟩ ∧ vs.length = 4) ∧
        GoodC (ctrlOkSW pT nvSSatp) false rsL (AxEpiProbe.w64 sPc) none (owAmo 15#5 s) t'.regs)
      ⟨.CPend, .BInf, false⟩ (riscvStep tick) (σL AxLeafS3.wAmo) :=
  spineCertXT (imgS (σL AxLeafS3.wAmo)) (AxLeafS3.dk (lkVa : Int) 4) .DKRmw (ctrlOkSW pT nvSSatp)
    (textAtS (σL AxLeafS3.wAmo) pT) (textAt4S (σL AxLeafS3.wAmo) pT)
    (SpineOkTSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    (SpineFetch4TSW _ pT nvSSatp nvSSatpMode nvSSatpAsid pTBase)
    rsL (AxEpiProbe.w64 sPc) _ AxLeafS3.insAmo (owAmo 15#5) .CPend false _
    rsLCtrlOk rsLPC text4Amo (by decide +kernel) (decAmo _)
    (fun _ ⟨_, h, _⟩ => by rw [h]; exact (by decide : (15#5 : BitVec 5).toNat ≠ 0))
    (fun _ ⟨_, h, _⟩ => by rw [h])
    (CertXTAmoswapS (σL AxLeafS3.wAmo) pT nvSSatp nvSSatpMode nvSSatpAsid pTBase
      (AxLeafS3.dk (lkVa : Int) 4) rsL (AxEpiProbe.w64 sPc) true 15#5 9#5 15#5
      (AxEpiProbe.w64 lkVa) (AxEpiProbe.w64 lkVa) false
      (by decide) (by decide +kernel) dataAmo ⟨by decide +kernel, rfl⟩)
    tick (σL AxLeafS3.wAmo) (σLAgree _)

/-- Rocq `amo_whole_wbytes`: the written word is a5's low word (= 1): the bytes `[1, 0, 0, 0]`. -/
theorem amoWholeWbytes : AxDataX.wrb 4 (amoStv 4 (gprVal rsL 15#5)) = [1#8, 0#8, 0#8, 0#8] := by
  decide +kernel

end Weak
