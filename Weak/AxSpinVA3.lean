/-
Weak: **the spinlock plan, PHASE 5 item (4), part 3** — the SYMBOLIC chain kit and the Sv39
translation at an ARBITRARY VA, at `FEC`.

Rocq: `iris/AxSpinVA3.v` @ xxvzwolszwmp.

## What this file proves

* §1 THE KIT for `AxSpinVA`'s `FEC`: mono / bind / try_catch / liftR / catch_early_return /
  `untilFuelM 1` (one round) and the position-exact transfer of a register-only (`rfF`) `execA`
  fact (`FECExecARfF`: no label, the chain is untouched) — ports of `AxWalk`'s `CertWP*`.
* §2 THE READ NODES: `FReadRamGo` (a plain / walker RAM read whose bytes are in the image
  CONTINUES the chain with the image word), `FReadRamEnd` (any such read ENDS it), their
  `checked_mem_read` wrappers and `FReadPte` (the 8-byte walker read; ports of `AxWalk3`'s
  `PReadRamW` / `PCheckedMemReadW` / `PReadPte`).  `slotImg`: a `WeakWalkEff.ptSlotMem` slot of the
  image state is an image-fed read returning the slot word.
* §3 THE WALK at a symbolic `vpn`, image-fed: `FPtWalk` — the chain gains exactly the three slot
  reads `[wkey (waddr2 vpn root), wkey (waddr1 vpn p2), wkey (waddr0 vpn p1)]` (port of
  `AxWalk3.PPtWalk`); `FTranslateTLBMiss` (A/D preset, TLB filled); `FTranslateTLBHit`
  (register-only: NO label); `FTranslateAddrFront` (`translateAddr` → `translate`);
  `FTranslateAddrImg` (the `execATranslateAddrImg` case split: hit ⇒ chain unchanged, miss /
  foreign slot ⇒ the three slot reads; post state `t` or the TLB fill).
  Every lemma is ∀ VA (canonical, mapped by the image tree `T`); the translation FAULT arms are
  not here (as Rocq).

## Deviations from Rocq

1. SPELLING (as `AxWalk3` / `AxSpineOk4` deviation 1): `mstate` ↦ `ExecSt`, `sregs`/`mem`/`mdev`
   ↦ `regs`/`mem`/`dev`, `MState r m d` ↦ `⟨r, m, d⟩`, `tm` is `AxWalk3`'s `tm`, `uint pa` ↦
   `paZ pa`, `Z.to_nat w` ↦ `w : Nat`, `register_lookup r t.(sregs)` ↦ `t.regs .r`,
   `Interface.Ret` ↦ `pure`, `Defs.bind0 m n` ↦ `m >>= fun _ => n`, `Defs.read_reg` ↦ `readReg`,
   `img_bytes` ↦ `imgBytes`, `img_of` ↦ `imgOf`, `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`,
   `ptree_maps` / `pt_addr2/1/0` ↦ `AxPtProt.ptreeMaps` / `AxPtProt.ptAddr2/1/0`, `pt_base T` ↦
   `T.base`, `svpn_of` ↦ `WeakKpt.svpnOf`, `vec_access_dec v i` ↦ `v[i]!`, `vec_update_dec` ↦
   `vectorUpdate`, `tlb_hash (__id 39)` ↦ `tlb_hash 39`, `mword_of_int 0 : mword 16` ↦ `0#16`,
   `autocast (PPN_of_PTE q)` ↦ `ppn0 q`, `u_walk_entry` ↦ `uWalkEntry`, `tlb_fill` ↦
   `AxWalk3.tlbFill`, `MISA_C` / `MENVCFG_S` ↦ `misaC` / `menvcfgS`, `eq_vec x 'b"0" = true` ↦
   `(x == 0#1) = true`; the `translateAddr` front premises take `AxSpineOk4`'s deviation-7 shapes.
   The PTE hypotheses `H2i`/`H2nl`/`H1i`/`H1nl`/`H0i`/`H0nl`/`Hchk0`/`H0N` are the `ExecSC9`
   predicates (`pteValid` / `ptePtr` / `pteLeaf` / `pteCheckOk`, as `AxSpineOk4` deviation 1);
   each walk theorem `include`s exactly the ones its Rocq proof uses.
2. THE KIT on lean-sail (as `AxWalk` deviation 2): `FECTryCatch` is about
   `PreSail.tryCatchAll`; `FECLiftRAny` / `FECLiftR` are stated on
   `ExceptT.run (liftM m : SailME R X)` (`.ok x ↦ Q`, `.error _` excluded; the failure nodes mapped
   by `QE ⊆ QE'`); `FECCatchEarlyReturn` takes the certificate of `ExceptT.run m` and concludes on
   `SailME.run m`; `FECUntilMT1` is about `untilFuelM 1` in the early-return monad (Rocq
   `untilMT` at measure 1); `FAssertTrue` is about lean-sail's `assert` (continuation on `()`).
   `FECReadReg` takes `¬ AxRunClose.pinReg r` (Rocq `¬ seip_reg r`).
3. READ KINDS (as `AxWalk3` deviation 2): the Lean model reads a PTE with `Read_ttw`, so
   `FReadRamGo` / `FReadRamEnd` take `rk = .Read_plain ∨ rk = .Read_ttw` (Rocq `Read_plain`), and
   the `checked_mem_read` wrappers take `acc ≠ .InstructionFetch ()` (a fetch is no chain key,
   `AxSpinVA` deviation 1); `0 < w` ↦ `vmemWidth w`.  The read node continues at
   `.Ok (wordOfBytes w vs, none)`; `rrv w vs` is `AxDataX.rrv` (= `wordOfBytes`).
4. THE WALK is Lean's self-recursive `pt_walk` (no `_rec_pt_walk`, no `Acc` argument; as
   `AxWalk3` deviation 8): `FRecWalkLeaf` / `FRecWalkL1` are about
   `pt_walk … (uNextBase p1) 0 g ()` / `(uNextBase p2) 1 g ()`; `ptwOut` is `AxWalk3`'s.  Rocq's
   `nl_true` / `and_boolM` steps are the `if` on the lifted test (as `AxWalk3`).
5. `FTranslateAddrImg`: Rocq's `pmp_ok t.(sregs)` / `pma_allows_all (pma_regions)` ↦
   `AxSpineOk6.pmpOk t.regs` / `t.regs .pma_regions = bootPMA` (the premises of
   `pteRdOkOfRegs`, `AxWalk4` deviation 2).  `update_PTE_Bits` premises are stated at the leaf
   word (as `AxSpineOk4`).
6. TACTICS: Rocq `fc_ctor` (inlined per case), `f_step` / `f_go` / `rffV` / `f_use` ↦ the
   Lean-only lemmas `AxSpinVA3.f*` and the tactic `ax_spin_va3_go`; `rfF` premises are passed
   explicitly.

**Rocq → Lean name map.**  `FEC_mono` `FECMono`, `FEC_bind` `FECBind`, `FEC_bind0` `FECBind0`,
`FEC_ret` `FECRet`, `FEC_read_reg` `FECReadReg`, `FEC_try_catch` `FECTryCatch`, `FEC_liftR_any`
`FECLiftRAny`, `FEC_liftR` `FECLiftR`, `FEC_catch_early_return` `FECCatchEarlyReturn`,
`FEC_execA_rfF` `FECExecARfF`, `FEC_execA_rfF_post` `FECExecARfFPost`, `FEC_execA_same`
`FECExecASame`, `FEC_untilMT_1` `FECUntilMT1`, `F_assert_true` `FAssertTrue`, `rrv8` `rrv8`,
`mapM_some_map` `mapMSomeMap`, `slot_img` `slotImg`, `F_read_ram_go` `FReadRamGo`,
`F_read_ram_end` `FReadRamEnd`, `F_checked_mem_read_go` `FCheckedMemReadGo`,
`F_checked_mem_read_end` `FCheckedMemReadEnd`, `F_read_pte` `FReadPte`, `wkey` `wkey`, `islot`
`islot`, `F_rec_walk_leaf` `FRecWalkLeaf`, `F_rec_walk_l1` `FRecWalkL1`, `F_pt_walk` `FPtWalk`,
`F_translate_TLB_miss` `FTranslateTLBMiss`, `F_translate_TLB_hit` `FTranslateTLBHit`,
`F_translateAddr_front` `FTranslateAddrFront`, `tlb_hitb` `tlbHitb`, `walk_keys` `walkKeys`,
`F_translateAddr_img` `FTranslateAddrImg`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpinVA3.fFact`, `fFactRead`, `fFactPure`, `fFactAssoc`,
`fFactUse`, `fRBind`, `fRLift`, `fRRead`, `fRPureBind`, `fRAssoc`, `fRPure`, `fRUse`,
`fcMrdEndAt`; tactic
`ax_spin_va3_go`.

**Dropped:** none (Rocq 4 definitions + 29 lemmas; Lean the same, + 13 Lean-only helpers).  **Not ported:** the Ltacs
`nseipV` / `fc_ctor` / `f_step` / `f_go` / `rffV` / `f_use` (deviation 6) and the
`Print Assumptions` lines.
-/
import Weak.AxSpinVA
import Weak.AxWalk4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The kit -/

section kit
variable (img : Image)

local notation "FC" => FEC img

theorem FECMono {X : Type} (QE QE' : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q Q' : List ekey → X → ExecSt → Prop) (Ks : List ekey) (m : SailM X) (t : ExecSt) :
    (∀ Ks' e t', QE Ks' e t' → QE' Ks' e t') → (∀ Ks' x t', Q Ks' x t' → Q' Ks' x t') →
    FC QE Q Ks m t → FC QE' Q' Ks m t := by
  intro HE HQ h
  induction h with
  | fcRet Ks x t h => exact .fcRet Ks x t (HQ Ks x t h)
  | fcRd Ks r k t _ _ ihs ihn => exact .fcRd Ks r k t ihs ihn
  | fcWr Ks r v k t hr _ ih => exact .fcWr Ks r v k t hr ih
  | fcMrdEnd n va req k t h1 h2 => exact .fcMrdEnd n va req k t h1 h2
  | fcMrdGo e Ks n va req k t vs h1 h2 h3 h4 h5 h6 _ ih =>
    exact .fcMrdGo e Ks n va req k t vs h1 h2 h3 h4 h5 h6 ih
  | fcIf Ks n va req k t vs h1 h2 h3 _ ih => exact .fcIf Ks n va req k t vs h1 h2 h3 ih
  | fcNf n va req k t h1 h2 h3 => exact .fcNf n va req k t h1 h2 h3
  | fcMwr n va req k t h1 => exact .fcMwr n va req k t h1
  | fcBar b k t x h => exact .fcBar b k t x h
  | fcIa Ks n w k t hs _ ih => exact .fcIa Ks n w k t hs ih
  | fcSf n w k t h => exact .fcSf n w k t h
  | fcBa Ks n a k t _ ih => exact .fcBa Ks n a k t ih
  | fcCo Ks c k t _ ih => exact .fcCo Ks c k t ih
  | fcTl Ks c k t _ ih => exact .fcTl Ks c k t ih
  | fcTe Ks f k t _ ih => exact .fcTe Ks f k t ih
  | fcRx Ks a k t _ ih => exact .fcRx Ks a k t ih
  | fcTs Ks a k t _ ih => exact .fcTs Ks a k t ih
  | fcTx Ks a k t _ ih => exact .fcTx Ks a k t ih
  | fcCc Ks k t _ ih => exact .fcCc Ks k t ih
  | fcMsg Ks a k t _ ih => exact .fcMsg Ks a k t ih
  | fcGcc Ks k t _ ih => exact .fcGcc Ks k t ih
  | fcExt Ks e k t h => exact .fcExt Ks e k t (HE Ks e t h)

theorem FECBind {X Y : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (Ks : List ekey)
    (t : ExecSt) :
    FC QE (fun Ks' x t' => FC QE Q Ks' (f x) t') Ks m t → FC QE Q Ks (m >>= f) t := by
  intro h
  induction h with
  | fcRet Ks x t h => exact h
  | fcRd Ks r k t _ _ ihs ihn => exact .fcRd Ks r _ t ihs ihn
  | fcWr Ks r v k t hr _ ih => exact .fcWr Ks r v _ t hr ih
  | fcMrdEnd n va req k t h1 h2 => exact .fcMrdEnd n va req _ t h1 h2
  | fcMrdGo e Ks n va req k t vs h1 h2 h3 h4 h5 h6 _ ih =>
    exact .fcMrdGo e Ks n va req _ t vs h1 h2 h3 h4 h5 h6 ih
  | fcIf Ks n va req k t vs h1 h2 h3 _ ih => exact .fcIf Ks n va req _ t vs h1 h2 h3 ih
  | fcNf n va req k t h1 h2 h3 => exact .fcNf n va req _ t h1 h2 h3
  | fcMwr n va req k t h1 => exact .fcMwr n va req _ t h1
  | fcBar b k t x h => exact .fcBar b _ t x h
  | fcIa Ks n w k t hs _ ih => exact .fcIa Ks n w _ t hs ih
  | fcSf n w k t h => exact .fcSf n w _ t h
  | fcBa Ks n a k t _ ih => exact .fcBa Ks n a _ t ih
  | fcCo Ks c k t _ ih => exact .fcCo Ks c _ t ih
  | fcTl Ks c k t _ ih => exact .fcTl Ks c _ t ih
  | fcTe Ks f k t _ ih => exact .fcTe Ks f _ t ih
  | fcRx Ks a k t _ ih => exact .fcRx Ks a _ t ih
  | fcTs Ks a k t _ ih => exact .fcTs Ks a _ t ih
  | fcTx Ks a k t _ ih => exact .fcTx Ks a _ t ih
  | fcCc Ks k t _ ih => exact .fcCc Ks _ t ih
  | fcMsg Ks a k t _ ih => exact .fcMsg Ks a _ t ih
  | fcGcc Ks k t _ ih => exact .fcGcc Ks _ t ih
  | fcExt Ks e k t h => exact .fcExt Ks e _ t h

theorem FECBind0 {Y : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y) (Ks : List ekey)
    (t : ExecSt) :
    FC QE (fun Ks' _ t' => FC QE Q Ks' n t') Ks m t → FC QE Q Ks (m >>= fun _ => n) t :=
  FECBind img QE Q m (fun _ => n) Ks t

theorem FECRet {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (Ks : List ekey) (x : X) (t : ExecSt) :
    Q Ks x t → FC QE Q Ks (pure x : SailM X) t :=
  fun h => .fcRet Ks x t h

theorem FECReadReg (QE : List ekey → Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : List ekey → RegisterType r → ExecSt → Prop) (Ks : List ekey) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q Ks (t.regs r) t → FC QE Q Ks (readReg r : SailM _) t :=
  fun hr hq => .fcRd Ks r _ t (fun h => absurd h hr) (fun _ => .fcRet _ _ t hq)

theorem FECTryCatch {X : Type} (QE1 QE2 : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X)
    (Ks : List ekey) (t : ExecSt) :
    (∀ Ks' e t', QE1 Ks' e t' → FC QE2 Q Ks' (h e) t') →
    FC QE1 Q Ks m t → FC QE2 Q Ks (PreSail.tryCatchAll m h) t := by
  intro Hh H
  induction H with
  | fcRet Ks x t h => exact .fcRet Ks x t h
  | fcRd Ks r k t _ _ ihs ihn => exact .fcRd Ks r _ t ihs ihn
  | fcWr Ks r v k t hr _ ih => exact .fcWr Ks r v _ t hr ih
  | fcMrdEnd n va req k t h1 h2 => exact .fcMrdEnd n va req _ t h1 h2
  | fcMrdGo e Ks n va req k t vs h1 h2 h3 h4 h5 h6 _ ih =>
    exact .fcMrdGo e Ks n va req _ t vs h1 h2 h3 h4 h5 h6 ih
  | fcIf Ks n va req k t vs h1 h2 h3 _ ih => exact .fcIf Ks n va req _ t vs h1 h2 h3 ih
  | fcNf n va req k t h1 h2 h3 => exact .fcNf n va req _ t h1 h2 h3
  | fcMwr n va req k t h1 => exact .fcMwr n va req _ t h1
  | fcBar b k t x h => exact .fcBar b _ t x h
  | fcIa Ks n w k t hs _ ih => exact .fcIa Ks n w _ t hs ih
  | fcSf n w k t h => exact .fcSf n w _ t h
  | fcBa Ks n a k t _ ih => exact .fcBa Ks n a _ t ih
  | fcCo Ks c k t _ ih => exact .fcCo Ks c _ t ih
  | fcTl Ks c k t _ ih => exact .fcTl Ks c _ t ih
  | fcTe Ks f k t _ ih => exact .fcTe Ks f _ t ih
  | fcRx Ks a k t _ ih => exact .fcRx Ks a _ t ih
  | fcTs Ks a k t _ ih => exact .fcTs Ks a _ t ih
  | fcTx Ks a k t _ ih => exact .fcTx Ks a _ t ih
  | fcCc Ks k t _ ih => exact .fcCc Ks _ t ih
  | fcMsg Ks a k t _ ih => exact .fcMsg Ks a _ t ih
  | fcGcc Ks k t _ ih => exact .fcGcc Ks _ t ih
  | fcExt Ks e k t he => exact Hh Ks e t he

theorem FECLiftRAny {R X : Type} (QE QE' : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailM X) (Ks : List ekey) (t : ExecSt) :
    (∀ Ks' e t', QE Ks' e t' → QE' Ks' e t') →
    FC QE Q Ks m t →
    FC QE' (fun Ks' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q Ks' x t'
        | .error _ => False)
      Ks (ExceptT.run (liftM m : SailME R X)) t := by
  intro HE H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply FECBind
  exact FECMono img QE QE' Q _ Ks m t HE (fun Ks' x t' h => .fcRet _ _ t' h) H

theorem FECLiftR {R X : Type} (QE' : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailM X) (Ks : List ekey) (t : ExecSt) :
    FC (fun _ _ _ => False) Q Ks m t →
    FC QE' (fun Ks' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q Ks' x t'
        | .error _ => False)
      Ks (ExceptT.run (liftM m : SailME R X)) t :=
  FECLiftRAny img _ QE' Q m Ks t (fun _ _ _ h => h.elim)

theorem FECCatchEarlyReturn {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailME X X) (Ks : List ekey) (t : ExecSt) :
    FC QE (fun Ks' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q Ks' x t'
        | .error (.inr x) => Q Ks' x t'
        | .error (.inl e) => QE Ks' e t')
      Ks (ExceptT.run m) t →
    FC QE Q Ks (SailME.run m) t := by
  intro H
  show FC QE Q Ks (ExceptT.run m >>= _) t
  apply FECBind
  refine FECMono img QE QE _ _ Ks _ t (fun _ _ _ h => h) ?_ H
  intro Ks' r t' hr
  rcases r with (e | x) | x
  · exact .fcExt Ks' e _ t' hr
  · exact .fcRet Ks' x t' hr
  · exact .fcRet Ks' x t' hr

/-- THE TRANSFER: a register-only `execA` run leaves the chain alone. -/
theorem FECExecARfF {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (m : SailM X) :
    rfF m → ∀ (s0 : ExecSt) (x : X) (s1 : ExecSt), execA m s0 = some (x, s1) →
    ∀ (t : ExecSt), t.regs = s0.regs → ∀ (Ks : List ekey),
    FC QE (fun Ks' x' t' => Ks' = Ks ∧ x' = x ∧ t'.regs = s1.regs ∧ t'.mem = t.mem ∧
      t'.dev = t.dev) Ks m t := by
  induction m with
  | pure y =>
    intro _ s0 x s1 h t ht Ks
    simp only [execA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .fcRet Ks y t ⟨rfl, rfl, ht, rfl, rfl⟩
  | impure call kk ih =>
    intro hrf s0 x s1 h t ht Ks
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .fcRd Ks r kk t (fun hp => absurd hp hr) (fun _ => ?_)
          rw [ht]
          exact ih _ (hrf.2 _) s0 x s1 h t ht Ks
      case regWrite r v =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .fcWr Ks r v kk t hr ?_
          have HI := ih PUnit.unit hrf.2 (s0.setReg r v) x s1 h (t.setReg r v)
            (by simp [ExecSt.setReg, ht]) Ks
          exact FECMono img _ _ _ _ _ _ _ (fun _ _ _ h => h)
            (fun _ _ _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩) HI
      case memRead => exact hrf.elim
      case memWrite => exact hrf.elim
      case barrier => exact hrf.elim
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · exact .fcIa Ks n w kk t hrf.1 (ih _ hrf.2 s0 x s1 h t ht Ks)
      case choose => cases h
      case readRam => cases h
      case writeRam => cases h
      case branchAnnounce => exact .fcBa Ks _ _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case cacheOp => exact .fcCo Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case tlbi => exact .fcTl Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case takeException => exact .fcTe Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case returnException => exact .fcRx Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case translationStart => exact .fcTs Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case translationEnd => exact .fcTx Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case cycleCount => exact .fcCc Ks kk t (ih _ hrf s0 x s1 h t ht Ks)
      case message => exact .fcMsg Ks _ kk t (ih _ hrf s0 x s1 h t ht Ks)
      case getCycleCount => exact .fcGcc Ks kk t (ih _ hrf s0 x s1 h t ht Ks)

theorem FECExecARfFPost {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailM X) (s0 : ExecSt) (x : X) (s1 : ExecSt)
    (t : ExecSt) (Ks : List ekey) :
    rfF m → execA m s0 = some (x, s1) → t.regs = s0.regs →
    Q Ks x ⟨s1.regs, t.mem, t.dev⟩ → FC QE Q Ks m t := by
  intro Hrf He Ht HQ
  refine FECMono img QE QE _ Q Ks m t (fun _ _ _ h => h) ?_
    (FECExecARfF img QE m Hrf s0 x s1 He t Ht Ks)
  rintro _ _ ⟨r', m', d'⟩ ⟨rfl, rfl, hr, hm, hd⟩
  simp only [] at hr hm hd
  subst hr hm hd
  exact HQ

/-- The `execA` fact at the image-memory twin `tm μ t` of `t`. -/
theorem FECExecASame {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (m : SailM X) (μ : ExecSt) (x : X) (Ks : List ekey)
    (t : ExecSt) :
    rfF m → execA m (tm μ t) = some (x, tm μ t) → Q Ks x t → FC QE Q Ks m t := by
  intro Hrf He HQ
  exact FECExecARfFPost img QE Q m (tm μ t) x (tm μ t) t Ks Hrf He rfl HQ

/-- Rocq `FEC_untilMT_1` (deviation 2): lean-sail `untilFuelM 1`, in the early-return monad. -/
theorem FECUntilMT1 {R Vars : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Except (Sail.Error exception ⊕ R) Vars → ExecSt → Prop) (vars : Vars)
    (cond : Vars → SailME R Bool) (body : Vars → SailME R Vars) (Ks : List ekey) (t : ExecSt) :
    FC QE (fun Ks' r t' => match r with
      | .ok v => FC QE (fun Ks'' r' t'' => match r' with
          | .ok b => b = true ∧ Q Ks'' (.ok v) t''
          | .error e => Q Ks'' (.error e) t'') Ks' (ExceptT.run (cond v)) t'
      | .error e => Q Ks' (.error e) t') Ks (ExceptT.run (body vars)) t →
    FC QE Q Ks (ExceptT.run (untilFuelM 1 cond vars body)) t := by
  intro Hb
  unfold untilFuelM untilFuelM.go
  rw [ExceptT.run_bind]
  apply FECBind
  refine FECMono img _ _ _ _ Ks _ t (fun _ _ _ h => h) ?_ Hb
  intro Ks' r t' hr
  rcases r with e | v
  · exact .fcRet _ _ _ hr
  · show FC QE Q Ks' (ExceptT.run (cond v >>= fun b => if b then pure v else _)) t'
    rw [ExceptT.run_bind]
    apply FECBind
    refine FECMono img _ _ _ _ Ks' _ t' (fun _ _ _ h => h) ?_ hr
    intro Ks'' r' t'' hr'
    rcases r' with e | b
    · exact .fcRet _ _ _ hr'
    · obtain ⟨rfl, hq⟩ := hr'
      exact .fcRet _ _ _ hq

/-- Rocq `F_assert_true` (deviation 2: lean-sail's `assert` returns `()`). -/
theorem FAssertTrue {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (b0 : Bool) (Hb0 : b0 = true) (msg : String)
    (f : Unit → SailM X) (Ks : List ekey) (t : ExecSt) :
    FC QE Q Ks (f ()) t → FC QE Q Ks (assert b0 msg >>= f) t := by
  intro H
  subst Hb0
  exact H

end kit

/-! # 1b. (Lean-only) the stepping kit at `FEC` (Rocq's `f_step` / `f_go` / `f_use`) -/

section kit2
variable {img : Image}

local notation "FC" => FEC img

theorem AxSpinVA3.fFact {X Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {P : List ekey → X → ExecSt → Prop} {Q : List ekey → Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {Ks : List ekey} {t : ExecSt}
    (Hm : FC (fun _ _ _ => False) P Ks m t)
    (Hf : ∀ Ks' x t', P Ks' x t' → FC QE Q Ks' (f x) t') :
    FC QE Q Ks (m >>= f) t :=
  FECBind img QE Q m f Ks t
    (FECMono img _ _ _ _ Ks m t (fun _ _ _ h => h.elim) Hf Hm)

theorem AxSpinVA3.fFactRead {Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Y → ExecSt → Prop} {r : Register} {f : RegisterType r → SailM Y}
    {Ks : List ekey} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : FC QE Q Ks (f (t.regs r)) t) :
    FC QE Q Ks (readReg r >>= f) t :=
  .fcRd Ks r _ t (fun h => absurd h hr) (fun _ => H)

theorem AxSpinVA3.fFactPure {X Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Y → ExecSt → Prop} {x : X} {f : X → SailM Y} {Ks : List ekey} {t : ExecSt}
    (H : FC QE Q Ks (f x) t) : FC QE Q Ks (pure x >>= f) t := H

theorem AxSpinVA3.fFactAssoc {X Y Z : Type}
    {QE : List ekey → Sail.Error exception → ExecSt → Prop} {Q : List ekey → Z → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {g : Y → SailM Z} {Ks : List ekey} {t : ExecSt}
    (H : FC QE Q Ks (m >>= fun x => f x >>= g) t) : FC QE Q Ks ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

/-- Rocq `f_use` (base monad): a register-only `execA` fact at the image state `tm μ t`. -/
theorem AxSpinVA3.fFactUse {X Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Y → ExecSt → Prop} {μ : ExecSt} {m : SailM X} {f : X → SailM Y}
    {Ks : List ekey} {t : ExecSt} {a : X}
    (hrf : rfF m) (He : execA m (tm μ t) = some (a, tm μ t)) (H : FC QE Q Ks (f a) t) :
    FC QE Q Ks (m >>= f) t :=
  AxSpinVA3.fFact (P := fun Ks' x t' => Ks' = Ks ∧ x = a ∧ t' = t)
    (FECExecASame img _ _ m μ a Ks t hrf He ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- The early-return monad's bind, through `ExceptT.run`. -/
theorem AxSpinVA3.fRBind {R X Y : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop)
    (m : SailME R Y) (f : Y → SailME R X) (Ks : List ekey) (t : ExecSt) :
    FC QE (fun Ks' r t' => match r with
      | .ok a => FC QE Q Ks' (ExceptT.run (f a)) t'
      | .error e => Q Ks' (.error e) t') Ks (ExceptT.run m) t →
    FC QE Q Ks (ExceptT.run (m >>= f)) t := by
  intro H
  rw [ExceptT.run_bind]
  apply FECBind
  refine FECMono img _ _ _ _ Ks _ t (fun _ _ _ h => h) ?_ H
  intro Ks' r t' h
  cases r with
  | ok a => exact h
  | error e => exact .fcRet _ _ _ h

theorem AxSpinVA3.fRLift {R X Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {P : List ekey → X → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {Ks : List ekey} {t : ExecSt}
    (Hm : FC (fun _ _ _ => False) P Ks m t)
    (Hf : ∀ Ks' x t', P Ks' x t' → FC QE Q Ks' (ExceptT.run (f x)) t') :
    FC QE Q Ks (ExceptT.run (liftM m >>= f)) t := by
  apply AxSpinVA3.fRBind
  refine FECMono img _ _ _ _ Ks _ t (fun _ _ _ h => h) ?_ (FECLiftR img QE P m Ks t Hm)
  intro Ks' r t' h
  cases r with
  | ok a => exact Hf Ks' a t' h
  | error e => exact h.elim

theorem AxSpinVA3.fRRead {R X : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {Ks : List ekey} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : FC QE Q Ks (ExceptT.run (f (t.regs r))) t) :
    FC QE Q Ks (ExceptT.run (liftM (readReg r) >>= f)) t :=
  AxSpinVA3.fRLift (P := fun Ks' x t' => Ks' = Ks ∧ x = t.regs r ∧ t' = t)
    (FECReadReg img _ r _ Ks t hr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxSpinVA3.fRPureBind {R X Y : Type}
    {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {x : Y} {f : Y → SailME R X} {Ks : List ekey} {t : ExecSt}
    (H : FC QE Q Ks (ExceptT.run (f x)) t) : FC QE Q Ks (ExceptT.run (pure x >>= f)) t := H

theorem AxSpinVA3.fRAssoc {R X Y Z : Type}
    {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop}
    {m : SailME R X} {f : X → SailME R Y} {g : Y → SailME R Z} {Ks : List ekey} {t : ExecSt}
    (H : FC QE Q Ks (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    FC QE Q Ks (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

theorem AxSpinVA3.fRPure {R X : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {x : X} {Ks : List ekey} {t : ExecSt} (H : Q Ks (.ok x) t) :
    FC QE Q Ks (ExceptT.run (pure x : SailME R X)) t :=
  .fcRet _ _ _ H

/-- Rocq `f_use` (early-return monad). -/
theorem AxSpinVA3.fRUse {R X Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {μ : ExecSt} {m : SailM X} {f : X → SailME R Y} {Ks : List ekey} {t : ExecSt} {a : X}
    (hrf : rfF m) (He : execA m (tm μ t) = some (a, tm μ t))
    (H : FC QE Q Ks (ExceptT.run (f a)) t) : FC QE Q Ks (ExceptT.run (liftM m >>= f)) t :=
  AxSpinVA3.fRLift (P := fun Ks' x t' => Ks' = Ks ∧ x = a ∧ t' = t)
    (FECExecASame img _ _ m μ a Ks t hrf He ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

end kit2

/-- (Lean-only) Rocq `f_go`: run the register reads, `pure`s and re-associate binds, in both
monads. -/
macro "ax_spin_va3_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxSpinVA3.fRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSpinVA3.fRPureBind ?_
  | with_reducible refine AxSpinVA3.fRAssoc ?_
  | with_reducible refine AxSpinVA3.fFactAssoc ?_
  | ((with_reducible refine AxSpinVA3.fFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSpinVA3.fFactPure ?_))

/-! # 2. The read nodes -/

/-- Rocq `rrv8`. -/
theorem rrv8 (vs : List (BitVec 8)) (p : BitVec 64) : wordOfBytes 8 vs = p → rrv 8 vs = p :=
  id

/-- Rocq `mapM_some_map`. -/
theorem mapMSomeMap {α β : Type} (f : α → Option β) (g : α → β) (l : List α) :
    (∀ x, x ∈ l → f x = some (g x)) → l.mapM f = some (l.map g) :=
  AxSpineOk.mapMMap f g l

/-- A page-table slot of the image state is an image-fed 8-byte read of the slot word. -/
theorem slotImg (σ : ExecSt) (a p : BitVec 64) :
    WeakWalkEff.ptSlotMem σ a p → ∃ vs, imgBytes (imgOf σ) (paZ a) 8 = some vs ∧ rrv 8 vs = p := by
  rintro ⟨hb, hram, -⟩
  have hr : bmRead σ.mem a 8 = some p := bmRead_of_bytes _ _ _ _ hb
  have hwf : paZ a + 8 ≤ 2 ^ 64 := by
    have := hram.2
    unfold ramEnd at this
    unfold paZ
    omega
  exact readBytesImg σ a 8 p hwf hr

section reads
variable (img : Image)

local notation "FC" => FEC img

/-- Rocq `F_read_ram_go` (deviation 3). -/
theorem FReadRamGo (rk : read_kind) (hrk : rk = .Read_plain ∨ rk = .Read_ttw) (w : Nat)
    (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (Ks : List ekey)
    (vs : List (BitVec 8)) (t : ExecSt) :
    Ks ≠ [] → devAddr pa = false → imgBytes img (paZ pa) w = some vs →
    Q Ks (rrv w vs, default_meta) t →
    FC QE Q (.ERd (false, paZ pa, w) :: Ks) (read_ram rk (.Physaddr pa) w false) t := by
  intro hKs hdev hv hq
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    exact .fcMrdGo _ Ks w 64 _ _ t vs hKs hdev rfl rfl rfl hv (.fcRet _ _ _ hq)

/-- (Lean-only) `FEC.fcMrdEnd` with the key as an argument (unified from the goal first). -/
theorem AxSpinVA3.fcMrdEndAt {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) (e : ekey) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    e = .ERd ((classify req.access_kind).akSync, paZ req.pa, n) →
    FC QE Q [e] (.impure (.ok (.memRead n va req)) k) t := by
  rintro h1 h2 rfl
  exact .fcMrdEnd _ _ _ _ _ h1 h2

/-- Rocq `F_read_ram_end` (deviation 3). -/
theorem FReadRamEnd (rk : read_kind) (hrk : rk = .Read_plain ∨ rk = .Read_ttw) (w : Nat)
    (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (t : ExecSt) :
    devAddr pa = false →
    FC QE Q [.ERd (false, paZ pa, w)] (read_ram rk (.Physaddr pa) w false) t := by
  intro hdev
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    exact AxSpinVA3.fcMrdEndAt img _ _ _ w 64 _ _ t hdev rfl rfl

section cmr
variable (μ : ExecSt) (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (w : Nat)
  (pa : BitVec 64) (t : ExecSt)
variable (Hw : vmemWidth w) (Hacc : acc ≠ .InstructionFetch ())
  (Hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tm μ t)
    = some (.Ok pmaOkAligned, tm μ t))
  (Hpmp : execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tm μ t) = some (none, tm μ t))
  (Hmmio : execA (within_mmio_readable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t))
  (Hdev : devAddr pa = false)

include Hw Hacc Hcp Hpmp Hmmio Hdev in
/-- Rocq `F_checked_mem_read_go` (deviation 3). -/
theorem FCheckedMemReadGo
    (Q : List ekey → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (Ks : List ekey) (vs : List (BitVec 8)) :
    Ks ≠ [] → imgBytes img (paZ pa) w = some vs →
    Q Ks (.Ok (rrv w vs, default_meta)) t →
    FC (fun _ _ _ => False) Q (.ERd (false, paZ pa, w) :: Ks)
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false false false) t := by
  intro hKs hv hq
  unfold checked_mem_read
  apply FECCatchEarlyReturn
  refine AxSpinVA3.fRAssoc ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) Hcp ?_
  refine AxSpinVA3.fRPureBind ?_
  refine AxSpinVA3.fRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases Hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals try exact absurd rfl Hacc
  all_goals
    simp only [read_kind_of_flags]
    first
      | refine AxSpinVA3.fRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRBind _ _ _ _ _ _ ?_
    refine FECUntilMT1 img _ _ _ _ _ _ _ ?_
    refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxSpinVA3.fRUse (μ := μ) (rfFPmpCheck _ _ _ _) Hpmp ?_
    dsimp only
    refine AxSpinVA3.fRUse (μ := μ) (rfFWithinMmioReadable _ _) Hmmio ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRLift
      (P := fun Ks' x t' => Ks' = Ks ∧ x = (rrv _ vs, default_meta) ∧ t' = t)
      (FReadRamGo img _ (by simp) _ _ _ pa Ks vs t hKs Hdev hv ⟨rfl, rfl, rfl⟩) ?_
    rintro Ks' x t' ⟨rfl, rfl, rfl⟩
    refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRPure ?_
    refine AxSpinVA3.fRPure ⟨rfl, ?_⟩
    refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRPure ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ hq
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    try bv_decide

include Hw Hacc Hcp Hpmp Hmmio Hdev in
/-- Rocq `F_checked_mem_read_end` (deviation 3). -/
theorem FCheckedMemReadEnd
    (Q : List ekey → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop) :
    FC (fun _ _ _ => False) Q [.ERd (false, paZ pa, w)]
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false false false) t := by
  unfold checked_mem_read
  apply FECCatchEarlyReturn
  refine AxSpinVA3.fRAssoc ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) Hcp ?_
  refine AxSpinVA3.fRPureBind ?_
  refine AxSpinVA3.fRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases Hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals try exact absurd rfl Hacc
  all_goals
    simp only [read_kind_of_flags]
    first
      | refine AxSpinVA3.fRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRBind _ _ _ _ _ _ ?_
    refine FECUntilMT1 img _ _ _ _ _ _ _ ?_
    refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxSpinVA3.fRUse (μ := μ) (rfFPmpCheck _ _ _ _) Hpmp ?_
    dsimp only
    refine AxSpinVA3.fRUse (μ := μ) (rfFWithinMmioReadable _ _) Hmmio ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRLift (P := fun _ _ _ => False) (FReadRamEnd img _ ?_ _ _ _ pa t Hdev)
      (fun _ _ _ h => h.elim)
    simp
end cmr

/-- THE IMAGE-FED PTE READ (Rocq `F_read_pte`): one chain key, the slot word. -/
theorem FReadPte (μ : ExecSt) (pa p : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * 8)) (physaddr × ExceptionType) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteRdOk (fun _ _ => True) μ t pa →
    (∃ vs, imgBytes img (paZ pa) 8 = some vs ∧ rrv 8 vs = p) → Ks ≠ [] →
    Q Ks (.Ok p) t →
    FC (fun _ _ _ => False) Q (.ERd (false, paZ pa, 8) :: Ks) (read_pte (.Physaddr pa) 8) t := by
  rintro ⟨hcp, hpmp, hmm, hdev, -⟩ ⟨vs, hv, rfl⟩ hKs hq
  unfold read_pte mem_read_priv mem_read_priv_meta
  ax_spin_va3_go
  refine AxSpinVA3.fFact (FCheckedMemReadGo img μ _ _ 8 pa t (by simp [vmemWidth])
    (by intro h; cases h) hcp hpmp hmm hdev
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok (rrv 8 vs, default_meta) ∧ t' = t) Ks vs hKs hv
    ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  ax_spin_va3_go
  exact .fcRet _ _ _ hq

end reads

/-! # 3. The walk, the TLB, the translation front -/

/-- Rocq `wkey`: the walker key of the 8-byte slot read at `a`. -/
def wkey (a : BitVec 64) : ekey := .ERd (false, paZ a, 8)

/-- Rocq `islot`: the image holds the slot word `p` at `a`. -/
def islot (img : Image) (a p : BitVec 64) : Prop :=
  ∃ vs, imgBytes img (paZ a) 8 = some vs ∧ rrv 8 vs = p

section walkF
variable (img : Image) (μ : ExecSt) (vpn : BitVec 27) (root : BitVec 44) (p2 p1 p0 : BitVec 64)
  (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : Bool)
variable (H2i : pteValid p2) (H2nl : ptePtr p2) (H1i : pteValid p1) (H1nl : ptePtr p1)
  (H0i : pteValid p0) (H0nl : pteLeaf p0) (Hchk0 : pteCheckOk acc p mxr do_sum p0)
  (H0N : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)

local notation "FC" => FEC img

include H0i H0nl Hchk0 H0N in
/-- Rocq `F_rec_walk_leaf`: level 0, the leaf. -/
theorem FRecWalkLeaf (g : Bool) (menvcfg0 : BitVec 64)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk (fun _ _ => True) μ t (waddr0 vpn p1) → islot img (waddr0 vpn p1) p0 → Ks ≠ [] →
    Q Ks (.Ok (ptwOut vpn p1 p0 (g || uGbit p0), ())) t →
    FC (fun _ _ _ => False) Q (wkey (waddr0 vpn p1) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p1) 0 g ()) t := by
  intro hmisa hmenv hpbmte hok hsl hKs hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (waddr0 vpn p1) p0
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok p0 ∧ t' = t) Ks t hok hsl hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _) (h0iA p0 H0i _) ?_
  rw [if_neg (by simp)]
  refine AxSpinVA3.fFactUse (μ := μ) (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _)
    (execACheckLeafPteLeaf0 vpn acc p mxr do_sum p0 H0i H0nl Hchk0 H0N _ menvcfg0 _ hmisa hmenv
      hpbmte) ?_
  exact .fcRet _ _ _ hq
include H1i H1nl H0i H0nl Hchk0 H0N in
/-- Rocq `F_rec_walk_l1`: level 1, a valid non-leaf step into the leaf. -/
theorem FRecWalkL1 (g : Bool) (menvcfg0 : BitVec 64)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk (fun _ _ => True) μ t (waddr1 vpn p2) → pteRdOk (fun _ _ => True) μ t (waddr0 vpn p1) →
    islot img (waddr1 vpn p2) p1 → islot img (waddr0 vpn p1) p0 → Ks ≠ [] →
    Q Ks (.Ok (ptwOut vpn p1 p0 ((g || uGbit p1) || uGbit p0), ())) t →
    FC (fun _ _ _ => False) Q (wkey (waddr1 vpn p2) :: wkey (waddr0 vpn p1) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p2) 1 g ()) t := by
  intro hmisa hmenv hpbmte hok1 hok0 hsl1 hsl0 hKs hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (waddr1 vpn p2) p1
    (fun Ks' x t' => Ks' = wkey (waddr0 vpn p1) :: Ks ∧ x = .Ok p1 ∧ t' = t) _ t hok1 hsl1
    (List.cons_ne_nil _ _) ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _) (h1iA p1 H1i _) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨H1nl, by decide⟩)]
  exact FRecWalkLeaf (img := img) (μ := μ) (vpn := vpn) (p1 := p1) (p0 := p0) (acc := acc)
    (p := p) (mxr := mxr) (do_sum := do_sum) (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0)
    (H0N := H0N) (g || uGbit p1) menvcfg0 Q Ks t' hmisa hmenv hpbmte hok0 hsl0 hKs hq

include H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N in
/-- Rocq `F_pt_walk`: level 2, the full walk — exactly the three slot keys. -/
theorem FPtWalk (menvcfg0 : BitVec 64)
    (Q : List ekey → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk (fun _ _ => True) μ t (waddr2 vpn root) → pteRdOk (fun _ _ => True) μ t (waddr1 vpn p2) →
    pteRdOk (fun _ _ => True) μ t (waddr0 vpn p1) →
    islot img (waddr2 vpn root) p2 → islot img (waddr1 vpn p2) p1 → islot img (waddr0 vpn p1) p0 →
    Ks ≠ [] →
    Q Ks (.Ok (ptwOut vpn p1 p0 (uGlobal p2 p1 p0), ())) t →
    FC (fun _ _ _ => False) Q
      (wkey (waddr2 vpn root) :: wkey (waddr1 vpn p2) :: wkey (waddr0 vpn p1) :: Ks)
      (pt_walk 39 vpn acc p mxr do_sum root 2 false ()) t := by
  intro hmisa hmenv hpbmte hok2 hok1 hok0 hsl2 hsl1 hsl0 hKs hq
  rw [pt_walk]
  refine FAssertTrue img _ _ _ rfl _ _ _ _ ?_
  refine AxSpinVA3.fFact (FReadPte img μ (waddr2 vpn root) p2
    (fun Ks' x t' => Ks' = wkey (waddr1 vpn p2) :: wkey (waddr0 vpn p1) :: Ks ∧ x = .Ok p2 ∧
      t' = t) _ t hok2 hsl2 (List.cons_ne_nil _ _) ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  refine AxSpinVA3.fFactUse (μ := μ) (rfFPteIsInvalid _ _) (h2iA p2 H2i _) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨H2nl, by decide⟩)]
  exact FRecWalkL1 (img := img) (μ := μ) (vpn := vpn) (p2 := p2) (p1 := p1) (p0 := p0)
    (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H1i := H1i) (H1nl := H1nl)
    (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0) (H0N := H0N) (false || uGbit p2) menvcfg0 Q Ks t'
    hmisa hmenv hpbmte hok1 hok0 hsl1 hsl0 hKs hq

include H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N in
/-- THE MISS (A/D preset, Rocq `F_translate_TLB_miss`): exactly the three slot reads, TLB
filled. -/
theorem FTranslateTLBMiss (asid : BitVec 16) (menvcfg0 : BitVec 64)
    (Q : List ekey → Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk (fun _ _ => True) μ t (waddr2 vpn root) → pteRdOk (fun _ _ => True) μ t (waddr1 vpn p2) →
    pteRdOk (fun _ _ => True) μ t (waddr0 vpn p1) →
    islot img (waddr2 vpn root) p2 → islot img (waddr1 vpn p2) p1 → islot img (waddr0 vpn p1) p0 →
    Ks ≠ [] →
    update_PTE_Bits p0 acc = none →
    Q Ks (.Ok (ppn0 p0, .PBMT_PMA, ())) (AxWalk3.tlbFill vpn p2 p1 t asid p0) →
    FC (fun _ _ _ => False) Q
      (wkey (waddr2 vpn root) :: wkey (waddr1 vpn p2) :: wkey (waddr0 vpn p1) :: Ks)
      (translate_TLB_miss 39 asid root vpn acc p mxr do_sum ()) t := by
  intro hmisa hmenv hpbmte R2 R1 R0 S2 S1 S0 hKs hnoupd hq
  unfold translate_TLB_miss
  refine AxSpinVA3.fFact (FPtWalk (img := img) (μ := μ) (vpn := vpn) (root := root) (p2 := p2)
    (p1 := p1) (p0 := p0) (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H2i := H2i)
    (H2nl := H2nl) (H1i := H1i) (H1nl := H1nl) (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0)
    (H0N := H0N) menvcfg0
    (fun Ks' x t' => Ks' = Ks ∧ x = .Ok (ptwOut vpn p1 p0 (uGlobal p2 p1 p0), ()) ∧ t' = t)
    Ks t hmisa hmenv hpbmte R2 R1 R0 S2 S1 S0 hKs ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  dsimp only [ptwOut, uWalkOut]
  have hu : update_and_write_pte 39 vpn (.Physaddr (waddr0 vpn p1)) p0 0 acc p mxr do_sum ()
      = pure (.Ok (none, ())) := by
    unfold update_and_write_pte
    erw [hnoupd]
  rw [hu]
  refine AxSpinVA3.fFactPure ?_
  refine FECBind0 img _ _ _ _ _ _ ?_
  refine FECExecARfFPost img _ _ _ t' () _ t' _ (rfFAddToTLB _ _ _ _ _ _ _ _)
    (execAAddToTLBUser vpn p2 p1 p0 asid t') rfl ?_
  exact .fcRet _ _ _ hq
end walkF

/-- THE HIT (A/D preset, permission granted; Rocq `F_translate_TLB_hit`): register-only, NO
label. -/
theorem FTranslateTLBHit (img : Image) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr do_sum : Bool) (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat)
    (Q : List ekey → Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    pteCheckOk acc p mxr do_sum q0 → update_PTE_Bits q0 acc = none → ptePbmt0 q0 →
    Q Ks (.Ok (ppn0 q0, .PBMT_PMA, ())) t →
    FEC img (fun _ _ _ => False) Q Ks
      (translate_TLB_hit 39 asid vpn acc p mxr do_sum () idx (uWalkEntry vpn p2 p1 q0 asid)) t := by
  intro hchk hupd hpb hq
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe]
  refine AxSpinVA3.fFactUse (μ := t) (rfFCheckPTEPermission _ _ _ _ _ _ _)
    (hchk0A acc p mxr do_sum q0 hchk _) ?_
  dsimp only
  have hu : ∀ e l, update_and_write_pte 39 vpn e q0 l acc p mxr do_sum () = pure (.Ok (none, ())) := by
    intro e l
    unfold update_and_write_pte
    erw [hupd]
  erw [hu]
  refine AxSpinVA3.fFactPure ?_
  dsimp only
  have hpbA : execA (tlb_get_pbmt (uWalkEntry vpn p2 p1 q0 asid)) (tm t t) =
      some (.PBMT_PMA, tm t t) := by
    unfold tlb_get_pbmt
    ax_spine4_run
    erw [hpb]
    rfl
  refine AxSpinVA3.fFactUse (μ := t) (rfFTlbGetPbmt _) hpbA ?_
  rw [tlbGetPpnUwe]
  exact .fcRet _ _ _ hq

section frontF
variable (img : Image)

/-- THE FRONT (Rocq `F_translateAddr_front`: `translateAddr` → `translate`), canonical VA,
Sv39. -/
theorem FTranslateAddrFront (μ : ExecSt) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (vpn : BitVec 27) (root : BitVec 44) (satp0 va : BitVec 64)
    (Qf : List ekey → Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    exec (effectivePrivilege acc (t.regs .mstatus) p) (tm μ t) = some (p, tm μ t) →
    exec (is_shadow_stack_access acc) (tm μ t) = some (false, tm μ t) →
    t.regs .cur_privilege = p →
    exec (translationMode p) (tm μ t) = some (.Sv39, tm μ t) →
    t.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38
      Functions.pagesize_bits) = vpn →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => match r with
        | .Ok (ppn, pbmt, ext) =>
            Qf Ks' (.Ok (.Physaddr (zero_extend (m := 64)
              (ppn +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)), pbmt, ext)) t'
        | .Err _ => False)
      Ks
      (translate 39 0#16 root vpn acc p ((_get_Mstatus_MXR (t.regs .mstatus)) == 1#1)
        ((_get_Mstatus_SUM (t.regs .mstatus)) == 1#1) init_ext_ptw) t →
    FEC img (fun _ _ _ => False) Qf Ks (translateAddr (.Virtaddr va) acc) t := by
  intro heff hss hcp htm hsatp hppn hasid hcanon hvpn HTR
  have heffA := execAOfRfF _ (rfFEffectivePrivilege _ _ _) _ _ heff
  have hssA := execAOfRfF _ (rfFIsShadowStackAccess _) _ _ hss
  have htmA := execAOfRfF _ (rfFTranslationMode _) _ _ htm
  unfold translateAddr
  apply FECCatchEarlyReturn
  ax_spin_va3_go
  rw [hcp]
  refine AxSpinVA3.fRUse (μ := μ) (rfFEffectivePrivilege _ _ _) heffA ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFTranslationMode _) htmA ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFIsShadowStackAccess _) hssA ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp (config := { decide := true }) only [↓reduceIte]
  refine AxSpinVA3.fRUse (μ := μ) (rfFSatpModeWidthForwards _) (a := (39 : Int)) rfl ?_
  have hgs : execA (get_satp 39) (tm μ t) = some (satp0, tm μ t) := by
    unfold get_satp
    ax_spine4_run [hsatp]
    show some (BitVec.setWidth 64 satp0, _) = _
    rw [BitVec.setWidth_eq]
  simp (config := { decide := true }) only [Int.reduceToNat, Int.reduceSub, bits_of_virtaddr,
    hcanon, Bool.false_eq_true, ↓reduceIte, Nat.reduceSub]
  refine AxSpinVA3.fRUse (μ := μ) (rfFGetSatp _) hgs ?_
  refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
  ax_spin_va3_go
  erw [hasid, hppn, hvpn]
  refine AxSpinVA3.fRLift HTR ?_
  intro Ks' x t' hx
  cases x with
  | Ok a =>
    obtain ⟨ppn, pbmt, ext⟩ := a
    exact .fcRet _ _ _ hx
  | Err e => exact hx.elim
end frontF

/-- Rocq `tlb_hitb`: the TLB hits `vpn` (ASID 0). -/
def tlbHitb (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) : Bool :=
  match tlbvec[tlb_hash 39 vpn]! with
  | some ent => match_TLB_Entry ent 0#16 (sign_extend (m := 57 - 12) vpn)
  | none => false

/-- Rocq `walk_keys`: the walker keys the translation of `vpn` emits — none on a hit, the three
slot reads on a miss. -/
def walkKeys (T : PTree) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27)
    (p2 p1 : BitVec 64) : List ekey :=
  if tlbHitb tlbvec vpn then []
  else [wkey (AxPtProt.ptAddr2 T vpn), wkey (AxPtProt.ptAddr1 p2 vpn), wkey (AxPtProt.ptAddr0 p1 vpn)]

/-- THE TRANSLATION OF AN ARBITRARY MAPPED VA (Rocq `F_translateAddr_img`), image-fed, at
`FEC`: the chain gains `walkKeys` (TLB hit: nothing; miss / foreign slot: the three slot reads);
post: `t` (hit) or the TLB fill (miss).  Deviation 5: `AxSpineOk6.pmpOk` /
`pma_regions = bootPMA`. -/
theorem FTranslateAddrImg (σi : ExecSt) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (rootPpn : BitVec 44) (va w pa satp0 : BitVec 64) (T : PTree) (p2 p1 : BitVec 64)
    (Qf : List ekey → Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit) →
      ExecSt → Prop)
    (Ks : List ekey) (t : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    (∀ (mxr do_sum : Bool), pteCheckOk acc p mxr do_sum w) →
    update_PTE_Bits w acc = none →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    ptePbmt0 w → T.base = rootPpn → AxPtProt.ptreeMaps T vpn p2 p1 w →
    tlbExact T (t.regs .tlb) →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T vpn) p2 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 vpn) p1 →
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 vpn) w →
    t.regs .misa = misaC →
    t.regs .menvcfg = menvcfgS →
    t.regs .htif_tohost_base = none →
    t.regs .cur_privilege = p →
    exec (translationMode p) (tm σi t) = some (.Sv39, tm σi t) →
    exec (effectivePrivilege acc (t.regs .mstatus) p) (tm σi t) = some (p, tm σi t) →
    exec (is_shadow_stack_access acc) (tm σi t) = some (false, tm σi t) →
    t.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = rootPpn →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    AxSpineOk6.pmpOk t.regs → t.regs .pma_regions = bootPMA →
    Ks ≠ [] →
    (tlbHitb (t.regs .tlb) vpn = true →
      Qf Ks (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw)) t) →
    (tlbHitb (t.regs .tlb) vpn = false →
      Qf Ks (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw))
        (t.setReg .tlb (vectorUpdate (t.regs .tlb) (tlb_hash 39 vpn)
          (some (uWalkEntry vpn p2 p1 w 0#16))))) →
    FEC (imgOf σi) (fun _ _ _ => False) Qf (walkKeys T (t.regs .tlb) vpn p2 p1 ++ Ks)
      (translateAddr (.Virtaddr va) acc) t := by
  intro vpn hchk hupd hcanon hout hpb hbase hmaps htlbok hsm2 hsm1 hsm0 hmisa hmenv hhtif hcp htm
    heff hss hsatp hppn hasid hpmp hpma hKs hhit hmiss
  obtain ⟨c1, c0, -, -, -, -, -, -, -, hv2, hn2, hv1, hn1, hv0, hl0, hnap, -⟩ := id hmaps
  have ha2 : AxPtProt.ptAddr2 T vpn = waddr2 vpn rootPpn := by
    unfold AxPtProt.ptAddr2 waddr2; rw [hbase]; rfl
  have ha1 : AxPtProt.ptAddr1 p2 vpn = waddr1 vpn p2 := rfl
  have ha0 : AxPtProt.ptAddr0 p1 vpn = waddr0 vpn p1 := rfl
  have R2 := pteRdOkOfRegs (fun _ _ => True) σi t _ _ σi hsm2 hpmp hpma hhtif trivial
  have R1 := pteRdOkOfRegs (fun _ _ => True) σi t _ _ σi hsm1 hpmp hpma hhtif trivial
  have R0 := pteRdOkOfRegs (fun _ _ => True) σi t _ _ σi hsm0 hpmp hpma hhtif trivial
  have S2 := slotImg σi _ _ hsm2
  have S1 := slotImg σi _ _ hsm1
  have S0 := slotImg σi _ _ hsm0
  rw [ha2] at R2 S2
  rw [ha1] at R1 S1
  rw [ha0] at R0 S0
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  -- the miss path, shared by the empty and the foreign slot
  have hmissp : execA (lookup_TLB 39 0#16 vpn) (tm σi t) = some (none, tm σi t) →
      tlbHitb (t.regs .tlb) vpn = false →
      FEC (imgOf σi) (fun _ _ _ => False) Qf
        (wkey (AxPtProt.ptAddr2 T vpn) :: wkey (AxPtProt.ptAddr1 p2 vpn) ::
          wkey (AxPtProt.ptAddr0 p1 vpn) :: Ks)
        (translateAddr (.Virtaddr va) acc) t := by
    intro hlk hhb
    refine FTranslateAddrFront (imgOf σi) σi acc p vpn rootPpn satp0 va Qf _ t heff hss hcp htm
      hsatp hppn hasid hcanon rfl ?_
    unfold translate
    refine AxSpinVA3.fFactUse (μ := σi) (rfFLookupTLB _ _ _) hlk ?_
    rw [ha2, ha1, ha0]
    refine FTranslateTLBMiss (img := imgOf σi) (μ := σi) (vpn := vpn) (root := rootPpn) (p2 := p2)
      (p1 := p1) (p0 := w) (acc := acc) (p := p) (mxr := _) (do_sum := _) (H2i := hv2)
      (H2nl := hn2) (H1i := hv1) (H1nl := hn1) (H0i := hv0) (H0nl := hl0) (Hchk0 := hchk _ _)
      (H0N := hnap) 0#16 menvcfgS _ Ks t hmisa hmenv hpbmte R2 R1 R0 S2 S1 S0 hKs hupd ?_
    show Qf Ks (.Ok (.Physaddr (zero_extend (m := 64)
      (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)), .PBMT_PMA, ())) _
    rw [hout]
    exact hmiss hhb
  unfold walkKeys
  cases hslot : (t.regs .tlb)[tlb_hash 39 vpn]! with
  | none =>
    have hhb : tlbHitb (t.regs .tlb) vpn = false := by
      unfold tlbHitb; rw [hslot]
    rw [hhb]
    have hlk := execLookupTLBMiss vpn 0#16 (t.regs .tlb) (tm σi t) rfl hslot
    to_a hlk
    exact hmissp hlk hhb
  | some ent =>
    obtain ⟨vpn0, q2, q1, q0, hm0, -, hent⟩ := htlbok vpn ent hslot
    by_cases hne : vpn0 = vpn
    · rw [hne] at hm0 hent
      obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet T vpn q2 q1 q0 p2 p1 w hm0 hmaps
      rw [h2, h1, h0] at hent
      rw [hent] at hslot
      have hhb : tlbHitb (t.regs .tlb) vpn = true := by
        unfold tlbHitb; rw [hslot]; exact WeakKpt.uweMatchSelf vpn p2 p1 w 0#16
      rw [hhb]
      have hlk := execLookupTLBHitEnt vpn 0#16 (t.regs .tlb) _ (tm σi t) rfl hslot
        (WeakKpt.uweMatchSelf vpn p2 p1 w 0#16)
      to_a hlk
      refine FTranslateAddrFront (imgOf σi) σi acc p vpn rootPpn satp0 va Qf _ t heff hss hcp htm
        hsatp hppn hasid hcanon rfl ?_
      unfold translate
      refine AxSpinVA3.fFactUse (μ := σi) (rfFLookupTLB _ _ _) hlk ?_
      refine FTranslateTLBHit (imgOf σi) acc p _ _ vpn p2 p1 w 0#16 _ _ _ t (hchk _ _) hupd hpb ?_
      show Qf _ (.Ok (.Physaddr (zero_extend (m := 64)
        (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)), .PBMT_PMA, ())) _
      rw [hout]
      exact hhit hhb
    · have hhb : tlbHitb (t.regs .tlb) vpn = false := by
        unfold tlbHitb; rw [hslot, hent]
        exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 q0 0#16 hne
      rw [hhb]
      have hlk := execLookupTLBNomatchS vpn 0#16 ent (t.regs .tlb) (tm σi t) rfl hslot
        (by rw [hent]; exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 q0 0#16 hne)
      to_a hlk
      exact hmissp hlk hhb

end Weak
