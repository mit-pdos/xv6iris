/-
Weak: **RUN PAIRING, §10** -- THE REAL STORE `main+0xb0`, `c.sw a4,0(a5)` = `0xc398`, on the
machine's own register file.

Rocq: `iris/AxPair.v` @ xxvzwolszwmp, lines 1622–1977 (§§10–11; §§1–9 are `Weak/AxPair.lean`).

## The Rocq header, in substance

THE FINDING, MEASURED: from the fetch's resume the instruction takes 7 administrative nodes to the
`regRead` of `x14` -- a4, THE DATA REGISTER -- and reads `x15` (a5, the ADDRESS) at node 8; 172
more silent nodes reach the `memWrite` (pa = `&started`, plain, value = the data word); the
announced bits decode to `ORstore 15 14` (`asrc = [DReg 15]`, `vsrc = [DReg 14]`); 8 silent nodes
reach `pure`.  So two runs from files differing only in `x14` part company at a `regRead` BEFORE
the write.  Proved at ARBITRARY data words `w1 w2 : BitVec 64`: `rswRun` (the machine's own run
from the data-read node: 172 × `LSilent`, the store label, 8 × `LSilent`), `rswPair` (the two
runs' label lists are pointwise `lblModdata`), `rswTwoWords` (at the words 1 and 7 they DIFFER, in
the data), `rswStopRead` (the data-read node paired WITH ITSELF is a READ STOP of `tpddStep`).
WHAT IS NOT PROVED, AND WHY IT CANNOT BE AS A TREE RELATION: the per-instruction fact
`∀ v1 v2, tpdd T (K v1) (K v2)` is FALSE for the real continuation `K` as a relation on trees (its
MMIO branch hands the data to the platform's console); it must be a RUN-LEVEL statement.

## Deviations from Rocq

1. NAMES / VOCABULARY: as `AxPair` (deviation 1 there).  `bv_unsigned ev_wf` ↦ `evWf.toNat`
   (the Lean fetch is ONE 2-byte read, `WeakEvStarted` deviation 7).
2. THE STATE: Rocq's `ColdBoot.cold_regs (mword_of_int 0)` ↦ `bootLand ⟨0, _⟩
   WeakEvStarted.regs0`, as `WeakEvStarted.evRs0` (whose `x14` is `1`; here it is the free `w`).
   `ev_flag`/`ev_pc`/`ev_wf` are `WeakEvStarted`'s `evFlag`/`evPc`/`evWf` (the Lean kernel image).
   The MEASUREMENT MATCHES ROCQ: 7 nodes to the data read, 172 to the store, 8 to `pure`.
3. THE COMPUTATIONS: Rocq's `vm_cast_no_check (eq_refl _)` at the free word `w` are closed by
   `WeakRvwmoAdm`'s `weak_adm_krfl` (kernel `Eq.refl` over the local context); closed facts by
   `decide +kernel`.  `bool_decide (14 ∈ …)` ↦ `decide (14 ∈ …)`.
4. lean-sail's write request value is an `Option` (`AxPair` deviation 3): `rswLbl req` is stated
   at `req.value.getD 0` (so `rswLblModdata` keeps Rocq's one premise), and the Lean-only fact
   `AxPair.rswStoreHasVal` (the computed request carries a value) feeds `rswStoreStep`.  `rswReq`
   is the Lean request literal (`va := none`, `size := 4`, `tag := none`, the plain access
   kind `swAk`); Rocq's `WriteReq.make 4 ev_flag sw_ak … None tt None`.
5. `option_map` ↦ `Option.map`; `Example rsw_two_words` ↦ `theorem`; §11's `Print Assumptions`
   are dropped.
6. `phrun_app` is a duplicated Rocq name (`WeakRvwmoCert3`): `AxPair.phrunApp`.

**Rocq → Lean name map.**  `rsw_rs0` `rswRs0`, `rsw_x14_carrier` `rswX14Carrier`,
`rsw_rs0_agree` `rswRs0Agree`, `rsw_x0/x1/xf/xr/xw/xt` `rswX0/X1/Xf/Xr/Xw/Xt`, `rsw_rd_data`
`rswRdData`, `rsw_rd_addr` `rswRdAddr`, `rsw_first_taint` `rswFirstTaint`, `rsw_lbls_pre`
`rswLblsPre`, `rsw_lbls_tail` `rswLblsTail`, `rsw_end_ret` `rswEndRet`, `rsw_store_pa`
`rswStorePa`, `rsw_store_ak` `rswStoreAk`, `rsw_flag_ram` `rswFlagRam`, `rsw_bits` `rswBits`,
`rsw_ib_bits` `rswIbBits`, `rsw_bits_roles/asrc/vsrc` `rswBitsRoles/Asrc/Vsrc`, `rsw_lbl`
`rswLbl`, `rsw_lbl_moddata` `rswLblModdata`, `rsw_store_step` `rswStoreStep`, `phrun_app`
`AxPair.phrunApp`, `rsw_run` `rswRun`, `Forall2_moddata_replicate` `forall2ModdataReplicate`,
`rsw_pair` `rswPair`, `rsw_req` `rswReq`, `rsw_req1/req7` `rswReq1/rswReq7`, `rsw_lbl_differ`
`rswLblDiffer`, `lookup_replicate_mid` `lookupReplicateMid`, `rsw_two_words` `rswTwoWords`,
`rsw_stop_read` `rswStopRead`.  Lean-only (file-qualified): `AxPair.rswStoreHasVal`,
`AxPair.forall2App` (`Forall2_app`, not in Lean core).

**Dropped:** nothing (Rocq §10: 37 declarations; Lean 37 + 2 Lean-only).
-/
import Weak.AxPair

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 10. THE REAL STORE -/

/-- The publisher's file with the DATA register `x14` = a4 left free. -/
def rswRs0 (w : BitVec 64) : RegFile :=
  ((((bootLand ⟨0, by decide⟩ WeakEvStarted.regs0).set .x14 w).set .x15 evFlag).set .PC
    evPc).set .nextPC evPc

theorem rswX14Carrier : eregNum .x14 = some 14 := by decide +kernel

/-- Two such files agree off `[14]`. -/
theorem rswRs0Agree (w1 w2 : BitVec 64) :
    dregAgree (fun n => n ∉ [14]) (rswRs0 w1) (rswRs0 w2) := by
  unfold rswRs0
  refine dregAgreeSet _ _ _ _ _ (dregAgreeSet _ _ _ _ _ (dregAgreeSet _ _ _ _ _ ?_))
  exact dregAgreeExcl2 _ _ _ .x14 w1 w2
    ⟨14, rswX14Carrier, fun h => h (List.mem_singleton_self _)⟩ (dregAgreeRefl _ _)

/-- THE CURSORS -- unevaluated compositions. -/
noncomputable def rswX0 (w : BitVec 64) : aht := ((rswRs0 w, ibNone), riscvStep false)
noncomputable def rswX1 (w : BitVec 64) : aht := admIter false 400 (rswX0 w)
noncomputable def rswXf (w : BitVec 64) : aht := ahRead evWf.toNat (rswX1 w)
noncomputable def rswXr (w : BitVec 64) : aht := admIter false 7 (rswXf w)
noncomputable def rswXw (w : BitVec 64) : aht := admIter false 172 (rswXr w)
noncomputable def rswXt (w : BitVec 64) : aht := admIter false 8 (ahWrite (rswXw w))

/-- (i) THE NODE ORDER: the data register first, the address register next. -/
theorem rswRdData (w : BitVec 64) : pnodeRds (ahM (rswXr w)) = [14] := by
  weak_adm_krfl

theorem rswRdAddr (w : BitVec 64) : pnodeRds (ahM (admIter false 1 (rswXr w))) = [15] := by
  weak_adm_krfl

theorem rswFirstTaint (w : BitVec 64) : decide (14 ∈ (ahIb (rswXr w)).ibRds) = false := by
  weak_adm_krfl

/-- (ii) THE STRETCHES ARE SILENT AND DATA-INDEPENDENT. -/
theorem rswLblsPre (w : BitVec 64) :
    admLbls false 172 (rswXr w) = List.replicate 172 LSilent := by
  weak_adm_krfl

theorem rswLblsTail (w : BitVec 64) :
    admLbls false 8 (ahWrite (rswXw w)) = List.replicate 8 LSilent := by
  weak_adm_krfl

theorem rswEndRet (w : BitVec 64) : ahM (rswXt w) = .pure () := by
  weak_adm_krfl

/-- (iii) THE STORE NODE, by small projections. -/
theorem rswStorePa (w : BitVec 64) :
    (ewriteReqAt 4 64 (ahM (rswXw w))).map (·.pa) = some evFlag := by
  weak_adm_krfl

theorem rswStoreAk (w : BitVec 64) :
    (ewriteReqAt 4 64 (ahM (rswXw w))).map (fun r => classify r.access_kind) =
      some ⟨false, false, false⟩ := by
  weak_adm_krfl

/-- (Lean-only, deviation 4) the computed request carries a value. -/
theorem AxPair.rswStoreHasVal (w : BitVec 64) :
    (ewriteReqAt 4 64 (ahM (rswXw w))).map (fun r => r.value.isSome) = some true := by
  weak_adm_krfl

theorem rswFlagRam : devAddr evFlag = false := by decide +kernel

def rswBits : BitVec 32 := BitVec.ofNat 32 0xc398   -- c.sw a4,0(a5)

theorem rswIbBits (w : BitVec 64) : (ahIb (rswXw w)).ibBits = some rswBits := by
  weak_adm_krfl

theorem rswBitsRoles : depsOfIb (some rswBits) = .ORstore 15 14 := by decide +kernel

theorem rswBitsAsrc : depsAsrc (depsOfIb (some rswBits)) = [.DReg 15] := by decide +kernel

theorem rswBitsVsrc : depsVsrc (depsOfIb (some rswBits)) = [.DReg 14] := by decide +kernel

/-- The store's label at a request (deviation 4). -/
def rswLbl (req : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak) : Wlabel :=
  LStore false (paZ req.pa) (WeakInterpProj.wbytes 4 (req.value.getD 0)) [.DReg 15] [.DReg 14]

theorem rswLblModdata (req1 req2 : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak) :
    req1.pa = req2.pa → lblModdata (rswLbl req1) (rswLbl req2) := by
  intro hpa
  refine Or.inr (Or.inl ⟨false, paZ req1.pa, WeakInterpProj.wbytes 4 (req1.value.getD 0),
    WeakInterpProj.wbytes 4 (req2.value.getD 0), [.DReg 15], [.DReg 14], ?_, rfl, ?_⟩)
  · rw [wbytesLength, wbytesLength]
  · rw [rswLbl, hpa]

/-- THE STORE STEP of the machine's node, at any data word. -/
theorem rswStoreStep (cpu : CPU) (d : Efab) (w : BitVec 64) :
    ∃ req : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak,
      ewriteReqAt 4 64 (ahM (rswXw w)) = some req ∧
      req.pa = evFlag ∧
      pstepHw cpu (ahM (rswXw w)) (ahRs (rswXw w)) none (ahIb (rswXw w)) d
        (rswLbl req) [] [] false (ahM (ahWrite (rswXw w))) none none d none none := by
  have hpa := rswStorePa w
  have hak := rswStoreAk w
  have hhv := AxPair.rswStoreHasVal w
  cases E : ewriteReqAt 4 64 (ahM (rswXw w)) with
  | none => rw [E] at hpa; cases hpa
  | some req =>
    rw [E] at hpa hak hhv
    simp only [Option.map_some, Option.some.injEq] at hpa hak hhv
    refine ⟨req, rfl, hpa, ?_⟩
    obtain ⟨K, hm, hres⟩ := ewriteReqAtInv 4 64 _ req E
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hhv
    have hst := pnodeStepStore 4 64 req v K (ahRs (rswXw w)) (ahIb (rswXw w)) d.efDev
      (by rw [hpa]; exact rswFlagRam) hv (by decide) (by rw [hak])
    rw [rswIbBits, rswBitsAsrc, rswBitsVsrc, hak] at hst
    have hl : rswLbl req =
        LStore false (paZ req.pa) (WeakInterpProj.wbytes 4 v) [.DReg 15] [.DReg 14] := by
      simp only [rswLbl, hv, Option.getD_some]
    change pstepHw cpu (ahM (rswXw w)) (ahRs (rswXw w)) none (ahIb (rswXw w)) d
      (rswLbl req) [] [] false (ewriteResume (ahM (rswXw w))) none none d none none
    rw [hres, hl, hm]
    exact Or.inl ⟨rfl, ⟨hst, rfl⟩, rfl, rfl, rfl⟩

/-- Runs compose. -/
theorem AxPair.phrunApp (cpu : CPU) (ls1 : List Wlabel) (rds1 : List Nat)
    (ws1 : List Register) (ann1 : Bool) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool))
    (ib1 : Ibch) (d1 : Efab) (ls2 : List Wlabel) (rds2 : List Nat)
    (ws2 : List Register) (ann2 : Bool) (m2 : SailM Unit) (rs2 : RegFile)
    (fn2 : Option (Bool × Bool × Bool × Bool)) (ib2 : Ibch) (d2 : Efab) :
    phrun cpu ls1 rds1 ws1 ann1 m rs fn ib d m1 rs1 fn1 ib1 d1 →
    phrun cpu ls2 rds2 ws2 ann2 m1 rs1 fn1 ib1 d1 m2 rs2 fn2 ib2 d2 →
    phrun cpu (ls1 ++ ls2) (rds1 ++ rds2) (ws1 ++ ws2) (ann1 || ann2)
      m rs fn ib d m2 rs2 fn2 ib2 d2 := by
  intro h1
  induction h1 with
  | nil => intro h2; exact h2
  | more hstep _ ih =>
    intro h2
    rw [List.cons_append, List.append_assoc, List.append_assoc, Bool.or_assoc]
    exact phrun.more hstep (ih h2)

/-- THE RUN: the machine's own, from the data-read node to `pure`. -/
theorem rswRun (cpu : CPU) (d : Efab) (w : BitVec 64) :
    ∃ (req : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak) (rds : List Nat)
      (ws : List Register) (ann : Bool),
      ewriteReqAt 4 64 (ahM (rswXw w)) = some req ∧
      req.pa = evFlag ∧
      phrun cpu (List.replicate 172 LSilent ++ rswLbl req :: List.replicate 8 LSilent)
        rds ws ann
        (ahM (rswXr w)) (ahRs (rswXr w)) none (ahIb (rswXr w)) d
        (.pure ()) (ahRs (rswXt w)) none (ahIb (rswXt w)) d := by
  obtain ⟨req, E, hpa, hst⟩ := rswStoreStep cpu d w
  obtain ⟨rds1, ws1, ann1, h1⟩ :=
    pevrunPhrun _ _ _ _ _ (pevrunOfIter false 172 cpu d (rswXr w)) cpu (ahM (rswXr w))
      (ahRs (rswXr w)) none (ahIb (rswXr w)) (ahM (rswXw w)) (ahRs (rswXw w)) none
      (ahIb (rswXw w)) rfl rfl
  obtain ⟨rds3, ws3, ann3, h3⟩ :=
    pevrunPhrun _ _ _ _ _ (pevrunOfIter false 8 cpu d (ahWrite (rswXw w))) cpu
      (ahM (ahWrite (rswXw w))) (ahRs (ahWrite (rswXw w))) none (ahIb (ahWrite (rswXw w)))
      (ahM (rswXt w)) (ahRs (rswXt w)) none (ahIb (rswXt w)) rfl rfl
  rw [rswLblsPre] at h1
  rw [rswLblsTail, rswEndRet] at h3
  exact ⟨req, _, _, _, E, hpa, AxPair.phrunApp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h1 (phrun.more hst h3)⟩

/-- (Lean-only) `Forall₂` of an append. -/
theorem AxPair.forall2App {R : Wlabel → Wlabel → Prop} {a1 a2 b1 b2 : List Wlabel} :
    List.Forall₂ R a1 a2 → List.Forall₂ R b1 b2 → List.Forall₂ R (a1 ++ b1) (a2 ++ b2) := by
  intro ha hb
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

theorem forall2ModdataReplicate (n : Nat) :
    List.Forall₂ lblModdata (List.replicate n LSilent) (List.replicate n LSilent) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (Or.inl rfl) ih

/-- THE PAIR, on the real machine. -/
theorem rswPair (cpu : CPU) (d : Efab) (w1 w2 : BitVec 64) :
    dregAgree (fun n => n ∉ [14]) (rswRs0 w1) (rswRs0 w2) ∧
    ∃ (ls1 ls2 : List Wlabel) (rds1 rds2 : List Nat) (ws1 ws2 : List Register)
      (ann1 ann2 : Bool),
      phrun cpu ls1 rds1 ws1 ann1
        (ahM (rswXr w1)) (ahRs (rswXr w1)) none (ahIb (rswXr w1)) d
        (.pure ()) (ahRs (rswXt w1)) none (ahIb (rswXt w1)) d ∧
      phrun cpu ls2 rds2 ws2 ann2
        (ahM (rswXr w2)) (ahRs (rswXr w2)) none (ahIb (rswXr w2)) d
        (.pure ()) (ahRs (rswXt w2)) none (ahIb (rswXt w2)) d ∧
      ls1.length = 181 ∧
      List.Forall₂ lblModdata ls1 ls2 ∧
      ls1.map lblIdent = ls2.map lblIdent := by
  refine ⟨rswRs0Agree w1 w2, ?_⟩
  obtain ⟨req1, rds1, ws1, ann1, -, hpa1, h1⟩ := rswRun cpu d w1
  obtain ⟨req2, rds2, ws2, ann2, -, hpa2, h2⟩ := rswRun cpu d w2
  have hf : List.Forall₂ lblModdata
      (List.replicate 172 LSilent ++ rswLbl req1 :: List.replicate 8 LSilent)
      (List.replicate 172 LSilent ++ rswLbl req2 :: List.replicate 8 LSilent) :=
    AxPair.forall2App (forall2ModdataReplicate 172)
      (.cons (rswLblModdata req1 req2 (hpa1.trans hpa2.symm)) (forall2ModdataReplicate 8))
  exact ⟨_, _, _, _, _, _, _, _, h1, h2,
    by rw [List.length_append, List.length_cons, List.length_replicate, List.length_replicate], hf, forall2ModdataIdent _ _ hf⟩

/-- THE TWO WORDS 1 AND 7: the requests, read back small. -/
def rswReq (v : Nat) : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := swAk, va := none, pa := evFlag, translation := (), size := 4,
    value := some (BitVec.ofNat 32 v), tag := none }

theorem rswReq1 : ewriteReqAt 4 64 (ahM (rswXw (BitVec.ofNat 64 1))) = some (rswReq 1) := by
  weak_adm_krfl

theorem rswReq7 : ewriteReqAt 4 64 (ahM (rswXw (BitVec.ofNat 64 7))) = some (rswReq 7) := by
  weak_adm_krfl

theorem rswLblDiffer : rswLbl (rswReq 1) ≠ rswLbl (rswReq 7) := by
  have hz : wdataZ (rswLbl (rswReq 1)) ≠ wdataZ (rswLbl (rswReq 7)) := by decide +kernel
  intro h
  exact hz (by rw [h])

theorem lookupReplicateMid (n : Nat) (x l : Wlabel) (t : List Wlabel) :
    (List.replicate n x ++ l :: t)[n]? = some l := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ] at ih ⊢

theorem rswTwoWords (cpu : CPU) (d : Efab) :
    ∃ (ls1 ls2 : List Wlabel) (rds1 rds2 : List Nat) (ws1 ws2 : List Register)
      (ann1 ann2 : Bool),
      phrun cpu ls1 rds1 ws1 ann1
        (ahM (rswXr (BitVec.ofNat 64 1))) (ahRs (rswXr (BitVec.ofNat 64 1))) none
        (ahIb (rswXr (BitVec.ofNat 64 1))) d
        (.pure ()) (ahRs (rswXt (BitVec.ofNat 64 1))) none
        (ahIb (rswXt (BitVec.ofNat 64 1))) d ∧
      phrun cpu ls2 rds2 ws2 ann2
        (ahM (rswXr (BitVec.ofNat 64 7))) (ahRs (rswXr (BitVec.ofNat 64 7))) none
        (ahIb (rswXr (BitVec.ofNat 64 7))) d
        (.pure ()) (ahRs (rswXt (BitVec.ofNat 64 7))) none
        (ahIb (rswXt (BitVec.ofNat 64 7))) d ∧
      List.Forall₂ lblModdata ls1 ls2 ∧
      ls1.map lblIdent = ls2.map lblIdent ∧
      ls1 ≠ ls2 := by
  obtain ⟨req1, rds1, ws1, ann1, E1, -, h1⟩ := rswRun cpu d (BitVec.ofNat 64 1)
  obtain ⟨req2, rds2, ws2, ann2, E2, -, h2⟩ := rswRun cpu d (BitVec.ofNat 64 7)
  rw [rswReq1, Option.some.injEq] at E1
  rw [rswReq7, Option.some.injEq] at E2
  subst E1 E2
  have hf : List.Forall₂ lblModdata
      (List.replicate 172 LSilent ++ rswLbl (rswReq 1) :: List.replicate 8 LSilent)
      (List.replicate 172 LSilent ++ rswLbl (rswReq 7) :: List.replicate 8 LSilent) :=
    AxPair.forall2App (forall2ModdataReplicate 172)
      (.cons (rswLblModdata _ _ rfl) (forall2ModdataReplicate 8))
  refine ⟨_, _, _, _, _, _, _, _, h1, h2, hf, forall2ModdataIdent _ _ hf, ?_⟩
  intro H
  apply rswLblDiffer
  have hm : some (rswLbl (rswReq 1)) = some (rswLbl (rswReq 7)) := by
    rw [← lookupReplicateMid 172 LSilent (rswLbl (rswReq 1)) (List.replicate 8 LSilent),
      ← lookupReplicateMid 172 LSilent (rswLbl (rswReq 7)) (List.replicate 8 LSilent), H]
  exact Option.some.inj hm

/-- WHERE THE GENERAL MACHINERY STOPS: the data-read node paired with itself is a READ STOP. -/
theorem rswStopRead (w : BitVec 64) :
    stopRead [14] (ahM (rswXr w)) (ahM (rswXr w)) [14] := by
  obtain ⟨r, k, hm, hr, -⟩ := pnodeRdsShape (ahM (rswXr w)) 14
    (by rw [rswRdData]; exact List.mem_singleton_self _)
  exact ⟨r, k, k, 14, hm, hm, hr, List.mem_singleton_self _, rfl, fun _ => tpdg.tgConv _⟩

end Weak
