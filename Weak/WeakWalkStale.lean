/-
Weak: **the S-mode page-table walk with a RACY LEAF READ** (6a): the miss-path
translation at the stale mirror `WeakStale.execStale la 8 pv` -- the walk's PLAIN leaf
read returns the racy word `pv`, the CAS's exclusive re-read returns the memory's `p0`.

Rocq: `iris/WeakWalkStale.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakStale` is generic; this file is the walk.  It
states the miss-path translation at `execStale la 8 pv` and proves it WITHOUT mirroring
`WeakWalkEff` / `WeakUpdEff`, by the two transfers:
* the WALK (`pt_walk`, three plain reads, one of them the window): no PINNED read, so
  `execStaleOfPatchId` turns `execEffPtWalkUser` AT THE PATCHED STATE into the
  `execStale` fact (the leaf slot holding `pv`);
* the CAS (`read_pte_exclusive` + `write_pte_conditional`) and the TLB fill: no
  UNPINNED read, so `execStaleOfExecEff` turns `WeakUpdEff`'s arms AT THE REAL STATE
  into `execStale` facts.  Those arms already take the STALE word as a parameter
  separate from the freshly-read one (the model's atomic recheck).
THE SIXTH OUTCOME: at `execEff` the miss path's O-FRESH arm is unreachable (the fresh
word IS the walked word); under a racy plain read it is REACHABLE -- the gate fires on
the stale word, the CAS re-reads a word that needs nothing, and the run ends READ-ONLY.
§3's dispatch has three arms where the `execEff` one has two.  §4 is the early-return
interpreter at the mirror, §5 the `translateAddr` front, §6 the end-to-end case theorem,
§7 the slot facts at the patched state.

O2 (`notes/weak-port-o2-design.md`): the walker's `read_pte` classifies as `wakPlain`
(`WeakWalkEff` header), the exclusive pair as `wakExcl = ⟨false, true, false⟩`
(`WeakUpdEff` header) -- Rocq's kinds literally.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WeakWalkEff.lean` / `Weak/WeakUpdEff.lean` deviation 1 and
   `Weak/WeakStale.lean` deviation 1 (`register_lookup r s.(sregs)` ↦ `s.regs r`,
   `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `autocast (PPN_of_PTE p)` ↦ `ppn0 p`, the
   walk's output record ↦ `uWalkOut`, `mword_of_int 0` ↦ `0#16`, `set_reg s tlb v` ↦
   `s.setReg .tlb v`, `register_set tlb v s.(sregs)` ↦ `s.regs.set .tlb v`,
   `MState s.(sregs) (write_bytes …) s.(mdev)` ↦ `s.setMem (bmWrite …)`, `MISA_C` ↦
   `misaC`, `pte_set_ad` ↦ `pteSetAD`, stdpp `Forall P es` ↦ `∀ e, e ∈ es → P e`).
   Section variables/hypotheses and the section `Let`s `addr2/1/0` are theorem
   arguments / inlined; the statement-level `let la := … in` (and `e2/e1/e0`) are
   inlined.  The front premises are `WeakWalkEff.execEffTranslateAddrPtFront`'s
   (`WeakWalkEff` deviation 7).
2. `execRStale` is not a second `Fixpoint` (as `WeakEffSkel.execREff`, WeakEffSkel
   deviation 2): Lean's `SailME R X` is `ExceptT`, so it is `execStale` of the `run`;
   the kit is proved from `WeakStale.execStaleBindEq` rather than by induction.
3. The two `Ltac`s (`plain_trace`, `pinned_trace`) are the Lean-only tactic
   `walk_stale_trace`; the scripts use the Lean-only `exec_stale_run` (the
   `execStale` twin of `WeakLeafEff8`'s `exec_eff_run`).
4. Pure facts used by the proofs: `pt_fill_ent_uwe` ↦ `WeakUpdEff.ptFillEntUwe`,
   `update_PTE_Bits_set_ad` ↦ `PtAdBits.updatePTEBitsSetAd`, `pte_set_ad_absorb` ↦
   `MachCSL.pteSetAD_pteSetAD`, `pte_set_ad_refl` ↦ the Lean-only
   `WeakWalkStale.pteSetAdRefl` (not in the Lean tree).
5. §2's three read premises and the conclusion's trace are the literal singletons
   (as in Rocq); the walk fact's `[e2] ++ ([e1] ++ [e0])` is normalised.
6. §4 (the early-return kit) is placed before §2, since `exec_stale_run` uses it.

**Rocq → Lean name map.**  `wak_excl` `wakExcl`, `ak_pins_plain` `akPinsPlain`,
`ak_pins_excl` `akPinsExcl`, `trace_pin_win_plain` `tracePinWinPlain`,
`trace_off_win_pinned` `traceOffWinPinned`, `exec_stale_pt_walk_user`
`execStalePtWalkUser`, `exec_stale_of_eff_quiet` `execStaleOfEffQuiet`,
`exec_stale_translate_TLB_miss_none` `execStaleTranslateTLBMissNone`,
`exec_stale_translate_TLB_miss_fresh` `execStaleTranslateTLBMissFresh`,
`exec_stale_translate_TLB_miss_written` `execStaleTranslateTLBMissWritten`,
`execR_stale` `execRStale`, `execR_stale_returnR` `execRStaleReturnR`,
`execR_stale_bind` `execRStaleBind`, `execR_stale_bind_None` `execRStaleBindNone`,
`execR_stale_bind_eq` `execRStaleBindEq`, `execR_stale_bind_cat` `execRStaleBindCat`,
`execR_stale_bind_nil` `execRStaleBindNil`, `execR_stale_liftR` `execRStaleLiftR`,
`execR_stale_liftR_cat` `execRStaleLiftRCat`, `execR_stale_liftR_seq`
`execRStaleLiftRSeq`, `exec_stale_catch_early_return` `execStaleCatchEarlyReturn`,
`exec_stale_translateAddr_pt_front` `execStaleTranslateAddrPtFront`,
`exec_stale_translate_miss` `execStaleTranslateMiss`,
`exec_stale_translateAddr_pt_miss_cases` `execStaleTranslateAddrPtMissCases`,
`pt_slot_mem_mpatch_disj` `ptSlotMemMpatchDisj`, `pt_slot_mem_mpatch_win`
`ptSlotMemMpatchWin`.  Lean-only (file-qualified): `WeakWalkStale.execRStaleThrow`,
`WeakWalkStale.pteSetAdRefl`; tactics `walk_stale_trace`, `exec_stale_run`.

**Dropped:** nothing -- 1 `Definition` + 1 `Fixpoint` + 24 `Lemma`s (26 Rocq
declarations), all ported (26 Lean declarations, plus the 2 Lean-only ones).
-/
import Weak.WeakUpdEff
import Weak.WeakStale

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The two kinds, and the trace side conditions they make trivial -/

/-- Rocq `wak_excl`: the CAS pair's kind (not an ifetch, latest, not synchronising). -/
def wakExcl : AkInfo := ⟨false, true, false⟩

theorem akPinsPlain : akPins wakPlain = false := rfl

theorem akPinsExcl : akPins wakExcl = true := rfl

/-- A trace of PLAIN reads has no pinned read, so `tracePinWin` is vacuous. -/
theorem tracePinWinPlain (ra : PAddr) (rn : Nat) (es : List Weff) :
    (∀ e, e ∈ es → match e with
      | .WEread ak _ _ => akPins ak = false
      | _ => True) →
    tracePinWin ra rn es := by
  intro hall ak pa n hin hpin
  have h := hall _ hin
  simp only at h
  rw [h] at hpin
  cases hpin

/-- ... and a trace with no unpinned read makes `traceOffWin` vacuous. -/
theorem traceOffWinPinned (ra : PAddr) (rn : Nat) (es : List Weff) :
    (∀ e, e ∈ es → match e with
      | .WEread ak _ _ => akPins ak = true
      | _ => True) →
    traceOffWin ra rn es := by
  intro hall ak pa n hin hnp
  have h := hall _ hin
  simp only at h
  rw [h] at hnp
  cases hnp

/-- Rocq's `plain_trace` / `pinned_trace` (Lean-only, deviation 3). -/
macro "walk_stale_trace" : tactic => `(tactic|
  ((simp only [List.singleton_append, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]) <;>
   (try and_intros) <;> (first | rfl | trivial)))

/-! ## 4. The early-return interpreter, at the stale mirror (placed before §2: the
`exec_stale_run` tactic uses its kit) -/

section StaleR
variable (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn))
variable {R X Y : Type}

/-- Rocq `execR_stale` (deviation 2): `execStale` of the `ExceptT` run, the early return
`inl`, the value `inr`, a model exception stuck. -/
def execRStale (m : SailME R X) (s : ExecSt) : Option ((R ⊕ X) × ExecSt × List Weff) :=
  match execStale ra rn w (ExceptT.run m) s with
  | some (.ok x, s', es) => some (.inr x, s', es)
  | some (.error (.inr r), s', es) => some (.inl r, s', es)
  | some (.error (.inl _), _, _) => none
  | none => none

theorem execRStaleReturnR (x : X) (s : ExecSt) :
    execRStale ra rn w (pure x : SailME R X) s = some (.inr x, s, []) := rfl

/-- An early return (Lean-only). -/
theorem WeakWalkStale.execRStaleThrow (r : R) (s : ExecSt) :
    execRStale ra rn w (SailME.throw r : SailME R X) s = some (.inl r, s, []) := rfl

theorem execRStaleBindEq (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) :
    execRStale ra rn w (m >>= f) s =
      match execRStale ra rn w m s with
      | some (.inl e, st, es) => some (.inl e, st, es)
      | some (.inr a, st, es) =>
        match execRStale ra rn w (f a) st with
        | some (y, s', es') => some (y, s', es ++ es')
        | none => none
      | none => none := by
  unfold execRStale
  rw [ExceptT.run_bind, WeakStale.execStaleBindEq]
  rcases he : execStale ra rn w (ExceptT.run m) s with _ | ⟨e | a, s1, es1⟩
  · rfl
  · rcases e with e | r0
    · rfl
    · simp only [effThen]
      show some (Sum.inl r0, s1, es1 ++ []) = _
      rw [List.append_nil]
  · simp only [effThen]
    rcases hf : execStale ra rn w (ExceptT.run (f a)) s1 with _ | ⟨e | b, s2, es2⟩
    · rfl
    · rcases e with e | r0 <;> rfl
    · rfl

theorem execRStaleBind (m : SailME R Y) (f : Y → SailME R X) :
    ∀ s r st es, execRStale ra rn w m s = some (r, st, es) →
      execRStale ra rn w (m >>= f) s =
        match r with
        | .inl e => some (.inl e, st, es)
        | .inr a =>
          match execRStale ra rn w (f a) st with
          | some (y, s', es') => some (y, s', es ++ es')
          | none => none := by
  intro s r st es hm
  rw [execRStaleBindEq, hm]
  cases r <;> rfl

theorem execRStaleBindNone (m : SailME R Y) (f : Y → SailME R X) :
    ∀ s, execRStale ra rn w m s = none → execRStale ra rn w (m >>= f) s = none := by
  intro s hm
  rw [execRStaleBindEq, hm]

theorem execRStaleBindCat (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (st : ExecSt)
    (es : List Weff) :
    execRStale ra rn w m s = some (.inr a, st, es) →
    execRStale ra rn w (m >>= f) s =
      match execRStale ra rn w (f a) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none :=
  fun h => execRStaleBind ra rn w m f s (.inr a) st es h

theorem execRStaleBindNil (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (st : ExecSt) :
    execRStale ra rn w m s = some (.inr a, st, []) →
    execRStale ra rn w (m >>= f) s = execRStale ra rn w (f a) st := by
  intro h
  rw [execRStaleBindCat ra rn w m f s a st [] h]
  rcases execRStale ra rn w (f a) st with _ | ⟨y, s', es'⟩ <;> rfl

/-- A lifted base computation never early-returns. -/
theorem execRStaleLiftR (m : SailM X) (s : ExecSt) :
    execRStale ra rn w (liftM m : SailME R X) s =
      match execStale ra rn w m s with
      | some (x, s', es) => some (.inr x, s', es)
      | none => none := by
  unfold execRStale
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e, WeakStale.execStaleBindEq]
  rcases execStale ra rn w m s with _ | ⟨x, s', es⟩
  · rfl
  · show some (Sum.inr x, s', es ++ []) = _
    rw [List.append_nil]

theorem execRStaleLiftRCat (m : SailM Y) (f : Y → SailME R X) (s st : ExecSt) (x : Y) (es : List Weff) :
    execStale ra rn w m s = some (x, st, es) →
    execRStale ra rn w (liftM m >>= f) s =
      match execRStale ra rn w (f x) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none := by
  intro hm
  apply execRStaleBindCat ra rn w _ f s x st es
  rw [execRStaleLiftR, hm]

theorem execRStaleLiftRSeq (m : SailM Y) (f : Y → SailME R X) (s st : ExecSt) (x : Y) :
    execStale ra rn w m s = some (x, st, []) →
    execRStale ra rn w (liftM m >>= f) s = execRStale ra rn w (f x) st := by
  intro hm
  apply execRStaleBindNil ra rn w _ f s x st
  rw [execRStaleLiftR, hm]

theorem execStaleCatchEarlyReturn {X : Type} (body : SailME X X) (s : ExecSt) :
    execStale ra rn w (SailME.run body) s =
      match execRStale ra rn w body s with
      | some (.inl r, s', es) => some (r, s', es)
      | some (.inr r, s', es) => some (r, s', es)
      | none => none := by
  unfold execRStale
  show execStale ra rn w (ExceptT.run body >>= _) s = _
  rw [WeakStale.execStaleBindEq]
  rcases execStale ra rn w (ExceptT.run body) s with _ | ⟨e | a, s', es⟩
  · rfl
  · rcases e with e | r
    · rfl
    · show some (r, s', es ++ []) = _
      rw [List.append_nil]
  · show some (a, s', es ++ []) = _
    rw [List.append_nil]

end StaleR

/-- The `execStale` twin of `exec_eff_run` (Lean-only, deviation 3). -/
syntax "exec_stale_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_stale_run) => `(tactic| exec_stale_run [List.nil_append])
  | `(tactic| exec_stale_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only
      [WeakStale.execStaleBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit,
      execStale, effThen, Weff.cons, execStaleReturnm, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true,
      assert, PreSail.assert, execRStaleBindEq, execRStaleLiftR, execRStaleReturnR,
      WeakWalkStale.execRStaleThrow, decide_false, decide_true, Bool.and_false, Bool.false_and,
      Bool.and_true, Bool.true_and, List.nil_append, List.append_nil, List.cons_append, $ls,*])

/-! ## 2. The walk, at the stale mirror -/

/-- The quiet transfer, used at every register-only step of the composite. -/
theorem execStaleOfEffQuiet (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X)
    (s t : ExecSt) (x : X) :
    accWf ra rn → execEff m s = some (x, t, []) → execStale ra rn w m s = some (x, t, []) := by
  intro hracc hex
  exact execStaleOfExecEff ra rn w m hracc s x t [] hex (fun _ _ _ hin => by cases hin)

/-- Rocq `exec_stale_pt_walk_user`: `execEffPtWalkUser` transferred; the three read
facts are supplied AT THE PATCHED STATE, where the leaf slot holds the racy word. -/
theorem execStalePtWalkUser (vpn : BitVec 27) (root : BitVec 44) (pte2 pte1 pv : BitVec 64)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (h2i : wpteValid pte2) (h2nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte2 7 0)) = true)
    (h1i : wpteValid pte1) (h1nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pte1 7 0)) = true)
    (h0i : wpteValid pv) (h0nl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pv 7 0)) = false)
    (hchk0 : wpteCheckOk acc p mxr dosum pv)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pv) == 1#1) = false)
    (menvcfg0 : BitVec 64) (s : ExecSt)
    (hracc : accWf (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8)
      (mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pte2, mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8)
      (mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pte1, mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9)) 8]))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8)
      (mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pv, mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execStale (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv
      (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pv
        (uGlobal pte2 pte1 pv), ()), s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) := by
  have hw := execEffPtWalkUser vpn root pte2 pte1 pv acc p mxr dosum h2i h2nl h1i h1nl h0i h0nl hchk0 h0N
    menvcfg0 _ _ _ (mpatch (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s)
    hmisa hrd2 hrd1 hrd0 hmenv hpbmte
  simp only [List.singleton_append] at hw
  refine execStaleOfPatchId _ 8 pv _ s _ _ hracc hw ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> trivial
  · apply tracePinWinPlain
    walk_stale_trace

/-! ## 3. THE MISS-PATH TRANSLATION, at the stale mirror -/

/-- Rocq `exec_stale_translate_TLB_miss_none` (A: the gate does not fire on the racy
word -- the walk fills cleanly, the CAS is never entered). -/
theorem execStaleTranslateTLBMissNone (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 pv : BitVec 64) (menvcfg0 : BitVec 64) (asid : BitVec 16)
    (s : ExecSt)
    (hracc : accWf (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8)
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid pv) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pv 7 0)) = false)
    (hchk : wpteCheckOk acc p mxr dosum pv)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pv) == 1#1) = false)
    (hnoupd : update_PTE_Bits pv acc = none)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p2, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p1, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8]))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pv, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv
      (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pv, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 pv asid))),
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) := by
  have hw := execStalePtWalkUser vpn root p2 p1 pv acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0 hchk h0N menvcfg0 s
    hracc hmisa hrd2 hrd1 hrd0 hmenv hpbmte
  have hu := execStaleOfEffQuiet _ 8 pv _ s s _ hracc
    (execEffUpdateAndWritePteNone acc p mxr dosum vpn
      (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) pv 0 s hnoupd)
  have ht := execStaleOfEffQuiet _ 8 pv _ s _ _ hracc (execEffAddToTLBUser vpn p2 p1 pv asid s)
  unfold translate_TLB_miss
  exec_stale_run
  erw [hw]
  unfold uWalkOut
  exec_stale_run
  erw [hu]
  exec_stale_run
  erw [ht]

/-- Rocq `exec_stale_translate_TLB_miss_fresh` (B: THE SIXTH OUTCOME -- the gate fires on
the racy word, the CAS re-reads a word that needs nothing: the leaf slot is read twice and
nothing is written). -/
theorem execStaleTranslateTLBMissFresh (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 pv p0 g : BitVec 64) (a1 d1 : BitVec 1)
    (menvcfg0 : BitVec 64) (asid : BitVec 16) (s : ExecSt)
    (hracc : accWf (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8)
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid pv) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pv 7 0)) = false)
    (hchk : wpteCheckOk acc p mxr dosum pv)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pv) == 1#1) = false)
    (hvar : p0 = pteSetAD pv a1 d1)
    (hfv : wpteValid p0) (hfl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p0 7 0)) = false)
    (hfchk : wpteCheckOk acc p mxr dosum p0)
    (hfN : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)
    (hgate : update_PTE_Bits pv acc = some g)
    (hnoupd : update_PTE_Bits p0 acc = none)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p2, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p1, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8]))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pv, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv
      (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pv, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 asid))),
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ++
        [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) := by
  have hw := execStalePtWalkUser vpn root p2 p1 pv acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0 hchk h0N menvcfg0 s
    hracc hmisa hrd2 hrd1 hrd0 hmenv hpbmte
  have hu := execStaleOfExecEff _ 8 pv _ hracc s _ _ _
    (execEffUpdateAndWritePteFresh acc p mxr dosum vpn (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
      pv g p0 0 (ppn0 p0) .PBMT_PMA menvcfg0 _ s hgate hmenv hadue hrdx
      (execEffCheckLeafPteLeaf0 vpn p0 acc p mxr dosum hfv hfl hfchk hfN _ menvcfg0 s hmisa hmenv hpbmte)
      hnoupd)
    (traceOffWinPinned _ _ _ (by walk_stale_trace))
  have ht := execStaleOfEffQuiet _ 8 pv _ s _ _ hracc
    (execEffAddToTLBPt asid vpn (ppn0 pv) p0
      (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) (uGlobal p2 p1 pv) s)
  unfold translate_TLB_miss
  exec_stale_run
  erw [hw]
  unfold uWalkOut
  exec_stale_run
  erw [hu]
  exec_stale_run
  erw [ht]
  rw [WeakUpdEff.ptFillEntUwe vpn p2 p1 pv p0 asid a1 d1 hvar]

/-- Rocq `exec_stale_translate_TLB_miss_written` (C: the write-back -- the gate fires on
the racy word AND the fresh one still needs bits; the value written is computed from the
FRESH word). -/
theorem execStaleTranslateTLBMissWritten (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (vpn : BitVec 27) (root : BitVec 44) (p2 p1 pv p0 p0' g : BitVec 64) (a1 d1 : BitVec 1)
    (menvcfg0 : BitVec 64) (asid : BitVec 16) (sw s : ExecSt)
    (hracc : accWf (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8)
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid pv) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pv 7 0)) = false)
    (hchk : wpteCheckOk acc p mxr dosum pv)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pv) == 1#1) = false)
    (hvar : p0 = pteSetAD pv a1 d1)
    (hfv : wpteValid p0) (hfl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p0 7 0)) = false)
    (hfchk : wpteCheckOk acc p mxr dosum p0)
    (hfN : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)
    (hgate : update_PTE_Bits pv acc = some g)
    (hupdf : update_PTE_Bits p0 acc = some p0')
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hwrite : execEff (write_pte_conditional (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)))
      8 p0') s =
      some (.Ok true, sw, [.WEwrite wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0']))
    (hswregs : sw.regs = s.regs)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p2, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p1, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8]))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pv, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv
      (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pv, .PBMT_PMA, ()),
        sw.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0' asid))),
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
         .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ++
        [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
         .WEwrite wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0']) := by
  have hw := execStalePtWalkUser vpn root p2 p1 pv acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0 hchk h0N menvcfg0 s
    hracc hmisa hrd2 hrd1 hrd0 hmenv hpbmte
  have hu := execStaleOfExecEff _ 8 pv _ hracc s _ _ _
    (execEffUpdateAndWritePteWritten acc p mxr dosum vpn (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
      pv g p0 p0' 0 (ppn0 p0) .PBMT_PMA menvcfg0 _ _ sw s hgate hmenv hadue hrdx
      (execEffCheckLeafPteLeaf0 vpn p0 acc p mxr dosum hfv hfl hfchk hfN _ menvcfg0 s hmisa hmenv hpbmte)
      hupdf hwrite)
    (traceOffWinPinned _ _ _ (by walk_stale_trace))
  have ht := execStaleOfEffQuiet _ 8 pv _ sw _ _ hracc
    (execEffAddToTLBPt asid vpn (ppn0 pv) p0'
      (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) (uGlobal p2 p1 pv) sw)
  obtain ⟨a2, d2, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupdf
  have hvar' : p0' = pteSetAD pv a2 d2 := by rw [hq, hvar]; exact pteSetAD_pteSetAD pv a1 d1 a2 d2
  unfold translate_TLB_miss
  exec_stale_run
  erw [hw]
  unfold uWalkOut
  exec_stale_run
  erw [hu]
  exec_stale_run
  erw [ht]
  rw [WeakUpdEff.ptFillEntUwe vpn p2 p1 pv p0' asid a2 d2 hvar', hswregs]

/-! ## 5. THE `translateAddr` FRONT, at the stale mirror -/

/-- Rocq `exec_stale_translateAddr_pt_front`: the front performs NO memory access, its
whole trace is the `translate`'s. -/
theorem execStaleTranslateAddrPtFront (acc : MemoryAccessType mem_payload) (p : Privilege) (la : PAddr)
    (pv : BitVec 64) (vpn : BitVec 27) (root ppnv : BitVec 44) (satp0 va pa : BitVec 64) (estr : List Weff)
    (s s' : ExecSt)
    (hracc : accWf la 8)
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits) =
      vpn)
    (htr : ∀ mxr dosum, execStale la 8 pv (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Ok (ppnv, .PBMT_PMA, ()), s', estr))
    (hident : zero_extend (m := 64) (ppnv +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa) :
    execStale la 8 pv (translateAddr (.Virtaddr va) acc) s =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), s', estr) := by
  have heff' := execStaleOfEffQuiet la 8 pv _ s s _ hracc heff
  have hss' := execStaleOfEffQuiet la 8 pv _ s s _ hracc hss
  have htm' := execStaleOfEffQuiet la 8 pv _ s s _ hracc htm
  have hw : execStale la 8 pv (satp_mode_width_forwards .Sv39) s = some (39, s, []) := rfl
  have hgs : execStale la 8 pv (get_satp 39) s = some (satp0, s, []) := by
    unfold get_satp
    exec_stale_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s, []) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [execStaleCatchEarlyReturn]
  exec_stale_run [hcp, heff', htm', hss', hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr]
  erw [hgs]
  exec_stale_run [hcanon]
  erw [hasid, hppn, hvpn, htr]
  exec_stale_run
  subst hident
  rfl

/-- Rocq `exec_stale_translate_miss`: a TLB miss is register-only, so the dispatch
transfers and the whole trace is the miss path's. -/
theorem execStaleTranslateMiss (acc : MemoryAccessType mem_payload) (p : Privilege) (la : PAddr)
    (pv : BitVec 64) (vpn : BitVec 27) (root : BitVec 44) (asid : BitVec 16) (mxr dosum : Bool)
    (r : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) (s s' : ExecSt) (es : List Weff)
    (hracc : accWf la 8)
    (hlk : execEff (lookup_TLB 39 asid vpn) s = some (none, s, []))
    (hmiss : execStale la 8 pv (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = some (r, s', es)) :
    execStale la 8 pv (translate 39 asid root vpn acc p mxr dosum ()) s = some (r, s', es) := by
  unfold translate
  rw [execStaleBindNil la 8 pv _ _ _ _ _ (execStaleOfEffQuiet la 8 pv _ s s _ hracc hlk)]
  exact hmiss

/-! ## 6. THE RACY WALK, END TO END -/

/-- The leaf word is an A/D variant of itself (Lean-only twin of `PtAdBits.pte_set_ad_refl`). -/
theorem WeakWalkStale.pteSetAdRefl (w : BitVec 64) : ∃ a d : BitVec 1, w = pteSetAD w a d := by
  refine ⟨_get_PTE_Flags_A (Sail.BitVec.extractLsb w 7 0), _get_PTE_Flags_D (Sail.BitVec.extractLsb w 7 0), ?_⟩
  simp only [pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
    BitVec.extractLsb, _update_PTE_Flags_A, _update_PTE_Flags_D, _get_PTE_Flags_A, _get_PTE_Flags_D]
  bv_decide

/-- Rocq `exec_stale_translateAddr_pt_miss_cases`: ONE `translateAddr` fact at the stale
mirror covering every outcome a TLB-miss walk can take when its plain leaf read returns a
variant `pv` of the memory's word `p0` -- three outcomes where the `execEff` statement has
two; the translated address is the SAME in all three. -/
theorem execStaleTranslateAddrPtMissCases (acc : MemoryAccessType mem_payload) (p : Privilege)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 pv p0 : BitVec 64) (a1 d1 : BitVec 1)
    (satp0 va pa menvcfg0 : BitVec 64) (s : ExecSt)
    (hracc : accWf (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8)
    -- the front
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits) =
      vpn)
    (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, []))
    (hident : zero_extend (m := 64) (ppn0 pv +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa)
    -- the walk
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid pv) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb pv 7 0)) = false)
    (hchkall : ∀ mxr dosum, wpteCheckOk acc p mxr dosum pv)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pv) == 1#1) = false)
    -- the FRESH word: an A/D variant of the racy one, and a leaf too
    (hvar : p0 = pteSetAD pv a1 d1)
    (hfv : wpteValid p0) (hfl : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p0 7 0)) = false)
    (hfchkall : ∀ mxr dosum, wpteCheckOk acc p mxr dosum p0)
    (hfN : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)
    -- the reads: the walk's at the PATCHED memory, the CAS's at the REAL one
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p2, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok p1, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8]))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8)
      (mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s) =
      some (.Ok pv, mpatch (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv s,
        [.WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))
    -- the conditional write, wherever the fresh word still needs bits
    (hwrite : ∀ p0' : BitVec 64, update_PTE_Bits p0 acc = some p0' →
      execEff (write_pte_conditional (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8 p0') s =
        some (.Ok true, s.setMem (bmWrite s.mem (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0'),
          [.WEwrite wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0']))
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true) :
    ∃ (sg' : ExecSt) (es : List Weff),
      execStale (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 pv
          (translateAddr (.Virtaddr va) acc) s =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
      sg'.dev = s.dev ∧
      -- the entry filled is always an A/D variant of the racy word
      (∃ ae de : BitVec 1,
        sg'.regs = s.regs.set .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn)
          (some (uWalkEntry vpn p2 p1 (pteSetAD pv ae de) 0#16)))) ∧
      ( -- the two READ-ONLY outcomes, each carrying the equation that DECIDED it
        (sg'.mem = s.mem ∧
          ((update_PTE_Bits pv acc = none ∧
            es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) ∨
           (update_PTE_Bits p0 acc = none ∧
            es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ++
                 [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]))) ∨
        -- the write-back
        (∃ p0' : BitVec 64,
          update_PTE_Bits p0 acc = some p0' ∧
          sg'.mem = bmWrite s.mem (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0' ∧
          es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ++
               [.WEread wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                .WEwrite wakExcl (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8 p0'])) := by
  -- the gate is decided by the RACY word, the write by the FRESH one
  rcases hgate : update_PTE_Bits pv acc with _ | g
  · -- O-UNCHANGED: the gate does not fire on the racy word
    obtain ⟨ar, dr, hself⟩ := WeakWalkStale.pteSetAdRefl pv
    refine ⟨_, _, execStaleTranslateAddrPtFront acc p _ pv vpn root (ppn0 pv) satp0 va pa _ s _ hracc heff hss
      hcp htm hsatp hppn hasid hcanon hvpn (fun mxr dosum => execStaleTranslateMiss acc p _ pv vpn root 0#16
        mxr dosum _ s _ _ hracc hlk (execStaleTranslateTLBMissNone acc p mxr dosum vpn root p2 p1 pv menvcfg0
          0#16 s hracc hv2 hn2 hv1 hn1 hv0 hl0 (hchkall mxr dosum) h0N hgate hmisa hrd2 hrd1 hrd0 hmenv
          hpbmte)) hident, rfl, ⟨ar, dr, ?_⟩, .inl ⟨rfl, .inl ⟨rfl, rfl⟩⟩⟩
    rw [← hself]; rfl
  · rcases hupdf : update_PTE_Bits p0 acc with _ | p0'
    · -- O-FRESH -- the sixth outcome
      refine ⟨_, _, execStaleTranslateAddrPtFront acc p _ pv vpn root (ppn0 pv) satp0 va pa _ s _ hracc heff
        hss hcp htm hsatp hppn hasid hcanon hvpn (fun mxr dosum => execStaleTranslateMiss acc p _ pv vpn root
          0#16 mxr dosum _ s _ _ hracc hlk (execStaleTranslateTLBMissFresh acc p mxr dosum vpn root p2 p1 pv p0
            g a1 d1 menvcfg0 0#16 s hracc hv2 hn2 hv1 hn1 hv0 hl0 (hchkall mxr dosum) h0N hvar hfv hfl
            (hfchkall mxr dosum) hfN hgate hupdf hadue hrdx hmisa hrd2 hrd1 hrd0 hmenv hpbmte)) hident,
        rfl, ⟨a1, d1, ?_⟩, .inl ⟨rfl, .inr ⟨rfl, rfl⟩⟩⟩
      rw [← hvar]; rfl
    · -- O-WRITTEN
      obtain ⟨a2, d2, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupdf
      have hvar' : p0' = pteSetAD pv a2 d2 := by rw [hq, hvar]; exact pteSetAD_pteSetAD pv a1 d1 a2 d2
      refine ⟨_, _, execStaleTranslateAddrPtFront acc p _ pv vpn root (ppn0 pv) satp0 va pa _ s _ hracc heff
        hss hcp htm hsatp hppn hasid hcanon hvpn (fun mxr dosum => execStaleTranslateMiss acc p _ pv vpn root
          0#16 mxr dosum _ s _ _ hracc hlk (execStaleTranslateTLBMissWritten acc p mxr dosum vpn root p2 p1 pv
            p0 p0' g a1 d1 menvcfg0 0#16 _ s hracc hv2 hn2 hv1 hn1 hv0 hl0 (hchkall mxr dosum) h0N hvar hfv hfl
            (hfchkall mxr dosum) hfN hgate hupdf hadue hrdx (hwrite p0' hupdf) rfl hmisa hrd2 hrd1 hrd0 hmenv
            hpbmte)) hident,
        rfl, ⟨a2, d2, ?_⟩, .inr ⟨p0', rfl, rfl, rfl⟩⟩
      rw [← hvar']; rfl

/-! ## 7. The slot facts at the patched state -/

/-- Rocq `pt_slot_mem_mpatch_disj`: a slot disjoint from the window survives the patch. -/
theorem ptSlotMemMpatchDisj (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (s : ExecSt) (a v : BitVec 64) :
    accWf ra rn → accWf a 8 → raccDisj ra rn a 8 →
    WeakWalkEff.ptSlotMem s a v → WeakWalkEff.ptSlotMem (mpatch ra rn w s) a v := by
  intro hracc hacc hdisj ⟨hbytes, hram, hal⟩
  refine ⟨fun j hj => ?_, hram, hal⟩
  show bmWrite s.mem ra rn w (a + BitVec.ofNat 64 j) = _
  rw [writeBytesLookupNe s.mem ra rn w _ (fun i hi => paAddNeq a ra 8 rn j i hacc hracc hdisj hj hi)]
  exact hbytes j hj

/-- Rocq `pt_slot_mem_mpatch_win`: the LEAF slot holds the racy word after the patch. -/
theorem ptSlotMemMpatchWin (la : PAddr) (pv : BitVec 64) (s : ExecSt) (v : BitVec 64) :
    accWf la 8 → WeakWalkEff.ptSlotMem s la v → WeakWalkEff.ptSlotMem (mpatch la 8 pv s) la pv := by
  intro hracc ⟨_, hram, hal⟩
  exact ⟨fun j hj => writeBytesLookupAt s.mem la 8 pv j hracc hj, hram, hal⟩

end Weak
