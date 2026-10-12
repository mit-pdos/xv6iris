/-
Weak: **the SYMBOLIC `wpd` instruction engine** (owner decision D1): ONE bridge "pure execution
certificate ⇒ `wpd` step", generic over the monad tree, the pc and the control state — no
concrete ledgers.

Rocq: `iris/AxSymEngine.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `EvA img QE Q m t` — the certificate.  An INDUCTIVE, all-paths, big-step predicate on Sail
trees: register reads answer from `t` EXCEPT the PLIC pins, whose read must succeed for EVERY
answer (the wire may flip them at any time); register writes update `t` (never a pin); a plain
RAM read answers from the fixed IMAGE `img` (text / page-table image, D3); the silent outcomes
pass; every other node (memory write, barrier, `choose`, MMIO, the legacy RAM events) is NOT
covered; a failure node `.impure (.error e)` is covered by `QE`.  It is a weakest precondition
over trees with the kit `EvABind`, `EvAMono`, `EvATryCatch`, `EvALiftR`, `EvACatchEarlyReturn`.
§2 THE BRIDGE `wpdOfEvA`: an `EvA` certificate of the thread's tree at ANY state agreeing off the
pins with the thread's registers gives its `wpd`, with continuation at every `.pure ()` reached
(any row position).  Per node: `wpdAdminNode` (one closed step via `AxWpdLift.wpdOfClosedRun`;
wire flips stay in the class) and `wpdMreadNode` (an image read).  `wpdRetNode`: the instruction
boundary (both ticks).  `wpdInstrOfEvA`: from a `.pure ()` boundary, ∀ tick certificates.
PREMISES (section context of §2, instance-level, instruction-free): `Hend` every `postLifting Φ`
is free; `Htext` the graph's reads of image bytes read the image (`textFixed`); `Hflow` the
read-annotation deposit at image reads, uniformly in the row position.

## Deviations from Rocq

1. O2 STAGE C (fetch = pinned admin step; `AxCjrWpd` deviation 1).  Rocq's `ev_mrd` covers a
   plain (`ak_coh = false`) RAM read, which in Rocq is also how the model fetches; every such
   read consumed one row item.  In Lean an `akIfetch` read is the pinned admin step `LIFetch` at
   the SAME row position, and the other plain reads (data, page-table walk) are graph reads.  So
   `EvA.evMrd` DROPS Rocq's `ak_coh = false` premise (it covers both kinds; Lean `akIfetch` is
   Rocq `ak_coh` renamed), and `wpdMreadNode` continues at `AxSymEngine.rdNext req k` (`k` for a
   fetch, `k + 1` for a graph read; Rocq `S k`).  The two halves are the Lean-only
   `AxSymEngine.wpdImgFetch` (continuation owed for the IMAGE bytes only: the step clause offers
   only fetches pinned to the boot image, `AxCjrWpd.pinnedBytes`, fed by `textFixed`'s first
   conjunct) and `AxSymEngine.wpdImgRead` (Rocq's clause (a) verbatim).  Rocq's clause (b)
   (`AStepFetch`, the image oracle) is gone: a non-fetch read node has no program step.
   Consequently Rocq's section premise `Hloc` (the local-interp advance at a fetch) is unused and
   DROPPED.
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`sig_seip` or
   `sig_meip`) in `EvA.evRd`/`evWr` and every `regs_agree`.
3. Q7 (sfence marker, `WeakEvExecEff` Q7): `EvA.evIa` takes `sfAnnB n w = false` — an
   SFENCE.VMA announce is a graph event (`LFence false false false false`), not a silent node.
4. LEAN-SAIL OUTCOMES: Rocq's extra-outcome type `E` (exceptions, early returns) ↦ lean-sail's
   failure node `.impure (.error e)` with `e : Sail.Error exception`, covered by `QE`
   (`EvA.evExt`).  `EvA` is stated on `SailM X`; the early-return monad `SailME R X` is
   `ExceptT (Sail.Error exception ⊕ R) SailM X`, so its early returns and model exceptions are
   RESULT values: `EvALiftR` states `liftM m` (result `.ok x`; `.error _` excluded), and
   `EvACatchEarlyReturn` takes the certificate of `ExceptT.run m` with
   `.ok x`/`.error (.inr x)` ↦ `Q x`, `.error (.inl e)` ↦ `QE e` (the `throw e` that
   `SailME.run` turns it into).  `Defs.try_catch` ↦ `PreSail.tryCatchAll` (`EvATryCatch`, `QE`
   over one error type); Lean-only `AxSymEngine.evASailTryCatch` is the model's own
   `sailTryCatch` (catches `.User` only).  `ev_gcc` answers `(0 : Nat)`.  Lean-sail's `choose`,
   `readRam`/`writeRam` are not covered (as Rocq's `Choose`).
5. TYPES: `Z → option (bv 8)` ↦ `Image`, `mstate` ↦ `ExecSt` (`sregs` ↦ `regs`), `set_reg` ↦
   `ExecSt.setReg`, `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`,
   `seq 0 n` ↦ `List.range n`, `N.to_nat n` ↦ `n : Nat`, `inl (w, None)` ↦ `.Ok (w, none)`,
   `Interface.Ret tt` ↦ `.pure ()`, `ib_none` ↦ `ibNone`, `MState rs ∅ dev0_state` ↦
   `⟨rs, fun _ => none, testDevs⟩`; `WPd s @ MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`); `A -∗ B` ↦ `⊢ A -∗ B`.
   `pstepRdInv` returns the `ibRd` bits; `pstepWrInv` the `rs.set` file.
6. Lean-only helpers (file-qualified): `AxSymEngine.mapMSome` (`mapM_Some_1` + `Forall2`),
   `AxSymEngine.rdNext`, `AxSymEngine.wpdImgFetch`, `AxSymEngine.wpdImgRead`,
   `AxSymEngine.silentPs` / `AxSymEngine.wpdSilentNode` (the Rocq `silent_ps` tactic, as lemmas),
   `AxSymEngine.evASailTryCatch`.

**Rocq → Lean name map.**  `img_bytes` `imgBytes`, `img_bytes_spec` `imgBytesSpec`, `EvA` `EvA`
(constructors `ev_ret` `evRet`, `ev_rd` `evRd`, `ev_wr` `evWr`, `ev_mrd` `evMrd`, `ev_ia` `evIa`,
`ev_ba` `evBa`, `ev_co` `evCo`, `ev_tl` `evTl`, `ev_te` `evTe`, `ev_rx` `evRx`, `ev_ts` `evTs`,
`ev_tx` `evTx`, `ev_cc` `evCc`, `ev_msg` `evMsg`, `ev_gcc` `evGcc`, `ev_ext` `evExt`), `EvA_mono`
`EvAMono`, `EvA_bind` `EvABind`, `EvA_bind0` `EvABind0`, `EvA_ret` `EvARet`, `EvA_read_reg`
`EvAReadReg`, `EvA_write_reg` `EvAWriteReg`, `EvA_try_catch` `EvATryCatch`, `EvA_liftR`
`EvALiftR`, `EvA_catch_early_return` `EvACatchEarlyReturn`, `text_fixed` `textFixed`,
`pstep_rd_inv` `pstepRdInv`, `pstep_wr_inv` `pstepWrInv`, `wpd_admin_node` `wpdAdminNode`,
`wpd_mread_node` `wpdMreadNode`, `wpd_of_EvA` `wpdOfEvA`, `wpd_ret_node` `wpdRetNode`,
`wpd_instr_of_EvA` `wpdInstrOfEvA`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 20 definitions/lemmas + the `silent_ps` tactic; Lean 20 + 7 Lean-only).
**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiChainSdLd
import Weak.AxLdspWpd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The certificate `EvA` -/

def imgBytes (img : Image) (base : Int) (n : Nat) : Option (List (BitVec 8)) :=
  (List.range n).mapM (fun j : Nat => img (base + j))

/-- (Lean-only) A successful `mapM` in `Option`: lengths agree, entries are the images. -/
theorem AxSymEngine.mapMSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (vs : List β), l.mapM f = some vs →
      vs.length = l.length ∧ ∀ (j : Nat) (hj : j < l.length), f l[j] = vs[j]?
  | [], vs, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := AxSymEngine.mapMSome f l bs hl
        refine ⟨by simp [hlen], ?_⟩
        intro j hj
        cases j with
        | zero => simpa using hfa
        | succ j =>
          simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
          exact hall j (by simp at hj; omega)

theorem imgBytesSpec (img : Image) (base : Int) (n : Nat) (vs : List (BitVec 8)) :
    imgBytes img base n = some vs →
    vs.length = n ∧ ∀ j : Nat, j < n → img (base + j) = vs[j]? := by
  intro h
  obtain ⟨hlen, hall⟩ := AxSymEngine.mapMSome _ _ vs h
  rw [List.length_range] at hlen
  refine ⟨hlen, fun j hj => ?_⟩
  have := hall j (by rw [List.length_range]; exact hj)
  rw [List.getElem_range] at this
  exact this

/-- THE CERTIFICATE (see the header). -/
inductive EvA (img : Image) {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) : SailM X → ExecSt → Prop where
  | evRet (x : X) (t : ExecSt) : Q x t → EvA img QE Q (.pure x) t
  | evRd (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, EvA img QE Q (k v) t) →
      (¬ AxRunClose.pinReg r → EvA img QE Q (k (t.regs r)) t) →
      EvA img QE Q (.impure (.ok (.regRead r)) k) t
  | evWr (r : Register) (v : RegisterType r) (k : PUnit → SailM X) (t : ExecSt) :
      ¬ AxRunClose.pinReg r → EvA img QE Q (k PUnit.unit) (t.setReg r v) →
      EvA img QE Q (.impure (.ok (.regWrite r v)) k) t
  | evMrd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      imgBytes img (paZ req.pa) n = some vs →
      EvA img QE Q (k (.Ok (wordOfBytes n vs, none))) t →
      EvA img QE Q (.impure (.ok (.memRead n va req)) k) t
  | evIa (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = false → EvA img QE Q (k ()) t →
      EvA img QE Q (.impure (.ok (.instrAnnounce n w)) k) t
  | evBa (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.branchAnnounce n a)) k) t
  | evCo (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.cacheOp c)) k) t
  | evTl (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.tlbi c)) k) t
  | evTe (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.takeException f)) k) t
  | evRx (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.returnException a)) k) t
  | evTs (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.translationStart a)) k) t
  | evTx (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.translationEnd a)) k) t
  | evCc (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok .cycleCount) k) t
  | evMsg (a : String) (k : Unit → SailM X) (t : ExecSt) :
      EvA img QE Q (k ()) t → EvA img QE Q (.impure (.ok (.message a)) k) t
  | evGcc (k : Nat → SailM X) (t : ExecSt) :
      EvA img QE Q (k (0 : Nat)) t → EvA img QE Q (.impure (.ok .getCycleCount) k) t
  | evExt (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt) :
      QE e t → EvA img QE Q (.impure (.error e) k) t

section eva
variable (img : Image)

theorem EvAMono {X : Type} (QE QE' : Sail.Error exception → ExecSt → Prop)
    (Q Q' : X → ExecSt → Prop) (m : SailM X) (t : ExecSt) :
    (∀ e t', QE e t' → QE' e t') → (∀ x t', Q x t' → Q' x t') →
    EvA img QE Q m t → EvA img QE' Q' m t := by
  intro HE HQ h
  induction h with
  | evRet x t h => exact .evRet x t (HQ x t h)
  | evExt e k t h => exact .evExt e k t (HE e t h)
  | evRd r k t _ _ ihs ihn => exact .evRd r k t ihs ihn
  | evWr r v k t hr _ ih => exact .evWr r v k t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih => exact .evMrd n va req k t vs h1 h2 h3 ih
  | evIa n w k t hs _ ih => exact .evIa n w k t hs ih
  | evBa n a k t _ ih => exact .evBa n a k t ih
  | evCo c k t _ ih => exact .evCo c k t ih
  | evTl c k t _ ih => exact .evTl c k t ih
  | evTe f k t _ ih => exact .evTe f k t ih
  | evRx a k t _ ih => exact .evRx a k t ih
  | evTs a k t _ ih => exact .evTs a k t ih
  | evTx a k t _ ih => exact .evTx a k t ih
  | evCc k t _ ih => exact .evCc k t ih
  | evMsg a k t _ ih => exact .evMsg a k t ih
  | evGcc k t _ ih => exact .evGcc k t ih

theorem EvABind {X Y : Type} (QE : Sail.Error exception → ExecSt → Prop) (Q : Y → ExecSt → Prop)
    (m : SailM X) (f : X → SailM Y) (t : ExecSt) :
    EvA img QE (fun x t' => EvA img QE Q (f x) t') m t → EvA img QE Q (m >>= f) t := by
  intro h
  induction h with
  | evRet x t h => exact h
  | evExt e k t h => exact .evExt e _ t h
  | evRd r k t _ _ ihs ihn => exact .evRd r _ t ihs ihn
  | evWr r v k t hr _ ih => exact .evWr r v _ t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih => exact .evMrd n va req _ t vs h1 h2 h3 ih
  | evIa n w k t hs _ ih => exact .evIa n w _ t hs ih
  | evBa n a k t _ ih => exact .evBa n a _ t ih
  | evCo c k t _ ih => exact .evCo c _ t ih
  | evTl c k t _ ih => exact .evTl c _ t ih
  | evTe f k t _ ih => exact .evTe f _ t ih
  | evRx a k t _ ih => exact .evRx a _ t ih
  | evTs a k t _ ih => exact .evTs a _ t ih
  | evTx a k t _ ih => exact .evTx a _ t ih
  | evCc k t _ ih => exact .evCc _ t ih
  | evMsg a k t _ ih => exact .evMsg a _ t ih
  | evGcc k t _ ih => exact .evGcc _ t ih

theorem EvABind0 {Y : Type} (QE : Sail.Error exception → ExecSt → Prop) (Q : Y → ExecSt → Prop)
    (m : SailM Unit) (n : SailM Y) (t : ExecSt) :
    EvA img QE (fun _ t' => EvA img QE Q n t') m t → EvA img QE Q (m >>= fun _ => n) t :=
  EvABind img QE Q m (fun _ => n) t

theorem EvARet {X : Type} (QE : Sail.Error exception → ExecSt → Prop) (Q : X → ExecSt → Prop)
    (x : X) (t : ExecSt) : Q x t → EvA img QE Q (pure x : SailM X) t :=
  fun h => .evRet x t h

theorem EvAReadReg (QE : Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : RegisterType r → ExecSt → Prop) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q (t.regs r) t → EvA img QE Q (readReg r : SailM _) t :=
  fun hr hq => .evRd r _ t (fun h => absurd h hr) (fun _ => .evRet _ t hq)

theorem EvAWriteReg (QE : Sail.Error exception → ExecSt → Prop) (Q : PUnit → ExecSt → Prop)
    (r : Register) (v : RegisterType r) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q PUnit.unit (t.setReg r v) →
    EvA img QE Q (writeReg r v : SailM _) t :=
  fun hr hq => .evWr r v _ t hr (.evRet _ _ hq)

theorem EvATryCatch {X : Type} (QE1 QE2 : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X) (t : ExecSt) :
    (∀ e t', QE1 e t' → EvA img QE2 Q (h e) t') →
    EvA img QE1 Q m t → EvA img QE2 Q (PreSail.tryCatchAll m h) t := by
  intro Hh H
  induction H with
  | evRet x t h => exact .evRet x t h
  | evExt e k t he => exact Hh e t he
  | evRd r k t _ _ ihs ihn => exact .evRd r _ t ihs ihn
  | evWr r v k t hr _ ih => exact .evWr r v _ t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih => exact .evMrd n va req _ t vs h1 h2 h3 ih
  | evIa n w k t hs _ ih => exact .evIa n w _ t hs ih
  | evBa n a k t _ ih => exact .evBa n a _ t ih
  | evCo c k t _ ih => exact .evCo c _ t ih
  | evTl c k t _ ih => exact .evTl c _ t ih
  | evTe f k t _ ih => exact .evTe f _ t ih
  | evRx a k t _ ih => exact .evRx a _ t ih
  | evTs a k t _ ih => exact .evTs a _ t ih
  | evTx a k t _ ih => exact .evTx a _ t ih
  | evCc k t _ ih => exact .evCc _ t ih
  | evMsg a k t _ ih => exact .evMsg a _ t ih
  | evGcc k t _ ih => exact .evGcc _ t ih

/-- (Lean-only, deviation 4) The model's own `try … catch`: only user exceptions reach the
handler; any other failure stays a failure node. -/
theorem AxSymEngine.evASailTryCatch {X : Type} (QE1 QE2 : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailM X) (h : exception → SailM X) (t : ExecSt) :
    (∀ e t', QE1 e t' →
      match e with
      | .User u => EvA img QE2 Q (h u) t'
      | e => QE2 e t') →
    EvA img QE1 Q m t → EvA img QE2 Q (PreSail.sailTryCatch m h) t := by
  intro Hh H
  induction H with
  | evRet x t h => exact .evRet x t h
  | evExt e k t he =>
    have H2 := Hh e t he
    cases e <;> first | exact H2 | exact .evExt _ _ t H2
  | evRd r k t _ _ ihs ihn => exact .evRd r _ t ihs ihn
  | evWr r v k t hr _ ih => exact .evWr r v _ t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih => exact .evMrd n va req _ t vs h1 h2 h3 ih
  | evIa n w k t hs _ ih => exact .evIa n w _ t hs ih
  | evBa n a k t _ ih => exact .evBa n a _ t ih
  | evCo c k t _ ih => exact .evCo c _ t ih
  | evTl c k t _ ih => exact .evTl c _ t ih
  | evTe f k t _ ih => exact .evTe f _ t ih
  | evRx a k t _ ih => exact .evRx a _ t ih
  | evTs a k t _ ih => exact .evTs a _ t ih
  | evTx a k t _ ih => exact .evTx a _ t ih
  | evCc k t _ ih => exact .evCc _ t ih
  | evMsg a k t _ ih => exact .evMsg a _ t ih
  | evGcc k t _ ih => exact .evGcc _ t ih

theorem EvALiftR {R X : Type} (QE : Sail.Error exception → ExecSt → Prop) (Q : X → ExecSt → Prop)
    (m : SailM X) (t : ExecSt) :
    EvA img QE Q m t →
    EvA img QE
      (fun (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q x t'
        | .error _ => False)
      (ExceptT.run (liftM m : SailME R X)) t := by
  intro H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply EvABind
  exact EvAMono img QE QE Q _ m t (fun _ _ h => h) (fun x t' h => .evRet _ t' h) H

theorem EvACatchEarlyReturn {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailME X X) (t : ExecSt) :
    EvA img QE
      (fun (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q x t'
        | .error (.inr x) => Q x t'
        | .error (.inl e) => QE e t')
      (ExceptT.run m) t →
    EvA img QE Q (SailME.run m) t := by
  intro H
  show EvA img QE Q (ExceptT.run m >>= _) t
  apply EvABind
  refine EvAMono img QE QE _ _ _ t (fun _ _ h => h) ?_ H
  intro r t' hr
  rcases r with (e | x) | x
  · exact .evExt e _ t' hr
  · exact .evRet x t' hr
  · exact .evRet x t' hr

end eva

/-! # 2. THE BRIDGE: `EvA` ⇒ `wpd` -/

/-- The graph fixes the image: every row read of image bytes is a plain read of the image value
(text immutable, page tables immutable — D3). -/
def textFixed (GD : Gdexec) (i : Agent) (img : Image) : Prop :=
  (∀ a b, img a = some b → GD.gdG.gxImg a = some b) ∧
  ∀ k lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb →
    aidentRd (aident lb) = some (aq, base, n) → imgBytes img base n = some vs →
    aident lb = .IRead aq base n ∧ graphValue GD (i, k) = some vs

theorem pstepRdInv (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (.impure (.ok (.regRead r)) k) rs none ib) d l p' d' →
    l = .LSilent ∧ p' = .PHart cpu (k (rs r)) rs none (ibRd ib r) := by
  cases p' with
  | PDisk _ => intro h; exact h.elim
  | PHart c' m' rs' fn' ib' =>
    rintro ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨rfl, rfl⟩

theorem pstepWrInv (cpu : CPU) (r : Register) (v : RegisterType r) (k : PUnit → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (.impure (.ok (.regWrite r v)) k) rs none ib) d l p' d' →
    AxOpsem.lbAdminAx true l ∧ p' = .PHart cpu (k PUnit.unit) (rs.set r v) none ib := by
  cases p' with
  | PDisk _ => intro h; exact h.elim
  | PHart c' m' rs' fn' ib' =>
    rintro ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨AxCjrWpd.erwLabelAdmin _, rfl⟩

/-- (Lean-only) Rocq's `silent_ps`: a node whose every `pnodeStep` is admin, lands at `m1` and
writes no register steps (in the program half) to `m1` at the same registers. -/
theorem AxSymEngine.silentPs (cpu : CPU) (m m1 : SailM Unit)
    (H : ∀ rs ib d l m' ors fn' d' oib obar, pnodeStep m rs ib d l m' ors fn' d' oib obar →
      AxOpsem.lbAdminAx true l ∧ m' = m1 ∧ ors = none ∧ fn' = none) :
    ∀ rs ib d l p' d', pstepProg (.PHart cpu m rs none ib) d l p' d' →
      AxOpsem.lbAdminAx true l ∧ ∃ ib1, p' = .PHart cpu m1 rs none ib1 := by
  intro rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact h.elim
  | PHart c' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    obtain ⟨hadm, rfl, rfl, rfl⟩ := H _ _ _ _ _ _ _ _ _ _ hn
    exact ⟨hadm, _, rfl⟩

section bridge
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (Hend : ∀ s, ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hend in
/-- ONE administrative node: every program step from the class `A` of register files is admin,
lands in `N`; the wire keeps the class. -/
theorem wpdAdminNode (m : SailM Unit) (kk : Nat) (A : RegFile → Prop) (N : Athread → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hps : ∀ rs ib d l p' d', A rs → pstepProg (.PHart cpu m rs none ib) d l p' d' →
       AxOpsem.lbAdminAx true l ∧ N ⟨p', kk⟩) :
    ∀ rs ib, A rs →
    ⊢ (∀ s2, ⌜N s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro rs ib HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1, s = ⟨.PHart cpu m rs1 none ib1, kk⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K ⟨rs1, ib1, rfl, HA1⟩ ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨l, d, d', Hl, -, Hp, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨Had, -⟩ := Hps _ _ _ _ _ _ HA1 Hp
    rw [← Hl, lbAdminRd l Had] at Hrd
    cases Hrd
  have Hclos : ∀ GD s1 l s2, P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ N s2) := by
    rintro GD s1 l s2 ⟨rs1, ib1, rfl, HA1⟩ Hst
    obtain ⟨d, d', Hp⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨Had, HN⟩ := Hps _ _ _ _ _ _ HA1 Hp
    have Hk := astepProgAdminK' _ _ _ _ Hst Had
    refine ⟨AxRunClose.lbAdminWdata l Had, Hk, .inr ?_⟩
    obtain ⟨p2, k2⟩ := s2
    simp only at Hk
    subst Hk
    exact HN
  have Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ N s2 := by
    rintro s1 s2 ⟨rs1, ib1, rfl, HA1⟩ Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p2, k2⟩ := s2
    simp only at hk hp
    subst hk
    cases p2 with
    | PDisk _ => exact hp.elim
    | PHart c m2 rs2 fn2 ib2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      exact .inl ⟨rs2, ib2, rfl, HA rs1 rs2 HA1 hag⟩
  iintro C
  iapply (wpdOfClosedRun .MaybeStuck i P N Φ
    (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2) Hnord Hclos Hwire) $$
    %⟨.PHart cpu m rs none ib, kk⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iexact C
  · iintro %GD %s1 %_ %_
    iapply (Hend s1)

/-- (Lean-only) Where an image read continues: a fetch keeps the row position, a graph read
consumes one row item (deviation 1). -/
def AxSymEngine.rdNext {n va : Nat} (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Nat) : Nat :=
  if (classify req.access_kind).akIfetch then k else k + 1

include Hend Htext in
/-- (Lean-only, deviation 1) An image FETCH: the pinned admin step, at the same position; the
continuation is owed for the image's bytes only. -/
theorem AxSymEngine.wpdImgFetch (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  obtain ⟨Hlen, Himgj⟩ := imgBytesSpec img _ n vs Hvs
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Htext GD Hc) $$ Hg
  icases Hok with %Hok
  have Himg : ∀ j : Nat, j < vs.length → GD.gdG.gxImg (paZ req.pa + j) = vs[j]? := by
    intro j hj
    have h1 := Himgj j (by omega)
    rw [List.getElem?_eq_getElem hj] at h1 ⊢
    exact Hok.1 _ _ h1
  isplit
  · iintro %id %K %Hst
    exact (AxCjrWpd.fetchNoRead _ cpu n va req KK rs ib k id K Hdev Hfe Hst).elim
  isplit
  · iintro %l %s' %Hst %Hpin
    obtain ⟨tvs, hlen, rfl, rfl⟩ := AxCjrWpd.fetchAstepInv _ cpu n va req KK rs ib k l s' Hdev Hfe Hst
    rw [AxCjrWpd.pinnedBytes _ _ tvs vs (by omega) Himg Hpin]
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply C $$ %rs %HP
  isplit
  · iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · iintro %_
    iapply (Hend _)

include Hend Htext Hflow in
/-- (Lean-only, deviation 1) An image GRAPH READ (Rocq's clause (a)): `textFixed` pins the row
identity and the graph value to the image bytes at WHATEVER row item the thread is at. -/
theorem AxSymEngine.wpdImgRead (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Htext GD Hc) $$ Hg
  icases Hok with %Hok
  isplit
  · -- (a) THE READ
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
    simp only [wlRd, Htl0] at Hl0
    obtain ⟨Hidlb, Hgv⟩ := Hok.2 k lb _ _ _ vs Hlb Hl0.symm Hvs
    have Hadv0 : aidentAdvRd (aident lb) = 1 := by rw [Hidlb]; rfl
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d _ _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    have hvs : tvs.map Prod.snd = vs := by
      rw [Hgv] at Hv
      exact (Option.some.inj Hv).symm
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk', hvs]
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := (BI.wand_intro (Hflow GD ls k Hc ⟨lb, _, _, _, vs, Hlb, Hidlb, Hvs⟩)) $$ Hg Hloc
    unfold fetchFlow
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %rs %HP
  isplit
  · -- (b) no program step exists at a plain read node
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire: back to the read node, Löb
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · -- (d) row end
    iintro %_
    iapply (Hend _)

include Hend Htext Hflow in
/-- A plain RAM read of image bytes (deviation 1: a fetch at `k`, a graph read to `k + 1`). -/
theorem wpdMreadNode (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib,
           AxSymEngine.rdNext req k⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  cases hfe : (classify req.access_kind).akIfetch with
  | true =>
    have e : AxSymEngine.rdNext req k = k := by simp only [AxSymEngine.rdNext, hfe, ↓reduceIte]
    rw [e]
    exact AxSymEngine.wpdImgFetch img i Φ cpu Hend Htext n va req KK ib k vs A HA Hdev hfe Hvs
  | false =>
    have e : AxSymEngine.rdNext req k = k + 1 := by
      simp only [AxSymEngine.rdNext, hfe, Bool.false_eq_true, ↓reduceIte]
    rw [e]
    exact AxSymEngine.wpdImgRead img i Φ cpu Hend Htext Hflow n va req KK ib k vs A HA Hdev Hlat
      hfe Hvs

include Hend in
/-- (Lean-only) A silent node (Rocq's `silent_ps` arm of `wpd_of_EvA`), through `wpdAdminNode`
over the agreement class of a state `t`. -/
theorem AxSymEngine.wpdSilentNode (m m1 : SailM Unit) (kk : Nat) (t : ExecSt)
    (H : ∀ rs ib d l m' ors fn' d' oib obar, pnodeStep m rs ib d l m' ors fn' d' oib obar →
      AxOpsem.lbAdminAx true l ∧ m' = m1 ∧ ors = none ∧ fn' = none) :
    ∀ rs ib, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ (∀ rs1 ib1, ⌜regsAgree AxRunClose.pinReg rs1 t.regs⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu m1 rs1 none ib1, kk⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro rs ib Hag
  iintro C
  iapply (wpdAdminNode i Φ cpu Hend m kk (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
    (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu m1 rs1 none ib1, kk⟩ ∧
      regsAgree AxRunClose.pinReg rs1 t.regs)
    (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
  · intro rs1 ib1 d l p' d' HA1 Hp
    obtain ⟨Had, ib2, rfl⟩ := AxSymEngine.silentPs cpu m m1 H rs1 ib1 d l p' d' Hp
    exact ⟨Had, rs1, ib2, rfl, HA1⟩
  · iintro %s2 %HN
    obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
    iapply C $$ %rs1 %ib1 %HA1

include Hend Htext Hflow in
/-- THE BRIDGE. -/
theorem wpdOfEvA (Q : Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) :
    EvA img (fun _ _ => False) Q m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | evRet x t HQ =>
    intro rs ib kk Hag
    iintro C
    iapply C $$ %t %rs %ib %kk %HQ %Hag
  | evExt e k t he => exact he.elim
  | evRd r k t _ _ IHs IHn =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdAdminNode i Φ cpu Hend _ kk (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1) $$ C
      · have h := IHn Hs rs1 ib1 kk HA1
        rw [← HA1 r Hs] at h
        iapply h $$ C
  | evWr r v k t Hr _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdAdminNode i Φ cpu Hend _ kk (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1)) $$ C
  | evMrd n va req k t vs Hdev Hlat Hvs _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdMreadNode img i Φ cpu Hend Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib _ HA') $$ C
  | evIa n w k t Hsf _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (AxSymEngine.wpdSilentNode i Φ cpu Hend _ (k ()) kk t ?_ rs ib Hag)
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ C
  | evBa _ _ k t _ IH | evCo _ k t _ IH | evTl _ k t _ IH | evTe _ k t _ IH | evRx _ k t _ IH
  | evTs _ k t _ IH | evTx _ k t _ IH | evCc k t _ IH | evMsg _ k t _ IH | evGcc k t _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (AxSymEngine.wpdSilentNode i Φ cpu Hend _ _ kk t ?_ rs ib Hag)
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ C

include Hend in
/-- The instruction boundary: from `.pure ()` (up to `aeqv`) the only steps are the two ticks;
the row end is `Hend`. -/
theorem wpdRetNode (rs : RegFile) (k : Nat) (s : Athread) (Hs : RetX cpu rs k s) :
    ⊢ (∀ s2, ⌜RetNext cpu rs k s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗
      wpd .MaybeStuck i s Φ := by
  have Hnord : ∀ GD s1 id K, RetX cpu rs k s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K HP ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s1 HP
    obtain ⟨l, d, d', Hl, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    rw [← Hl] at Hrd
    simp [wlRd] at Hrd
  have Hclos : ∀ GD s1 l s2, RetX cpu rs k s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (RetX cpu rs k s2 ∨ RetNext cpu rs k s2) := by
    rintro GD s1 l s2 HP Hst
    obtain ⟨rs1, ib1, rfl, Hag⟩ := retxShape cpu rs k s1 HP
    obtain ⟨d, d', Hps⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨tick, rfl⟩ := astepProgRetShape _ cpu rs1 ib1 k l s2 Hst
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    exact ⟨rfl, rfl, .inr ⟨tick, rs1, regsAgreeSym _ _ _ Hag, rfl⟩⟩
  have Hwire : ∀ s1 s2, RetX cpu rs k s1 → awire s1 s2 →
      RetX cpu rs k s2 ∨ RetNext cpu rs k s2 := by
    rintro s1 s2 ⟨ib', Hq⟩ Hw
    exact .inl ⟨ib', aeqvTrans _ _ _ (awireAeqv _ _ Hw) Hq⟩
  iintro Hcont
  iapply (wpdOfClosedRun .MaybeStuck i (RetX cpu rs k) (RetNext cpu rs k) Φ
    (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2) Hnord Hclos Hwire) $$ %s %Hs
  isplit
  · iexact Hcont
  · iintro %GD %s1 %_ %_
    iapply (Hend s1)

include Hend Htext Hflow in
/-- ONE INSTRUCTION from a `.pure ()` boundary: certificates for BOTH ticks at any state agreeing
with the boundary registers off the pins. -/
theorem wpdInstrOfEvA (Q : Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvA img (fun _ _ => False) Q (riscvStep tick) t) :
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i s Φ := by
  iintro C
  iapply (wpdRetNode i Φ cpu Hend rs k s Hs)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfEvA img i Φ cpu Hend Htext Hflow Q _ ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _)) $$ C

end bridge

end Weak
