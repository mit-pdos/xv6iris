/-
Weak: **Q1-c [OWN.144] (E2), part 1 — THE SAIL-TEXT OFFSET LEMMA** (`PROGRESS-W11F.md` §14).
Lean-only, no Rocq twin.

`CapFetchOfs.foB pc P m i` is an all-paths predicate on a Sail tree whose state `i` counts the
instruction-fetch reads made so far (`PinFetchPa.fqB` without the translation configuration):
* a register read is answered by any `Rboot`-admitted value, `PC` by `pc`;
* a register write writes an `Rboot`-admitted value;
* an instruction-fetch read OWES: it is no MMIO read, it is the first or the second of the
  cycle (`i < 2`), and its physical address is congruent to its granule `pc + 2i` modulo the
  page size (`foOk`); then it counts; any other read is answered by anything;
* there is no announce; every other node continues for every answer.
The headline **`foFetch`**: `fetch ()` (`Fetch.lean:233-288`), started with no fetch read at
`PC = pc`, makes its `k`-th fetch read at a physical address `≡ pc + 2k (mod 4096)` — WHATEVER the
translation answers: `translateAddr` (`Vmem.lean:567-590`) returns `pa = va` (Bare) or
`pa = ppn ++ va[11:0]` (Sv32/39/48/57), so it keeps the page offset (`fpTranslateAddrOfs`); the
fetch's PMA check answers `Ok` only in RAM and unsplit (W5's `fpCheckPmaIFS`, `fpSplitCannot`),
so each `fetch_bytes` makes ONE read at the translated address.

Spec: FAITHFUL — a theorem about the Sail text; no configuration fact is assumed (the TLB, `satp`
and the PTE answers are arbitrary).  With the MachCSL fetch guard ([OWN.144],
`MachCSL.MState.fetchPa_of_reducible`: a Supervisor-mode fetch at a RAM `PC` reads `PC` or
`PC + 2`) it gives the read exactly at `pc + 2k` (`Weak/CapDataOk.lean` §4).  Every helper is
`Weak.CapFetchOfs.*`.
-/
import Weak.PinFetchPaFqF

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace CapFetchOfs
open SailCycleOrderK SailCycleOrderFp

/-! ## 1. The predicate and its kit -/

/-- The obligation of the `i`-th fetch read at `pa`: one of the cycle's two, at its granule's page
offset. -/
def foOk (pc : Int) (i : Nat) (pa : BitVec 64) : Prop :=
  i < 2 ∧ paZ pa % 4096 = (pc + 2 * (i : Int)) % 4096

/-- **THE FETCH-OFFSET PREDICATE** (header). -/
def foB (pc : Int) {X : Type} (P : X → Nat → Prop) : SailM X → Nat → Prop
  | .pure x, i => P x i
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, i =>
    match o, k with
    | .memRead n _ req, k =>
        ((classify req.access_kind).akIfetch = true → devAddr req.pa = false ∧ foOk pc i req.pa ∧
          ∀ w : BitVec (8 * n), foB pc P (k (.Ok (w, none))) (i + 1)) ∧
        ((classify req.access_kind).akIfetch = false →
          ∀ w : BitVec (8 * n), foB pc P (k (.Ok (w, none))) i)
    | .instrAnnounce .., _ => False
    | .regRead r, k => ∀ v, Rboot r v →
        (∀ h : r = .PC, cast (congrArg RegisterType h) v = BitVec.ofInt 64 pc) → foB pc P (k v) i
    | .regWrite r v, k => Rboot r v ∧ ∀ u, foB pc P (k u) i
    | .barrier _, k => ∀ v, foB pc P (k v) i
    | .memWrite .., k => ∀ v, foB pc P (k v) i
    | .branchAnnounce .., k => ∀ v, foB pc P (k v) i
    | .cacheOp _, k => ∀ v, foB pc P (k v) i
    | .tlbi _, k => ∀ v, foB pc P (k v) i
    | .takeException _, k => ∀ v, foB pc P (k v) i
    | .returnException _, k => ∀ v, foB pc P (k v) i
    | .translationStart _, k => ∀ v, foB pc P (k v) i
    | .translationEnd _, k => ∀ v, foB pc P (k v) i
    | .cycleCount, k => ∀ v, foB pc P (k v) i
    | .getCycleCount, k => ∀ v, foB pc P (k v) i
    | .message _, k => ∀ v, foB pc P (k v) i
    | .choose _, k => ∀ v, foB pc P (k v) i
    | .readRam .., k => ∀ v, foB pc P (k v) i
    | .writeRam .., k => ∀ v, foB pc P (k v) i

section kit
variable {pc : Int}

theorem foBind {X Y : Type} (Q : X → Nat → Prop) (P : Y → Nat → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ i, foB pc Q m i → (∀ x i', Q x i' → foB pc P (f x) i') → foB pc P (m >>= f) i := by
  induction m with
  | pure y => intro i hm hf; exact hf y i hm
  | impure call k ih =>
    intro i hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show foB pc P (FreeM.impure (.ok o) (fun v => k v >>= f)) i
      cases o
      case memRead =>
        exact ⟨fun h => ⟨(hm.1 h).1, (hm.1 h).2.1, fun w => ih _ _ ((hm.1 h).2.2 w) hf⟩,
          fun h w => ih _ _ (hm.2 h w) hf⟩
      case instrAnnounce => exact hm
      case regRead => exact fun v hv hp => ih v _ (hm v hv hp) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      all_goals exact fun v => ih v _ (hm v) hf

/-- **The footprint lift**: W-SCO's strict footprint (no fetch read, `Rboot` reads and writes)
keeps the count. -/
theorem foOfFp {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) i, fp S m → foB pc (fun x i' => S x ∧ i' = i) m i := by
  intro m
  induction m with
  | pure y => intro i h; exact ⟨h, rfl⟩
  | impure call k ih =>
    intro i hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hm
        refine ⟨fun h2 => ?_, fun _ w => ih _ i (hk _)⟩
        exact absurd h2 (by simp only [SailCycleOrderFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v i hm.2
      case regRead r => exact fun v hv _ => ih v i (hm v hv)
      case regWrite r v => exact ⟨hm.1, fun u => ih u i (hm.2 u)⟩
      all_goals exact fun v => ih v i (hm v)

theorem foFpBind {X Y : Type} (S : X → Prop) (P : Y → Nat → Prop) (m : SailM X) (f : X → SailM Y)
    (i : Nat) (hm : fp S m) (hf : ∀ x, S x → foB pc P (f x) i) : foB pc P (m >>= f) i :=
  foBind _ P m f i (foOfFp S m i hm) (fun x i' h => h.2 ▸ hf x h.1)

/-- A `PC` read answers `pc`. -/
theorem foReadPC {Y : Type} (P : Y → Nat → Prop) (f : BitVec 64 → SailM Y) (i : Nat)
    (h : foB pc P (f (BitVec.ofInt 64 pc)) i) : foB pc P (readReg .PC >>= f) i := by
  intro v _ hpc
  have e : v = BitVec.ofInt 64 pc := hpc rfl
  subst e
  exact h

/-- A leaf under the trivial post. -/
theorem foTrueLeaf {X : Type} (x : X) (i : Nat) : foB pc (fun _ _ => True) (pure x) i := trivial

end kit

/-! ## 2. `translateAddr` keeps the page offset -/

/-- The low twelve bits of `ppn ++ off`, at any width of `ppn`: `off`. -/
theorem lowOfs {w m : Nat} (ppn : BitVec w) (off : BitVec m) (hm : m = 12) :
    (BitVec.setWidth 64 (ppn ++ off)).toNat % 4096 = off.toNat := by
  subst hm
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt off.isLt,
    Nat.shiftLeft_eq]
  have := off.isLt
  have e : (2 : Nat) ^ 12 = 4096 := rfl
  rw [e] at this ⊢
  have e2 : (2 : Nat) ^ 64 = 4096 * 4503599627370496 := rfl
  rw [e2, Nat.mod_mul_right_mod]
  omega

/-- The Sv leaf of `translateAddr`: `ppn ++ va[11:0]` keeps `va`'s page offset. -/
theorem lowOfsG {w : Nat} (ppn : BitVec w) (x : BitVec 64) (hi : Nat) (hhi : hi = 11) :
    (BitVec.zeroExtend 64 (ppn ++ Sail.BitVec.extractLsb x hi 0)).toNat % 4096 = x.toNat % 4096 := by
  subst hhi
  show (BitVec.setWidth 64 (ppn ++ Sail.BitVec.extractLsb x 11 0)).toNat % 4096 = _
  rw [lowOfs ppn _ rfl]
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]

/-- The page offset of an `Ok` answer. -/
def ofsPost (va : BitVec 64) (r : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) :
    Prop :=
  ∀ pa pb e, r = .Ok (.Physaddr pa, pb, e) → pa.toNat % 4096 = va.toNat % 4096

set_option maxHeartbeats 8000000 in
/-- `translate` writes nothing the footprint forbids (the walker's own proof, kept as a lemma so
that the offset walk below treats its answer as opaque). -/
@[fp_reg] theorem fpTranslateT (sv : Nat) (asid : BitVec 16)
    (base : BitVec (if (sv = 32 : Bool) then 22 else 44)) (vpn : BitVec (sv - 12))
    (acc : MemoryAccessType mem_payload) (priv : Privilege) (mxr sum : Bool) (ext : Unit) :
    fpT (translate sv asid base vpn acc priv mxr sum ext) := by
  unfold translate
  fp_walk
  all_goals (split <;> decide)

set_option maxHeartbeats 40000000 in
/-- **`translateAddr` KEEPS THE PAGE OFFSET** (header): every path of an instruction-fetch
translation of `va` that answers `Ok (pa, _, _)` has `pa ≡ va (mod 4096)` — Bare `pa = va`, every
Sv mode `pa = ppn ++ va[11:0]` (`Vmem.lean:567-590`), whatever `translate` answers. -/
theorem fpTranslateAddrOfs (va : BitVec 64) :
    fp (ofsPost va) (translateAddr (.Virtaddr va) (.InstructionFetch ())) := by
  unfold translateAddr
  fp_walk_v
  all_goals (intro pa pb e h; cases h)
  all_goals first
    | (simp only [bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend]; done)
    | (simp only [bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend]
       show (BitVec.setWidth 64 va).toNat % 4096 = _
       rw [BitVec.setWidth_eq])
    | (simp only [bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend]
       refine lowOfsG _ va _ ?_
       first | rfl | decide)

/-- The page-offset congruence, as integers. -/
theorem ofsInt (pa va : BitVec 64) (h : pa.toNat % 4096 = va.toNat % 4096) :
    (pa.toNat : Int) % 4096 = (va.toNat : Int) % 4096 := by
  omega

/-! ## 3. The i-cache read chain -/

section chain
variable {pc : Int}

/-- **The i-cache read** at the `i`-th granule's offset. -/
theorem foReadRamIF (pa : BitVec 64) (n : Nat) (i : Nat) (hd : devAddr pa = false)
    (ha : foOk pc i pa) :
    foB pc (fun _ i' => i' = i + 1) (read_ram .Read_ifetch (.Physaddr pa) n false) i := by
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind]
  show foB pc _ (FreeM.impure (Except.ok (Outcome.memRead n 64 _)) _) i
  refine ⟨fun _ => ⟨hd, ha, fun w => rfl⟩, fun h => ?_⟩
  simp only [classifyIfetch] at h
  cases h

set_option maxHeartbeats 40000000 in
/-- **`checked_mem_read` of an instruction fetch**: `Ok` only after ONE read, at `pa`. -/
theorem foCheckedMemReadIF (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat)
    (i : Nat) (ha : foOk pc i (bits_of_physaddr pa)) :
    foB pc (fun r i' => ∀ d m, r = .Ok (d, m) → i' = i + 1)
      (checked_mem_read (.InstructionFetch ()) pbmt priv pa w false false false false) i := by
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure]
  refine foFpBind _ _ _ _ i (PinFetchVal.fpCheckPmaIFS pbmt priv pa w false) (fun r hr => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro d m h; cases h
  | Ok info =>
    obtain ⟨hram, hsp⟩ := hr info rfl
    simp only [ExceptT.run_pure, pure_bind, hsp]
    rw [bind_assoc]
    refine foFpBind _ _ _ _ i (PinFetchVal.fpSplitCannot pa w _) (fun p hp => ?_)
    subst hp
    simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
      Bool.false_eq_true, ↓reduceIte]
    rw [show Int.toNat 1 = 0 + 1 from rfl]
    simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine foFpBind _ _ _ _ i (by fp_walk : fpT (assert true "loop dummy assert")) (fun _ _ => ?_)
    refine foFpBind _ _ _ _ i (fpPmpCheck _ _ _ _) (fun o _ => ?_)
    have hr0 := ramShift0 pa (w : Int) hram
    have hd0 := devShift0 pa (w : Int) hram
    cases o with
    | some e =>
      simp only []
      intro d m h; cases h
    | none =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine foFpBind _ _ _ _ i (fpWithinMmioRam _ _ hr0) (fun b hb => ?_)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine foBind _ _ _ _ i (foReadRamIF _ _ i hd0 (by rw [addInt0]; exact ha)) (fun r i' hi => ?_)
      subst hi
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, pure_bind, ExceptT.run_pure]
      intro d m _; rfl

set_option maxHeartbeats 40000000 in
/-- **`mem_read` of an instruction fetch** at the `i`-th granule's offset. -/
theorem foMemReadIF (pbmt : page_based_mem_type) (pa : physaddr) (w : Nat) (i : Nat)
    (ha : foOk pc i (bits_of_physaddr pa)) :
    foB pc (fun r i' => ∀ d, r = .Ok d → i' = i + 1)
      (mem_read (.InstructionFetch ()) pbmt pa w false false false) i := by
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine foFpBind _ _ _ _ i (by fp_walk : fpT (readReg Register.mstatus)) (fun a _ => ?_)
  refine foFpBind _ _ _ _ i (by fp_walk : fpT (readReg Register.cur_privilege)) (fun b _ => ?_)
  refine foFpBind _ _ _ _ i (fpEffectivePrivilege _ _ _) (fun p _ => ?_)
  refine foBind _ _ _ _ i (foCheckedMemReadIF pbmt p pa w i ha) (fun r i' h => ?_)
  intro d hd
  cases r with
  | Ok q =>
    obtain ⟨d', m⟩ := q
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hd

set_option maxHeartbeats 40000000 in
/-- **`fetch_bytes`** of the `i`-th granule `gs` (`i < 2`, `gs ≡ pc + 2i`): `Success` only after
ONE fetch read, at the granule's page offset. -/
theorem foFetchBytes (fs gs : BitVec 64) (w : Nat) (i : Nat) (hi : i < 2)
    (hgs : (gs.toNat : Int) % 4096 = (pc + 2 * (i : Int)) % 4096) :
    foB pc (fun r i' => ∀ b, r = .FetchBytes_Success b → i' = i + 1) (fetch_bytes fs gs w) i := by
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine foBind _ _ _ _ i (foOfFp _ _ i (fpTranslateAddrOfs gs)) (fun r i' hr' => ?_)
  obtain ⟨hpa, hi'⟩ := hr'
  subst i'
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro b hb; cases hb
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    cases paddr with
    | Physaddr pa =>
    have hoff := hpa pa pbmt u rfl
    have ha : foOk pc i (bits_of_physaddr (.Physaddr pa)) := by
      refine ⟨hi, ?_⟩
      show (pa.toNat : Int) % 4096 = _
      rw [ofsInt pa gs hoff]; exact hgs
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine foBind _ _ _ _ i (foMemReadIF pbmt _ w i ha) (fun r i' h => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine foFpBind (fun _ => True) _ _ _ i' ?_ (fun _ _ => ?_)
      · fp_walk
      · intro b hb; cases hb
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      intro b _
      exact h bytes rfl

end chain

/-! ## 4. The fetch -/

section fetch
variable {pc : Int}

/-- **The 4-byte / first 2-byte arm's read** at `PC` (count 0). -/
theorem foFBAt0 {Y : Type} (P : Y → Nat → Prop) (w : Nat)
    (hg1 : ((BitVec.ofInt 64 pc).toNat : Int) % 4096 = (pc + 2 * ((0 : Nat) : Int)) % 4096)
    (f : FetchBytes_Result w → SailM Y)
    (h : ∀ r i', (∀ b, r = .FetchBytes_Success b → i' = 1) → foB pc P (f r) i') :
    foB pc P (fetch_bytes (BitVec.ofInt 64 pc) (BitVec.ofInt 64 pc) w >>= f) 0 :=
  foBind _ _ _ _ 0 (foFetchBytes _ _ w 0 (by decide) hg1) h

/-- **The second 2-byte read** at `PC + 2` (count 1). -/
theorem foFBAt1 {Y : Type} (P : Y → Nat → Prop)
    (hg2 : ((BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat : Int) % 4096 = (pc + 2 * ((1 : Nat) : Int)) % 4096)
    (f : FetchBytes_Result 2 → SailM Y)
    (h : ∀ r i', foB pc P (f r) i') :
    foB pc P (fetch_bytes (BitVec.ofInt 64 pc) (BitVec.addInt (BitVec.ofInt 64 pc) 2) 2 >>= f) 1 :=
  foBind _ _ _ _ 1 (foFetchBytes _ _ 2 1 (by decide) hg2) (fun r i' _ => h r i')

/-- The 4-byte arm after its `PC` reads (one read at `PC`). -/
macro "fo_arm4" hg1:term:max : tactic => `(tactic| (
  refine foFBAt0 _ 4 $hg1 _ (fun r i' _ => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact foTrueLeaf _ _
  | FetchBytes_Exception e =>
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
    exact foReadPC _ _ _ (foTrueLeaf _ _)
  | FetchBytes_Success b =>
    simp only []
    split <;> exact foTrueLeaf _ _))

/-- The 2-byte arm after its `PC` reads (a read at `PC`, a second at `PC + 2`). -/
macro "fo_arm2" hg1:term:max hg2:term:max : tactic => `(tactic| (
  refine foFBAt0 _ 2 $hg1 _ (fun r i' hr => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact foTrueLeaf _ _
  | FetchBytes_Exception e =>
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
    exact foReadPC _ _ _ (foTrueLeaf _ _)
  | FetchBytes_Success b =>
    have e := hr _ rfl
    subst e
    simp only []
    split
    · exact foTrueLeaf _ _
    · simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure, pure_bind]
      refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
      refine foFBAt1 _ $hg2 _ (fun r i' => ?_)
      cases r with
      | FetchBytes_Ext_Error e => exact foTrueLeaf _ _
      | FetchBytes_Exception e =>
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
        exact foReadPC _ _ _ (foTrueLeaf _ _)
      | FetchBytes_Success b' => exact foTrueLeaf _ _))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH'S PAGE OFFSETS** (header): the `k`-th fetch read of `fetch ()` at `PC = pc` is at
a physical address `≡ pc + 2k (mod 4096)`, `k < 2`, and is no MMIO read. -/
theorem foFetch (pc : Int) (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) :
    foB pc (fun _ _ => True) (fetch ()) 0 := by
  have hg1 : ((BitVec.ofInt 64 pc).toNat : Int) % 4096 = (pc + 2 * ((0 : Nat) : Int)) % 4096 := by
    rw [PinFetchPa.toNatOfInt pc h0 (by omega)]; simp
  have hg2 : ((BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat : Int) % 4096 =
      (pc + 2 * ((1 : Nat) : Int)) % 4096 := by
    rw [PinFetchPa.toNatOfInt2 pc h0 hlt]; simp
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine foReadPC _ _ _ ?_
  refine foReadPC _ _ _ ?_
  refine foReadPC _ _ _ ?_
  refine foBind (fun _ _ => True) _ _ _ 0 ?_ ?_
  rotate_left
  · intro r i' _
    rcases r with (e | e) | e <;> exact trivial
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure,
    PinFetchVal.runIte, PinFetchVal.iteBind, Bool.false_eq_true, ↓reduceIte]
  -- the arms
  split
  · exact foReadPC _ _ _ (foTrueLeaf _ _)
  · refine foReadPC _ _ _ ?_
    try dsimp only
    split
    · refine foFpBind _ _ _ _ _ (fpCurrentlyEnabled _) (fun _ _ => ?_)
      split
      · exact foReadPC _ _ _ (foTrueLeaf _ _)
      · refine foReadPC _ _ _ ?_
        try dsimp only
        split
        · refine foFpBind _ _ _ _ _ (fpCurrentlyEnabled _) (fun _ _ => ?_)
          split
          · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
            fo_arm4 hg1
          · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
            fo_arm2 hg1 hg2
        · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
          fo_arm2 hg1 hg2
    · refine foReadPC _ _ _ ?_
      try dsimp only
      split
      · refine foFpBind _ _ _ _ _ (fpCurrentlyEnabled _) (fun _ _ => ?_)
        split
        · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
          fo_arm4 hg1
        · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
          fo_arm2 hg1 hg2
      · refine foReadPC _ _ _ (foReadPC _ _ _ ?_)
        fo_arm2 hg1 hg2

end fetch

end CapFetchOfs
end Weak
