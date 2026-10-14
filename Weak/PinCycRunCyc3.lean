/-
Weak: **W9a (B) B5 cycRun — the Sail cycle walk, part 3: the fetch, the announce, the decode, the
execute, the cycle** ([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

`cySailOf` proves the Sail cycle fact `cySailAt pc` (`Weak/PinCycRunAsm.lean`) at a walk pc whose
word decodes (`PinWalkTab.decS`) from TWO per-instruction facts, each its own named Prop:
* `fetchCyR1 pc` — r1's content at the cycle: `fetch ()` returns one of Sail's four fetch arms
  over the reads it logs (`Fetch.lean:253-288`) — the value chain W5's `PinFetchVal.faFetch`
  proves — with the frame (no protected register written);
* `execCyAt pc` — the execute stage of the decoded instruction (`uxaExecAs`): it retires with the
  next pc a walk successor and B1's slots full, or traps at a load/store; nothing else.
Around them (proved here): the announce (the role of the announced bits is the arm's, and is
`krole pc` — B4's `annRole*`), the decoder on the kernel configuration (`runRead drefS`, the
table's `decS`, transported to the mirror by `cyOfRunRead`), the landing-pad check (`elp = 0`),
the `Ext_Zca` gate, `nextPC := PC + len`, then the arms of `Weak/PinCycRunCyc2.lean`.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunCyc2
import Weak.SailCycleOrderAllDecode

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

-- The decoder's walk reads the platform configuration (see `Weak/PinWalkTab.lean`).
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-! ## 1. The two per-instruction obligations -/

/-- The fetch's arm over its log (`Fetch.lean:253-288`), at `pc`. -/
def fetchShapeOk (pc : Int) : FetchResult → List FeEnt → Prop
  | .F_Base w, fe =>
      (fe = [⟨pc, 4, w⟩] ∧ isRVC (Sail.BitVec.extractLsb w 15 0) = false) ∨
      (∃ lo hi : BitVec 16, fe = [⟨pc, 2, lo⟩, ⟨pc + 2, 2, hi⟩] ∧ w = hi ++ lo ∧ isRVC lo = false)
  | .F_RVC h, fe =>
      (∃ w : BitVec 32, fe = [⟨pc, 4, w⟩] ∧ h = Sail.BitVec.extractLsb w 15 0 ∧ isRVC h = true) ∨
      (fe = [⟨pc, 2, h⟩] ∧ isRVC h = true)
  | .F_Error _, _ => True
  | .F_Ext_Error _, _ => False

/-- The fetch's post: the frame and the pre-announce dataflow kept, every logged byte `kA`-
admitted, the result the arm of the log. -/
def fetchPostCy (pc : Int) (st : CySt) (fr : FetchResult) (st' : CySt) : Prop :=
  (∀ r, pfProt r = true → st'.rv r = st.rv r) ∧ RbootAll st'.rv ∧ st'.an = st.an ∧
  st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok ∧
  (∀ e, e ∈ st'.fe → ∀ j, j < e.n → kA (e.a + (j : Int)) (nthByte e.w j)) ∧
  fetchShapeOk pc fr st'.fe

/-- **(3) r1 AT THE CYCLE (NAMED, header)**: from an empty log, `fetch ()` returns the arm of the
reads it logs (Sail's value chain `fetch` → `fetch_bytes` → `mem_read` → the i-cache read: W5's
`PinFetchVal.faFetch`), writes no protected register, never an extension error. -/
def fetchCyR1 (pc : Int) : Prop :=
  ∀ (T : CySt → (r : Register) → RegisterType r → Prop) (st : CySt),
    st.fe = [] → st.an = false → st.rv .PC = BitVec.ofInt 64 pc → kCfg st.rv → RbootAll st.rv →
    st.d.ro = OpRoles.ORnone →
    cyB kA (kAa pc) cyS T (fetchPostCy pc st) (fetch ()) st

/-- The execute stage's entry: `PC = pc`, `nextPC = pc + len`, the kernel configuration, the
announced role `krole pc`, empty slots. -/
def execPre (pc : Int) (st : CySt) : Prop :=
  st.rv .PC = BitVec.ofInt 64 pc ∧ kCfg st.rv ∧ RbootAll st.rv ∧
  st.rv .nextPC = BitVec.ofInt 64 (pc + wSize (kw pc)) ∧ st.an = true ∧ st.d.ro = krole pc ∧
  st.d.n = 0 ∧ st.d.ok = true

/-- The execute stage's post: log, flag, role kept, the protected mirror kept but `nextPC`; a
RETIREMENT with B1's slots full and `nextPC` a walk successor, or a TRAP at a load/store. -/
def execPost (pc : Int) (st : CySt) (r : ExecutionResult) (st' : CySt) : Prop :=
  st'.fe = st.fe ∧ st'.an = st.an ∧ st'.d.ro = st.d.ro ∧ RbootAll st'.rv ∧
  (∀ r', pfProt r' = true → r' ≠ .nextPC → st'.rv r' = st.rv r') ∧
  ((r = RETIRE_SUCCESS ∧ st'.d.ok = true ∧ st'.d.n = (dfDests st'.d.ro).length ∧
      ∃ pc', pc' ∈ succPcs pc ∧ st'.rv .nextPC = BitVec.ofInt 64 pc') ∨
    (∃ x, r = .Trap x ∧ memPc pc = true))

/-- **(2) THE EXECUTE STAGE (NAMED, header)**: the decoded instruction's `uxaExecAs` at the
execute entry retires to a walk successor with B1's slots full, or traps at a load/store. -/
def execCyAt (pc : Int) : Prop :=
  ∀ a, PinWalkTab.decS pc = some a →
    ∀ (T : CySt → (r : Register) → RegisterType r → Prop) (st : CySt), execPre pc st →
      cyB kA (kAa pc) cyS T (execPost pc st) (uxaExecAs a) st

/-! ## 2. The fetched word IS the kernel's word -/

theorem PinCycRun.kAByte (pc : Int) (j : Nat) (b : BitVec 8) (hlo : textLo ≤ pc)
    (hhi : pc + 3 < textHi) (hj : j < 4) (h : kA (pc + (j : Int)) b) :
    b = BitVec.ofNat 8 (kbyte (pc + (j : Int))) := h (by omega) (by omega)

/-- A 4-byte read of the kernel's bytes at `pc` is `kword pc`. -/
theorem PinCycRun.word4 (pc : Int) (w : BitVec 32) (hlo : textLo ≤ pc) (hhi : pc + 3 < textHi)
    (hb : ∀ j : Nat, j < 4 → kA (pc + (j : Int)) (nthByte (n := 4) w j)) : w = kword pc :=
  kwordOfBytes pc w (fun j hj => PinCycRun.kAByte pc j _ hlo hhi hj (hb j hj))

theorem PinCycRun.kwMod (pc : Int) : kw pc % 65536 = kbyte pc + 256 * kbyte (pc + 1) := by
  have := WeakRvwmoPinBridge4.kbyteLt pc
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 1)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 2)
  have := WeakRvwmoPinBridge4.kbyteLt (pc + 3)
  unfold kw
  omega

/-- A 2-byte read of the kernel's bytes at `pc` is the low half of `kw pc`. -/
theorem PinCycRun.half2 (pc : Int) (h : BitVec 16) (hlo : textLo ≤ pc) (hhi : pc + 3 < textHi)
    (hb : ∀ j : Nat, j < 2 → kA (pc + (j : Int)) (nthByte (n := 2) h j)) :
    h = BitVec.ofNat 16 (kw pc) := by
  have e := WeakRvwmoPinBridge4.toNatOfBytes2 pc h
    (fun j hj => PinCycRun.kAByte pc j _ hlo hhi (by omega) (hb j hj))
  apply BitVec.eq_of_toNat_eq
  rw [e, BitVec.toNat_ofNat, show (2 : Nat) ^ 16 = 65536 from rfl, PinCycRun.kwMod]

/-- The high half of a 2+2 fetch: the bytes at `pc + 2`, `pc + 3`. -/
theorem PinCycRun.halfHi (pc : Int) (h : BitVec 16) (hlo : textLo ≤ pc) (hhi : pc + 3 < textHi)
    (hb : ∀ j : Nat, j < 2 → kA (pc + 2 + (j : Int)) (nthByte (n := 2) h j)) :
    h.toNat = kbyte (pc + 2) + 256 * kbyte (pc + 2 + 1) :=
  WeakRvwmoPinBridge4.toNatOfBytes2 (pc + 2) h (fun j hj => by
    have := hb j hj
    have e : pc + 2 + (j : Int) = pc + ((j + 2 : Nat) : Int) := by push_cast; omega
    rw [e] at this ⊢
    exact PinCycRun.kAByte pc (j + 2) _ hlo hhi (by omega) this)

/-- The low half of `kword pc`. -/
theorem PinCycRun.lo16Kword (pc : Int) :
    Sail.BitVec.extractLsb (kword pc) 15 0 = BitVec.ofNat 16 (kw pc) := by
  apply BitVec.eq_of_toNat_eq
  unfold Sail.BitVec.extractLsb kword
  rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show kw pc % 2 ^ 32 % 2 ^ (15 - 0 + 1) = kw pc % 2 ^ 16
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- Sail's `isRVC` of the low half is the walk's compressed test `wIsRvc`. -/
theorem PinCycRun.isRvcKw (x : Nat) : isRVC (BitVec.ofNat 16 x) = wIsRvc x := by
  have h4 : (Sail.BitVec.extractLsb (BitVec.ofNat 16 x) 1 0).toNat = x % 4 := by
    unfold Sail.BitVec.extractLsb
    rw [BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
    show x % 2 ^ 16 % 2 ^ (1 - 0 + 1) = x % 4
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  have h3 : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2
  unfold isRVC wIsRvc
  rw [h3]
  have hb : Sail.BitVec.extractLsb (BitVec.ofNat 16 x) 1 0 = BitVec.ofNat 2 (x % 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [h4, BitVec.toNat_ofNat]
    show x % 4 = x % 4 % 4
    rw [Nat.mod_mod]
  rw [hb]
  have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

/-- The table's decode, as a `runRead` walk: a base word. -/
theorem PinCycRun.decBase (pc : Int) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hr : wIsRvc (kw pc) = false) :
    ∃ b, runRead drefS (ext_decode (BitVec.ofNat 32 (kw pc))) = some (a, b) := by
  unfold PinWalkTab.decS at hdec
  simp only [hr, Bool.false_eq_true, ↓reduceIte] at hdec
  split at hdec
  · rename_i a' b' h
    cases hdec
    exact ⟨b', h⟩
  · cases hdec

/-- The table's decode, as a `runRead` walk: a compressed halfword. -/
theorem PinCycRun.decRvc (pc : Int) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hr : wIsRvc (kw pc) = true) :
    ∃ b, runRead drefS (ext_decode_compressed (BitVec.ofNat 16 (kw pc))) = some (a, b) := by
  unfold PinWalkTab.decS at hdec
  simp only [hr, ↓reduceIte] at hdec
  split at hdec
  · rename_i a' b' h
    cases hdec
    exact ⟨b', h⟩
  · cases hdec

/-- The kernel configuration agrees with the decoder's reference map. -/
theorem PinCycRun.drefAgree (rv : RegFile) (h : kCfg rv) :
    ∀ r v, drefS r = some v → wireReg r = false ∧ rv r = v := by
  intro r v hv
  obtain ⟨c1, c2, c3, c4, -⟩ := h
  unfold drefS at hv
  split at hv
  · cases hv; exact ⟨rfl, c1⟩
  · cases hv; exact ⟨rfl, c2⟩
  · cases hv; exact ⟨rfl, c3⟩
  · cases hv; exact ⟨rfl, c4⟩
  · cases hv

/-- `Ext_Zca` is enabled on the kernel configuration. -/
theorem PinCycRun.zcaOn : runRead drefS (currentlyEnabled .Ext_Zca) = some (true, true) := by
  decide +kernel

/-! ## 3. After the fetch -/

section after
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {S : Register → Bool}
  {T : CySt → (r : Register) → RegisterType r → Prop}

theorem cyBBindF {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) (st : CySt) (hm : cyB A Aa S T Q m st)
    (hf : ∀ x st', Q x st' → cyB A Aa S T P (f x) st') : cyB A Aa S T P (FreeM.bind m f) st :=
  cyBBind Q P m f st hm hf

theorem cyAnnBind {Y : Type} (Q : Y → CySt → Prop) {n : Nat} (w : BitVec n) (f : Unit → SailM Y)
    (st : CySt) (han : st.an = false) (h : cyB A Aa S T Q (f ()) (cyAnn st n w)) :
    cyB A Aa S T Q (instr_announce w >>= f) st :=
  ⟨han, fun u => by cases u; exact h⟩

end after

/-- `nextPC`'s write is labelled `LCtrl`: it moves no slot. -/
theorem PinCycRun.dfWrNextPC (d : DfSt) : (dfWr d .nextPC).n = d.n ∧ (dfWr d .nextPC).ok = d.ok ∧
    (dfWr d .nextPC).ro = d.ro := by
  have hl : ∀ rd srcs, erwLabel (erwOf d.ro d.rds .nextPC) ≠ Wlabel.LRegW rd srcs := by
    intro rd srcs e
    unfold erwOf at e
    rw [if_pos rfl] at e
    cases e
  have := dfLabNeutral d.ro d.n d.ok _ hl
  simp only [dfWr, this, and_self]

/-- The post-fetch facts of a base word: the word is `kword pc`, the walk's word is not
compressed, the log is the arm `fa` at `pc` whose role is the announced one and `krole pc`. -/
theorem PinCycRun.baseFacts (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (w : BitVec 32)
    (fe : List FeEnt) (hkA : ∀ e, e ∈ fe → ∀ j, j < e.n → kA (e.a + (j : Int)) (nthByte e.w j))
    (hsh : fetchShapeOk pc (.F_Base w) fe) :
    w = kword pc ∧ wIsRvc (kw pc) = false ∧ depsOfIb (some (ibOfBvn w)) = krole pc ∧
      ∃ fa, armOf pc fe = some fa ∧ fa.annRole = depsOfIb (some (ibOfBvn w)) := by
  obtain ⟨hlo, hhi⟩ := htext
  rcases hsh with ⟨rfl, hr⟩ | ⟨lo, hi, rfl, rfl, hr⟩
  · have hb : ∀ j : Nat, j < 4 → kA (pc + (j : Int)) (nthByte (n := 4) w j) :=
      fun j hj => hkA ⟨pc, 4, w⟩ (List.mem_singleton.2 rfl) j hj
    have hw := PinCycRun.word4 pc w hlo hhi hb
    have hrole := (annRoleBase4 pc w (fun j hj => PinCycRun.kAByte pc j _ hlo hhi hj (hb j hj))).2
    refine ⟨hw, ?_, hrole, .base4 w, ?_, rfl⟩
    · rw [← PinCycRun.isRvcKw, ← PinCycRun.lo16Kword, ← hw]; exact hr
    · simp only [armOf, ↓reduceIte, hr, Bool.false_eq_true]
  · have hlo2 := PinCycRun.half2 pc lo hlo hhi (fun j hj =>
      hkA ⟨pc, 2, lo⟩ List.mem_cons_self j hj)
    have hhi2 := PinCycRun.halfHi pc hi hlo hhi (fun j hj =>
      hkA ⟨pc + 2, 2, hi⟩ (List.mem_cons_of_mem _ List.mem_cons_self) j hj)
    have hlo2' : lo.toNat = kbyte pc + 256 * kbyte (pc + 1) := by
      rw [hlo2, BitVec.toNat_ofNat, show (2 : Nat) ^ 16 = 65536 from rfl, PinCycRun.kwMod]
    obtain ⟨hw, hrole⟩ := annRoleBase22 pc lo hi hlo2' hhi2
    have hid : ibOfBvn (hi ++ lo) = hi ++ lo := by
      apply BitVec.eq_of_toNat_eq
      unfold ibOfBvn
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi ++ lo).isLt]
    refine ⟨hid ▸ hw, ?_, hrole, .base22 lo hi, ?_, rfl⟩
    · rw [← PinCycRun.isRvcKw, ← hlo2]; exact hr
    · simp [armOf]

/-- The post-fetch facts of a compressed halfword. -/
theorem PinCycRun.rvcFacts (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (h : BitVec 16)
    (fe : List FeEnt) (hkA : ∀ e, e ∈ fe → ∀ j, j < e.n → kA (e.a + (j : Int)) (nthByte e.w j))
    (hsh : fetchShapeOk pc (.F_RVC h) fe) :
    h = BitVec.ofNat 16 (kw pc) ∧ wIsRvc (kw pc) = true ∧ depsOfIb (some (ibOfBvn h)) = krole pc ∧
      ∃ fa, armOf pc fe = some fa ∧ fa.annRole = depsOfIb (some (ibOfBvn h)) := by
  obtain ⟨hlo, hhi⟩ := htext
  rcases hsh with ⟨w, rfl, rfl, hr⟩ | ⟨rfl, hr⟩
  · have hb : ∀ j : Nat, j < 4 → kA (pc + (j : Int)) (nthByte (n := 4) w j) :=
      fun j hj => hkA ⟨pc, 4, w⟩ (List.mem_singleton.2 rfl) j hj
    have hw := PinCycRun.word4 pc w hlo hhi hb
    have hrole := annRoleRvc4 pc w (fun j hj => PinCycRun.kAByte pc j _ hlo hhi (by omega)
      (hb j (by omega))) hr
    have hh : Sail.BitVec.extractLsb w 15 0 = BitVec.ofNat 16 (kw pc) := by
      rw [hw]; exact PinCycRun.lo16Kword pc
    refine ⟨hh, ?_, hrole, .rvc4 w, ?_, rfl⟩
    · rw [← PinCycRun.isRvcKw, ← hh]; exact hr
    · simp only [armOf, ↓reduceIte, hr]
  · have hh := PinCycRun.half2 pc h hlo hhi (fun j hj => hkA ⟨pc, 2, h⟩ (List.mem_singleton.2 rfl) j hj)
    have hh' : h.toNat = kbyte pc + 256 * kbyte (pc + 1) := by
      rw [hh, BitVec.toNat_ofNat, show (2 : Nat) ^ 16 = 65536 from rfl, PinCycRun.kwMod]
    refine ⟨hh, ?_, annRoleRvc pc h hh' hr, .rvc2 h, ?_, rfl⟩
    · rw [← PinCycRun.isRvcKw, ← hh]; exact hr
    · simp [armOf, hr]

/-! ## 4. THE CYCLE -/

theorem PinCycRun.kCfgProt (rv rv' : RegFile)
    (h : ∀ r, pfProt r = true → r ≠ .PC → r ≠ .nextPC → rv' r = rv r) :
    kCfg rv → kCfg rv' := by
  rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h .cur_privilege (by decide) (by decide) (by decide)]; exact c1
  · rw [h .misa (by decide) (by decide) (by decide)]; exact c2
  · rw [h .menvcfg (by decide) (by decide) (by decide)]; exact c3
  · rw [h .mseccfg (by decide) (by decide) (by decide)]; exact c4
  · rw [h .hart_state (by decide) (by decide) (by decide)]; exact c5
  · rw [h .mstatus (by decide) (by decide) (by decide)]; exact c6
  · rw [h .elp (by decide) (by decide) (by decide)]; exact c7

set_option maxHeartbeats 4000000 in
/-- **THE SAIL CYCLE FACT FROM THE TWO PER-INSTRUCTION FACTS** (header). -/
theorem cySailOf (pc : Int) (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction)
    (hdec : PinWalkTab.decS pc = some a) (hfetch : fetchCyR1 pc) (hexec : execCyAt pc)
    (hnw : dfNwRole (krole pc)) : cySailAt pc := by
  intro tick st hinit
  obtain ⟨⟨hpc, hcfg, hrb⟩, hfe, han, hd⟩ := hinit
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  have hpre0 : preInv st st := ⟨cyFrameRefl st hrb, by rw [hd], by rw [hd], by rw [hd]⟩
  refine cyPrelude _ _ _ _ _ st st hpre0 (fun st1 h1 => ?_)
  rw [hcfg.2.2.2.2.1]
  simp only [ucBody]
  rw [uc_runHartActive_eq]
  simp only [bind_assoc]
  refine cyDispatch _ _ _ _ _ st st1 h1 (fun o st2 h2 => ?_)
  have han2 : st2.an = false := h2.1.2.2.2.trans han
  cases o with
  | some ip =>
    refine cyPureBind _ _ _ _ ?_
    refine cyFinishIntr kA (kAa pc) (cyT pc) _ ip tick st2 h2.1.2.1
      (fun st' r v _ han' _ _ h => ?_)
    rw [han', han2] at h; cases h
  | none =>
    simp only [bind_assoc]
    refine cyBBind (fetchPostCy pc st2) _ _ _ st2 ?_ (fun fr st3 h3 => ?_)
    · exact hfetch _ st2 (h2.1.2.2.1.trans hfe) han2
        (by rw [h2.1.1 .PC (by decide)]; exact hpc)
        (PinCycRun.kCfgProt _ _ (fun r hr _ _ => h2.1.1 r hr) hcfg) h2.1.2.1 h2.2.1
    · obtain ⟨hp3, hrb3, han3, hro3, hn3, hok3, hkA3, hsh3⟩ := h3
      have han3' : st3.an = false := han3.trans han2
      cases fr with
      | F_Ext_Error e => exact hsh3.elim
      | F_Error p =>
        obtain ⟨e, addr⟩ := p
        simp only [ucAfterFetch, ext_fetch_hook]
        refine cyPureBind _ _ _ _ ?_
        refine cyFinishFetchFail kA (kAa pc) (cyT pc) _ (virtaddr.Virtaddr addr, e) tick st3 hrb3
          (fun st' r v _ han' _ _ h => ?_)
        rw [han', han3'] at h; cases h
      | F_RVC h =>
        obtain ⟨hw, hrvc, hrole, fa, hfa, hfaR⟩ := PinCycRun.rvcFacts pc htext h st3.fe hkA3 hsh3
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyAnnBind _ h _ st3 han3' ?_
        have hp4 : ∀ r, pfProt r = true → (cyAnn st3 16 h).rv r = st.rv r := fun r hr =>
          (hp3 r hr).trans (h2.1.1 r hr)
        have hcfg4 : kCfg (cyAnn st3 16 h).rv :=
          PinCycRun.kCfgProt _ _ (fun r hr _ _ => hp4 r hr) hcfg
        obtain ⟨b, hrr⟩ := PinCycRun.decRvc pc a hdec hrvc
        have hrr' : runRead drefS (ext_decode_compressed h) = some (a, b) := by rw [hw]; exact hrr
        refine cyBBind (fun i st' => i = a ∧ st'.rv = (cyAnn st3 16 h).rv ∧
          st'.fe = st3.fe ∧ st'.an = true ∧ st'.d.ro = krole pc ∧ st'.d.n = 0 ∧
          st'.d.ok = true) _ _ _ _ ?_ (fun i st5 h5 => ?_)
        · refine cyOfRunRead kA (kAa pc) cyS (cyT pc) drefS _ _ _ _ a b hrr'
            (SailCycleOrderFp.fpDecodeC _) (PinCycRun.drefAgree _ hcfg4) hrb3
            (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, ?_, ?_, ?_⟩)
          · rw [e4]; exact hrole
          · rw [e5]; exact hn3.trans h2.2.2.1
          · rw [e6]; exact hok3.trans h2.2.2.2
        · obtain ⟨rfl, e1, e2, e3, e4, e5, e6⟩ := h5
          unfold is_landing_pad_expected
          simp only [bind_assoc]
          refine cyReadBind _ _ _ _ (fun ev hev => ?_)
          have hev' : ev = 0#1 := by
            rw [PinCycRun.rdMirror _ _ _ (by decide) hev, e1]; exact hcfg4.2.2.2.2.2.2
          subst hev'
          refine cyPureBind _ _ _ _ ?_
          simp only [landing_pad_bits_backwards]
          rw [if_neg (by decide)]
          simp only [bind_assoc]
          refine cyBBind (fun z st' => z = true ∧ st'.rv = (cyRd st5 .elp).rv ∧
            st'.fe = st5.fe ∧ st'.an = st5.an ∧ st'.d.ro = st5.d.ro ∧ st'.d.n = st5.d.n ∧
            st'.d.ok = st5.d.ok) _ _ _ _ ?_ (fun z st5' h5' => ?_)
          · refine cyOfRunRead kA (kAa pc) cyS (cyT pc) drefS _ _ _ _ true true PinCycRun.zcaOn
              (SailCycleOrderFp.fpCurrentlyEnabled _) ?_ ?_
              (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, e4, e5, e6⟩)
            · show ∀ r v, drefS r = some v → wireReg r = false ∧ st5.rv r = v
              rw [e1]; exact PinCycRun.drefAgree _ hcfg4
            · show RbootAll st5.rv
              rw [e1]; exact hrb3
          obtain ⟨rfl, f1, f2, f3, f4, f5, f6⟩ := h5'
          simp only [↓reduceIte]
          refine cyReadBind _ _ _ _ (fun pcv hpcv => ?_)
          have hpcv' : pcv = BitVec.ofInt 64 pc := by
            rw [PinCycRun.rdMirror _ _ _ (by decide) hpcv, f1]
            show st5.rv .PC = _
            rw [e1]; exact (hp4 .PC (by decide)).trans hpc
          subst hpcv'
          refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
          -- the execute entry
          have hW := PinCycRun.dfWrNextPC (cyRd st5' .PC).d
          have hsz : wSize (kw pc) = 2 := by simp [wSize, hrvc]
          have hnpc : BitVec.addInt (BitVec.ofInt 64 pc) 2 = BitVec.ofInt 64 (pc + wSize (kw pc)) := by
            rw [hsz, BitVec.addInt, BitVec.ofInt_add]
          let st6 := cyWr (cyRd st5' .PC) .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 2)
          have hp6 : ∀ r, pfProt r = true → r ≠ .nextPC → st6.rv r = st.rv r := by
            intro r hr hne
            show (st5'.rv.set .nextPC _) r = _
            rw [RegFile.set_other _ _ _ _ hne, f1]
            show st5.rv r = _
            rw [e1]; exact hp4 r hr
          have hpre6 : execPre pc st6 := by
            refine ⟨?_, ?_, rbootAllSet _ _ _ ?_ trivial, ?_, f3.trans e3, ?_, ?_, ?_⟩
            · rw [hp6 .PC (by decide) (by decide)]; exact hpc
            · exact PinCycRun.kCfgProt st.rv st6.rv (fun r hr _ hne => hp6 r hr hne) hcfg
            · show RbootAll st5'.rv
              rw [f1]
              show RbootAll st5.rv
              rw [e1]; exact hrb3
            · show (st5'.rv.set .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 2)) .nextPC = _
              rw [RegFile.set_same]; exact hnpc
            · exact hW.2.2.trans (f4.trans e4)
            · exact hW.1.trans (f5.trans e5)
            · exact hW.2.1.trans (f6.trans e6)
          simp only [FreeMLemmas.bind_pure]
          refine cyBBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend h) ∧
            execPost pc st6 r st') _ _ _ st6 ?_ (fun s st7 hs => ?_)
          · exact cyBBind (execPost pc st6) _ _ _ st6 (hexec i hdec _ st6 hpre6)
              (fun r st' h => ⟨r, rfl, h⟩)
          obtain ⟨r, rfl, h7⟩ := hs
          obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
          have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
            (hp7 r hr hne).trans (hp6 r hr hne)
          rcases hres with ⟨rfl, hok7, hn7, pc', hpc', hnpc7⟩ | ⟨x, rfl, hmem⟩
          · refine cyFinishRetire kA (kAa pc) (cyT pc) _ _ tick st7 ?_ hrb7 ?_ (fun st8 ht8 => ?_)
            · rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1
            · rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw
            · obtain ⟨hPC8, hp8, hfe8, han8, hro8, hn8, hok8, hrb8⟩ := ht8
              refine ⟨fa, ?_, ?_, ?_, ?_, ?_, ⟨pc', hpc', ?_⟩, ?_⟩
              · rw [hfe8, hfe7]; exact (f2.trans e2) ▸ hfa
              · rw [han8, han7]; exact f3.trans e3
              · rw [hok8]; exact hok7
              · rw [hn8, hro8]; exact hn7
              · rw [hro8, hro7]; show st5'.d.ro = _; rw [f4, e4, ← hrole, hfaR]
              · rw [hPC8]; exact hnpc7
              · refine PinCycRun.kCfgProt st.rv st8.rv (fun r hr hne hne' => ?_) hcfg
                rw [hp8 r hr hne]; exact hp7' r hr hne'
          · refine cyFinishTrap kA (kAa pc) (cyT pc) _ x _ tick st7 hrb7
              (fun st' r v _ _ _ hcb _ => ⟨hcb, hmem⟩)

      | F_Base w =>
        obtain ⟨hw, hrvc, hrole, fa, hfa, hfaR⟩ := PinCycRun.baseFacts pc htext w st3.fe hkA3 hsh3
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        refine cyAnnBind _ w _ st3 han3' ?_
        have hp4 : ∀ r, pfProt r = true → (cyAnn st3 32 w).rv r = st.rv r := fun r hr =>
          (hp3 r hr).trans (h2.1.1 r hr)
        have hcfg4 : kCfg (cyAnn st3 32 w).rv :=
          PinCycRun.kCfgProt _ _ (fun r hr _ _ => hp4 r hr) hcfg
        obtain ⟨b, hrr⟩ := PinCycRun.decBase pc a hdec hrvc
        have hrr' : runRead drefS (ext_decode w) = some (a, b) := by rw [hw]; exact hrr
        refine cyBBind (fun i st' => i = a ∧ st'.rv = (cyAnn st3 32 w).rv ∧
          st'.fe = st3.fe ∧ st'.an = true ∧ st'.d.ro = krole pc ∧ st'.d.n = 0 ∧
          st'.d.ok = true) _ _ _ _ ?_ (fun i st5 h5 => ?_)
        · refine cyOfRunRead kA (kAa pc) cyS (cyT pc) drefS _ _ _ _ a b hrr'
            (SailCycleOrderFp.fpDecodeS _) (PinCycRun.drefAgree _ hcfg4) hrb3
            (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, ?_, ?_, ?_⟩)
          · rw [e4]; exact hrole
          · rw [e5]; exact hn3.trans h2.2.2.1
          · rw [e6]; exact hok3.trans h2.2.2.2
        · obtain ⟨rfl, e1, e2, e3, e4, e5, e6⟩ := h5
          unfold is_landing_pad_expected
          simp only [bind_assoc]
          refine cyReadBind _ _ _ _ (fun ev hev => ?_)
          have hev' : ev = 0#1 := by
            rw [PinCycRun.rdMirror _ _ _ (by decide) hev, e1]; exact hcfg4.2.2.2.2.2.2
          subst hev'
          refine cyPureBind _ _ _ _ ?_
          simp only [landing_pad_bits_backwards]
          refine cyReadBind _ _ _ _ (fun pcv hpcv => ?_)
          have hpcv' : pcv = BitVec.ofInt 64 pc := by
            rw [PinCycRun.rdMirror _ _ _ (by decide) hpcv]
            show st5.rv .PC = _
            rw [e1]; exact (hp4 .PC (by decide)).trans hpc
          subst hpcv'
          refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
          -- the execute entry
          have hW := PinCycRun.dfWrNextPC (cyRd (cyRd st5 .elp) .PC).d
          have hsz : wSize (kw pc) = 4 := by simp [wSize, hrvc]
          have hnpc : BitVec.addInt (BitVec.ofInt 64 pc) 4 = BitVec.ofInt 64 (pc + wSize (kw pc)) := by
            rw [hsz, BitVec.addInt, BitVec.ofInt_add]
          let st6 := cyWr (cyRd (cyRd st5 .elp) .PC) .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 4)
          have hp6 : ∀ r, pfProt r = true → r ≠ .nextPC → st6.rv r = st.rv r := by
            intro r hr hne
            show (st5.rv.set .nextPC _) r = _
            rw [RegFile.set_other _ _ _ _ hne, e1]; exact hp4 r hr
          have hpre6 : execPre pc st6 := by
            refine ⟨?_, ?_, rbootAllSet _ _ _ ?_ trivial, ?_, e3, ?_, ?_, ?_⟩
            · rw [hp6 .PC (by decide) (by decide)]; exact hpc
            · exact PinCycRun.kCfgProt st.rv st6.rv (fun r hr _ hne => hp6 r hr hne) hcfg
            · show RbootAll st5.rv
              rw [e1]; exact hrb3
            · show (st5.rv.set .nextPC (BitVec.addInt (BitVec.ofInt 64 pc) 4)) .nextPC = _
              rw [RegFile.set_same]; exact hnpc
            · exact hW.2.2.trans e4
            · exact hW.1.trans e5
            · exact hW.2.1.trans e6
          simp only [FreeMLemmas.bind_pure]
          refine cyBBindF (fun s st' => ∃ r, s = Step.Step_Execute (r, zero_extend w) ∧
            execPost pc st6 r st') _ _ _ st6 ?_ (fun s st7 hs => ?_)
          · exact cyBBind (execPost pc st6) _ _ _ st6 (hexec i hdec _ st6 hpre6)
              (fun r st' h => ⟨r, rfl, h⟩)
          obtain ⟨r, rfl, h7⟩ := hs
          obtain ⟨hfe7, han7, hro7, hrb7, hp7, hres⟩ := h7
          have hp7' : ∀ r, pfProt r = true → r ≠ .nextPC → st7.rv r = st.rv r := fun r hr hne =>
            (hp7 r hr hne).trans (hp6 r hr hne)
          rcases hres with ⟨rfl, hok7, hn7, pc', hpc', hnpc7⟩ | ⟨x, rfl, hmem⟩
          · refine cyFinishRetire kA (kAa pc) (cyT pc) _ _ tick st7 ?_ hrb7 ?_ (fun st8 ht8 => ?_)
            · rw [hp7' .hart_state (by decide) (by decide)]; exact hcfg.2.2.2.2.1
            · rw [hro7]; exact hpre6.2.2.2.2.2.1 ▸ hnw
            · obtain ⟨hPC8, hp8, hfe8, han8, hro8, hn8, hok8, hrb8⟩ := ht8
              refine ⟨fa, ?_, ?_, ?_, ?_, ?_, ⟨pc', hpc', ?_⟩, ?_⟩
              · rw [hfe8, hfe7]; exact e2 ▸ hfa
              · rw [han8, han7]; exact e3
              · rw [hok8]; exact hok7
              · rw [hn8, hro8]; exact hn7
              · rw [hro8, hro7]; show st5.d.ro = _; rw [e4, ← hrole, hfaR]
              · rw [hPC8]; exact hnpc7
              · refine PinCycRun.kCfgProt st.rv st8.rv (fun r hr hne hne' => ?_) hcfg
                rw [hp8 r hr hne]; exact hp7' r hr hne'
          · refine cyFinishTrap kA (kAa pc) (cyT pc) _ x _ tick st7 hrb7
              (fun st' r v _ _ _ hcb _ => ⟨hcb, hmem⟩)

end PinCycRun
end Weak
