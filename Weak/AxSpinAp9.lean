/-
Weak: **the inlined allocpid's CRITICAL-SECTION BODY on the positional engine** —
`wpdAllocpidCs`: from acquire's return (`allocproc + 0x44`) to `jal release` (`allocproc + 0x94`),
at the joint instance Ixv6, interrupts off (`ctrlOkSW`: S-mode, SIE = 0), warm TLB.

Rocq: `iris/AxSpinAp9.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the allocpid copy that
this tree's kernel INLINES into `allocproc`; code and mapping in `Weak/AxSpinAp.lean`'s header,
"Design"; design in `PROGRESS-Q18.md`, "AxSpinAp9").

## The Rocq header, in substance

Rocq's body is seven instructions (`auipc/addi a5 = &nextpid`, `c.lw s1,0(a5)` THE READ,
`addiw a4,s1,1`, `c.sw a4,0(a5)` THE WRITE, `auipc/addi a0 = &pid_lock`); the theorem takes
`e ↦ₐ R_np e` (nextpid's component of `R_pid` at an anchor `e` lob-before the read) and gives the
continuation the read's source fact `np_src` at the read, `R_np` re-established and the minted
`FRAG (word vs)` at the store, and the register facts.  The inlined copy's normal path (pid ≠ 1000,
no pid collision) is `+0x44 auipc a3`, `+0x48 lw a3,1998(a3)` (THE READ, row `k`), `li a6,1000`,
`c.li a0,1`, `a2 = &proc[NPROC]`, `c.j`, `c.mv a1,a0`, `beq a3,a6` (not taken),
`addiw a1,a3,1`, `a5 = proc`, 64 × (`c.lw a4,48(a5)` (row `k + 1 + j`); `beq a4,a3` not taken;
`addi a5,a5,376`; `bne a5,a2`), `+0x82 auipc a5`, `+0x86 sw a1,1936(a5)` (THE WRITE, row
`k + 65`), `+0x8a c.sw a3,48(s1)` (`p->pid`, row `k + 66`), `a0 = &pid_lock`; continuation at
`k + 67`, `PC = +0x94`.  As in Rocq the row pinning is a TEMPORARY ASSUMPTION (owner decision
2026-10-03): `RowAllocpidBody` fixes the path and the data addresses; ownership carries the values.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinAp9`, Q-S2-1/2)

`RowAllocpidBodyP k row pnp ppid` is `RowAllocpidBody` on a PREFIX row: the shape as
`RowShP` (AxSpinRowP; each of the 67 items that is PRESENT is matched, no length), the read
identities verbatim (vacuous at absent positions); `AxSpinAp9.rowBodyPOfFull`: full ⇒ prefix.
`wpdAllocpidCsP` is the same script as `wpdAllocpidCs` with one `by_cases` on `LEN ≤ position`
at each boundary where the row may end — `k`, `k + 1`, and, inside the 64-round scan induction
`AxSpinAp9.scanLoopP`, each round's start `k + 1 + j` and the boundary after its read
`k + 2 + j`; then `k + 65`, `k + 66`, `k + 67` (the other leaf calls at the same position reuse
the bound).  Every end case is the WINDOWED, RESOURCE-FREE hook (orchestrator's exact form):
  `HΨend : ∀ k', k ≤ k' → k' ≤ k + 67 → (grow (gtAdGd GT) i).length ≤ k' →
     ∀ pr : Pexv6, ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`
(the caller instantiates it by `AxSpinApA.wpdEndAnn` + `postLiftingTrue`).  The CS has NO
designated cut, so no end arm is proved here.  GUARDED premises (design §A "guarded pins"): the
two that name position `k` and are not vacuous at an absent position — `Hpo` (writes po-before
`(i, k)` are mo-before it) and the `RNp` anchor `e ∈ lobp (i, k)` — are stated under
`k < LEN`; `Hone`, `Hnowrap`, `Hncoll` are `∀ … = some …` forms, already vacuous, kept verbatim.
The continuation (unchanged) is reached only on rows with `k + 67 < LEN`.  `wpdAllocpidCs` and
`AxSpinAp9.scanLoop` keep their exact statements and are now corollaries (guards discharged,
hook vacuous under `k + 67 < LEN`).  HONESTY: no new pin; the P-form premises are implied by
the stage-1 ones.

## Deviations from Rocq

1. KERNEL INLINING (Q18).  `a5v` is the nextpid STORE base `pca 0x82 + auipc 8` (= nextpid − 1936;
   Rocq: `&nextpid`, the shared base of the read and the write); `vaNp` is the READ address
   `pca 0x44 + auipc 8 + 1998` (Rocq `a5v + 0`); `a0v` is `pca 0x8c + auipc 17 − 1790`.  The
   lemmas are `decide` (Rocq `vm_compute`) against `MachCSL.KernelSyms` (Xv6/KernelImage.lean:
   nextpid 0x8000a384, pid_lock 0x80012500, proc 0x80012930, tickslock 0x80018730).
2. `imm0` has no use in the inlined code (no zero-offset access); kept file-qualified.
3. `wpdAllocpidCs` RESTATED for the inlined copy and Stage C (fetches are not row items):
   * entry `PC = pca 0x44` (Rocq `+0x16`) at row `k`; the read is AT `k` (Rocq `k + 3`), the
     nextpid write at `k + 65` (Rocq `k + 6`), NEW `p->pid` write at `k + 66`, continuation at
     `k + 67` (Rocq `k + 9`), `PC = pca 0x94` (Rocq `+0x2e`).  `Hone`/`Hpo`/`e ∈ lobp` move to
     these positions.
   * NEW premise `k + 67 < LEN`: the register leaves `+0x8c/+0x90` run at boundary `k + 67`
     (`XxReg` needs `k < LEN`; `RowAllocpidBody` gives only `k + 67 ≤ LEN`).
   * Q18b (owner, FINAL) value pins of the normal path: `Hnowrap` also asks the read word
     `≠ 1000` (stated as `∀ vs, graph_value (i,k) = vs → word vs ≠ 1000 ∧ word + 1 < 2³²`),
     and NEW `Hncoll`: no scan read's word equals the read word.
   * Q18a (FINAL): the 64 racy scan reads use the value-agnostic `AxSpinAp8.FldMWScan`; NEW
     premises per `j < 64`: `dataAtS` (load) of `scanVa j` at `Pscan j`, `paZ (Pscan j) =
     scanAddr j`, `hitW rs0 (scanVa j)`.
   * Q18c (FINAL): the `p->pid` store flow `FstM (dokAtP (paZ Ppid) 4) i Opid` is a premise
     resource; NEW premises `dataAtS` (store) of `s1 + 48` at `Ppid` and its `hitW`; the
     continuation gets `Opid (k + 66) (wbytes 4 w)`.  `RowAllocpidBody` takes `paZ Ppid`.
   * the nextpid store's address is `a5v + 1936`, rewritten to `vaNp` (`AxSpinAp9.a5vVaNp`), so
     the store `dataAtS` is stated at `vaNp` as in Rocq.
   * post: the pid is in `a3` (Rocq `s1`; `+0x32`'s move to `a0` is gone), `a1 = addiw1 a3`
     (Rocq `a4`), `a5 = a5v` (Rocq `&nextpid`), `a0 = &pid_lock`, NEW `a2 = tickslock`
     (`&proc[NPROC]`), `a6 = 1000`; kept: every GPR other than 10–16 (Rocq: other than 9, 10,
     14, 15); NEW `graph_data (i, k + 66) = wbytes 4 w`.  The `+1` sum is stated at `BitVec 32`
     (`@HAdd.hAdd (BitVec 32) …`, as `npBytes`).
   * Q22 (known, being fixed separately): `allocpidText` is currently unsatisfiable (4-byte words
     at 2-mod-4 pcs); the theorem is stated over it as Rocq does, not worked around.
4. TYPES / SPELLING (as AxSpinPO5 deviation 3/4): `uint P` ↦ `paZ P`, `register_lookup PC rs` ↦
   `rs .PC`, `uint r ≠ n` ↦ `r.toNat ≠ n`; `[InvGS_gen hlc GF]` (any `hlc`); the local instances
   `x9_pol`/`x9_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section variables are
   explicit arguments in AxSpinE6's order (+ `Htxt`).  Tactics: `pcs`/`nz`/`zq` ↦ `decide`,
   `zsimp` ↦ the file-local macro `ax_spin_ap9_zsimp`.  The trailing `Print Assumptions` is not
   ported.

**Rocq → Lean name map.**  `a5v` `a5v`, `va_np` `vaNp`, `a0v` `a0v`, `a5v_nextpid` `a5vNextpid`,
`va_np_nextpid` `vaNpNextpid`, `a0v_pid_lock` `a0vPidLock`, `r9` `AxSpinAp9.r9` (duplicated),
`r14` `r14`, `imm0` `AxSpinAp9.imm0` (duplicated), `wpd_allocpid_cs` `wpdAllocpidCs`; the local
instances `x9_pol`, `x9_G` are inlined.  Lean-only (file-qualified): `AxSpinAp9.vw4`,
`AxSpinAp9.a5j`, `AxSpinAp9.scanVa`, `AxSpinAp9.a5j0`, `AxSpinAp9.a5j64`,
`AxSpinAp9.a5jTickslock`, `AxSpinAp9.a5jSucc`, `AxSpinAp9.a5jNe`, `AxSpinAp9.rdLoad`,
`AxSpinAp9.sext32Inj`, `AxSpinAp9.ldResInj`, `AxSpinAp9.sext32Ne1000`, `AxSpinAp9.ldResNe1000`,
`AxSpinAp9.st4Ld`, `AxSpinAp9.a5vVaNp`, `AxSpinAp9.li1000`, `AxSpinAp9.xxLdWG` (XxLdW generic in
`is_rvc`, explicit premises), `AxSpinAp9.scanLoop` (the 64-round scan by induction); + 1 local
macro.  Stage 2 (Lean-only): `RowAllocpidBodyP`, `wpdAllocpidCsP`, `AxSpinAp9.scanLoopP`,
`AxSpinAp9.rowBodyPOfFull`, `AxSpinAp9.bRdP`, `AxSpinAp9.bWrP` (new short names grepped absent);
reused `RowShP`/`rowShPOfSh`/`rowShPAt` (AxSpinRowP), `AxSpinAp8.FldMWFrame`.

**Dropped:** nothing (Rocq 10 definitions/lemmas + 2 local instances, inlined; Lean 10 + 18
Lean-only, + 6 stage-2 Lean-only).
-/
import Weak.AxSpinAp8
import Weak.AxSpinAp6
import Weak.AxSpinRowP

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The addresses the body computes -/

/-- Rocq `a5v` (deviation 1): `a5` at the nextpid store, `pca 0x82 + auipc 8`. -/
def a5v : BitVec 64 := pca 0x82 + auipcOff 8#20
/-- Rocq `va_np` (deviation 1): the nextpid read address of `lw a3,1998(a3)`. -/
def vaNp : BitVec 64 := (pca 0x44 + auipcOff 8#20) + sign_extend (m := 64) 1998#12
/-- Rocq `a0v` (deviation 1): `a0` after `+0x8c/+0x90`. -/
def a0v : BitVec 64 := (pca 0x8c + auipcOff 17#20) + sign_extend (m := 64) 0x902#12

/-- Rocq `a5v_nextpid` (deviation 1: the store's offset 1936 included). -/
theorem a5vNextpid : a5v + sign_extend (m := 64) 1936#12 = BitVec.ofNat 64 KernelSyms.«nextpid» := by
  decide
/-- Rocq `va_np_nextpid`. -/
theorem vaNpNextpid : vaNp = BitVec.ofNat 64 KernelSyms.«nextpid» := by decide
/-- Rocq `a0v_pid_lock`. -/
theorem a0vPidLock : a0v = BitVec.ofNat 64 KernelSyms.«pid_lock» := by decide

/-- Rocq `r9` (duplicated name). -/
abbrev AxSpinAp9.r9 : BitVec 5 := 9#5
/-- Rocq `r14`. -/
abbrev r14 : BitVec 5 := 14#5
/-- Rocq `imm0` (duplicated name; deviation 2). -/
abbrev AxSpinAp9.imm0 : BitVec 12 := 0#12

/-! # 2. Lean-only helpers for the capstone -/

theorem AxSpinAp9.vw4 : vmemWidth 4 := Or.inr (Or.inr (Or.inl rfl))

/-- (Lean-only) the scan pointer `a5` at round `j`: `&proc[j]`. -/
def AxSpinAp9.a5j (j : Nat) : BitVec 64 := BitVec.ofNat 64 (KernelSyms.«proc» + 376 * j)

/-- (Lean-only) the `j`-th scan read's virtual address (`c.lw a4,48(a5)`). -/
def AxSpinAp9.scanVa (j : Nat) : BitVec 64 := AxSpinAp9.a5j j + sign_extend (m := 64) 48#12

/-- (Lean-only) `+0x6c/+0x70` compute `proc`. -/
theorem AxSpinAp9.a5j0 :
    (pca 0x6c + auipcOff 17#20) + sign_extend (m := 64) 0xd52#12 = AxSpinAp9.a5j 0 := by decide

/-- (Lean-only) `+0x52/+0x56` compute `&proc[NPROC]`. -/
theorem AxSpinAp9.a5j64 :
    (pca 0x52 + auipcOff 0x17#20) + sign_extend (m := 64) 0xb6c#12 = AxSpinAp9.a5j 64 := by
  decide

/-- (Lean-only) `&proc[NPROC]` is `tickslock`. -/
theorem AxSpinAp9.a5jTickslock : AxSpinAp9.a5j 64 = BitVec.ofNat 64 KernelSyms.«tickslock» := by
  decide

/-- (Lean-only) `addi a5,a5,376` advances the scan pointer. -/
theorem AxSpinAp9.a5jSucc (j : Nat) :
    AxSpinAp9.a5j j + sign_extend (m := 64) 376#12 = AxSpinAp9.a5j (j + 1) := by
  rw [show sign_extend (m := 64) 376#12 = BitVec.ofNat 64 376 by decide]
  unfold AxSpinAp9.a5j
  rw [BitVec.ofNat_add_ofNat]
  exact congrArg (BitVec.ofNat 64) (by omega)

/-- (Lean-only) `bne a5,a2` is taken before the last round. -/
theorem AxSpinAp9.a5jNe (j : Nat) (hj : j < 64) : AxSpinAp9.a5j j ≠ AxSpinAp9.a5j 64 := by
  intro h
  have h2 := congrArg BitVec.toNat h
  unfold AxSpinAp9.a5j at h2
  simp only [BitVec.toNat_ofNat] at h2
  have hp : KernelSyms.«proc» = 0x80012930 := rfl
  rw [hp, Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega),
    Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)] at h2
  omega

/-- (Lean-only) the nextpid read's row label, from its identity and its graph value. -/
theorem AxSpinAp9.rdLoad (GD : Gdexec) (i : Agent) (k : Nat) (pnp : Int) (vs : List (BitVec 8)) :
    (∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead false pnp 4) →
    (∃ lb, (AxOpsem.grow GD i)[k]? = some lb) → graphValue GD (i, k) = some vs →
    ∃ ts, (AxOpsem.grow GD i)[k]? =
      some (.LLoad false pnp ts (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs))) := by
  rintro Hid ⟨lb, Hlb⟩ Hgv
  have Hlb' := Hid lb Hlb
  cases lb with
  | LStore _ _ _ _ => simp [aident] at Hlb'
  | LFence _ _ _ _ => simp [aident] at Hlb'
  | LRmw _ _ _ _ _ _ _ => simp [aident] at Hlb'
  | LLoad aq' b ts vs3 =>
    simp only [aident, AidentT.IRead.injEq] at Hlb'
    obtain ⟨rfl, rfl, Hlen⟩ := Hlb'
    have Hl := lblOfRow _ _ _ _ Hlb
    have Hv : vs3 = vs := by
      rw [graphValue, Hl] at Hgv
      simpa [lblValue] using Hgv
    subst Hv
    exact ⟨ts, by rw [wbytesWordOfBytes 4 vs3 Hlen]; exact Hlb⟩


/-! # 2b. The PREFIX twin of the body's row piece (stage 2) -/

/-- (stage 2) `RowAllocpidBody` on a PREFIX row: the shape as `RowShP` (each of the 67 items
that is PRESENT is matched; no length), the read identities verbatim (already vacuous at absent
positions). -/
def RowAllocpidBodyP (k : Nat) (row : List Lbl) (pnp ppid : Int) : Prop :=
  RowShP k row (apBodySh pnp ppid) ∧
  (∀ lb, row[k]? = some lb → aident lb = .IRead false pnp 4) ∧
  (∀ j, j < 64 → ∀ lb, row[k + 1 + j]? = some lb →
    aident lb = .IRead false (AxSpinAp7.scanAddr j) 4)

/-- (Lean-only) a full row piece is a prefix row piece. -/
theorem AxSpinAp9.rowBodyPOfFull {k : Nat} {row : List Lbl} {pnp ppid : Int} :
    RowAllocpidBody k row pnp ppid → RowAllocpidBodyP k row pnp ppid :=
  fun HR => ⟨rowShPOfSh HR.1, HR.2.1, HR.2.2⟩

/-- (Lean-only) `bRd` on a prefix row whose position `k` is present. -/
theorem AxSpinAp9.bRdP (k : Nat) (row : List Lbl) (pnp ppid : Int)
    (HR : RowAllocpidBodyP k row pnp ppid) (Hk : k < row.length) :
    ∃ lb, row[k]? = some lb ∧ aident lb = .IRead false pnp 4 := by
  obtain ⟨lb, Hlb, _⟩ := rowShPAt (j := 0) (it := .RL pnp 4) HR.1 rfl (by omega)
  rw [Nat.add_zero] at Hlb
  exact ⟨lb, Hlb, HR.2.1 lb Hlb⟩

/-- (Lean-only) `AxSpinAp7.bWr` on a prefix row whose position `k + 65` is present. -/
theorem AxSpinAp9.bWrP (k : Nat) (row : List Lbl) (pnp ppid : Int)
    (HR : RowAllocpidBodyP k row pnp ppid) (Hk : k + 65 < row.length) :
    ∃ vw cls, row[k + 65]? = some (.LStore false pnp vw cls) ∧ vw.length = 4 := by
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := rowShPAt (j := 65) (it := .RS pnp 4) HR.1 rfl Hk
  exact ⟨vw, cls, Hlb, Hl⟩

/-! # 3. Byte facts of the 4-byte loads (Lean-only) -/

/-- (Lean-only) 32-to-64 sign extension is injective. -/
theorem AxSpinAp9.sext32Inj (x y : BitVec 32) :
    extend_value false x = extend_value false y → x = y := by
  unfold extend_value sign_extend Sail.BitVec.signExtend
  simp only [Bool.false_eq_true, ↓reduceIte]
  intro h
  bv_decide

/-- (Lean-only) the 4-byte sign-extended load result determines the loaded word. -/
theorem AxSpinAp9.ldResInj (a b : List (BitVec 8)) :
    ldRes false 4 a = ldRes false 4 b → (wordOfBytes 4 a : BitVec 32) = wordOfBytes 4 b :=
  AxSpinAp9.sext32Inj _ _

/-- (Lean-only) a sign-extended word other than 1000 is not `li a6,1000`'s value. -/
theorem AxSpinAp9.sext32Ne1000 (x : BitVec 32) :
    x ≠ 1000#32 → extend_value false x ≠ 0#64 + sign_extend (m := 64) 1000#12 := by
  unfold extend_value sign_extend Sail.BitVec.signExtend
  simp only [Bool.false_eq_true, ↓reduceIte]
  intro h
  bv_decide

/-- (Lean-only) a loaded word other than 1000 is not `li a6,1000`'s value. -/
theorem AxSpinAp9.ldResNe1000 (vs : List (BitVec 8)) :
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 →
    ldRes false 4 vs ≠ 0#64 + sign_extend (m := 64) 1000#12 :=
  AxSpinAp9.sext32Ne1000 _

/-- (Lean-only) storing a 4-byte load result stores the loaded word. -/
theorem AxSpinAp9.st4Ld (vs : List (BitVec 8)) :
    stBytes 4 (ldRes false 4 vs) = WeakInterpProj.wbytes 4 (wordOfBytes 4 vs : BitVec 32) := by
  rw [st4Trunc]
  congr 1
  unfold ldRes rrv
  generalize (wordOfBytes 4 vs : BitVec 32) = x
  show BitVec.setWidth 32 (extend_value false x) = x
  unfold extend_value sign_extend Sail.BitVec.signExtend
  simp only [Bool.false_eq_true, ↓reduceIte]
  bv_decide

/-- (Lean-only) the store base `a5v` plus the `sw` offset is the read address. -/
theorem AxSpinAp9.a5vVaNp : a5v + sign_extend (m := 64) 1936#12 = vaNp := by decide

/-- (Lean-only) `li a6,1000`. -/
theorem AxSpinAp9.li1000 : 0#64 + sign_extend (m := 64) 1000#12 = BitVec.ofNat 64 1000 := by
  decide

/-- (Lean-only, Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_ap9_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 4. The width/compression-generic positional load leaf and the scan loop -/

section cs
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxt : allocpidText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- (Lean-only) `AxSpinXP2.XxLdW` with the compression bit a parameter (the nextpid read
`lw` at `+0x48` is 4-byte) and the `XLdP` premises explicit. -/
theorem AxSpinAp9.xxLdWG (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64)
    (is_rvc : Bool) (imm : BitVec 12) (rs1 rd : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, w)) →
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va w pa → hitW rs va →
    (∀ (lb : Lbl) (aq rl : Bool) (n : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aident lb = .IRmw aq rl (paZ pa) n → n ≠ w) →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ pa) w) i
        Out k (k + 1) -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = w⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false w vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗ Out k vs -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx hrd hvw hw1 hw8 hva hda hhv Hnormw1 Hle
  have HnoRmwX : Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + 1 →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokAtP (paZ pa) w base n⌝ := by
    intro _ GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq rl base n ⟨H1, H2⟩ Hlb Hid ⟨rfl, rfl⟩
    obtain rfl : k' = k := by omega
    exact Hnormw1 lb aq rl _ Hlb Hid rfl
  have HnoSplitX : Dkind.DKLd = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + 1 →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n →
        ¬ dokAtP (paZ pa) w base n⌝ := by
    intro h
    cases h
  have H := @XBkW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0P GT i)
    ⟨_, rfl⟩ Ψ (Hmid0P L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokAtP (paZ pa) w) .DKLd (OutRP GT i (paZ pa) w Out)
    s rs k pc is_rvc _ 1 none (owLdB rd false w) .CPend false
    (fun d r' => ∃ vs, d = .CLd vs ∧ vs.length = w ∧ r' = false)
    HnoRmwX HnoSplitX (by rintro d r ⟨vs, rfl, -⟩ aq vs' h; cases h)
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokAtP (paZ pa) w) rs pc is_rvc imm rs1 rd false w
      va pa false hrd hvw hw1 hw8 hva hda hhv ⟨rfl, rfl⟩)
    (by omega) (by omega)
  iintro F C
  iapply H $$ [F] [C]
  · simp only [CResW, CFkW]
    iapply (FldMWRowW L GT nm i (paZ pa) w Out k (k + 1))
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResW]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutRP
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- (Lean-only) THE PID-COLLISION SCAN (`+0x74 .. +0x7e`, 64 rounds), by induction on the
number `n` of remaining rounds: round `j` runs at row position `k + 1 + j` with `a5 = &proc[j]`
(`c.lw a4,48(a5)` reads `proc[j].pid` through the value-agnostic flow `AxSpinAp8.FldMWScan`;
`beq a4,a3` falls through by the no-collision pin; `addi a5,a5,376`; `bne a5,a2` loops back
for `j < 63` and falls through at `j = 63`).  STAGE-2 P-FORM: on a PREFIX row
(`RowAllocpidBodyP`, no length premise) the row may end at any round — at the start of round `j`
(`LEN ≤ k + 1 + j`) or right after its read (`LEN ≤ k + 2 + j`); those ends are discharged by the
windowed, resource-free hook `HΨend`. -/
theorem AxSpinAp9.scanLoopP (k : Nat) (pnp ppid : Int)
    (HR : RowAllocpidBodyP k (AxOpsem.grow (gtAdGd GT) i) pnp ppid)
    (HΨend : ∀ k' : Nat, k ≤ k' → k' ≤ k + 67 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ)
    (Pscan : Nat → BitVec 64) (rsB : RegFile) (vs : List (BitVec 8))
    (Hsc : ∀ j, j < 64 → dataAtS σi T (.Load .Data) (AxSpinAp9.scanVa j) 4 (Pscan j) ∧
      paZ (Pscan j) = AxSpinAp7.scanAddr j ∧ hitW rsB (AxSpinAp9.scanVa j))
    (Hhit : hitW rsB (pca 0x44))
    (Hncoll : ∀ j, j < 64 → ∀ v, graphValue (gtAdGd GT) (i, k + 1 + j) = some v →
      (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs)
    (H13 : gprVal rsB 13#5 = ldRes false 4 vs) (H12 : gprVal rsB 12#5 = AxSpinAp9.a5j 64) :
    ∀ n j, j + n = 64 → 0 < n → ∀ (rs : RegFile) (ib : Ibch),
      ctrlOkSW T satp0 rs → rs .PC = pca 0x74 → rs .tlb = rsB .tlb →
      (∀ r, r ≠ 14#5 → r ≠ 15#5 → gprVal rs r = gprVal rsB r) →
      gprVal rs 15#5 = AxSpinAp9.a5j j →
      ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
          ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x82 ∧ rs' .tlb = rsB .tlb ∧
            (∀ r, r ≠ 14#5 → r ≠ 15#5 → gprVal rs' r = gprVal rsB r) ∧
            gprVal rs' 15#5 = AxSpinAp9.a5j 64⌝ -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨.PHart cpu (.pure ()) rs' none ib', k + 65⟩ Ψ) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs none ib, k + 1 + j⟩ Ψ := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ m ih =>
  intro j hjn _ rs ib Hc HPC Htl Hkeep H15
  have hj : j < 64 := by omega
  obtain ⟨Hda, Hpa, Hhv⟩ := Hsc j hj
  have XR := XxReg (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ
    HΨmid
  have F0 := AxSpinAp8.FldMWFrame (hlc := hlc) (GF := GF) L GT nm HL Hcons i
    (AxSpinAp7.scanAddr j) 4 (k + 1 + j) (k + 1 + j + 1) (by
      intro k' lb aq rl m Hw Hlb Hid
      obtain rfl : k' = k + 1 + j := by omega
      rw [HR.2.2 j hj lb Hlb] at Hid
      cases Hid)
  rw [← Hpa] at F0
  have Hnormw : ∀ (lb : Lbl) (aq rl : Bool) (n : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k + 1 + j]? = some lb →
      aident lb = .IRmw aq rl (paZ (Pscan j)) n → n ≠ 4 := by
    intro lb aq rl n Hlb Hid
    rw [HR.2.2 j hj lb Hlb] at Hid
    cases Hid
  iintro K
  -- row end at the start of round j
  by_cases Ej : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1 + j
  · iclear K
    iapply (HΨend _ (by omega) (by omega) Ej _)
  ihave F := F0
  -- ---- + 0x74: c.lw a4,48(a5) (row k+1+j) ----
  iapply (AxSpinAp9.xxLdWG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
    _ rs (k + 1 + j) (pca 0x74) true 48#12 15#5 14#5 4 (AxSpinAp9.scanVa j) (Pscan j)
    (fun _ _ => iprop(True)) (retxRefl cpu rs (k + 1 + j) ib) Hc HPC
    (hitWSvpn rs (pca 0x74) (pca 0x44) (by decide) (hitWAgree rsB rs _ Htl Hhit))
    (atok74 σi T satp0 Htxt) (by decide) AxSpinAp9.vw4 (by decide) (by decide)
    (by rw [H15]; rfl) Hda (hitWAgree rsB rs _ Htl Hhv) Hnormw (by omega)) $$ F
  iintro %v %rs1 %ib1 %_ %HG1 %Hgv1 -
  -- row end right after round j's read
  by_cases Ej1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1 + j + 1
  · iclear K
    iapply (HΨend _ (by omega) (by omega) Ej1 _)
  have HF1 := stepRegs T satp0 _ rs _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pca 0x76 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rsB .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG1).trans Htl
  -- ---- + 0x76: beq a4,a3 — falls through (no collision) ----
  have Hcb : CertC (ctrlOkSW T satp0) rs1 (pca 0x76) false ap76 none none := by
    have h := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs1 (pca 0x76) false
      8166#13 13#5 14#5 .BEQ (by decide)
    have E14 : gval 14#5 rs1 = ldRes false 4 v := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs1 14#5 = _
      rw [HF1]
      ax_spin_ap9_zsimp
    have E13 : gval 13#5 rs1 = ldRes false 4 vs := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs1 13#5 = _
      rw [HF1]
      ax_spin_ap9_zsimp
      rw [Hkeep 13#5 (by decide) (by decide)]
      exact H13
    have Eot : brOt .BEQ 14#5 13#5 rs1 (pca 0x76 + sign_extend (m := 64) 8166#13) = none := by
      unfold brOt AxSymCtl2.bcond
      rw [E14, E13, beq_eq_false_iff_ne.mpr
        (fun h => Hncoll j hj v Hgv1 (AxSpinAp9.ldResInj _ _ h))]
      rfl
    rw [Eot] at h
    exact h
  iapply (XR _ rs1 (k + 1 + j + 1) (pca 0x76) false ap76 none none
    (retxRefl cpu rs1 (k + 1 + j + 1) ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (pca 0x76) (pca 0x44) (by decide) (hitWAgree rsB rs1 _ Htl1 Hhit))
    (atok76 σi T satp0 Htxt) trivial rfFAp76 Hcb (by omega))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pca 0x7a := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rsB .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- ---- + 0x7a: addi a5,a5,376 ----
  have Hca : CertC (ctrlOkSW T satp0) rs2 (pca 0x7a) false ap7a none
      (some (15#5, AxSpinAp9.a5j (j + 1))) := by
    have h := certAddi (ctrlOkSW T satp0) rs2 (pca 0x7a) false 15#5 15#5 376#12 (by decide)
    simp only [HF2] at h
    ax_spin_ap9_zsimp at h
    rw [H15, AxSpinAp9.a5jSucc] at h
    exact h
  iapply (XR _ rs2 (k + 1 + j + 1) (pca 0x7a) false ap7a none _
    (retxRefl cpu rs2 (k + 1 + j + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (pca 0x7a) (pca 0x44) (by decide) (hitWAgree rsB rs2 _ Htl2 Hhit))
    (atok7a σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFAp7a Hca (by omega))
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = pca 0x7e := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rsB .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have E15 : gval 15#5 rs3 = AxSpinAp9.a5j (j + 1) := by
    unfold gval
    rw [if_neg (by decide)]
    show gprVal rs3 15#5 = _
    rw [HF3]
    ax_spin_ap9_zsimp
  have E12 : gval 12#5 rs3 = AxSpinAp9.a5j 64 := by
    unfold gval
    rw [if_neg (by decide)]
    show gprVal rs3 12#5 = _
    rw [HF3]
    ax_spin_ap9_zsimp
    rw [Hkeep 12#5 (by decide) (by decide)]
    exact H12
  have Hkeep3 : ∀ r, r ≠ 14#5 → r ≠ 15#5 → gprVal rs3 r = gprVal rsB r := by
    intro r h14 h15
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.gprValZero _ r E0, AxSpinE8.gprValZero _ r E0]
    · rw [HF3]
      simp (disch := assumption) only [AxSpinE8.updOther]
      exact Hkeep r h14 h15
  have H15' : gprVal rs3 15#5 = AxSpinAp9.a5j (j + 1) := by
    rw [HF3]
    ax_spin_ap9_zsimp
  -- ---- + 0x7e: bne a5,a2 — loops back for j < 63 ----
  have hc := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs3 (pca 0x7e) false
    8182#13 12#5 15#5 .BNE (by decide)
  cases m with
  | zero =>
    obtain rfl : j = 63 := by omega
    have Eot : brOt .BNE 15#5 12#5 rs3 (pca 0x7e + sign_extend (m := 64) 8182#13) = none := by
      unfold brOt AxSymCtl2.bcond
      rw [E15, E12]
      simp
    rw [Eot] at hc
    iapply (XR _ rs3 (k + 1 + 63 + 1) (pca 0x7e) false ap7e none none
      (retxRefl cpu rs3 (k + 1 + 63 + 1) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
      (hitWSvpn rs3 (pca 0x7e) (pca 0x44) (by decide) (hitWAgree rsB rs3 _ Htl3 Hhit))
      (atok7e σi T satp0 Htxt) trivial rfFAp7e hc (by omega))
    iintro %rs4 %ib4 %HG4
    have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 (fun _ => rfl) HG4
    rw [show k + 1 + 63 + 1 = k + 65 by omega]
    iapply K $$ %rs4 %ib4
    ipureintro
    refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG4, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3,
      fun r h14 h15 => (HF4 r).trans (Hkeep3 r h14 h15), (HF4 _).trans H15'⟩
    rw [gbPc T satp0 _ _ _ _ _ _ HG4]
    decide
  | succ m' =>
    have Eot : brOt .BNE 15#5 12#5 rs3 (pca 0x7e + sign_extend (m := 64) 8182#13) =
        some (pca 0x74) := by
      unfold brOt AxSymCtl2.bcond
      rw [E15, E12, bne_iff_ne.mpr (AxSpinAp9.a5jNe (j + 1) (by omega))]
      simp only [↓reduceIte]
      congr 1
    rw [Eot] at hc
    iapply (XR _ rs3 (k + 1 + j + 1) (pca 0x7e) false ap7e (some (pca 0x74)) none
      (retxRefl cpu rs3 (k + 1 + j + 1) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
      (hitWSvpn rs3 (pca 0x7e) (pca 0x44) (by decide) (hitWAgree rsB rs3 _ Htl3 Hhit))
      (atok7e σi T satp0 Htxt) trivial rfFAp7e hc (by omega))
    iintro %rs4 %ib4 %HG4
    have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 (fun _ => rfl) HG4
    rw [show k + 1 + j + 1 = k + 1 + (j + 1) by omega]
    iapply (ih (j + 1) (by omega) (by omega) rs4 ib4 (gbCtrl T satp0 _ _ _ _ _ _ HG4)
      (gbPc T satp0 _ _ _ _ _ _ HG4) ((gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3)
      (fun r h14 h15 => (HF4 r).trans (Hkeep3 r h14 h15)) ((HF4 _).trans H15')) $$ K

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- (Lean-only) THE PID-COLLISION SCAN on a FULL row piece (stage-1 statement), the corollary of
`AxSpinAp9.scanLoopP`: under `k + 67 < LEN` the hook's end case is impossible. -/
theorem AxSpinAp9.scanLoop (k : Nat) (pnp ppid : Int)
    (HR : RowAllocpidBody k (AxOpsem.grow (gtAdGd GT) i) pnp ppid)
    (Hlen : k + 67 < (AxOpsem.grow (gtAdGd GT) i).length)
    (Pscan : Nat → BitVec 64) (rsB : RegFile) (vs : List (BitVec 8))
    (Hsc : ∀ j, j < 64 → dataAtS σi T (.Load .Data) (AxSpinAp9.scanVa j) 4 (Pscan j) ∧
      paZ (Pscan j) = AxSpinAp7.scanAddr j ∧ hitW rsB (AxSpinAp9.scanVa j))
    (Hhit : hitW rsB (pca 0x44))
    (Hncoll : ∀ j, j < 64 → ∀ v, graphValue (gtAdGd GT) (i, k + 1 + j) = some v →
      (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs)
    (H13 : gprVal rsB 13#5 = ldRes false 4 vs) (H12 : gprVal rsB 12#5 = AxSpinAp9.a5j 64) :
    ∀ n j, j + n = 64 → 0 < n → ∀ (rs : RegFile) (ib : Ibch),
      ctrlOkSW T satp0 rs → rs .PC = pca 0x74 → rs .tlb = rsB .tlb →
      (∀ r, r ≠ 14#5 → r ≠ 15#5 → gprVal rs r = gprVal rsB r) →
      gprVal rs 15#5 = AxSpinAp9.a5j j →
      ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
          ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x82 ∧ rs' .tlb = rsB .tlb ∧
            (∀ r, r ≠ 14#5 → r ≠ 15#5 → gprVal rs' r = gprVal rsB r) ∧
            gprVal rs' 15#5 = AxSpinAp9.a5j 64⌝ -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨.PHart cpu (.pure ()) rs' none ib', k + 65⟩ Ψ) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs none ib, k + 1 + j⟩ Ψ :=
  AxSpinAp9.scanLoopP (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    Hfix Htxt Ψ HΨmid k pnp ppid (AxSpinAp9.rowBodyPOfFull HR)
    (fun _ _ h2 h3 _ => absurd h3 (by omega)) Pscan rsB vs Hsc Hhit Hncoll H13 H12

/-! # 5. THE THEOREM -/

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- STAGE-2 P-FORM of Rocq `wpd_allocpid_cs` (retargeted, Q18): the inlined allocpid's critical-section body from
`allocproc + 0x44` (acquire's return) to `allocproc + 0x94` (`jal release`), at the joint instance
Ixv6, interrupts off, warm TLB.  Row piece `RowAllocpidBody k` (67 items: the nextpid read at
`k`, the 64 scan reads at `k + 1 + j`, the nextpid write at `k + 65`, the `p->pid` write at
`k + 66`); the continuation is at `k + 67`.  The normal path is pinned by value premises
(Q18b): the read pid is not 1000 and no scan read sees it.  The `p->pid` store flow `Opid` is
the caller's (Q18c).  PREFIX row (`RowAllocpidBodyP`, no length premise): a `by_cases` on
`LEN ≤ position` at each boundary where the row may end (`k`, `k + 1`, each scan round's start
and read in `AxSpinAp9.scanLoopP`, `k + 65`, `k + 66`, `k + 67`); every such end is discharged
by the WINDOWED, RESOURCE-FREE hook `HΨend` (window `[k, k + 67]`; the CS has no designated
cut).  The two premises naming position `k` that are not vacuous at an absent position
(`Hpo`, the anchor `e ∈ lobp (i, k)`) are GUARDED by `k < LEN`; the continuation is reached
only when `k + 67 < LEN`. -/
theorem wpdAllocpidCsP (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pnp Ppid : BitVec 64)
    (Pscan : Nat → BitVec 64) (e : Geid) (Opid : Nat → List (BitVec 8) → IProp GF) :
    -- the row
    RowAllocpidBodyP k (AxOpsem.grow (gtAdGd GT) i) (paZ Pnp) (paZ Ppid) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat), (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, paZ Pnp, m) → k' = k + 65) →
    (k < (AxOpsem.grow (gtAdGd GT) i).length → ∀ w a v', a ∈ npb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k)) →
    (∀ vs, graphValue (gtAdGd GT) (i, k) = some vs →
      (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32) →
    (∀ vs, graphValue (gtAdGd GT) (i, k) = some vs → ∀ j, j < 64 → ∀ v,
      graphValue (gtAdGd GT) (i, k + 1 + j) = some v →
      (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pca 0x44 → hitW rs0 (pca 0x44) →
    -- nextpid
    paZ Pnp = L.xlNp → ¬ L.xlText (paZ Pnp) →
    dataAtS σi T (.Load .Data) vaNp 4 Pnp → dataAtS σi T (.Store .Data) vaNp 4 Pnp →
    hitW rs0 vaNp →
    -- the scanned `proc[j].pid` fields
    (∀ j, j < 64 → dataAtS σi T (.Load .Data) (AxSpinAp9.scanVa j) 4 (Pscan j) ∧
      paZ (Pscan j) = AxSpinAp7.scanAddr j ∧ hitW rs0 (AxSpinAp9.scanVa j)) →
    -- `p->pid` (`s1 = p`)
    dataAtS σi T (.Store .Data) (gprVal rs0 9#5 + sign_extend (m := 64) 48#12) 4 Ppid →
    hitW rs0 (gprVal rs0 9#5 + sign_extend (m := 64) 48#12) →
    -- the anchor of `RNp`
    (k < (AxOpsem.grow (gtAdGd GT) i).length →
      e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k)) →
    -- the row-end hook (stage 2, design §B / Q-S2-2; windowed, resource-free)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 67 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ AxAnnot.annotOwn e (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ Ppid) 4) i
        Opid -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x94 ∧ rs' .tlb = rs0 .tlb ∧ vs.length = 4 ∧
          graphValue (gtAdGd GT) (i, k) = some vs ∧
          gprVal rs' 13#5 = ldRes false 4 vs ∧
          gprVal rs' 11#5 = AxSpinAp7.addiw1 (ldRes false 4 vs) ∧
          gprVal rs' 15#5 = a5v ∧
          gprVal rs' 10#5 = BitVec.ofNat 64 KernelSyms.«pid_lock» ∧
          gprVal rs' 12#5 = BitVec.ofNat 64 KernelSyms.«tickslock» ∧
          gprVal rs' 16#5 = BitVec.ofNat 64 1000 ∧
          (∀ r : BitVec 5, r.toNat ≠ 10 → r.toNat ≠ 11 → r.toNat ≠ 12 → r.toNat ≠ 13 →
            r.toNat ≠ 14 → r.toNat ≠ 15 → r.toNat ≠ 16 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k + 65) = some (WeakInterpProj.wbytes 4
            (@HAdd.hAdd (BitVec 32) (BitVec 32) (BitVec 32) _ (wordOfBytes 4 vs) one32)) ∧
          graphData (gtAdGd GT) (i, k + 66) = some (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs))⌝ -∗
        AxAnnot.annotOwn (i, k) iprop(⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝) -∗
        AxAnnot.annotOwn (i, k + 65) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k + 65)) -∗
        AxAnnot.annotOwn (i, k + 65) (FRAG nm (wordOfBytes 4 vs)) -∗
        Opid (k + 66) (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 67⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hone Hpo Hnowrap Hncoll Hc0 HPC0 Hhit0 Hnp Hntx HdaL HdaS Hhv Hsc HdaP HhvP He HΨend
  have XR := XxReg (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    Hfix Ψ HΨmid
  have XS := XxStF (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    Hfix Ψ HΨmid
  have Hkr : ∀ lb, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb → aident lb = .IRead false L.xlNp 4 := by
    intro lb Hlb
    rw [← Hnp]
    exact HR.2.1 lb Hlb
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iintro - - -
    iapply (HΨend _ (by omega) (by omega) E0 _)
  have FN := FldMWNp (hlc := hlc) (GF := GF) L GT nm HL Hcons i e k k (k + 1)
    (fun k' h hne => absurd (by omega) hne) Hkr (He (by omega)) (Hpo (by omega))
  rw [← Hnp] at FN
  iintro HRN Fpid C
  ihave F := FN $$ HRN
  -- ---- + 0x44: auipc a3,0x8 (row k) ----
  iapply (XR _ rs0 k (pca 0x44) false ap44 none (some (13#5, pca 0x44 + auipcOff 8#20))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0 Hhit0 (atok44 σi T satp0 Htxt)
    (AxSpinE8.owOkSome 13#5 _ (by decide)) rfFAp44
    (certAuipc _ rs0 (pca 0x44) false 13#5 8#20 (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pca 0x48 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- + 0x48: lw a3,1998(a3) — THE nextpid READ (row k) ----
  have Hnormw : ∀ (lb : Lbl) (aq rl : Bool) (n : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aident lb = .IRmw aq rl (paZ Pnp) n → n ≠ 4 := by
    intro lb aq rl n Hlb Hid
    rw [HR.2.1 lb Hlb] at Hid
    cases Hid
  iapply (AxSpinAp9.xxLdWG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
    _ rs1 k (pca 0x48) false 1998#12 13#5 13#5 4 vaNp Pnp (OLd L GT nm i e k)
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (pca 0x48) (pca 0x44) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (atok48 σi T satp0 Htxt) (by decide) AxSpinAp9.vw4 (by decide) (by decide)
    (by rw [HF1]; ax_spin_ap9_zsimp; rfl) HdaL (hitWAgree rs0 rs1 _ Htl1 Hhv) Hnormw
    (by omega)) $$ F
  iintro %vs %rs2 %ib2 %Hlvs %HG2 %Hgv
  rw [OLd, if_pos rfl]
  iintro ⟨HNP, Hsrc⟩
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear HNP Hsrc Fpid C
    iapply (HΨend _ (by omega) (by omega) E1 _)
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pca 0x4c := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  obtain ⟨Hn1000, Hnwr⟩ := Hnowrap vs Hgv
  -- ---- + 0x4c: li a6,1000 (k+1) ----
  have Hc3 : CertC (ctrlOkSW T satp0) rs2 (pca 0x4c) false ap4c none
      (some (16#5, BitVec.ofNat 64 1000)) := by
    have h := certAddi (ctrlOkSW T satp0) rs2 (pca 0x4c) false 0#5 16#5 1000#12 (by decide)
    simp only [HF2] at h
    ax_spin_ap9_zsimp at h
    rw [AxSpinAp9.li1000] at h
    exact h
  iapply (XR _ rs2 (k + 1) (pca 0x4c) false ap4c none _
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (pca 0x4c) (pca 0x44) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (atok4c σi T satp0 Htxt) (AxSpinE8.owOkSome 16#5 _ (by decide)) rfFAp4c Hc3 (by omega))
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = pca 0x50 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- + 0x50: c.li a0,1 (k+1) ----
  iapply (XR _ rs3 (k + 1) (pca 0x50) true ap50 none _
    (retxRefl cpu rs3 (k + 1) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (pca 0x50) (pca 0x44) (by decide) (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (atok50 σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp50
    (certAddi _ rs3 (pca 0x50) true (zero_extend (m := 5) 0b00#2) 10#5
      (sign_extend (m := 12) (1#6)) (by decide)) (by omega))
  iintro %rs4 %ib4 %HG4
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = pca 0x52 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- + 0x52: auipc a2,0x17 (k+1) ----
  iapply (XR _ rs4 (k + 1) (pca 0x52) false ap52 none (some (12#5, pca 0x52 + auipcOff 0x17#20))
    (retxRefl cpu rs4 (k + 1) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (pca 0x52) (pca 0x44) (by decide) (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (atok52 σi T satp0 Htxt) (AxSpinE8.owOkSome 12#5 _ (by decide)) rfFAp52
    (certAuipc _ rs4 (pca 0x52) false 12#5 0x17#20 (by decide)) (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = pca 0x56 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x56: addi a2,a2,-1172 (a2 = &proc[NPROC]) (k+1) ----
  have Hc6 : CertC (ctrlOkSW T satp0) rs5 (pca 0x56) false ap56 none
      (some (12#5, AxSpinAp9.a5j 64)) := by
    have h := certAddi (ctrlOkSW T satp0) rs5 (pca 0x56) false 12#5 12#5 0xb6c#12 (by decide)
    simp only [HF5] at h
    ax_spin_ap9_zsimp at h
    rw [AxSpinAp9.a5j64] at h
    exact h
  iapply (XR _ rs5 (k + 1) (pca 0x56) false ap56 none _
    (retxRefl cpu rs5 (k + 1) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (pca 0x56) (pca 0x44) (by decide) (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (atok56 σi T satp0 Htxt) (AxSpinE8.owOkSome 12#5 _ (by decide)) rfFAp56 Hc6 (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = pca 0x5a := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- + 0x5a: c.j +0x62 (k+1) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs6 (pca 0x5a) true ap5a (some (pca 0x62)) none := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs6 (pca 0x5a) true
      (sign_extend (m := 21) (4#11 +++ 0#1)) (zero_extend (m := 5) 0b00#2) (by decide)
    rw [show pca 0x5a + sign_extend (m := 64) (sign_extend (m := 21) (4#11 +++ 0#1)) = pca 0x62
      by decide, linkOwZero _ _ (by decide)] at h
    exact h
  iapply (XR _ rs6 (k + 1) (pca 0x5a) true ap5a (some (pca 0x62)) none
    (retxRefl cpu rs6 (k + 1) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (pca 0x5a) (pca 0x44) (by decide) (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (atok5a σi T satp0 Htxt) trivial rfFAp5a Hcj (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs0 T satp0 _ rs6 _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = pca 0x62 := gbPc T satp0 _ _ _ _ _ _ HG7
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- + 0x62: c.mv a1,a0 (k+1) ----
  iapply (XR _ rs7 (k + 1) (pca 0x62) true ap62 none _
    (retxRefl cpu rs7 (k + 1) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (pca 0x62) (pca 0x44) (by decide) (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (atok62 σi T satp0 Htxt) (AxSpinE8.owOkSome 11#5 _ (by decide)) rfFAp62
    (certAdd _ rs7 (pca 0x62) true 10#5 (zero_extend (m := 5) 0b00#2) 11#5 (by decide))
    (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = pca 0x64 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- + 0x64: beq a3,a6 — falls through (pid ≠ 1000) (k+1) ----
  have Hcb : CertC (ctrlOkSW T satp0) rs8 (pca 0x64) false ap64 none none := by
    have h := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs8 (pca 0x64) false
      8#13 16#5 13#5 .BEQ (by decide)
    have E13 : gval 13#5 rs8 = ldRes false 4 vs := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs8 13#5 = _
      rw [HF8]
      ax_spin_ap9_zsimp
    have E16 : gval 16#5 rs8 = 0#64 + sign_extend (m := 64) 1000#12 := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs8 16#5 = _
      rw [HF8]
      ax_spin_ap9_zsimp
      exact AxSpinAp9.li1000.symm
    have Eot : brOt .BEQ 13#5 16#5 rs8 (pca 0x64 + sign_extend (m := 64) 8#13) = none := by
      unfold brOt AxSymCtl2.bcond
      rw [E13, E16, beq_eq_false_iff_ne.mpr (AxSpinAp9.ldResNe1000 vs Hn1000)]
      rfl
    rw [Eot] at h
    exact h
  iapply (XR _ rs8 (k + 1) (pca 0x64) false ap64 none none
    (retxRefl cpu rs8 (k + 1) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (pca 0x64) (pca 0x44) (by decide) (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (atok64 σi T satp0 Htxt) trivial rfFAp64 Hcb (by omega))
  iintro %rs9 %ib9 %HG9
  have HF9 := stepRegs0 T satp0 _ rs8 _ _ _ rs9 HF8 HG9
  have HPC9 : rs9 .PC = pca 0x68 := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
  have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
  -- ---- + 0x68: addiw a1,a3,1 (k+1) ----
  have Hc10 : CertC (ctrlOkSW T satp0) rs9 (pca 0x68) false ap68 none
      (some (11#5, AxSpinAp7.addiw1 (ldRes false 4 vs))) := by
    have h := certAddiw (ctrlOkSW T satp0) rs9 (pca 0x68) false 13#5 11#5 1#12 (by decide)
    simp only [HF9] at h
    ax_spin_ap9_zsimp at h
    exact h
  iapply (XR _ rs9 (k + 1) (pca 0x68) false ap68 none _
    (retxRefl cpu rs9 (k + 1) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
    (hitWSvpn rs9 (pca 0x68) (pca 0x44) (by decide) (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (atok68 σi T satp0 Htxt) (AxSpinE8.owOkSome 11#5 _ (by decide)) rfFAp68 Hc10 (by omega))
  iintro %rs10 %ib10 %HG10
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 HF9 HG10
  have HPC10 : rs10 .PC = pca 0x6c := by rw [gbPc T satp0 _ _ _ _ _ _ HG10]; decide
  have Htl10 : rs10 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9
  -- ---- + 0x6c: auipc a5,0x11 (k+1) ----
  iapply (XR _ rs10 (k + 1) (pca 0x6c) false ap6c none (some (15#5, pca 0x6c + auipcOff 17#20))
    (retxRefl cpu rs10 (k + 1) ib10) (gbCtrl T satp0 _ _ _ _ _ _ HG10) HPC10
    (hitWSvpn rs10 (pca 0x6c) (pca 0x44) (by decide) (hitWAgree rs0 rs10 _ Htl10 Hhit0))
    (atok6c σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFAp6c
    (certAuipc _ rs10 (pca 0x6c) false 15#5 17#20 (by decide)) (by omega))
  iintro %rs11 %ib11 %HG11
  have HF11 := stepRegs T satp0 _ rs10 _ _ _ _ _ rs11 HF10 HG11
  have HPC11 : rs11 .PC = pca 0x70 := by rw [gbPc T satp0 _ _ _ _ _ _ HG11]; decide
  have Htl11 : rs11 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG11).trans Htl10
  -- ---- + 0x70: addi a5,a5,-686 (a5 = proc) (k+1) ----
  have Hc12 : CertC (ctrlOkSW T satp0) rs11 (pca 0x70) false ap70 none
      (some (15#5, AxSpinAp9.a5j 0)) := by
    have h := certAddi (ctrlOkSW T satp0) rs11 (pca 0x70) false 15#5 15#5 0xd52#12 (by decide)
    simp only [HF11] at h
    ax_spin_ap9_zsimp at h
    rw [AxSpinAp9.a5j0] at h
    exact h
  iapply (XR _ rs11 (k + 1) (pca 0x70) false ap70 none _
    (retxRefl cpu rs11 (k + 1) ib11) (gbCtrl T satp0 _ _ _ _ _ _ HG11) HPC11
    (hitWSvpn rs11 (pca 0x70) (pca 0x44) (by decide) (hitWAgree rs0 rs11 _ Htl11 Hhit0))
    (atok70 σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFAp70 Hc12 (by omega))
  iintro %rs12 %ib12 %HG12
  have HF12 := stepRegs T satp0 _ rs11 _ _ _ _ _ rs12 HF11 HG12
  have HPC12 : rs12 .PC = pca 0x74 := by rw [gbPc T satp0 _ _ _ _ _ _ HG12]; decide
  have Htl12 : rs12 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG12).trans Htl11
  -- ---- the scan (+ 0x74 .. + 0x7e, rows k+1 .. k+64) ----
  have H13 : gprVal rs12 13#5 = ldRes false 4 vs := by rw [HF12]; ax_spin_ap9_zsimp
  have H12 : gprVal rs12 12#5 = AxSpinAp9.a5j 64 := by rw [HF12]; ax_spin_ap9_zsimp
  have H15 : gprVal rs12 15#5 = AxSpinAp9.a5j 0 := by rw [HF12]; ax_spin_ap9_zsimp
  have SL := AxSpinAp9.scanLoopP (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid
    hppn i cpu Hfix Htxt Ψ HΨmid k (paZ Pnp) (paZ Ppid) HR HΨend Pscan rs12 vs
    (fun j hj => ⟨(Hsc j hj).1, (Hsc j hj).2.1, hitWAgree rs0 rs12 _ Htl12 (Hsc j hj).2.2⟩)
    (hitWAgree rs0 rs12 _ Htl12 Hhit0) (Hncoll vs Hgv) H13 H12 64 0 rfl (by omega) rs12 ib12
    (gbCtrl T satp0 _ _ _ _ _ _ HG12) HPC12 rfl (fun _ _ _ => rfl) H15
  rw [Nat.add_zero] at SL
  iapply SL
  iintro %rs13 %ib13 %⟨Hc13, HPC13, Htl13', Hkeep13, H15_13⟩
  have Htl13 : rs13 .tlb = rs0 .tlb := Htl13'.trans Htl12
  -- row end at k + 65 (after the scan)
  by_cases E65 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 65
  · iclear HNP Hsrc Fpid C
    iapply (HΨend _ (by omega) (by omega) E65 _)
  -- ---- + 0x82: auipc a5,0x8 (k+65) ----
  iapply (XR _ rs13 (k + 65) (pca 0x82) false ap82 none (some (15#5, pca 0x82 + auipcOff 8#20))
    (retxRefl cpu rs13 (k + 65) ib13) Hc13 HPC13
    (hitWSvpn rs13 (pca 0x82) (pca 0x44) (by decide) (hitWAgree rs0 rs13 _ Htl13 Hhit0))
    (atok82 σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFAp82
    (certAuipc _ rs13 (pca 0x82) false 15#5 8#20 (by decide)) (by omega))
  iintro %rs14 %ib14 %HG14
  have HF14 := stepRegs T satp0 _ rs13 _ _ _ _ _ rs14 (fun _ => rfl) HG14
  have HPC14 : rs14 .PC = pca 0x86 := by rw [gbPc T satp0 _ _ _ _ _ _ HG14]; decide
  have Htl14 : rs14 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG14).trans Htl13
  -- ---- + 0x86: sw a1,1936(a5) — THE nextpid WRITE (k+65) ----
  have E11 : gprVal rs14 11#5 = AxSpinAp7.addiw1 (ldRes false 4 vs) := by
    rw [HF14]
    ax_spin_ap9_zsimp
    rw [Hkeep13 11#5 (by decide) (by decide), HF12]
    ax_spin_ap9_zsimp
  obtain ⟨lb0, Hlb0, _⟩ := AxSpinAp9.bRdP k _ _ _ HR (by omega)
  have P1 := AxSpinAp9.rdLoad (gtAdGd GT) i k L.xlNp vs Hkr ⟨lb0, Hlb0⟩ Hgv
  have P2 : ∀ (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlNp, m) → k' = k + 65 := by
    intro k' lb rl m Hlb Hid
    rw [← Hnp] at Hid
    exact Hone k' lb rl m Hlb Hid
  have P3 : ∃ vw cls, (AxOpsem.grow (gtAdGd GT) i)[k + 65]? = some (.LStore false L.xlNp vw cls) ∧
      vw.length = 4 := by
    rw [← Hnp]
    exact AxSpinAp9.bWrP k _ _ _ HR (by omega)
  have FS := FstMNp (hlc := hlc) (GF := GF) L GT nm HL Hcons i k (k + 65) (wordOfBytes 4 vs)
    (by omega) P1 P2 P3 Hnwr
  rw [← Hnp] at FS
  ihave FSn := FS $$ HNP
  iapply (XS _ rs14 (k + 65) (pca 0x86) false 1936#12 11#5 15#5 4 vaNp Pnp
    (OSt L GT nm i (k + 65) (wordOfBytes 4 vs))
    (retxRefl cpu rs14 (k + 65) ib14) (gbCtrl T satp0 _ _ _ _ _ _ HG14) HPC14
    (hitWSvpn rs14 (pca 0x86) (pca 0x44) (by decide) (hitWAgree rs0 rs14 _ Htl14 Hhit0))
    (atok86 σi T satp0 Htxt) AxSpinAp9.vw4 (by decide) (by decide)
    (by rw [HF14]; ax_spin_ap9_zsimp; exact AxSpinAp9.a5vVaNp.symm) HdaS
    (hitWAgree rs0 rs14 _ Htl14 Hhv) (by omega)) $$ FSn
  iintro %rs15 %ib15 %HG15 %Hgd65
  rw [E11, npBytes] at Hgd65
  rw [E11, npBytes, OSt, if_pos ⟨rfl, rfl⟩]
  iintro ⟨HRN65, HFR⟩
  have HF15 := stepRegs0 T satp0 _ rs14 _ _ _ rs15 HF14 HG15
  have HPC15 : rs15 .PC = pca 0x8a := by rw [gbPc T satp0 _ _ _ _ _ _ HG15]; decide
  have Htl15 : rs15 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG15).trans Htl14
  rw [show k + 65 + 1 = k + 66 by omega]
  -- row end at k + 66
  by_cases E66 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 66
  · iclear HRN65 HFR Hsrc Fpid C
    iapply (HΨend _ (by omega) (by omega) E66 _)
  -- ---- + 0x8a: c.sw a3,48(s1) — the `p->pid` WRITE (k+66) ----
  have E9 : gprVal rs15 9#5 = gprVal rs0 9#5 := by
    rw [HF15]
    ax_spin_ap9_zsimp
    rw [Hkeep13 9#5 (by decide) (by decide), HF12]
    ax_spin_ap9_zsimp
  have E13 : gprVal rs15 13#5 = ldRes false 4 vs := by
    rw [HF15]
    ax_spin_ap9_zsimp
    rw [Hkeep13 13#5 (by decide) (by decide)]
    exact H13
  iapply (XS _ rs15 (k + 66) (pca 0x8a) true 48#12 13#5 9#5 4
    (gprVal rs0 9#5 + sign_extend (m := 64) 48#12) Ppid Opid
    (retxRefl cpu rs15 (k + 66) ib15) (gbCtrl T satp0 _ _ _ _ _ _ HG15) HPC15
    (hitWSvpn rs15 (pca 0x8a) (pca 0x44) (by decide) (hitWAgree rs0 rs15 _ Htl15 Hhit0))
    (atok8a σi T satp0 Htxt) AxSpinAp9.vw4 (by decide) (by decide)
    (by rw [E9]) HdaP (hitWAgree rs0 rs15 _ Htl15 HhvP) (by omega)) $$ Fpid
  iintro %rs16 %ib16 %HG16 %Hgd66
  rw [E13, AxSpinAp9.st4Ld] at Hgd66
  rw [E13, AxSpinAp9.st4Ld]
  iintro HOp
  have HF16 := stepRegs0 T satp0 _ rs15 _ _ _ rs16 HF15 HG16
  have HPC16 : rs16 .PC = pca 0x8c := by rw [gbPc T satp0 _ _ _ _ _ _ HG16]; decide
  have Htl16 : rs16 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG16).trans Htl15
  rw [show k + 66 + 1 = k + 67 by omega]
  -- row end at k + 67 (the continuation is reached only when `k + 67 < LEN`)
  by_cases E67 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 67
  · iclear HOp HRN65 HFR Hsrc C
    iapply (HΨend _ (by omega) (by omega) E67 _)
  -- ---- + 0x8c: auipc a0,0x11 (k+67) ----
  iapply (XR _ rs16 (k + 67) (pca 0x8c) false ap8c none (some (10#5, pca 0x8c + auipcOff 17#20))
    (retxRefl cpu rs16 (k + 67) ib16) (gbCtrl T satp0 _ _ _ _ _ _ HG16) HPC16
    (hitWSvpn rs16 (pca 0x8c) (pca 0x44) (by decide) (hitWAgree rs0 rs16 _ Htl16 Hhit0))
    (atok8c σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp8c
    (certAuipc _ rs16 (pca 0x8c) false 10#5 17#20 (by decide)) (by omega))
  iintro %rs17 %ib17 %HG17
  have HF17 := stepRegs T satp0 _ rs16 _ _ _ _ _ rs17 HF16 HG17
  have HPC17 : rs17 .PC = pca 0x90 := by rw [gbPc T satp0 _ _ _ _ _ _ HG17]; decide
  have Htl17 : rs17 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG17).trans Htl16
  -- ---- + 0x90: addi a0,a0,-1790 (a0 = &pid_lock) (k+67) ----
  have Hc18 : CertC (ctrlOkSW T satp0) rs17 (pca 0x90) false ap90 none
      (some (10#5, BitVec.ofNat 64 KernelSyms.«pid_lock»)) := by
    have h := certAddi (ctrlOkSW T satp0) rs17 (pca 0x90) false 10#5 10#5 0x902#12 (by decide)
    simp only [HF17] at h
    ax_spin_ap9_zsimp at h
    rw [show pca 0x8c + auipcOff 17#20 + sign_extend (m := 64) 0x902#12 =
      BitVec.ofNat 64 KernelSyms.«pid_lock» from a0vPidLock] at h
    exact h
  iapply (XR _ rs17 (k + 67) (pca 0x90) false ap90 none _
    (retxRefl cpu rs17 (k + 67) ib17) (gbCtrl T satp0 _ _ _ _ _ _ HG17) HPC17
    (hitWSvpn rs17 (pca 0x90) (pca 0x44) (by decide) (hitWAgree rs0 rs17 _ Htl17 Hhit0))
    (atok90 σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFAp90 Hc18 (by omega))
  iintro %rs' %ib' %HG'
  have HF' := stepRegs T satp0 _ rs17 _ _ _ _ _ rs' HF17 HG'
  have Hkeep : ∀ r : BitVec 5, r.toNat ≠ 10 → r.toNat ≠ 11 → r.toNat ≠ 12 → r.toNat ≠ 13 →
      r.toNat ≠ 14 → r.toNat ≠ 15 → r.toNat ≠ 16 → gprVal rs' r = gprVal rs0 r := by
    intro r H10 H11 H12' H13' H14 H15' H16
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.gprValZero _ r E0, AxSpinE8.gprValZero _ r E0]
    · have n10 : r ≠ 10#5 := fun h => H10 (by rw [h]; rfl)
      have n11 : r ≠ 11#5 := fun h => H11 (by rw [h]; rfl)
      have n12 : r ≠ 12#5 := fun h => H12' (by rw [h]; rfl)
      have n13 : r ≠ 13#5 := fun h => H13' (by rw [h]; rfl)
      have n14 : r ≠ 14#5 := fun h => H14 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => H15' (by rw [h]; rfl)
      have n16 : r ≠ 16#5 := fun h => H16 (by rw [h]; rfl)
      have A : gprVal rs' r = gprVal rs13 r := by
        rw [HF']
        simp (disch := assumption) only [AxSpinE8.updOther]
      have B : gprVal rs12 r = gprVal rs0 r := by
        rw [HF12]
        simp (disch := assumption) only [AxSpinE8.updOther]
      rw [A, Hkeep13 r n14 n15, B]
  have Hfin : ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x94 ∧ rs' .tlb = rs0 .tlb ∧ vs.length = 4 ∧
      graphValue (gtAdGd GT) (i, k) = some vs ∧
      gprVal rs' 13#5 = ldRes false 4 vs ∧
      gprVal rs' 11#5 = AxSpinAp7.addiw1 (ldRes false 4 vs) ∧
      gprVal rs' 15#5 = a5v ∧
      gprVal rs' 10#5 = BitVec.ofNat 64 KernelSyms.«pid_lock» ∧
      gprVal rs' 12#5 = BitVec.ofNat 64 KernelSyms.«tickslock» ∧
      gprVal rs' 16#5 = BitVec.ofNat 64 1000 ∧
      (∀ r : BitVec 5, r.toNat ≠ 10 → r.toNat ≠ 11 → r.toNat ≠ 12 → r.toNat ≠ 13 →
        r.toNat ≠ 14 → r.toNat ≠ 15 → r.toNat ≠ 16 → gprVal rs' r = gprVal rs0 r) ∧
      graphData (gtAdGd GT) (i, k + 65) = some (WeakInterpProj.wbytes 4
        (@HAdd.hAdd (BitVec 32) (BitVec 32) (BitVec 32) _ (wordOfBytes 4 vs) one32)) ∧
      graphData (gtAdGd GT) (i, k + 66) = some (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs)) := by
    refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG', ?_, (gbTlb T satp0 _ _ _ _ _ _ HG').trans Htl17,
      Hlvs, Hgv, ?_, ?_, ?_, ?_, ?_, ?_, Hkeep, Hgd65, Hgd66⟩
    · rw [gbPc T satp0 _ _ _ _ _ _ HG']
      decide
    · rw [HF']
      ax_spin_ap9_zsimp
      rw [Hkeep13 13#5 (by decide) (by decide)]
      exact H13
    · rw [HF']
      ax_spin_ap9_zsimp
      rw [Hkeep13 11#5 (by decide) (by decide), HF12]
      ax_spin_ap9_zsimp
    · rw [HF']
      ax_spin_ap9_zsimp
      rfl
    · rw [HF']
      ax_spin_ap9_zsimp
    · rw [HF']
      ax_spin_ap9_zsimp
      rw [Hkeep13 12#5 (by decide) (by decide)]
      exact H12.trans AxSpinAp9.a5jTickslock
    · rw [HF']
      ax_spin_ap9_zsimp
      rw [Hkeep13 16#5 (by decide) (by decide), HF12]
      ax_spin_ap9_zsimp
  iapply C $$ %vs %rs' %ib' %Hfin Hsrc HRN65 HFR HOp


set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- Rocq `wpd_allocpid_cs` (retargeted, Q18), stage-1 statement on a FULL row piece: the
corollary of `wpdAllocpidCsP` (`RowAllocpidBody ⇒ RowAllocpidBodyP`; the guards are discharged
unconditionally; under `k + 67 < LEN` the hook's end case is impossible). -/
theorem wpdAllocpidCs (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pnp Ppid : BitVec 64)
    (Pscan : Nat → BitVec 64) (e : Geid) (Opid : Nat → List (BitVec 8) → IProp GF) :
    -- the row
    RowAllocpidBody k (AxOpsem.grow (gtAdGd GT) i) (paZ Pnp) (paZ Ppid) →
    k + 67 < (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (m : Nat), (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, paZ Pnp, m) → k' = k + 65) →
    (∀ w a v', a ∈ npb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k) → gmoLt (gtAdGd GT).gdG w (i, k)) →
    (∀ vs, graphValue (gtAdGd GT) (i, k) = some vs →
      (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32) →
    (∀ vs, graphValue (gtAdGd GT) (i, k) = some vs → ∀ j, j < 64 → ∀ v,
      graphValue (gtAdGd GT) (i, k + 1 + j) = some v →
      (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pca 0x44 → hitW rs0 (pca 0x44) →
    -- nextpid
    paZ Pnp = L.xlNp → ¬ L.xlText (paZ Pnp) →
    dataAtS σi T (.Load .Data) vaNp 4 Pnp → dataAtS σi T (.Store .Data) vaNp 4 Pnp →
    hitW rs0 vaNp →
    -- the scanned `proc[j].pid` fields
    (∀ j, j < 64 → dataAtS σi T (.Load .Data) (AxSpinAp9.scanVa j) 4 (Pscan j) ∧
      paZ (Pscan j) = AxSpinAp7.scanAddr j ∧ hitW rs0 (AxSpinAp9.scanVa j)) →
    -- `p->pid` (`s1 = p`)
    dataAtS σi T (.Store .Data) (gprVal rs0 9#5 + sign_extend (m := 64) 48#12) 4 Ppid →
    hitW rs0 (gprVal rs0 9#5 + sign_extend (m := 64) 48#12) →
    -- the anchor of `RNp`
    e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k) →
    ⊢ AxAnnot.annotOwn e (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) e) -∗
      @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ Ppid) 4) i
        Opid -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pca 0x94 ∧ rs' .tlb = rs0 .tlb ∧ vs.length = 4 ∧
          graphValue (gtAdGd GT) (i, k) = some vs ∧
          gprVal rs' 13#5 = ldRes false 4 vs ∧
          gprVal rs' 11#5 = AxSpinAp7.addiw1 (ldRes false 4 vs) ∧
          gprVal rs' 15#5 = a5v ∧
          gprVal rs' 10#5 = BitVec.ofNat 64 KernelSyms.«pid_lock» ∧
          gprVal rs' 12#5 = BitVec.ofNat 64 KernelSyms.«tickslock» ∧
          gprVal rs' 16#5 = BitVec.ofNat 64 1000 ∧
          (∀ r : BitVec 5, r.toNat ≠ 10 → r.toNat ≠ 11 → r.toNat ≠ 12 → r.toNat ≠ 13 →
            r.toNat ≠ 14 → r.toNat ≠ 15 → r.toNat ≠ 16 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k + 65) = some (WeakInterpProj.wbytes 4
            (@HAdd.hAdd (BitVec 32) (BitVec 32) (BitVec 32) _ (wordOfBytes 4 vs) one32)) ∧
          graphData (gtAdGd GT) (i, k + 66) = some (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs))⌝ -∗
        AxAnnot.annotOwn (i, k) iprop(⌜npSrc (gtAdGd GT).gdG L (i, k) e⌝) -∗
        AxAnnot.annotOwn (i, k + 65) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, k + 65)) -∗
        AxAnnot.annotOwn (i, k + 65) (FRAG nm (wordOfBytes 4 vs)) -∗
        Opid (k + 66) (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 67⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hlen Hone Hpo Hnowrap Hncoll Hc0 HPC0 Hhit0 Hnp Hntx HdaL HdaS Hhv Hsc HdaP HhvP He
  exact wpdAllocpidCsP (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    Hfix Htxt Ψ HΨmid k rs0 ib0 Pnp Ppid Pscan e Opid (AxSpinAp9.rowBodyPOfFull HR) Hone
    (fun _ => Hpo) Hnowrap Hncoll Hc0 HPC0 Hhit0 Hnp Hntx HdaL HdaS Hhv Hsc HdaP HhvP (fun _ => He)
    (fun _ _ h2 h3 _ => absurd h3 (by omega))

end cs

end Weak
