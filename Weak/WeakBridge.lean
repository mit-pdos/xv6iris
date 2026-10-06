/-
Weak: **the pinned-fragment transfer bridge** (M2b, item 0): ONE lemma family
that makes every `Weak.exec`-level fact (`Weak/Exec.lean`, `Weak/ExecLib.lean`,
and through `execOfRunRW` every MachCSL walk equation) reusable on the weak side.

Rocq: `iris/WeakBridge.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  A weak state `s : Wmstate` projects to an SC
state `wflatSt s` -- registers and devices verbatim, memory the COHERENT flat
view `WeakLang.wflat` of image + log (byte `a` holds what its latest write
wrote, `wflatLookup`).  On the fragment of runs where every read is FORCED to
that latest value, `wexec` over `s` and `exec` over `wflatSt s` are the same
run, and every existing leaf transfers.  A read is forced when
- the access is EXCLUSIVE/ATOMIC (`akLatest`, the AMO read half): its
  admissibility IS `WeakMem.latest`, so it is pinned with no ownership at all;
- the byte is PINNED in `s` (`pinnedRead`): the hart's own index covers the
  latest write to it -- what owning an `↦w` at the hart's index gives (§9),
  and `WeakMem.readableLatestPin` turns it into "every admissible timestamp is
  THE latest one";
- the byte has NEVER BEEN WRITTEN in this era (`latestTs = 0`, all kernel text
  and rodata): pinned unconditionally (`pinnedReadUnwritten`).
`pinnedExec` mirrors `wexec`'s recursion and collects exactly the per-ACCESS side
conditions: the read footprint's pinnedness (only where the access kind does
not already force it) and the wrap-freedom `accWf` of every RAM access.  The
two directions: `execOfWexecPinned` (wexec ⟹ exec, the CONSUMPTION direction:
a leaf handed a `wexec` fact at an oracle it did not choose identifies the
post-state by `exec`'s functionality) and `wexecOfExecPinned` (exec ⟹ ∃ oracle,
wexec, the REDUCIBILITY direction); `wexecPinnedAgree` packages both.  §11 merges
`pinnedExec` with `WeakExec.mchoiceFree` into `wstepOk`, and `wexecLeafAgree` is
the one lemma a leaf applies.

**O2: the i-cache fetch (owner decision, route (a), 2026-10-06).**  Rocq's
`ak_pins ak = ak_coh || ak_latest` let a coherent read (fetch/walker, dead for
rv64d) through for free: its admissibility WAS `latest`.  Under O2 an
`akIfetch` read is the i-cache read (`WeakInterp` header): byte `a` may return
any `t` with no write to `a` in `(t, max t itv]`, a stale value when `itv` lags.
So the fetch is NOT forced by its kind; it is forced by THE FETCH PIN
`fetchPinned s a := latestTs s.wmLog a ≤ s.wmItv` (the instruction view covers
the latest write), under which every admissible fetch timestamp IS `latestTs`
(`wbyteOkPinned`'s ifetch case).  Kernel text (`latestTs = 0`) satisfies it
unconditionally (`fetchPinnedUnwritten`), so the fetch/decode path stays on the
pinned fragment for free, as in Rocq.  `akPins ak := !akIfetch && akLatest`
(an exclusive i-cache read is not a kind the model emits; it would read through
the i-cache window, which `akLatest` does not constrain), and the per-byte
obligation is `readPinned s ak a := if akIfetch then fetchPinned else pinnedRead`.

**Deviations from Rocq.**
1. NAMES: lowerCamelCase (`Weak/WeakMem.lean` deviation 1).  File-qualified
   (duplicated-name rule): `WeakBridge.seqCons`.
2. STATE: `wflatSt s : ExecSt := ⟨s.wmRegs, wflatMem s.wmImg s.wmLog, s.wmDev⟩`
   (Rocq `MState (wm_regs s) (wflat …) (wm_dev s)`), with
   `wflatMem img log : BMap := fun a => get? (wflat img log) a` (Exec's flat
   memory is MachCSL's function-map `BMap`; `WeakLang.wflat` is an `ExtTreeMap`).
   `read_bytes`/`write_bytes` are `bmRead`/`bmWrite`; `set_reg` is
   `ExecSt.setReg`; Rocq `MState r m d` updates are `ExecSt.setDev`/`setMem`.
   The agreement conclusions `mem t0 = wflat …` read
   `wflatMem s'.wmImg s'.wmLog = t0.mem`.
3. O2 (above): `akPins` is `!akIfetch && akLatest` (Rocq `ak_coh || ak_latest`);
   the read-arm obligation of `pinnedExec`/`wstepOk`/`wreadPinnedTs` is
   `readPinned` (Rocq `pinned_read`), whose i-cache case is the fetch pin.
   Lean's `wexec` consumes the oracle at EVERY RAM read (WeakInterp deviation 8),
   so the Rocq `ak_coh` case splits in the bridge proofs are gone.
4. THE MMIO TEST is `mmioAcc pa n` (Exec deviation 2; WeakInterp deviation 11),
   Rocq `dev_addr pa`, in `pinnedExec`/`wstepOk` as in `wexec`/`exec`.
5. WRITE ARMS: answers `.Ok (some true)` (owner decision; Rocq `inl None`); the
   write value is `req.value : Option _` (WeakInterp deviation 6), so the write
   arms of `pinnedExec`/`wstepOk` match on it like `wexec` (`none`: `True`,
   both interpreters are stuck), and the device arm quantifies over `d'` only.
6. `wflatWrite` / `wflatStWritePost` take `accWf pa n` (Rocq: none).  Rocq's
   `write_bytes` is a `foldr` (byte 0 inserted last, wins) and `bytes_map` a
   left-biased chain, which agree even on a wrapping access; MachCSL's `bmWrite`
   is a `foldl` (the LAST byte wins), so the two maps agree only when the `n`
   addresses are distinct, i.e. without wrap.  Every use is under the arm's
   `accWf` already.
7. The Rocq address-seam helpers: `bv_unsigned_mword_of_int` ↦
   `bvUnsignedMwordOfInt` (`(zPa z).toNat = (z % 2^64).toNat`, Lean's
   `BitVec.ofInt`); `seq_cons`/`mapM_seq_ext` are over `List.range'`;
   `bytes_map_union_foldr` ↦ `bytesMapUnionFoldr`, restated pointwise (the
   message map in the union against `bmWrite`, under `accWf`, deviation 6).
8. The Iris connector (§9) is stated at `wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
   vwpHold P σ.wmWs -∗ ⌜…⌝` (Rocq: the curried wand `wlat_interp … -∗ vwp_hold …
   -∗ ⌜…⌝`).
9. §10: Rocq's ITYPE/ADDI `Example` is the theorem `wexecExecuteITYPEADDI`,
   over `ExecLib.execExecuteITYPEADDI` (Rocq `ExecCommon.exec_execute_ITYPE_ADDI`);
   `add_vec a (sign_extend' 64 imm)` ↦ `a + sign_extend (m := 64) imm`.
10. `wflatStWs` is stated for `wsetWs`; Lean-only `wflatStBarrier` covers Stage
   B's `wbarrierPost` (data views and `wmItv`, both invisible to `wflatSt`).

**Rocq → Lean name map.**  `bv_unsigned_mword_of_int` `bvUnsignedMwordOfInt`,
`z_pa_acc_addr` `zPaAccAddr`, `acc_wf` `accWf`, `acc_wf_byte` `accWfByte`,
`acc_wf_msg` `accWfMsg`, `wflat_st` `wflatSt`, `wflat_st_regs/dev/mem`
`wflatStRegs/Dev/Mem`, `wflat_st_ws` `wflatStWs`, `wflat_st_dev_set`
`wflatStDevSet`, `wflat_st_reg_set` `wflatStRegSet`, `pinned_read`
`pinnedRead`, `pinned_read_unwritten` `pinnedReadUnwritten`, `ak_pins`
`akPins`, `wbyte_flat` `wbyteFlat`, `wbyte_read_latest_ts`
`wbyteReadLatestTs`, `wflat_byte` `wflatByte`, `wbyte_ok_pinned`
`wbyteOkPinned`, `seq_cons` `WeakBridge.seqCons`, `mapM_seq_ext` `mapMSeqExt`,
`wread_bytes_read_bytes` `wreadBytesReadBytes`, `bytes_map_union_foldr`
`bytesMapUnionFoldr`, `wflat_write` `wflatWrite`, `wflat_write_wf`
`wflatWriteWf`, `pinned_exec` `pinnedExec`, `wread_pinned_ts`
`wreadPinnedTs`, `wflat_st_read_post` `wflatStReadPost`, `wflat_st_write_post`
`wflatStWritePost`, `wlog_wf_read_post` `wlogWfReadPost`,
`exec_of_wexec_pinned` `execOfWexecPinned`, `wexec_of_exec_pinned`
`wexecOfExecPinned`, `wexec_pinned_agree` `wexecPinnedAgree`,
`wexec_pinned_wlog_wf` `wexecPinnedWlogWf`, `wpt_pinned_read`
`wptPinnedRead`, `wpt_own_h_pinned_read` `wptOwnHPinnedRead`,
`wpt_img_pinned_read` `wptImgPinnedRead`, `wpt_pinned_acc` `wptPinnedAcc`,
`wexec_execute_ITYPE_ADDI` `wexecExecuteITYPEADDI`, `wstep_ok` `wstepOk`,
`wstep_ok_pinned` `wstepOkPinned`, `wrun_wexec_wstep_ok` `wrunWexecWstepOk`,
`wstep_ok_covers` `wstepOkCovers`, `wexec_leaf_agree` `wexecLeafAgree`.
Lean-only: `wflatMem`, `fetchPinned`, `fetchPinnedUnwritten`, `readPinned`,
`readPinnedUnwritten`, `wflatStBarrier`, `bmReadAssemble`, `bmReadNone`,
`mapMAssembleBmRead`, `bmFoldLookup`, `bmWriteLookup`, `wwriteMsgByteAt`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakExec
import Weak.WeakVProp
import Weak.ExecLib

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The address seam, in the direction the bridge needs -/

/-- Rocq `bv_unsigned_mword_of_int`: Lean's `zPa` is `BitVec.ofInt`. -/
theorem bvUnsignedMwordOfInt (z : Int) : (zPa z).toNat = (z % ((2 ^ 64 : Nat) : Int)).toNat := by
  simp only [zPa, BitVec.toNat_ofInt]

/-- `zPa` of the additive address IS the model's `pa + j`, unconditionally. -/
theorem zPaAccAddr (a : PAddr) (j : Nat) : zPa (WeakInterp.accAddr a j) = a + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [zPa, WeakInterp.accAddr, paZ, BitVec.toNat_ofInt, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.reducePow]
  omega

/-- Rocq `acc_wf`: the access does not wrap the address space. -/
def accWf (pa : PAddr) (n : Nat) : Prop := paZ pa + (n : Int) ≤ 18446744073709551616

theorem accWfByte (pa : PAddr) (n j : Nat) :
    accWf pa n → j < n → paZ (pa + BitVec.ofNat 64 j) = WeakInterp.accAddr pa j := by
  intro hwf hj
  apply paZAdd
  unfold accWf at hwf
  omega

/-- The messages a wrap-free write appends are well-formed. -/
theorem accWfMsg (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    accWf pa n → wmsgWf (wwriteMsg tid k pa n v) :=
  wwriteMsgWf tid k pa n v

/-! ## 2. The flat projection of a weak state, and the pinned predicate -/

/-- The coherent flat memory, as `exec`'s byte map (deviation 2). -/
def wflatMem (img : Mem) (log : List Wmsg) : BMap := fun a => get? (wflat img log) a

/-- Rocq `wflat_st`: the SC state a weak state projects to. -/
def wflatSt (s : Wmstate) : ExecSt := ⟨s.wmRegs, wflatMem s.wmImg s.wmLog, s.wmDev⟩

theorem wflatStRegs (s : Wmstate) : (wflatSt s).regs = s.wmRegs := rfl
theorem wflatStDev (s : Wmstate) : (wflatSt s).dev = s.wmDev := rfl
theorem wflatStMem (s : Wmstate) : (wflatSt s).mem = wflatMem s.wmImg s.wmLog := rfl

theorem wflatStWs (s : Wmstate) (ws : Wstate) : wflatSt (wsetWs s ws) = wflatSt s := rfl
theorem wflatStDevSet (s : Wmstate) (d : DevStates) : wflatSt (wsetDev s d) = (wflatSt s).setDev d := rfl
theorem wflatStRegSet (s : Wmstate) (r : Register) (v : RegisterType r) :
    wflatSt (wsetReg s r v) = (wflatSt s).setReg r v := rfl
/-- Stage B's barrier post-state moves only what the projection does not see. -/
theorem wflatStBarrier (s : Wmstate) (b : barrier_kind) : wflatSt (wbarrierPost s b) = wflatSt s := rfl

/-- THE PINNED PREDICATE (Rocq `pinned_read`): the hart's own index
`wVrNew ⊔ coh(a)` covers the latest write to `a`. -/
def pinnedRead (s : Wmstate) (a : Int) : Prop :=
  latestTs s.wmLog a ≤ max s.wmWs.wVrNew (coh s.wmWs a)

/-- A byte no message has ever written is pinned for free. -/
theorem pinnedReadUnwritten (s : Wmstate) (a : Int) : latestTs s.wmLog a = 0 → pinnedRead s a := by
  intro h; unfold pinnedRead; rw [h]; omega

/-- THE FETCH PIN (O2): the instruction view covers the latest write to `a`. -/
def fetchPinned (s : Wmstate) (a : Int) : Prop := latestTs s.wmLog a ≤ s.wmItv

/-- Text (never written) is fetch-pinned at every instruction view. -/
theorem fetchPinnedUnwritten (s : Wmstate) (a : Int) : latestTs s.wmLog a = 0 → fetchPinned s a := by
  intro h; unfold fetchPinned; rw [h]; omega

/-- Rocq `ak_pins`, under O2: only a non-i-cache exclusive read forces the latest
write by its kind (deviation 3). -/
def akPins (ak : AkInfo) : Bool := !ak.akIfetch && ak.akLatest

/-- The per-byte read obligation: the fetch pin for an i-cache read, the hart's
index pin otherwise. -/
def readPinned (s : Wmstate) (ak : AkInfo) (a : Int) : Prop :=
  if ak.akIfetch then fetchPinned s a else pinnedRead s a

theorem readPinnedUnwritten (s : Wmstate) (ak : AkInfo) (a : Int) :
    latestTs s.wmLog a = 0 → readPinned s ak a := by
  intro h
  unfold readPinned
  split
  · exact fetchPinnedUnwritten s a h
  · exact pinnedReadUnwritten s a h

/-! ## 3. One byte: the weak read IS the flat lookup -/

/-- Rocq `wbyte_flat`: the byte the flat projection holds, in the log's vocabulary. -/
def wbyteFlat (s : Wmstate) (a : Int) : Option (BitVec 8) :=
  logByte (wimg s) s.wmLog (latestTs s.wmLog a) a

/-- THE LATEST TIMESTAMP IS ALWAYS ADMISSIBLE, at every access kind (the i-cache
window included): nothing above it writes `a` at all. -/
theorem wbyteReadLatestTs (s : Wmstate) (ak : AkInfo) (a : Int) :
    wbyteRead s ak a (latestTs s.wmLog a) = wbyteFlat s a := by
  have hclip : ∀ hi, writesInb s.wmLog a (latestTs s.wmLog a) hi = false := fun hi =>
    (notWritesInb _ _ _ _).2 fun hw =>
      latestTsTop s.wmLog a (writesInMonoHi _ _ _ _ _ (Nat.min_le_right _ _) (writesInClip _ _ _ _ hw))
  unfold wbyteRead wbyteOkb wbyteFlat
  cases hv : logByte (wimg s) s.wmLog (latestTs s.wmLog a) a with
  | none => simp
  | some b =>
    have hrd : readableb (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs ak.akSync) a (latestTs s.wmLog a) = true := by
      unfold readableb; rw [hv]; simp [hclip]
    cases ak.akIfetch <;> cases ak.akLatest <;> simp [hclip, hrd]

/-- ... and the flat lookup IS that byte, on a wrap-free access. -/
theorem wflatByte (s : Wmstate) (pa : PAddr) (n j : Nat) :
    wlogWf s.wmLog → accWf pa n → j < n →
    wflatMem s.wmImg s.wmLog (pa + BitVec.ofNat 64 j) = wbyteFlat s (WeakInterp.accAddr pa j) := by
  intro hwf hacc hj
  unfold wflatMem wbyteFlat wimg
  rw [wflatLookup _ _ _ hwf, accWfByte pa n j hacc hj]

/-- THE PINNING STEP: with the byte pinned (or the kind forcing the latest read),
an admissible timestamp can only be `latestTs`.  O2: the i-cache case is the
fetch pin. -/
theorem wbyteOkPinned (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    (akPins ak = false → readPinned s ak a) → wbyteOk s ak a t b → t = latestTs s.wmLog a := by
  rintro hpin ⟨hv, hadm⟩
  have hts : (logByte (wimg s) s.wmLog t a).isSome := by rw [hv]; rfl
  have hlat : latest (wimg s) s.wmLog a (latestTs s.wmLog a) :=
    latestTsLatest _ _ _ (latestTsSome _ _ a t hts)
  cases hc : ak.akIfetch with
  | true =>
    have hp : fetchPinned s a := by
      have := hpin (by simp [akPins, hc])
      simpa [readPinned, hc] using this
    rw [hc] at hadm
    simp only [↓reduceIte] at hadm
    obtain ⟨hLs, hLtop⟩ := hlat
    unfold fetchPinned at hp
    apply Classical.byContradiction
    intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hadm ((writesInLogByte (wimg s) _ a t _).2 ⟨_, hlt, by omega, hLs⟩)
    · exact hLtop ((writesInLogByte (wimg s) _ a _ _).2 ⟨t, hgt, logByteBounded _ _ t a hts, hts⟩)
  | false =>
    rw [hc] at hadm
    simp only [Bool.false_eq_true, ↓reduceIte] at hadm
    obtain ⟨hrd, hlt⟩ := hadm
    cases hl : ak.akLatest with
    | true => exact (latestTsEq _ _ _ _ ⟨hts, hlt hl⟩).symm
    | false =>
      have hp : pinnedRead s a := by
        have := hpin (by simp [akPins, hc, hl])
        simpa [readPinned, hc] using this
      unfold pinnedRead at hp
      have := loadVpreVrNew s.wmWs ak.akSync
      exact readableLatestPin _ _ _ _ _ _ _ hlat (by omega) hrd

/-! ## 4. A whole access: the read arm and the write arm -/

/-- Rocq `seq_cons`, over `List.range'`. -/
theorem WeakBridge.seqCons (k n : Nat) : List.range' k (n + 1) = k :: List.range' (k + 1) n := rfl

/-- Rocq `mapM_seq_ext`: `mapM` over a range only looks at the range. -/
theorem mapMSeqExt {A : Type} (f g : Nat → Option A) (k n : Nat) :
    (∀ j, k ≤ j → j < k + n → f j = g j) → (List.range' k n).mapM f = (List.range' k n).mapM g := by
  induction n generalizing k with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [WeakBridge.seqCons, List.mapM_cons, List.mapM_cons, h k (Nat.le_refl _) (by omega),
      ih (k + 1) (fun j h1 h2 => h j (by omega) (by omega))]

/-- A map that holds every byte of the footprint reads the assembled word. -/
theorem bmReadAssemble (mm : BMap) (pa : PAddr) :
    ∀ (n : Nat) (g : Nat → BitVec 8), (∀ j, j < n → mm (pa + BitVec.ofNat 64 j) = some (g j)) →
      bmRead mm pa n = some (assembleBytes n g)
  | 0, _, _ => rfl
  | n + 1, g, h => by
    simp only [bmRead]
    rw [bmReadAssemble mm pa n g (fun j hj => h j (by omega)), h n (by omega)]
    rfl

/-- A missing byte sticks the read. -/
theorem bmReadNone (mm : BMap) (pa : PAddr) (n j : Nat) :
    j < n → mm (pa + BitVec.ofNat 64 j) = none → bmRead mm pa n = none := by
  intro hj hn
  cases h : bmRead mm pa n with
  | none => rfl
  | some w =>
    have := bmRead_spec mm pa n w h j hj
    rw [hn] at this
    cases this

/-- `wreadBytes`' gather-and-assemble IS `bmRead`, byte function for byte function. -/
theorem mapMAssembleBmRead (mm : BMap) (pa : PAddr) (n : Nat) :
    (match (List.range' 0 n).mapM (fun j => mm (pa + BitVec.ofNat 64 j)) with
     | some bs => some (assembleBytes n (fun j => bs[j]?.getD 0))
     | none => none) = bmRead mm pa n := by
  by_cases hall : ∀ j, j < n → (mm (pa + BitVec.ofNat 64 j)).isSome = true
  · let g : Nat → BitVec 8 := fun j => (mm (pa + BitVec.ofNat 64 j)).getD 0
    have hg : ∀ j, j < n → mm (pa + BitVec.ofNat 64 j) = some (g j) := fun j hj => by
      have := hall j hj
      simp only [g]
      cases h : mm (pa + BitVec.ofNat 64 j) with
      | none => rw [h] at this; cases this
      | some b => rfl
    have hm : (List.range' 0 n).mapM (fun j => mm (pa + BitVec.ofNat 64 j)) =
        some ((List.range' 0 n).map g) :=
      mapM_Some_2 (forall2MapOfForall _ fun j hj => hg j (by rw [List.mem_range'_1] at hj; omega))
    rw [hm, bmReadAssemble mm pa n g hg]
    simp only [Option.some.injEq]
    apply bvEqOfBytes
    intro j hj
    rw [nthByteAssembleBytes n _ j hj, nthByteAssembleBytes n _ j hj, List.getElem?_map]
    simp [hj]
  · have hex : ∃ j, j < n ∧ mm (pa + BitVec.ofNat 64 j) = none := by
      apply Classical.byContradiction
      intro hne
      apply hall
      intro j hj
      cases h : mm (pa + BitVec.ofNat 64 j) with
      | none => exact absurd ⟨j, hj, h⟩ hne
      | some b => rfl
    obtain ⟨j, hj, hn⟩ := hex
    rw [bmReadNone mm pa n j hj hn]
    cases hm : (List.range' 0 n).mapM (fun j => mm (pa + BitVec.ofNat 64 j)) with
    | none => rfl
    | some bs =>
      exfalso
      have hF := mapM_Some_1 hm
      have hseq : (List.range' 0 n)[j]? = some j := by simp [hj]
      obtain ⟨b, _, hb⟩ := Forall2_lookup_l hF hseq
      rw [hn] at hb
      cases hb

/-- THE READ ARM: at the coherent timestamps the weak read and the flat read are
the SAME partial function. -/
theorem wreadBytesReadBytes (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) :
    wlogWf s.wmLog → accWf pa n →
    wreadBytes s ak pa n (cohTs s pa n) = bmRead (wflatMem s.wmImg s.wmLog) pa n := by
  intro hwf hacc
  unfold wreadBytes
  rw [if_pos (cohTsLength s pa n)]
  rw [mapMSeqExt (fun j => wbyteRead s ak (WeakInterp.accAddr pa j) (cohTs s pa n)[j]!)
      (fun j => wflatMem s.wmImg s.wmLog (pa + BitVec.ofNat 64 j)) 0 n (fun j _ hj => by
        rw [cohTsLookup s pa n j (by omega), wbyteReadLatestTs, wflatByte s pa n j hwf hacc (by omega)])]
  exact mapMAssembleBmRead _ pa n

/-- `bmWrite`, pointwise, on a non-wrapping footprint. -/
theorem bmFoldLookup (mm : BMap) (pa : PAddr) (g : Nat → BitVec 8) (a : PAddr) :
    ∀ m, m ≤ 18446744073709551616 →
      ((List.range m).foldl (fun mm' j => bmSet mm' (pa + BitVec.ofNat 64 j) (g j)) mm) a =
        if (a - pa).toNat < m then some (g (a - pa).toNat) else mm a
  | 0, _ => by simp
  | m + 1, hm => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [bmSet]
    rw [bmFoldLookup mm pa g a m (by omega)]
    have key : a = pa + BitVec.ofNat 64 m ↔ (a - pa).toNat = m := by
      constructor
      · rintro rfl
        have := pa.isLt
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
        omega
      · intro h
        apply BitVec.eq_of_toNat_eq
        have := pa.isLt
        have := a.isLt
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at h ⊢
        omega
    by_cases h : a = pa + BitVec.ofNat 64 m
    · have hd : (a - pa).toNat = m := key.1 h
      rw [if_pos h, if_pos (by omega), hd]
    · have hd : (a - pa).toNat ≠ m := fun e => h (key.2 e)
      rw [if_neg h]
      by_cases h2 : (a - pa).toNat < m
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem bmWriteLookup (mm : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (a : PAddr) :
    n ≤ 18446744073709551616 →
    bmWrite mm pa n w a = if (a - pa).toNat < n then some (nthByte w (a - pa).toNat) else mm a := by
  intro hn
  unfold bmWrite
  exact bmFoldLookup mm pa (nthByte w) a n hn

/-- The written message, read at a machine address. -/
theorem wwriteMsgByteAt (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
    (a : PAddr) : accWf pa n →
    msgByte (wwriteMsg tid k pa n v) (paZ a) =
      if (a - pa).toNat < n then some (nthByte v (a - pa).toNat) else none := by
  intro hacc
  unfold accWf at hacc
  have hpa := pa.isLt
  have ha := a.isLt
  have hsub : (a - pa).toNat = (2 ^ 64 - pa.toNat + a.toNat) % 2 ^ 64 := BitVec.toNat_sub a pa
  simp only [Nat.reducePow] at hsub
  simp only [msgByte, wwriteMsg, paZ] at hacc ⊢
  generalize (a - pa).toNat = d at hsub ⊢
  by_cases h1 : (pa.toNat : Int) ≤ (a.toNat : Int)
  · rw [if_pos h1]
    have e : ((a.toNat : Int) - (pa.toNat : Int)).toNat = d := by omega
    rw [e, List.getElem?_map]
    by_cases h2 : d < n
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]; simp [h2]
  · rw [if_neg h1, if_neg (by omega)]

/-- Rocq `bytes_map_union_foldr`, pointwise (deviation 7): the message map laid over
the flat memory IS `bmWrite`, on a wrap-free access. -/
theorem bytesMapUnionFoldr (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
    (mm : GMapF PAddr (BitVec 8)) (a : PAddr) : accWf pa n →
    get? (PartialMap.union (msgMap (wwriteMsg tid k pa n v)) mm) a =
      bmWrite (fun b => get? mm b) pa n v a := by
  intro hacc
  have hn : n ≤ 18446744073709551616 := by
    have := WeakInterp.paZRange pa; unfold accWf at hacc; omega
  rw [bmWriteLookup _ _ _ _ _ hn]
  have hm := msgMapLookup (wwriteMsg tid k pa n v) a (accWfMsg tid k pa n v hacc)
  rw [wwriteMsgByteAt tid k pa n v a hacc] at hm
  by_cases hd : (a - pa).toNat < n
  · rw [if_pos hd] at hm ⊢
    exact flatUnionSomeL hm
  · rw [if_neg hd] at hm ⊢
    exact flatUnionR hm

/-- THE WRITE ARM: appending the message and overwriting the flat map are the
same map (deviation 6: under `accWf`). -/
theorem wflatWrite (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : accWf pa n →
    wflatMem s.wmImg (wwritePost tid s ak pa n v).wmLog = bmWrite (wflatMem s.wmImg s.wmLog) pa n v := by
  intro hacc
  funext a
  rw [wwritePostLog]
  show get? (wflat s.wmImg (s.wmLog ++ _)) a = _
  rw [wflatApp]
  exact bytesMapUnionFoldr tid _ pa n v _ a hacc

/-- ... and the log stays `wflat`-describable. -/
theorem wflatWriteWf (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : wlogWf s.wmLog → accWf pa n → wlogWf (wwritePost tid s ak pa n v).wmLog := by
  intro hwf hacc
  rw [wwritePostLog]
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact hwf m h
  · rw [List.mem_singleton] at h
    subst h
    exact accWfMsg tid _ pa n v hacc

/-! ## 5. `pinnedExec`: the run predicate

The side conditions of a WHOLE run, collected along `wexec`'s own recursion.  Per
RAM access: wrap-freedom, and -- only where the access kind does not already
force the latest read -- pinnedness of the read footprint (O2: the fetch pin at
an i-cache read).  The successor states are the CANONICAL ones (reads at
`cohTs`); §3 says the actual run cannot use any others. -/

def pinnedExec (tid : Option Nat) {X : Type} : SailM X → Wmstate → Prop
  | .pure _, _ => True
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => pinnedExec tid (k (s.wmRegs r)) s
    | .regWrite r v, k => pinnedExec tid (k PUnit.unit) (wsetReg s r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        ∀ w d', devRead s.wmDev req.pa n = some (w, d') →
          pinnedExec tid (k (.Ok (w, none))) (wsetDev s d')
      else
        accWf req.pa n ∧
        (akPins (classify req.access_kind) = false →
          ∀ j, j < n → readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j)) ∧
        (∀ w, wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w →
          pinnedExec tid (k (.Ok (w, none)))
            (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)))
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          ∀ d', devWrite s.wmDev req.pa n v = some d' →
            pinnedExec tid (k (.Ok (some true))) (wsetDev s d')
        | none => True
      else
        accWf req.pa n ∧
        (match req.value with
         | some v =>
           pinnedExec tid (k (.Ok (some true))) (wwritePost tid s (classify req.access_kind) req.pa n v)
         | none => True)
    | .barrier b, k => pinnedExec tid (k ()) (wbarrierPost s b)
    | .instrAnnounce _ _, k => pinnedExec tid (k ()) s
    | .branchAnnounce _ _, k => pinnedExec tid (k ()) s
    | .cacheOp _, k => pinnedExec tid (k ()) s
    | .tlbi _, k => pinnedExec tid (k ()) s
    | .takeException _, k => pinnedExec tid (k ()) s
    | .returnException _, k => pinnedExec tid (k ()) s
    | .translationStart _, k => pinnedExec tid (k ()) s
    | .translationEnd _, k => pinnedExec tid (k ()) s
    | .cycleCount, k => pinnedExec tid (k ()) s
    | .message _, k => pinnedExec tid (k ()) s
    | .getCycleCount, k => pinnedExec tid (k (0 : Nat)) s
    -- choose / the legacy direct-RAM events: both interpreters are stuck
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- THE TIMESTAMP-COLLAPSE STEP, at a whole access: the oracle has NO freedom. -/
theorem wreadPinnedTs (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    (akPins ak = false → ∀ j, j < n → readPinned s ak (WeakInterp.accAddr pa j)) →
    wreadOk s ak pa n ts w → ts = cohTs s pa n := by
  rintro hpin ⟨hlen, hbytes⟩
  apply List.ext_getElem (by rw [hlen, cohTsLength])
  intro j h1 h2
  have hj : j < n := by omega
  have := wbyteOkPinned s ak _ _ _ (fun hp => hpin hp j hj) (hbytes j hj)
  rw [getBangLt _ _ h1] at this
  rw [this, ← cohTsLookup s pa n j hj, getBangLt _ _ h2]

/-- The post-state projections the induction needs. -/
theorem wflatStReadPost (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    wflatSt (wreadPost s ak pa ts) = wflatSt s := by
  unfold wreadPost; split <;> rfl

theorem wflatStWritePost (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : accWf pa n →
    wflatSt (wwritePost tid s ak pa n v) = (wflatSt s).setMem (bmWrite (wflatSt s).mem pa n v) := by
  intro hacc
  show (⟨s.wmRegs, wflatMem s.wmImg (wwritePost tid s ak pa n v).wmLog, s.wmDev⟩ : ExecSt) =
    ⟨s.wmRegs, bmWrite (wflatMem s.wmImg s.wmLog) pa n v, s.wmDev⟩
  rw [wflatWrite tid s ak pa n v hacc]

theorem wlogWfReadPost (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    wlogWf s.wmLog → wlogWf (wreadPost s ak pa ts).wmLog := by
  intro h; rw [wreadPostLog]; exact h

/-! ## 6. THE BRIDGE, direction 1: `wexec` ⟹ `exec` (the CONSUMPTION direction) -/

theorem execOfWexecPinned (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ s, pinnedExec tid m s → wlogWf s.wmLog →
    ∀ χ x s' χ', wexec tid m χ s = some (x, s', χ') → exec m (wflatSt s) = some (x, wflatSt s') := by
  induction m with
  | pure y =>
    intro s _ _ χ x s' χ' h
    simp only [wexec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  | impure call k ih =>
    intro s hp hwf χ x s' χ' h
    cases call with
    | error e => simp [wexec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [pinnedExec] at hp
        simp only [wexec] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hp h
          rw [execMemReadDev n va req k _ hd, wflatStDev]
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at h
            exact ih _ _ (hp w0 d' hdr) hwf _ _ _ _ h
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hp h
          rw [execMemRead n va req k _ hd', wflatStMem]
          obtain ⟨hacc, hpin, hk⟩ := hp
          cases hχ : χ.head? with
          | none => rw [hχ] at h; cases h
          | some ts =>
            simp only [hχ] at h
            cases hrb : wreadBytes s (classify req.access_kind) req.pa n ts with
            | none => rw [hrb] at h; cases h
            | some w0 =>
              rw [hrb] at h
              have hts := wreadPinnedTs s _ req.pa n ts w0 hpin (wreadBytesSpec _ _ _ _ _ _ hrb)
              subst hts
              have hiex := ih _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf) _ _ _ _ h
              rw [wflatStReadPost] at hiex
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc] at hrb
              rw [hrb]
              exact hiex
      case memWrite n va req =>
        simp only [pinnedExec] at hp
        simp only [wexec] at h
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd, hv] at h
          · simp [hd, hv] at h
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hp h
            simp only [hv] at hp h
            rw [execMemWriteDev n va req k _ v hv hd, wflatStDev]
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at h; cases h
            | some d' =>
              rw [hdw] at h
              exact ih _ _ (hp d' hdw) hwf _ _ _ _ h
          · have hd' : mmioAcc req.pa n = false := by simpa using hd
            rw [if_neg hd] at hp h
            simp only [hv] at hp h
            obtain ⟨hacc, hp⟩ := hp
            rw [execMemWrite n va req k _ v hv hd']
            have hiex := ih _ _ hp (wflatWriteWf _ _ _ _ _ _ hwf hacc) _ _ _ _ h
            rw [wflatStWritePost _ _ _ _ _ _ hacc] at hiex
            exact hiex
      all_goals first
        | (simp only [wexec, reduceCtorEq] at h; done)
        | (simp only [pinnedExec] at hp
           simp only [wexec] at h
           exact ih _ _ hp hwf _ _ _ _ h)

/-! ## 7. THE BRIDGE, direction 2: `exec` ⟹ `wexec` (the REDUCIBILITY direction) -/

theorem wexecOfExecPinned (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ s, pinnedExec tid m s → wlogWf s.wmLog →
    ∀ x t', exec m (wflatSt s) = some (x, t') →
      ∃ χ s' χ', wexec tid m χ s = some (x, s', χ') ∧ wflatSt s' = t' := by
  induction m with
  | pure y =>
    intro s _ _ x t' h
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], s, [], rfl, rfl⟩
  | impure call k ih =>
    intro s hp hwf x t' h
    cases call with
    | error e => simp [exec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [pinnedExec] at hp
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hp
          rw [execMemReadDev n va req k _ hd, wflatStDev] at h
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ (hp w0 d' hdr) hwf _ _ h
            exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hdr]; exact hw, heq⟩
        · have hd' : mmioAcc req.pa n = false := by simpa using hd
          rw [if_neg hd] at hp
          obtain ⟨hacc, _, hk⟩ := hp
          rw [execMemRead n va req k _ hd', wflatStMem] at h
          cases hbr : bmRead (wflatMem s.wmImg s.wmLog) req.pa n with
          | none => rw [hbr] at h; cases h
          | some w0 =>
            rw [hbr] at h
            have hrb : wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w0 := by
              rw [wreadBytesReadBytes s _ req.pa n hwf hacc, hbr]
            have h2 : exec (k (.Ok (w0, none)))
                (wflatSt (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n))) =
                some (x, t') := by
              rw [wflatStReadPost]; exact h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf) _ _ h2
            exact ⟨cohTs s req.pa n :: χ, s2, χ',
              by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hw, heq⟩
      case memWrite n va req =>
        simp only [pinnedExec] at hp
        cases hv : req.value with
        | none =>
          simp only [exec, hv] at h
          cases h
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hp
            simp only [hv] at hp
            rw [execMemWriteDev n va req k _ v hv hd, wflatStDev] at h
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at h; cases h
            | some d' =>
              rw [hdw] at h
              obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ (hp d' hdw) hwf _ _ h
              exact ⟨χ, s2, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hw, heq⟩
          · have hd' : mmioAcc req.pa n = false := by simpa using hd
            rw [if_neg hd] at hp
            simp only [hv] at hp
            obtain ⟨hacc, hp⟩ := hp
            rw [execMemWrite n va req k _ v hv hd'] at h
            have h2 : exec (k (.Ok (some true)))
                (wflatSt (wwritePost tid s (classify req.access_kind) req.pa n v)) = some (x, t') := by
              rw [wflatStWritePost _ _ _ _ _ _ hacc]; exact h
            obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ hp (wflatWriteWf _ _ _ _ _ _ hwf hacc) _ _ h2
            exact ⟨χ, s2, χ', by simp only [wexec, if_neg hd, hv]; exact hw, heq⟩
      all_goals first
        | (simp only [exec, reduceCtorEq] at h; done)
        | (simp only [pinnedExec] at hp
           obtain ⟨χ, s2, χ', hw, heq⟩ := ih _ _ hp hwf _ _ h
           exact ⟨χ, s2, χ', by simp only [wexec]; exact hw, heq⟩)

/-! ## 8. What the leaf applies -/

/-- The two directions packaged against ONE `exec` fact: on the pinned fragment the
weak machine can step, and every way it steps agrees with the SC run on the value,
the registers, the devices and the (flat) memory. -/
theorem wexecPinnedAgree (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) (x0 : X)
    (t0 : ExecSt) :
    pinnedExec tid m s → wlogWf s.wmLog →
    exec m (wflatSt s) = some (x0, t0) →
    (∃ χ s0 χ', wexec tid m χ s = some (x0, s0, χ')) ∧
    (∀ χ x s' χ', wexec tid m χ s = some (x, s', χ') →
      x = x0 ∧ s'.wmRegs = t0.regs ∧ s'.wmDev = t0.dev ∧ wflatMem s'.wmImg s'.wmLog = t0.mem) := by
  intro hp hwf hex
  refine ⟨?_, ?_⟩
  · obtain ⟨χ, s0, χ', hw, _⟩ := wexecOfExecPinned tid m s hp hwf x0 t0 hex
    exact ⟨χ, s0, χ', hw⟩
  · intro χ x s' χ' hw
    have hex' := execOfWexecPinned tid m s hp hwf χ x s' χ' hw
    rw [hex] at hex'
    simp only [Option.some.injEq, Prod.mk.injEq] at hex'
    obtain ⟨hx, ht⟩ := hex'
    subst hx ht
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The log stays `wflat`-describable across a pinned run. -/
theorem wexecPinnedWlogWf (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ s, pinnedExec tid m s → wlogWf s.wmLog →
    ∀ χ x s' χ', wexec tid m χ s = some (x, s', χ') → wlogWf s'.wmLog := by
  induction m with
  | pure y =>
    intro s _ hwf χ x s' χ' h
    simp only [wexec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact hwf
  | impure call k ih =>
    intro s hp hwf χ x s' χ' h
    cases call with
    | error e => simp [wexec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [pinnedExec] at hp
        simp only [wexec] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hp h
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at h
            exact ih _ _ (hp w0 d' hdr) hwf _ _ _ _ h
        · rw [if_neg hd] at hp h
          obtain ⟨_, hpin, hk⟩ := hp
          cases hχ : χ.head? with
          | none => rw [hχ] at h; cases h
          | some ts =>
            simp only [hχ] at h
            cases hrb : wreadBytes s (classify req.access_kind) req.pa n ts with
            | none => rw [hrb] at h; cases h
            | some w0 =>
              rw [hrb] at h
              have hts := wreadPinnedTs s _ req.pa n ts w0 hpin (wreadBytesSpec _ _ _ _ _ _ hrb)
              subst hts
              exact ih _ _ (hk w0 hrb) (wlogWfReadPost _ _ _ _ hwf) _ _ _ _ h
      case memWrite n va req =>
        simp only [pinnedExec] at hp
        simp only [wexec] at h
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd, hv] at h
          · simp [hd, hv] at h
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hp h
            simp only [hv] at hp h
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at h; cases h
            | some d' =>
              rw [hdw] at h
              exact ih _ _ (hp d' hdw) hwf _ _ _ _ h
          · rw [if_neg hd] at hp h
            simp only [hv] at hp h
            obtain ⟨hacc, hp⟩ := hp
            exact ih _ _ hp (wflatWriteWf _ _ _ _ _ _ hwf hacc) _ _ _ _ h
      all_goals first
        | (simp only [wexec, reduceCtorEq] at h; done)
        | (simp only [pinnedExec] at hp
           simp only [wexec] at h
           exact ih _ _ hp hwf _ _ _ _ h)

/-! ## 9. The connector: OWNERSHIP ⟹ PINNEDNESS

A byte owned at the hart's index is pinned: the `γlat` element IS the latest write
(`WeakGhost.wlatLookup`) and the points-to's receipt says the hart's floor covers
its timestamp (`WeakVProp.wpt_at`).  An ERA-IMAGE byte (`wptImg`, timestamp 0) is
pinned -- and fetch-pinned, `fetchPinnedUnwritten` -- with no receipt at all. -/

section connector
variable {GF : BundledGFunctors} [WeakGS GF]

theorem wptPinnedRead (σ : Wmstate) (a : Int) (dq : DFrac) (v : BitVec 8) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (a ↦w{dq} v : VProp GF) σ.wmWs -∗ ⌜pinnedRead σ a⌝ := by
  iintro Hi Hpt
  icases (wpt_at a dq v σ.wmWs).mp $$ Hpt with ⟨%t, He, %ht⟩
  ihave %hlat := wlatLookup σ.wmImg σ.wmLog a dq t v $$ [Hi He]
  · iframe Hi He
  ipureintro
  unfold pinnedRead
  rw [latestValTs _ _ _ _ _ hlat]
  rw [flr_wsView] at ht
  exact ht

/-- The OWNED (C-or-D) form. -/
theorem wptOwnHPinnedRead (c : CPU) (σ : Wmstate) (a : Int) (v : BitVec 8) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wptOwnH (GF := GF) c a v) σ.wmWs -∗ ⌜pinnedRead σ a⌝ := by
  iintro Hi Hpt
  icases (wptOwnH_at c a v σ.wmWs).mp $$ Hpt with ⟨%t, He, -, %ht⟩
  ihave %hlat := wlatLookupElem σ.wmImg σ.wmLog a _ t v $$ [Hi He]
  · iframe Hi He
  ipureintro
  unfold pinnedRead
  rw [latestValTs _ _ _ _ _ hlat]
  rw [flr_wsView] at ht
  exact ht

/-- The era-image case: no view, no receipt, no hypothesis about the hart. -/
theorem wptImgPinnedRead (σ : Wmstate) (a : Int) (dq : DFrac) (v : BitVec 8) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wptImg (GF := GF) a dq v) σ.wmWs -∗ ⌜pinnedRead σ a⌝ := by
  iintro Hi Hpt
  icases (wptImg_at a dq v σ.wmWs).mp $$ Hpt with He
  ihave %hlat := wlatLookup σ.wmImg σ.wmLog a dq 0 v $$ [Hi He]
  · iframe Hi He
  ipureintro
  exact pinnedReadUnwritten σ a (latestValTs _ _ _ _ _ hlat)

/-- THE ACCESS-FOOTPRINT FORM: owning the `n` bytes of the access at the hart's
index discharges the whole read obligation. -/
theorem wptPinnedAcc (σ : Wmstate) (pa : PAddr) (n : Nat) (dq : DFrac) (bs : List (BitVec 8)) :
    bs.length = n →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      ([∗list] j ↦ b ∈ bs, vwpHold (WeakInterp.accAddr pa j ↦w{dq} b : VProp GF) σ.wmWs) -∗
      ⌜∀ j, j < n → pinnedRead σ (WeakInterp.accAddr pa j)⌝ := by
  intro hlen
  apply wand_intro
  by_cases hall : ∀ j, j < n → pinnedRead σ (WeakInterp.accAddr pa j)
  · exact pure_intro hall
  · have hex : ∃ j, j < n ∧ ¬ pinnedRead σ (WeakInterp.accAddr pa j) := by
      apply Classical.byContradiction
      intro hne
      exact hall fun j hj => Classical.byContradiction fun hp => hne ⟨j, hj, hp⟩
    obtain ⟨j, hj, hnp⟩ := hex
    have hlk : bs[j]? = some bs[j]! := by
      rw [List.getElem?_eq_getElem (by omega)]
      simp [getElem!_pos, show j < bs.length by omega]
    exact (sep_mono_right (BigSepL.bigSepL_lookup
        (Φ := fun j' b => vwpHold (WeakInterp.accAddr pa j' ↦w{dq} b : VProp GF) σ.wmWs) hlk)).trans
      ((wand_elim (wptPinnedRead σ _ dq _)).trans (pure_mono fun h => absurd h hnp))

end connector

/-! ## 10. PROOF OF CONCEPT: an existing `exec` leaf, transferred

`ExecLib.execExecuteITYPEADDI` is an ordinary member of the `exec`-level library;
its weak counterpart is ONE application of the bridge over it. -/

theorem wexecExecuteITYPEADDI (tid : Option Nat) (imm : BitVec 12) (rs1 rd : regidx) (a : BitVec 64)
    (s : Wmstate) (t' : ExecSt) :
    pinnedExec tid (execute (.ITYPE (imm, rs1, rd, .ADDI))) s →
    wlogWf s.wmLog →
    exec (rX_bits rs1) (wflatSt s) = some (a, wflatSt s) →
    exec (wX_bits rd (a + sign_extend (m := 64) imm)) (wflatSt s) = some ((), t') →
    -- the weak machine can execute it ...
    (∃ χ s0 χ', wexec tid (execute (.ITYPE (imm, rs1, rd, .ADDI))) χ s = some (RETIRE_SUCCESS, s0, χ')) ∧
    -- ... and however it does, the result is the SC one
    (∀ χ x s' χ', wexec tid (execute (.ITYPE (imm, rs1, rd, .ADDI))) χ s = some (x, s', χ') →
      x = RETIRE_SUCCESS ∧ s'.wmRegs = t'.regs ∧ s'.wmDev = t'.dev ∧
      wflatMem s'.wmImg s'.wmLog = t'.mem) := by
  intro hp hwf ha hw
  exact wexecPinnedAgree tid _ s _ t' hp hwf (execExecuteITYPEADDI imm rs1 rd a (wflatSt s) t' ha hw)

/-! ## 11. THE MERGED PEEL: `wstepOk` (M3a, item 1)

`pinnedExec` with the `choose` arm turned from `True` into `False`: strictly
weaker than `pinnedExec ∧ WeakExec.mchoiceFree`, and still delivers everything --
on the pinned fragment every admissible read returns the canonical one, so the
∀-over-read-results of `mchoiceFree` is not needed. -/

def wstepOk (tid : Option Nat) {X : Type} : SailM X → Wmstate → Prop
  | .pure _, _ => True
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => wstepOk tid (k (s.wmRegs r)) s
    | .regWrite r v, k => wstepOk tid (k PUnit.unit) (wsetReg s r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        ∀ w d', devRead s.wmDev req.pa n = some (w, d') →
          wstepOk tid (k (.Ok (w, none))) (wsetDev s d')
      else
        accWf req.pa n ∧
        (akPins (classify req.access_kind) = false →
          ∀ j, j < n → readPinned s (classify req.access_kind) (WeakInterp.accAddr req.pa j)) ∧
        (∀ w, wreadBytes s (classify req.access_kind) req.pa n (cohTs s req.pa n) = some w →
          wstepOk tid (k (.Ok (w, none)))
            (wreadPost s (classify req.access_kind) req.pa (cohTs s req.pa n)))
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          ∀ d', devWrite s.wmDev req.pa n v = some d' →
            wstepOk tid (k (.Ok (some true))) (wsetDev s d')
        | none => True
      else
        accWf req.pa n ∧
        (match req.value with
         | some v =>
           wstepOk tid (k (.Ok (some true))) (wwritePost tid s (classify req.access_kind) req.pa n v)
         | none => True)
    | .barrier b, k => wstepOk tid (k ()) (wbarrierPost s b)
    | .instrAnnounce _ _, k => wstepOk tid (k ()) s
    | .branchAnnounce _ _, k => wstepOk tid (k ()) s
    | .cacheOp _, k => wstepOk tid (k ()) s
    | .tlbi _, k => wstepOk tid (k ()) s
    | .takeException _, k => wstepOk tid (k ()) s
    | .returnException _, k => wstepOk tid (k ()) s
    | .translationStart _, k => wstepOk tid (k ()) s
    | .translationEnd _, k => wstepOk tid (k ()) s
    | .cycleCount, k => wstepOk tid (k ()) s
    | .message _, k => wstepOk tid (k ()) s
    | .getCycleCount, k => wstepOk tid (k (0 : Nat)) s
    -- THE ONLY ARM THAT DIFFERS FROM `pinnedExec`
    | .choose _, _ => False
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- The merged predicate implies the transfer's side conditions ... -/
theorem wstepOkPinned (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ s, wstepOk tid m s → pinnedExec tid m s := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro s hok
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOk] at hok
        simp only [pinnedExec]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          intro w d' h
          exact ih _ _ (hok w d' h)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨h1, h2, h3⟩ := hok
          exact ⟨h1, h2, fun w hw => ih _ _ (h3 w hw)⟩
      case memWrite n va req =>
        simp only [wstepOk] at hok
        simp only [pinnedExec]
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd]
          · rw [if_neg hd] at hok ⊢
            simp only [hv] at hok ⊢
            exact ⟨hok.1, trivial⟩
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok ⊢
            simp only [hv] at hok ⊢
            intro d' h
            exact ih _ _ (hok d' h)
          · rw [if_neg hd] at hok ⊢
            simp only [hv] at hok ⊢
            exact ⟨hok.1, ih _ _ hok.2⟩
      case choose => simp only [pinnedExec]
      case readRam => simp only [pinnedExec]
      case writeRam => simp only [pinnedExec]
      all_goals (simp only [wstepOk] at hok; simp only [pinnedExec]; exact ih _ _ hok)

/-- ... and, on its own, the `wrun` → `wexec` bridge: at a pinned read the run
CANNOT have used any timestamps but the canonical ones. -/
theorem wrunWexecWstepOk (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ s, wstepOk tid m s →
    ∀ x s', wrun tid m s x s' → ∃ χ χ', wexec tid m χ s = some (x, s', χ') := by
  induction m with
  | pure y =>
    intro s _ x s' hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], [], rfl⟩
  | impure call k ih =>
    intro s hok x s' hrun
    cases call with
    | error e => exact hrun.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOk] at hok
        simp only [wrun] at hrun
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok hrun
          cases hdr : devRead s.wmDev req.pa n with
          | none => rw [hdr] at hrun; exact hrun.elim
          | some p =>
            obtain ⟨w0, d'⟩ := p
            rw [hdr] at hrun
            obtain ⟨χ, χ', hex⟩ := ih _ _ (hok w0 d' hdr) _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_pos hd, hdr]; exact hex⟩
        · rw [if_neg hd] at hok hrun
          obtain ⟨w, ts, hokr, hrun⟩ := hrun
          obtain ⟨_, hpin, hk⟩ := hok
          have hts := wreadPinnedTs s _ _ _ _ _ hpin hokr
          subst hts
          have hrb := wreadBytesComplete _ _ _ _ _ _ hokr
          obtain ⟨χ, χ', hex⟩ := ih _ _ (hk w hrb) _ _ hrun
          exact ⟨cohTs s req.pa n :: χ, χ',
            by simp only [wexec, if_neg hd, List.head?_cons, List.tail_cons, hrb]; exact hex⟩
      case memWrite n va req =>
        simp only [wstepOk] at hok
        simp only [wrun] at hrun
        cases hv : req.value with
        | none =>
          by_cases hd : mmioAcc req.pa n = true
          · simp [hd, hv] at hrun
          · simp [hd, hv] at hrun
        | some v =>
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at hok hrun
            simp only [hv] at hok hrun
            cases hdw : devWrite s.wmDev req.pa n v with
            | none => rw [hdw] at hrun; exact hrun.elim
            | some d' =>
              rw [hdw] at hrun
              obtain ⟨χ, χ', hex⟩ := ih _ _ (hok d' hdw) _ _ hrun
              exact ⟨χ, χ', by simp only [wexec, if_pos hd, hv, hdw]; exact hex⟩
          · rw [if_neg hd] at hok hrun
            simp only [hv] at hok hrun
            obtain ⟨χ, χ', hex⟩ := ih _ _ hok.2 _ _ hrun
            exact ⟨χ, χ', by simp only [wexec, if_neg hd, hv]; exact hex⟩
      case choose => simp only [wstepOk] at hok
      case readRam => exact hrun.elim
      case writeRam => exact hrun.elim
      all_goals
        simp only [wstepOk] at hok
        simp only [wrun] at hrun
        obtain ⟨χ, χ', hex⟩ := ih _ _ hok _ _ hrun
        exact ⟨χ, χ', by simp only [wexec]; exact hex⟩

theorem wstepOkCovers (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) :
    wstepOk tid m s → wexecCovers tid m s :=
  fun hok x s' hrun => wrunWexecWstepOk tid m s hok x s' hrun

/-- THE ONE LEMMA A LEAF APPLIES.  One peel in, everything `WeakExec.wpWexecStep`
asks for out. -/
theorem wexecLeafAgree (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) (x0 : X) (t0 : ExecSt) :
    wstepOk tid m s → wlogWf s.wmLog →
    exec m (wflatSt s) = some (x0, t0) →
    wexecCovers tid m s ∧
    (∃ χ s0 χ', wexec tid m χ s = some (x0, s0, χ')) ∧
    (∀ χ x s' χ', wexec tid m χ s = some (x, s', χ') →
      x = x0 ∧ s'.wmRegs = t0.regs ∧ s'.wmDev = t0.dev ∧
      wflatMem s'.wmImg s'.wmLog = t0.mem ∧ wlogWf s'.wmLog) := by
  intro hok hwf hex
  have hp := wstepOkPinned tid m s hok
  obtain ⟨hred, hag⟩ := wexecPinnedAgree tid m s x0 t0 hp hwf hex
  refine ⟨wstepOkCovers tid m s hok, hred, ?_⟩
  intro χ x s' χ' hw
  obtain ⟨h1, h2, h3, h4⟩ := hag χ x s' χ' hw
  exact ⟨h1, h2, h3, h4, wexecPinnedWlogWf tid m s hp hwf χ x s' χ' hw⟩

end Weak
