/-
Weak: **validation of the `AxLdgSeal` kit on register-only code** — addi, c.addi, add, sub, and,
or, slli (+ addiw, slt) with SYMBOLIC source registers; tick = false for all, tick = true for addi.

Rocq: `iris/AxLdgSealArith.v` @ xxvzwolszwmp.

Each `ldg*` ledger is `ax_ldg_seal_solve`: the boundary walk by `ax_epi_ledger_krfl`, then per
pin-answer branch the kernel spine closed by `ax_ldg_seal_close`, at the reference state
`probeRegs pc` with the source GPRs set to fresh variables (the data operations sealed as in
Rocq, `AxLdgSeal` §5; in Lean the seals are optional, see `AxLdgSeal`'s method).  Each
`wpd*Sym` is `AxLdgSeal.wpdLdg` at that ledger: the WPd from ANY register file agreeing with
`probeRegs pc` on the CONTROL part of the upward-exposed read set; the post is at the caller's
own source values.  `post*Spec` states the post in `Int` arithmetic, e.g. `postAddiSpec`:
PC = pc+4 ∧ x6 = (x5 + 7) mod 2^64.

## Deviations from Rocq

1. As `AxLdgSeal` deviations 1–2: the engines take `Hgd` as `AxCjrWpd.fetchImgOk`, drop
   `Hflow`/`Hloc`, state `RetS`/`RetP` at `kk` (Rocq `S kk`), are generic in `hlc`; registers
   as `W64r` written `⟨.x6, rfl⟩` (Rocq `x6 : w64r`); `gset` ↦ `List` (`A ∖ syms gs` ↦
   `A.filter (· ∉ syms gs)`); `Z` ↦ `Int`, `bv_unsigned` ↦ `toNat` cast to `Int`, `bv_wrap 64 z`
   ↦ `z % 2 ^ 64`, `Z.shiftl z 3` ↦ `z * 2 ^ 3` (`slli3Unsigned`); `mword_of_int` ↦
   `BitVec.ofInt`; `sign_extend'` ↦ the model's `sign_extend`; `subrange_vec_dec v 31 0` ↦
   `Sail.BitVec.extractLsb v 31 0`; `add_vec`/`sub_vec`/`and_vec`/`or_vec` ↦ `+`/`-`/`&&&`/`|||`;
   `riscv_extras.shift_bits_left` ↦ `shift_bits_left`.  `probeRegs` takes a `Nat` pc:
   `baseA := probeRegs pcA.toNat`.
2. NEGATIVE TEST: Rocq `ldg_addi_wrong` is a `Fail ldg_solve …; Abort` (no declaration).  The
   Lean closing tactic does not reject a wrong post at tactic time (the kernel does, at the
   declaration: `AxLdgSeal` header), so it cannot be a `fail_if_success`.  Ported as the PROVED
   Lean-only `AxLdgSealArith.postAddiWrongRejected`: the wrong post (`+8`) is false at every
   state where the right post (`+7`) holds — so no ledger can establish both.
3. Rocq `wpd_add_sym := wpd_rr_sym add_vec vs_add ldg_add` (and sub/and/or) are `Definition`s
   of proofs; Lean: `theorem`s restating `wpdRrSym`'s statement at the instance, proved by it.
4. Rocq `post_local_false` is stated at `List Register` (Lean `postLocal`).
5. SPLIT (Lean-only, elaboration ~260 s in one file): this file has the vocabulary, the addi /
   c.addi / add / sub / slli ledgers and the Int-arithmetic posts; `Weak.AxLdgSealArith2` has
   the and / or / addiw / slt / full-seal-add / tick / three-symbol ledgers and the WPds.

**Rocq → Lean name map.**  `pc_a` `pcA`, `pc_c` `pcC`, `base_a` `baseA`, `base_c` `baseC`,
`imm12` `imm12`, `imm6` `imm6`, `sx` `sx`, `post_local_false` `postLocalFalse`, `vs_addi`
`vsAddi`, `vs_add` `vsAdd`, `vs_sub` `vsSub`, `vs_and` `vsAnd`, `vs_or` `vsOr`, `vs_slli`
`vsSlli`, `vs_caddi` `vsCaddi`, `A_addi` `AAddi`, `A_rr` `ARr`, `A_caddi` `ACaddi`, `post_addi`
`postAddi`, `ldg_addi` `ldgAddi`, `post_addi_local` `postAddiLocal`, `post_addi_spec`
`postAddiSpec`, `post_addi_wrong` `postAddiWrong`, `post_caddi` `postCaddi`, `ldg_caddi`
`ldgCaddi`, `post_rr` `postRr`, `ldg_add` `ldgAdd`, `ldg_sub` `ldgSub`, `ldg_and` `ldgAnd`,
`ldg_or` `ldgOr`, `post_slli` `postSlli`, `ldg_slli` `ldgSlli`, `slli3_unsigned`
`slli3Unsigned`, `vs_addiw` `vsAddiw`, `vs_slt` `vsSlt`, `post_addiw` `postAddiw`, `ldg_addiw`
`ldgAddiw`, `post_slt` `postSlt`, `ldg_slt` `ldgSlt`, `ldg_add_all` `ldgAddAll`,
`post_rr_spec` `postRrSpec`, `post_rr_local` `postRrLocal`, `post_caddi_spec` `postCaddiSpec`,
`post_caddi_local` `postCaddiLocal`, `post_slli_spec` `postSlliSpec`, `post_slli_local`
`postSlliLocal`, `A_addi_t` `AAddiT`, `post_addi3` `postAddi3`, `ldg_addi_tick` `ldgAddiTick`,
`ldg_addi3` `ldgAddi3`, `post_addi3_local` `postAddi3Local`, `post_addi3_spec` `postAddi3Spec`,
`wpd_addi_sym` `wpdAddiSym`, `wpd_addi_sym_tick` `wpdAddiSymTick`, `wpd_rr_sym` `wpdRrSym`,
`wpd_add_sym`/`sub`/`and`/`or` `wpdAddSym`/`wpdSubSym`/`wpdAndSym`/`wpdOrSym`, `wpd_caddi_sym`
`wpdCaddiSym`, `wpd_slli_sym` `wpdSlliSym`.  None is in the duplicated-name table.  Lean-only:
`AxLdgSealArith.postAddiWrongRejected` (deviation 2), `AxLdgSealArith.sx7`/`sx8` (Rocq's inline
`vm_compute` asserts).

**Dropped:** nothing (`ldg_addi_wrong` is not a Rocq declaration; deviation 2).
-/
import Weak.AxLdgSeal

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- 4-aligned: 4-byte fetch. -/
def pcA : Int := 0x80000004
/-- 2-aligned: 2-byte fetch. -/
def pcC : Int := 0x80000006
def baseA : RegFile := probeRegs pcA.toNat
def baseC : RegFile := probeRegs pcC.toNat

def imm12 (z : Int) : BitVec 12 := BitVec.ofInt 12 z
def imm6 (z : Int) : BitVec 6 := BitVec.ofInt 6 z
def sx (z : Int) : BitVec 64 := sign_extend (m := 64) (imm12 z)

theorem postLocalFalse (P : List Register) : postLocal P (fun _ => false) := fun _ _ _ => rfl

/-! Encodings (little-endian). -/
/-- addi x6,x5,7 -/
def vsAddi : List (BitVec 8) := [0x13#8, 0x83#8, 0x72#8, 0x00#8]
/-- add x7,x5,x6 -/
def vsAdd : List (BitVec 8) := [0xB3#8, 0x83#8, 0x62#8, 0x00#8]
/-- sub x7,x5,x6 -/
def vsSub : List (BitVec 8) := [0xB3#8, 0x83#8, 0x62#8, 0x40#8]
/-- and x7,x5,x6 -/
def vsAnd : List (BitVec 8) := [0xB3#8, 0xF3#8, 0x62#8, 0x00#8]
/-- or x7,x5,x6 -/
def vsOr : List (BitVec 8) := [0xB3#8, 0xE3#8, 0x62#8, 0x00#8]
/-- slli x6,x5,3 -/
def vsSlli : List (BitVec 8) := [0x13#8, 0x93#8, 0x32#8, 0x00#8]
/-- c.addi x5,7 -/
def vsCaddi : List (BitVec 8) := [0x9D#8, 0x02#8]

/-! Upward-exposed read sets (tracer-computed at the concrete control). -/
noncomputable def AAddi : List Register := AOf baseA pcA vsAddi
noncomputable def ARr : List Register := AOf baseA pcA vsAdd
noncomputable def ACaddi : List Register := AOf baseC pcC vsCaddi

/-! # addi x6, x5, 7 -/

def postAddi : List (BitVec 64) → RegFile → Bool
  | [x] => ldgPost (pcA + 4) [(⟨.x6, rfl⟩, ((x + sx 7).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgAddi : LdgFacts probeMem baseA [⟨.x5, rfl⟩] AAddi DrLdg DwLdg DLdg pcA vsAddi
    (PRegs [⟨.x6, rfl⟩]) postAddi := by
  ax_ldg_seal_solve (unfold postAddi execute_ITYPE) (ax_ldg_seal_alu)

theorem postAddiLocal (xs : List (BitVec 64)) : postLocal (PRegs [⟨.x6, rfl⟩]) (postAddi xs) := by
  match xs with
  | [] => exact postLocalFalse _
  | [_] => exact ldgPostLocal _ [(_, _)]
  | _ :: _ :: _ => exact postLocalFalse _

theorem AxLdgSealArith.sx7 : ((sx 7).toNat : Int) = 7 := by decide +kernel
theorem AxLdgSealArith.sx8 : ((sx 8).toNat : Int) = 8 := by decide +kernel

theorem postAddiSpec (x : BitVec 64) (rs : RegFile) :
    postAddi [x] rs = true ↔
      obs64 AxLdgSeal.pcR rs = pcA + 4 ∧
        obs64 ⟨.x6, rfl⟩ rs = ((x.toNat : Int) + 7) % 2 ^ 64 := by
  simp only [postAddi, ldgPostSpec, List.mem_singleton, forall_eq, addVecUnsigned,
    AxLdgSealArith.sx7]

/-- Negative control: the same ledger with a WRONG post (`+8`). -/
def postAddiWrong : List (BitVec 64) → RegFile → Bool
  | [x] => ldgPost (pcA + 4) [(⟨.x6, rfl⟩, ((x + sx 8).toNat : Int))]
  | _ => fun _ => false

/-- (Lean-only, deviation 2) The wrong post is rejected wherever the right one holds. -/
theorem AxLdgSealArith.postAddiWrongRejected (x : BitVec 64) (rs : RegFile) :
    postAddi [x] rs = true → postAddiWrong [x] rs = false := by
  intro H
  rw [postAddiSpec] at H
  cases hw : postAddiWrong [x] rs with
  | false => rfl
  | true =>
    simp only [postAddiWrong, ldgPostSpec, List.mem_singleton, forall_eq, addVecUnsigned,
      AxLdgSealArith.sx8] at hw
    have h := H.2.symm.trans hw.2
    omega

/-! # c.addi x5, 7 (compressed, 2-byte fetch; rd = rs1) -/

def postCaddi : List (BitVec 64) → RegFile → Bool
  | [x] => ldgPost (pcC + 2) [(⟨.x5, rfl⟩, ((x + sx 7).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgCaddi : LdgFacts probeMem baseC [⟨.x5, rfl⟩] ACaddi DrLdg DwLdg DLdg pcC vsCaddi
    (PRegs [⟨.x5, rfl⟩]) postCaddi := by
  ax_ldg_seal_solve (unfold postCaddi execute_ITYPE) (ax_ldg_seal_alu)

/-! # add / sub / and / or  x7, x5, x6 -/

def postRr (f : BitVec 64 → BitVec 64 → BitVec 64) : List (BitVec 64) → RegFile → Bool
  | [x, y] => ldgPost (pcA + 4) [(⟨.x7, rfl⟩, ((f x y).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgAdd : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vsAdd
    (PRegs [⟨.x7, rfl⟩]) (postRr (· + ·)) := by
  ax_ldg_seal_solve (unfold postRr execute_RTYPE) (ax_ldg_seal_alu)

set_option maxHeartbeats 4000000 in
theorem ldgSub : LdgFacts probeMem baseA [⟨.x5, rfl⟩, ⟨.x6, rfl⟩] ARr DrLdg DwLdg DLdg pcA vsSub
    (PRegs [⟨.x7, rfl⟩]) (postRr (· - ·)) := by
  ax_ldg_seal_solve (unfold postRr execute_RTYPE) (ax_ldg_seal_alu)

/-! # slli x6, x5, 3 -/

def postSlli : List (BitVec 64) → RegFile → Bool
  | [x] => ldgPost (pcA + 4) [(⟨.x6, rfl⟩, ((shift_bits_left x (imm6 3)).toNat : Int))]
  | _ => fun _ => false

set_option maxHeartbeats 4000000 in
theorem ldgSlli : LdgFacts probeMem baseA [⟨.x5, rfl⟩] AAddi DrLdg DwLdg DLdg pcA vsSlli
    (PRegs [⟨.x6, rfl⟩]) postSlli := by
  ax_ldg_seal_solve (unfold postSlli execute_SHIFTIOP) (ax_ldg_seal_alu)

theorem slli3Unsigned (x : BitVec 64) :
    ((shift_bits_left x (imm6 3)).toNat : Int) = ((x.toNat : Int) * 2 ^ 3) % 2 ^ 64 := by
  have h3 : (imm6 3).toNat = 3 := by decide +kernel
  rw [shift_bits_left, BitVec.shiftLeft_eq', h3, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-! # The posts in Int arithmetic -/

theorem postRrSpec (f : BitVec 64 → BitVec 64 → BitVec 64) (x y : BitVec 64) (rs : RegFile) :
    postRr f [x, y] rs = true ↔
      obs64 AxLdgSeal.pcR rs = pcA + 4 ∧ obs64 ⟨.x7, rfl⟩ rs = ((f x y).toNat : Int) := by
  simp only [postRr, ldgPostSpec, List.mem_singleton, forall_eq]

theorem postRrLocal (f : BitVec 64 → BitVec 64 → BitVec 64) (xs : List (BitVec 64)) :
    postLocal (PRegs [⟨.x7, rfl⟩]) (postRr f xs) := by
  match xs with
  | [] => exact postLocalFalse _
  | [_] => exact postLocalFalse _
  | [_, _] => exact ldgPostLocal _ [(_, _)]
  | _ :: _ :: _ :: _ => exact postLocalFalse _

theorem postCaddiSpec (x : BitVec 64) (rs : RegFile) :
    postCaddi [x] rs = true ↔
      obs64 AxLdgSeal.pcR rs = pcC + 2 ∧
        obs64 ⟨.x5, rfl⟩ rs = ((x.toNat : Int) + 7) % 2 ^ 64 := by
  simp only [postCaddi, ldgPostSpec, List.mem_singleton, forall_eq, addVecUnsigned,
    AxLdgSealArith.sx7]

theorem postCaddiLocal (xs : List (BitVec 64)) : postLocal (PRegs [⟨.x5, rfl⟩]) (postCaddi xs) := by
  match xs with
  | [] => exact postLocalFalse _
  | [_] => exact ldgPostLocal _ [(_, _)]
  | _ :: _ :: _ => exact postLocalFalse _

theorem postSlliSpec (x : BitVec 64) (rs : RegFile) :
    postSlli [x] rs = true ↔
      obs64 AxLdgSeal.pcR rs = pcA + 4 ∧
        obs64 ⟨.x6, rfl⟩ rs = ((x.toNat : Int) * 2 ^ 3) % 2 ^ 64 := by
  simp only [postSlli, ldgPostSpec, List.mem_singleton, forall_eq, slli3Unsigned]

theorem postSlliLocal (xs : List (BitVec 64)) : postLocal (PRegs [⟨.x6, rfl⟩]) (postSlli xs) := by
  match xs with
  | [] => exact postLocalFalse _
  | [_] => exact ldgPostLocal _ [(_, _)]
  | _ :: _ :: _ => exact postLocalFalse _

end Weak
