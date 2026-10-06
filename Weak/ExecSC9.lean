/-
Weak: the Sv39 page walk over abstract PTE words, the TLB hit, `sfence.vma`,
`csrw pmpcfg0`.

Rocq: `iris/CommonWalk.v` (sections `UserWalk`, `UserWalkFault`), `iris/PtTree.v`
(§1 predicates, sections `PtHit`, `PtFault`), `iris/UserretDefs.v`
(`exec_execute_SFENCE_VMA_S`), `iris/WpGprCsrwA.v` (`pmpWriteCfg_val`,
`pmp_cfg_step`, `pmpcfg0_final`, `exec_execute_csrw_pmpcfg0`) @ xxvzwolszwmp.

**Conventions (all `Weak/ExecSC*.lean` files; the deviations every statement shares).**
Statements are about `Weak.exec` over the LEAN model (sail-riscv `070832a1`,
`-D SYMBOLIC`: announce events silent), not Rocq's `exec` over the Coq model.
* GPRs: Rocq `if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64
  (gpr_of_Z (uint i))) s.(sregs)` ↦ `s.gpr i`; Rocq `if uint rd =? 0 then s else
  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦
  `s.setGpr rd v` (`Weak/ExecSC.lean`).  Where Rocq has a `uint rd ≠ 0` premise and a
  plain `set_reg`, the premise is kept and the result is `setGpr` (equal under it).
* Spelling: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
  `(x == 1#1) = b`; `vec_access_dec v i` ↦ `v[i]!`; `vec_update_dec v i x` ↦
  `vectorUpdate v i x`; `uint x` ↦ `x.toNat`; `Z` widths/indices ↦ `Nat`;
  `mword n` ↦ `BitVec n`; `tt` ↦ `()`; `zeros' n` ↦ `zeros (n := n)`.
* Memory: `dev_addr pa = false` ↦ `devAddr pa = false`; Rocq's byte window
  `∀ j < n, s.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt s pa n w`;
  `MState s.(sregs) (write_bytes s.(mem) pa n v) s.(mdev)` ↦
  `s.setMem (bmWrite s.mem pa n v)`.  An ifetch is a RAM read in `exec`
  (`Weak/Exec.lean`), so the fetch facts read the byte map (`AK_ifetch` plays no role).
* `hartSupports` is pure in Lean: Rocq `exec (hartSupports X) s = Some (true, s)` ↦
  `hartSupports .X = true`; Rocq's fuelled `_rec_currentlyEnabled` facts are stated on
  `currentlyEnabled`.  Rocq loops (`foreach_ZM_up'`, `untilMT`) ↦ lean-sail's `IntRange`
  `forIn` and `untilFuelM`.
* Rocq section hypotheses become theorem premises; section `Let`s become `def`s or are
  inlined; premise bundles that several statements share are `structure`s
  (`FetchM4`, `FetchM2`, `FetchS`, `MemM8`, `AmoS4`), each field a Rocq hypothesis.

**Deviations from Rocq.**
1. The walk is Lean's well-founded `pt_walk` (Rocq `_rec_pt_walk` with an `Acc`): the
   level lemmas are about `pt_walk … level …`; the Rocq `Acc`-generic
   `∀ g' a` sub-walk premises are `∀ g'`.  Rocq's section hypotheses become premises
   (`h2i … H0N`); `autocast (PPN_of_PTE pte0)` is `ppn0 pte0`; the walk's leaf
   record is `uWalkOut`.
2. The model's PTE-typed values (`BitVec (if 39 = 32 then … else …)`) meet the
   premises up to conversion only, so the proofs rewrite with `erw`.
3. `exec_translate_pt_denied/_blocks`: the ASID is `0#16` (Rocq `mword_of_int 0`).
4. `exec_execute_SFENCE_VMA_S`: the `TVM` premise is `(… == 1#1) = false`; the loop is
   `flush_TLB`'s `IntRange` loop (`execForInInv`, a state-invariant loop rule).
5. `pmpcfg0_final` is `pmpCfgStep` at `Nat` indices 0..7; `exec_execute_csrw_pmpcfg0`
   uses `s.gpr rs1` for Rocq's `x0`-guarded read.

**Name map (Rocq → Lean).**  CommonWalk: `u_pte_addr` ↦ `uPteAddr`, `u_next_base` ↦
`uNextBase`, `u_gbit` ↦ `uGbit`, `u_global` ↦ `uGlobal`, `u_walk_entry` ↦
`uWalkEntry`, `exec_check_leaf_pte_leaf0` ↦ `execCheckLeafPteLeaf0`,
`exec_rec_walk_leaf` ↦ `execPtWalkLeaf`, `exec_rec_walk_l1` ↦ `execPtWalkL1`,
`exec_pt_walk_user` ↦ `execPtWalkUser`, `exec_translate_TLB_miss_user` ↦
`execTranslateTLBMissUser`, `exec_check_leaf_pte_invalid` ↦
`execCheckLeafPteInvalid`, `exec_check_leaf_pte_noperm0` ↦ `execCheckLeafPteNoperm0`,
`exec_rec_walk_leaf_invalid` ↦ `execPtWalkLeafInvalid`, `exec_rec_walk_leaf_noperm`
↦ `execPtWalkLeafNoperm`, `exec_rec_walk_l1_invalid` ↦ `execPtWalkL1Invalid`,
`exec_rec_walk_l1_sub` ↦ `execPtWalkL1Sub`, `exec_pt_walk_user_l2_invalid` ↦
`execPtWalkL2Invalid`, `exec_pt_walk_user_sub` ↦ `execPtWalkL2Sub`,
`exec_translate_TLB_miss_user_walk_err` ↦ `execTranslateTLBMissWalkErr`,
`exec_translate_walk_user_err` ↦ `execTranslateWalkUserErr`.  PtTree: `pte_valid` ↦
`pteValid`, `pte_invalid` ↦ `pteInvalid`, `pte_ptr` ↦ `ptePtr`, `pte_leaf` ↦
`pteLeaf`, `pte_pbmt0` ↦ `ptePbmt0`, `pte_check_ok` ↦ `pteCheckOk`,
`pte_check_denied` ↦ `pteCheckDenied`, `exec_translate_TLB_hit_pt` ↦
`execTranslateTLBHitPt`, `exec_translate_pt_denied` ↦ `execTranslatePtDenied`,
`exec_translate_pt_blocks` ↦ `execTranslatePtBlocks`.  UserretDefs:
`exec_execute_SFENCE_VMA_S` ↦ `execExecuteSFENCEVMAS`.  WpGprCsrwA:
`pmpWriteCfg_val` ↦ `pmpWriteCfgVal`, `exec_pmpWriteCfg` ↦ `execPmpWriteCfg`,
`pmp_cfg_step` ↦ `pmpCfgStep`, `pmpcfg0_final` ↦ `pmpcfg0Final`,
`exec_execute_csrw_pmpcfg0` ↦ `execExecuteCsrwPmpcfg0`.  Lean-only: `ppn0`,
`uWalkOut`, `tlbGetPteUwe`, `tlbGetPpnUwe`, `execForInInv`, `vecSetGet`,
`execFlushTLBAll`, `pmpCfgUpto`, `execPmpWriteCfgReg0`, `execWriteCSRPmpcfg0`.

**Dropped**: none of the names the weak tier uses (CommonWalk's
`exec_add_to_TLB_user` is `execAddToTLBPt` of `Weak/ExecSC6.lean` at the walk entry).
-/
import Weak.ExecSC8
import MachCSL.WpCsrFacts

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. PTE vocabulary (Rocq `CommonWalk` §helpers, `PtTree` §1) -/

/-- Rocq `CommonWalk.u_pte_addr`: the PTE slot address at one walk level. -/
def uPteAddr (base : BitVec 44) (idx : BitVec 9) : BitVec 64 := zero_extend (m := 64) (base ++ (idx ++ zeros (n := 3)))

/-- Rocq `CommonWalk.u_next_base`. -/
def uNextBase (pte : BitVec 64) : BitVec 44 := PPN_of_PTE pte

/-- The PPN field of a 64-bit PTE (Rocq `autocast (PPN_of_PTE pte)`). -/
def ppn0 (pte : BitVec 64) : BitVec 44 := PPN_of_PTE pte

/-- Rocq `PtTree.pte_valid`. -/
def pteValid (w : BitVec 64) : Prop :=
  ∀ s, exec (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w)) s = some (false, s)
/-- Rocq `PtTree.pte_invalid`. -/
def pteInvalid (w : BitVec 64) : Prop :=
  ∀ s, exec (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w)) s = some (true, s)
/-- Rocq `PtTree.pte_ptr`. -/
def ptePtr (w : BitVec 64) : Prop := pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) = true
/-- Rocq `PtTree.pte_leaf`. -/
def pteLeaf (w : BitVec 64) : Prop := pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) = false
/-- Rocq `PtTree.pte_check_denied`. -/
def pteCheckDenied (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool) (f : pte_check_failure)
    (w : BitVec 64) : Prop :=
  ∀ s, exec (check_PTE_permission acc p mxr dosum (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w) ())
    s = some (.PTE_Check_Failure ((), f), s)

/-! ## 2. The leaf checks and the walk faults -/

/-- Rocq `CommonWalk.exec_check_leaf_pte_invalid`. -/
theorem execCheckLeafPteInvalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte : BitVec 64) (pa : physaddr) (lvl : Nat) (s : ExecSt) (hinv : pteInvalid pte) :
    exec (check_leaf_pte 39 vpn acc p mxr dosum pte pa lvl ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s) := by
  unfold check_leaf_pte
  rw [execCatchEarlyReturn]
  exec_run
  erw [hinv s]
  rfl

/-- Rocq `CommonWalk.exec_translate_walk_user_err`. -/
theorem execTranslateWalkUserErr (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (asid : BitVec 16) (root : BitVec 44) (f : PTW_Error) (s : ExecSt)
    (hlk : exec (lookup_TLB 39 asid vpn) s = some (none, s))
    (hmiss : exec (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = some (.Err (f, ()), s)) :
    exec (translate 39 asid root vpn acc p mxr dosum ()) s = some (.Err (f, ()), s) := by
  unfold translate
  exec_run [hlk, hmiss]

set_option simprocs false in
/-- Level 0 of the walk: the leaf slot holds an invalid PTE. -/
theorem execPtWalkLeafInvalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0))) 8) s = some (.Ok pte, s))
    (hinv : pteInvalid pte) :
    exec (pt_walk 39 vpn acc p mxr dosum base 0 g ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hinv s]
  exec_run
  erw [execCheckLeafPteInvalid vpn acc p mxr dosum pte _ 0 s hinv]
  rfl

/-- A leaf at level 0 failing the permission check (Rocq `CommonWalk.exec_check_leaf_pte_noperm0`). -/
theorem execCheckLeafPteNoperm0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte : BitVec 64) (pa : physaddr) (f : pte_check_failure) (s : ExecSt)
    (hv : pteValid pte) (hl : pteLeaf pte) (hchk : pteCheckDenied acc p mxr dosum f pte) :
    exec (check_leaf_pte 39 vpn acc p mxr dosum pte pa 0 ()) s = some (.Err (ext_get_ptw_error f, ()), s) := by
  unfold check_leaf_pte
  rw [execCatchEarlyReturn]
  exec_run
  erw [hv s]
  exec_run
  erw [hl]
  exec_run
  erw [hchk s]
  rfl

set_option simprocs false in
/-- Level 0: a valid leaf failing the permission check (Rocq `CommonWalk.exec_rec_walk_leaf_noperm`). -/
theorem execPtWalkLeafNoperm (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (f : pte_check_failure) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0))) 8) s = some (.Ok pte, s))
    (hv : pteValid pte) (hl : pteLeaf pte) (hchk : pteCheckDenied acc p mxr dosum f pte) :
    exec (pt_walk 39 vpn acc p mxr dosum base 0 g ()) s = some (.Err (ext_get_ptw_error f, ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hv s]
  exec_run [Functions.not, execIte]
  erw [execCheckLeafPteNoperm0 vpn acc p mxr dosum pte _ f s hv hl hchk]
  rfl

set_option simprocs false in
/-- Level 1: an invalid PTE (Rocq `CommonWalk.exec_rec_walk_l1_invalid`). -/
theorem execPtWalkL1Invalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9))) 8) s = some (.Ok pte, s))
    (hinv : pteInvalid pte) :
    exec (pt_walk 39 vpn acc p mxr dosum base 1 g ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hinv s]
  exec_run [Functions.not, execIte]
  erw [execCheckLeafPteInvalid vpn acc p mxr dosum pte _ 1 s hinv]
  rfl

set_option simprocs false in
/-- Level 2: an invalid PTE (Rocq `CommonWalk.exec_pt_walk_user_l2_invalid`). -/
theorem execPtWalkL2Invalid (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte : BitVec 64) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = some (.Ok pte, s))
    (hinv : pteInvalid pte) :
    exec (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hinv s]
  exec_run [Functions.not, execIte]
  erw [execCheckLeafPteInvalid vpn acc p mxr dosum pte _ 2 s hinv]
  rfl

set_option simprocs false in
/-- Level 1: a valid pointer, the result the level-0 sub-walk gives (Rocq
`CommonWalk.exec_rec_walk_l1_sub`). -/
theorem execPtWalkL1Sub (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte : BitVec 64) (g : Bool)
    (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9))) 8) s = some (.Ok pte, s))
    (hv : pteValid pte) (hn : ptePtr pte)
    (hsub : ∀ g', exec (pt_walk 39 vpn acc p mxr dosum (uNextBase pte) 0 g' ()) s = some (r, s)) :
    exec (pt_walk 39 vpn acc p mxr dosum base 1 g ()) s = some (r, s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hv s]
  exec_run [Functions.not, execIte]
  erw [hn]
  exec_run [execIte]
  erw [hsub]

set_option simprocs false in
/-- Level 2: a valid pointer, the result the level-1 sub-walk gives (Rocq
`CommonWalk.exec_pt_walk_user_sub`). -/
theorem execPtWalkL2Sub (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte : BitVec 64)
    (r : Result (PTW_Output 39 × Unit) (PTW_Error × Unit)) (s : ExecSt)
    (hrd : exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = some (.Ok pte, s))
    (hv : pteValid pte) (hn : ptePtr pte)
    (hsub : ∀ g', exec (pt_walk 39 vpn acc p mxr dosum (uNextBase pte) 1 g' ()) s = some (r, s)) :
    exec (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = some (r, s) := by
  rw [pt_walk]
  exec_run
  erw [hrd]
  exec_run
  erw [hv s]
  exec_run [Functions.not, execIte]
  erw [hn]
  exec_run [execIte]
  erw [hsub]

/-- A walk fault is the miss's fault (Rocq `CommonWalk.exec_translate_TLB_miss_user_walk_err`). -/
theorem execTranslateTLBMissWalkErr (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (asid : BitVec 16) (root : BitVec 44) (f : PTW_Error) (s : ExecSt)
    (hw : exec (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = some (.Err (f, ()), s)) :
    exec (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = some (.Err (f, ()), s) := by
  unfold translate_TLB_miss
  exec_run
  erw [hw]
  rfl

/-- Rocq `PtTree.pte_check_ok`. -/
def pteCheckOk (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool) (w : BitVec 64) : Prop :=
  ∀ s, exec (check_PTE_permission acc p mxr dosum (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w) ())
    s = some (.PTE_Check_Success (), s)

/-- Rocq `PtTree.exec_translate_pt_denied`: mapped but denied, state unchanged. -/
theorem execTranslatePtDenied (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 p0 : BitVec 64) (s : ExecSt)
    (hv2 : pteValid p2) (hn2 : ptePtr p2) (hv1 : pteValid p1) (hn1 : ptePtr p1) (hv0 : pteValid p0)
    (hl0 : pteLeaf p0) (hden : pteCheckDenied acc p mxr dosum (.PTE_No_Permission ()) p0)
    (hrd2 : exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = some (.Ok p2, s))
    (hrd1 : exec (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok p1, s))
    (hrd0 : exec (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s))
    (hlk : exec (lookup_TLB 39 0#16 vpn) s = some (none, s)) :
    exec (translate 39 0#16 root vpn acc p mxr dosum ()) s = some (.Err (.PTW_No_Permission (), ()), s) :=
  execTranslateWalkUserErr vpn acc p mxr dosum _ root _ s hlk
    (execTranslateTLBMissWalkErr vpn acc p mxr dosum _ root _ s
      (execPtWalkL2Sub vpn acc p mxr dosum root p2 _ s hrd2 hv2 hn2 (fun _ =>
        execPtWalkL1Sub vpn acc p mxr dosum _ p1 _ _ s hrd1 hv1 hn1 (fun _ =>
          execPtWalkLeafNoperm vpn acc p mxr dosum _ p0 _ (.PTE_No_Permission ()) s hrd0 hv0 hl0 hden))))

/-- Rocq `PtTree.exec_translate_pt_blocks`: the walk stops at an invalid word at level 2, 1
or 0, and `translate` page-faults, state unchanged. -/
theorem execTranslatePtBlocks (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (s : ExecSt)
    (h : (∃ w2, exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok w2, s) ∧ pteInvalid w2) ∨
         (∃ p2 w1, exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok p2, s) ∧ pteValid p2 ∧ ptePtr p2 ∧
          exec (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
            some (.Ok w1, s) ∧ pteInvalid w1) ∨
         (∃ p2 p1 w0, exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
            some (.Ok p2, s) ∧ pteValid p2 ∧ ptePtr p2 ∧
          exec (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
            some (.Ok p1, s) ∧ pteValid p1 ∧ ptePtr p1 ∧
          exec (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
            some (.Ok w0, s) ∧ pteInvalid w0))
    (hlk : exec (lookup_TLB 39 0#16 vpn) s = some (none, s)) :
    exec (translate 39 0#16 root vpn acc p mxr dosum ()) s = some (.Err (.PTW_Invalid_PTE (), ()), s) := by
  apply execTranslateWalkUserErr vpn acc p mxr dosum _ root _ s hlk
  apply execTranslateTLBMissWalkErr
  rcases h with ⟨w2, hrd2, hi2⟩ | ⟨p2, w1, hrd2, hv2, hn2, hrd1, hi1⟩ |
    ⟨p2, p1, w0, hrd2, hv2, hn2, hrd1, hv1, hn1, hrd0, hi0⟩
  · exact execPtWalkL2Invalid vpn acc p mxr dosum root w2 s hrd2 hi2
  · exact execPtWalkL2Sub vpn acc p mxr dosum root p2 _ s hrd2 hv2 hn2 (fun _ =>
      execPtWalkL1Invalid vpn acc p mxr dosum _ w1 _ s hrd1 hi1)
  · exact execPtWalkL2Sub vpn acc p mxr dosum root p2 _ s hrd2 hv2 hn2 (fun _ =>
      execPtWalkL1Sub vpn acc p mxr dosum _ p1 _ _ s hrd1 hv1 hn1 (fun _ =>
        execPtWalkLeafInvalid vpn acc p mxr dosum _ w0 _ s hrd0 hi0))

/-! ## 3. The success walk (Rocq `CommonWalk` section `UserWalk`) -/

/-- Rocq `CommonWalk.u_gbit`. -/
def uGbit (pte : BitVec 64) : Bool := _get_PTE_Flags_G (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0)) == 1#1
/-- Rocq `CommonWalk.u_global`. -/
def uGlobal (pte2 pte1 pte0 : BitVec 64) : Bool := ((false || uGbit pte2) || uGbit pte1) || uGbit pte0

/-- Rocq `CommonWalk.exec_check_leaf_pte_leaf0`: a valid, permitted, non-NAPOT leaf at
level 0 (section `UserWalk`'s `H0i`, `H0nl`, `Hchk0`, `H0N` as premises). -/
theorem execCheckLeafPteLeaf0 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte0 : BitVec 64) (pa : physaddr) (menvcfg0 : BitVec 64) (s : ExecSt)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    exec (check_leaf_pte 39 vpn acc p mxr dosum pte0 pa 0 ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()), s) := by
  unfold check_leaf_pte
  rw [execCatchEarlyReturn]
  exec_run
  erw [h0i s]
  exec_run
  erw [h0nl]
  exec_run
  erw [hchk0 s]
  exec_run [execCurrentlyEnabledSvnapot s hmisa]
  erw [h0N]
  exec_run [hmenv, hpbmte]
  rfl

/-- The leaf PTE of a level-0 walk as the model records it. -/
def uWalkOut (pa0 : BitVec 64) (pte0 : BitVec 64) (g : Bool) : PTW_Output 39 :=
  { ppn := ppn0 pte0, pte := pte0, pteAddr := .Physaddr pa0, level := 0, pbmt := .PBMT_PMA, global := g }

set_option simprocs false in
/-- Rocq `CommonWalk.exec_rec_walk_leaf`: level 0, the leaf. -/
theorem execPtWalkLeaf (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte0 : BitVec 64) (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC)
    (hrd0 : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0))) 8) s = some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    exec (pt_walk 39 vpn acc p mxr dosum base 0 g ()) s =
      some (.Ok (uWalkOut (uPteAddr base (Sail.BitVec.extractLsb vpn 8 0)) pte0 (g || uGbit pte0), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd0]
  exec_run
  erw [h0i s]
  exec_run [Functions.not, execIte]
  erw [execCheckLeafPteLeaf0 vpn acc p mxr dosum pte0 _ menvcfg0 s h0i h0nl hchk0 h0N hmisa hmenv hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `CommonWalk.exec_rec_walk_l1`: level 1, a pointer into the leaf. -/
theorem execPtWalkL1 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (base : BitVec 44) (pte1 pte0 : BitVec 64) (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC)
    (hrd1 : exec (read_pte (.Physaddr (uPteAddr base (Sail.BitVec.extractLsb vpn 17 9))) 8) s = some (.Ok pte1, s))
    (hrd0 : exec (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    exec (pt_walk 39 vpn acc p mxr dosum base 1 g ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        ((g || uGbit pte1) || uGbit pte0), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd1]
  exec_run
  erw [h1i s]
  exec_run [Functions.not, execIte]
  erw [h1nl]
  exec_run [execIte]
  erw [execPtWalkLeaf vpn acc p mxr dosum (uNextBase pte1) pte0 _ menvcfg0 s h0i h0nl hchk0 h0N hmisa hrd0 hmenv
    hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `CommonWalk.exec_pt_walk_user`: the full three-level walk. -/
theorem execPtWalkUser (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64) (menvcfg0 : BitVec 64) (s : ExecSt)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = some (.Ok pte2, s))
    (hrd1 : exec (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd0 : exec (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    exec (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s =
      some (.Ok (uWalkOut (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0)) pte0
        (uGlobal pte2 pte1 pte0), ()), s) := by
  rw [pt_walk]
  exec_run
  erw [hrd2]
  exec_run
  erw [h2i s]
  exec_run [Functions.not, execIte]
  erw [h2nl]
  exec_run [execIte]
  erw [execPtWalkL1 vpn acc p mxr dosum (uNextBase pte2) pte1 pte0 _ menvcfg0 s h1i h1nl h0i h0nl hchk0 h0N hmisa
    hrd1 hrd0 hmenv hpbmte]
  rfl

/-- Rocq `CommonWalk.u_walk_entry` (`PtTree`'s five-argument form): the TLB entry a
level-0 walk installs. -/
def uWalkEntry (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) (asid : BitVec 16) : TLB_Entry :=
  ptFillEnt asid vpn (ppn0 p0) p0 (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)))
    (uGlobal p2 p1 p0)

/-- Rocq `CommonWalk.exec_translate_TLB_miss_user`: the success walk, no A/D update, the
TLB fill. -/
theorem execTranslateTLBMissUser (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64) (asid : BitVec 16) (menvcfg0 : BitVec 64)
    (s : ExecSt)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC) (hnoupd : update_PTE_Bits pte0 acc = none)
    (hrd2 : exec (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = some (.Ok pte2, s))
    (hrd1 : exec (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd0 : exec (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    exec (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 pte0, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn pte2 pte1 pte0 asid)))) := by
  unfold translate_TLB_miss
  exec_run
  erw [execPtWalkUser vpn acc p mxr dosum root pte2 pte1 pte0 menvcfg0 s h2i h2nl h1i h1nl h0i h0nl hchk0 h0N hmisa
    hrd2 hrd1 hrd0 hmenv hpbmte]
  unfold uWalkOut update_and_write_pte
  exec_run
  erw [hnoupd]
  exec_run
  erw [execAddToTLBPt]
  rfl

/-! ## 4. A TLB hit (Rocq `PtTree` section `PtHit`) -/

/-- Rocq `PtTree.pte_pbmt0`. -/
def ptePbmt0 (w : BitVec 64) : Prop := _get_PTE_Ext_PBMT (ext_bits_of_PTE w) = 0#2

theorem tlbGetPteUwe (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) :
    tlb_get_pte (if (39 == 32) = true then 4 else 8) (uWalkEntry vpn p2 p1 q0 asid) = q0 := by
  show Sail.BitVec.extractLsb (zero_extend (m := 64) q0) 63 0 = q0
  simp only [Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

theorem tlbGetPpnUwe (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) :
    tlb_get_ppn 39 (uWalkEntry vpn p2 p1 q0 asid) vpn = ppn0 q0 := by
  unfold tlb_get_ppn uWalkEntry ptFillEnt ppn0
  simp only [trunc, zero_extend, sign_extend, ones, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend,
    Sail.BitVec.truncate]
  show BitVec.truncate 44 (BitVec.zeroExtend 64 (BitVec.zeroExtend 44 ((PPN_of_PTE q0 : BitVec 44) &&&
      ~~~BitVec.zeroExtend 44 (sail_ones 0))) ||| BitVec.signExtend 64 vpn &&&
      BitVec.zeroExtend 64 (BitVec.zeroExtend 45 (sail_ones 0))) = (PPN_of_PTE q0 : BitVec 44)
  generalize (PPN_of_PTE q0 : BitVec 44) = P
  have h1 : sail_ones 0 = 0#0 := by decide
  rw [h1]
  bv_decide

/-- Rocq `PtTree.exec_translate_TLB_hit_pt`. -/
theorem execTranslateTLBHitPt (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat) (s : ExecSt)
    (hchk : pteCheckOk acc p mxr dosum q0) (hupd : update_PTE_Bits q0 acc = none) (hpb : ptePbmt0 q0) :
    exec (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn p2 p1 q0 asid)) s =
      some (.Ok (ppn0 q0, .PBMT_PMA, ()), s) := by
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe]
  exec_run
  erw [hchk s]
  unfold update_and_write_pte
  exec_run
  erw [hupd]
  unfold tlb_get_pbmt
  exec_run
  erw [hpb]
  rfl

/-! ## 5. `sfence.vma` (Rocq `UserretDefs`) -/

/-- A unit-state `SailM` loop (step 1) with a state invariant. -/
theorem execForInInv (range : IntRange) (hstep : range.step = 1) (f : Int → Unit → SailM (ForInStep Unit))
    (P : Int → ExecSt → Prop) (s : ExecSt) (hP0 : P range.start s) (hle : range.start ≤ range.stop + 1)
    (hf : ∀ i st, i ∈ range → P i st → ∃ st', exec (f i ()) st = some (.yield (), st') ∧ P (i + 1) st') :
    ∃ st', exec (forIn range () f) s = some ((), st') ∧ P (range.stop + 1) st' := by
  show ∃ st', exec (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _ ∧ _
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (st : ExecSt),
      (range.stop - i + 1).toNat = n → range.start ≤ i → i ≤ range.stop + 1 → P i st →
      ∃ st', exec (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) st = some ((), st') ∧
        P (range.stop + 1) st' from
    H _ _ _ s rfl (Int.le_refl _) hle hP0
  intro n
  induction n with
  | zero =>
    intro i hs st hn hge hi hP
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    have : i = range.stop + 1 := by
      have := Int.toNat_eq_zero.mp hn
      omega
    subst this
    exact ⟨st, rfl, hP⟩
  | succ n ih =>
    intro i hs st hn hge hi hP
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      obtain ⟨st', he, hP'⟩ := hf i st h hP
      rw [execBind, he]
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
        rw [hstep]
        omega
      have hi' : i + range.step ≤ range.stop + 1 := by rw [hstep]; omega
      exact ih _ _ st' hn' (by rw [hstep]; omega) hi' (by rw [hstep]; exact hP')
    · simp only [dif_neg h]
      have : i = range.stop + 1 := by
        simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
        omega
      subst this
      exact ⟨st, rfl, hP⟩

theorem vecSetGet (v : Vector (Option TLB_Entry) 64) (n j : Nat) (hn : n < 64) :
    (vectorUpdate v n none)[j]! = if j = n then none else v[j]! := by
  unfold vectorUpdate
  by_cases hj : j < 64
  · by_cases h : j = n
    · subst h; simp [Vector.set!, hj]
    · simp [Vector.set!, h, hj]
      first
      | simp [Array.getElem_setIfInBounds, Ne.symm h]
      | (rw [Array.getElem_setIfInBounds_ne]; rfl; omega)
  · have hjn : ¬ j = n := by omega
    simp only [hjn, ↓reduceIte]
    first
    | (rw [getElem!_neg, getElem!_neg] <;> simp <;> omega)
    | simp [Vector.set!, hj]

/-- `flush_TLB none none` empties every TLB slot (the core of Rocq
`UserretDefs.exec_execute_SFENCE_VMA_S`). -/
theorem execFlushTLBAll (s : ExecSt) :
    ∃ tlbvec' : Vector (Option TLB_Entry) 64, exec (flush_TLB none none) s = some ((), s.setReg .tlb tlbvec') ∧
      ∀ i : Nat, i < 64 → tlbvec'[i]! = none := by
  unfold flush_TLB
  exec_run
  generalize hx : exec (forIn (m := SailM) (_ : IntRange) () _) s = x
  have hlen : (Vector.length (s.regs .tlb) : Int) - 1 = 63 := rfl
  obtain ⟨st', hex, v, rfl, hv⟩ : ∃ st', x = some ((), st') ∧
      ∃ v : Vector (Option TLB_Entry) 64, st' = s.setReg .tlb v ∧ ∀ j : Nat, (j : Int) < 63 + 1 → v[j]! = none :=
    hlen ▸ hx ▸ execForInInv _ rfl _ (fun i st => ∃ v : Vector (Option TLB_Entry) 64, st = s.setReg .tlb v ∧
      ∀ j : Nat, (j : Int) < i → v[j]! = none) s ⟨s.regs .tlb, (ExecSt.setReg_self s .tlb).symm, by
        intro j hj; simp at hj; omega⟩ (by show (0 : Int) ≤ _ + 1; rw [hlen]; decide) (fun i st hi hP => by
        obtain ⟨v, rfl, hv⟩ := hP
        have hi' : 0 ≤ i ∧ i ≤ 63 := by
          simp only [Membership.mem, show (1 : Int) > 0 from by decide, ite_true] at hi
          rw [hlen] at hi
          omega
        exec_run [ExecSt.setReg_regs, RegFile.set_same]
        have e : (v[i]! : Option TLB_Entry) = v[i.toNat]! := rfl
        rw [e]
        cases hvi : v[i.toNat]! with
        | none =>
          refine ⟨_, rfl, v, rfl, fun j hj => ?_⟩
          by_cases hji : (j : Int) < i
          · exact hv j hji
          · have : j = i.toNat := by omega
            subst this; exact hvi
        | some ent =>
          have hfl : flush_TLB_Entry ent none none = true := by
            unfold flush_TLB_Entry; rfl
          exec_run [hfl, ExecSt.setReg_regs, RegFile.set_same, ExecSt.setReg_setReg_same]
          refine ⟨_, rfl, vectorUpdate v i.toNat none, rfl, fun j hj => ?_⟩
          rw [vecSetGet v i.toNat j (by omega)]
          split
          · rfl
          · exact hv j (by omega))
  refine ⟨v, ?_, ?_⟩
  · rw [hex]
  · intro j hj; exact hv j (by omega)

/-- Rocq `UserretDefs.exec_execute_SFENCE_VMA_S`. -/
theorem execExecuteSFENCEVMAS (s : ExecSt) (hcp : s.regs .cur_privilege = .Supervisor)
    (htvm : (_get_Mstatus_TVM (s.regs .mstatus) == 1#1) = false) :
    ∃ tlbvec' : Vector (Option TLB_Entry) 64,
      exec (execute (.SFENCE_VMA (zreg, zreg))) s = some (RETIRE_SUCCESS, s.setReg .tlb tlbvec') ∧
      ∀ i : Nat, i < 64 → tlbvec'[i]! = none := by
  obtain ⟨v, hfl, hv⟩ := execFlushTLBAll s
  refine ⟨v, ?_, hv⟩
  have h0 : _get_Mstatus_TVM (s.regs .mstatus) = 0#1 := by
    generalize _get_Mstatus_TVM (s.regs .mstatus) = b at htvm ⊢
    revert b; decide
  show exec (execute_SFENCE_VMA zreg zreg) s = _
  unfold execute_SFENCE_VMA
  have hz : (zreg != zreg) = false := rfl
  exec_run [hz, hcp, h0]
  erw [hfl]

/-! ## 6. `csrw pmpcfg0` (Rocq `WpGprCsrwA`) -/

/-- Rocq `WpGprCsrwA.pmpWriteCfg_val`. -/
def pmpWriteCfgVal (cfg v : BitVec 8) : BitVec 8 :=
  if pmpLocked cfg then cfg
  else
    let c := Mk_Pmpcfg_ent (v &&& 0x9F#8)
    let c := if ((_get_Pmpcfg_ent_W c == 1#1) && (_get_Pmpcfg_ent_R c == 0#1)) = true
      then _update_Pmpcfg_ent_R (_update_Pmpcfg_ent_W (_update_Pmpcfg_ent_X c 0#1) 0#1) 0#1 else c
    if (match pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A c) with
        | .OFF => true | .TOR => true | .NA4 => (true && sys_pmp_grain == 0) | .NAPOT => true) = true
    then c else _update_Pmpcfg_ent_A c (pmpAddrMatchType_encdec_forwards .OFF)

/-- Rocq `WpGprCsrwA.exec_pmpWriteCfg`. -/
theorem execPmpWriteCfg (cfg v : BitVec 8) (s : ExecSt) :
    exec (pmpWriteCfg cfg v) s = some (pmpWriteCfgVal cfg v, s) := by
  unfold pmpWriteCfg pmpWriteCfgVal
  cases hl : pmpLocked cfg
  · cases hw : ((_get_Pmpcfg_ent_W (Mk_Pmpcfg_ent (v &&& 0x9F#8)) == 1#1) &&
        (_get_Pmpcfg_ent_R (Mk_Pmpcfg_ent (v &&& 0x9F#8)) == 0#1)) <;>
    exec_run [hw, pmp_write_only_reserved_behavior, execIte] <;> split <;>
    (rename_i h; simp only [h, ↓reduceIte, Bool.false_eq_true, sys_pmp_grain]; try rfl)
  · rfl

/-- Rocq `WpGprCsrwA.pmp_cfg_step`: the `i`-th byte of `v` written to entry `i`. -/
def pmpCfgStep (v : BitVec 64) (s : ExecSt) (i : Nat) : ExecSt :=
  s.setReg .pmpcfg_n (vectorUpdate (s.regs .pmpcfg_n) i
    (pmpWriteCfgVal (s.regs .pmpcfg_n)[i]! (Sail.BitVec.extractLsb v (8 * i + 7) (8 * i))))

/-- Rocq `WpGprCsrwA.pmpcfg0_final`. -/
def pmpcfg0Final (v : BitVec 64) (s : ExecSt) : ExecSt :=
  pmpCfgStep v (pmpCfgStep v (pmpCfgStep v (pmpCfgStep v (pmpCfgStep v (pmpCfgStep v (pmpCfgStep v
    (pmpCfgStep v s 0) 1) 2) 3) 4) 5) 6) 7

/-- The first `k` steps of `pmpcfg0Final`. -/
def pmpCfgUpto (v : BitVec 64) (s : ExecSt) : Nat → ExecSt
  | 0 => s
  | k + 1 => pmpCfgStep v (pmpCfgUpto v s k) k

theorem execPmpWriteCfgReg0 (v : BitVec 64) (s : ExecSt) :
    exec (pmpWriteCfgReg 0 v) s = some ((), pmpcfg0Final v s) := by
  unfold pmpWriteCfgReg
  exec_run
  generalize hx : exec (forIn (m := SailM) (_ : IntRange) () _) s = x
  obtain ⟨st', hex, hst⟩ : ∃ st', x = some ((), st') ∧ st' = pmpCfgUpto v s ((7 : Int) + 1).toNat :=
    hx ▸ execForInInv _ rfl _ (fun i st => st = pmpCfgUpto v s i.toNat) s rfl (by decide) (fun i st hi hP => by
      subst hP
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
        simp only [Membership.mem, show (1 : Int) > 0 from by decide, ite_true] at hi
        omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · exec_run [execPmpWriteCfg]
        exact ⟨_, rfl, rfl⟩)
  rw [hex, hst]
  rfl

theorem execWriteCSRPmpcfg0 (v : BitVec 64) (s : ExecSt) :
    ∃ r, exec (write_CSR 0x3A0#12 v) s = some (.Ok r, pmpcfg0Final v s) := by
  rw [write_CSR_pmpcfg0]
  unfold pmpReadCfgReg
  exec_run [execPmpWriteCfgReg0]
  exact ⟨_, rfl⟩

/-- Rocq `WpGprCsrwA.exec_execute_csrw_pmpcfg0` (`csrw pmpcfg0, rs1` in M-mode; `x0` reads zero). -/
theorem execExecuteCsrwPmpcfg0 (rs1 : BitVec 5) (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine) :
    exec (execute_CSRReg 0x3A0#12 (.Regidx rs1) zreg .CSRRW) s =
      some (RETIRE_SUCCESS, pmpcfg0Final (s.gpr rs1) s) := by
  obtain ⟨r, hw⟩ := execWriteCSRPmpcfg0 (s.gpr rs1) s
  rw [execExecuteCSRRegCsrw]
  exact execDoCSRCsrwP _ _ _ s _ _ hcp
    (execCheckCSRResultCsrwM _ s (by csr_dispatch_eq) (by decide) (by rfl) (by csr_dispatch_eq))
    (by decide) (by decide) (by decide) hw rfl

end Weak
