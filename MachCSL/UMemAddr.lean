/-
MachCSL: **the data address of a user access, and `vmem_read` /
`vmem_write`** (brief `notes/briefs/user_layer.md` §2.1 G9, lane U2-M1).

Rocq: `UserMemAccess` §9 (`exec_transform_effective_address_u`: at User,
with `senvcfg.PMM = 0`, pointer masking is the identity), and the
`vmem_read`/`vmem_write` fronts of `UserMemArmsBase`.

`get_transformed_data_addr rs off acc w` reads the base register (a
hypothesis in the walker's shape, `runRW D orc s (rX_bits rs) = some (b, s,
orc)` -- lane U1-X1's GPR facts at a symbolic index) and answers
`Virtaddr (b + off)`: pointer masking applies to a user data access
(`MXR = 0`, `umaDAcc`) but its length is `0` (`senvcfg = 0`), so the address
is untransformed.  `uma_vmem_read`/`uma_vmem_write` then hand the access to
`vmem_read_addr`/`vmem_write_addr` (UMemAccess, UMemStore).
-/
import MachCSL.UMemRam
import MachCSL.UWalk
import MachCSL.UWalkRun
import MachCSL.Tactics

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- The user DATA access kinds (the kinds `vmem_read`/`vmem_write` and the
AMOs issue at U). -/
def umaDAcc : MemoryAccessType mem_payload → Bool
  | .Load .Data => true
  | .Store .Data => true
  | .LoadReserved (_, _, .Data) => true
  | .StoreConditional (_, _, .Data) => true
  | .Atomic (_, _, _, .Data, .Data) => true
  | _ => false

theorem umaDAcc_utrAcc (acc : MemoryAccessType mem_payload) (h : umaDAcc acc = true) : utrAcc acc = true := by
  rcases acc with p | p | ⟨_, _, p⟩ | ⟨_, _, p⟩ | ⟨_, _, _, p, q⟩ | _ | c <;>
    (try cases p) <;> (try cases q) <;> simp [umaDAcc] at h <;> rfl

/-- Pointer masking applies to a user data access when `MXR = 0`. -/
theorem uma_pmm_applicable (acc : MemoryAccessType mem_payload) (h : umaDAcc acc = true) (ms : BitVec 64)
    (hmxr : BitVec.extractLsb' 19 1 ms = 0#1) :
    (acc != MemoryAccessType.InstructionFetch () &&
      (acc != MemoryAccessType.Load mem_payload.PageTableEntry &&
        (acc != MemoryAccessType.Store mem_payload.PageTableEntry &&
          ((Privilege.User == Privilege.Machine || _get_Mstatus_MXR ms == 0#1) &&
            Functions.xlen == 64)))) = true := by
  rw [show _get_Mstatus_MXR ms = BitVec.extractLsb' 19 1 ms from rfl, hmxr]
  rcases acc with p | p | ⟨_, _, p⟩ | ⟨_, _, p⟩ | ⟨_, _, _, p, q⟩ | _ | c <;>
    (try cases p) <;> (try cases q) <;> simp [umaDAcc] at h <;> rfl

/-- Pointer masking with `PMLEN = 0` is the identity. -/
theorem uma_pm_transform_VA0 (va : BitVec 64) : pm_transform_VA (.Virtaddr va) 0 = .Virtaddr va := by
  simp only [pm_transform_VA, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb,
    virtaddr.Virtaddr.injEq, Functions.xlen]
  sail_norm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The data-address transform at User** (Rocq §9): the identity. -/
theorem uma_transform_effective_address_U (D : UFoot) (orc : UOrc) (s : UWSt) (hp : UtrPins D s)
    (hw : UwkPins D s.file)
    (hds : D.Dr .senvcfg = true) (hsenv : s.file .senvcfg = 0#64)
    (hmxr : BitVec.extractLsb' 19 1 (s.file .mstatus) = 0#1)
    (va : BitVec 64) (acc : MemoryAccessType mem_payload) (hacc : umaDAcc acc = true) :
    runRW D orc s (transform_effective_address (.Virtaddr va) acc) = some (.Virtaddr va, s, orc) := by
  obtain ⟨hms, hcpD, hsatp, hcp, ⟨hsxl, hmprv⟩, ⟨hmode, hasid⟩⟩ := hp
  have htm := utr_translationMode_U D orc s hms hsatp hsxl hmode
  have hpmm := uma_pmm_applicable acc hacc _ hmxr
  uwk_pins hw
  uwk_run [htm, hcp, utr_effPriv _ _ _ hmprv]
  rw [uma_pm_transform_VA0]

/-- The data address of a user access: the base register plus the offset,
untransformed (Rocq `exec_transform_effective_address_u` under
`exec_ext_data_get_addr`). -/
theorem uma_get_transformed_data_addr (D : UFoot) (orc : UOrc) (s : UWSt) (hp : UtrPins D s)
    (hw : UwkPins D s.file) (hds : D.Dr .senvcfg = true) (hsenv : s.file .senvcfg = 0#64)
    (hmxr : BitVec.extractLsb' 19 1 (s.file .mstatus) = 0#1) (rs : regidx) (b off : BitVec 64)
    (hrx : runRW D orc s (rX_bits rs) = some (b, s, orc)) (acc : MemoryAccessType mem_payload)
    (hacc : umaDAcc acc = true) (w : Nat) :
    runRW D orc s (get_transformed_data_addr rs off acc w) = some (.Ext_DataAddr_OK (.Virtaddr (b + off)), s, orc) := by
  have ht := uma_transform_effective_address_U D orc s hp hw hds hsenv hmxr (b + off) acc hacc
  unfold get_transformed_data_addr ext_data_get_addr
  uma_seq hrx
  uma_pures
  uma_seq ht
  uma_pures
  rfl

/-- **`vmem_read`**: the data address, then `vmem_read_addr` at it. -/
theorem uma_vmem_read (D : UFoot) (orc orc' : UOrc) (s s' : UWSt) (rs : regidx) (off : BitVec 64) (w : Nat)
    (acc : MemoryAccessType mem_payload) (aq rl res : Bool) (va : BitVec 64)
    (x : Result (BitVec (8 * w)) ExecutionResult)
    (hgt : runRW D orc s (get_transformed_data_addr rs off acc w) = some (.Ext_DataAddr_OK (.Virtaddr va), s, orc))
    (hva : runRW D orc s (vmem_read_addr (.Virtaddr va) w acc aq rl res) = some (x, s', orc')) :
    runRW D orc s (vmem_read rs off w acc aq rl res) = some (x, s', orc') := by
  unfold vmem_read
  sail_norm
  uma_seq hgt
  uma_pures
  uma_seq hva
  uma_pures
  try rfl

/-- **`vmem_write`**: the data address, then `vmem_write_addr` at it. -/
theorem uma_vmem_write (D : UFoot) (orc orc' : UOrc) (s s' : UWSt) (rs : regidx) (off : BitVec 64) (w : Nat)
    (data : BitVec (8 * w)) (acc : MemoryAccessType mem_payload) (aq rl res : Bool) (va : BitVec 64)
    (x : Result Bool ExecutionResult)
    (hgt : runRW D orc s (get_transformed_data_addr rs off acc w) = some (.Ext_DataAddr_OK (.Virtaddr va), s, orc))
    (hva : runRW D orc s (vmem_write_addr (.Virtaddr va) w data acc aq rl res) = some (x, s', orc')) :
    runRW D orc s (vmem_write rs off w data acc aq rl res) = some (x, s', orc') := by
  unfold vmem_write
  sail_norm
  uma_seq hgt
  uma_pures
  uma_seq hva
  uma_pures
  try rfl

end MachCSL
