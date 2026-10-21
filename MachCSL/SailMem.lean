/-
MachCSL: the memory primitives of concurrency interface v2, as single events.

lean-sail v7's `sail_mem_read`/`sail_mem_write` (re-exported by the generated model's
`SpecializationArchSem` as `LeanRV64D.ArchSem.sail_mem_read`/`…write`) are one `memRead`/
`memWrite` event of the request (`Mem_request.toArchSem`, here `memReq`) whose continuation converts between the
event's bits and the model's byte vectors through local `let`-bound functions.  The equations
below restate each primitive as that one event followed by a NAMED conversion (`memReadAns`,
`memWriteAns`), so the program logic and the symbolic executor can match it.  The conversions are
`abbrev`s: on a concrete answer they reduce to the model's value
(`memReadAns (.ok (w, t)) = .Ok (bitvec_to_vecbytes w, bitvec_to_vecbool t)`).

The bits↔bytes round trips themselves (what `read_ram`/`write_ram` do with the vectors) are in
`MachCSL/SailBytes.lean`.
-/
import LeanRV64D.SpecializationArchSem

noncomputable section

namespace MachCSL

open Sail Sail.ArchSem LeanRV64D

/-- The interface request of a model request: lean-sail's `Mem_request.toArchSem` restated as an
`abbrev`, so that its fields (`size = n`, `numTag = nt`, `address`) reduce in the proof mode, whose
unification does not unfold the plain `def`. -/
abbrev memReq {n nt : Nat} (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    MemRequest :=
  { accessKind := req.access_kind, address := req.address, addressSpace := req.address_space,
    size := n, numTag := nt }

/-- What v2's `sail_mem_read` hands the model for the memory's answer. -/
abbrev memReadAns {n nt : Nat} : Except Unit (BitVec (8 * n) × BitVec nt) →
    Result (Vector (BitVec 8) n × Vector Bool nt) Unit
  | .ok (w, t) => .Ok (bitvec_to_vecbytes w, bitvec_to_vecbool t)
  | .error e => .Err e

/-- What v2's `sail_mem_write` hands the model for the memory's answer. -/
abbrev memWriteAns : Except Unit Unit → Result (Option Bool) Unit
  | .ok () => .Ok none
  | .error e => .Err e

/-- A memory read is ONE `memRead` event of the request. -/
theorem sail_mem_read_def {n nt : Nat}
    (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    (LeanRV64D.ArchSem.sail_mem_read req : SailM _) =
      FreeM.impure (Sum.inl (Except.ok (InstructionEffect.memRead (memReq req))))
        (fun v => FreeM.pure (memReadAns v)) := by
  unfold LeanRV64D.ArchSem.sail_mem_read PreSail.sail_mem_read
  simp only []
  congr 1
  funext v
  rcases v with e | ⟨w, t⟩ <;> rfl

/-- A memory write is ONE `memWrite` event of the request, carrying the bits of the bytes. -/
theorem sail_mem_write_def {n nt : Nat}
    (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc)
    (bytes : Vector (BitVec 8) n) (tags : Vector Bool nt) :
    (LeanRV64D.ArchSem.sail_mem_write req bytes tags : SailM _) =
      FreeM.impure (Sum.inl (Except.ok (InstructionEffect.memWrite (memReq req)
          (vecbytes_to_bitvec bytes) (vecbool_to_bitvec tags))))
        (fun v => FreeM.pure (memWriteAns v)) := by
  unfold LeanRV64D.ArchSem.sail_mem_write PreSail.sail_mem_write
  simp only []
  congr 1
  funext v
  rcases v with e | ⟨⟩ <;> rfl

/-- A barrier is ONE `barrier` event. -/
theorem sail_barrier_def (b : barrier_kind) :
    (LeanRV64D.ArchSem.sail_barrier b : SailM Unit) =
      FreeM.impure (Sum.inl (Except.ok (InstructionEffect.barrier b))) (fun v => FreeM.pure v) := rfl

/-- The write announce is ONE `memWriteAnnounce` event. -/
theorem sail_mem_address_announce_def {n nt : Nat}
    (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    (LeanRV64D.ArchSem.sail_mem_address_announce req : SailM Unit) =
      FreeM.impure (Sum.inl (Except.ok (InstructionEffect.memWriteAnnounce (memReq req))))
        (fun v => FreeM.pure v) := rfl

end MachCSL
