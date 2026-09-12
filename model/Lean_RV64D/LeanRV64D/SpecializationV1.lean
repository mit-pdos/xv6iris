import Sail
import LeanRV64D.Defs

open Sail ConcurrencyInterfaceV1

namespace LeanRV64D

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.undefined_unit ()
abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.undefined_bit ()
abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.undefined_bool ()
abbrev undefined_int (_ : Unit) : SailM Int := PreSail.undefined_int ()
abbrev undefined_range (low high : Int) : SailM Int := PreSail.undefined_range low high
abbrev undefined_nat (_ : Unit) : SailM Nat := PreSail.undefined_nat ()
abbrev undefined_string (_ : Unit) : SailM String := PreSail.undefined_string ()
abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.undefined_bitvector n
abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := PreSail.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := PreSail.readReg reg

abbrev RegisterRef := @Sail.ConcurrencyInterfaceV1.RegisterRef Register RegisterType

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.assert p s

namespace ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1

abbrev sail_mem_write (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak) : SailM (Result (Option Bool) Arch.abort) :=
  PreSail.sail_mem_write req

abbrev write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    SailM Unit := PreSail.write_ram addr_size data_size _hex_ram addr value

abbrev sail_mem_read (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak) : SailM (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := PreSail.sail_mem_read req

abbrev read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : SailM (BitVec (8 * data_size)) := PreSail.read_ram addr_size data_size _hex_ram addr

abbrev sail_barrier (a : Arch.barrier) : SailM Unit := PreSail.sail_barrier a

abbrev sail_cache_op (op : Arch.cache_op) : SailM Unit := PreSail.sail_cache_op op
abbrev sail_tlbi (op : Arch.tlb_op) : SailM Unit := PreSail.sail_tlbi op
abbrev sail_translation_start (ts : Arch.trans_start) : SailM Unit := PreSail.sail_translation_start ts
abbrev sail_translation_end (te : Arch.trans_end) : SailM Unit := PreSail.sail_translation_end te
abbrev sail_take_exception (f : Arch.fault) : SailM Unit := PreSail.sail_take_exception f
abbrev sail_return_exception (a : Arch.pa) : SailM Unit := PreSail.sail_return_exception a

end ConcurrencyInterfaceV1

abbrev cycle_count (a : Unit) : SailM Unit := PreSail.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := PreSail.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := PreSail.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.PreSailME.run m

def SailME.throw (e : α) : SailME α β := PreSail.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.sailTryCatchE e h

def unwrapValue [Inhabited α] (x : SailM α) : α :=
  match x with
  | .pure x => x
  | _ => default
