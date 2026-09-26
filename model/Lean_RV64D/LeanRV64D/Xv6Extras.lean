-- ======================================================================
-- Xv6Extras.lean -- THE LEAN REALISATIONS OF THE SAIL PLATFORM HOOKS.
--
-- HAND-WRITTEN.  This is the Lean twin of Rocq's
-- `model-xv6iris/xv6iris_extras.v` (/shared/xv6rocq), and mirrors it
-- definition for definition.  The master copy is `model/Xv6Extras.lean`;
-- `tools/regen_sail_model.sh` hands it to sail as a SECOND
-- `--lean-import-file` (after the fork's `handwritten_support/RiscvExtras.lean`),
-- so sail copies it verbatim to `model/Lean_RV64D/LeanRV64D/Xv6Extras.lean`
-- and every generated module imports it.  Edit the master copy only; the
-- regen script checks the two are identical.
--
-- WHAT IT IS FOR.  The platform hooks below are Sail `val`s with no Sail
-- body.  Their `lean`-backend spelling is their Sail name (the pinned fork
-- gives them no `lean:` extern binding), and the fork's
-- `RiscvExtras.lean` declares each one as a bare root-level `axiom` so the
-- model compiles for a consumer that supplies nothing else.  An opaque
-- `SailM` term cannot be stepped by the free-monad language, so under those
-- axioms an `lr`/`sc` in arbitrary user code is IRREDUCIBLE (a NotStuck
-- hole, not an inconvenience), and the decode gates on
-- `sys_enable_experimental_extensions` are undecided.
--
-- HOW IT OVERRIDES.  Rocq overrides by `Require` order.  Lean has no
-- redeclaration, but it has namespace priority: every generated function
-- body lives in `namespace LeanRV64D.Functions`, and Lean resolves an
-- identifier to a declaration in an enclosing namespace BEFORE it looks at
-- the root (and at `open`s).  So the definitions below, in
-- `LeanRV64D.Functions`, are what the generated model calls; the fork's
-- root-level axioms stay declared but unused, and drop out of every
-- `#print axioms`.  Nothing generated and nothing from the fork is patched.
--
-- WHAT IS DEFINED OUTRIGHT (as in Rocq).  The three `SailM`-valued hooks
-- have NO observable effect on the state this model carries: the LR/SC
-- reservation set is platform state outside the register file and memory,
-- and the HTIF terminal is not modelled.  `pure ()` is therefore an exact
-- realisation.  The experimental-extensions flag is `false`, as in
-- sail-riscv's own `riscv_extras.v`.
--
-- WHAT STAYS UNKNOWN (as in Rocq).  The two reservation PREDICATES.  Sail
-- declares them `pure`, so each is a FIXED function within one evaluation,
-- and the honest reading is "an arbitrary but fixed platform predicate".
-- Rocq realises them over two `Parameter`s; here they are `opaque`
-- constants (`xv6_resv_matches`, `xv6_resv_is_valid`), whose values the
-- kernel never unfolds, so every proof that reads one must handle both
-- answers -- exactly the Rocq obligation.  Do NOT replace them by concrete
-- functions: the theorem would then describe one platform (e.g. one whose
-- SC always fails) instead of every platform.
--
-- NOT OVERRIDDEN (as in Rocq): `plat_term_read`, `get_16_random_bits` and the
-- softfloat `riscv_f*` family.  Their results are CONSUMED, so any
-- realisation would fabricate data; a hart that reaches one stays stuck.
-- ======================================================================

import Sail.Sail
import LeanRV64D.Defs

open Sail
open ConcurrencyInterfaceV1

namespace LeanRV64D.Functions

-- ---- LR/SC reservation: the two effectful hooks ----------------------
-- Both are the identity on the modelled state, so `pure ()` is exact.

def load_reservation (_addr : physaddrbits) (_width : Nat) : SailM Unit :=
  pure ()

def cancel_reservation (_ : Unit) : SailM Unit :=
  pure ()

-- ---- LR/SC reservation: the two predicates ---------------------------
-- Arbitrary but fixed.  These two opaque constants are the whole unknown
-- content of this file.

opaque xv6_resv_matches : physaddrbits → Bool
opaque xv6_resv_is_valid : Bool

def match_reservation (addr : physaddrbits) : Bool := xv6_resv_matches addr

def valid_reservation (_ : Unit) : Bool := xv6_resv_is_valid

-- ---- HTIF terminal output --------------------------------------------
-- The terminal is not part of the modelled state.

def plat_term_write (_ : BitVec 8) : SailM Unit :=
  pure ()

-- ---- Experimental extensions: off ------------------------------------

def sys_enable_experimental_extensions (_ : Unit) : Bool := false

end LeanRV64D.Functions
