-- xv6iris: an Iris (iris-lean) weakest-precondition development for the
-- xv6 RISC-V kernel over the Sail RISC-V Lean model.
--
-- Port of the Rocq/Iris development in ../iris to Lean 4. See lean/README.md.
--
-- Layers (bottom-up):
--   SailMonad — the Sail free/interaction monad (effects as data; interposable)
--   Interp    — the exec/run interpreter over it + determinism
--   Lang      — the iris-lean `Language` instance (operational semantics)
--   Ptsto     — ghost state, points-to, stateInterp, the read bridge (reg_valid)
import Xv6Iris.Hello
import Xv6Iris.ModelBytes
import Xv6Iris.SailMonad
import Xv6Iris.Interp
import Xv6Iris.Lang
import Xv6Iris.Ptsto
