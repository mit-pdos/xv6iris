/-
`fileclose` meets its specification, given `acquire`, `release`,
`pipeclose`, `begin_op`, `iput` and `end_op` (Rocq LinkFileclose.v:
`Module Fileclose := FilecloseProof Acquire Release Pipeclose BeginOp Iput EndOp`).
-/
import Xv6.ProofFileclose

namespace Xv6

theorem Fileclose (AC : ACQUIRE) (RE : RELEASE) (PC : PIPECLOSE) (BO : BEGIN_OP) (IP : IPUT)
    (EO : END_OP) : FILECLOSE :=
  fileclose_proof AC RE PC BO IP EO

end Xv6
