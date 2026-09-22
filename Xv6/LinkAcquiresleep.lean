/-
`acquiresleep` meets its specification, given `acquire`, `release`,
`myproc`, `sleep_prepare` and `sleep`.
-/
import Xv6.ProofAcquiresleep

namespace Xv6

theorem Acquiresleep (AC : ACQUIRE) (RE : RELEASE) (MP : MYPROC) (SP : SLEEP_PREPARE)
    (SL : SLEEP) : ACQUIRESLEEP := acquiresleep_proof AC RE MP SP SL

theorem AcquiresleepNb (AC : ACQUIRE) (RE : RELEASE) (MP : MYPROC) : ACQUIRESLEEP_NB :=
  acquiresleep_nb_proof AC RE MP

end Xv6
