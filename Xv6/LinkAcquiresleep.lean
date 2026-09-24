/-
`acquiresleep` meets its specification, given `acquire`, `release`,
`myproc`, `sleep_prepare` and `sleep`.
-/
import Xv6.ProofAcquiresleep

namespace Xv6

/-- The store-order form (the primitive one): the acquire edge's receipt,
cashed into `MachCSL.ctxFloor curCtx tl`. -/
theorem AcquiresleepLlb (ACL : ACQUIRE_LLB) (RE : RELEASE) (MP : MYPROC) (SP : SLEEP_PREPARE)
    (SL : SLEEP) : ACQUIRESLEEP_LLB := acquiresleep_llb_proof ACL RE MP SP SL

theorem Acquiresleep (ACL : ACQUIRE_LLB) (RE : RELEASE) (MP : MYPROC) (SP : SLEEP_PREPARE)
    (SL : SLEEP) : ACQUIRESLEEP := (AcquiresleepLlb ACL RE MP SP SL).toACQUIRESLEEP

theorem AcquiresleepNb (AC : ACQUIRE) (RE : RELEASE) (MP : MYPROC) : ACQUIRESLEEP_NB :=
  acquiresleep_nb_proof AC RE MP

end Xv6
