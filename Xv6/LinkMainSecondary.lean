/-
Link `main`'s secondary-hart arm: the sealed proof instance clients import
(Rocq `LinkMainSecondary.v`).  Every callee is sealed: cpuid, printk,
kvminithart, trapinithart, plicinithart, scheduler, and kernelvec over
kerneltrap over yield.
-/
import Xv6.ProofMainSecondary
import Xv6.LinkPrintk
import Xv6.LinkKvminithart
import Xv6.LinkTrapinithart
import Xv6.LinkPlicinithart
import Xv6.LinkScheduler
import Xv6.LinkKernelvec
import Xv6.LinkKerneltrap
import Xv6.LinkYield

namespace Xv6

/-- The proved interface of `main`'s secondary arm. -/
theorem MainSecondary : MAIN_SECONDARY :=
  main_secondary_proof Cpuid Printk Kvminithart Trapinithart Plicinithart Scheduler
    (Kernelvec (Kerneltrap Yield))

end Xv6
