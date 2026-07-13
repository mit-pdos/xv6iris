(* M-mode Csr family (decode families CSRReg/CSRImm).
   The CSR read/write leaf lemmas' value-helpers (csr_* addresses, mepc_val,
   *_rdval, *_legalized) appear in the leaves' post-conditions and are shared by
   value with the M-mode boot-code consumers (WpStartNew/WpEntryNew/...). A
   physical merge would duplicate those helpers and break those consumers' proofs
   (LHS/goal mismatch), or import the read+write helper modules back and cycle. So
   the CSR leaves remain in the read/write sub-files and this file re-exports them
   as the consistently-named Csr family access point. *)
Require Export WpGprCsrr WpGprCsrw WpGprCsrwC.
