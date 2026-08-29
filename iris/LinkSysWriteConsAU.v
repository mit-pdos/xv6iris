(* LinkSysWriteConsAU.v -- the console-write syscall seal, CLOSED.

   [ProofSysWriteConsAU]'s functor takes four arguments -- argaddr, argint,
   argfd and filewrite's console arm -- and the first three are the landed
   argument-fetch links every sys_* cone in this tree already uses
   ([LinkSysOpenAU.v] wires twelve callee proofs the same way).  The fourth
   is this campaign's: [LinkFilewriteCons.FilewriteCons], which is
   [SpecFilewriteCons.FILEWRITE_CONS] proved rather than assumed.

   SO [SYSWRITE_CONS_AU] STOPS BEING A SEAL.  Every module type on the path
   from [sys_write]'s dispatch arm down to the UART's THR store is now
   discharged by a proof: argfd -> argint -> argaddr -> filewrite's device
   dispatch -> consolewrite's located walk -> uartwrite's located walk ->
   the transmit lock.  init.c's printf path -- write(1, buf, n) on the
   console descriptor mknod("console", 1, 1) installed -- is proved end to
   end, and what it returns is [SpecSysWriteConsAU.write_cons_arms]: the
   count is the UART's accepted-byte receipt, or filewrite's own sign
   guard's -1.

   AUDIT (machine-checked, [Print Assumptions
   SysWriteConsAU.wp_sys_write_cons_au] on the EC2 mirror at 523cc4e8): THE
   STANDING THREE and nothing else -- [xv6iris_extras.resv_matches],
   [xv6iris_extras.resv_is_valid], [functional_extensionality_dep].  Nothing
   new enters here and nothing new entered below: the whole console-write
   syscall is a theorem over the platform's two reservation primitives and
   funext.  (The three argument-fetch cones are the standing ones; the
   console arm's is [LinkFilewriteCons.v]'s, whose audit is the same three.) *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFilewriteCons
        ProofSysWriteConsAU.

Module SysWriteConsAU := SysWriteConsAUProof Argaddr Argint Argfd
                                             FilewriteCons.
