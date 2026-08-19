(* LinkSysMkdir.v -- instantiates the sys_mkdir proof against its five
   callees' proofs.  Sealed, so this is the only place the six ever meet.

   sys_mkdir is the FIRST syscall-level consumer of the sealed create
   contract, so this is also the first Link file whose cone contains
   [LinkCreateFreshTy.v]'s [Lemma create_fresh_ty] (an AXIOM until item 7).  Nothing else new
   enters: begin_op / argstr / iunlockput / end_op are all already in
   LinkSysChdir.v's cone.

   The two things the composition actually rests on, both recorded at the
   point of use in SpecSysMkdir.v's header:

   - the [ok = true] LOG FLOOR in create's post.  [iunlockput(ip)] at +0x2e
     runs BEFORE [end_op] and wants [SpecIput.iput_units] in hand; nothing
     between create's return and that call mints a unit, so the call is
     payable only out of create's residue.  On the mkdir arm the floor is
     ATTAINED ([CreateBudget.cr_budget_mkdir]'s [u6 = 3]), i.e. this cone
     has zero log slack;
   - the [ok = true] IREF FLOOR.  create keeps one slot out on success and
     the [iunlockput] hands it back, which is what closes the reference
     ledger at [ns' + 1 <= ns].

   panic is NOT a module here.  Every panic sys_mkdir can reach is inside a
   callee; the [kernel_data] / [panic_env] the contract takes are threaded
   down to the callees' own arms.

   So this cone's assumption count is the five platform axioms plus funext.
   (It carried [create_fresh_ty] too until item 7 proved the span, and it
   also used to carry
   [ProofIput.iput_acquiresleep_order_ADMITTED] in through iunlockput; that
   axiom is gone -- claude-notes/projects/iput-acquiresleep.md.) *)
Require Import LinkBeginOp LinkArgstr LinkCreate LinkIunlockput LinkEndOp
        ProofSysMkdir.

Module SysMkdir := SysMkdirProof BeginOp Argstr Create Iunlockput EndOp.
