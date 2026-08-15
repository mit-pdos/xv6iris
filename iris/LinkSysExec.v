(* LinkSysExec.v -- the only file where sys_exec's proof meets its callees'.

   Eight functor arguments, and sys_exec is the marshaller in front of the
   largest of them: [Kexec] drags in the whole FS cone, the page-table
   builder and [struct proc] behind this one line (LinkKexec.v).  The other
   seven are the copy-in layer -- argaddr / argstr / fetchaddr / fetchstr --
   plus memset for the argv array and kalloc / kfree for the pages each
   argument is copied into.

   The allocator appears TWICE, as [Kalloc] and [Kfree], because the loop
   allocates a page per argument and both exits give every one of them back;
   see SpecSysExec.v's header on why the kalloc'd pages therefore do not
   appear in the contract at all.

   panic is not a module argument: the contract takes [panic_wp_any] and
   relays it to kalloc, kfree and kexec, never consuming it locally. *)
Require Import LinkArgaddr LinkArgstr LinkMemsetArray LinkFetchaddr LinkKalloc
        LinkFetchstr LinkKexec LinkKfree
        ProofSysExec.

Module SysExec := SysExecProof Argaddr Argstr MemsetArray Fetchaddr Kalloc
                               Fetchstr Kexec Kfree.
