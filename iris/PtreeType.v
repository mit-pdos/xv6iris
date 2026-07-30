(* PtreeType.v -- the INERT page-table description type, and nothing else.

   [ptree] is one page-table node: its page's base ppn, its 512 raw slot
   words, and a subtree wherever the description claims a child.  All of its
   meaning lives in PtTree.v ([ptree_own], [ptree_maps], [ptree_canon], ...);
   this file exists only so that the type sits BELOW RiscvPtsto.v.

   Why: the shared kernel page table's ghost (claude-notes/projects/
   kpt-share.md) is an agreement on the A/D-CANONICAL table, i.e. a resource
   algebra over [leibnizO ptree].  Its gname has to live in [riscvGS] beside
   [kmap_name] -- for exactly the reason recorded there, that a separate
   class would have to be threaded through every sconf-tier file (measured:
   292 files, 507 [Context] sites) -- and [riscvGS] can only name a type
   defined before it.  The definition needs nothing but [mword], so pulling
   it down here costs nothing.                                            *)
From Stdlib Require Import ZArith.
Require Import SailStdpp.Values.
Local Open Scope Z_scope.

Inductive ptree : Type :=
  | PtNode (base : mword 44)
           (ents : mword 9 -> mword 64)
           (kids : mword 9 -> option ptree).

Definition pt_base (t : ptree) : mword 44 :=
  match t with PtNode b _ _ => b end.
Definition pt_ents (t : ptree) : mword 9 -> mword 64 :=
  match t with PtNode _ e _ => e end.
Definition pt_kids (t : ptree) : mword 9 -> option ptree :=
  match t with PtNode _ _ k => k end.
