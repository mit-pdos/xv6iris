(* SyncHook.v -- the OPTIONAL SYNC HOOK and its receipt, named once where
   both tiers can see them (claude-notes/design/sync.md section 4.3 item 4).

   [SpecSysSync]'s contract takes [hook_opt gen_id oQ] in and hands
   [Q_opt oQ] back; the process tier states the same pair ([UkSync]'s
   ecall leaf, [UexecExecInst]'s row 22) and sits on the other side of the
   file-system tower, so the two definitions live here, over
   [RiscvPtsto.riscv_sync_hook] alone, and not in the kernel spec. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
Require Import RiscvPtsto.

Section sync_hook.
  Context `{!riscvGS Σ}.

  (* At [None] both are [emp] (the dispatcher's own arm 22, a program that
     deposits no hook); at [Some Q] the caller hands in the era's hook at
     [Q] and gets [Q] back, fired once at a ghost commit. *)
  Definition hook_opt (gen : nat) (oQ : option (iProp Σ)) : iProp Σ :=
    (match oQ with None => emp | Some Q => riscv_sync_hook gen Q end)%I.

  Definition Q_opt (oQ : option (iProp Σ)) : iProp Σ :=
    (match oQ with None => emp | Some Q => Q end)%I.
End sync_hook.
