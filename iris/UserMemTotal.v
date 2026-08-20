(* ====================================================================== *)
(* UserMemTotal.v -- THE MEMORY ARMS' SHARED CLOSERS, PURE.                *)
(*                                                                        *)
(* Package P4b (claude-notes/projects/user-tier-port.md section 9 and      *)
(* section 14.3 item 3).  [UserTotalU]'s [finish_*] family closes          *)
(* [UserClassifyAsm.base_post] / [rvc_post] for the REGISTER-ONLY arms,    *)
(* where the tree and the byte map do not move: every one of them ends in  *)
(* [u_post_id] / [u_post_gpr] / [u_post_npc] / [u_post_npc_gpr], all of    *)
(* which pin [t' := t] and [mm' := mm].                                    *)
(*                                                                        *)
(* A MEMORY arm cannot use any of them, and not because of the value it    *)
(* writes: a user load runs a page WALK, and a walk may fill the TLB and   *)
(* write back an A/D bit -- so the post state carries a NEW tree and a NEW *)
(* map, which is exactly what [base_post]'s existential [t'] and its       *)
(* [u_mem_step] conjunct are for.  The two closers here are [base_post] /  *)
(* [rvc_post] with those two handed in rather than derived, and they are   *)
(* the ONLY place a memory arm counts the nine conjuncts.                  *)
(*                                                                        *)
(* Everything else about a memory arm -- the translation, the physical     *)
(* access, the execute-level classification -- is a PAIR of facts (an      *)
(* [exec] and its [goodmb] certificate) supplied by the layers below:      *)
(* [UserMemCert] (the composers), [UserMemAccess] / [UserMemMis] (the      *)
(* vmem layer) and [UserMemArms] (the execute layer).  This file adds no   *)
(* machinery of its own beyond the two closers and the trap-result         *)
(* helpers, on purpose: it is the seam, not an engine.                     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import HartLift HartSpan HartMemRun PtBytes.
Require Import PtreeType PtTree.
Require Import UserFrame UserBytes.
Require Import UserPtTree UserExec UserClassify UserClassifyAsm.
Local Open Scope Z_scope.
Import Defs.

Section UserMemTotal.
  Context (pt : uptd).

  (* the two execute states, spelled EXACTLY as [base_post] / [rvc_post]
     spell them ([Local Notation], not [Definition]: an intermediate
     register file behind a [Definition] is a conversion bomb) *)
  Local Notation s0r rsf va := (register_set nextPC (add_vec_int va 4) rsf).
  Local Notation s2r rsf va := (register_set nextPC (add_vec_int va 2) rsf).
  Local Notation s0 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).
  Local Notation s2 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 2) rsf) mm).

  (* ------------------------------------------------------------------- *)
  (* THE TWO CLOSERS.                                                     *)
  (* ------------------------------------------------------------------- *)
  Lemma finish_mem_base (t t' : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i : instruction) (r : ExecutionResult) (w : mword 32)
      (s_x : mstate) :
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va) = Some (r, s_x) ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    reg_agree_on u_Dfix s_x.(sregs) (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb s_x.(sregs)) ->
    u_mem_step pt t t' mm s_x.(mem) ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hlpad Hexec Hgm Hok Hnex Hag Htlb Hst.
    exists i, r, s_x, t'. split_and!;
      first [ exact Hdec | exact Hhv | exact Hlpad
            | exact (or_introl (conj Hexec Hgm))
            | exact Hok | exact Hnex | exact Hag | exact Htlb | exact Hst ].
  Qed.

  (* the same through ONE [ExecuteAs] redirect -- the compressed memory
     instructions expand to their base form and only THEN touch memory, so
     the redirect's own step makes no event and lands where it started *)
  Lemma finish_mem_base_redirect (t t' : ptree) (mm : PtBytes.pamap)
      (rsf : regstate) (va : mword 64) (i other : instruction)
      (r : ExecutionResult) (w : mword 32) (s_x : mstate) :
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va) = Some (ExecuteAs other, s0 rsf mm va) ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    exec (execute other) (s0 rsf mm va) = Some (r, s_x) ->
    goodmb Du_r Du_w (execute other) (s0 rsf mm va) mm = true ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    reg_agree_on u_Dfix s_x.(sregs) (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb s_x.(sregs)) ->
    u_mem_step pt t t' mm s_x.(mem) ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hlpad Hex1 Hg1 Hex2 Hg2 Hok Hnex Hag Htlb Hst.
    exists i, r, s_x, t'. split_and!;
      first [ exact Hdec | exact Hhv | exact Hlpad
            | exact (or_intror (ex_intro _ other
                       (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
            | exact Hok | exact Hnex | exact Hag | exact Htlb | exact Hst ].
  Qed.

  Lemma finish_mem_rvc (t t' : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i other : instruction) (r : ExecutionResult)
      (h : mword 16) (s_x : mstate) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) i rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) ->
    exec (execute i) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    goodmb Du_r Du_w (execute i) (s2 rsf mm va) mm = true ->
    exec (execute other) (s2 rsf mm va) = Some (r, s_x) ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    reg_agree_on u_Dfix s_x.(sregs) (s2r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb s_x.(sregs)) ->
    u_mem_step pt t t' mm s_x.(mem) ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hex1 Hg1 Hex2 Hg2 Hok Hnex Hag Htlb Hst.
    exists i, r, s_x, t'. split_and!;
      first [ exact Hdec | exact Hhv | exact Hzca
            | exact (or_intror (ex_intro _ other
                       (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
            | exact Hok | exact Hnex | exact Hag | exact Htlb | exact Hst ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TWO RESULT SHAPES a memory arm produces, and the ONE post-state    *)
  (* fact each owes.  A retiring access writes at most one gpr (a load) or  *)
  (* nothing (a store); a faulting one delegates the trap and touches no    *)
  (* register at all -- so both are [reg_agree_on u_Dfix] against the       *)
  (* ticked file, and [UserClassifyAsm]'s [u_fix_*] family closes them.     *)
  (* ------------------------------------------------------------------- *)
  Lemma u_ok_retire : u_result_ok RETIRE_SUCCESS.
  Proof. unfold u_result_ok. by left. Qed.

  Lemma u_ok_trap (e : ExceptionType) (xv pcx : mword 64) :
    user_exc e = true ->
    u_result_ok (rv64d_types.Trap (User, make_sync_exception e xv, pcx)).
  Proof.
    intro Hue. unfold u_result_ok. right; left.
    exists e, xv, pcx. split; [reflexivity | exact Hue].
  Qed.

  Lemma u_nex_retire : match RETIRE_SUCCESS with ExecuteAs _ => False | _ => True end.
  Proof. exact I. Qed.

  Lemma u_nex_trap (p : Privilege) (sx : sync_exception) (pcx : mword 64) :
    match rv64d_types.Trap (p, sx, pcx) with ExecuteAs _ => False | _ => True end.
  Proof. exact I. Qed.

End UserMemTotal.
