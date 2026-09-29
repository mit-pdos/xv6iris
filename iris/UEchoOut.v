(* ===================================================================== *)
(*  UEchoOut.v -- ECHO'S CONSOLE CURSOR FAMILY, and the pure facts about  *)
(*  its output (the argv words on the alternative, the two .rodata bytes).*)
(*                                                                       *)
(*  <echo> is the program on the GOOD alternative of a completed line     *)
(*  ([EchoDisc.line_alts_of ws !!! 0]).  Its own share of that            *)
(*  alternative is the output [wl_line (drop 1 ws)] -- the line minus its *)
(*  command name; the shell writes the prompt after it reaps -- and it    *)
(*  writes it two calls per argument:                                     *)
(*                                                                       *)
(*      write(1, argv[i], strlen(argv[i]))                                *)
(*      write(1, i + 1 < argc ? the space : the newline, 1)               *)
(*                                                                       *)
(*  [ech v ps0 cs0 I0 P p] says [p] of those bytes are out and the era's  *)
(*  cursor says so -- the generic cursor ([StageRec.CurRec]) at echo's    *)
(*  stage -- with [echq] its exit payload and [ech_step] its byte step;   *)
(*  [echo_out_argv] / [out_argv_at] read argv as the alternative's words. *)
(*                                                                       *)
(*  WHAT LEFT (lane user-once, B3, 2026-09-27).  This file used to pay    *)
(*  echo's whole walk itself: the console chain ([ech_chain_at]), the     *)
(*  deposit and post of one write at row 16 ([kecho_w_of_link_data_at],  *)
(*  the text-half twin [kecho_w_of_link_txt_at] with [echo_wtxt]), the    *)
(*  payment of the chain ([kecho_pay_of_link_at]) and the ENTRY at the    *)
(*  era's stage ([echo_uexec_slot_at]) -- the per-destination copy of     *)
(*  what the endpoint interface now states once: the console is a device *)
(*  of [UkHandler.ep_iface] ([UkConsOut], whose write law was moulded on  *)
(*  the chain here), the entry is [UkTreeEntry]'s at a handler parameter, *)
(*  and echo at the console is its instance at the union's record         *)
(*  ([UkUnionEntries.uecho_cons_image_entry]).  Nothing consumed the      *)
(*  copy any more, and it is gone.                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UmodeArith.
(* ...and [UserHeap] LAST among the libraries: [UmodeAbi.uargs] has fields
   named [ua_ptr] and [ua_len] as well, and it is [UserHeap.uarg]'s that
   echo's argument vector is spelled with. *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import VcGen.
Require Import WpUart.
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import LineWords.   (* [wl_sp] / [wl_nl] / [wl_off] *)
Require Import EchoDisc.
Require Import EchoOut.
Require Import EchoLinks.
Require Import StageRec.       (* the cursor / stage record *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S0  THE PURE HALF                                                     *)
(*                                                                       *)
(*  THE STAGE MOVED (lane LINK-GEN-3).  [echo_stage] and the three        *)
(*  lemmas under it -- and [echcs] -- are [StageRec.v]'s now: they are    *)
(*  what the echo instance of [StageRec.CurRec] is built out of, and      *)
(*  that record sits below this file.                                     *)
(* ===================================================================== *)

(* a word of the line, read back through [!!] so that [LineWords]' lemmas
   -- every one of which is keyed on [ws !! i = Some w] -- apply *)
Lemma ws_at (ws : list (list (bv 8))) (i : nat) :
  (i < length ws)%nat -> ws !! i = Some (ws !!! i).
Proof.
  intro Hi. destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
  by rewrite Hw list_lookup_total_alt Hw.
Qed.

(* THE TWO BYTES ECHO WRITES THAT ARE NOT argv'S are the line's own two
   blanks -- the separator the join puts between words and the newline it
   closes with ([LineWords.wl_sp] / [wl_nl]).  They had a second spelling
   here; they do not now, and WHERE they land is [EchoDisc.out_sep]
   and [out_last] rather than two offsets.  These two readings stay
   closed: they are echo's .rodata, which is a dump. *)
Lemma echo_sep_ro : echo_ro !! UkEcho.echo_sep_ptr = Some wl_sp.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_nl_ro : echo_ro !! UkEcho.echo_nl_ptr = Some wl_nl.
Proof. vm_compute. reflexivity. Qed.

(* THE READING THAT MAKES THE TEXT LEAF TRUE now LIVES IN THE ENGINE
   ([UserHeap.lazy_free_ux_addr], the twin of [UserHeap.lazy_free_uw_addr]
   one test weaker on the permission side; lane TXT-ROW).  It was proved
   here while [echo_wtxt] was a premise, because that is where the need for
   it was visible; it had to move down for the leaf that hands the row out
   ([UkRunSys.wp_uk_ecall_write_chain_txt]) to use it, and nothing in this
   file refers to it any more. *)

(* THE KERNEL'S COUNT IS THE CALLER'S REQUEST ([UShLine.ush_count_is_cap]
   at echo's own shape): argument 2 reaches file.c as a 32-bit INT and the
   walk names it as a [nat], and the two agree below the sign boundary --
   which [UserHeap.ustr] carries for a string and which is closed at one
   byte. *)
Lemma echo_count_is (nb : nat) :
  (Z.of_nat nb < 2 ^ 31)%Z ->
  sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
Proof.
  intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
  assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
    by (apply uint_moi; unfold Z64; lia).
  rewrite uint_unsigned in Hu.
  rewrite /sys_rw_count. unfold bv_signed.
  rewrite trunc32_subrange subrange_31_0_unsigned Hu.
  rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
  assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
Qed.

(* echo's own reading of its argument vector: it IS the line's words,
   and argument [i] sits in the alternative where the OUTPUT join puts
   it ([EchoDisc.out_cur]) -- because echo's output IS that join.
   Argument 0 is the command name, which echo does not print.

   NOT "argc is three and each is five bytes at offsets 0 and 6".  It is
   stated in the ERA's vocabulary rather than the shell's, so that
   nothing here depends on which parser produced the vector; lane
   IO-LEAF's M3 supplies it off the exec channel. *)
(* AT THE ALTERNATIVE'S BYTES, NOT AT [line_alts_of] (lane LINK-GEN-3).
   The reading is the same one at every era; what changes is which list
   the era's own model puts there, so the list is a parameter and
   [echo_out_argv] is this at the echo era's. *)
Definition out_argv_at (A : list (bv 8)) (ws : list (list (bv 8)))
    (args : list uarg) : Prop :=
  length args = length ws
  /\ forall (i : nat) (g : uarg), (1 <= i)%nat -> args !! i = Some g ->
       ua_len g = length (ws !!! i)
       /\ forall j : nat, (j < ua_len g)%nat ->
            A !! (out_cur ws i + j)%nat = Some (ua_bytes g j).

Definition echo_out_argv (ws : list (list (bv 8))) (args : list uarg)
  : Prop := out_argv_at (line_alts_of ws !!! 0%nat) ws args.


(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (LinkRec's pattern).                *)
(*                                                                       *)
(*  Every name this file exported is the generic one at                   *)
(*  [StageRec.echo_cur_inst], recovered by a [Definition] with NO PROOF    *)
(*  TEXT -- so no landed echo statement moves and [make audit-echo-only]  *)
(*  does not change.  If one of these ever needs a tactic, a statement    *)
(*  has moved.                                                           *)
(* ===================================================================== *)
Section UEchoOutEcho.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.
  Context `{PS : uprogSG Σ}.

  Local Notation CE := (echo_cur_inst T γ).

  (* =================================================================== *)
  (*  S1  THE CURSOR FAMILY                                              *)
  (*                                                                     *)
  (*  "[p] of echo's output bytes are out, and the era's cursor says so"  *)
  (*  -- or the era is TAINTED.  The choice list grows at the FIRST byte  *)
  (*  and not before, which is the whole content of [StageRec.echcs].    *)
  (* =================================================================== *)
  Definition ech (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (P p : nat) : iProp Σ :=
    ck_cur CE (S gen_id) v (MkEchoStg ps0 cs0 I0 P) p.

  Global Instance ech_timeless v ps0 cs0 I0 P p :
    Timeless (ech v ps0 cs0 I0 P p).
  Proof using HTT. rewrite /ech. apply _. Qed.

  (* ...AND ECHO'S EXIT PAYLOAD, which is that family at its END and is
     STATUS-INDEPENDENT ([UkRun.ukn_const]): echo exits with 0 and its
     parent reaps it at whatever status the walk passed, and what the
     parent is owed is the same either way. *)
  Definition echq (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat)
    : Z -> iProp Σ := fun _ => ech v ps0 cs0 I0 P (length (wl_line (drop 1 ws))).

  Definition ech_step (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P p : nat)
      (b : bv 8) (Φ : iProp Σ) :
    echo_stage ps0 cs0 I0 ws P ->
    line_alts_of ws !!! 0%nat !! p = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ech v ps0 cs0 I0 P p -∗
    (ech v ps0 cs0 I0 P (S p) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ
    := ck_step CE (S gen_id) v (MkEchoStg ps0 cs0 I0 P) ws p b Φ.


End UEchoOutEcho.
