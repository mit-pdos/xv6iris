(* FileLinks.v -- THE FILE APPLICATION'S CONSOLE LINKS.

   Design of record: claude-notes/design/app-file.md section 4, deliverable
   3.  [EchoOut.v]'s [Section echo_links] at the file claim: the same links
   wrapped onto the kernel's own console contracts, with the era's BOOT FILE
   STATE beside the three bounds a writer already carried, and the era's
   FIRST byte -- which files that state out of the deed's own typed witness
   -- as a link of its own.

   A link runs at [⊤ ∖ ↑uartN Uart0] and opens NOTHING but the port
   invariant: every authority an era has is in the claim the link is handed,
   so no link reaches the application's ledger and [App.al_echo] stays a
   CLOSED entailment, exactly as for the echo application. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import LineModelInst.
Require Import GenLinks.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
Local Open Scope list_scope.

Section file_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.

  (* the record equations, as section parameters: [App.al_echo] hands them
     over at the [boot_fixedGS] literal *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = ftag g).

  (* (R) THE READ LINK.  Beside the window it exports THE ERA'S INPUT AT THE
     WINDOW'S FAR END, its discipline, the era's BOOT STATE and the stage
     the writer has reached -- with the choice list TRUNCATED to the
     window's own line count, because [FileOutPure.alts_pre] ties every
     entry to the line at its index. *)
  Definition fread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((file_taint (fgn_cl g) ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜E_disc_f (seg_of (echoed pops))⌝
           ∗ ⌜forall x : list mobs * bv 8, x ∈ dl ++ ws -> obs_boots x.1 = k⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜disc_input_f (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (vf : file_era) (s0 : fstate),
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ file_era_pin g k vf ∗ f0_lb vf s0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0)
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜rd_stage_f ps0 cs0 (snd <$> (dl ++ ws))⌝))%I.

End file_links.

(* ====================================================================== *)
(*  THE BUNDLE.  The file application's links are what the record         *)
(*  equation gives: every console link of the era is [GenLinks] at this  *)
(*  instance once the console record's claim is [fecl g].  So the bundle *)
(*  a program holds and spends is the EQUATION ITSELF, as a pure         *)
(*  persistent fact, and the links are read off it where they are spent  *)
(*  ([file_links_rd] here, the write interface [GenLinksGl.gcl_glinks]   *)
(*  in [FileLinkGen]).  The record equation stays where [App.al_echo]   *)
(*  hands it over; this is what fills [LinkRec.lk_links] at the file     *)
(*  application.                                                         *)
(* ====================================================================== *)
Section file_links_bundle.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.

  Definition file_links : iProp Σ :=
    ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g⌝%I.
  Global Instance file_links_persistent : Persistent file_links.
  Proof using . rewrite /file_links. apply _. Qed.
End file_links_bundle.
