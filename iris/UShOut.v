(* ===================================================================== *)
(*  UShOut.v -- WHAT PAYS FOR SH'S PROMPT                                 *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane IO-LEAF, M4a.)      *)
(*                                                                       *)
(*  <sh> writes "$ " at the head of every command loop -- [getcmd]'s      *)
(*  [write(2, "$ ", 2)] at 0x10..0x1c -- and the FIRST of those two bytes *)
(*  is the one that RESOLVES ROUND 0 OF THE PROLOGUE: /init printed       *)
(*  eighteen bytes of banner and forked, and what the wire sees next      *)
(*  decides which of [EchoDisc.pro_alts] the round took.  sh's '$' is     *)
(*  alternative 0 ("the session begins"), so it goes through the era's    *)
(*  PROLOGUE link ([EchoLinks.echo_link_pro] at [a = 0]) and files the    *)
(*  index; the ' ' after it is an ordinary byte of the round that is now  *)
(*  fixed, and goes through the plain write link at [ps0 = [0]].          *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN, and why sh's walk cannot do this itself: the   *)
(*  conversion needs row 16's CONCRETE reading -- the console chain it    *)
(*  deposits ([UkWriteLeaf.uwrite_chain_sup]) and the arms it reads back  *)
(*  ([uwrite_no_short]) -- and every file of sh's walk sits BELOW the     *)
(*  file system.  It is [UInitBanner.v]'s job at sh, and it is stated     *)
(*  against [UkSh.ksh_w], the per-CALL obligation sh's walk spends,       *)
(*  because sh's prompt is ONE two-byte write and not two one-byte ones.  *)
(*                                                                       *)
(*  THE SOURCE RUN IS IN THE TEXT HALF.  "$ " is sh's .rodata at 0x1290,  *)
(*  X-and-not-W, so [UserHeap.uheap_ubytes_w] says nothing about it and   *)
(*  the leaf that answers is lane TXT-ROW's -- [UkSh.wp_ksh_write_chain_  *)
(*  txt], over [UkRunSys.wp_uk_ecall_write_chain_txt].  That is the same  *)
(*  route echo's separator and newline take ([UEchoOut.kecho_w_of_link_   *)
(*  txt]).                                                               *)
(*                                                                       *)
(*  WHAT IS STILL OWED (lane IO-LEAF, M4a proper): the TRANSPORT.  The    *)
(*  bundle this file consumes -- the era's cursor at stage 18 -- is       *)
(*  /init's, lent to sh at its fork and carried to the prompt site by     *)
(*  [UkSh.ush_at]; and the row that says sh's fd 2 IS the console is      *)
(*  /init's pinned table, inherited through the exec channel.  Both are   *)
(*  PREMISES here, for [UEchoOut]'s reason: this file says what the link  *)
(*  pays for, not how the credential got here.                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* the ghost binder list, each module IMPORTED and not merely required --
   see [UkWriteLeaf.v]'s header *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UmodeArith.
Require Import UserBits.           (* [uint_add_vec_int_small] *)
Require Import UexecSlot UexecSG.
Require Import UkRun.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UCodeShK.           (* [shk_ro] / [shk_rodata] *)
Require Import UkSh.               (* [ksh_w] / [wp_ksh_write_chain_txt] *)
Require Import UkWriteClosed.      (* [ksh_w_of_closed]: the prompt on a
                                      closed fd 2 (step 3) *)
Require Import UShKernel.          (* [sh_prompt_law]: the conversion of
                                      the loop's credential into this call *)
Require Import LineWords.          (* [rest_of] / [nlines] *)
Require Import EchoOutPure.        (* [pending_at] *)
Require Import EchoDisc.
Require Import EchoOut.
Require Import EchoLinks.
Require Import CtxIdDefs.
Require User.ShSyms.
(* as in EchoDisc / UEchoOut: the Sail imports leave string_scope on top
   and [++] would elaborate as String.append *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE PURE HALF: sh's rodata prompt IS round 0's alternative        *)
(*                                                                       *)
(*  [auipc a1,0x1] at 0x12 and [addi a1,a1,638] put 0x1290 in a1, and     *)
(*  0x1290 is where "$ " sits in [UCodeShK.shk_ro].  The era's side is    *)
(*  [EchoDisc.pro_alts !!! 0] = [u_prompt] = "$ ", and the two bytes of   *)
(*  the ROUND-0 stream at 18 and 19 are those two -- all four facts are   *)
(*  closed computations on the literals.                                 *)
(* ===================================================================== *)
(* ...AND THE ADDRESS IS [UkSh]'s (lane IO-LEAF, M4a(3)): sh's walk needs
   it in a REGISTER fact at the call and this file needs it in a statement,
   so it is named once, below both. *)
Local Notation sh_prompt_pv := UkSh.sh_prompt_pv.
Definition sh_dollar_b : bv 8 := Z_to_bv 8 0x24.
Definition sh_space_b  : bv 8 := Z_to_bv 8 0x20.

Lemma sh_dollar_ro : shk_ro !! sh_prompt_pv = Some sh_dollar_b.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_space_ro : shk_ro !! (sh_prompt_pv + 1)%Z = Some sh_space_b.
Proof. vm_compute. reflexivity. Qed.

(* the '$' is the FIRST byte of the round's alternative 0 *)
Lemma sh_dollar_pro : pro_alts !!! 0%nat !! 0%nat = Some sh_dollar_b.
Proof. vm_compute. reflexivity. Qed.

Lemma pro_alts_len3 : (0 < length pro_alts)%nat.
Proof. vm_compute. lia. Qed.

(* ROUND 0's stream AT THE EMPTY INPUT, before and after the choice:
   eighteen banner bytes, then -- once alternative 0 is filed -- the
   prompt's two.  The round a shell runs in is decided by the INPUT now
   (project echo-any-line), and round 0's input is [[]]. *)
Lemma sh_pro_stage : length (proc_stream [3%nat] [] []) = 18%nat.
Proof.
  rewrite /proc_stream proc_before_nil pending_at_nil.
  vm_compute. reflexivity.
Qed.

Lemma sh_space_stream :
  proc_stream [3%nat; 0%nat] [] [] !! 19%nat = Some sh_space_b.
Proof.
  rewrite /proc_stream proc_before_nil pending_at_nil.
  vm_compute. reflexivity.
Qed.

Lemma sh_pro_open :
  ~ pro_done (pro_from (pro_idx [] (nlines ([] : list (bv 8)))) []).
Proof. vm_compute. intro H. inversion H. Qed.

Lemma sh_pro_lines : (nlines ([] : list (bv 8)) <= length ([] : list nat))%nat.
Proof. vm_compute. lia. Qed.

Lemma sh_pro_rest : rest_of ([] : list (bv 8)) = [].
Proof. exact rest_of_nil. Qed.

Lemma sh_pro_pin (ps cs : list nat) : pro_pin ps cs [].
Proof. exact (pro_pin_nil ps cs). Qed.

(* fd 2, as the kernel narrows it *)
Lemma sh_fd2_signed : bv_signed (trunc32 (mword_of_int 2 : mword 64)) = Z.of_nat 2.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_count2 :
  sys_rw_count (mword_of_int (Z.of_nat 2%nat) : mword 64) = Z.of_nat 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* a non-wrapping add, as the chain's key reads it *)
Lemma uint_avi_small (a : mword 64) (j : Z) :
  0 <= j -> uint a + j < 18446744073709551616 ->
  uint (add_vec_int a j) = (uint a + j)%Z.
Proof.
  intros Hj Hfit. rewrite !uint_unsigned in Hfit |- *.
  exact (uint_add_vec_int_small a j Hj Hfit).
Qed.

Section UShOut.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  (* NO [ctokG] AND NO [uexecSG] VARIABLE, for [UInitBanner]'s reasons:
     [Xv6G.xv6_ctok] is an instance and this file reads row 16's CONCRETE
     arm, so the deposit instance has to be the xv6 one. *)
  Context `{PS : uprogSG Σ}.
  (* sh's own section binders, as [UkSh] fixes them *)
  Context `{!uartGhostG Σ}.
  Context (γp : gname).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  THE CURSOR FAMILY                                              *)
  (*                                                                     *)
  (*  [p] of sh's two prompt bytes are out, at a LINE BOUNDARY [n] the    *)
  (*  shell's lease stands at.  Round 0's prompt at [n = 0] is the one    *)
  (*  /init's banner hands over, but the family is stated at every [n]    *)
  (*  because the shell prints a prompt at every turn of its command      *)
  (*  loop, and what each '$' resolves is [EchoLinks]'s business and not  *)
  (*  this file's: [ewc_owed] is either shape and [ewc_open] is what      *)
  (*  the pair of bytes leaves behind.                                    *)
  (* =================================================================== *)
  (* THE FAMILY IS [EchoLinks.ewc_pr] NOW (lane IO-LEAF, M6a(3)): the
     shell's loop carries it with the era's pin beside it
     ([EchoLinks.ewc_cred]), and the read side ([UShLine]) has to name the
     same constant, so it lives where both can see it. *)
  Local Notation ushpr := (EchoLinks.ewc_pr T).

  (* =================================================================== *)
  (*  S2  ONE BYTE, THROUGH THE ERA'S LINKS                               *)
  (*                                                                     *)
  (*  The '$' is a CHOICE and goes through whichever of the era's two     *)
  (*  choice links its shape asks for; the ' ' is an ordinary byte of the *)
  (*  block the choice fixed and goes through the plain one.  The taint   *)
  (*  arm continues the tower on its own, which is what                   *)
  (*  [EchoLinks.echo_link_taint] is for -- both steps carry it.          *)
  (* =================================================================== *)
  Lemma ushpr_step (v : era_pins) (I : list (bv 8)) (p : nat) (b : bv 8)
      (Φ : iProp Σ) :
    u_prompt !! p = Some b ->
    (p < 2)%nat ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ushpr v I p -∗
    (ushpr v I (S p) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ.
  Proof using Persistent0.
    intros Hb Hp. destruct p as [| [| p]]; [| | exfalso; lia].
    - assert (Hb0 : b = u_prompt !!! 0%nat).
      { rewrite wr_prompt_head in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (EchoLinks.echo_prompt_dollar T γ (S gen_id) v I b Φ Hb0
                with "Hpin Hlk Hc HΦ").
    - assert (Hb1 : b = u_prompt !!! 1%nat).
      { rewrite wr_prompt_tail in Hb. by injection Hb. }
      iIntros "#Hpin #Hlk Hc HΦ".
      iApply (EchoLinks.echo_prompt_space T γ (S gen_id) v I b Φ Hb1
                with "Hpin Hlk Hc HΦ").
  Qed.

  (* =================================================================== *)
  (*  S3  THE TWO BYTES, AS THE CONSOLE CHAIN                             *)
  (*                                                                     *)
  (*  consolewrite's chain node is ADDITIVE -- the cursor at [i] AND the  *)
  (*  step for the byte the image holds there -- so one copy of the era's *)
  (*  bundle answers both, which is what makes a SHORT write survivable   *)
  (*  at the logic level (and refutable at the leaf).                     *)
  (* =================================================================== *)
  Lemma ushpr_chain (v : era_pins) (I : list (bv 8)) (M : gmap Z (bv 8))
      (ua : mword 64) (fb : nat -> bv 8) :
    forall (c i : nat),
    (i + c <= 2)%nat ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       u_prompt !! j = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ushpr v I i -∗
    cons_out_chain (S gen_id) M ua (fun j : nat => ushpr v I j) i c.
  Proof using Persistent0.
    intros c. induction c as [| c IH]; intros i Hle Hline HM.
    - iIntros "_ _ Hc". cbn [cons_out_chain]. iExact "Hc".
    - iIntros "#Hpin #Hlk Hc". cbn [cons_out_chain]. iSplit.
      + iExact "Hc".
      + iIntros (b) "%Hbm".
        assert (Hbb : b = fb i).
        { rewrite (HM i ltac:(lia) ltac:(lia)) in Hbm. by injection Hbm. }
        subst b.
        iApply (ushpr_step v I i (fb i) _
                  (Hline i ltac:(lia) ltac:(lia)) ltac:(lia)
                  with "Hpin Hlk Hc").
        iIntros "Hc".
        iApply (IH (S i) ltac:(lia)
                  ltac:(intros j H1 H2; apply Hline; lia)
                  ltac:(intros j H1 H2; apply HM; lia) with "Hpin Hlk Hc").
  Qed.

  (* =================================================================== *)
  (*  S4  THE CALL                                                        *)
  (* =================================================================== *)
  (* the ecall leaves take [UexecSG.sfam] and an [xfam]-typed argument is
     not one until the instance is fixed -- [UInitBanner.kbn_fam]'s mould *)
  Definition ksh_fam (N : uk_names Σ) (Q : nat -> iProp Σ) : sfam :=
    xfam_wr Q (ukn_pay N).

  Lemma shk_rodata_byte (g : gname) (a : Z) (b : bv 8) :
    shk_ro !! a = Some b -> shk_rodata g -∗ utext g a b.
  Proof using .
    intros Ha. rewrite /shk_rodata /utext_img. iIntros "#H".
    iApply (big_sepM_lookup _ _ a b with "H"). exact Ha.
  Qed.

  (* THE PROMPT, AS ONE CALL: [write(2, "$ ", 2)], paid by the era's two
     links and answered on the ONE ledger row it asks for -- sh's fd 2 is
     the console, which is /init's pinned table inherited through the exec
     channel.  What comes back is the cursor two bytes on, or the taint. *)
  Lemma ksh_w_of_link_prompt (N : uk_names Σ) (v : era_pins)
      (I : list (bv 8)) (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    shk_rodata (ukn_t N) -∗
    UkSh.ksh_w N (mword_of_int 2 : mword 64)
      (mword_of_int sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd N) l vw ∗ ushpr v I 0%nat)
      (UserFd.ustd_at (ukn_fd N) l vw ∗ ushpr v I 2%nat).
  Proof.
    intros Hl2.
    iIntros "#Hpin #Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    assert (Hua : uint (m !!! Regidx a1_idx) = sh_prompt_pv)
      by (rewrite Ha1; apply uint_moi; unfold sh_prompt_pv, Z64; lia).
    (* the two keys the console chain is indexed by, as plain addresses:
       the buffer is a .rodata literal at 0x1290, so neither add wraps *)
    assert (Havi0 : uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat 0))
                    = sh_prompt_pv).
    { assert (Hhi : uint (m !!! Regidx a1_idx) + Z.of_nat 0
                    < 18446744073709551616)
        by (rewrite Hua; unfold sh_prompt_pv; lia).
      rewrite (uint_avi_small (m !!! Regidx a1_idx) (Z.of_nat 0)
                 ltac:(lia) Hhi).
      rewrite Hua. lia. }
    assert (Havi1 : uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat 1))
                    = (sh_prompt_pv + 1)%Z).
    { assert (Hhi : uint (m !!! Regidx a1_idx) + Z.of_nat 1
                    < 18446744073709551616)
        by (rewrite Hua; unfold sh_prompt_pv; lia).
      rewrite (uint_avi_small (m !!! Regidx a1_idx) (Z.of_nat 1)
                 ltac:(lia) Hhi).
      rewrite Hua. lia. }
    (* the two literal bytes, off sh's own .rodata *)
    iAssert (utext (ukn_t N) sh_prompt_pv sh_dollar_b) as "#Hb0".
    { iApply (shk_rodata_byte (ukn_t N) sh_prompt_pv sh_dollar_b
                sh_dollar_ro with "Hro"). }
    iAssert (utext (ukn_t N) (sh_prompt_pv + 1)%Z sh_space_b) as "#Hb1".
    { iApply (shk_rodata_byte (ukn_t N) (sh_prompt_pv + 1)%Z sh_space_b
                sh_space_ro with "Hro"). }
    iAssert ([∗ list] j ∈ seq 0 2%nat,
               utext (ukn_t N) (uint (m !!! Regidx a1_idx) + Z.of_nat j)%Z
                 (u_prompt !!! j))%I as "#Hbs".
    { rewrite Hua. cbn [seq]. rewrite big_sepL_cons big_sepL_singleton.
      iSplitL.
      - rewrite Z.add_0_r.
        replace (u_prompt !!! 0%nat) with sh_dollar_b
          by (vm_compute; reflexivity).
        iExact "Hb0".
      - replace (u_prompt !!! 1%nat) with sh_space_b
          by (vm_compute; reflexivity).
        replace (sh_prompt_pv + Z.of_nat 1)%Z with (sh_prompt_pv + 1)%Z by lia.
        iExact "Hb1". }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 2%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 2%nat)
      by (rewrite Ham2 sh_count2; lia).
    iApply (UkSh.wp_ksh_write_chain_txt_at N h m avail
              (ksh_fam N (fun j : nat => ushpr v I j)) l vw
              2%nat (fun j : nat => u_prompt !!! j)
              with "Hcode Hrun [Hc] Hstd Hbs").
    { (* THE DEPOSIT: sh's own chain at its own cursor *)
      iApply (uwrite_chain_sup N (fun j : nat => ushpr v I j)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   sh_prompt_pv sh_dollar_b with "Hheap Hb0") as %(HM0 & _ & _).
      iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (sh_prompt_pv + 1)%Z sh_space_b
                   with "Hheap Hb1") as %(HM1 & _ & _).
      iFrame "Hheap".
      (* the two keys the chain is indexed by, as plain addresses *)
      rewrite Ham1 Hcnt.
      iApply (ushpr_chain v I M (m !!! Regidx a1_idx)
                (fun j : nat => u_prompt !!! j) 2%nat 0%nat ltac:(lia)
                ltac:(intros j _ Hj;
                      destruct j as [| [| j]];
                      [ vm_compute; reflexivity
                      | vm_compute; reflexivity
                      | exfalso; lia ])
                ltac:(intros j _ Hj;
                      destruct j as [| [| j]];
                      [ rewrite Havi0 HM0; vm_compute; reflexivity
                      | rewrite Havi1 HM1; vm_compute; reflexivity
                      | exfalso; lia ])
                with "Hpin Hlk Hc"). }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
    iDestruct (uwrite_no_short (fun j : nat => ushpr v I j)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 2%nat rb 2%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; exact sh_count2)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    iApply ("Hcont" $! h' ret with "[$Hstd $HQ] Hrun").
  Qed.

  (* =================================================================== *)
  (*  S5  THE CALL AT THE LOOP'S OWN CREDENTIAL (lane IO-LEAF, M6a(3)):  *)
  (*      the era's pin travels INSIDE the credential, because            *)
  (*      the command loop names no [v]; the call reads it out and puts   *)
  (*      it back.  This is what [UShKernel.sh_prompt_law] is built from. *)
  (* =================================================================== *)
  Lemma ksh_w_of_link_cred (N : uk_names Σ) (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    echo_links T γ -∗
    shk_rodata (ukn_t N) -∗
    UkSh.ksh_w N (mword_of_int 2 : mword 64)
      (mword_of_int sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd N) l vw ∗ EchoLinks.ewc_cred T γ (S gen_id) I 0%nat)
      (UserFd.ustd_at (ukn_fd N) l vw ∗ EchoLinks.ewc_cred T γ (S gen_id) I 2%nat).
  Proof.
    intros Hl2. iIntros "#Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    rewrite /EchoLinks.ewc_cred. iDestruct "Hc" as (v) "[#Hpin Hc]".
    iApply (ksh_w_of_link_prompt N v I l vw rb Hl2
              with "Hpin Hlk Hro [%] [%] [%] Hcode [$Hstd $Hc] Hrun [Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "[Hstd Hc] Hrun".
    iApply ("Hcont" $! h' ret with "[$Hstd Hc] Hrun").
    iExists v. iFrame "Hpin Hc".
  Qed.

  (* ...AND ITS CLOSED ARM (lane IO-LEAF, step 3): a prompt on a closed
     fd 2 writes nothing and needs nothing ([UkWriteClosed.ksh_w_of_closed]
     -- the kernel's write contract's [FdClosed] arm is [emp]). *)
  Lemma sh_prompt_law_holds :
    echo_links T γ -∗
    UShKernel.sh_prompt_law (EchoLinks.ewc_cred T γ (S gen_id)).
  Proof.
    iIntros "#Hlk". rewrite /UShKernel.sh_prompt_law.
    iIntros "!>" (N) "#Hro". rewrite /UkSh.ush_prompt_law.
    iModIntro. iSplitL "".
    - iIntros (I l vw) "%Hfd2". destruct Hfd2 as [rb Hl2].
      iApply (ksh_w_of_link_cred N I l vw rb Hl2 with "Hlk Hro").
    - iIntros (l vw) "%Hcl".
      iApply (UkWriteClosed.ksh_w_of_closed_at N (mword_of_int 2)
                (mword_of_int sh_prompt_pv) 2%nat l vw 2%nat
                sh_fd2_signed ltac:(unfold NSTD; lia) Hcl).
  Qed.

End UShOut.
