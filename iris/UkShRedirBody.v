(* ===================================================================== *)
(* UkShRedirBody.v -- SH'S BODY AT THE REDIRECT LINE, and the THREE-WAY   *)
(* CASE the file application's command loop turns on (lane SH-CHILD;      *)
(* design/app-file.md §5.1, SKELETON's obligation 18).                    *)
(*                                                                        *)
(* WHAT THE LANE FOUND, and it is what decides this file's shape: sh's     *)
(* body reads its line EXACTLY ONCE, at 0x97a, and only to see that the    *)
(* first byte is not 'c'.  Everything else the walk does with the line is  *)
(* to hand it to the CHILD's law.  So [UkShFork.wp_kshm_body_at] is        *)
(* abstract in the line shape, [wp_kshm_body_redir] below is that lemma at *)
(* the redirect shape and costs ONE fact ([ushs_lp0]), and the three-way   *)
(* case is not three walks but two plus cat's.                             *)
(*                                                                        *)
(* THE THREE ARMS.                                                         *)
(*   [LEcho ws]  -- [echo a b], first byte 'e': [UkShFork.wp_kshm_body_at] *)
(*     at [UkSh.ush_line_is], i.e. [UkShFork.ushf_body_law_echo].          *)
(*   [LEchoF ws nm] -- [echo a b > nm], first byte 'e' TOO (the redirect is a  *)
(*     suffix): the SAME walk, at [ushs_lp], closing on the redirect       *)
(*     child's law.                                                       *)
(*   [LCat nm]     -- [cat nm], first byte 'c': the [bne] at 0x97a is NOT   *)
(*     taken and control goes into the three-byte [cd] test.  That test is *)
(*     three instructions and [cat f] falls out of it at the second        *)
(*     ('a' is not 'd'), back into the fork the other two arms use, so the *)
(*     arm is [wp_kshm_body_cat] and NOT a walk this tree lacks            *)
(*     ([UkShCd.wp_kshc_cd] stays deleted).  Nothing in this file is owed: *)
(*     the two children (the redirect's and cat's) are premises.           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import WpUmodeBranch.  (* [uv_btaken] -- the branch's own reading *)
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.        (* [uline]: the three lines the file
                                   discipline admits *)
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShParseCmd.    (* [ushp_setb] / [ushp_nulfold]: the cut *)
Require Import UkShRedirPc.     (* [ushs_nulcut]: the redirect line's cut *)
Require Import UkShWords.       (* [wl_cut_in] / [wl_cut_end] *)
Require Import UkShEcho.        (* [echo_argv_bytes] and the exec arm *)
Require Import UkShRedirLine.   (* [ushs_line_is] and the typed bridge *)
Require Import UkShFork.        (* [ushf_body_law] / [wp_kshm_body_at] *)
Require Import UNameBytes.      (* the line [cat N]'s bytes at any name *)
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import UserCwd.
Require Import UserChildren.
Require Import UserPerm.        (* [usz_ok] *)
Require Import UserPtTree.
Require Import Xv6Cameras.
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirBody.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.
  Context `{HWct : forall (I : list (bv 8)) (p : nat), Timeless (Wc I p)}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head N γp T Wc Wb Pm).

  (* =================================================================== *)
  (*  §1  THE REDIRECT LINE, AS A LINE SHAPE                              *)
  (*                                                                     *)
  (*  The file name is existential because the WALK never reads it: what  *)
  (*  reads it is the child, off its own copy of the line.  At the file   *)
  (*  application it is the line's own name ([ushs_lp_of_at], cut W3).    *)
  (* =================================================================== *)
  (* THE WORDS ARE THE WHOLE BODY'S (RULING SLOT-WS, option B;
     [UShPipeRound.ushq_lp] is the same shape one constructor over): what
     the body walk is handed is [FileDisc.uline_ws (LEchoF ws nm)], which is
     what the line LEXES to -- four words at `echo a > f' -- and the
     existential binds the command's own. *)
  Definition ushs_lp (wsf : list (list (bv 8))) (g : nat -> bv 8)
      (k len : nat) : Prop :=
    exists (ws : list (list (bv 8))) (file : list (bv 8)),
      wsf = ws ++ [FileDisc.fd_w_gt; file]
      /\ UkShRedirLine.ushs_line_is ws file g k len.

  Lemma ushs_lp0 (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) :
    ushs_lp ws g k len -> bv_unsigned (g k) = 101%Z.
  Proof using .
    intros (ws0 & file & _ & Hl).
    exact (UkShRedirLine.ushs_line_is_byte0 ws0 file g k len Hl).
  Qed.

  Lemma ushs_lp_of_at (ws : list (list (bv 8))) (nm : list (bv 8))
      (f : nat -> bv 8) (k len : nat) :
    UkSh.ush_line_at (LEchoF ws nm) f k len ->
    ushs_lp (FileDisc.uline_ws (LEchoF ws nm))
      (fun j : nat => f (k + j)%nat) 0%nat len.
  Proof using .
    intros H. exists ws, nm. split; [ reflexivity | ].
    exact (UkShRedirLine.ushs_line_is_shift ws nm f k len
             (UkShRedirLine.ushs_line_is_of_at ws nm f k len H)).
  Qed.

  (* =================================================================== *)
  (*  §2  THE BODY AT THE REDIRECT LINE (deliverable 2)                   *)
  (*                                                                     *)
  (*  [UkShFork.wp_kshm_body_at] at [ushs_lp].  The prefix walk -- fork1, *)
  (*  the diagnostic, the [cd] refutation -- is SHARED with the echo      *)
  (*  line's, character for character, because the refutation reads only  *)
  (*  the first byte and both lines carry the same [EchoDisc.line_ok].    *)
  (*  What differs is the CHILD's law, and that is the parameter.         *)
  (* =================================================================== *)
  Lemma wp_kshm_body_redir
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8))) (file : list (bv 8))
      (sz : Z) (l : list fdstate) (n : nat) :
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* THE LINE IS THE REDIRECT SHAPE *)
    UkShRedirLine.ushs_line_is ws file (fun j : nat => f (k + j)%nat)
      0%nat len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    (* THE REDIRECT CHILD'S LAW, which is [sh_redir_child_law] below *)
    UkShFork.ushf_child_law_at Wc ushs_lp 68 -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l (ws ++ [FileDisc.fd_w_gt; file]) -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT HWct Hpay Hpsok_free.
    intros Hregs Hs1 Ha5 Hnn Hnul Hkl Hline Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl.
    exact (UkShFork.wp_kshm_body_at N γp T Wc Wb Pm Hpsok_free ushs_lp 68
             h m f k len (ws ++ [FileDisc.fd_w_gt; file]) sz l n
             ltac:(lia) ushs_lp0
             Hregs Hs1 Ha5 Hnn Hnul Hkl
             (ex_intro _ ws (ex_intro _ file (conj eq_refl Hline)))
             Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl).
  Qed.

  (* =================================================================== *)
  (*  §2b  THE ARGV BYTES AT THE REDIRECT CUT (lane SH-CHILD-2, item 3)   *)
  (*                                                                     *)
  (*  [UkShEcho.echo_argv_bytes_of_line_holds] is this at the SYMBOL-FREE *)
  (*  cut, [ushp_nulfold (echo_toks ws) (ushp_ext len f)].  The redirect  *)
  (*  child's tree is built over [UkShRedirPc.ushs_nulcut], which is that *)
  (*  cut with ONE MORE terminator -- [nulterminate]'s REDIR arm zeroes   *)
  (*  the file name's end too -- and SH-LEX-REDIR's ruling makes the      *)
  (*  token list the SAME ([wl_toks ws], echo's own).  So the whole proof *)
  (*  is: the extra store is at [fe], every argument byte and every       *)
  (*  argument's terminator is below [|wl_body ws| < fe], and underneath  *)
  (*  it the two cuts are the same function.                             *)
  (* =================================================================== *)
  Lemma echo_argv_bytes_of_redir (ws : list (list (bv 8)))
      (file : list (bv 8)) (f : nat -> bv 8) (k len fe : nat) :
    UkShRedirLine.ushs_line_is ws file f k len ->
    fe = (length (wl_body ws) + 3 + length file)%nat ->
    UkShEcho.echo_argv_bytes ws
      (UkShRedirPc.ushs_nulcut (wl_toks ws) len
         (fun j : nat => f (k + j)%nat) fe).
  Proof using .
    intros Hl Hfe. pose proof Hl as HL.
    destruct HL as (Hok & Hfile & Hlen & Hbody & _ & _ & _ & _ & _).
    assert (Hfpos : (0 < length file)%nat)
      by (destruct Hfile as [ Hne _ ]; destruct file; [ done | cbn; lia ]).
    split.
    - intros i j Hi Hj.
      pose proof (line_ok_at ws i Hok Hi) as Hw.
      rewrite /UkShEcho.echo_alen in Hj.
      assert (Hle : (UkShEcho.echo_off ws i + (j + 1)
                     <= 0 + length (wl_body ws))%nat)
        by exact (wl_off_le_body ws 0%nat i (ws !!! i) (j + 1)%nat Hw
                    ltac:(lia)).
      rewrite /UkShEcho.echo_off in Hle |- *.
      rewrite /UkShRedirPc.ushs_nulcut /ushp_setb.
      rewrite (proj2 (Nat.eqb_neq (wl_off 0%nat ws i + j)%nat fe)
                 ltac:(lia)).
      rewrite (wl_cut_in ws (fun x : nat => f (k + x)%nat) len i
                 (ws !!! i) j Hw Hj ltac:(lia)).
      rewrite (Hbody (wl_off 0%nat ws i + j)%nat ltac:(lia)).
      symmetry.
      exact (wl_lta_app_l (wl_body ws) [wl_nl]
               (wl_off 0%nat ws i + j)%nat ltac:(lia)).
    - intros i Hi.
      pose proof (line_ok_at ws i Hok Hi) as Hw.
      assert (Hle : (UkShEcho.echo_off ws i + length (ws !!! i)
                     <= 0 + length (wl_body ws))%nat)
        by exact (wl_off_le_body ws 0%nat i (ws !!! i) (length (ws !!! i))
                    Hw ltac:(lia)).
      rewrite /UkShEcho.echo_off /UkShEcho.echo_alen in Hle |- *.
      rewrite /UkShRedirPc.ushs_nulcut /ushp_setb.
      rewrite (proj2 (Nat.eqb_neq
                        (wl_off 0%nat ws i + length (ws !!! i))%nat fe)
                 ltac:(lia)).
      exact (wl_cut_end ws (fun x : nat => f (k + x)%nat) len i
               (ws !!! i) Hw).
  Qed.

  (* =================================================================== *)
  (*  §3  THE REDIRECT CHILD'S LAW (SKELETON's obligation 18)             *)
  (*                                                                     *)
  (*  [UShRound.sh_redir_child_law] is [UkShFork.ushf_child_law]'s body   *)
  (*  with [UkSh.ush_line_is] replaced by [UkShRedirLine.ushs_line_is],   *)
  (*  the file name bound OUTSIDE.  That is this file's [ushf_child_law_at *)
  (*  ushs_lp] with the existential pulled out, and the two are           *)
  (*  interderivable -- [sh_redir_child_law_at] is the direction the body  *)
  (*  above consumes, which is the one [UShRound] owes.                    *)
  (* =================================================================== *)
  Definition sh_redir_child_law : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (h : CpuId) (m : regfile) (dw dv : dfrac)
          (s0 : Z) (len : nat) (ws : list (list (bv 8)))
          (file : list (bv 8)) (fb : nat -> bv 8)
          (sz : Z) (ld : list fdstate) (n : nat) (I : list (bv 8)),
          ⌜ ukn_pay N' = (fun _ : Z => UkShFork.ushf_wq Wc I) ⌝ -∗
          ⌜ m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          ⌜ UkShRedirLine.ushs_line_is ws file fb 0%nat len ⌝ -∗
          (* the fork assertion's words are the WHOLE body's (RULING
             SLOT-WS, option B): the command's own, then `>', then the
             file name *)
          ⌜ ws ++ [FileDisc.fd_w_gt; file] = last_ws I ⌝ -∗
          (* the era's own line at that input (the PROGRAM STREAM): the
             slot the loop left says the input's last body PARSES *)
          ⌜ FileDisc.fline_ok (UkSh.ush_lastbody I) ⌝ -∗
          ⌜ 0 < s0 ⌝ -∗ ⌜ s0 + Z.of_nat len + 1 < Z64 ⌝ -∗
          ⌜ s0 + Z.of_nat len < 2 ^ 38 ⌝ -∗
          ⌜ 8344 <= sz ⌝ -∗ ⌜ UserPtTree.pgroundup sz = sz ⌝ -∗
          ⌜ usz_ok (sz + 65536) ⌝ -∗
          ⌜ UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld ⌝ -∗
          UCodeShK.shk_code (ukn_t N') -∗
          UCodeShP.shp_code (ukn_t N') -∗
          UCodeShP.shp_rodata (ukn_t N') -∗
          UkSh.ush_jtab (ukn_t N') -∗
          ustr (ukn_d N') (DfracOwn 1) s0 len fb -∗
          ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
          ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
          UserFd.ustd (ukn_fd N') ld -∗
          UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
          (* THE TWO ROWS [UkShFork.ushf_child_law_at] BOUGHT (design
             app-pipe SS4.3w, purchase 2), MIRRORED HERE so that the two
             shapes stay INTERDERIVABLE.  [sh_redir_child_law_of_at] below
             is the direction that needs them: it has to FEED the generic
             law's premises, and at [uch_any] it could not.  Free for this
             law's provers -- it has none in the tree, and the redirect
             child's walk reads neither row -- and owed by its consumers,
             which are the two conversions in this section. *)
          UserChildren.uch (ukn_ch N') ∅ -∗
          UkSh.ush_pid N' -∗
          UkShMalloc.ushm_fresh N' sz -∗
          Wc I 3%nat -∗
          (* EIGHT MORE THAN ECHO'S: the redirect parse is that much
             deeper, and [UkSh.ush_Dbody] carries it (the program stream's
             "one number") *)
          urun N' h m (mword_of_int 0x9c0)
            (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
          mWP (Loop : expr riscv_lang)))%I.

  Global Instance sh_redir_child_law_persistent :
    Persistent sh_redir_child_law.
  Proof using .
    (* NAME the modality, do not search for it: the body is one [□] and
       [apply _] descends through the whole 30-premise wand tower under
       it (40s measured). *)
    rewrite /sh_redir_child_law. apply bi.intuitionistically_persistent.
  Qed.

  (* the two shapes, one step apart: the walk takes the file name out of
     the line fact, the law binds it. *)
  Lemma ushf_child_law_at_of_redir :
    sh_redir_child_law -∗ UkShFork.ushf_child_law_at Wc ushs_lp 68.
  Proof using .
    iIntros "#Hl". rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv s0 len wsf g sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcr Hrun".
    destruct Hline as (ws & file & -> & Hline).
    iApply ("Hl" $! N' h m dw dv s0 len ws file g sz ld n I
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcode Hpcode Hpro Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
                    Hcr Hrun");
      [ exact Hpeq | exact Hs1 | exact Hline | exact Hlws | exact Hfbk
      | exact Hs0 | exact Hs64 | exact Hs38 | exact Hszlo | exact Hszal
      | exact Hszok | exact Hrows ].
  Qed.

  (* ...and the other way, so the two shapes are interderivable and a
     supplier may prove whichever is convenient. *)
  Lemma sh_redir_child_law_of_at :
    UkShFork.ushf_child_law_at Wc ushs_lp 68 -∗ sh_redir_child_law.
  Proof using .
    iIntros "#Hl". rewrite /sh_redir_child_law.
    iIntros "!>" (N' h m dw dv s0 len ws file g sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
       Hcr Hrun".
    iApply ("Hl" $! N' h m dw dv s0 len (ws ++ [FileDisc.fd_w_gt; file])
                    g sz ld n I
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcode Hpcode Hpro Hjt Hstr Hws Hsy Hstd Hcwd Hch Hpid HM
                    Hcr Hrun");
      [ exact Hpeq | exact Hs1 | by exists ws, file | exact Hlws | exact Hfbk
      | exact Hs0 | exact Hs64 | exact Hs38 | exact Hszlo | exact Hszal
      | exact Hszok | exact Hrows ].
  Qed.

  (* =================================================================== *)
  (*  §3b  THE REDIRECT CHILD'S WALK (lane SH-CHILD-2, item 4)            *)
  (*                                                                     *)
  (*  From 0x9c0 to the exec, at the line the fork lent it.  Two halves:  *)
  (*  [UkShRedirSeam.wp_kshm_child_alloc_redir] -- parse, close(1),       *)
  (*  open(file), and out at runcmd with the EXEC sub-tree and the        *)
  (*  receipt -- and then [UkShEcho.wp_kshr_exec_echo_at_holds] at the    *)
  (*  fd-1 row the open left, which is the ONE thing echo's arm had to    *)
  (*  become abstract in.                                                 *)
  (*                                                                     *)
  (*  THE LEND PAYS EVERY EXIT.  The child's payload is                   *)
  (*  [UkShFork.ushf_wq Wc I] and the walk can leave at three places --   *)
  (*  the parser's NULL store, the open's failure and the exec's -- so    *)
  (*  the lend [Wc I 3] goes in and the law that turns it into the        *)
  (*  payload is one [iLeft].                                            *)
  (*                                                                     *)
  (*  THE OPEN AND THE SUPPLY ARE PREMISES, not hypotheses: both are the  *)
  (*  APPLICATION's ([UShRound.Hopen_hand] and K1's entry), and both come *)
  (*  out of the credential family the fork lent -- which is why they are *)
  (*  resources here and not [Hypothesis]es.                             *)
  (* =================================================================== *)
  Definition ushs_fd1f (ty : fdtype) (l : list fdstate) : Prop :=
    l !! 1%nat = Some (FdOpen false true ty).

  (* [wp_kshm_child_file_redir] -- the walk from 0x9c0 to the child's
     exits -- is [UkShRedirChild.v]'s: it is stated on the generic seam, at
     the application's own call ([UkShRedirAns.ush_open_call2]) and the
     paid open-failed diagnostic, neither of which this file sees. *)

  (* =================================================================== *)
  (*  §3c  THE CAT ARM'S BODY (the program stream; [Hcat_body] discharged) *)
  (*                                                                     *)
  (*  [cat f] begins with 'c', so 0x97a's [bne a5,s5] is NOT taken and    *)
  (*  the walk goes into the [cd] test.  That test is THREE instructions  *)
  (*  and it falls out at the second:                                     *)
  (*                                                                     *)
  (*    0x97a  bne a5,s5,92c   -- NOT taken ('c' IS s5)                   *)
  (*    0x97e  lbu a5,1(s1)    -- the line's second byte, 'a'             *)
  (*    0x982  bne a5,s3,92c   -- TAKEN ('a' is not 'd')                  *)
  (*                                                                     *)
  (*  and 0x92c is the fork, where the echo and redirect arms are.  So    *)
  (*  the cat arm is the SAME walk with two instructions in front of it   *)
  (*  -- not the 150-300 lines the obligation table priced, because       *)
  (*  [cat f] never reaches [chdir]: [UkShCd.wp_kshc_cd] is deleted and   *)
  (*  stays deleted.                                                      *)
  (* =================================================================== *)
  Definition ushs_lp_cat (ws : list (list (bv 8))) (g : nat -> bv 8)
      (k len : nat) : Prop :=
    exists nm : list (bv 8),
      ws = FileDisc.uline_ws (FileDisc.LCat nm)
      /\ UkSh.ush_line_at (FileDisc.LCat nm) g k len.

  Local Lemma ushs_bytes_at (dq : dfrac) (a : Z) (kk j : nat)
      (f : nat -> bv 8) :
    (j < kk)%nat ->
    ubytesq γd dq a kk f -∗
      ubyteq γd dq (a + Z.of_nat j) (f j) ∗
      (ubyteq γd dq (a + Z.of_nat j) (f j) -∗ ubytesq γd dq a kk f).
  Proof using .
    intros Hj. rewrite /ubytesq. iIntros "H".
    iDestruct (big_sepL_lookup_acc _ _ j j with "H") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hj ] | ].
    iSplitL "Hb"; [ iExact "Hb" | iExact "Hcl" ].
  Qed.

  (* the cat line's first bytes, off the typed line, at a name of any
     length *)
  Lemma ushs_cat_byte (nm : list (bv 8)) (f : nat -> bv 8) (k len j : nat) :
    UkSh.ush_line_at (FileDisc.LCat nm) f k len ->
    (j < 4)%nat ->
    f (k + j)%nat = cat_pre !!! j.
  Proof using .
    intros (Hok & Hlen & Hby) Hj.
    rewrite (Hby j ltac:(rewrite Hlen cat_line_len; lia)).
    exact (cat_line_head nm j Hj).
  Qed.

  (* THE FORK THE CAT ARM ENDS IN, AS A PARAMETER (cut C9f1): the landed
     [UkShFork.wp_kshf_fork_at] and the pipe era's twin
     [UkShPipeForkTwin.wp_kshf_fork_pipe] (whose credential need not be
     timeless) both have this statement, so the two-instruction [cd] test
     below is walked ONCE for both ([wp_kshm_body_cat_with]). *)
  Definition kshf_fork_law : Prop :=
    forall (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat) (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8))) (sz : Z) (l : list fdstate) (n : nat),
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    ⊢ UkSh.ush_gen_slot N T -∗
      ushl_head l sz -∗
      UCodeShK.shk_code γt -∗
      UCodeShK.shk_rodata γt -∗ UkSh.ush_jtab γt -∗
      UkShFork.ushf_kill_law Wc -∗
      UkShFork.ushf_child_law_at Wc Lp Dc -∗
      UkShDiag.ush_panic_law Wc Wb -∗
      ⌜ UkSh.ush_fd0p l ⌝ -∗
      UkSh.ush_bstate N γp T Wc Wb Pm l ws -∗
      ushl_dat -∗ usz γs sz -∗
      ubytes γd sh_buf sh_nbuf f -∗
      urun N h m (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n)) -∗
      mWP (Loop : expr riscv_lang).

  Lemma wp_kshm_body_ca_with (Hfork : kshf_fork_law)
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8))) (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    bv_unsigned (f k) = 99%Z -> bv_unsigned (f (k + 1)%nat) = 97%Z -> (2 <= len)%nat ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    UkShLoop.ushl_head N γp T Wc Wb Pm l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc Lp Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros HDc Hregs Hs1 Ha5 Hnn Hnul Hkl Hline Hb0 Hb1 Hlen2 Hszlo Hszal Hszok
           Hpm1 Hpmwb Hwbl.
    iIntros "#Hgen Hhead #Hcode #Hro #Hpcode #Hjt #Hkl #Hchl #Hplaw %Hfd0
             Hstd Hdat Hsz Hbuf Hrun".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    assert (Hbr : forall j : nat, 0 <= bv_unsigned (f j) < Z64).
    { intros j. pose proof (bv_unsigned_in_range 8 (f j)) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. unfold Z64. lia. }
    (* ---- 0x97a  bne a5,s5 -- NOT taken: the line's first byte IS 'c' ---- *)
    assert (Htk7a : false = uv_btaken BNE (m !!! Regidx a5_idx)
                              (m !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Ha5 Hs5 Hb0.
      symmetry. apply negb_false_iff.
      rewrite (moi_eq_vec 99 99 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uk_btype N h m (mword_of_int 0x97a)
              (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE false
              (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n))
              Htk7a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros Hc; discriminate Hc)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_97a with "Hcode"). }
    assert (E97a : add_vec_int (mword_of_int 0x97a : mword 64) 4
                   = mword_of_int 0x97e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E97a. iIntros (h1) "Hrun".
    (* ---- 0x97e  lbu a5,1(s1) -- the line's second byte ---- *)
    iDestruct (ushs_bytes_at (DfracOwn 1) sh_buf sh_nbuf (k + 1)%nat f
                 ltac:(lia) with "Hbuf") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h1 m (mword_of_int 0x97e)
              (mword_of_int 1 : mword 12) s1_idx a5_idx (DfracOwn 1)
              (sh_buf + Z.of_nat (k + 1)) (f (k + 1)%nat)
              (16 + (UkSh.ush_Dbody + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (sh_buf + Z.of_nat k)
                                   ltac:(unfold sh_buf, sh_nbuf, Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (UCodeShK.uis_shk_97e with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hbuf".
    assert (E97e : add_vec_int (mword_of_int 0x97e : mword 64) 4
                   = mword_of_int 0x982)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E97e. iIntros (h2) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (f (k + 1)%nat : mword 8)
                                     : mword 64)]> m).
    assert (Ha5_1 : m1 !!! Regidx a5_idx
                    = (zero_extend' 64 (f (k + 1)%nat : mword 8) : mword 64))
      by exact (upd_eq m (Regidx a5_idx) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Hregs1 : UkSh.ush_regs m1).
    { split_and!;
        [ rewrite (Hm1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2
        | rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)); exact Hs3
        | rewrite (Hm1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4
        | rewrite (Hm1 s5_idx ltac:(vm_compute; discriminate)); exact Hs5
        | rewrite (Hm1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6 ]. }
    assert (Hs1_1 : m1 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat k))
      by (rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x982  bne a5,s3 -- TAKEN: the second byte is not 'd' ---- *)
    assert (Htk82 : true = uv_btaken BNE (m1 !!! Regidx a5_idx)
                             (m1 !!! Regidx s3_idx)).
    { cbn [uv_btaken].
      rewrite Ha5_1 (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3.
      rewrite (zext8_moi (f (k + 1)%nat)) Hb1.
      symmetry. apply negb_true_iff.
      rewrite (moi_eq_vec 97 100 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uk_btype N h2 m1 (mword_of_int 0x982)
              (mword_of_int 8106 : mword 13) s3_idx a5_idx BNE true
              (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n))
              Htk82
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_982 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* ---- 0x92c: the fork, at the cat line's own child law ---- *)
    iApply (Hfork
              Lp Dc h3 m1 f k len ws sz l n
              HDc Hregs1 Hs1_1 Hnn Hnul Hkl Hline
              Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl
              with "Hgen Hhead Hcode Hro Hjt Hkl Hchl Hplaw [%] Hstd Hdat
                    Hsz Hbuf Hrun").
    exact Hfd0.
  Qed.

  (* [cat f] itself *)
  Lemma wp_kshm_body_cat_with (Hfork : kshf_fork_law)
      (Dc : nat) (nm : list (bv 8))
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    UkSh.ush_line_at (FileDisc.LCat nm) f k len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    UkShLoop.ushl_head N γp T Wc Wb Pm l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc ushs_lp_cat Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l (FileDisc.uline_ws (FileDisc.LCat nm)) -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros HDc Hregs Hs1 Ha5 Hnn Hnul Hkl Hline.
    assert (Hb0 : bv_unsigned (f k) = 99%Z).
    { pose proof (ushs_cat_byte nm f k len 0%nat Hline ltac:(lia)) as H0.
      rewrite Nat.add_0_r in H0. rewrite H0. by vm_compute. }
    assert (Hb1 : bv_unsigned (f (k + 1)%nat) = 97%Z).
    { pose proof (ushs_cat_byte nm f k len 1%nat Hline ltac:(lia)) as H1.
      rewrite H1. by vm_compute. }
    assert (Hlen2 : (2 <= len)%nat).
    { destruct Hline as (_ & Hl & _). rewrite Hl cat_line_len. lia. }
    exact (wp_kshm_body_ca_with Hfork ushs_lp_cat Dc h m f k len
             (FileDisc.uline_ws (FileDisc.LCat nm)) sz l n HDc Hregs Hs1 Ha5 Hnn Hnul Hkl
             (ex_intro _ nm (conj eq_refl Hline)) Hb0 Hb1 Hlen2).
  Qed.

  Lemma wp_kshm_body_cat
      (Dc : nat) (nm : list (bv 8))
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    UkSh.ush_line_at (FileDisc.LCat nm) f k len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    UkShLoop.ushl_head N γp T Wc Wb Pm l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc ushs_lp_cat Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l (FileDisc.uline_ws (FileDisc.LCat nm)) -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT HWct Hpay Hpsok_free.
    exact (wp_kshm_body_cat_with
             (UkShFork.wp_kshf_fork_at N γp T Wc Wb Pm Hpsok_free) Dc nm h m f k len sz l n).
  Qed.

  (* =================================================================== *)
  (*  §4  THE THREE-WAY CASE (deliverable 3)                              *)
  (*                                                                     *)
  (*  [D] is the file era's: every constructor of [FileDisc.uline].  The  *)
  (*  case is on the CONSTRUCTOR and nothing else -- the era's tag law     *)
  (*  ([FileOut.ftag], [FileDisc.disc_f]) is what says the buffer holds    *)
  (*  one of them, and this is where that turns into a walk.              *)
  (* =================================================================== *)
  (* THE ERA'S LINES ARE THE PARSER'S RANGE (lane ULINE-LPIPE).  This was
     [True], which was honest while [uline] had exactly the three
     constructors this case splits on.  Now that [FileDisc.uline] also
     carries the PIPELINE application's [LPipe] -- a line the FILE era's
     [parse_line] never files and has no walk for -- the predicate has to
     say so, and [FileReadInst.file_disc_line] supplies it from
     [FileDisc.uline_of_nopipe] at no cost. *)
  Definition ush_line_file (l : uline) : Prop := FileDisc.uline_nopipe l.

  (* ---- THE CAT ARM, PROVED (lane PROGRAM STREAM) --------------------- *)
  (*  This used to be [Hypothesis Hcat_body]: the whole body walk for      *)
  (*  [cat f], priced at 150-300 lines against [UkShCd.v]'s mould.  It is  *)
  (*  none of that -- see 3c: the [cd] test is three instructions and      *)
  (*  [cat f] falls out of it at the second, into the fork the other two   *)
  (*  arms use.  What is left over is the CHILD, and that is the round's   *)
  (*  own [Hchild_cat] (cat's entry), taken here as a premise exactly as   *)
  (*  the redirect arm takes [sh_redir_child_law].                         *)
  Lemma ushf_body_law_cat (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm
      (fun l : uline => exists nm : list (bv 8), l = LCat nm) sz.
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hplaw".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct Hd as [nm ->].
    iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
    iApply (wp_kshm_body_cat 68 nm h m f k len sz l n ltac:(lia)
              Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlat Hszlo Hszal Hszok
              Hpm1 Hpmwb Hwbl
              with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                    Hdat Hsz Hbuf Hrun").
    - iApply (UkShFork.ushf_code_shp with "Hcode").
    - exact Hfd0.
  Qed.

  Lemma ushf_body_law_file (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law Wc -∗
    sh_redir_child_law -∗
    UkShFork.ushf_child_law_at Wc ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm ush_line_file sz.
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hred #Hcatl #Hplaw".
    iPoseProof (UkShFork.ushf_body_law_echo N γp T Wc Wb Pm Hpsok_free sz
                  Hszlo Hszal Hszok Hwbl with "Hkl Hchl Hplaw") as "#Hecho".
    iPoseProof (ushf_body_law_cat sz Hszlo Hszal Hszok Hwbl
                  with "Hkl Hcatl Hplaw") as "#Hcat".
    iPoseProof (ushf_child_law_at_of_redir with "Hred") as "#Hchr".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct lu as [ ws | ws Nf | Nf | ws npc | ws];
      [| | | by destruct (proj1 Hd ws npc eq_refl) | by destruct (proj2 Hd ws eq_refl) ].
    - (* [echo a b] -- the landed walk *)
      iApply ("Hecho" $! (LEcho ws) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists ws | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* [echo a b > nm] -- the SAME walk at the redirect child's law *)
      pose proof (proj1 (proj2 (proj1 Hlat))) as Hu.
      iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
      iApply (UkShFork.wp_kshm_body_at N γp T Wc Wb Pm Hpsok_free ushs_lp 68
                h m f k len (FileDisc.uline_ws (LEchoF ws Nf)) sz l n
                ltac:(lia) ushs_lp0
                Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (ushs_lp_of_at ws Nf f k len Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchr Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp with "Hcode").
      + exact Hfd0.
    - (* [cat nm] -- the 'c' arm *)
      iApply ("Hcat" $! (LCat Nf) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists Nf | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
  Qed.

  (* ...AND THE OBLIGATION ITSELF, at the file era's lines.  This is what
     [UShRound.sh_round_holds_file] applies. *)
  Lemma ushf_rest_of_body_file (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law Wc -∗
    sh_redir_child_law -∗
    UkShFork.ushf_child_law_at Wc ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkSh.ush_rest_l_at N γp T Wc Wb Pm ush_line_file
      (UkShLoop.ushl_R N sz).
  Proof using HT HWct Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hred #Hcatl #Hplaw".
    iApply (UkShFork.ushf_rest_of_body_at N γp T Wc Wb Pm Hpsok_free
              ush_line_file sz Hszlo Hszal Hszok Hwbl).
    iApply (ushf_body_law_file sz Hszlo Hszal Hszok Hwbl
              with "Hkl Hchl Hred Hcatl Hplaw").
  Qed.

End UkShRedirBody.
