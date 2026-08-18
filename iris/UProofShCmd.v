(* UProofShCmd.v -- the VERIFIED-EXECUTION proofs of `sh''s two COMMAND-level
   functions: [nulterminate] @0x7ee and [parsecmd] @0x86e
   (claude-notes/projects/user-sh.md).

   [nulterminate] is the function that turns the token BOUNDARIES the parser
   recorded into real C strings: for an EXEC node it walks argv/eargv in
   lockstep and stores a NUL byte through every [eargv[i]].  It is the last
   thing that happens to the command buffer before [runcmd] hands the argv
   vector to [exec], so its postcondition is what the protocol's exec arm
   eventually observes.  Two things make it more than a loop:

     - gcc compiles its `switch (cmd->type)' as a JUMP TABLE.  The five
       instructions at 0x804..0x818 load a 32-bit displacement out of
       .rodata at 0x13b4, add it to the table base 0x13b0 and [c.jr] to the
       result.  So the proof must READ the image as data -- [sh_data_sub],
       not [sh_text_sub] -- and compute 0x13b0 + (-2966) = 0x81a.  This is
       the tier's first computed control transfer.

     - the loop writes into the CALLER's buffer, at |toks| scattered
       addresses.  The memory it leaves behind is spelled [nt_mem] (below),
       a left fold of one-byte stores, so the loop's invariant is an
       EQUATION rather than a conjunction of preservation facts.  What makes
       the postcondition TRUE is that no token's end offset lands inside
       another token -- §0's [sh_tokens_sep], out of [sh_tokens] and
       [sh_no_symbols].

   [parsecmd] is the four-callee sequence [strlen] / [parseline] / [peek] /
   [nulterminate] around a `s == es' test whose other arm is the unreachable
   [panic("syntax")].  [parseline] is proved by a sibling lane, so it enters
   here as a section HYPOTHESIS (§6) rather than as an [Admitted] hole. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import RiscvModelBytes.
Require Import WpMmodeLeafBase.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeArith UmodeIo.
Require Import WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UCodeSh USpecSh USpecShParse.
Require Import UProofShLib UProofShLex UProofShIo UProofShInput.
(* re-imported LAST on purpose: WpUmodeStep.v's funnel names its optional
   gpr write [uv_wr], which otherwise shadows UmodeAbi's writable-window
   record of the same name. *)
Require Import UmodeAbi.
Require User.ShSyms User.ShInstrs User.ShData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 PURE: the image's SHARP key bound, the NUL-store fold, and the       *)
(* separation of the token boundaries.                                    *)
(* ===================================================================== *)

(* [UCodeSh.sh_data_key_lt] rounds the dumped data map's keys up to the next
   page (12288).  That is enough for a write to the HEAP, but not for the
   two allocator statics [SH_FREEP] = 0x2010 and [SH_BASE] = 0x2088, which
   the run's single [malloc] writes and which [parsecmd] must carry
   [sh_data_sub] across.  The dumper's own range lemma is sharp: the last
   key is 0x200f. *)
Lemma sh_data_key_lt' (k : Z) (b : bv 8) :
  ShData.sh_data !! k = Some b -> k < 8208.
Proof.
  intro Hk. pose proof (ShData.sh_data_range k b Hk) as Hr.
  unfold ShData.sh_data_lo, ShData.sh_data_hi in Hr. lia.
Qed.

(* ---- the memory [nulterminate]'s loop leaves behind ------------------ *)

(* one one-byte NUL store per token, in loop order.  Writing the invariant
   as an EQUATION [Mi = nt_mem MB s0 (take i toks)] is what keeps the loop
   lemma's premise list short: every property the exit needs (which bytes
   are NUL, which are untouched, the domain) is read off this fold ONCE,
   after the loop, instead of being threaded through it. *)
Fixpoint nt_mem (M : gmap Z (bv 8)) (s0 : Z) (ts : list (nat * nat))
    : gmap Z (bv 8) :=
  match ts with
  | [] => M
  | t :: ts' => nt_mem (uM_store M (s0 + Z.of_nat (snd t)) 1 zero_reg) s0 ts'
  end.

Lemma nt_zero_byte : nth_byte (zero_reg : mword 64) 0 = ubyte0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma nt_mem_snoc (ts : list (nat * nat)) (M : gmap Z (bv 8)) (s0 : Z)
    (t : nat * nat) :
  nt_mem M s0 (ts ++ [t])
  = uM_store (nt_mem M s0 ts) (s0 + Z.of_nat (snd t)) 1 zero_reg.
Proof.
  revert M. induction ts as [ | u us IH ]; intro M; simpl; [ reflexivity | ].
  apply IH.
Qed.

Lemma nt_mem_ne (ts : list (nat * nat)) (M : gmap Z (bv 8)) (s0 k : Z) :
  (forall t : nat * nat, t ∈ ts -> k <> s0 + Z.of_nat (snd t)) ->
  nt_mem M s0 ts !! k = M !! k.
Proof.
  revert M. induction ts as [ | u us IH ]; intros M H; simpl; [ reflexivity | ].
  rewrite (IH (uM_store M (s0 + Z.of_nat (snd u)) 1 zero_reg)
            ltac:(intros t Ht; apply H; apply elem_of_list_further; exact Ht)).
  apply uM_store_lookup_ne. intros j Hj.
  change (Z.to_nat 1) with 1%nat in Hj.
  assert (Hj0 : j = 0%nat) by lia. subst j.
  pose proof (H u ltac:(apply elem_of_list_here)) as Hu. cbn [Z.of_nat]. lia.
Qed.

Lemma nt_mem_dom (ts : list (nat * nat)) (M : gmap Z (bv 8)) (s0 k : Z) :
  is_Some (M !! k) -> is_Some (nt_mem M s0 ts !! k).
Proof.
  revert M. induction ts as [ | u us IH ]; intros M H; simpl; [ exact H | ].
  apply IH. apply uM_store_is_Some. exact H.
Qed.

Lemma nt_mem_zero_keep (ts : list (nat * nat)) (M : gmap Z (bv 8)) (s0 k : Z) :
  M !! k = Some ubyte0 -> nt_mem M s0 ts !! k = Some ubyte0.
Proof.
  revert M. induction ts as [ | u us IH ]; intros M H; simpl; [ exact H | ].
  apply IH.
  destruct (Z.eq_dec k (s0 + Z.of_nat (snd u))) as [ -> | Hne ].
  - pose proof (uM_store_lookup M (s0 + Z.of_nat (snd u)) 1 zero_reg 0%nat
                  ltac:(cbn; lia)) as Hq.
    change (Z.of_nat 0) with 0 in Hq. rewrite Z.add_0_r in Hq.
    rewrite nt_zero_byte in Hq. exact Hq.
  - rewrite (uM_store_lookup_ne M (s0 + Z.of_nat (snd u)) 1 zero_reg k
               ltac:(intros j Hj; change (Z.to_nat 1) with 1%nat in Hj;
                     assert (Hj0 : j = 0%nat) by lia; subst j;
                     cbn [Z.of_nat]; lia)).
    exact H.
Qed.

Lemma nt_mem_zero (ts : list (nat * nat)) (M : gmap Z (bv 8)) (s0 : Z)
    (t : nat * nat) :
  t ∈ ts -> nt_mem M s0 ts !! (s0 + Z.of_nat (snd t)) = Some ubyte0.
Proof.
  revert M. induction ts as [ | u us IH ]; intros M Ht;
    [ exfalso; rewrite elem_of_nil in Ht; exact Ht | ].
  apply elem_of_cons in Ht as [ Heq | Ht ].
  - simpl. apply nt_mem_zero_keep. rewrite Heq.
    pose proof (uM_store_lookup M (s0 + Z.of_nat (snd u)) 1 zero_reg 0%nat
                  ltac:(cbn; lia)) as Hq.
    change (Z.of_nat 0) with 0 in Hq. rewrite Z.add_0_r in Hq.
    rewrite nt_zero_byte in Hq. exact Hq.
  - simpl. apply IH. exact Ht.
Qed.

(* ---- the token boundaries are SEPARATED ----------------------------- *)

(* the byte a token stops on, when it stops before the end of the buffer *)
Lemma sh_toklen_stop_byte (bs : list (bv 8)) :
  (sh_toklen bs < length bs)%nat ->
  exists b : bv 8,
    bs !! sh_toklen bs = Some b /\ sh_is_ws b || sh_is_sym b = true.
Proof.
  unfold sh_toklen.
  destruct (list_find (fun x => sh_is_ws x || sh_is_sym x) bs)
    as [ [i x] | ] eqn:E.
  - intros _. apply list_find_Some in E as (Hi & HP & _).
    exists x. split; [ exact Hi | exact (Is_true_eq_true _ HP) ].
  - intro H. lia.
Qed.

(* ... and a whitespace byte at [o] makes the skip from [o] non-empty *)
Lemma sh_skipws_pos (bs : list (bv 8)) (o : nat) (b : bv 8) :
  bs !! o = Some b -> sh_is_ws b = true -> (0 < sh_skipws (drop o bs))%nat.
Proof.
  intros Ho Hb. rewrite (drop_S bs b o Ho).
  rewrite (sh_skipws_cons_ws b (drop (S o) bs) Hb). lia.
Qed.

(* EVERY token recorded by [sh_tokens bs off toks] starts at or after the
   first non-whitespace byte from [off], is non-empty, and ends inside the
   buffer.  The lower bound is stated with the leading skip INCLUDED, which
   is what makes the separation below strict. *)
Lemma sh_tokens_bounds (bs : list (bv 8)) (off : nat)
    (toks : list (nat * nat)) :
  sh_tokens bs off toks -> (off <= length bs)%nat ->
  forall (i : nat) (t : nat * nat), toks !! i = Some t ->
    (off + sh_skipws (drop off bs) <= fst t /\ fst t < snd t /\
     snd t <= length bs)%nat.
Proof.
  induction 1 as [ o Ho | o ts k n Hn Htk IH ]; intros Hle i t Hi.
  - rewrite lookup_nil in Hi. discriminate.
  - assert (Ek : k = sh_skipws (drop o bs)) by reflexivity.
    assert (En : n = sh_toklen (drop (o + k) bs)) by reflexivity.
    assert (Hk : (sh_skipws (drop o bs) <= length bs - o)%nat).
    { pose proof (sh_skipws_le (drop o bs)) as H.
      rewrite length_drop in H. exact H. }
    assert (Hnn : (sh_toklen (drop (o + k) bs) <= length bs - (o + k))%nat).
    { pose proof (sh_toklen_le (drop (o + k) bs)) as H.
      rewrite length_drop in H. exact H. }
    destruct i as [ | i' ].
    + cbn in Hi. injection Hi as <-. cbn [fst snd]. lia.
    + cbn in Hi.
      destruct (IH ltac:(lia) i' t Hi) as (H1 & H2 & H3).
      split_and!; [ lia | exact H2 | exact H3 ].
Qed.

(* THE separation [nulterminate] needs: no token's END OFFSET lands strictly
   inside another token.  Without it the loop's stores would punch NULs into
   the middle of a token and the postcondition -- "each token is now a C
   string with exactly its own bytes" -- would be FALSE, not merely
   unprovable.  It is strict because a token can only stop on a whitespace
   byte (symbols are excluded by [sh_no_symbols]), and the next token's scan
   must therefore skip at least that one byte. *)
Lemma sh_tokens_sep (bs : list (bv 8)) :
  sh_no_symbols bs ->
  forall (off : nat) (toks : list (nat * nat)),
    sh_tokens bs off toks -> (off <= length bs)%nat ->
    forall (i j : nat) (t u : nat * nat),
      toks !! i = Some t -> toks !! j = Some u ->
      ~ (fst t <= snd u < snd t)%nat.
Proof.
  intro Hns.
  induction 1 as [ o Ho | o ts k n Hn Htk IH ]; intros Hle i j t u Hi Hj.
  - rewrite lookup_nil in Hi. discriminate.
  - assert (Ek : k = sh_skipws (drop o bs)) by reflexivity.
    assert (En : n = sh_toklen (drop (o + k) bs)) by reflexivity.
    assert (Hk : (sh_skipws (drop o bs) <= length bs - o)%nat).
    { pose proof (sh_skipws_le (drop o bs)) as H.
      rewrite length_drop in H. exact H. }
    assert (Hnn : (sh_toklen (drop (o + k) bs) <= length bs - (o + k))%nat).
    { pose proof (sh_toklen_le (drop (o + k) bs)) as H.
      rewrite length_drop in H. exact H. }
    assert (Hb : (o + k + n <= length bs)%nat) by lia.
    destruct i as [ | i' ]; destruct j as [ | j' ].
    + cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
      cbn [fst snd]. lia.
    + (* the first token, against a LATER boundary: later boundaries are
         strictly beyond this token's end *)
      cbn in Hi, Hj. injection Hi as <-.
      destruct (sh_tokens_bounds bs (o + k + n) ts Htk Hb j' u Hj)
        as (H1 & H2 & H3).
      cbn [fst snd]. lia.
    + (* a LATER token, against the first boundary: this is where the
         strictness is spent *)
      cbn in Hi, Hj. injection Hj as <-.
      destruct (sh_tokens_bounds bs (o + k + n) ts Htk Hb i' t Hi)
        as (H1 & H2 & H3).
      cbn [fst snd].
      assert (Hpos : (0 < sh_skipws (drop (o + k + n) bs))%nat).
      { assert (Hn' : (sh_toklen (drop (o + k) bs) < length (drop (o + k) bs))%nat)
          by (rewrite length_drop; lia).
        destruct (sh_toklen_stop_byte (drop (o + k) bs) Hn') as (c & Hc & Hcp).
        rewrite <- En in Hc.
        rewrite lookup_drop in Hc.
        assert (Hsym : sh_is_sym c = false) by exact (Hns _ c Hc).
        rewrite Hsym in Hcp. rewrite orb_false_r in Hcp.
        exact (sh_skipws_pos bs (o + k + n) c Hc Hcp). }
      lia.
    + cbn in Hi, Hj. exact (IH ltac:(lia) i' j' t u Hi Hj).
Qed.

Section UProofShCmd.
  Context `{!riscvGS Σ} `{!uioG Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).
  Local Notation x0_idx := (mword_of_int 0 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §1 The leaf-side plumbing.                                            *)
  (* ------------------------------------------------------------------- *)

  (* x0 reads as zero -- what `sb zero,0(a4)' needs about its SOURCE *)
  Local Lemma uv_x0 (CIDx : CpuId) (Mx : gmap Z (bv 8)) (mx : regfile) :
    uv_cap_gpr (CID := CIDx) C pt Psh Mx mx -∗
    ⌜mx !!! Regidx x0_idx = zero_reg⌝ ∗
    uv_cap_gpr (CID := CIDx) C pt Psh Mx mx.
  Proof.
    iIntros "(Hcap & Hlin & Hgpr)".
    iDestruct (gpr_file_x0 mx x0_idx ltac:(vm_compute; reflexivity) with "Hgpr")
      as "[%Hz Hgpr]".
    iSplitR; [ iPureIntro; exact Hz | ].
    rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr".
  Qed.

  Local Lemma st8_ne (Mx : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
    (k < a \/ a + 8 <= k) -> uM_store8 Mx a v !! k = Mx !! k.
  Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

  (* an 8-byte window survives a DISJOINT 8-byte store *)
  Local Lemma st8_bne (Mx : gmap Z (bv 8)) (a b : Z) (v w : mword 64) :
    (b + 8 <= a \/ a + 8 <= b) -> uM_bytes Mx a 8 v ->
    uM_bytes (uM_store8 Mx b w) a 8 v.
  Proof.
    intros Hd Hby j Hj. rewrite (st8_ne Mx b w (a + Z.of_nat j) ltac:(lia)).
    exact (Hby j Hj).
  Qed.

  (* everything an 8-byte ACCESS at a closed 8-aligned address needs, off
     ONE [uM_bytes] premise (UProofShHeap.acc8_facts, which is Local there) *)
  Local Lemma acc8 (Mx : gmap Z (bv 8)) (a : Z) (v : mword 64) :
    0 <= a -> a mod 8 = 0 -> a + 8 <= 2 ^ 38 ->
    uM_bytes Mx a 8 v ->
    uint (mword_of_int a : mword 64) = a /\
    uva_canon (mword_of_int a : mword 64) /\
    Z.rem (uint (mword_of_int a : mword 64)) 4096 <= 4088 /\
    is_aligned_vaddr (Virtaddr (mword_of_int a : mword 64)) 8 = true /\
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8,
         Mx !! (uint (mword_of_int a : mword 64) + Z.of_nat j) = Some bb) /\
    v = uM_word Mx (uint (mword_of_int a : mword 64)) 8.
  Proof.
    intros Ha0 Ha8 Hahi Hbw.
    destruct (uv_slot8_facts a (mword_of_int a) Ha0 Ha8 Hahi eq_refl)
      as (Hu & Hcanon & Hpg & Hal).
    split_and!; try assumption.
    - rewrite Hu. exact (uM_bytes_exists Mx a 8 _ Hbw).
    - rewrite Hu. symmetry. exact (uM_word_w8 Mx a _ Hbw).
  Qed.

  (* the same at width 4, for the [lwu]/[c.lw] that read [cmd->type] and
     the jump table's displacement *)
  Local Lemma acc4 (Mx : gmap Z (bv 8)) (a : Z) (v : mword 32) :
    0 <= a -> a mod 4 = 0 -> a + 4 <= 2 ^ 38 ->
    uM_bytes Mx a 4 v ->
    uint (mword_of_int a : mword 64) = a /\
    uva_canon (mword_of_int a : mword 64) /\
    Z.rem (uint (mword_of_int a : mword 64)) 4096 <= 4092 /\
    is_aligned_vaddr (Virtaddr (mword_of_int a : mword 64)) 4 = true /\
    uM_bytes Mx (uint (mword_of_int a : mword 64)) 4 v.
  Proof.
    intros Ha0 Ha4 Hahi Hbw.
    destruct (uv_slot4_facts a (mword_of_int a) Ha0 Ha4 Hahi eq_refl)
      as (Hu & Hcanon & Hpg & Hal).
    split_and!; try assumption. rewrite Hu. exact Hbw.
  Qed.

  (* the node's field offsets are 8-aligned because the node is: [malloc]
     hands out 16-aligned blocks.  [lia] cannot get from [cmd mod 16 = 0] to
     [(cmd + c + 8*i) mod 8 = 0] on its own -- the divisibility step is
     outside what its preprocessing supplies -- so it is spelled once. *)
  Local Lemma node_off_mod8 (cmd c : Z) (i : nat) :
    cmd mod 16 = 0 -> c mod 8 = 0 -> (cmd + c + 8 * Z.of_nat i) mod 8 = 0.
  Proof.
    intros H1 H2.
    pose proof (Z.div_mod cmd 16 ltac:(lia)) as D1.
    pose proof (Z.div_mod c 8 ltac:(lia)) as D2.
    replace (cmd + c + 8 * Z.of_nat i)
      with ((2 * (cmd / 16) + c / 8 + Z.of_nat i) * 8) by lia.
    apply Z.mod_mul. lia.
  Qed.

  Local Lemma node_off_mod8' (cmd c : Z) :
    cmd mod 16 = 0 -> c mod 8 = 0 -> (cmd + c) mod 8 = 0.
  Proof.
    intros H1 H2.
    pose proof (node_off_mod8 cmd c 0%nat H1 H2) as H.
    replace (cmd + c) with (cmd + c + 8 * Z.of_nat 0) by (cbn [Z.of_nat]; lia).
    exact H.
  Qed.

  Local Lemma node_mod4 (cmd : Z) : cmd mod 16 = 0 -> cmd mod 4 = 0.
  Proof.
    intro H1. pose proof (Z.div_mod cmd 16 ltac:(lia)) as D1.
    replace cmd with ((4 * (cmd / 16)) * 4) by lia.
    apply Z.mod_mul. lia.
  Qed.

  (* the image survives the loop's NUL stores, because the command buffer
     is above EVERY key of the dumped image ([sh_data_key_lt']'s 8208, not
     the page-rounded 12288) *)
  Local Lemma nt_img (MB : gmap Z (bv 8)) (s0 : Z) (ts : list (nat * nat)) :
    sh_img_sub MB -> 8208 <= s0 -> sh_img_sub (nt_mem MB s0 ts).
  Proof.
    intros (Htext & Hdata) Hs0. split.
    - intros k b Hk.
      rewrite (nt_mem_ne ts MB s0 k
                 ltac:(intros t _; pose proof (sh_bytes_key_lt k b Hk);
                       pose proof (Nat2Z.is_nonneg (snd t)); lia)).
      exact (Htext k b Hk).
    - intros k b Hk.
      rewrite (nt_mem_ne ts MB s0 k
                 ltac:(intros t _; pose proof (sh_data_key_lt' k b Hk);
                       pose proof (Nat2Z.is_nonneg (snd t)); lia)).
      exact (Hdata k b Hk).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 nulterminate's EXIT, from 0x83e.                                   *)
  (*                                                                       *)
  (*   83e  c.mv a0,s1        -- the return value is the node              *)
  (*   840  c.ldsp ra,24(sp)  842 c.ldsp s0,16(sp)  844 c.ldsp s1,8(sp)    *)
  (*   846  c.addi16sp sp,32  848 c.jr ra                                  *)
  (*                                                                       *)
  (* All three of the function's exits (cmd == 0 at 0x7fa, argv[0] == 0 at *)
  (* 0x81c, and the loop's fall-through at 0x830) reconverge here, so it is *)
  (* written once.                                                         *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_nt_exit (CIDp : CpuId)
      (Mx : gmap Z (bv 8)) (m mx : regfile) (sp0 : mword 64) (cmd : Z)
      (vra vs0 vs1 : mword 64) :
    sh_text_layout pt -> sh_text_sub Mx ->
    uv_stack pt Mx sp0 32 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    m !!! Regidx sp_idx = sp0 ->
    vra = m !!! Regidx ra_idx ->
    vs0 = m !!! Regidx s0_idx ->
    vs1 = m !!! Regidx s1_idx ->
    mx !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64) ->
    mx !!! Regidx s1_idx = (mword_of_int cmd : mword 64) ->
    uM_bytes Mx (uint sp0 - 32 + 24) 8 vra ->
    uM_bytes Mx (uint sp0 - 32 + 16) 8 vs0 ->
    uM_bytes Mx (uint sp0 - 32 + 8) 8 vs1 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
       Regidx r <> Regidx s1_idx -> mx !!! Regidx r = m !!! Regidx r) ->
    uv_cap_gpr (CID := CIDp) C pt Psh Mx mx -∗
    pc_is (CID := CIDp) (mword_of_int 0x83e) -∗
    (∀ (CID : CpuId) (m' : regfile),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       uv_cap_gpr (CID := CID) C pt Psh Mx m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hl Htext Hst Hret2 Hspm Evra Evs0 Evs1 Hspx Hs1x Bra Bs0 Bs1 Hpres.
    subst vra vs0 vs1.
    iIntros "Hcg Hpc Hcont".
    (* ---- 0x83e  c.mv a0,s1 ---- *)
    assert (Hw0 : (mword_of_int cmd : mword 64)
                  = add_vec zero_reg (mx !!! Regidx s1_idx))
      by (rewrite Hs1x moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh Mx mx (mword_of_int 0x83e)
              a0_idx s1_idx (mword_of_int cmd)
              (ui_sh_83e pt Mx Hl Htext)
              ltac:(vm_compute; discriminate) Hw0 with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (n1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> mx).
    assert (E83e : add_vec_int (mword_of_int 0x83e : mword 64) 2
                   = mword_of_int 0x840)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E83e) in "Hpc".
    assert (Hsp1 : n1 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne mx (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspx. }
    (* ---- 0x840  c.ldsp ra,24(sp) ---- *)
    iApply (wp_sh_reload C pt CID1 Psh 0x840 0x842 32 24
              (mword_of_int 3 : mword 6) ra_idx (m !!! Regidx ra_idx)
              Mx n1 sp0 Hst Hsp1
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bra (ui_sh_840 pt Mx Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (n2 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> n1).
    assert (Hsp2 : n2 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne n1 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x842  c.ldsp s0,16(sp) ---- *)
    iApply (wp_sh_reload C pt CID2 Psh 0x842 0x844 32 16
              (mword_of_int 2 : mword 6) s0_idx (m !!! Regidx s0_idx)
              Mx n2 sp0 Hst Hsp2
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs0 (ui_sh_842 pt Mx Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (n3 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> n2).
    assert (Hsp3 : n3 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne n2 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x844  c.ldsp s1,8(sp) ---- *)
    iApply (wp_sh_reload C pt CID3 Psh 0x844 0x846 32 8
              (mword_of_int 1 : mword 6) s1_idx (m !!! Regidx s1_idx)
              Mx n3 sp0 Hst Hsp3
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs1 (ui_sh_844 pt Mx Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (n4 := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> n3).
    assert (Hsp4 : n4 !!! Regidx csp_rs1 = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne n3 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp3. }
    (* ---- 0x846  c.addi16sp sp,sp,32 ---- *)
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    assert (Hwsp : sp0 = add_vec (n4 !!! Regidx csp_rs1)
                           (sign_extend' 64
                              (caddi16sp_imm (mword_of_int 2 : mword 6)))).
    { rewrite Hsp4.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 32 + 32) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh Mx n4 (mword_of_int 0x846)
              (mword_of_int 2 : mword 6) sp0
              (ui_sh_846 pt Mx Hl Htext) Hwsp with "Hcg Hpc").
    iIntros (CID5) "Hcg Hpc".
    set (n5 := <[Regidx csp_rs1 := regval_into_reg sp0]> n4).
    assert (E846 : add_vec_int (mword_of_int 0x846 : mword 64) 2
                   = mword_of_int 0x848)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E846) in "Hpc".
    (* ---- 0x848  c.jr ra ---- *)
    assert (Hra5 : n5 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne n4 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne n3 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne n2 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq n1 (Regidx ra_idx) _). }
    assert (Htgt : (m !!! Regidx ra_idx) = ret_pc (n5 !!! Regidx ra_idx)).
    { rewrite Hra5. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh Mx n5 (mword_of_int 0x848)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_848 pt Mx Hl Htext)
              ltac:(vm_compute; discriminate) Htgt with "Hcg Hpc").
    iIntros (CID6) "Hcg Hpc".
    iApply ("Hcont" $! CID6 n5 with "[] [] Hcg Hpc").
    - iPureIntro. intros r Hr.
      destruct (decide (Regidx r = Regidx csp_rs1)) as [ Esp | Nsp ].
      { rewrite Esp. rewrite (upd_eq n4 (Regidx csp_rs1) _).
        symmetry. exact Hspm. }
      rewrite (upd_ne n4 (Regidx csp_rs1) (Regidx r) _ Nsp).
      destruct (decide (Regidx r = Regidx s1_idx)) as [ E1 | N1 ].
      { rewrite E1. exact (upd_eq n3 (Regidx s1_idx) _). }
      rewrite (upd_ne n3 (Regidx s1_idx) (Regidx r) _ N1).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ E0 | N0 ].
      { rewrite E0. exact (upd_eq n2 (Regidx s0_idx) _). }
      rewrite (upd_ne n2 (Regidx s0_idx) (Regidx r) _ N0).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (upd_ne n1 (Regidx ra_idx) (Regidx r) _ Nra).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (upd_ne mx (Regidx a0_idx) (Regidx r) _ Na0).
      exact (Hpres r Hr Nsp N0 N1).
    - iPureIntro.
      rewrite (upd_ne n4 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne n3 (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne n2 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne n1 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mx (Regidx a0_idx) _).
  Qed.

  (* a node field survives every NUL the loop writes: the writes all land in
     the command buffer, which [sh_disj] keeps off the node *)
  Local Lemma nt_node (MB : gmap Z (bv 8)) (s0 cmd len a : Z)
      (ts : list (nat * nat)) (v : mword 64) :
    (forall t : nat * nat, t ∈ ts -> 0 <= Z.of_nat (snd t) < len) ->
    sh_disj s0 len cmd SH_EXECCMD_SZ ->
    cmd <= a -> a + 8 <= cmd + SH_EXECCMD_SZ ->
    uM_bytes MB a 8 v -> uM_bytes (nt_mem MB s0 ts) a 8 v.
  Proof.
    intros Hts Hdisj Hlo Hhi Hbw j Hj.
    rewrite (nt_mem_ne ts MB s0 (a + Z.of_nat j)
               ltac:(intros t Ht; pose proof (Hts t Ht);
                     unfold sh_disj in Hdisj;
                     pose proof (Nat2Z.is_nonneg j); lia)).
    exact (Hbw j Hj).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3 THE ARG LOOP, head 0x822, back edge 0x82e.                         *)
  (*                                                                       *)
  (*   822  c.ld  a4,72(a5)   -- a4 = eargv[i]  (a5 = &cmd->argv[i+1] - 8) *)
  (*   824  sb    zero,0(a4)  -- *eargv[i] = 0                             *)
  (*   828  c.addi a5,a5,8                                                 *)
  (*   82a  ld    a4,-8(a5)   -- a4 = argv[i+1]                            *)
  (*   82e  c.bnez a4,822     -- the BACK EDGE                             *)
  (*   830                    <- the exit (a [c.j] to 0x83e)               *)
  (*                                                                       *)
  (* Ordinary Rocq induction on the STRICT nat measure [|toks| - i]; the    *)
  (* branch leaf is later-free, so a bounded loop pays no [>].  The memory  *)
  (* at index [i] is the EQUATION [nt_mem MB s0 (take i toks)].            *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_nt_loop (nn : nat) :
    forall (CIDp : CpuId) (MB : gmap Z (bv 8)) (mE : regfile) (sp0 : mword 64)
      (cmd s0 : Z) (bs : list (bv 8)) (toks : list (nat * nat)) (i : nat),
      (length toks - i < nn)%nat ->
      sh_text_layout pt ->
      sh_img_sub MB ->
      8208 <= s0 ->
      s0 + Z.of_nat (length bs) + 1 <= 2 ^ 38 ->
      uv_wr pt MB s0 (Z.of_nat (length bs) + 1) ->
      uv_rd pt MB cmd SH_EXECCMD_SZ ->
      cmd mod 16 = 0 ->
      sh_disj s0 (Z.of_nat (length bs) + 1) cmd SH_EXECCMD_SZ ->
      sh_execcmd_argv MB cmd s0 toks ->
      (forall (j : nat) (t : nat * nat), toks !! j = Some t ->
         (fst t < snd t <= length bs)%nat) ->
      (length toks < 10)%nat ->
      (i < length toks)%nat ->
      mE !!! Regidx a5_idx
        = (mword_of_int (cmd + 16 + 8 * Z.of_nat i) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh (nt_mem MB s0 (take i toks)) mE -∗
      pc_is (CID := CIDp) (mword_of_int 0x822) -∗
      (∀ (CID : CpuId) (m' : regfile),
         ⌜forall r : mword 5, Regidx r <> Regidx a5_idx ->
            Regidx r <> Regidx a4_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh (nt_mem MB s0 toks) m' -∗
         pc_is (CID := CID) (mword_of_int 0x830) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction nn as [ | nn IH ];
      intros CIDp MB mE sp0 cmd s0 bs toks i Hmeas Hl Himg Hs0hi Hbufhi Hwr
             Hrd Hal Hdisj Hargv Hsep Hmax Hi Ha5.
    { exfalso. lia. }
    pose proof (urd_lo _ _ _ _ Hrd) as Hcmd0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hcmdhi.
    change (2 ^ 38) with 274877906944 in Hcmdhi.
    change (2 ^ 38) with 274877906944 in Hbufhi.
    pose proof (uwr_lo _ _ _ _ Hwr) as Hs0lo.
    unfold SH_EXECCMD_SZ in Hcmdhi.
    destruct Hargv as (Hav & Hnul1 & Hnul2).
    destruct (lookup_lt_is_Some_2 toks i Hi) as (ti & Hti).
    pose proof (Hsep i ti Hti) as (Hti1 & Hti2).
    destruct (Hav i ti Hti) as (Hargvi & Heargvi).
    (* the memory at the loop head *)
    set (Mi := nt_mem MB s0 (take i toks)).
    assert (Htake : forall t : nat * nat, t ∈ take i toks ->
              0 <= Z.of_nat (snd t) < Z.of_nat (length bs) + 1).
    { intros t Ht.
      apply elem_of_list_lookup in Ht as (j & Hj).
      rewrite lookup_take_Some in Hj. destruct Hj as (Hj & _).
      pose proof (Hsep j t Hj) as (_ & H2).
      pose proof (Nat2Z.is_nonneg (snd t)). lia. }
    assert (HimgI : sh_img_sub Mi) by (unfold Mi; apply nt_img; assumption).
    assert (HtextI : sh_text_sub Mi) by exact (sh_img_text Mi HimgI).
    assert (HdomI : forall k : Z, is_Some (MB !! k) -> is_Some (Mi !! k))
      by (unfold Mi; intros k Hk; apply nt_mem_dom; exact Hk).
    (* ---- 0x822  c.ld a4,72(a5)  (a4 := eargv[i]) ---- *)
    assert (Hea : uM_bytes Mi (cmd + 88 + 8 * Z.of_nat i) 8
                    (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64))
      by (unfold Mi; exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                              (cmd + 88 + 8 * Z.of_nat i) (take i toks) _
                              Htake Hdisj ltac:(lia) ltac:(unfold SH_EXECCMD_SZ; lia)
                              Heargvi)).
    destruct (acc8 Mi (cmd + 88 + 8 * Z.of_nat i) _
                ltac:(lia)
                ltac:(exact (node_off_mod8 cmd 88 i Hal ltac:(reflexivity)))
                ltac:(change (2 ^ 38) with 274877906944; lia) Hea)
      as (Hu1 & Hcn1 & Hpg1 & Hal1 & Hby1 & Hwv1).
    destruct (urd_leaf _ _ _ _ Hrd (88 + 8 * Z.of_nat i)
                ltac:(unfold SH_EXECCMD_SZ; lia)) as (wld1 & Hlf1 & Hok1).
    assert (Hva1 : (mword_of_int (cmd + 88 + 8 * Z.of_nat i) : mword 64)
                   = add_vec (mE !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 9 : mword 5) ('b"000"))))).
    { rewrite Ha5.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 9 : mword 5) ('b"000")))
                    : mword 64) = mword_of_int 72)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    replace (cmd + (88 + 8 * Z.of_nat i)) with (cmd + 88 + 8 * Z.of_nat i)
      in Hlf1 by lia.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_cld C pt Psh Mi mE (mword_of_int 0x822)
              (mword_of_int 9 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 6 : mword 3) a5_idx a4_idx
              wld1 (mword_of_int (cmd + 88 + 8 * Z.of_nat i))
              (mword_of_int (s0 + Z.of_nat (snd ti)))
              (ui_sh_822 pt Mi Hl HtextI)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva1 Hlf1 Hok1 Hcn1 Hpg1 Hal1
              ltac:(rewrite Hu1; exact Hea)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (m1 := <[Regidx a4_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64)]> mE).
    assert (E822 : add_vec_int (mword_of_int 0x822 : mword 64) 2
                   = mword_of_int 0x824)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E822) in "Hpc".
    assert (Hm1a4 : m1 !!! Regidx a4_idx
                    = (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64))
      by exact (upd_eq mE (Regidx a4_idx) _).
    assert (Hm1a5 : m1 !!! Regidx a5_idx
                    = (mword_of_int (cmd + 16 + 8 * Z.of_nat i) : mword 64)).
    { rewrite (upd_ne mE (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5. }
    (* ---- 0x824  sb zero,0(a4)  -- store the NUL at eargv[i] ---- *)
    iDestruct (uv_x0 CID1 Mi m1 with "Hcg") as "[%Hz Hcg]".
    destruct (uwr_leaf _ _ _ _ Hwr (Z.of_nat (snd ti)) ltac:(lia))
      as (wst & Hlfs & Hoks).
    destruct (uwr_bytes _ _ _ _ Hwr (Z.of_nat (snd ti)) ltac:(lia)) as (bb0 & Hbb0).
    destruct (HdomI (s0 + Z.of_nat (snd ti)) (mk_is_Some _ _ Hbb0)) as (bb & Hbb).
    assert (Hus : uint (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64)
                  = s0 + Z.of_nat (snd ti))
      by (apply uint_moi; unfold Z64; lia).
    assert (Hvas : (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64)
                   = add_vec (m1 !!! Regidx a4_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hm1a4.
      assert (Hc0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc0 moi_add. f_equal; lia. }
    assert (Hcns : uva_canon (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hbb' : Mi !! (uint (mword_of_int (s0 + Z.of_nat (snd ti)) : mword 64))
                   = Some bb) by (rewrite Hus; exact Hbb).
    iApply (wp_uv_sb C pt Psh Mi m1 (mword_of_int 0x824)
              (mword_of_int 0 : mword 12) a4_idx x0_idx
              wst (mword_of_int (s0 + Z.of_nat (snd ti))) zero_reg bb
              (ui_sh_824 pt Mi Hl HtextI)
              Hvas (eq_sym Hz) Hlfs Hoks Hcns Hbb'
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    iEval (rewrite Hus) in "Hcg".
    assert (E824 : add_vec_int (mword_of_int 0x824 : mword 64) 4
                   = mword_of_int 0x828)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E824) in "Hpc".
    (* the memory is now the fold over one more token *)
    assert (Hstep : uM_store Mi (s0 + Z.of_nat (snd ti)) 1 zero_reg
                    = nt_mem MB s0 (take (S i) toks)).
    { rewrite (take_S_r toks i ti Hti). unfold Mi.
      symmetry. exact (nt_mem_snoc (take i toks) MB s0 ti). }
    iEval (rewrite Hstep) in "Hcg".
    set (Mj := nt_mem MB s0 (take (S i) toks)).
    assert (HtakeS : forall t : nat * nat, t ∈ take (S i) toks ->
              0 <= Z.of_nat (snd t) < Z.of_nat (length bs) + 1).
    { intros t Ht.
      apply elem_of_list_lookup in Ht as (j & Hj).
      rewrite lookup_take_Some in Hj. destruct Hj as (Hj & _).
      pose proof (Hsep j t Hj) as (_ & H2).
      pose proof (Nat2Z.is_nonneg (snd t)). lia. }
    assert (HimgJ : sh_img_sub Mj) by (unfold Mj; apply nt_img; assumption).
    assert (HtextJ : sh_text_sub Mj) by exact (sh_img_text Mj HimgJ).
    (* ---- 0x828  c.addi a5,a5,8 ---- *)
    assert (Hadd : (mword_of_int (cmd + 16 + 8 * Z.of_nat (S i)) : mword 64)
                   = add_vec (m1 !!! Regidx a5_idx)
                       (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 8 : mword 6)))).
    { rewrite Hm1a5.
      assert (Hc8 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))
                     : mword 64) = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc8 moi_add. f_equal. rewrite Nat2Z.inj_succ. lia. }
    iApply (wp_uv_caddi C pt Psh Mj m1 (mword_of_int 0x828)
              (mword_of_int 8 : mword 6) a5_idx
              (mword_of_int (cmd + 16 + 8 * Z.of_nat (S i)))
              (ui_sh_828 pt Mj Hl HtextJ)
              ltac:(vm_compute; discriminate) Hadd with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (cmd + 16 + 8 * Z.of_nat (S i))
                       : mword 64)]> m1).
    assert (E828 : add_vec_int (mword_of_int 0x828 : mword 64) 2
                   = mword_of_int 0x82a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E828) in "Hpc".
    assert (Hm2a5 : m2 !!! Regidx a5_idx
                    = (mword_of_int (cmd + 16 + 8 * Z.of_nat (S i)) : mword 64))
      by exact (upd_eq m1 (Regidx a5_idx) _).
    (* ---- 0x82a  ld a4,-8(a5)  (a4 := argv[i+1]) ---- *)
    assert (Hvnext : exists vnext : Z,
              0 <= vnext < 274877906944 /\
              uM_bytes MB (cmd + 8 + 8 * Z.of_nat (S i)) 8
                (mword_of_int vnext : mword 64) /\
              ((S i = length toks)%nat -> vnext = 0) /\
              ((S i < length toks)%nat -> vnext <> 0)).
    { destruct (decide ((S i) = length toks)%nat) as [ Hend | Hne ].
      - exists 0. split_and!.
        + lia.
        + lia.
        + rewrite Hend. exact Hnul1.
        + intros _. reflexivity.
        + intros Hlt. exfalso. lia.
      - destruct (lookup_lt_is_Some_2 toks (S i)
                    ltac:(pose proof (lookup_lt_Some toks i ti Hti); lia))
          as (t' & Ht').
        pose proof (Hsep (S i) t' Ht') as (Ht'1 & Ht'2).
        destruct (Hav (S i) t' Ht') as (Hargvn & _).
        exists (s0 + Z.of_nat (fst t')). split_and!.
        + lia.
        + lia.
        + exact Hargvn.
        + intro Hc. exfalso. lia.
        + intros _. lia. }
    destruct Hvnext as (vnext & Hvn & Hvbytes & Hvz & Hvnz).
    assert (Hvj : uM_bytes Mj (cmd + 8 + 8 * Z.of_nat (S i)) 8
                    (mword_of_int vnext : mword 64))
      by (unfold Mj; exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                              (cmd + 8 + 8 * Z.of_nat (S i)) (take (S i) toks) _
                              HtakeS Hdisj ltac:(lia)
                              ltac:(unfold SH_EXECCMD_SZ; lia) Hvbytes)).
    destruct (acc8 Mj (cmd + 8 + 8 * Z.of_nat (S i)) _
                ltac:(lia)
                ltac:(exact (node_off_mod8 cmd 8 (S i) Hal ltac:(reflexivity)))
                ltac:(change (2 ^ 38) with 274877906944;
                      rewrite Nat2Z.inj_succ; lia) Hvj)
      as (Hu2 & Hcn2 & Hpg2 & Hal2 & Hby2 & Hwv2).
    destruct (urd_leaf _ _ _ _ Hrd (8 + 8 * Z.of_nat (S i))
                ltac:(unfold SH_EXECCMD_SZ; rewrite Nat2Z.inj_succ; lia))
      as (wld2 & Hlf2 & Hok2).
    replace (cmd + (8 + 8 * Z.of_nat (S i)))
      with (cmd + 8 + 8 * Z.of_nat (S i)) in Hlf2 by lia.
    assert (Hva2 : (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)) : mword 64)
                   = add_vec (m2 !!! Regidx a5_idx)
                       (sign_extend' 64 (mword_of_int 4088 : mword 12))).
    { rewrite Hm2a5.
      assert (Hc : (sign_extend' 64 (mword_of_int 4088 : mword 12) : mword 64)
                   = mword_of_int (-8)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_ld C pt Psh Mj m2 (mword_of_int 0x82a)
              (mword_of_int 4088 : mword 12) a5_idx a4_idx
              wld2 (mword_of_int (cmd + 8 + 8 * Z.of_nat (S i)))
              (mword_of_int vnext)
              (ui_sh_82a pt Mj Hl HtextJ)
              ltac:(vm_compute; discriminate) Hva2 Hlf2 Hok2 Hcn2 Hpg2 Hal2
              Hby2 Hwv2
              with "Hcg Hpc").
    iIntros (CID4) "Hcg Hpc".
    set (m3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int vnext : mword 64)]> m2).
    assert (E82a : add_vec_int (mword_of_int 0x82a : mword 64) 4
                   = mword_of_int 0x82e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E82a) in "Hpc".
    assert (Hm3a4 : m3 !!! Regidx a4_idx = (mword_of_int vnext : mword 64))
      by exact (upd_eq m2 (Regidx a4_idx) _).
    assert (Hm3a5 : m3 !!! Regidx a5_idx
                    = (mword_of_int (cmd + 16 + 8 * Z.of_nat (S i)) : mword 64)).
    { rewrite (upd_ne m2 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Hm2a5. }
    assert (Hpres3 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
              Regidx r <> Regidx a4_idx -> m3 !!! Regidx r = mE !!! Regidx r).
    { intros r H5 H4.
      rewrite (upd_ne m2 (Regidx a4_idx) (Regidx r) _ H4).
      rewrite (upd_ne m1 (Regidx a5_idx) (Regidx r) _ H5).
      exact (upd_ne mE (Regidx a4_idx) (Regidx r) _ H4). }
    (* ---- 0x82e  c.bnez a4,0x822 ---- *)
    assert (Htgtb : (mword_of_int 0x822 : mword 64)
                    = add_vec (mword_of_int 0x82e)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 250 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (decide ((S i) = length toks)%nat) as [ Hend | Hne ].
    - (* the last token: fall through to 0x830 *)
      assert (Htk : false = neq_vec (m3 !!! Regidx a4_idx) zero_reg).
      { rewrite Hm3a4. rewrite (moi_neq_zero vnext ltac:(unfold Z64; lia)).
        rewrite (Hvz Hend). reflexivity. }
      iApply (wp_uv_cbnez C pt Psh Mj m3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                false (mword_of_int 0x822)
                (ui_sh_82e pt Mj Hl HtextJ)
                ltac:(vm_compute; reflexivity) Htk Htgtb
                ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      assert (E82e : (if false then (mword_of_int 0x822 : mword 64)
                      else add_vec_int (mword_of_int 0x82e : mword 64) 2)
                     = mword_of_int 0x830)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E82e) in "Hpc".
      assert (Hfull : Mj = nt_mem MB s0 toks).
      { unfold Mj. rewrite (take_ge toks (S i) ltac:(lia)). reflexivity. }
      iEval (rewrite Hfull) in "Hcg".
      iApply ("Hcont" $! CID5 m3 with "[] Hcg Hpc").
      iPureIntro. exact Hpres3.
    - (* a further token: take the back edge with i := S i *)
      assert (Htk : true = neq_vec (m3 !!! Regidx a4_idx) zero_reg).
      { rewrite Hm3a4. rewrite (moi_neq_zero vnext ltac:(unfold Z64; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq.
        apply Hvnz. pose proof (lookup_lt_Some toks i ti Hti). lia. }
      iApply (wp_uv_cbnez C pt Psh Mj m3 (mword_of_int 0x82e)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                true (mword_of_int 0x822)
                (ui_sh_82e pt Mj Hl HtextJ)
                ltac:(vm_compute; reflexivity) Htk Htgtb
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      iApply (IH CID5 MB m3 sp0 cmd s0 bs toks (S i)
                ltac:(lia) Hl Himg Hs0hi Hbufhi Hwr Hrd Hal Hdisj
                (conj Hav (conj Hnul1 Hnul2)) Hsep Hmax
                ltac:(pose proof (lookup_lt_Some toks i ti Hti); lia)
                Hm3a5
                with "Hcg Hpc").
      iIntros (CID6 m') "%Hp Hcg Hpc".
      iApply ("Hcont" $! CID6 m' with "[] Hcg Hpc").
      iPureIntro. intros r H5 H4. rewrite (Hp r H5 H4). exact (Hpres3 r H5 H4).
  Qed.

  (* the loop's stores, as a two-window image effect *)
  Local Lemma nt_only (MB : gmap Z (bv 8)) (s0 len fa fn : Z)
      (ts : list (nat * nat)) :
    (forall t : nat * nat, t ∈ ts -> 0 <= Z.of_nat (snd t) < len) ->
    uM_only_in MB (nt_mem MB s0 ts) [sh_win s0 len; sh_win fa fn].
  Proof.
    intro Hts. split.
    - intros k Hk. apply nt_mem_dom. exact Hk.
    - intros k Hk. apply nt_mem_ne. intros t Ht Heq.
      apply Hk. apply (uM_in_windows_here _ s0 len k).
      + apply elem_of_list_here.
      + pose proof (Hts t Ht). lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4 nulterminate @0x7ee, the whole function.                           *)
  (*                                                                       *)
  (*   7ee..7f8  the 32-byte frame (ra,s0,s1) and s1 := cmd                *)
  (*   7fa       if (cmd == 0) return 0                -- not taken        *)
  (*   7fc..800  the switch's RANGE check (type <= 5)  -- not taken        *)
  (*   804..818  the JUMP TABLE: a5 := table[type] + 0x13b0, table at 0x13b0 *)
  (*   81a..81c  if (argv[0] == 0) goto the exit                           *)
  (*   81e       a5 := &cmd->argv[1] - 8                                   *)
  (*   822..82e  the arg loop  830  c.j 83e   83e..848  the exit           *)
  (*                                                                       *)
  (* [Hsep] is GONE from the contract: it admitted OVERLAPPING tokens, and  *)
  (* a boundary landing inside another token makes the postcondition FALSE. *)
  (* [Htoks : sh_tokens bs off toks] replaces it; §0's [sh_tokens_sep] and   *)
  (* [sh_tokens_bounds] recover the separation and the old [Hsep] from it.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_nulterminate (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd s0 : Z) (bs : list (bv 8)) (off : nat)
      (toks : list (nat * nat)) :
    wp_sh_nulterminate_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 cmd s0 bs off toks.
  Proof.
    intros Hpre Hsp Hst Hcmd Htype Hargv Hrd Hnode Hbufc Hmax Hoff Htoks Hret2.
    destruct Hpre as (Hlay & Himg & Htab & Hbufok & Hnosym & Hrdbuf & Hwrbuf &
                      Hs0hi & Hs0hi2 & Hfr & Hbuflo).
    assert (Hs0p : 0 < s0) by lia.
    (* the buffer misses the node, because it is BELOW the heap *)
    destruct Hbufc as (Hbcf & Hbcb & Hbufh).
    (* THE SEPARATION, and the old [Hsep], both out of [sh_tokens] *)
    pose proof (sh_tokens_sep bs Hnosym off toks Htoks Hoff) as Hsepx.
    assert (Hsep : forall (i : nat) (t : nat * nat), toks !! i = Some t ->
              (fst t < snd t <= length bs)%nat).
    { intros i t Hi.
      destruct (sh_tokens_bounds bs off toks Htoks Hoff i t Hi) as (_ & Q1 & Q2).
      lia. }
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (sh_img_data M Himg) as Hdata.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    (* THE NODE, from [Hnode]: inside the heap and 16-aligned *)
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    pose proof (Z.div_mod hbase 4096 ltac:(lia)) as Hhbq.
    assert (Hnu : sh_nunits SH_EXECCMD_SZ = 12)
      by (unfold sh_nunits, SH_EXECCMD_SZ; vm_compute; reflexivity).
    rewrite Hnu in Hnode.
    assert (Hnlo : hbase <= cmd) by lia.
    assert (Hnhi : cmd + SH_EXECCMD_SZ <= hbase + 65536)
      by (unfold SH_EXECCMD_SZ; lia).
    assert (Hnal : cmd mod 16 = 0).
    { replace cmd with ((256 * (hbase / 4096) + 4085) * 16) by lia.
      apply Z.mod_mul. lia. }
    unfold sh_frame_ok in Hfr.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi2.
    unfold SH_EXECCMD_SZ in Hnhi.
    destruct sh_syms_pins as
      (_&_&_&_&_&_&_&_&_&_&_&_&_&_& Hsnul &_&_&_&_&_&_&_&_&_&_&_&_&_&_).
    assert (Hbot : hbase + 65536 <= uint sp0 - 32) by lia.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsnul) in "Hpc".
    (* ---- 0x7ee  c.addi sp,sp,-32 ---- *)
    assert (Hi32 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                    : mword 64) = mword_of_int (-32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hspw : (mword_of_int (uint sp0 - 32) : mword 64)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64
                          (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite Hsp Hi32 moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh M m (mword_of_int 0x7ee)
              (mword_of_int 32 : mword 6) sp_idx (mword_of_int (uint sp0 - 32))
              (ui_sh_7ee pt M Hl Htext)
              ltac:(vm_compute; discriminate) Hspw with "Hcg Hpc").
    iIntros (CIDa) "Hcg Hpc".
    set (p1 := <[Regidx sp_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 32) : mword 64)]> m).
    assert (E7ee : add_vec_int (mword_of_int 0x7ee : mword 64) 2
                   = mword_of_int 0x7f0)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7ee) in "Hpc".
    assert (Hp1sp : p1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hp1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              p1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx sp_idx) (Regidx r) _ Hr)).
    (* ---- 0x7f0 / 0x7f2 / 0x7f4  the three spills ---- *)
    iApply (wp_sh_spill C pt CIDa Psh 0x7f0 0x7f2 32 24
              (mword_of_int 3 : mword 6) ra_idx M p1 sp0 Hst Hp1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_7f0 pt M Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDb) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 32 + 24) (p1 !!! Regidx ra_idx)).
    assert (Hne1 : forall k : Z, (k < uint sp0 - 32 \/ uint sp0 <= k) ->
              M1 !! k = M !! k)
      by (intros k Hk; apply st8_ne; lia).
    assert (Hdom1 : forall k : Z, is_Some (M !! k) -> is_Some (M1 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact Hk).
    assert (Htext1 : sh_text_sub M1).
    { intros k b Hk. rewrite (Hne1 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hst1 : uv_stack pt M1 sp0 32)
      by exact (uv_stack_dom pt M M1 sp0 32 Hdom1 Hst).
    iApply (wp_sh_spill C pt CIDb Psh 0x7f2 0x7f4 32 16
              (mword_of_int 2 : mword 6) s0_idx M1 p1 sp0 Hst1 Hp1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_7f2 pt M1 Hl Htext1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDc) "Hcg Hpc".
    set (M2 := uM_store8 M1 (uint sp0 - 32 + 16) (p1 !!! Regidx s0_idx)).
    assert (Hne2 : forall k : Z, (k < uint sp0 - 32 \/ uint sp0 <= k) ->
              M2 !! k = M !! k).
    { intros k Hk. unfold M2.
      rewrite (st8_ne M1 (uint sp0 - 32 + 16) (p1 !!! Regidx s0_idx) k
                 ltac:(lia)).
      exact (Hne1 k ltac:(lia)). }
    assert (Hdom2 : forall k : Z, is_Some (M !! k) -> is_Some (M2 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hdom1 k Hk)).
    assert (Htext2 : sh_text_sub M2).
    { intros k b Hk. rewrite (Hne2 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hst2 : uv_stack pt M2 sp0 32)
      by exact (uv_stack_dom pt M M2 sp0 32 Hdom2 Hst).
    iApply (wp_sh_spill C pt CIDc Psh 0x7f4 0x7f6 32 8
              (mword_of_int 1 : mword 6) s1_idx M2 p1 sp0 Hst2 Hp1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_7f4 pt M2 Hl Htext2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDd) "Hcg Hpc".
    set (MB := uM_store8 M2 (uint sp0 - 32 + 8) (p1 !!! Regidx s1_idx)).
    assert (HneB : forall k : Z, (k < uint sp0 - 32 \/ uint sp0 <= k) ->
              MB !! k = M !! k).
    { intros k Hk. unfold MB.
      rewrite (st8_ne M2 (uint sp0 - 32 + 8) (p1 !!! Regidx s1_idx) k
                 ltac:(lia)).
      exact (Hne2 k ltac:(lia)). }
    assert (HdomB : forall k : Z, is_Some (M !! k) -> is_Some (MB !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hdom2 k Hk)).
    assert (HimgB : sh_img_sub MB).
    { split.
      - intros k b Hk. rewrite (HneB k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
        exact (Htext k b Hk).
      - intros k b Hk. rewrite (HneB k ltac:(pose proof (sh_data_key_lt' k b Hk); lia)).
        exact (Hdata k b Hk). }
    assert (HtextB : sh_text_sub MB) by exact (sh_img_text MB HimgB).
    assert (HstB : uv_stack pt MB sp0 32)
      by exact (uv_stack_dom pt M MB sp0 32 HdomB Hst).
    (* the three spill slots, read back *)
    assert (Bra : uM_bytes MB (uint sp0 - 32 + 24) 8 (p1 !!! Regidx ra_idx)).
    { unfold MB, M2, M1.
      apply st8_bne; [ lia | ]. apply st8_bne; [ lia | ]. apply uM_store8_bytes. }
    assert (Bs0 : uM_bytes MB (uint sp0 - 32 + 16) 8 (p1 !!! Regidx s0_idx)).
    { unfold MB, M2. apply st8_bne; [ lia | ]. apply uM_store8_bytes. }
    assert (Bs1 : uM_bytes MB (uint sp0 - 32 + 8) 8 (p1 !!! Regidx s1_idx)).
    { unfold MB. apply uM_store8_bytes. }
    assert (Evra : p1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (Hp1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Evs0 : p1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (Hp1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Evs1 : p1 !!! Regidx s1_idx = m !!! Regidx s1_idx)
      by exact (Hp1 s1_idx ltac:(vm_compute; discriminate)).
    (* ... and everything the body reads, moved to [MB] *)
    assert (HrdB : uv_rd pt MB cmd SH_EXECCMD_SZ).
    { constructor; try (destruct Hrd; assumption).
      intros j Hj. unfold SH_EXECCMD_SZ in Hj.
      destruct (urd_bytes _ _ _ _ Hrd j ltac:(unfold SH_EXECCMD_SZ; lia))
        as (b & Hb).
      exists b. rewrite (HneB (cmd + j) ltac:(lia)). exact Hb. }
    assert (HwrB : uv_wr pt MB s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct Hwrbuf; assumption).
      intros j Hj.
      destruct (uwr_bytes _ _ _ _ Hwrbuf j Hj) as (b & Hb).
      exists b. rewrite (HneB (s0 + j) ltac:(lia)). exact Hb. }
    assert (HargvB : sh_execcmd_argv MB cmd s0 toks).
    { destruct Hargv as (Hav & Hn1 & Hn2). split_and!.
      - intros i t Hi.
        pose proof (Hsep i t Hi) as Hti.
        pose proof (lookup_lt_Some toks i t Hi) as Hilt.
        destruct (Hav i t Hi) as (H1 & H2). split.
        + intros j Hj.
          rewrite (HneB (cmd + 8 + 8 * Z.of_nat i + Z.of_nat j) ltac:(lia)).
          exact (H1 j Hj).
        + intros j Hj.
          rewrite (HneB (cmd + 88 + 8 * Z.of_nat i + Z.of_nat j) ltac:(lia)).
          exact (H2 j Hj).
      - intros j Hj.
        rewrite (HneB (cmd + 8 + 8 * Z.of_nat (length toks) + Z.of_nat j)
                   ltac:(lia)).
        exact (Hn1 j Hj).
      - intros j Hj.
        rewrite (HneB (cmd + 88 + 8 * Z.of_nat (length toks) + Z.of_nat j)
                   ltac:(lia)).
        exact (Hn2 j Hj). }
    assert (HtypeB : uM_bytes MB cmd 4 (mword_of_int 1 : mword 32)).
    { intros j Hj. rewrite (HneB (cmd + Z.of_nat j) ltac:(lia)).
      exact (Htype j Hj). }
    destruct Hbufok as (Hstr & Hbnz).
    assert (HstrB : ustr_at MB s0 bs).
    { destruct Hstr as (Hb1 & Hb2). split.
      - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj).
        rewrite (HneB (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      - rewrite (HneB (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2. }
    (* ---- 0x7f6  c.addi4spn s0,sp,32 ---- *)
    assert (Hi4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                   : mword 64) = mword_of_int 32)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hs0w : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (p1 !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hp1sp Hi4 moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh MB p1 (mword_of_int 0x7f6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_7f6 pt MB Hl HtextB)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hs0w
              with "Hcg Hpc").
    iIntros (CIDe) "Hcg Hpc".
    set (p2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> p1).
    assert (E7f6 : add_vec_int (mword_of_int 0x7f6 : mword 64) 2
                   = mword_of_int 0x7f8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7f6) in "Hpc".
    (* ---- 0x7f8  c.mv s1,a0 ---- *)
    assert (Hp2a0 : p2 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne p1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hp1 a0_idx ltac:(vm_compute; discriminate)). exact Hcmd. }
    assert (Hmv1 : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (p2 !!! Regidx a0_idx))
      by (rewrite Hp2a0 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MB p2 (mword_of_int 0x7f8)
              s1_idx a0_idx (mword_of_int cmd)
              (ui_sh_7f8 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hmv1 with "Hcg Hpc").
    iIntros (CIDf) "Hcg Hpc".
    set (p3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> p2).
    assert (E7f8 : add_vec_int (mword_of_int 0x7f8 : mword 64) 2
                   = mword_of_int 0x7fa)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7f8) in "Hpc".
    assert (Hp3a0 : p3 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne p2 (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp2a0. }
    assert (Hp3s1 : p3 !!! Regidx s1_idx = (mword_of_int cmd : mword 64))
      by exact (upd_eq p2 (Regidx s1_idx) _).
    assert (Hp3sp : p3 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 32) : mword 64)).
    { rewrite (upd_ne p2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hp1sp. }
    assert (Hp3pres : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              Regidx r <> Regidx s0_idx -> Regidx r <> Regidx s1_idx ->
              p3 !!! Regidx r = m !!! Regidx r).
    { intros r N2 N0 N1.
      rewrite (upd_ne p2 (Regidx s1_idx) (Regidx r) _ N1).
      rewrite (upd_ne p1 (Regidx s0_idx) (Regidx r) _ N0).
      exact (Hp1 r N2). }
    (* ---- 0x7fa  c.beqz a0,0x83e  (cmd != 0, so not taken) ---- *)
    assert (Ht7fa : false = eq_vec (p3 !!! Regidx a0_idx) zero_reg).
    { rewrite Hp3a0. rewrite (moi_eq_zero cmd ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uv_cbeqz C pt Psh MB p3 (mword_of_int 0x7fa)
              (mword_of_int 34 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x83e)
              (ui_sh_7fa pt MB Hl HtextB)
              ltac:(vm_compute; reflexivity) Ht7fa
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CIDg) "Hcg Hpc".
    assert (E7fa : (if false then (mword_of_int 0x83e : mword 64)
                    else add_vec_int (mword_of_int 0x7fa : mword 64) 2)
                   = mword_of_int 0x7fc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7fa) in "Hpc".
    (* ---- 0x7fc  c.lw a4,0(a0)  (a4 := cmd->type = 1) ---- *)
    destruct (acc4 MB cmd (mword_of_int 1 : mword 32)
                ltac:(lia)
                ltac:(exact (node_mod4 cmd Hnal))
                ltac:(change (2 ^ 38) with 274877906944; lia) HtypeB)
      as (Huc & Hcnc & Hpgc & Halc & Hbwc).
    destruct (urd_leaf _ _ _ _ HrdB 0 ltac:(unfold SH_EXECCMD_SZ; lia))
      as (wldc & Hlfc & Hokc).
    rewrite Z.add_0_r in Hlfc.
    assert (Hvac : (mword_of_int cmd : mword 64)
                   = add_vec (p3 !!! Regidx a0_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))).
    { rewrite Hp3a0.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
                    : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_clw C pt Psh MB p3 (mword_of_int 0x7fc)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx
              wldc (mword_of_int cmd) (mword_of_int 1) (mword_of_int 1 : mword 32)
              (ui_sh_7fc pt MB Hl HtextB)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hvac Hlfc Hokc Hcnc Hpgc Halc
              Hbwc
              ltac:(symmetry; apply sext32_moi; lia)
              with "Hcg Hpc").
    iIntros (CIDh) "Hcg Hpc".
    set (p4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> p3).
    assert (E7fc : add_vec_int (mword_of_int 0x7fc : mword 64) 2
                   = mword_of_int 0x7fe)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7fc) in "Hpc".
    assert (Hp4 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p4 !!! Regidx r = p3 !!! Regidx r)
      by (intros r H4 H5; exact (upd_ne p3 (Regidx a4_idx) (Regidx r) _ H4)).
    assert (Hp4a4 : p4 !!! Regidx a4_idx = (mword_of_int 1 : mword 64))
      by exact (upd_eq p3 (Regidx a4_idx) _).
    (* ---- 0x7fe  c.li a5,5 ---- *)
    assert (Hli5 : (mword_of_int 5 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh MB p4 (mword_of_int 0x7fe)
              (mword_of_int 5 : mword 6) a5_idx (mword_of_int 5 : mword 64)
              (ui_sh_7fe pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hli5 with "Hcg Hpc").
    iIntros (CIDi) "Hcg Hpc".
    set (p5 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 5 : mword 64)]> p4).
    assert (E7fe : add_vec_int (mword_of_int 0x7fe : mword 64) 2
                   = mword_of_int 0x800)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E7fe) in "Hpc".
    assert (Hp5 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p5 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p4 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp4 r H4 H5). }
    assert (Hp5a5 : p5 !!! Regidx a5_idx = (mword_of_int 5 : mword 64))
      by exact (upd_eq p4 (Regidx a5_idx) _).
    assert (Hp5a4 : p5 !!! Regidx a4_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_ne p4 (Regidx a5_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp4a4. }
    (* ---- 0x800  bltu a5,a4,0x83e  (5 <u 1 is false) ---- *)
    assert (Ht800 : false = uv_btaken BLTU (p5 !!! Regidx a5_idx)
                              (p5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Hp5a5 Hp5a4.
      rewrite (moi_lt_u 5 1 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uv_btype C pt Psh MB p5 (mword_of_int 0x800)
              (mword_of_int 62 : mword 13) a4_idx a5_idx BLTU
              false (mword_of_int 0x83e)
              (ui_sh_800 pt MB Hl HtextB)
              Ht800 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CIDj) "Hcg Hpc".
    assert (E800 : (if false then (mword_of_int 0x83e : mword 64)
                    else add_vec_int (mword_of_int 0x800 : mword 64) 4)
                   = mword_of_int 0x804)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E800) in "Hpc".
    (* ---- 0x804  lwu a5,0(a0)  (a5 := (unsigned)cmd->type = 1) ---- *)
    assert (Hp5a0 : p5 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (Hp5 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hp3a0. }
    assert (Hvac2 : (mword_of_int cmd : mword 64)
                    = add_vec (p5 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hp5a0.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_lwu C pt Psh MB p5 (mword_of_int 0x804)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              wldc (mword_of_int cmd) (mword_of_int 1) (mword_of_int 1 : mword 32)
              (ui_sh_804 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hvac2 Hlfc Hokc Hcnc Hpgc Halc
              Hbwc
              ltac:(symmetry; apply zext32_moi; lia)
              with "Hcg Hpc").
    iIntros (CIDk) "Hcg Hpc".
    set (p6 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> p5).
    assert (E804 : add_vec_int (mword_of_int 0x804 : mword 64) 4
                   = mword_of_int 0x808)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E804) in "Hpc".
    assert (Hp6 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p6 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p5 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp5 r H4 H5). }
    assert (Hp6a5 : p6 !!! Regidx a5_idx = (mword_of_int 1 : mword 64))
      by exact (upd_eq p5 (Regidx a5_idx) _).
    (* ---- 0x808  c.slli a5,a5,0x2  (a5 := 4) ---- *)
    assert (Hshl : (mword_of_int 4 : mword 64)
                   = shift_bits_left (p6 !!! Regidx a5_idx)
                       (subrange_vec_dec (mword_of_int 2 : mword 6)
                          (Z.sub log2_xlen 1) 0)).
    { rewrite Hp6a5. rewrite (moi_shl 1 2 ltac:(lia)). f_equal; lia. }
    iApply (wp_uv_cslli C pt Psh MB p6 (mword_of_int 0x808)
              (mword_of_int 2 : mword 6) a5_idx (mword_of_int 4)
              (ui_sh_808 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hshl with "Hcg Hpc").
    iIntros (CIDl) "Hcg Hpc".
    set (p7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 4 : mword 64)]> p6).
    assert (E808 : add_vec_int (mword_of_int 0x808 : mword 64) 2
                   = mword_of_int 0x80a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E808) in "Hpc".
    assert (Hp7 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p7 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p6 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp6 r H4 H5). }
    assert (Hp7a5 : p7 !!! Regidx a5_idx = (mword_of_int 4 : mword 64))
      by exact (upd_eq p6 (Regidx a5_idx) _).
    (* ---- 0x80a  auipc a4,0x1  (a4 := 0x180a) ---- *)
    assert (Hau : (mword_of_int 6154 : mword 64)
                  = add_vec (mword_of_int 0x80a) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh MB p7 (mword_of_int 0x80a)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 6154)
              (ui_sh_80a pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hau with "Hcg Hpc").
    iIntros (CIDm) "Hcg Hpc".
    set (p8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 6154 : mword 64)]> p7).
    assert (E80a : add_vec_int (mword_of_int 0x80a : mword 64) 4
                   = mword_of_int 0x80e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E80a) in "Hpc".
    assert (Hp8 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p8 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p7 (Regidx a4_idx) (Regidx r) _ H4).
      exact (Hp7 r H4 H5). }
    assert (Hp8a4 : p8 !!! Regidx a4_idx = (mword_of_int 6154 : mword 64))
      by exact (upd_eq p7 (Regidx a4_idx) _).
    assert (Hp8a5 : p8 !!! Regidx a5_idx = (mword_of_int 4 : mword 64)).
    { rewrite (upd_ne p7 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp7a5. }
    (* ---- 0x80e  addi a4,a4,-1114  (a4 := 0x13b0, the table base) ---- *)
    assert (Hadd1 : (mword_of_int 5040 : mword 64)
                    = add_vec (p8 !!! Regidx a4_idx)
                        (sign_extend' 64 (mword_of_int 2982 : mword 12))).
    { rewrite Hp8a4.
      assert (Hc : (sign_extend' 64 (mword_of_int 2982 : mword 12) : mword 64)
                   = mword_of_int (-1114))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh MB p8 (mword_of_int 0x80e)
              (mword_of_int 2982 : mword 12) a4_idx a4_idx (mword_of_int 5040)
              (ui_sh_80e pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hadd1 with "Hcg Hpc").
    iIntros (CIDn) "Hcg Hpc".
    set (p9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 5040 : mword 64)]> p8).
    assert (E80e : add_vec_int (mword_of_int 0x80e : mword 64) 4
                   = mword_of_int 0x812)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E80e) in "Hpc".
    assert (Hp9 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p9 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p8 (Regidx a4_idx) (Regidx r) _ H4).
      exact (Hp8 r H4 H5). }
    assert (Hp9a4 : p9 !!! Regidx a4_idx = (mword_of_int 5040 : mword 64))
      by exact (upd_eq p8 (Regidx a4_idx) _).
    assert (Hp9a5 : p9 !!! Regidx a5_idx = (mword_of_int 4 : mword 64)).
    { rewrite (upd_ne p8 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp8a5. }
    (* ---- 0x812  c.add a5,a5,a4  (a5 := &table[type]) ---- *)
    assert (Hadd2 : (mword_of_int 5044 : mword 64)
                    = add_vec (p9 !!! Regidx a5_idx) (p9 !!! Regidx a4_idx)).
    { rewrite Hp9a4 Hp9a5 moi_add. f_equal; lia. }
    iApply (wp_uv_cadd C pt Psh MB p9 (mword_of_int 0x812)
              a5_idx a4_idx (mword_of_int 5044)
              (ui_sh_812 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hadd2 with "Hcg Hpc").
    iIntros (CIDo) "Hcg Hpc".
    set (p10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 5044 : mword 64)]> p9).
    assert (E812 : add_vec_int (mword_of_int 0x812 : mword 64) 2
                   = mword_of_int 0x814)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E812) in "Hpc".
    assert (Hp10 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p10 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p9 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp9 r H4 H5). }
    assert (Hp10a5 : p10 !!! Regidx a5_idx = (mword_of_int 5044 : mword 64))
      by exact (upd_eq p9 (Regidx a5_idx) _).
    assert (Hp10a4 : p10 !!! Regidx a4_idx = (mword_of_int 5040 : mword 64)).
    { rewrite (upd_ne p9 (Regidx a5_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp9a4. }
    (* ---- 0x814  c.lw a5,0(a5)  -- THE JUMP TABLE READ.
       The four bytes at 0x13b4 are 6a f4 ff ff, i.e. the signed 32-bit
       displacement -2966; the entry is read out of the DUMPED DATA IMAGE
       ([sh_data_sub]), not out of the text map. ---- *)
    assert (Hjw : uM_bytes MB 5044 4 (mword_of_int 4294964330 : mword 32)).
    { intros j Hj.
      assert (Hb0 : nth_byte (mword_of_int 4294964330 : mword 32) 0
                    = Z_to_bv 8 0x6a) by (apply bv_eq; vm_compute; reflexivity).
      assert (Hb1 : nth_byte (mword_of_int 4294964330 : mword 32) 1
                    = Z_to_bv 8 0xf4) by (apply bv_eq; vm_compute; reflexivity).
      assert (Hb2 : nth_byte (mword_of_int 4294964330 : mword 32) 2
                    = Z_to_bv 8 0xff) by (apply bv_eq; vm_compute; reflexivity).
      assert (Hb3 : nth_byte (mword_of_int 4294964330 : mword 32) 3
                    = Z_to_bv 8 0xff) by (apply bv_eq; vm_compute; reflexivity).
      destruct j as [ | [ | [ | [ | j ] ] ] ]; try (exfalso; lia).
      - rewrite Hb0. change (5044 + Z.of_nat 0) with 5044.
        apply (proj2 HimgB). vm_compute.
        first [ reflexivity | f_equal; apply bv_eq; reflexivity ].
      - rewrite Hb1. change (5044 + Z.of_nat 1) with 5045.
        apply (proj2 HimgB). vm_compute.
        first [ reflexivity | f_equal; apply bv_eq; reflexivity ].
      - rewrite Hb2. change (5044 + Z.of_nat 2) with 5046.
        apply (proj2 HimgB). vm_compute.
        first [ reflexivity | f_equal; apply bv_eq; reflexivity ].
      - rewrite Hb3. change (5044 + Z.of_nat 3) with 5047.
        apply (proj2 HimgB). vm_compute.
        first [ reflexivity | f_equal; apply bv_eq; reflexivity ]. }
    destruct (acc4 MB 5044 (mword_of_int 4294964330 : mword 32)
                ltac:(lia) ltac:(vm_compute; reflexivity)
                ltac:(change (2 ^ 38) with 274877906944; lia) Hjw)
      as (Huj & Hcnj & Hpgj & Halj & Hbwj).
    destruct (sh_text_layout_load pt 5044 Hl ltac:(lia)) as (wldj & Hlfj & Hokj).
    assert (Hvaj : (mword_of_int 5044 : mword 64)
                   = add_vec (p10 !!! Regidx a5_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))).
    { rewrite Hp10a5.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
                    : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_clw C pt Psh MB p10 (mword_of_int 0x814)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx
              wldj (mword_of_int 5044) (mword_of_int (-2966))
              (mword_of_int 4294964330 : mword 32)
              (ui_sh_814 pt MB Hl HtextB)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hvaj Hlfj Hokj Hcnj Hpgj Halj
              Hbwj
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDp1) "Hcg Hpc".
    set (p11 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (-2966) : mword 64)]> p10).
    assert (E814 : add_vec_int (mword_of_int 0x814 : mword 64) 2
                   = mword_of_int 0x816)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E814) in "Hpc".
    assert (Hp11 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p11 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p10 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp10 r H4 H5). }
    assert (Hp11a5 : p11 !!! Regidx a5_idx = (mword_of_int (-2966) : mword 64))
      by exact (upd_eq p10 (Regidx a5_idx) _).
    assert (Hp11a4 : p11 !!! Regidx a4_idx = (mword_of_int 5040 : mword 64)).
    { rewrite (upd_ne p10 (Regidx a5_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Hp10a4. }
    (* ---- 0x816  c.add a5,a5,a4  (a5 := 0x13b0 - 2966 = 0x81a) ---- *)
    assert (Hadd3 : (mword_of_int 2074 : mword 64)
                    = add_vec (p11 !!! Regidx a5_idx) (p11 !!! Regidx a4_idx)).
    { rewrite Hp11a4 Hp11a5 moi_add. f_equal; lia. }
    iApply (wp_uv_cadd C pt Psh MB p11 (mword_of_int 0x816)
              a5_idx a4_idx (mword_of_int 2074)
              (ui_sh_816 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Hadd3 with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    set (p12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 2074 : mword 64)]> p11).
    assert (E816 : add_vec_int (mword_of_int 0x816 : mword 64) 2
                   = mword_of_int 0x818)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E816) in "Hpc".
    assert (Hp12 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p12 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p11 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp11 r H4 H5). }
    assert (Hp12a5 : p12 !!! Regidx a5_idx = (mword_of_int 2074 : mword 64))
      by exact (upd_eq p11 (Regidx a5_idx) _).
    (* ---- 0x818  c.jr a5  -- the computed transfer, to the EXEC arm ---- *)
    assert (Htgtj : (mword_of_int 0x81a : mword 64)
                    = ret_pc (p12 !!! Regidx a5_idx)).
    { rewrite Hp12a5. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 (mword_of_int 2074)
               ltac:(vm_compute; reflexivity)). }
    iApply (wp_uv_cjr C pt Psh MB p12 (mword_of_int 0x818)
              a5_idx (mword_of_int 0x81a)
              (ui_sh_818 pt MB Hl HtextB)
              ltac:(vm_compute; discriminate) Htgtj with "Hcg Hpc").
    iIntros (CIDp3) "Hcg Hpc".
    (* ---- 0x81a  c.ld a5,8(a0)  (a5 := argv[0]) ---- *)
    destruct HargvB as (HavB & Hn1B & Hn2B).
    assert (Hv0 : exists v0 : Z,
              0 <= v0 < 274877906944 /\
              uM_bytes MB (cmd + 8) 8 (mword_of_int v0 : mword 64) /\
              (toks = [] -> v0 = 0) /\ ((0 < length toks)%nat -> v0 <> 0)).
    { destruct toks as [ | t0 tks ].
      - exists 0. split_and!.
        + lia.
        + lia.
        + replace (cmd + 8) with (cmd + 8 + 8 * Z.of_nat (length (@nil (nat * nat))))
            by (cbn [length]; lia).
          exact Hn1B.
        + intros _. reflexivity.
        + cbn [length]. intro Hc0. exfalso. lia.
      - destruct (HavB 0%nat t0 ltac:(reflexivity)) as (Hb0 & _).
        pose proof (Hsep 0%nat t0 ltac:(reflexivity)) as (Hs1 & Hs2).
        exists (s0 + Z.of_nat (fst t0)). split_and!.
        + lia.
        + lia.
        + replace (cmd + 8) with (cmd + 8 + 8 * Z.of_nat 0) by lia. exact Hb0.
        + intro Hc0. discriminate Hc0.
        + intros _. lia. }
    destruct Hv0 as (v0 & Hv0r & Hv0b & Hv0z & Hv0nz).
    destruct (acc8 MB (cmd + 8) (mword_of_int v0 : mword 64)
                ltac:(lia)
                ltac:(exact (node_off_mod8' cmd 8 Hnal ltac:(reflexivity)))
                ltac:(change (2 ^ 38) with 274877906944; lia) Hv0b)
      as (Hu0 & Hcn0 & Hpg0 & Hal0 & Hby0 & Hwv0).
    destruct (urd_leaf _ _ _ _ HrdB 8 ltac:(unfold SH_EXECCMD_SZ; lia))
      as (wld0 & Hlf0 & Hok0).
    assert (Hp12a0 : p12 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (Hp12 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hp3a0. }
    assert (Hva0 : (mword_of_int (cmd + 8) : mword 64)
                   = add_vec (p12 !!! Regidx a0_idx)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 5) ('b"000"))))).
    { rewrite Hp12a0.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 5) ('b"000")))
                    : mword 64) = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_cld C pt Psh MB p12 (mword_of_int 0x81a)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 7 : mword 3) a0_idx a5_idx
              wld0 (mword_of_int (cmd + 8)) (mword_of_int v0)
              (ui_sh_81a pt MB Hl HtextB)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hva0 Hlf0 Hok0 Hcn0 Hpg0 Hal0
              ltac:(rewrite Hu0; exact Hv0b)
              with "Hcg Hpc").
    iIntros (CIDp4) "Hcg Hpc".
    set (p13 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int v0 : mword 64)]> p12).
    assert (E81a : add_vec_int (mword_of_int 0x81a : mword 64) 2
                   = mword_of_int 0x81c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E81a) in "Hpc".
    assert (Hp13 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> p13 !!! Regidx r = p3 !!! Regidx r).
    { intros r H4 H5. rewrite (upd_ne p12 (Regidx a5_idx) (Regidx r) _ H5).
      exact (Hp12 r H4 H5). }
    assert (Hp13a5 : p13 !!! Regidx a5_idx = (mword_of_int v0 : mword 64))
      by exact (upd_eq p12 (Regidx a5_idx) _).
    (* ---- 0x81c  c.beqz a5,0x83e  (argv[0] == 0 iff there are no tokens) -- *)
    assert (Htgt81c : (mword_of_int 0x83e : mword 64)
                      = add_vec (mword_of_int 0x81c)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 17 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec v0 0) as [ Hz0 | Hnz0 ].
    - (* --- no tokens: straight to the exit --- *)
      assert (Htnil : toks = []).
      { destruct toks as [ | t0 tks ]; [ reflexivity | ].
        exfalso. apply (Hv0nz ltac:(cbn [length]; lia)). exact Hz0. }
      assert (Htk : true = eq_vec (p13 !!! Regidx a5_idx) zero_reg).
      { rewrite Hp13a5. rewrite (moi_eq_zero v0 ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_eq. exact Hz0. }
      iApply (wp_uv_cbeqz C pt Psh MB p13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                true (mword_of_int 0x83e)
                (ui_sh_81c pt MB Hl HtextB)
                ltac:(vm_compute; reflexivity) Htk Htgt81c
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CIDp5) "Hcg Hpc".
      iApply (wp_sh_nt_exit CIDp5 MB m p13 sp0 cmd
                (p1 !!! Regidx ra_idx) (p1 !!! Regidx s0_idx)
                (p1 !!! Regidx s1_idx)
                Hl HtextB HstB Hret2 Hsp Evra Evs0 Evs1
                ltac:(rewrite (Hp13 csp_rs1 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hp3sp)
                ltac:(rewrite (Hp13 s1_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hp3s1)
                Bra Bs0 Bs1
                ltac:(intros r Hr N2 N0 N1;
                      assert (N4 : Regidx r <> Regidx a4_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      assert (N5 : Regidx r <> Regidx a5_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      rewrite (Hp13 r N4 N5); exact (Hp3pres r N2 N0 N1))
                with "Hcg Hpc [Hcont]").
      iIntros (CIDp6 m') "%Hcs %Ha0 Hcg Hpc".
      iApply ("Hcont" $! CIDp6 m' MB with "[] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + iPureIntro. intros i t Hi. rewrite Htnil in Hi.
        rewrite lookup_nil in Hi. discriminate.
      + iPureIntro. exact (conj HavB (conj Hn1B Hn2B)).
      + iPureIntro. split.
        * exact HdomB.
        * intros k Hk. apply HneB.
          destruct (Z.lt_ge_cases k (uint sp0 - 32)) as [ Ha | Ha ];
            [ left; lia | right ].
          destruct (Z.lt_ge_cases k (uint sp0)) as [ Hb | Hb ]; [ | lia ].
          exfalso. apply Hk.
          apply (uM_in_windows_here _ (uint sp0 - 32) 32 k).
          { apply elem_of_list_further. apply elem_of_list_here. }
          { cbn [fst snd]. lia. }
    - (* --- at least one token: the arg loop --- *)
      assert (Htne : (0 < length toks)%nat).
      { destruct toks as [ | t0 tks ]; [ | cbn [length]; lia ].
        exfalso. apply Hnz0. exact (Hv0z eq_refl). }
      assert (Htk : false = eq_vec (p13 !!! Regidx a5_idx) zero_reg).
      { rewrite Hp13a5. rewrite (moi_eq_zero v0 ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Hnz0. }
      iApply (wp_uv_cbeqz C pt Psh MB p13 (mword_of_int 0x81c)
                (mword_of_int 17 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                false (mword_of_int 0x83e)
                (ui_sh_81c pt MB Hl HtextB)
                ltac:(vm_compute; reflexivity) Htk Htgt81c
                ltac:(intro Hc0; discriminate Hc0)
                with "Hcg Hpc").
      iIntros (CIDp5) "Hcg Hpc".
      assert (E81c : (if false then (mword_of_int 0x83e : mword 64)
                      else add_vec_int (mword_of_int 0x81c : mword 64) 2)
                     = mword_of_int 0x81e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E81c) in "Hpc".
      (* ---- 0x81e  addi a5,a0,16 ---- *)
      assert (Hp13a0 : p13 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
      { rewrite (Hp13 a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hp3a0. }
      assert (Hadd4 : (mword_of_int (cmd + 16 + 8 * Z.of_nat 0) : mword 64)
                      = add_vec (p13 !!! Regidx a0_idx)
                          (sign_extend' 64 (mword_of_int 16 : mword 12))).
      { rewrite Hp13a0.
        assert (Hc : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                     = mword_of_int 16)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. f_equal. cbn [Z.of_nat]. lia. }
      iApply (wp_uv_addi C pt Psh MB p13 (mword_of_int 0x81e)
                (mword_of_int 16 : mword 12) a0_idx a5_idx
                (mword_of_int (cmd + 16 + 8 * Z.of_nat 0))
                (ui_sh_81e pt MB Hl HtextB)
                ltac:(vm_compute; discriminate) Hadd4 with "Hcg Hpc").
      iIntros (CIDp6) "Hcg Hpc".
      set (p14 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (cmd + 16 + 8 * Z.of_nat 0)
                          : mword 64)]> p13).
      assert (E81e : add_vec_int (mword_of_int 0x81e : mword 64) 4
                     = mword_of_int 0x822)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E81e) in "Hpc".
      assert (Hp14 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                Regidx r <> Regidx a5_idx -> p14 !!! Regidx r = p3 !!! Regidx r).
      { intros r H4 H5. rewrite (upd_ne p13 (Regidx a5_idx) (Regidx r) _ H5).
        exact (Hp13 r H4 H5). }
      assert (Hp14a5 : p14 !!! Regidx a5_idx
                       = (mword_of_int (cmd + 16 + 8 * Z.of_nat 0) : mword 64))
        by exact (upd_eq p13 (Regidx a5_idx) _).
      (* ---- 0x822..0x82e  the loop ---- *)
      iApply (wp_sh_nt_loop (S (length toks)) CIDp6 MB p14 sp0 cmd s0 bs toks 0%nat
                ltac:(lia) Hl HimgB Hs0hi ltac:(lia) HwrB HrdB Hnal
                ltac:(unfold sh_disj in *; unfold SH_EXECCMD_SZ; lia)
                (conj HavB (conj Hn1B Hn2B)) Hsep Hmax Htne Hp14a5
                with "Hcg Hpc [Hcont]").
      iIntros (CIDp7 mf) "%Hpf Hcg Hpc".
      (* ---- 0x830  c.j 0x83e ---- *)
      assert (HimgF : sh_img_sub (nt_mem MB s0 toks))
        by (apply nt_img; assumption).
      assert (HtextF : sh_text_sub (nt_mem MB s0 toks))
        by exact (sh_img_text _ HimgF).
      assert (HdomF : forall k : Z, is_Some (MB !! k) -> is_Some (nt_mem MB s0 toks !! k))
        by (intros k Hk; apply nt_mem_dom; exact Hk).
      assert (HstF : uv_stack pt (nt_mem MB s0 toks) sp0 32)
        by exact (uv_stack_dom pt MB _ sp0 32 HdomF HstB).
      assert (Htoksbnd : forall t : nat * nat, t ∈ toks ->
                0 <= Z.of_nat (snd t) < Z.of_nat (length bs) + 1).
      { intros t Ht. apply elem_of_list_lookup in Ht as (j & Hj).
        pose proof (Hsep j t Hj) as (_ & H2).
        pose proof (Nat2Z.is_nonneg (snd t)). lia. }
      assert (HneF : forall k : Z, (k < s0 \/ s0 + Z.of_nat (length bs) + 1 <= k) ->
                nt_mem MB s0 toks !! k = MB !! k).
      { intros k Hk. apply nt_mem_ne. intros t Ht.
        pose proof (Htoksbnd t Ht). lia. }
      iApply (wp_uv_cj C pt Psh (nt_mem MB s0 toks) mf (mword_of_int 0x830)
                (mword_of_int 7 : mword 11) (mword_of_int 0x83e)
                (ui_sh_830 pt _ Hl HtextF)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CIDp8) "Hcg Hpc".
      (* ---- 0x83e..0x848  the exit ---- *)
      assert (BraF : uM_bytes (nt_mem MB s0 toks) (uint sp0 - 32 + 24) 8
                       (p1 !!! Regidx ra_idx))
        by (intros j Hj; rewrite (HneF (uint sp0 - 32 + 24 + Z.of_nat j)
                                    ltac:(lia)); exact (Bra j Hj)).
      assert (Bs0F : uM_bytes (nt_mem MB s0 toks) (uint sp0 - 32 + 16) 8
                       (p1 !!! Regidx s0_idx))
        by (intros j Hj; rewrite (HneF (uint sp0 - 32 + 16 + Z.of_nat j)
                                    ltac:(lia)); exact (Bs0 j Hj)).
      assert (Bs1F : uM_bytes (nt_mem MB s0 toks) (uint sp0 - 32 + 8) 8
                       (p1 !!! Regidx s1_idx))
        by (intros j Hj; rewrite (HneF (uint sp0 - 32 + 8 + Z.of_nat j)
                                    ltac:(lia)); exact (Bs1 j Hj)).
      iApply (wp_sh_nt_exit CIDp8 (nt_mem MB s0 toks) m mf sp0 cmd
                (p1 !!! Regidx ra_idx) (p1 !!! Regidx s0_idx)
                (p1 !!! Regidx s1_idx)
                Hl HtextF HstF Hret2 Hsp Evra Evs0 Evs1
                ltac:(rewrite (Hpf csp_rs1 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hp14 csp_rs1 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hp3sp)
                ltac:(rewrite (Hpf s1_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hp14 s1_idx ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Hp3s1)
                BraF Bs0F Bs1F
                ltac:(intros r Hr N2 N0 N1;
                      assert (N4 : Regidx r <> Regidx a4_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      assert (N5 : Regidx r <> Regidx a5_idx)
                        by (intro E; injection E as E'; subst r;
                            vm_compute in Hr; discriminate);
                      rewrite (Hpf r N5 N4); rewrite (Hp14 r N4 N5);
                      exact (Hp3pres r N2 N0 N1))
                with "Hcg Hpc [Hcont]").
      iIntros (CIDp9 m') "%Hcs %Ha0 Hcg Hpc".
      iApply ("Hcont" $! CIDp9 m' (nt_mem MB s0 toks)
                with "[] [] [] [] Hcg Hpc").
      + iPureIntro. exact Hcs.
      + (* every token is now a NUL-terminated string at its own address *)
        iPureIntro. intros i t Hi.
        pose proof (Hsep i t Hi) as (Hti1 & Hti2).
        assert (Hlent : length (sh_tok_bytes bs t) = (snd t - fst t)%nat).
        { unfold sh_tok_bytes. rewrite length_take length_drop. lia. }
        split.
        * intros j b Hj.
          apply lookup_take_Some in Hj as (Hj & Hjlt).
          rewrite lookup_drop in Hj.
          (* THE separation premise is spent here: a byte strictly inside a
             token is not any token's END, so no NUL was written on it *)
          rewrite (nt_mem_ne toks MB s0 (s0 + Z.of_nat (fst t) + Z.of_nat j)
                     ltac:(intros u Hu;
                           apply elem_of_list_lookup in Hu as (i2 & Hi2);
                           pose proof (Hsepx i i2 t u Hi Hi2) as Hno; lia)).
          rewrite (HneB (s0 + Z.of_nat (fst t) + Z.of_nat j) ltac:(lia)).
          replace (s0 + Z.of_nat (fst t) + Z.of_nat j)
            with (s0 + Z.of_nat (fst t + j)) by lia.
          exact (proj1 Hstr (fst t + j)%nat b Hj).
        * rewrite Hlent.
          replace (s0 + Z.of_nat (fst t) + Z.of_nat (snd t - fst t))
            with (s0 + Z.of_nat (snd t)) by lia.
          apply nt_mem_zero. apply elem_of_list_lookup. exists i. exact Hi.
      + (* the node is untouched *)
        iPureIntro. split_and!.
        * intros i t Hi.
          pose proof (Hsep i t Hi) as Hti.
          pose proof (lookup_lt_Some toks i t Hi) as Hilt.
          destruct (HavB i t Hi) as (H1 & H2). split.
          { exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                     (cmd + 8 + 8 * Z.of_nat i) toks _ Htoksbnd
                     ltac:(unfold sh_disj in *; unfold SH_EXECCMD_SZ; lia)
                     ltac:(lia) ltac:(unfold SH_EXECCMD_SZ; lia) H1). }
          { exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                     (cmd + 88 + 8 * Z.of_nat i) toks _ Htoksbnd
                     ltac:(unfold sh_disj in *; unfold SH_EXECCMD_SZ; lia)
                     ltac:(lia) ltac:(unfold SH_EXECCMD_SZ; lia) H2). }
        * exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                   (cmd + 8 + 8 * Z.of_nat (length toks)) toks _ Htoksbnd
                   ltac:(unfold sh_disj in *; unfold SH_EXECCMD_SZ; lia)
                   ltac:(lia) ltac:(unfold SH_EXECCMD_SZ; lia) Hn1B).
        * exact (nt_node MB s0 cmd (Z.of_nat (length bs) + 1)
                   (cmd + 88 + 8 * Z.of_nat (length toks)) toks _ Htoksbnd
                   ltac:(unfold sh_disj in *; unfold SH_EXECCMD_SZ; lia)
                   ltac:(lia) ltac:(unfold SH_EXECCMD_SZ; lia) Hn2B).
      + (* the buffer and the frame, and nothing else *)
        iPureIntro.
        apply (uM_only_in_trans M MB (nt_mem MB s0 toks)).
        * split.
          { exact HdomB. }
          { intros k Hk. apply HneB.
            destruct (Z.lt_ge_cases k (uint sp0 - 32)) as [ Ha | Ha ];
              [ left; lia | right ].
            destruct (Z.lt_ge_cases k (uint sp0)) as [ Hb | Hb ]; [ | lia ].
            exfalso. apply Hk.
            apply (uM_in_windows_here _ (uint sp0 - 32) 32 k).
            { apply elem_of_list_further. apply elem_of_list_here. }
            { cbn [fst snd]. lia. } }
        * exact (nt_only MB s0 (Z.of_nat (length bs) + 1) (uint sp0 - 32) 32
                   toks Htoksbnd).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5 The two transports [parsecmd] needs across each of its four calls. *)
  (* ------------------------------------------------------------------- *)

  (* a doubleword ABOVE every disturbed window survives the call *)
  Local Lemma keep_hi (Mx My : gmap Z (bv 8)) (ws : list (Z * Z)) (lo a : Z)
      (v : mword 64) :
    uM_only_in Mx My ws ->
    (forall w : Z * Z, w ∈ ws -> fst w + snd w <= lo) ->
    lo <= a ->
    uM_bytes Mx a 8 v -> uM_bytes My a 8 v.
  Proof.
    intros Honly Hws Hlo Hbw j Hj.
    rewrite (uM_only_in_out Mx My ws (a + Z.of_nat j) Honly
               ltac:(intros w Hw Hin; pose proof (Hws w Hw);
                     pose proof (Nat2Z.is_nonneg j); lia)).
    exact (Hbw j Hj).
  Qed.

  (* ... and so does the loaded image, whose keys all sit below 8208 *)
  Local Lemma keep_img (Mx My : gmap Z (bv 8)) (ws : list (Z * Z)) :
    uM_only_in Mx My ws ->
    (forall w : Z * Z, w ∈ ws -> 8208 <= fst w) ->
    sh_img_sub Mx -> sh_img_sub My.
  Proof.
    intros Honly Hws (Htext & Hdata). split.
    - refine (uM_only_in_img ShInstrs.sh_bytes Mx My ws 8208 _ _ Honly Htext).
      + intros k b Hk. pose proof (sh_bytes_key_lt k b Hk). lia.
      + intros k Hk (w & Hw & Hin). pose proof (Hws w Hw). lia.
    - refine (uM_only_in_img ShData.sh_data Mx My ws 8208 _ _ Honly Hdata).
      + intros k b Hk. exact (sh_data_key_lt' k b Hk).
      + intros k Hk (w & Hw & Hin). pose proof (Hws w Hw). lia.
  Qed.

  Local Lemma keep_dom (Mx My : gmap Z (bv 8)) (ws : list (Z * Z)) :
    uM_only_in Mx My ws ->
    forall k : Z, is_Some (Mx !! k) -> is_Some (My !! k).
  Proof. intros (Hd & _). exact Hd. Qed.

  (* ------------------------------------------------------------------- *)
  (* §6 [parseline]'s contract, as a section HYPOTHESIS.                   *)
  (*                                                                       *)
  (* It is proved by a sibling lane into UProofShParse.v; carrying it here  *)
  (* as a hypothesis rather than as an [Admitted] keeps the hole VISIBLE in *)
  (* [wp_sh_parsecmd]'s type.                                              *)
  (*                                                                       *)
  (* It is exactly [USpecShParse.wp_sh_parseline_body] -- including the     *)
  (* conjunct that says where the parse left [*ps], which parsecmd needs     *)
  (* both for its own trailing [peek] (whose [sh_ptr_cell] premise wants the *)
  (* offset) and to discharge the `s == es' test guarding the unreachable    *)
  (* [panic("syntax")].                                                      *)
  (* ------------------------------------------------------------------- *)
  Hypothesis Hparseline :
    forall (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (psaddr s0 : Z) (bs : list (bv 8)) (off : nat) (toks : list (nat * nat)),
      wp_sh_parseline_body (CID := CIDp) C pt gin gbrk hbase hlen Q
        M m sp0 psaddr s0 bs off toks.

  (* "k is outside the window [a, a+n) of a window list" *)
  Local Lemma nwin (ws : list (Z * Z)) (a n k : Z) :
    (a, n) ∈ ws -> ~ uM_in_windows ws k -> k < a \/ a + n <= k.
  Proof.
    intros Hin Hnot.
    destruct (Z.lt_ge_cases k a) as [ Hlt | Hge ]; [ left; lia | ].
    destruct (Z.lt_ge_cases k (a + n)) as [ Hlt2 | Hge2 ]; [ | right; lia ].
    exfalso. apply Hnot. exists (a, n). split; [ exact Hin | simpl; lia ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §7 parsecmd @0x86e.                                                   *)
  (*                                                                       *)
  (*   86e..87a  the 64-byte frame (ra,s0,s1,s2,s3) and s0 := sp0          *)
  (*   87c       the LOCAL `char *s' at s0-56 := s                         *)
  (*   880..88a  s1 := s + strlen(s)   ( = es; the shift pair is the        *)
  (*             zero-extension of the `int' strlen returns)               *)
  (*   88c..894  s2 := &s;  parseline(&s, es)                              *)
  (*   898..8a6  s3 := cmd;  peek(&s, es, "")                              *)
  (*   8aa..8ae  the `s == es' test -- its other arm is the UNREACHABLE     *)
  (*             fprintf/panic("syntax") at 0x8c8                          *)
  (*   8b2..8b4  nulterminate(cmd)                                         *)
  (*   8b8..8c6  a0 := cmd and the frame back                              *)
  (*                                                                       *)
  (* The two facts this needs about WHERE the buffer is -- above the loaded *)
  (* image (8208 <= s0) and below the heap -- now come straight out of      *)
  (* [sh_parse_pre] and [sh_buf_clear]; the second is what bounds every     *)
  (* string [sh_exec_below] names.                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parsecmd_strong (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s0 : Z) (bs : list (bv 8)) (toks : list (nat * nat)) :
    forall (Hpre : sh_parse_pre pt hbase hlen M s0 bs sp0
                     (64 + 48 + 48 + 128 + 112 + 64 + 16))
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 48 + 48 + 128 + 112 + 64 + 16))
      (Hs : m !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      (Hbufc : sh_buf_clear hbase s0 (Z.of_nat (length bs) + 1))
      (Htoks : sh_tokens bs 0%nat toks)
      (Hne : (0 < length toks < 10)%nat)
      (Hlen : Z.of_nat (length bs) < 2 ^ 31)
      (Hfreep0  : sh_zeroed M SH_FREEP 0 8)
      (Hbasesz0 : sh_zeroed M (SH_BASE + 8) 0 8)
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    uv_cap_gpr (CID := CIDp) C pt Psh M m -∗
    ubrk gbrk hbase -∗
    pc_is (CID := CIDp) (mword_of_int ShSyms.parsecmd) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)) (cmd p0 : Z),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       ⌜cmd = hbase + 65536 - 16 * (sh_nunits SH_EXECCMD_SZ - 1)⌝ -∗
       ⌜uM_bytes M' cmd 4 (mword_of_int 1 : mword 32)⌝ -∗
       ⌜uM_bytes M' (cmd + 8) 8 (mword_of_int p0 : mword 64)⌝ -∗
       ⌜p0 <> 0⌝ -∗
       ⌜sh_exec_below M' p0 (cmd + 8)
           (sh_tok_bytes bs (default (0%nat, 0%nat) (toks !! 0%nat)))
           (sh_tok_bytes bs <$> toks) (hbase + hlen)⌝ -∗
       ⌜uv_rd pt M' cmd SH_EXECCMD_SZ⌝ -∗
       ⌜uM_only_in M M' [sh_win hbase 65536; sh_win SH_FREEP 8;
                         sh_win SH_BASE 16;
                         sh_win s0 (Z.of_nat (length bs) + 1);
                         sh_win (uint sp0 - (64 + 48 + 48 + 128 + 112 + 64 + 16))
                                (64 + 48 + 48 + 128 + 112 + 64 + 16)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       uv_cap_gpr (CID := CID) C pt Psh M' m' -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpre Hsp Hst Hs Hbufc Htoks Hne Hlen Hfreep0 Hbasesz0 Hbssw Hret2.
    destruct Hpre as (Hlay & Himg & Htab & Hbufok & Hnosym & Hrdbuf & Hwrbuf &
                      Hs0hi & Hs0hi2 & Hfr & Hbuflo).
    assert (Hs0p : 0 < s0) by lia.
    pose proof (sh_img_text M Himg) as Htext.
    pose proof (sh_img_data M Himg) as Hdata.
    pose proof (shl_text _ _ _ Hlay) as Hl.
    pose proof (shl_hlo _ _ _ Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom _ _ _ Hlay) as Hhroom.
    pose proof (shl_hbase _ _ _ Hlay) as Hhb.
    pose proof (shl_hhi _ _ _ Hlay) as Hhhi.
    change (2 ^ 38) with 274877906944 in Hhhi.
    unfold sh_frame_ok in Hfr.
    change (64 + 48 + 48 + 128 + 112 + 64 + 16) with 480 in Hfr, Hst, Hbuflo.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    change (2 ^ 38) with 274877906944 in Hs0hi2.
    change (2 ^ 31) with 2147483648 in Hlen.
    destruct Hbufc as (Hbc1 & Hbc2 & Hbc3).
    unfold sh_disj in Hbc1. unfold sh_disj in Hbc2.
    unfold SH_FREEP, SH_BASE, SH_DATA_PG in Hbc1, Hbc2.
    (* [sh_buf_clear]'s third conjunct IS the bound [sh_exec_below] needs *)
    assert (Hs0lo : s0 + Z.of_nat (length bs) + 1 <= hbase) by lia.
    destruct sh_syms_pins as
      (_&_&_&_&_&_&_& Hspc & Hspl &_&_&_& Hspk &_& Hsnul &_& Hsstr &_&_&_&_&_&
       _&_&_&_&_&_&_&_).
    (* the callee-entry sp *)
    destruct (uv_stack_split pt M sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as (Hst64 & Hst416).
    rewrite (uv_stack_sp_moi pt M sp0 64 Hst64) in Hst416.
    assert (Hubot : uint (mword_of_int (uint sp0 - 64) : mword 64)
                    = uint sp0 - 64) by (apply uint_moi; unfold Z64; lia).
    assert (Hnu : sh_nunits SH_EXECCMD_SZ = 12)
      by (unfold sh_nunits, SH_EXECCMD_SZ; vm_compute; reflexivity).
    rewrite Z.rem_mod_nonneg in Hhb; [ | lia | lia ].
    pose proof (Z.div_mod hbase 4096 ltac:(lia)) as Hhbq.
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hspc) in "Hpc".
    (* ---- 0x86e  c.addi16sp sp,sp,-64 ---- *)
    assert (Hi64 : (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))
                    : mword 64) = mword_of_int (-64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hspw : (mword_of_int (uint sp0 - 64) : mword 64)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { rewrite Hsp Hi64 moi_add_l. f_equal; lia. }
    iApply (wp_uv_caddi16sp C pt Psh M m (mword_of_int 0x86e)
              (mword_of_int 60 : mword 6) (mword_of_int (uint sp0 - 64))
              (ui_sh_86e pt M Hl Htext) Hspw with "Hcg Hpc").
    iIntros (CIDa) "Hcg Hpc".
    set (r1 := <[Regidx csp_rs1
                 := regval_into_reg (mword_of_int (uint sp0 - 64) : mword 64)]> m).
    assert (E86e : add_vec_int (mword_of_int 0x86e : mword 64) 2
                   = mword_of_int 0x870)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E86e) in "Hpc".
    assert (Hr1sp : r1 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hr1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
              r1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x870..0x878  the five spills ---- *)
    iApply (wp_sh_spill C pt CIDa Psh 0x870 0x872 64 56
              (mword_of_int 7 : mword 6) ra_idx M r1 sp0 Hst64 Hr1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_870 pt M Hl Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDb) "Hcg Hpc".
    set (N1 := uM_store8 M (uint sp0 - 64 + 56) (r1 !!! Regidx ra_idx)).
    assert (Hn1 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N1 !! k = M !! k) by (intros k Hk; apply st8_ne; lia).
    assert (Hd1 : forall k : Z, is_Some (M !! k) -> is_Some (N1 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact Hk).
    assert (Ht1 : sh_text_sub N1).
    { intros k b Hk. rewrite (Hn1 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hs1 : uv_stack pt N1 sp0 64)
      by exact (uv_stack_dom pt M N1 sp0 64 Hd1 Hst64).
    iApply (wp_sh_spill C pt CIDb Psh 0x872 0x874 64 48
              (mword_of_int 6 : mword 6) s0_idx N1 r1 sp0 Hs1 Hr1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_872 pt N1 Hl Ht1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDc) "Hcg Hpc".
    set (N2 := uM_store8 N1 (uint sp0 - 64 + 48) (r1 !!! Regidx s0_idx)).
    assert (Hn2 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N2 !! k = M !! k).
    { intros k Hk. unfold N2.
      rewrite (st8_ne N1 (uint sp0 - 64 + 48) (r1 !!! Regidx s0_idx) k
                 ltac:(lia)). exact (Hn1 k Hk). }
    assert (Hd2 : forall k : Z, is_Some (M !! k) -> is_Some (N2 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hd1 k Hk)).
    assert (Ht2 : sh_text_sub N2).
    { intros k b Hk. rewrite (Hn2 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hs2 : uv_stack pt N2 sp0 64)
      by exact (uv_stack_dom pt M N2 sp0 64 Hd2 Hst64).
    iApply (wp_sh_spill C pt CIDc Psh 0x874 0x876 64 40
              (mword_of_int 5 : mword 6) s1_idx N2 r1 sp0 Hs2 Hr1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_874 pt N2 Hl Ht2)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDd) "Hcg Hpc".
    set (N3 := uM_store8 N2 (uint sp0 - 64 + 40) (r1 !!! Regidx s1_idx)).
    assert (Hn3 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N3 !! k = M !! k).
    { intros k Hk. unfold N3.
      rewrite (st8_ne N2 (uint sp0 - 64 + 40) (r1 !!! Regidx s1_idx) k
                 ltac:(lia)). exact (Hn2 k Hk). }
    assert (Hd3 : forall k : Z, is_Some (M !! k) -> is_Some (N3 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hd2 k Hk)).
    assert (Ht3 : sh_text_sub N3).
    { intros k b Hk. rewrite (Hn3 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hs3 : uv_stack pt N3 sp0 64)
      by exact (uv_stack_dom pt M N3 sp0 64 Hd3 Hst64).
    iApply (wp_sh_spill C pt CIDd Psh 0x876 0x878 64 32
              (mword_of_int 4 : mword 6) s2_idx N3 r1 sp0 Hs3 Hr1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_876 pt N3 Hl Ht3)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDe) "Hcg Hpc".
    set (N4 := uM_store8 N3 (uint sp0 - 64 + 32) (r1 !!! Regidx s2_idx)).
    assert (Hn4 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N4 !! k = M !! k).
    { intros k Hk. unfold N4.
      rewrite (st8_ne N3 (uint sp0 - 64 + 32) (r1 !!! Regidx s2_idx) k
                 ltac:(lia)). exact (Hn3 k Hk). }
    assert (Hd4 : forall k : Z, is_Some (M !! k) -> is_Some (N4 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hd3 k Hk)).
    assert (Ht4 : sh_text_sub N4).
    { intros k b Hk. rewrite (Hn4 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hs4 : uv_stack pt N4 sp0 64)
      by exact (uv_stack_dom pt M N4 sp0 64 Hd4 Hst64).
    iApply (wp_sh_spill C pt CIDe Psh 0x878 0x87a 64 24
              (mword_of_int 3 : mword 6) s3_idx N4 r1 sp0 Hs4 Hr1sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              (ui_sh_878 pt N4 Hl Ht4)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDf) "Hcg Hpc".
    set (N5 := uM_store8 N4 (uint sp0 - 64 + 24) (r1 !!! Regidx s3_idx)).
    assert (Hn5 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N5 !! k = M !! k).
    { intros k Hk. unfold N5.
      rewrite (st8_ne N4 (uint sp0 - 64 + 24) (r1 !!! Regidx s3_idx) k
                 ltac:(lia)). exact (Hn4 k Hk). }
    assert (Hd5 : forall k : Z, is_Some (M !! k) -> is_Some (N5 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hd4 k Hk)).
    assert (Ht5 : sh_text_sub N5).
    { intros k b Hk. rewrite (Hn5 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hs5 : uv_stack pt N5 sp0 64)
      by exact (uv_stack_dom pt M N5 sp0 64 Hd5 Hst64).
    (* the five spill slots, read back *)
    assert (Bra : uM_bytes N5 (uint sp0 - 64 + 56) 8 (r1 !!! Regidx ra_idx)).
    { unfold N5, N4, N3, N2, N1. repeat (apply st8_bne; [ lia | ]).
      apply uM_store8_bytes. }
    assert (Bs0 : uM_bytes N5 (uint sp0 - 64 + 48) 8 (r1 !!! Regidx s0_idx)).
    { unfold N5, N4, N3, N2. repeat (apply st8_bne; [ lia | ]).
      apply uM_store8_bytes. }
    assert (Bs1 : uM_bytes N5 (uint sp0 - 64 + 40) 8 (r1 !!! Regidx s1_idx)).
    { unfold N5, N4, N3. repeat (apply st8_bne; [ lia | ]).
      apply uM_store8_bytes. }
    assert (Bs2 : uM_bytes N5 (uint sp0 - 64 + 32) 8 (r1 !!! Regidx s2_idx)).
    { unfold N5, N4. repeat (apply st8_bne; [ lia | ]). apply uM_store8_bytes. }
    assert (Bs3 : uM_bytes N5 (uint sp0 - 64 + 24) 8 (r1 !!! Regidx s3_idx)).
    { unfold N5. apply uM_store8_bytes. }
    (* a few more arithmetic and stack shims, needed from here on *)
    assert (Hmsub8 : forall a b : Z, a mod 16 = 0 -> b mod 8 = 0 ->
              (a - b) mod 8 = 0).
    { intros a b H1 H2.
      pose proof (Z.div_mod a 16 ltac:(lia)).
      pose proof (Z.div_mod b 8 ltac:(lia)).
      replace (a - b) with ((2 * (a / 16) - b / 8) * 8) by lia.
      apply Z.mod_mul. lia. }
    pose proof (us_al _ _ _ _ Hst) as Hal16.
    rewrite Z.rem_mod_nonneg in Hal16; [ | lia | lia ].
    assert (Hpsal : (uint sp0 - 56) mod 8 = 0)
      by (apply Hmsub8; [ exact Hal16 | reflexivity ]).
    assert (Hstrd : forall (Mx : gmap Z (bv 8)) (spx : mword 64) (n a k : Z),
              uv_stack pt Mx spx n -> uint spx - n <= a -> 0 <= k ->
              a + k <= uint spx -> uv_rd pt Mx a k).
    { intros Mx spx n a k HS Ha Hk Hak.
      pose proof (us_lo _ _ _ _ HS) as Hlo'.
      pose proof (us_canon _ _ _ _ HS) as Hc'.
      pose proof (us_bytes _ _ _ _ HS) as Hb'.
      change (2 ^ 38) with 274877906944 in Hc'.
      constructor.
      - lia.
      - lia.
      - change (2 ^ 38) with 274877906944. lia.
      - intros j Hj.
        destruct (stack_leaf pt Mx spx n (a + j) HS ltac:(lia)) as (w & Hw & _ & Hld).
        exists w. split; assumption.
      - intros j Hj.
        destruct (Hb' (a + j - (uint spx - n)) ltac:(lia)) as (b & Hbb).
        exists b. replace (a + j) with (uint spx - n + (a + j - (uint spx - n)))
          by lia. exact Hbb. }
    assert (Hcstr : forall (Mx : gmap Z (bv 8)) (a : Z) (l : list (bv 8)),
              ustr_at Mx a l ->
              (forall (j : nat) (b : bv 8), l !! j = Some b -> b <> ubyte0) ->
              ucstr Mx a (Z.of_nat (length l))).
    { intros Mx a l (Hb1 & Hb2) Hnz. constructor.
      - lia.
      - intros j Hj.
        destruct (lookup_lt_is_Some_2 l (Z.to_nat j) ltac:(lia)) as (b & Hbj).
        exists b. split.
        + replace (a + j) with (a + Z.of_nat (Z.to_nat j)) by lia.
          exact (Hb1 (Z.to_nat j) b Hbj).
        + exact (Hnz (Z.to_nat j) b Hbj).
      - exact Hb2. }
    destruct Hbufok as (Hstr0 & Hbnz).
    (* ---- 0x87a  c.addi4spn s0,sp,64 ---- *)
    assert (Hi4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                   : mword 64) = mword_of_int 64)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hs0w : (mword_of_int (uint sp0) : mword 64)
                   = add_vec (r1 !!! Regidx csp_rs1)
                       (sign_extend' 64
                          (caddi4spn_imm (mword_of_int 16 : mword 8)))).
    { rewrite Hr1sp Hi4 moi_add. f_equal; lia. }
    iApply (wp_uv_caddi4spn C pt Psh N5 r1 (mword_of_int 0x87a)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8)
              s0_idx (mword_of_int (uint sp0))
              (ui_sh_87a pt N5 Hl Ht5)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hs0w
              with "Hcg Hpc").
    iIntros (CIDg) "Hcg Hpc".
    set (r2 := <[Regidx s0_idx
                 := regval_into_reg (mword_of_int (uint sp0) : mword 64)]> r1).
    assert (E87a : add_vec_int (mword_of_int 0x87a : mword 64) 2
                   = mword_of_int 0x87c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E87a) in "Hpc".
    assert (Hr2s0 : r2 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by exact (upd_eq r1 (Regidx s0_idx) _).
    assert (Hr2a0 : r2 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
    { rewrite (upd_ne r1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hr1 a0_idx ltac:(vm_compute; discriminate)). exact Hs. }
    assert (Hr2sp : r2 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr1sp. }
    (* ---- 0x87c  sd a0,-56(s0)   (the local `char *s') ---- *)
    destruct (uv_slot8_facts (uint sp0 - 56) (mword_of_int (uint sp0 - 56))
                ltac:(lia) Hpsal ltac:(change (2 ^ 38) with 274877906944; lia)
                eq_refl) as (Hupsa & Hcnpsa & Hpgpsa & Halpsa).
    destruct (stack_leaf pt N5 sp0 64 (uint sp0 - 56) Hs5 ltac:(lia))
      as (wps & Hwps & Hokps & _).
    assert (Hbps : forall j : nat, (j < 8)%nat ->
              exists bb : bv 8,
                N5 !! (uint (mword_of_int (uint sp0 - 56) : mword 64)
                       + Z.of_nat j) = Some bb).
    { intros j Hj. rewrite Hupsa.
      destruct (us_bytes _ _ _ _ Hs5 (uint sp0 - 56 + Z.of_nat j - (uint sp0 - 64))
                  ltac:(lia)) as (b & Hb).
      exists b. replace (uint sp0 - 56 + Z.of_nat j)
        with (uint sp0 - 64 + (uint sp0 - 56 + Z.of_nat j - (uint sp0 - 64)))
        by lia. exact Hb. }
    assert (Hvaps : (mword_of_int (uint sp0 - 56) : mword 64)
                    = add_vec (r2 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 4040 : mword 12))).
    { rewrite Hr2s0.
      assert (Hc : (sign_extend' 64 (mword_of_int 4040 : mword 12) : mword 64)
                   = mword_of_int (-56))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_sd C pt Psh N5 r2 (mword_of_int 0x87c)
              (mword_of_int 4040 : mword 12) s0_idx a0_idx
              wps (mword_of_int (uint sp0 - 56)) (mword_of_int s0)
              (ui_sh_87c pt N5 Hl Ht5)
              Hvaps (eq_sym Hr2a0) Hwps Hokps Hcnpsa Hpgpsa Halpsa Hbps
              with "Hcg Hpc").
    iIntros (CIDh) "Hcg Hpc".
    iEval (rewrite Hupsa) in "Hcg".
    set (N6 := uM_store N5 (uint sp0 - 56) 8 (mword_of_int s0 : mword 64)).
    assert (E87c : add_vec_int (mword_of_int 0x87c : mword 64) 4
                   = mword_of_int 0x880)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E87c) in "Hpc".
    assert (Hn6 : forall k : Z, (k < uint sp0 - 64 \/ uint sp0 <= k) ->
              N6 !! k = M !! k).
    { intros k Hk. unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64) k
                 ltac:(lia)). exact (Hn5 k Hk). }
    assert (Hd6 : forall k : Z, is_Some (M !! k) -> is_Some (N6 !! k))
      by (intros k Hk; apply uM_store8_is_Some; exact (Hd5 k Hk)).
    assert (Ht6 : sh_text_sub N6).
    { intros k b Hk. rewrite (Hn6 k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Htext k b Hk). }
    assert (Hi6 : sh_img_sub N6).
    { split; [ exact Ht6 | ].
      intros k b Hk. rewrite (Hn6 k ltac:(pose proof (sh_data_key_lt' k b Hk); lia)).
      exact (Hdata k b Hk). }
    assert (Hs6 : uv_stack pt N6 sp0 480)
      by exact (uv_stack_dom pt M N6 sp0 480 Hd6 Hst).
    destruct (uv_stack_split pt N6 sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hs6) as (Hs6a & Hs6b).
    rewrite (uv_stack_sp_moi pt N6 sp0 64 Hs6a) in Hs6b.
    assert (Hstr6 : ustr_at N6 s0 bs).
    { destruct Hstr0 as (Hb1 & Hb2). split.
      - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj).
        rewrite (Hn6 (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      - rewrite (Hn6 (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2. }
    assert (Hrd6 : uv_rd pt N6 s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct Hrdbuf; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ Hrdbuf j Hj) as (b & Hb).
      exists b. rewrite (Hn6 (s0 + j) ltac:(lia)). exact Hb. }
    assert (Hwr6 : uv_wr pt N6 s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct Hwrbuf; assumption).
      intros j Hj. destruct (uwr_bytes _ _ _ _ Hwrbuf j Hj) as (b & Hb).
      exists b. rewrite (Hn6 (s0 + j) ltac:(lia)). exact Hb. }
    (* ---- 0x880  c.mv s1,a0 ---- *)
    assert (Hmv1 : (mword_of_int s0 : mword 64)
                   = add_vec zero_reg (r2 !!! Regidx a0_idx))
      by (rewrite Hr2a0 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh N6 r2 (mword_of_int 0x880)
              s1_idx a0_idx (mword_of_int s0)
              (ui_sh_880 pt N6 Hl Ht6)
              ltac:(vm_compute; discriminate) Hmv1 with "Hcg Hpc").
    iIntros (CIDi) "Hcg Hpc".
    set (r3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int s0 : mword 64)]> r2).
    assert (E880 : add_vec_int (mword_of_int 0x880 : mword 64) 2
                   = mword_of_int 0x882)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E880) in "Hpc".
    (* ---- 0x882  jal ra,0xa30 <strlen> ---- *)
    assert (Htgt1 : (mword_of_int 0xa30 : mword 64)
                    = add_vec (mword_of_int 0x882)
                        (sign_extend' 64 (mword_of_int 430 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk1 : (mword_of_int 0x886 : mword 64)
                    = add_vec_int (mword_of_int 0x882 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh N6 r3 (mword_of_int 0x882)
              (mword_of_int 430 : mword 21) ra_idx
              (mword_of_int 0xa30) (mword_of_int 0x886)
              (ui_sh_882 pt N6 Hl Ht6)
              ltac:(vm_compute; discriminate) Htgt1 Hlnk1
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDj) "Hcg Hpc".
    set (r4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x886 : mword 64)]> r3).
    iEval (rewrite <- Hsstr) in "Hpc".
    assert (Hr4ra : r4 !!! Regidx ra_idx = (mword_of_int 0x886 : mword 64))
      by exact (upd_eq r3 (Regidx ra_idx) _).
    assert (Hr4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx csp_rs1 -> r4 !!! Regidx r = m !!! Regidx r).
    { intros r Nra Ns1 Ns0 Nsp.
      rewrite (upd_ne r3 (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx r) _ Ns1).
      rewrite (upd_ne r1 (Regidx s0_idx) (Regidx r) _ Ns0).
      exact (Hr1 r Nsp). }
    assert (Hr4sp : r4 !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r3 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr2sp. }
    assert (Hr4s0 : r4 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (upd_ne r3 (Regidx ra_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)). exact Hr2s0. }
    assert (Hr4s1 : r4 !!! Regidx s1_idx = (mword_of_int s0 : mword 64)).
    { rewrite (upd_ne r3 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx s1_idx) _). }
    assert (Hr4a0 : r4 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
    { rewrite (upd_ne r3 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Hr2a0. }
    destruct (uv_stack_split pt N6 (mword_of_int (uint sp0 - 64)) 416 16 400
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hs6b)
      as (Hs6c & _).
    iApply (wp_sh_strlen C pt gin gbrk hbase hlen Q CIDj N6 r4
              (mword_of_int (uint sp0 - 64)) s0 (Z.of_nat (length bs))
              Hlay Ht6 Hr4sp Hs6c Hr4a0 (Hcstr N6 s0 bs Hstr6 Hbnz) Hrd6
              ltac:(lia)
              ltac:(right; rewrite Hubot; lia)
              ltac:(unfold sh_frame_ok; rewrite Hubot; lia)
              ltac:(rewrite Hr4ra; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CIDk mS MS) "%Hcs1 %Ha0S %HonlyS Hcg Hpc".
    iEval (rewrite Hr4ra) in "Hpc".
    (* what survived strlen *)
    destruct HonlyS as (HdS & HeS).
    rewrite Hubot in HeS.
    assert (HnS : forall k : Z, k < uint sp0 - 80 -> MS !! k = N6 !! k)
      by (intros k Hk; apply HeS; left; lia).
    assert (HtS : sh_text_sub MS).
    { intros k b Hk. rewrite (HnS k ltac:(pose proof (sh_bytes_key_lt k b Hk); lia)).
      exact (Ht6 k b Hk). }
    assert (HiS : sh_img_sub MS).
    { split; [ exact HtS | ].
      intros k b Hk. rewrite (HnS k ltac:(pose proof (sh_data_key_lt' k b Hk); lia)).
      exact (proj2 Hi6 k b Hk). }
    assert (HstS : uv_stack pt MS sp0 480)
      by exact (uv_stack_dom pt N6 MS sp0 480 HdS Hs6).
    destruct (uv_stack_split pt MS sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) HstS) as (HstS64 & HstS416).
    rewrite (uv_stack_sp_moi pt MS sp0 64 HstS64) in HstS416.
    assert (HstrS : ustr_at MS s0 bs).
    { destruct Hstr6 as (Hb1 & Hb2). split.
      - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj).
        rewrite (HnS (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      - rewrite (HnS (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2. }
    assert (HrdS : uv_rd pt MS s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct Hrd6; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ Hrd6 j Hj) as (b & Hb).
      exists b. rewrite (HnS (s0 + j) ltac:(lia)). exact Hb. }
    assert (HwrS : uv_wr pt MS s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct Hwr6; assumption).
      intros j Hj. destruct (uwr_bytes _ _ _ _ Hwr6 j Hj) as (b & Hb).
      exists b. rewrite (HnS (s0 + j) ltac:(lia)). exact Hb. }
    assert (HcellS : uM_bytes MS (uint sp0 - 56) 8 (mword_of_int s0 : mword 64)).
    { intros j Hj. rewrite (HeS (uint sp0 - 56 + Z.of_nat j) ltac:(right; lia)).
      unfold N6. exact (uM_store_bytes N5 (uint sp0 - 56) 8 _ j Hj). }
    assert (HfreeS : sh_zeroed MS SH_FREEP 0 8).
    { intros j Hj. unfold SH_FREEP, SH_DATA_PG in *.
      rewrite (HnS (8208 + j) ltac:(lia)). rewrite (Hn6 (8208 + j) ltac:(lia)).
      exact (Hfreep0 j Hj). }
    assert (HbaseS : sh_zeroed MS (SH_BASE + 8) 0 8).
    { intros j Hj. unfold SH_BASE, SH_DATA_PG in *.
      rewrite (HnS (8328 + 8 + j) ltac:(lia)).
      rewrite (Hn6 (8328 + 8 + j) ltac:(lia)). exact (Hbasesz0 j Hj). }
    assert (HbsswS : uv_wr pt MS SH_FREEP 0x88).
    { constructor; try (destruct Hbssw; assumption).
      intros j Hj. destruct (uwr_bytes _ _ _ _ Hbssw j Hj) as (b & Hb).
      exists b. unfold SH_FREEP, SH_DATA_PG in *.
      rewrite (HnS (8208 + j) ltac:(lia)). rewrite (Hn6 (8208 + j) ltac:(lia)).
      exact Hb. }
    assert (BraS : uM_bytes MS (uint sp0 - 64 + 56) 8 (r1 !!! Regidx ra_idx)).
    { intros j Hj.
      rewrite (HeS (uint sp0 - 64 + 56 + Z.of_nat j) ltac:(right; lia)).
      unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64)
                 (uint sp0 - 64 + 56 + Z.of_nat j) ltac:(lia)).
      exact (Bra j Hj). }
    assert (Bs0S : uM_bytes MS (uint sp0 - 64 + 48) 8 (r1 !!! Regidx s0_idx)).
    { intros j Hj.
      rewrite (HeS (uint sp0 - 64 + 48 + Z.of_nat j) ltac:(right; lia)).
      unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64)
                 (uint sp0 - 64 + 48 + Z.of_nat j) ltac:(lia)).
      exact (Bs0 j Hj). }
    assert (Bs1S : uM_bytes MS (uint sp0 - 64 + 40) 8 (r1 !!! Regidx s1_idx)).
    { intros j Hj.
      rewrite (HeS (uint sp0 - 64 + 40 + Z.of_nat j) ltac:(right; lia)).
      unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64)
                 (uint sp0 - 64 + 40 + Z.of_nat j) ltac:(lia)).
      exact (Bs1 j Hj). }
    assert (Bs2S : uM_bytes MS (uint sp0 - 64 + 32) 8 (r1 !!! Regidx s2_idx)).
    { intros j Hj.
      rewrite (HeS (uint sp0 - 64 + 32 + Z.of_nat j) ltac:(right; lia)).
      unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64)
                 (uint sp0 - 64 + 32 + Z.of_nat j) ltac:(lia)).
      exact (Bs2 j Hj). }
    assert (Bs3S : uM_bytes MS (uint sp0 - 64 + 24) 8 (r1 !!! Regidx s3_idx)).
    { intros j Hj.
      rewrite (HeS (uint sp0 - 64 + 24 + Z.of_nat j) ltac:(right; lia)).
      unfold N6.
      rewrite (st8_ne N5 (uint sp0 - 56) (mword_of_int s0 : mword 64)
                 (uint sp0 - 64 + 24 + Z.of_nat j) ltac:(lia)).
      exact (Bs3 j Hj). }
    (* the callee-saved registers strlen handed back *)
    assert (HmSsp : mS !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hr4sp).
    assert (HmSs0 : mS !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcs1 s0_idx ltac:(vm_compute; reflexivity)); exact Hr4s0).
    assert (HmSs1 : mS !!! Regidx s1_idx = (mword_of_int s0 : mword 64))
      by (rewrite (Hcs1 s1_idx ltac:(vm_compute; reflexivity)); exact Hr4s1).
    (* ---- 0x886  c.slli a0,a0,0x20 ---- *)
    assert (Hshl : (mword_of_int (Z.of_nat (length bs) * 2 ^ 32) : mword 64)
                   = shift_bits_left (mS !!! Regidx a0_idx)
                       (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0)).
    { rewrite Ha0S. symmetry. exact (moi_shl (Z.of_nat (length bs)) 32 ltac:(lia)). }
    iApply (wp_uv_cslli C pt Psh MS mS (mword_of_int 0x886)
              (mword_of_int 32 : mword 6) a0_idx
              (mword_of_int (Z.of_nat (length bs) * 2 ^ 32))
              (ui_sh_886 pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Hshl with "Hcg Hpc").
    iIntros (CIDl) "Hcg Hpc".
    set (r5 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (length bs) * 2 ^ 32)
                       : mword 64)]> mS).
    assert (E886 : add_vec_int (mword_of_int 0x886 : mword 64) 2
                   = mword_of_int 0x888)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E886) in "Hpc".
    assert (Hr5a0 : r5 !!! Regidx a0_idx
                    = (mword_of_int (Z.of_nat (length bs) * 2 ^ 32) : mword 64))
      by exact (upd_eq mS (Regidx a0_idx) _).
    (* ---- 0x888  c.srli a0,a0,0x20 ---- *)
    assert (Hshr : (mword_of_int (Z.of_nat (length bs)) : mword 64)
                   = shift_bits_right (r5 !!! Regidx a0_idx)
                       (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0)).
    { rewrite Hr5a0.
      rewrite (moi_shr (Z.of_nat (length bs) * 2 ^ 32) 32 ltac:(lia)
                 ltac:(change (2 ^ 32) with 4294967296; unfold Z64; lia)).
      f_equal. rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ]. }
    iApply (wp_uv_csrli C pt Psh MS r5 (mword_of_int 0x888)
              (mword_of_int 32 : mword 6) (mword_of_int 2 : mword 3) a0_idx
              (mword_of_int (Z.of_nat (length bs)))
              (ui_sh_888 pt MS Hl HtS)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hshr
              with "Hcg Hpc").
    iIntros (CIDm) "Hcg Hpc".
    set (r6 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (length bs)) : mword 64)]> r5).
    assert (E888 : add_vec_int (mword_of_int 0x888 : mword 64) 2
                   = mword_of_int 0x88a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E888) in "Hpc".
    assert (Hr6 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
              r6 !!! Regidx r = mS !!! Regidx r).
    { intros r Hr. rewrite (upd_ne r5 (Regidx a0_idx) (Regidx r) _ Hr).
      exact (upd_ne mS (Regidx a0_idx) (Regidx r) _ Hr). }
    assert (Hr6a0 : r6 !!! Regidx a0_idx
                    = (mword_of_int (Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq r5 (Regidx a0_idx) _).
    assert (Hr6s1 : r6 !!! Regidx s1_idx = (mword_of_int s0 : mword 64))
      by (rewrite (Hr6 s1_idx ltac:(vm_compute; discriminate)); exact HmSs1).
    (* ---- 0x88a  c.add s1,s1,a0   (s1 := es) ---- *)
    assert (Hadd1 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                    = add_vec (r6 !!! Regidx s1_idx) (r6 !!! Regidx a0_idx))
      by (rewrite Hr6s1 Hr6a0 moi_add; reflexivity).
    iApply (wp_uv_cadd C pt Psh MS r6 (mword_of_int 0x88a)
              s1_idx a0_idx (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_88a pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Hadd1 with "Hcg Hpc").
    iIntros (CIDn) "Hcg Hpc".
    set (r7 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (length bs))
                       : mword 64)]> r6).
    assert (E88a : add_vec_int (mword_of_int 0x88a : mword 64) 2
                   = mword_of_int 0x88c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E88a) in "Hpc".
    assert (Hr7s0 : r7 !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (upd_ne r6 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hr6 s0_idx ltac:(vm_compute; discriminate)). exact HmSs0. }
    (* ---- 0x88c  addi s2,s0,-56   (s2 := &s) ---- *)
    assert (Hadd2 : (mword_of_int (uint sp0 - 56) : mword 64)
                    = add_vec (r7 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 4040 : mword 12))).
    { rewrite Hr7s0.
      assert (Hc : (sign_extend' 64 (mword_of_int 4040 : mword 12) : mword 64)
                   = mword_of_int (-56))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh MS r7 (mword_of_int 0x88c)
              (mword_of_int 4040 : mword 12) s0_idx s2_idx
              (mword_of_int (uint sp0 - 56))
              (ui_sh_88c pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Hadd2 with "Hcg Hpc").
    iIntros (CIDo) "Hcg Hpc".
    set (r8 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (uint sp0 - 56) : mword 64)]> r7).
    assert (E88c : add_vec_int (mword_of_int 0x88c : mword 64) 4
                   = mword_of_int 0x890)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E88c) in "Hpc".
    assert (Hr8s1 : r8 !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne r7 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx s1_idx) _). }
    (* ---- 0x890  c.mv a1,s1 ---- *)
    assert (Hmv2 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                   = add_vec zero_reg (r8 !!! Regidx s1_idx))
      by (rewrite Hr8s1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MS r8 (mword_of_int 0x890)
              a1_idx s1_idx (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_890 pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Hmv2 with "Hcg Hpc").
    iIntros (CIDp2) "Hcg Hpc".
    set (r9 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (length bs))
                       : mword 64)]> r8).
    assert (E890 : add_vec_int (mword_of_int 0x890 : mword 64) 2
                   = mword_of_int 0x892)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E890) in "Hpc".
    assert (Hr9s2 : r9 !!! Regidx s2_idx
                    = (mword_of_int (uint sp0 - 56) : mword 64)).
    { rewrite (upd_ne r8 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx s2_idx) _). }
    (* ---- 0x892  c.mv a0,s2 ---- *)
    assert (Hmv3 : (mword_of_int (uint sp0 - 56) : mword 64)
                   = add_vec zero_reg (r9 !!! Regidx s2_idx))
      by (rewrite Hr9s2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MS r9 (mword_of_int 0x892)
              a0_idx s2_idx (mword_of_int (uint sp0 - 56))
              (ui_sh_892 pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Hmv3 with "Hcg Hpc").
    iIntros (CIDq) "Hcg Hpc".
    set (r10 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int (uint sp0 - 56)
                                      : mword 64)]> r9).
    assert (E892 : add_vec_int (mword_of_int 0x892 : mword 64) 2
                   = mword_of_int 0x894)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E892) in "Hpc".
    (* ---- 0x894  jal ra,0x6e2 <parseline> ---- *)
    assert (Htgt2 : (mword_of_int 0x6e2 : mword 64)
                    = add_vec (mword_of_int 0x894)
                        (sign_extend' 64 (mword_of_int 2096718 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk2 : (mword_of_int 0x898 : mword 64)
                    = add_vec_int (mword_of_int 0x894 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MS r10 (mword_of_int 0x894)
              (mword_of_int 2096718 : mword 21) ra_idx
              (mword_of_int 0x6e2) (mword_of_int 0x898)
              (ui_sh_894 pt MS Hl HtS)
              ltac:(vm_compute; discriminate) Htgt2 Hlnk2
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDr) "Hcg Hpc".
    set (r11 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x898 : mword 64)]> r10).
    iEval (rewrite <- Hspl) in "Hpc".
    assert (Hr11ra : r11 !!! Regidx ra_idx = (mword_of_int 0x898 : mword 64))
      by exact (upd_eq r10 (Regidx ra_idx) _).
    assert (Hr11a0 : r11 !!! Regidx a0_idx
                     = (mword_of_int (uint sp0 - 56) : mword 64)).
    { rewrite (upd_ne r10 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r9 (Regidx a0_idx) _). }
    assert (Hr11a1 : r11 !!! Regidx a1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne r10 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r8 (Regidx a1_idx) _). }
    assert (Hr11q : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a1_idx ->
              Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s1_idx ->
              r11 !!! Regidx r = mS !!! Regidx r).
    { intros r Nra Na0 Na1 Ns2 Ns1.
      rewrite (upd_ne r10 (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne r9 (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne r8 (Regidx a1_idx) (Regidx r) _ Na1).
      rewrite (upd_ne r7 (Regidx s2_idx) (Regidx r) _ Ns2).
      rewrite (upd_ne r6 (Regidx s1_idx) (Regidx r) _ Ns1).
      rewrite (upd_ne r5 (Regidx a0_idx) (Regidx r) _ Na0).
      exact (upd_ne mS (Regidx a0_idx) (Regidx r) _ Na0). }
    assert (Hr11sp : r11 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hr11q csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HmSsp. }
    assert (Hr11s0 : r11 !!! Regidx s0_idx
                     = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (Hr11q s0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HmSs0. }
    assert (Hr11s1 : r11 !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne r10 (Regidx ra_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx a0_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx a1_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx s1_idx) _). }
    assert (Hr11s2 : r11 !!! Regidx s2_idx
                     = (mword_of_int (uint sp0 - 56) : mword 64)).
    { rewrite (upd_ne r10 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx s2_idx) _). }
    assert (HcellS' : uM_bytes MS (uint sp0 - 56) 8
                        (mword_of_int (s0 + Z.of_nat 0) : mword 64)).
    { replace (s0 + Z.of_nat 0) with s0 by (cbn [Z.of_nat]; lia). exact HcellS. }
    assert (Hcell0 : sh_ptr_cell pt MS (uint sp0 - 56) (s0 + Z.of_nat 0)
                       (mword_of_int (uint sp0 - 64))).
    { split_and!.
      - exact HcellS'.
      - exact (Hstrd MS sp0 64 (uint sp0 - 56) 8 HstS64 ltac:(lia) ltac:(lia)
                 ltac:(lia)).
      - exact (stack_wr pt MS sp0 64 (uint sp0 - 56) 8 HstS64 ltac:(lia)
                 ltac:(lia) ltac:(lia)).
      - exact Hpsal.
      - rewrite Hubot. lia.
      - change (2 ^ 38) with 274877906944. lia. }
    (* ---- parseline(&s, es) ---- *)
    iApply (Hparseline CIDr MS r11 (mword_of_int (uint sp0 - 64))
              (uint sp0 - 56) s0 bs 0%nat toks
              ltac:(unfold sh_parse_pre; rewrite Hubot; split_and!;
                    [ exact Hlay | exact HiS
                    | exact (sh_img_tables MS (proj2 HiS))
                    | split; [ exact HstrS | exact Hbnz ]
                    | exact Hnosym | exact HrdS | exact HwrS | lia | lia
                    | unfold sh_frame_ok; lia | lia ])
              Hr11sp HstS416 Hr11a0 Hr11a1 Hcell0
              ltac:(unfold sh_buf_clear, sh_disj, SH_FREEP, SH_BASE, SH_DATA_PG;
                    split_and!; lia)
              ltac:(lia) Htoks ltac:(lia) HfreeS HbaseS HbsswS
              ltac:(rewrite Hr11ra; vm_compute; reflexivity)
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CIDs mP MP cmd) "%Hcs2 %Ha0P %Hcmdeq %HtypeP %HargvP %HpsP %HrdP
                              %HonlyP Hbrk Hcg Hpc".
    iEval (rewrite Hr11ra) in "Hpc".
    rewrite Hubot in HonlyP.
    assert (Hs0f : 8216 <= s0) by lia.
    (* --- what survived parseline --- *)
    assert (HwinPlo : forall w : Z * Z,
              w ∈ [sh_win hbase 65536; sh_win SH_FREEP 8; sh_win SH_BASE 16;
                   sh_win (uint sp0 - 56) 8; sh_win (uint sp0 - 64 - 416) 416] ->
              8208 <= fst w).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst SH_FREEP SH_DATA_PG]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst SH_BASE SH_DATA_PG]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HwinPhi : forall w : Z * Z,
              w ∈ [sh_win hbase 65536; sh_win SH_FREEP 8; sh_win SH_BASE 16;
                   sh_win (uint sp0 - 56) 8; sh_win (uint sp0 - 64 - 416) 416] ->
              fst w + snd w <= uint sp0 - 48).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd SH_FREEP SH_DATA_PG]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd SH_BASE SH_DATA_PG]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HbufP : forall k : Z, s0 <= k < s0 + Z.of_nat (length bs) + 1 ->
              MP !! k = MS !! k).
    { intros k Hk. apply (uM_only_in_out MS MP _ k HonlyP).
      intros w Hw Hin.
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd SH_FREEP SH_DATA_PG] in Hin; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd SH_BASE SH_DATA_PG] in Hin; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; lia | ].
      rewrite elem_of_nil in Hw. exact Hw. }
    assert (HiP : sh_img_sub MP) by exact (keep_img MS MP _ HonlyP HwinPlo HiS).
    assert (HtP : sh_text_sub MP) by exact (sh_img_text MP HiP).
    assert (HdP : forall k : Z, is_Some (MS !! k) -> is_Some (MP !! k))
      by exact (keep_dom MS MP _ HonlyP).
    assert (HstP : uv_stack pt MP sp0 480)
      by exact (uv_stack_dom pt MS MP sp0 480 HdP HstS).
    destruct (uv_stack_split pt MP sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) HstP) as (HstP64 & HstP416).
    rewrite (uv_stack_sp_moi pt MP sp0 64 HstP64) in HstP416.
    assert (HstrP : ustr_at MP s0 bs).
    { destruct HstrS as (Hb1 & Hb2). split.
      - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj).
        rewrite (HbufP (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      - rewrite (HbufP (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2. }
    assert (HrdP2 : uv_rd pt MP s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct HrdS; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ HrdS j Hj) as (b & Hb).
      exists b. rewrite (HbufP (s0 + j) ltac:(lia)). exact Hb. }
    assert (HwrP2 : uv_wr pt MP s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct HwrS; assumption).
      intros j Hj. destruct (uwr_bytes _ _ _ _ HwrS j Hj) as (b & Hb).
      exists b. rewrite (HbufP (s0 + j) ltac:(lia)). exact Hb. }
    assert (BraP : uM_bytes MP (uint sp0 - 64 + 56) 8 (r1 !!! Regidx ra_idx))
      by exact (keep_hi MS MP _ (uint sp0 - 48) (uint sp0 - 64 + 56) _ HonlyP HwinPhi
                  ltac:(lia) BraS).
    assert (Bs0P : uM_bytes MP (uint sp0 - 64 + 48) 8 (r1 !!! Regidx s0_idx))
      by exact (keep_hi MS MP _ (uint sp0 - 48) (uint sp0 - 64 + 48) _ HonlyP HwinPhi
                  ltac:(lia) Bs0S).
    assert (Bs1P : uM_bytes MP (uint sp0 - 64 + 40) 8 (r1 !!! Regidx s1_idx))
      by exact (keep_hi MS MP _ (uint sp0 - 48) (uint sp0 - 64 + 40) _ HonlyP HwinPhi
                  ltac:(lia) Bs1S).
    assert (Bs2P : uM_bytes MP (uint sp0 - 64 + 32) 8 (r1 !!! Regidx s2_idx))
      by exact (keep_hi MS MP _ (uint sp0 - 48) (uint sp0 - 64 + 32) _ HonlyP HwinPhi
                  ltac:(lia) Bs2S).
    assert (Bs3P : uM_bytes MP (uint sp0 - 64 + 24) 8 (r1 !!! Regidx s3_idx))
      by exact (keep_hi MS MP _ (uint sp0 - 48) (uint sp0 - 64 + 24) _ HonlyP HwinPhi
                  ltac:(lia) Bs3S).
    assert (HmPsp : mP !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hr11sp).
    assert (HmPs0 : mP !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcs2 s0_idx ltac:(vm_compute; reflexivity)); exact Hr11s0).
    assert (HmPs1 : mP !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcs2 s1_idx ltac:(vm_compute; reflexivity)); exact Hr11s1).
    assert (HmPs2 : mP !!! Regidx s2_idx
                    = (mword_of_int (uint sp0 - 56) : mword 64))
      by (rewrite (Hcs2 s2_idx ltac:(vm_compute; reflexivity)); exact Hr11s2).
    (* ---- 0x898  c.mv s3,a0   (s3 := cmd) ---- *)
    assert (Hmv4 : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (mP !!! Regidx a0_idx))
      by (rewrite Ha0P moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MP mP (mword_of_int 0x898)
              s3_idx a0_idx (mword_of_int cmd)
              (ui_sh_898 pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Hmv4 with "Hcg Hpc").
    iIntros (CIDt) "Hcg Hpc".
    set (r12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int cmd : mword 64)]> mP).
    assert (E898 : add_vec_int (mword_of_int 0x898 : mword 64) 2
                   = mword_of_int 0x89a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E898) in "Hpc".
    (* ---- 0x89a  auipc a2,0x1 ---- *)
    assert (Hau : (mword_of_int 6298 : mword 64)
                  = add_vec (mword_of_int 0x89a)
                      (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_auipc C pt Psh MP r12 (mword_of_int 0x89a)
              (mword_of_int 1 : mword 20) a2_idx (mword_of_int 6298)
              (ui_sh_89a pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Hau with "Hcg Hpc").
    iIntros (CIDu) "Hcg Hpc".
    set (r13 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 6298 : mword 64)]> r12).
    assert (E89a : add_vec_int (mword_of_int 0x89a : mword 64) 4
                   = mword_of_int 0x89e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E89a) in "Hpc".
    assert (Hr13a2 : r13 !!! Regidx a2_idx = (mword_of_int 6298 : mword 64))
      by exact (upd_eq r12 (Regidx a2_idx) _).
    (* ---- 0x89e  addi a2,a2,-1554   (a2 := the "" literal at 0x1288) ---- *)
    assert (Haddl : (mword_of_int 4744 : mword 64)
                    = add_vec (r13 !!! Regidx a2_idx)
                        (sign_extend' 64 (mword_of_int 2542 : mword 12))).
    { rewrite Hr13a2.
      assert (Hc : (sign_extend' 64 (mword_of_int 2542 : mword 12) : mword 64)
                   = mword_of_int (-1554))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_addi C pt Psh MP r13 (mword_of_int 0x89e)
              (mword_of_int 2542 : mword 12) a2_idx a2_idx (mword_of_int 4744)
              (ui_sh_89e pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Haddl with "Hcg Hpc").
    iIntros (CIDv) "Hcg Hpc".
    set (r14 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 4744 : mword 64)]> r13).
    assert (E89e : add_vec_int (mword_of_int 0x89e : mword 64) 4
                   = mword_of_int 0x8a2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E89e) in "Hpc".
    assert (Hr14s1 : r14 !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne r13 (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r12 (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mP (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact HmPs1. }
    (* ---- 0x8a2  c.mv a1,s1 ---- *)
    assert (Hmv5 : (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                   = add_vec zero_reg (r14 !!! Regidx s1_idx))
      by (rewrite Hr14s1 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MP r14 (mword_of_int 0x8a2)
              a1_idx s1_idx (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_8a2 pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Hmv5 with "Hcg Hpc").
    iIntros (CIDw) "Hcg Hpc".
    set (r15 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (length bs))
                        : mword 64)]> r14).
    assert (E8a2 : add_vec_int (mword_of_int 0x8a2 : mword 64) 2
                   = mword_of_int 0x8a4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8a2) in "Hpc".
    assert (Hr15s2 : r15 !!! Regidx s2_idx
                     = (mword_of_int (uint sp0 - 56) : mword 64)).
    { rewrite (upd_ne r14 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r13 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r12 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mP (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). exact HmPs2. }
    (* ---- 0x8a4  c.mv a0,s2 ---- *)
    assert (Hmv6 : (mword_of_int (uint sp0 - 56) : mword 64)
                   = add_vec zero_reg (r15 !!! Regidx s2_idx))
      by (rewrite Hr15s2 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MP r15 (mword_of_int 0x8a4)
              a0_idx s2_idx (mword_of_int (uint sp0 - 56))
              (ui_sh_8a4 pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Hmv6 with "Hcg Hpc").
    iIntros (CIDx) "Hcg Hpc".
    set (r16 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int (uint sp0 - 56)
                                      : mword 64)]> r15).
    assert (E8a4 : add_vec_int (mword_of_int 0x8a4 : mword 64) 2
                   = mword_of_int 0x8a6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8a4) in "Hpc".
    (* ---- 0x8a6  jal ra,0x448 <peek> ---- *)
    assert (Htgt3 : (mword_of_int 0x448 : mword 64)
                    = add_vec (mword_of_int 0x8a6)
                        (sign_extend' 64 (mword_of_int 2096034 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk3 : (mword_of_int 0x8aa : mword 64)
                    = add_vec_int (mword_of_int 0x8a6 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MP r16 (mword_of_int 0x8a6)
              (mword_of_int 2096034 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x8aa)
              (ui_sh_8a6 pt MP Hl HtP)
              ltac:(vm_compute; discriminate) Htgt3 Hlnk3
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDy) "Hcg Hpc".
    set (r17 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8aa : mword 64)]> r16).
    iEval (rewrite <- Hspk) in "Hpc".
    assert (Hr17ra : r17 !!! Regidx ra_idx = (mword_of_int 0x8aa : mword 64))
      by exact (upd_eq r16 (Regidx ra_idx) _).
    assert (Hr17a0 : r17 !!! Regidx a0_idx
                     = (mword_of_int (uint sp0 - 56) : mword 64)).
    { rewrite (upd_ne r16 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r15 (Regidx a0_idx) _). }
    assert (Hr17a1 : r17 !!! Regidx a1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne r16 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r15 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r14 (Regidx a1_idx) _). }
    assert (Hr17a2 : r17 !!! Regidx a2_idx = (mword_of_int 4744 : mword 64)).
    { rewrite (upd_ne r16 (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r15 (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r14 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r13 (Regidx a2_idx) _). }
    assert (Hr17w : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a1_idx ->
              Regidx r <> Regidx a2_idx -> Regidx r <> Regidx s3_idx ->
              r17 !!! Regidx r = mP !!! Regidx r).
    { intros r Nra Na0 Na1 Na2 Ns3.
      rewrite (upd_ne r16 (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne r15 (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne r14 (Regidx a1_idx) (Regidx r) _ Na1).
      rewrite (upd_ne r13 (Regidx a2_idx) (Regidx r) _ Na2).
      rewrite (upd_ne r12 (Regidx a2_idx) (Regidx r) _ Na2).
      exact (upd_ne mP (Regidx s3_idx) (Regidx r) _ Ns3). }
    assert (Hr17sp : r17 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hr17w csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HmPsp. }
    assert (Hr17s0 : r17 !!! Regidx s0_idx
                     = (mword_of_int (uint sp0) : mword 64)).
    { rewrite (Hr17w s0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HmPs0. }
    assert (Hr17s1 : r17 !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (Hr17w s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HmPs1. }
    assert (Hr17s3 : r17 !!! Regidx s3_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne r16 (Regidx ra_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r15 (Regidx a0_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r14 (Regidx a1_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r13 (Regidx a2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r12 (Regidx a2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mP (Regidx s3_idx) _). }
    (* ---- peek(&s, es, "")  --  the "" literal is one NUL at 0x1288 ---- *)
    destruct (uv_stack_split pt MP (mword_of_int (uint sp0 - 64)) 416 80 336
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) HstP416)
      as (HstP80 & _).
    assert (Hlit : MP !! 4744 = Some ubyte0).
    { apply (proj2 HiP). vm_compute.
      first [ reflexivity | f_equal; apply bv_eq; reflexivity ]. }
    assert (Htbs0 : ustr_at MP 4744 (@nil (bv 8))).
    { split.
      - intros j b Hj. rewrite lookup_nil in Hj. discriminate.
      - change (4744 + Z.of_nat (length (@nil (bv 8)))) with 4744. exact Hlit. }
    assert (Hrdt : uv_rd pt MP 4744 (Z.of_nat (length (@nil (bv 8))) + 1)).
    { change (Z.of_nat (length (@nil (bv 8))) + 1) with 1.
      exact (sh_rodata_rd1 pt MP 4744 ubyte0 Hl (proj2 HiP) ltac:(lia)
               ltac:(vm_compute;
                     first [ reflexivity | f_equal; apply bv_eq; reflexivity ])). }
    iApply (wp_sh_peek C pt gin gbrk hbase hlen Q CIDy MP r17
              (mword_of_int (uint sp0 - 64)) (uint sp0 - 56) s0 bs
              (length bs) 4744 (@nil (bv 8))
              ltac:(unfold sh_parse_pre; rewrite Hubot; split_and!;
                    [ exact Hlay | exact HiP
                    | exact (sh_img_tables MP (proj2 HiP))
                    | split; [ exact HstrP | exact Hbnz ]
                    | exact Hnosym | exact HrdP2 | exact HwrP2 | lia | lia
                    | unfold sh_frame_ok; lia | lia ])
              Hr17sp HstP80 Hr17a0 Hr17a1 Hr17a2
              ltac:(split_and!;
                    [ exact HpsP
                    | exact (Hstrd MP sp0 64 (uint sp0 - 56) 8 HstP64
                               ltac:(lia) ltac:(lia) ltac:(lia))
                    | exact (stack_wr pt MP sp0 64 (uint sp0 - 56) 8 HstP64
                               ltac:(lia) ltac:(lia) ltac:(lia))
                    | exact Hpsal | rewrite Hubot; lia
                    | change (2 ^ 38) with 274877906944; lia ])
              ltac:(lia) ltac:(lia) Htbs0
              ltac:(intros j b Hj; rewrite lookup_nil in Hj; discriminate)
              Hrdt
              ltac:(rewrite Hubot; cbn [length Z.of_nat]; lia)
              ltac:(rewrite Hr17ra; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CIDz mK MK) "%Hcs3 %Ha0K %HpsK %HonlyK Hcg Hpc".
    iEval (rewrite Hr17ra) in "Hpc".
    rewrite Hubot in HonlyK.
    assert (Hdrop : sh_skipws (drop (length bs) bs) = 0%nat)
      by (rewrite drop_all; exact sh_skipws_nil).
    rewrite Hdrop in HpsK. rewrite Nat.add_0_r in HpsK.
    (* --- what survived peek --- *)
    assert (HwinKlo : forall w : Z * Z,
              w ∈ [sh_win (uint sp0 - 56) 8; sh_win (uint sp0 - 64 - 80) 80] ->
              8208 <= fst w).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HwinKhi : forall w : Z * Z,
              w ∈ [sh_win (uint sp0 - 56) 8; sh_win (uint sp0 - 64 - 80) 80] ->
              fst w + snd w <= uint sp0 - 48).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HlowK : forall k : Z, k < uint sp0 - 144 -> MK !! k = MP !! k).
    { intros k Hk. apply (uM_only_in_out MP MK _ k HonlyK).
      intros w Hw Hin.
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; lia | ].
      rewrite elem_of_nil in Hw. exact Hw. }
    assert (HiK : sh_img_sub MK) by exact (keep_img MP MK _ HonlyK HwinKlo HiP).
    assert (HtK : sh_text_sub MK) by exact (sh_img_text MK HiK).
    assert (HdK : forall k : Z, is_Some (MP !! k) -> is_Some (MK !! k))
      by exact (keep_dom MP MK _ HonlyK).
    assert (HstK : uv_stack pt MK sp0 480)
      by exact (uv_stack_dom pt MP MK sp0 480 HdK HstP).
    destruct (uv_stack_split pt MK sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) HstK) as (HstK64 & HstK416).
    rewrite (uv_stack_sp_moi pt MK sp0 64 HstK64) in HstK416.
    assert (HstrK : ustr_at MK s0 bs).
    { destruct HstrP as (Hb1 & Hb2). split.
      - intros j b Hj. pose proof (lookup_lt_Some bs j b Hj).
        rewrite (HlowK (s0 + Z.of_nat j) ltac:(lia)). exact (Hb1 j b Hj).
      - rewrite (HlowK (s0 + Z.of_nat (length bs)) ltac:(lia)). exact Hb2. }
    assert (HrdK2 : uv_rd pt MK s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct HrdP2; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ HrdP2 j Hj) as (b & Hb).
      exists b. rewrite (HlowK (s0 + j) ltac:(lia)). exact Hb. }
    assert (HwrK2 : uv_wr pt MK s0 (Z.of_nat (length bs) + 1)).
    { constructor; try (destruct HwrP2; assumption).
      intros j Hj. destruct (uwr_bytes _ _ _ _ HwrP2 j Hj) as (b & Hb).
      exists b. rewrite (HlowK (s0 + j) ltac:(lia)). exact Hb. }
    assert (BraK : uM_bytes MK (uint sp0 - 64 + 56) 8 (r1 !!! Regidx ra_idx))
      by exact (keep_hi MP MK _ (uint sp0 - 48) (uint sp0 - 64 + 56) _ HonlyK HwinKhi
                  ltac:(lia) BraP).
    assert (Bs0K : uM_bytes MK (uint sp0 - 64 + 48) 8 (r1 !!! Regidx s0_idx))
      by exact (keep_hi MP MK _ (uint sp0 - 48) (uint sp0 - 64 + 48) _ HonlyK HwinKhi
                  ltac:(lia) Bs0P).
    assert (Bs1K : uM_bytes MK (uint sp0 - 64 + 40) 8 (r1 !!! Regidx s1_idx))
      by exact (keep_hi MP MK _ (uint sp0 - 48) (uint sp0 - 64 + 40) _ HonlyK HwinKhi
                  ltac:(lia) Bs1P).
    assert (Bs2K : uM_bytes MK (uint sp0 - 64 + 32) 8 (r1 !!! Regidx s2_idx))
      by exact (keep_hi MP MK _ (uint sp0 - 48) (uint sp0 - 64 + 32) _ HonlyK HwinKhi
                  ltac:(lia) Bs2P).
    assert (Bs3K : uM_bytes MK (uint sp0 - 64 + 24) 8 (r1 !!! Regidx s3_idx))
      by exact (keep_hi MP MK _ (uint sp0 - 48) (uint sp0 - 64 + 24) _ HonlyK HwinKhi
                  ltac:(lia) Bs3P).
    (* the node's geometry, from [malloc]'s answer *)
    pose proof Hcmdeq as Hcmdeq0.
    rewrite Hnu in Hcmdeq.
    assert (Hcmdlo : hbase <= cmd) by lia.
    assert (Hcmdhi : cmd + SH_EXECCMD_SZ <= hbase + 65536)
      by (unfold SH_EXECCMD_SZ; lia).
    assert (Hcmdal : cmd mod 16 = 0).
    { replace cmd with ((256 * (hbase / 4096) + 4085) * 16) by lia.
      apply Z.mod_mul. lia. }
    assert (HnodeK : forall k : Z, cmd <= k < cmd + SH_EXECCMD_SZ ->
              MK !! k = MP !! k)
      by (intros k Hk; apply HlowK; unfold SH_EXECCMD_SZ in *; lia).
    assert (HtypeK : uM_bytes MK cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (HnodeK (cmd + Z.of_nat j)
                                  ltac:(unfold SH_EXECCMD_SZ; lia));
          exact (HtypeP j Hj)).
    assert (HrdcK : uv_rd pt MK cmd SH_EXECCMD_SZ).
    { constructor; try (destruct HrdP; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ HrdP j Hj) as (b & Hb).
      exists b. rewrite (HnodeK (cmd + j) ltac:(lia)). exact Hb. }
    assert (HargvK : sh_execcmd_argv MK cmd s0 toks).
    { destruct HargvP as (HavP & HgP1 & HgP2). split_and!.
      - intros i t Hi. pose proof (lookup_lt_Some toks i t Hi) as Hilt.
        destruct (HavP i t Hi) as (H1 & H2). split.
        + intros j Hj. rewrite (HnodeK (cmd + 8 + 8 * Z.of_nat i + Z.of_nat j)
                                  ltac:(unfold SH_EXECCMD_SZ; lia)).
          exact (H1 j Hj).
        + intros j Hj. rewrite (HnodeK (cmd + 88 + 8 * Z.of_nat i + Z.of_nat j)
                                  ltac:(unfold SH_EXECCMD_SZ; lia)).
          exact (H2 j Hj).
      - intros j Hj.
        rewrite (HnodeK (cmd + 8 + 8 * Z.of_nat (length toks) + Z.of_nat j)
                   ltac:(unfold SH_EXECCMD_SZ; lia)). exact (HgP1 j Hj).
      - intros j Hj.
        rewrite (HnodeK (cmd + 88 + 8 * Z.of_nat (length toks) + Z.of_nat j)
                   ltac:(unfold SH_EXECCMD_SZ; lia)). exact (HgP2 j Hj). }
    assert (HmKsp : mK !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hcs3 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hr17sp).
    assert (HmKs0 : mK !!! Regidx s0_idx = (mword_of_int (uint sp0) : mword 64))
      by (rewrite (Hcs3 s0_idx ltac:(vm_compute; reflexivity)); exact Hr17s0).
    assert (HmKs1 : mK !!! Regidx s1_idx
                    = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by (rewrite (Hcs3 s1_idx ltac:(vm_compute; reflexivity)); exact Hr17s1).
    assert (HmKs3 : mK !!! Regidx s3_idx = (mword_of_int cmd : mword 64))
      by (rewrite (Hcs3 s3_idx ltac:(vm_compute; reflexivity)); exact Hr17s3).
    (* ---- 0x8aa  ld a2,-56(s0)   (a2 := s) ---- *)
    destruct (acc8 MK (uint sp0 - 56)
                (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)
                ltac:(lia) Hpsal ltac:(change (2 ^ 38) with 274877906944; lia)
                HpsK) as (Hu8 & Hcn8 & Hpg8 & Hal8 & Hby8 & Hwv8).
    destruct (stack_leaf pt MK sp0 64 (uint sp0 - 56) HstK64 ltac:(lia))
      as (wld & Hwld & _ & Hldok).
    assert (Hvald : (mword_of_int (uint sp0 - 56) : mword 64)
                    = add_vec (mK !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 4040 : mword 12))).
    { rewrite HmKs0.
      assert (Hc : (sign_extend' 64 (mword_of_int 4040 : mword 12) : mword 64)
                   = mword_of_int (-56))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_ld C pt Psh MK mK (mword_of_int 0x8aa)
              (mword_of_int 4040 : mword 12) s0_idx a2_idx
              wld (mword_of_int (uint sp0 - 56))
              (mword_of_int (s0 + Z.of_nat (length bs)))
              (ui_sh_8aa pt MK Hl HtK)
              ltac:(vm_compute; discriminate) Hvald Hwld Hldok Hcn8 Hpg8 Hal8
              Hby8 Hwv8 with "Hcg Hpc").
    iIntros (CIDb2) "Hcg Hpc".
    set (r18 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (length bs))
                        : mword 64)]> mK).
    assert (E8aa : add_vec_int (mword_of_int 0x8aa : mword 64) 4
                   = mword_of_int 0x8ae)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8aa) in "Hpc".
    assert (Hr18a2 : r18 !!! Regidx a2_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64))
      by exact (upd_eq mK (Regidx a2_idx) _).
    assert (Hr18s1 : r18 !!! Regidx s1_idx
                     = (mword_of_int (s0 + Z.of_nat (length bs)) : mword 64)).
    { rewrite (upd_ne mK (Regidx a2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact HmKs1. }
    (* ---- 0x8ae  bne a2,s1,0x8c8  --  s == es, so NOT taken.  The other
       arm is the fprintf/panic("syntax") this development does not enter. -- *)
    assert (Htk : false = uv_btaken BNE (r18 !!! Regidx a2_idx)
                            (r18 !!! Regidx s1_idx)).
    { cbn [uv_btaken]. rewrite Hr18a2 Hr18s1.
      rewrite (moi_neq_vec (s0 + Z.of_nat (length bs))
                 (s0 + Z.of_nat (length bs))
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. reflexivity. }
    iApply (wp_uv_btype C pt Psh MK r18 (mword_of_int 0x8ae)
              (mword_of_int 26 : mword 13) s1_idx a2_idx BNE
              false (mword_of_int 0x8c8)
              (ui_sh_8ae pt MK Hl HtK)
              Htk ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc0; discriminate Hc0)
              with "Hcg Hpc").
    iIntros (CIDc2) "Hcg Hpc".
    assert (E8ae : (if false then (mword_of_int 0x8c8 : mword 64)
                    else add_vec_int (mword_of_int 0x8ae : mword 64) 4)
                   = mword_of_int 0x8b2)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8ae) in "Hpc".
    (* ---- 0x8b2  c.mv a0,s3 ---- *)
    assert (Hr18s3 : r18 !!! Regidx s3_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne mK (Regidx a2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact HmKs3. }
    assert (Hmv7 : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (r18 !!! Regidx s3_idx))
      by (rewrite Hr18s3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MK r18 (mword_of_int 0x8b2)
              a0_idx s3_idx (mword_of_int cmd)
              (ui_sh_8b2 pt MK Hl HtK)
              ltac:(vm_compute; discriminate) Hmv7 with "Hcg Hpc").
    iIntros (CIDd2) "Hcg Hpc".
    set (r19 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int cmd : mword 64)]> r18).
    assert (E8b2 : add_vec_int (mword_of_int 0x8b2 : mword 64) 2
                   = mword_of_int 0x8b4)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8b2) in "Hpc".
    (* ---- 0x8b4  jal ra,0x7ee <nulterminate> ---- *)
    assert (Htgt4 : (mword_of_int 0x7ee : mword 64)
                    = add_vec (mword_of_int 0x8b4)
                        (sign_extend' 64 (mword_of_int 2096954 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlnk4 : (mword_of_int 0x8b8 : mword 64)
                    = add_vec_int (mword_of_int 0x8b4 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh MK r19 (mword_of_int 0x8b4)
              (mword_of_int 2096954 : mword 21) ra_idx
              (mword_of_int 0x7ee) (mword_of_int 0x8b8)
              (ui_sh_8b4 pt MK Hl HtK)
              ltac:(vm_compute; discriminate) Htgt4 Hlnk4
              ltac:(vm_compute; reflexivity) with "Hcg Hpc").
    iIntros (CIDe2) "Hcg Hpc".
    set (r20 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x8b8 : mword 64)]> r19).
    iEval (rewrite <- Hsnul) in "Hpc".
    assert (Hr20ra : r20 !!! Regidx ra_idx = (mword_of_int 0x8b8 : mword 64))
      by exact (upd_eq r19 (Regidx ra_idx) _).
    assert (Hr20a0 : r20 !!! Regidx a0_idx = (mword_of_int cmd : mword 64)).
    { rewrite (upd_ne r19 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r18 (Regidx a0_idx) _). }
    assert (Hr20 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
              Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a2_idx ->
              r20 !!! Regidx r = mK !!! Regidx r).
    { intros r Nra Na0 Na2.
      rewrite (upd_ne r19 (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne r18 (Regidx a0_idx) (Regidx r) _ Na0).
      exact (upd_ne mK (Regidx a2_idx) (Regidx r) _ Na2). }
    assert (Hr20sp : r20 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (Hr20 csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact HmKsp. }
    destruct (uv_stack_split pt MK (mword_of_int (uint sp0 - 64)) 416 32 384
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) HstK416)
      as (HstK32 & _).
    (* ---- nulterminate(cmd) ---- *)
    iApply (wp_sh_nulterminate CIDe2 MK r20
              (mword_of_int (uint sp0 - 64)) cmd s0 bs 0%nat toks
              ltac:(unfold sh_parse_pre; rewrite Hubot; split_and!;
                    [ exact Hlay | exact HiK
                    | exact (sh_img_tables MK (proj2 HiK))
                    | split; [ exact HstrK | exact Hbnz ]
                    | exact Hnosym | exact HrdK2 | exact HwrK2 | lia | lia
                    | unfold sh_frame_ok; lia | lia ])
              Hr20sp HstK32 Hr20a0 HtypeK HargvK HrdcK
              Hcmdeq0
              ltac:(unfold sh_buf_clear, sh_disj, SH_FREEP, SH_BASE, SH_DATA_PG;
                    split_and!; lia)
              ltac:(lia) ltac:(lia) Htoks
              ltac:(rewrite Hr20ra; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CIDf2 mN MN) "%Hcs4 %HstrN %HargvN %HonlyN Hcg Hpc".
    iEval (rewrite Hr20ra) in "Hpc".
    rewrite Hubot in HonlyN.
    (* --- what survived nulterminate --- *)
    assert (HwinNlo : forall w : Z * Z,
              w ∈ [sh_win s0 (Z.of_nat (length bs) + 1);
                   sh_win (uint sp0 - 64 - 32) 32] -> 8208 <= fst w).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HwinNhi : forall w : Z * Z,
              w ∈ [sh_win s0 (Z.of_nat (length bs) + 1);
                   sh_win (uint sp0 - 64 - 32) 32] ->
              fst w + snd w <= uint sp0 - 48).
    { intros w Hw.
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ]; [ cbv [sh_win fst snd]; lia | ].
      rewrite elem_of_nil in Hw. exfalso. exact Hw. }
    assert (HiN : sh_img_sub MN) by exact (keep_img MK MN _ HonlyN HwinNlo HiK).
    assert (HtN : sh_text_sub MN) by exact (sh_img_text MN HiN).
    assert (HdN : forall k : Z, is_Some (MK !! k) -> is_Some (MN !! k))
      by exact (keep_dom MK MN _ HonlyN).
    assert (HstN : uv_stack pt MN sp0 480)
      by exact (uv_stack_dom pt MK MN sp0 480 HdN HstK).
    destruct (uv_stack_split pt MN sp0 480 64 416 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) HstN) as (HstN64 & _).
    assert (HnodeN : forall k : Z, cmd <= k < cmd + SH_EXECCMD_SZ ->
              MN !! k = MK !! k).
    { intros k Hk. apply (uM_only_in_out MK MN _ k HonlyN).
      intros w Hw Hin.
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; unfold SH_EXECCMD_SZ in *; lia | ].
      apply elem_of_cons in Hw as [ -> | Hw ];
        [ cbv [sh_win fst snd] in Hin; unfold SH_EXECCMD_SZ in *; lia | ].
      rewrite elem_of_nil in Hw. exact Hw. }
    assert (HrdcN : uv_rd pt MN cmd SH_EXECCMD_SZ).
    { constructor; try (destruct HrdcK; assumption).
      intros j Hj. destruct (urd_bytes _ _ _ _ HrdcK j Hj) as (b & Hb).
      exists b. rewrite (HnodeN (cmd + j) ltac:(lia)). exact Hb. }
    assert (HtypeN : uM_bytes MN cmd 4 (mword_of_int 1 : mword 32))
      by (intros j Hj; rewrite (HnodeN (cmd + Z.of_nat j)
                                  ltac:(unfold SH_EXECCMD_SZ; lia));
          exact (HtypeK j Hj)).
    assert (BraN : uM_bytes MN (uint sp0 - 64 + 56) 8 (r1 !!! Regidx ra_idx))
      by exact (keep_hi MK MN _ (uint sp0 - 48) (uint sp0 - 64 + 56) _ HonlyN HwinNhi
                  ltac:(lia) BraK).
    assert (Bs0N : uM_bytes MN (uint sp0 - 64 + 48) 8 (r1 !!! Regidx s0_idx))
      by exact (keep_hi MK MN _ (uint sp0 - 48) (uint sp0 - 64 + 48) _ HonlyN HwinNhi
                  ltac:(lia) Bs0K).
    assert (Bs1N : uM_bytes MN (uint sp0 - 64 + 40) 8 (r1 !!! Regidx s1_idx))
      by exact (keep_hi MK MN _ (uint sp0 - 48) (uint sp0 - 64 + 40) _ HonlyN HwinNhi
                  ltac:(lia) Bs1K).
    assert (Bs2N : uM_bytes MN (uint sp0 - 64 + 32) 8 (r1 !!! Regidx s2_idx))
      by exact (keep_hi MK MN _ (uint sp0 - 48) (uint sp0 - 64 + 32) _ HonlyN HwinNhi
                  ltac:(lia) Bs2K).
    assert (Bs3N : uM_bytes MN (uint sp0 - 64 + 24) 8 (r1 !!! Regidx s3_idx))
      by exact (keep_hi MK MN _ (uint sp0 - 48) (uint sp0 - 64 + 24) _ HonlyN HwinNhi
                  ltac:(lia) Bs3K).
    assert (HmNsp : mN !!! Regidx csp_rs1
                    = (mword_of_int (uint sp0 - 64) : mword 64))
      by (rewrite (Hcs4 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hr20sp).
    assert (HmNs3 : mN !!! Regidx s3_idx = (mword_of_int cmd : mword 64)).
    { rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hr20 s3_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact HmKs3. }
    (* ---- 0x8b8  c.mv a0,s3 ---- *)
    assert (Hmv8 : (mword_of_int cmd : mword 64)
                   = add_vec zero_reg (mN !!! Regidx s3_idx))
      by (rewrite HmNs3 moi_add_zero_l; reflexivity).
    iApply (wp_uv_cmv C pt Psh MN mN (mword_of_int 0x8b8)
              a0_idx s3_idx (mword_of_int cmd)
              (ui_sh_8b8 pt MN Hl HtN)
              ltac:(vm_compute; discriminate) Hmv8 with "Hcg Hpc").
    iIntros (CIDg2) "Hcg Hpc".
    set (r21 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int cmd : mword 64)]> mN).
    assert (E8b8 : add_vec_int (mword_of_int 0x8b8 : mword 64) 2
                   = mword_of_int 0x8ba)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8b8) in "Hpc".
    assert (Hr21sp : r21 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne mN (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact HmNsp. }
    (* ---- 0x8ba..0x8c2  the five reloads ---- *)
    iApply (wp_sh_reload C pt CIDg2 Psh 0x8ba 0x8bc 64 56
              (mword_of_int 7 : mword 6) ra_idx (r1 !!! Regidx ra_idx)
              MN r21 sp0 HstN64 Hr21sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              BraN (ui_sh_8ba pt MN Hl HtN)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDh2) "Hcg Hpc".
    set (r22 := <[Regidx ra_idx
                  := regval_into_reg (r1 !!! Regidx ra_idx)]> r21).
    assert (Hr22sp : r22 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r21 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr21sp. }
    iApply (wp_sh_reload C pt CIDh2 Psh 0x8bc 0x8be 64 48
              (mword_of_int 6 : mword 6) s0_idx (r1 !!! Regidx s0_idx)
              MN r22 sp0 HstN64 Hr22sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs0N (ui_sh_8bc pt MN Hl HtN)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDi2) "Hcg Hpc".
    set (r23 := <[Regidx s0_idx
                  := regval_into_reg (r1 !!! Regidx s0_idx)]> r22).
    assert (Hr23sp : r23 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r22 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr22sp. }
    iApply (wp_sh_reload C pt CIDi2 Psh 0x8be 0x8c0 64 40
              (mword_of_int 5 : mword 6) s1_idx (r1 !!! Regidx s1_idx)
              MN r23 sp0 HstN64 Hr23sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs1N (ui_sh_8be pt MN Hl HtN)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDj2) "Hcg Hpc".
    set (r24 := <[Regidx s1_idx
                  := regval_into_reg (r1 !!! Regidx s1_idx)]> r23).
    assert (Hr24sp : r24 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r23 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr23sp. }
    iApply (wp_sh_reload C pt CIDj2 Psh 0x8c0 0x8c2 64 32
              (mword_of_int 4 : mword 6) s2_idx (r1 !!! Regidx s2_idx)
              MN r24 sp0 HstN64 Hr24sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs2N (ui_sh_8c0 pt MN Hl HtN)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDk2) "Hcg Hpc".
    set (r25 := <[Regidx s2_idx
                  := regval_into_reg (r1 !!! Regidx s2_idx)]> r24).
    assert (Hr25sp : r25 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r24 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr24sp. }
    iApply (wp_sh_reload C pt CIDk2 Psh 0x8c2 0x8c4 64 24
              (mword_of_int 3 : mword 6) s3_idx (r1 !!! Regidx s3_idx)
              MN r25 sp0 HstN64 Hr25sp
              ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Bs3N (ui_sh_8c2 pt MN Hl HtN)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CIDl2) "Hcg Hpc".
    set (r26 := <[Regidx s3_idx
                  := regval_into_reg (r1 !!! Regidx s3_idx)]> r25).
    assert (Hr26sp : r26 !!! Regidx csp_rs1
                     = (mword_of_int (uint sp0 - 64) : mword 64)).
    { rewrite (upd_ne r25 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hr25sp. }
    (* ---- 0x8c4  c.addi16sp sp,sp,64 ---- *)
    assert (Hwsp : sp0 = add_vec (r26 !!! Regidx csp_rs1)
                          (sign_extend' 64
                             (caddi16sp_imm (mword_of_int 4 : mword 6)))).
    { rewrite Hr26sp.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))
                    : mword 64) = mword_of_int 64)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add.
      replace (uint sp0 - 64 + 64) with (uint sp0) by lia.
      symmetry. apply moi_of_uint. }
    iApply (wp_uv_caddi16sp C pt Psh MN r26 (mword_of_int 0x8c4)
              (mword_of_int 4 : mword 6) sp0
              (ui_sh_8c4 pt MN Hl HtN) Hwsp with "Hcg Hpc").
    iIntros (CIDm2) "Hcg Hpc".
    set (r27 := <[Regidx csp_rs1 := regval_into_reg sp0]> r26).
    assert (E8c4 : add_vec_int (mword_of_int 0x8c4 : mword 64) 2
                   = mword_of_int 0x8c6)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E8c4) in "Hpc".
    (* ---- 0x8c6  c.jr ra ---- *)
    assert (Hr27ra : r27 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne r26 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r25 (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r24 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r23 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r22 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq r21 (Regidx ra_idx) _).
      exact (Hr1 ra_idx ltac:(vm_compute; discriminate)). }
    assert (Htgtr : (m !!! Regidx ra_idx) = ret_pc (r27 !!! Regidx ra_idx)).
    { rewrite Hr27ra. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh MN r27 (mword_of_int 0x8c6)
              ra_idx (m !!! Regidx ra_idx)
              (ui_sh_8c6 pt MN Hl HtN)
              ltac:(vm_compute; discriminate) Htgtr with "Hcg Hpc").
    iIntros (CIDn2) "Hcg Hpc".
    (* ---- the postcondition ---- *)
    destruct (lookup_lt_is_Some_2 toks 0%nat ltac:(lia)) as (t0 & Ht0).
    destruct (sh_tokens_bounds bs 0%nat toks Htoks ltac:(lia) 0%nat t0 Ht0)
      as (_ & Ht01 & Ht02).
    destruct HargvN as (HavN & HnN1 & HnN2).
    destruct (HavN 0%nat t0 Ht0) as (Hp0b & _).
    assert (Hp0b' : uM_bytes MN (cmd + 8) 8
                      (mword_of_int (s0 + Z.of_nat (fst t0)) : mword 64)).
    { replace (cmd + 8) with (cmd + 8 + 8 * Z.of_nat 0)
        by (cbn [Z.of_nat]; lia).
      exact Hp0b. }
    assert (Hlenargs : length (sh_tok_bytes bs <$> toks) = length toks)
      by (rewrite length_fmap; reflexivity).
    iApply ("Hcont" $! CIDn2 r27 MN cmd (s0 + Z.of_nat (fst t0))
              with "[] [] [] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - (* ucallee_saved *)
      iPureIntro. intros r Hr.
      destruct (decide (Regidx r = Regidx csp_rs1)) as [ Fsp | Dsp ].
      { rewrite Fsp. rewrite (upd_eq r26 (Regidx csp_rs1) _).
        symmetry. exact Hsp. }
      rewrite (upd_ne r26 (Regidx csp_rs1) (Regidx r) _ Dsp).
      destruct (decide (Regidx r = Regidx s3_idx)) as [ F3 | D3 ].
      { rewrite F3. rewrite (upd_eq r25 (Regidx s3_idx) _).
        exact (Hr1 s3_idx ltac:(vm_compute; discriminate)). }
      rewrite (upd_ne r25 (Regidx s3_idx) (Regidx r) _ D3).
      destruct (decide (Regidx r = Regidx s2_idx)) as [ F2 | D2 ].
      { rewrite F2. rewrite (upd_eq r24 (Regidx s2_idx) _).
        exact (Hr1 s2_idx ltac:(vm_compute; discriminate)). }
      rewrite (upd_ne r24 (Regidx s2_idx) (Regidx r) _ D2).
      destruct (decide (Regidx r = Regidx s1_idx)) as [ F1 | D1 ].
      { rewrite F1. rewrite (upd_eq r23 (Regidx s1_idx) _).
        exact (Hr1 s1_idx ltac:(vm_compute; discriminate)). }
      rewrite (upd_ne r23 (Regidx s1_idx) (Regidx r) _ D1).
      destruct (decide (Regidx r = Regidx s0_idx)) as [ F0 | D0 ].
      { rewrite F0. rewrite (upd_eq r22 (Regidx s0_idx) _).
        exact (Hr1 s0_idx ltac:(vm_compute; discriminate)). }
      rewrite (upd_ne r22 (Regidx s0_idx) (Regidx r) _ D0).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (upd_ne r21 (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne mN (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (Hcs4 r Hr). rewrite (Hr20 r Nra Na0 Na2).
      rewrite (Hcs3 r Hr). rewrite (Hr17w r Nra Na0 Na1 Na2 D3).
      rewrite (Hcs2 r Hr). rewrite (Hr11q r Nra Na0 Na1 D2 D1).
      rewrite (Hcs1 r Hr). exact (Hr4 r Nra D1 D0 Dsp).
    - (* a0 = cmd *)
      iPureIntro.
      rewrite (upd_ne r26 (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r25 (Regidx s3_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r24 (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r23 (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r22 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r21 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mN (Regidx a0_idx) _).
    - iPureIntro. exact Hcmdeq0.
    - iPureIntro. exact HtypeN.
    - iPureIntro. exact Hp0b'.
    - iPureIntro. lia.
    - (* THE bounded exec arguments *)
      iPureIntro. unfold sh_exec_below. rewrite Ht0.
      cbn [default from_option id]. split_and!.
      + lia.
      + assert (Hlt0 : length (sh_tok_bytes bs t0) = (snd t0 - fst t0)%nat)
          by (unfold sh_tok_bytes; rewrite length_take length_drop; lia).
        rewrite Hlt0. lia.
      + exact (HstrN 0%nat t0 Ht0).
      + rewrite Hlenargs. unfold SH_EXECCMD_SZ in *. lia.
      + rewrite Hlenargs. exact HnN1.
      + intros i bs' Hi.
        rewrite list_lookup_fmap in Hi.
        destruct (toks !! i) as [ t | ] eqn:Hti;
          [ | cbn [fmap option_fmap option_map] in Hi; discriminate ].
        cbn [fmap option_fmap option_map] in Hi. injection Hi as <-.
        destruct (sh_tokens_bounds bs 0%nat toks Htoks ltac:(lia) i t Hti)
          as (_ & Hb1 & Hb2).
        destruct (HavN i t Hti) as (Hq1 & _).
        exists (s0 + Z.of_nat (fst t)). split_and!.
        * exact Hq1.
        * exact (HstrN i t Hti).
        * lia.
        * assert (Hlt : length (sh_tok_bytes bs t) = (snd t - fst t)%nat)
            by (unfold sh_tok_bytes; rewrite length_take length_drop; lia).
          rewrite Hlt. lia.
    - iPureIntro. exact HrdcN.
    - (* the image effect, composed across the four calls *)
      iPureIntro. split.
      + intros k Hk. apply HdN. apply HdK. apply HdP. apply HdS.
        apply Hd6. exact Hk.
      + intros k Hk.
        pose proof (nwin _ hbase 65536 k ltac:(apply elem_of_list_here) Hk)
          as K1.
        pose proof (nwin _ SH_FREEP 8 k
                      ltac:(apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as K2.
        pose proof (nwin _ SH_BASE 16 k
                      ltac:(apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as K3.
        pose proof (nwin _ s0 (Z.of_nat (length bs) + 1) k
                      ltac:(apply elem_of_list_further;
                            apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as K4.
        pose proof (nwin _ (uint sp0 - 480) 480 k
                      ltac:(apply elem_of_list_further;
                            apply elem_of_list_further;
                            apply elem_of_list_further;
                            apply elem_of_list_further; apply elem_of_list_here)
                      Hk) as K5.
        unfold SH_FREEP, SH_BASE, SH_DATA_PG in K2, K3.
        rewrite (uM_only_in_out MK MN _ k HonlyN
                   ltac:(intros w Hw Hin;
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         rewrite elem_of_nil in Hw; exact Hw)).
        rewrite (uM_only_in_out MP MK _ k HonlyK
                   ltac:(intros w Hw Hin;
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         rewrite elem_of_nil in Hw; exact Hw)).
        rewrite (uM_only_in_out MS MP _ k HonlyP
                   ltac:(intros w Hw Hin;
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd SH_FREEP SH_DATA_PG] in Hin;
                           lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd SH_BASE SH_DATA_PG] in Hin;
                           lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         apply elem_of_cons in Hw as [ -> | Hw ];
                         [ cbv [sh_win fst snd] in Hin; lia | ];
                         rewrite elem_of_nil in Hw; exact Hw)).
        rewrite (HeS k ltac:(lia)). exact (Hn6 k ltac:(lia)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §8 [parsecmd] at the contract USpecShParse.v states.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_parsecmd (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s0 : Z) (bs : list (bv 8)) (toks : list (nat * nat)) :
    wp_sh_parsecmd_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      M m sp0 s0 bs toks.
  Proof.
    intros Hpre Hsp Hst Hs Hbufc Htoks Hne Hlen Hfreep0 Hbasesz0 Hbssw Hret2.
    iIntros "Hcg Hbrk Hpc Hcont".
    iApply (wp_sh_parsecmd_strong CIDp M m sp0 s0 bs toks
              Hpre Hsp Hst Hs Hbufc Htoks Hne Hlen Hfreep0 Hbasesz0 Hbssw Hret2
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CID m' M' cmd p0) "%Hcs %Ha0 %Hcmdeq %Htype %Hp0b %Hp0nz
                                %Hexb %Hrd %Honly Hbrk Hcg Hpc".
    iApply ("Hcont" $! CID m' M' cmd p0
              with "[] [] [] [] [] [] [] [] [] Hbrk Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0.
    - iPureIntro. exact Hcmdeq.
    - iPureIntro. exact Htype.
    - iPureIntro. exact Hp0b.
    - iPureIntro. exact Hp0nz.
    - iPureIntro. exact Hexb.
    - iPureIntro. exact Hrd.
    - iPureIntro. exact Honly.
  Qed.

End UProofShCmd.
