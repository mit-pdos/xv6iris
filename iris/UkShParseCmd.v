(* ===================================================================== *)
(* UkShParseCmd.v -- SH LANE STAGE 4, part 6: the NUL cut and the line as  *)
(* bytes -- what the general parser ([UkShParser.v], lane user-once)       *)
(* builds on.                                                             *)
(*                                                                        *)
(*   nulterminate @0x7ca  the jump table -- the one COMPUTED control       *)
(*                        transfer in the parser -- walking the tree and   *)
(*                        writing a NUL at every recorded token END.  That *)
(*                        cut is what turns token BOUNDARIES into the argv *)
(*                        vector [exec] observes, and it is the fact       *)
(*                        stage 6's seam is built on.  The EXEC leaf's     *)
(*                        loop ([wp_kshp_nul_loop]) and the return         *)
(*                        ([wp_kshp_nul_fin]) live here; the walk of the   *)
(*                        whole function, over every constructor, is       *)
(*                        [UkShParser.wp_ref_nulterminate].                *)
(*   ushp_nulfold         the cut on the bytes, and [ushp_ext] the line as *)
(*                        a byte run.                                      *)
(*                                                                        *)
(* WHAT LEFT (lane user-once, A4).  The symbol-free walks of parsepipe,    *)
(* parseline, parsecmd and the parser theorem [wp_kshp_parser] -- and     *)
(* with them [UkShParseExec] (parseexec, the argument loop) and           *)
(* [UkShParseRedir] (parseredirs) -- were the third copy of the parser    *)
(* walk, stated at the symbol-free token model; their statements are      *)
(* instances of the general walks at [RefParseBridge.ref_parsecmd_nosym]  *)
(* and no file consumed them once [UkShEcho]'s child went through          *)
(* [UkShSeam.wp_ref_child].  The width-4 text load nulterminate's jump     *)
(* table needs is an engine leaf, [UkRunMem.wp_uk_clw_text].              *)
(*                                                                        *)
(* See iris/UkShParse.v's header for why stage 4 is several files.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.
Require Import UkShParseLex.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShParseCmd.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_slot := (UkShParse.ushp_slot N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).

  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
(*ALIASES-END*)

  (* ===================================================================== *)
  (* §13 nulterminate @0x7ca -- the jump table, and the ONE leaf this file  *)
  (*     could not build.                                                   *)
  (*                                                                       *)
  (*   struct cmd *nulterminate(struct cmd *cmd) {                          *)
  (*     if(cmd == 0) return 0;                                             *)
  (*     switch(cmd->type) {                                                *)
  (*     case EXEC: for(i = 0; ecmd->argv[i]; i++) *ecmd->eargv[i] = 0;      *)
  (*     ... }                                                              *)
  (*     return cmd; }                                                      *)
  (*                                                                       *)
  (* THIS IS WHERE THE TOKEN BOUNDARIES BECOME C STRINGS.  parseexec left   *)
  (* argv[i] and eargv[i] as two pointers INTO THE LINE; nulterminate       *)
  (* writes a NUL at every eargv[i], and after it the bytes from argv[i]    *)
  (* are the NUL-terminated argument [exec] observes.  The walk says        *)
  (* exactly that and no more: the node is unchanged and the line comes     *)
  (* back as [ushp_nulfold toks], the original bytes with a zero at each    *)
  (* token's END INDEX.                                                     *)
  (*                                                                       *)
  (* THE TEXT-HALF LOAD THIS FUNCTION FORCES.  The switch is a genuine      *)
  (* computed transfer through a table in .rodata, and .rodata is the TEXT  *)
  (* half, so the [c.lw a5,0(a5)] at 0x7f0 is a FOUR-BYTE LOAD OUT OF THE   *)
  (* TEXT HALF -- which the walker cannot serve, because a text page is X   *)
  (* and not W and its bytes are stamped and outside the walker's map       *)
  (* (claude-notes/design/icache.md).  The engine's text reader is          *)
  (* width-generic (WpUmodeTextLoad.v) and the leaf is                      *)
  (* [UkRunMem.wp_uk_clw_text]; this walk just calls it, and runcmd's own   *)
  (* jump table calls the same one.                                        *)
  (* ===================================================================== *)

  (* ---- the line, and what the loop does to it ------------------------- *)
  Definition ushp_setb (g : nat -> bv 8) (j : nat) (b : bv 8) : nat -> bv 8 :=
    fun i => if Nat.eqb i j then b else g i.

  Fixpoint ushp_nulfold (toks : list (nat * nat)) (g : nat -> bv 8)
    : nat -> bv 8 :=
    match toks with
    | [] => g
    | tk :: r => ushp_nulfold r (ushp_setb g (snd tk) ubyte0)
    end.

  Lemma ushp_bytes_upd (a : Z) (n : nat) (g : nat -> bv 8) (j : nat)
      (b : bv 8) :
    (j < n)%nat ->
    ubytes γd a n g -∗
    ubyte γd (a + Z.of_nat j) (g j) ∗
    (ubyte γd (a + Z.of_nat j) b -∗ ubytes γd a n (ushp_setb g j b)).
  Proof using .
    intro Hj. iIntros "H".
    assert (Hjs : seq 0 n !! j = Some j) by (apply lookup_seq; lia).
    rewrite /ubytes /ubytesq.
    rewrite (big_sepL_delete
               (fun _ i : nat => ubyteq γd (DfracOwn 1) (a + Z.of_nat i) (g i))
               (seq 0 n) j j Hjs).
    iDestruct "H" as "[Hj Hrest]". iFrame "Hj". iIntros "Hj".
    rewrite (big_sepL_delete
               (fun _ i : nat =>
                  ubyteq γd (DfracOwn 1) (a + Z.of_nat i)
                    (ushp_setb g j b i))
               (seq 0 n) j j Hjs).
    iSplitL "Hj".
    { assert (Ehit : ushp_setb g j b j = b)
        by (rewrite /ushp_setb Nat.eqb_refl; reflexivity).
      rewrite Ehit. iExact "Hj". }
    iApply (big_sepL_mono with "Hrest").
    intros k y Hy. apply lookup_seq in Hy as [ -> Hlt ].
    rewrite Nat.add_0_l.
    destruct (decide (k = j)) as [ Ek | Ek ]; [ done | ].
    assert (Ese : ushp_setb g j b k = g k)
      by (rewrite /ushp_setb (proj2 (Nat.eqb_neq k j) Ek); reflexivity).
    rewrite Ese. done.
  Qed.

  (* ---- reading one slot of a FINISHED node ---------------------------- *)
  Lemma ushp_slot_read (t0 base : Z) (toks : list (nat * nat))
      (sel : nat * nat -> nat) (i : nat) :
    (i < 10)%nat ->
    ([∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j) -∗
    ushp_slot t0 base toks sel i ∗
    (ushp_slot t0 base toks sel i -∗
     [∗ list] j ∈ seq 0 10, ushp_slot t0 base toks sel j).
  Proof using .
    intro Hi. iIntros "H".
    iApply (big_sepL_lookup_acc _ (seq 0 10) i i
              ltac:(apply lookup_seq; lia) with "H").
  Qed.

  (* ---- one byte of the read-only image, by its address ---------------- *)
  Lemma ushp_ro_byte (a : Z) (b : bv 8) :
    shp_ro !! a = Some b -> shp_rodata γt -∗ utext γt a b.
  Proof using .
    intro Ha. iIntros "#H". rewrite /shp_rodata /utext_img.
    iApply (big_sepM_lookup _ _ a b with "H"). exact Ha.
  Qed.

  (* ...and the FOUR that make the EXEC arm's jump-table entry.  The entry
     is a signed displacement from the table's own base, so 0x13b0 plus it
     is 0x7f6 -- which is checked by [vm_compute] below, not asserted. *)
  Lemma ushp_jrow_exec :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13b4 + Z.of_nat j)
        (nth_byte (mword_of_int 4294964294 : mword 32) j).
  Proof using .
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964294 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964294 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964294 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13b4 + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964294 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.

  (* ---- the EXEC arm's loop, 0x7fe..0x80a ------------------------------ *)
  Lemma wp_kshp_nul_loop (s0 p : Z) (len : nat) (nn : nat) :
    forall (rest : list (nat * nat)) (done : list (nat * nat))
           (tk : nat * nat) (toks : list (nat * nat)) (g : nat -> bv 8)
           (h : CpuId) (mc : regfile),
    0 < s0 -> s0 + Z.of_nat len < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    toks = done ++ tk :: rest ->
    (length toks < 10)%nat ->
    (forall (i : nat) (t : nat * nat), toks !! i = Some t ->
       (fst t <= len)%nat /\ (snd t <= len)%nat) ->
    mc !!! Regidx a5_idx
      = mword_of_int (p + 16 + 8 * Z.of_nat (length done)) ->
    shp_code γt -∗
    ushp_exec_at s0 p toks -∗
    ubytes γd s0 (S len) g -∗
    urun N h mc (mword_of_int 0x7fe) nn -∗
    (ushp_exec_at s0 p toks -∗
     ubytes γd s0 (S len) (ushp_nulfold (tk :: rest) g) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun N h' mc' (mword_of_int 0x81a) nn -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intro rest.
    induction rest as [| tk' rest IH ];
      intros done tk toks g h mc Hs0 Hs64 Hp0 Hp8 Hpsz Htoksd Htlen Hsnd Ha5;
      iIntros "#Hcode Hnode Hline Hrun Hcont".
    all: assert (Hlk : toks !! (length done) = Some tk)
      by (rewrite Htoksd; exact (ushp_lookup_app_mid' done tk _)).
    all: assert (Ht2 : (S (length done) <= length toks)%nat);
      [ rewrite Htoksd ushp_len_app_cons; lia | ].
    all: assert (Hdlen : (S (length done) < 10)%nat) by lia.
    all: assert (Hsndtk : (snd tk <= len)%nat)
      by exact (proj2 (Hsnd _ _ Hlk)).
    all: iDestruct "Hnode" as "(%Hnl & %Hnp & %Hna & Hty & Hav & Hev)".
    (* ---- 0x7fe  c.ld a4,72(a5) -- eargv[i] ---- *)
    all: iDestruct (ushp_slot_read s0 (p + 88) toks snd (length done)
                      ltac:(lia) with "Hev") as "[Hslot Hevc]".
    all: assert (Eslot : ushp_slot s0 (p + 88) toks snd (length done)
                         = uword γd (p + 88 + 8 * Z.of_nat (length done))
                             (mword_of_int (s0 + Z.of_nat (snd tk))))
      by (rewrite /ushp_slot Hlk; reflexivity).
    all: rewrite Eslot.
    all: iApply (wp_uk_cld N h mc (mword_of_int 0x7fe)
                   (mword_of_int 9 : mword 5) (mword_of_int 7 : mword 3)
                   (mword_of_int 6 : mword 3) a5_idx a4_idx
                   (p + 88 + 8 * Z.of_nat (length done))
                   (mword_of_int (s0 + Z.of_nat (snd tk))) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha5
                           (uint_moi (p + 16 + 8 * Z.of_nat (length done))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_c8; lia)
                   ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                   ltac:(vm_compute; discriminate)
                   with "[] Hslot Hrun");
      [ iApply (uis_shp_7fe with "Hcode") | ].
    all: iIntros "Hslot" (h1) "Hrun".
    all: iDestruct ("Hevc" with "Hslot") as "Hev".
    all: set (n1 := <[Regidx a4_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat (snd tk))
                            : mword 64)]> mc).
    all: assert (Hn1 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                   n1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a4_idx) (Regidx q) _ Hq)).
    all: assert (Ha4_1 : n1 !!! Regidx a4_idx
                         = mword_of_int (s0 + Z.of_nat (snd tk)))
      by exact (upd_eq mc (Regidx a4_idx)
                  (regval_into_reg
                     (mword_of_int (s0 + Z.of_nat (snd tk)) : mword 64))).
    (* ---- 0x800  sb zero,0(a4) -- THE NUL ---- *)
    all: iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    all: iDestruct (ushp_bytes_upd s0 (S len) g (snd tk) ubyte0
                      ltac:(lia) with "Hline") as "[Hb Hbc]".
    all: iApply (wp_uk_sb N h1 n1 (mword_of_int 0x800)
                   (mword_of_int 0 : mword 12) a4_idx x0_idx
                   (s0 + Z.of_nat (snd tk)) (g (snd tk)) nn
                   ltac:(rewrite Ha4_1
                           (uint_moi (s0 + Z.of_nat (snd tk))
                              ltac:(unfold Z64 in *; lia));
                         vm_compute uoff_i12; lia)
                   with "[] Hb Hrun");
      [ iApply (uis_shp_800 with "Hcode") | ].
    all: iIntros "Hb" (h2) "Hrun".
    all: rewrite Hx0.
    all: assert (Enb : nth_byte (zero_reg : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    all: rewrite Enb.
    all: iDestruct ("Hbc" with "Hb") as "Hline".
    (* ---- 0x804  c.addi a5,a5,8 ---- *)
    all: assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6)
                         : mword 64) = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    all: iApply (wp_uk_caddi N h2 n1 (mword_of_int 0x804)
                   (mword_of_int 8 : mword 6) a5_idx
                   (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)) nn
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hn1 a5_idx ltac:(vm_compute; discriminate))
                           Ha5 Esx8; symmetry; apply moi_add)
                   with "[] Hrun");
      [ iApply (uis_shp_804 with "Hcode") | ].
    all: iIntros (h3) "Hrun".
    all: set (n2 := <[Regidx a5_idx
                      := regval_into_reg
                           (mword_of_int
                              (p + 16 + 8 * Z.of_nat (length done) + 8)
                            : mword 64)]> n1).
    all: assert (Hn2 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                   n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx a5_idx) (Regidx q) _ Hq)).
    all: assert (Ha5_2 : n2 !!! Regidx a5_idx
                         = mword_of_int
                             (p + 16 + 8 * Z.of_nat (length done) + 8))
      by exact (upd_eq n1 (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int (p + 16 + 8 * Z.of_nat (length done) + 8)
                      : mword 64))).
    all: iDestruct (ushp_slot_read s0 (p + 8) toks fst
                      (S (length done)) ltac:(lia) with "Hav")
           as "[Hnx Havc]".
    - (* ======= the LAST token: argv[i+1] is the NULL cap ============== *)
      assert (Ecap : toks !! S (length done) = None)
        by (rewrite Htoksd ushp_lookup_app_past; reflexivity).
      assert (Ecl : (S (length done) = length toks)%nat).
      { rewrite Htoksd ushp_len_app_cons. cbn [length]. lia. }
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int 0)).
      { rewrite /ushp_slot Ecap (bool_decide_eq_true_2 _ Ecl). reflexivity. }
      rewrite Eslotn.
      (* ---- 0x806  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld N h3 n2 (mword_of_int 0x806)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int 0) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_806 with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx = (mword_of_int 0 : mword 64))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 0 : mword 64))).
      (* ---- 0x80a  c.bnez a4 -- NOT taken: the vector is capped ---- *)
      iApply (wp_uk_cbnez N h4 n3 (mword_of_int 0x80a)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx false (mword_of_int 0x7fe) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_80a with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x80c  c.j 0x81a ---- *)
      iApply (wp_uk_cj N h5 n3 (mword_of_int 0x80c)
                (mword_of_int 7 : mword 11) (mword_of_int 0x81a) nn
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_80c with "Hcode"). }
      iIntros (h6) "Hrun".
      iApply ("Hcont" with "[Hty Hav Hev] Hline [] Hrun").
      + rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ].
      + iPureIntro. intros r Hr.
        rewrite (Hn3 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn2 r (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)))
                (Hn1 r (ushp_cs_ne r a4_idx Hr
                          ltac:(vm_compute; reflexivity))).
        reflexivity.
    - (* ======= ANOTHER token: argv[i+1] points into the line ========== *)
      assert (Enx : toks !! S (length done) = Some tk')
        by (rewrite Htoksd; exact (ushp_lookup_app_next done tk tk' rest)).
      assert (Eslotn : ushp_slot s0 (p + 8) toks fst (S (length done))
                       = uword γd (p + 8 + 8 * Z.of_nat (S (length done)))
                           (mword_of_int (s0 + Z.of_nat (fst tk'))))
        by (rewrite /ushp_slot Enx; reflexivity).
      rewrite Eslotn.
      assert (Hfst' : (fst tk' <= len)%nat)
        by exact (proj1 (Hsnd _ _ Enx)).
      (* ---- 0x806  ld a4,-8(a5) ---- *)
      iApply (wp_uk_ld N h3 n2 (mword_of_int 0x806)
                (mword_of_int 4088 : mword 12) a5_idx a4_idx (DfracOwn 1)
                (p + 8 + 8 * Z.of_nat (S (length done)))
                (mword_of_int (s0 + Z.of_nat (fst tk'))) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Ha5_2
                        (uint_moi (p + 16 + 8 * Z.of_nat (length done) + 8)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (S (length done)) Hp8))
                ltac:(vm_compute; discriminate)
                with "[] Hnx Hrun").
      { iApply (uis_shp_806 with "Hcode"). }
      iIntros "Hnx" (h4) "Hrun".
      iDestruct ("Havc" with "Hnx") as "Hav".
      set (n3 := <[Regidx a4_idx
                   := regval_into_reg
                        (mword_of_int (s0 + Z.of_nat (fst tk'))
                         : mword 64)]> n2).
      assert (Hn3 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                 n3 !!! Regidx q = n2 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n2 (Regidx a4_idx) (Regidx q) _ Hq)).
      assert (Ha4_3 : n3 !!! Regidx a4_idx
                      = mword_of_int (s0 + Z.of_nat (fst tk')))
        by exact (upd_eq n2 (Regidx a4_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat (fst tk'))
                        : mword 64))).
      (* ---- 0x80a  c.bnez a4 -- TAKEN: the line's address is not 0 ---- *)
      iApply (wp_uk_cbnez N h4 n3 (mword_of_int 0x80a)
                (mword_of_int 250 : mword 8) (mword_of_int 6 : mword 3)
                a4_idx true (mword_of_int 0x7fe) nn
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha4_3;
                      assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Ezr;
                      rewrite (moi_neq_vec (s0 + Z.of_nat (fst tk')) 0
                                 ltac:(unfold Z64 in *; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hnz : (s0 + Z.of_nat (fst tk') =? 0) = false)
                        by (apply Z.eqb_neq; lia);
                      rewrite Hnz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_80a with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply (IH (done ++ [tk]) tk' toks (ushp_setb g (snd tk) ubyte0) h5 n3
                Hs0 Hs64 Hp0 Hp8 Hpsz
                ltac:(rewrite Htoksd; symmetry; apply ushp_app_cons)
                Htlen Hsnd
                ltac:(rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate))
                        Ha5_2 ushp_len_app1; f_equal;
                      rewrite Nat2Z.inj_succ; lia)
                with "Hcode [Hty Hav Hev] Hline Hrun").
      { rewrite /ushp_exec_at.
        iSplitR; [ iPureIntro; exact Hnl | ].
        iSplitR; [ iPureIntro; exact Hnp | ].
        iSplitR; [ iPureIntro; exact Hna | ].
        iSplitL "Hty"; [ iExact "Hty" | ].
        iSplitL "Hav"; [ iExact "Hav" | iExact "Hev" ]. }
      iIntros "Hnode Hline" (hf mf) "%Hpres Hrun".
      iApply ("Hcont" with "Hnode Hline [] Hrun").
      iPureIntro. intros r Hr.
      rewrite (Hpres r Hr)
              (Hn3 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn2 r (ushp_cs_ne r a5_idx Hr ltac:(vm_compute; reflexivity)))
              (Hn1 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity))).
      reflexivity.
  Qed.


  (* ---- the common landing, 0x81a..0x824 -------------------------------- *)
  (* Both ways out of the switch -- the empty argument vector and the loop's
     exit -- arrive here, so the [c.mv a0,s1] and the epilogue are one
     lemma rather than two copies. *)
  Lemma wp_kshp_nul_fin (sp0 spl : mword 64) (vals : nat -> mword 64)
      (p : Z) (nn : nat) (h : CpuId) (me : regfile) :
    uint sp0 mod 8 = 0 -> 32 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 24 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)) ->
    me !!! Regidx s1_idx = mword_of_int p ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 1 -∗
    urun N h me (mword_of_int 0x81a) nn -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] vals
               (<[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> me)))
         (ret_pc (vals 0%nat)) (4 + nn) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hal8 Hlo Hhi Hsplu Hsp Hs1.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    iApply (wp_uk_cmv N h me (mword_of_int 0x81a) a0_idx s1_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_81a with "Hcode"). }
    iIntros (h1) "Hrun".
    set (mz := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> me).
    assert (Hspz : mz !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne me (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp. }
    iApply (wp_kshp_frame_epi 4 1 [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] (mword_of_int 3 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x81c | 1%nat => 0x81e
                              | 2%nat => 0x820 | _ => 0x822 end)
              (mword_of_int 2 : mword 6) sp0 spl vals nn h1 mz
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(cbn [length]; lia)
              Hspz
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_81c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_81e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_820 with "Hcode") | done ]. }
    { iApply (uis_shp_822 with "Hcode"). }
    { iApply (uis_shp_824 with "Hcode"). }
    iIntros (hf) "Hrun". iApply ("Hcont" $! hf with "Hrun").
  Qed.



  (* the line as a byte run: [len] body bytes and the terminator *)
  Definition ushp_ext (len : nat) (f : nat -> bv 8) : nat -> bv 8 :=
    fun j => if bool_decide (j < len)%nat then f j else ubyte0.

  Lemma ushp_ustr_bytes (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd (DfracOwn 1) a len f -∗ ubytes γd a (S len) (ushp_ext len f).
  Proof using .
    iIntros "(_ & _ & Hbs & Hnul)".
    assert (ES : S len = (len + 1)%nat) by lia.
    rewrite ES (ubytes_app γd a len 1 (ushp_ext len f)).
    iSplitL "Hbs".
    - iApply (ushp_ubytes_ext a len f (ushp_ext len f) with "Hbs").
      intros j Hj. rewrite /ushp_ext (bool_decide_eq_true_2 _ Hj).
      reflexivity.
    - rewrite /ubytes /ubytesq. cbn [seq].
      rewrite big_sepL_cons big_sepL_nil.
      iSplitL; [ | done ].
      assert (Ez : a + Z.of_nat len + Z.of_nat 0 = a + Z.of_nat len) by lia.
      rewrite Ez.
      assert (Eh : ushp_ext len f (len + 0)%nat = ubyte0).
      { rewrite /ushp_ext
          (bool_decide_eq_false_2 (len + 0 < len)%nat ltac:(lia)).
        reflexivity. }
      rewrite Eh. iExact "Hnul".
  Qed.



  (* the NUL-cut, as a fact about the bytes: every write the loop makes is a
     zero, so a byte it has zeroed stays zero *)
  Lemma ushp_nulfold_keep (toks : list (nat * nat)) (g : nat -> bv 8)
      (j : nat) :
    g j = ubyte0 -> ushp_nulfold toks g j = ubyte0.
  Proof using .
    revert g. induction toks as [| tk r IH ]; intros g Hg;
      cbn [ushp_nulfold]; [ exact Hg | ].
    apply IH. rewrite /ushp_setb.
    destruct (Nat.eqb j (snd tk)); [ reflexivity | exact Hg ].
  Qed.

  Lemma ushp_nulfold_hit (toks : list (nat * nat)) (g : nat -> bv 8)
      (i : nat) (tk : nat * nat) :
    toks !! i = Some tk -> ushp_nulfold toks g (snd tk) = ubyte0.
  Proof using .
    revert g i. induction toks as [| t r IH ]; intros g i Hi;
      [ rewrite lookup_nil in Hi; discriminate | ].
    destruct i as [| i ]; cbn in Hi.
    - injection Hi as <-. cbn [ushp_nulfold]. apply ushp_nulfold_keep.
      rewrite /ushp_setb Nat.eqb_refl. reflexivity.
    - cbn [ushp_nulfold]. exact (IH _ i Hi).
  Qed.


End UkShParseCmd.
