(* UCodeEcho.v -- the CODE CATALOG of the user program [echo].

   The verified-user tier (claude-notes/projects/user-verified.md,
   claude-notes/projects/user-echo.md) drives one step from one [uinstr] fact
   (UmodeMem.v): the pure statement that at a given user pc the program's
   bytes sit in the process image [M], the pc's page is mapped fetch-
   executable, and the fetched word decodes to a named AST on any U-mode
   machine.  This file proves those facts for the 73 instructions of the five
   functions [echo] actually executes, from the dumped image
   [User.EchoInstrs.echo_bytes].

   Two premises carry every [uinstr] lemma:

     [echo_text_sub M]   -- [M] contains the dumped text (so a proof may talk
                            about a process image that ALSO has rodata, bss,
                            a stack page and an argument area in it);
     [echo_layout pt]    -- the pure page-table fact.  Unlike [sync], echo
                            makes TWO claims about its text page: it is
                            mapped fetch-executable AND load-readable, because
                            echo's two rodata strings live on it (page 0) and
                            are handed to [write] as buffers.  Every pc below
                            is < 0x400 and both strings are < 0x1000, hence
                            all on that one page; the [svpn_of]
                            identifications are per-instance [vm_compute]s.
                            Stack and argv facts ride in the function specs,
                            not here.

   The disassembly (objdump on xv6-riscv/user/_echo; EchoSyms.main = 0x0,
   start = 0x7c, strlen = 0xdc, exit = 0x332, write = 0x352):

     <main> @0x0
        0:  7139        c.addi16sp sp,-64
        2:  fc06        c.sdsp    ra,56(sp)
        4:  f822        c.sdsp    s0,48(sp)
        6:  f426        c.sdsp    s1,40(sp)
        8:  f04a        c.sdsp    s2,32(sp)
        a:  ec4e        c.sdsp    s3,24(sp)
        c:  e852        c.sdsp    s4,16(sp)
        e:  e456        c.sdsp    s5,8(sp)
       10:  e05a        c.sdsp    s6,0(sp)
       12:  0080        c.addi4spn s0,sp,64
       14:  4785        c.li      a5,1
       16:  06a7d063    bge       a5,a0,0x76
       1a:  00858493    addi      s1,a1,8
       1e:  3579        c.addiw   a0,a0,-2
       20:  02051793    slli      a5,a0,0x20
       24:  01d7d513    srli      a0,a5,0x1d
       28:  00a48ab3    add       s5,s1,a0
       2c:  05c1        c.addi    a1,a1,16
       2e:  00a58a33    add       s4,a1,a0
       32:  4985        c.li      s3,1
       34:  00001b17    auipc     s6,0x1
       38:  8fcb0b13    addi      s6,s6,-1796      (s6 = 0x930, the " " string)
       3c:  a809        c.j       0x4e
       3e:  864e        c.mv      a2,s3
       40:  85da        c.mv      a1,s6
       42:  854e        c.mv      a0,s3
       44:  30e000ef    jal       ra,0x352 <write>
       48:  04a1        c.addi    s1,s1,8
       4a:  03448663    beq       s1,s4,0x76
       4e:  0004b903    ld        s2,0(s1)
       52:  854a        c.mv      a0,s2
       54:  088000ef    jal       ra,0xdc <strlen>
       58:  862a        c.mv      a2,a0
       5a:  85ca        c.mv      a1,s2
       5c:  854e        c.mv      a0,s3
       5e:  2f4000ef    jal       ra,0x352 <write>
       62:  fd549ee3    bne       s1,s5,0x3e
       66:  4605        c.li      a2,1
       68:  00001597    auipc     a1,0x1
       6c:  8d058593    addi      a1,a1,-1840      (a1 = 0x938, the "\n" string)
       70:  8532        c.mv      a0,a2
       72:  2e0000ef    jal       ra,0x352 <write>
       76:  4501        c.li      a0,0
       78:  2ba000ef    jal       ra,0x332 <exit>
     <start> @0x7c
       7c:  1141        c.addi    sp,sp,-16
       7e:  e406        c.sdsp    ra,8(sp)
       80:  e022        c.sdsp    s0,0(sp)
       82:  0800        c.addi4spn s0,sp,16
       84:  f7dff0ef    jal       ra,0x0 <main>
       88:  2aa000ef    jal       ra,0x332 <exit>
     <strlen> @0xdc
       dc:  1141        c.addi    sp,sp,-16
       de:  e406        c.sdsp    ra,8(sp)
       e0:  e022        c.sdsp    s0,0(sp)
       e2:  0800        c.addi4spn s0,sp,16
       e4:  00054783    lbu       a5,0(a0)
       e8:  cf91        c.beqz    a5,0x104
       ea:  00150793    addi      a5,a0,1
       ee:  86be        c.mv      a3,a5
       f0:  0785        c.addi    a5,a5,1
       f2:  fff7c703    lbu       a4,-1(a5)
       f6:  ff65        c.bnez    a4,0xee
       f8:  40a6853b    subw      a0,a3,a0
       fc:  60a2        c.ldsp    ra,8(sp)
       fe:  6402        c.ldsp    s0,0(sp)
      100:  0141        c.addi    sp,sp,16
      102:  8082        c.jr      ra
      104:  4501        c.li      a0,0
      106:  bfdd        c.j       0xfc
     <exit> @0x332
      332:  4889        c.li      a7,2
      334:  00000073    ecall              (the c.jr at 0x338 is dead code)
     <write> @0x352
      352:  48c1        c.li      a7,16
      354:  00000073    ecall
      358:  8082        c.jr      ra

   NOT catalogued, because never decoded: [main]'s register-restore epilogue
   from 0x7a on (the [jal ra,0x332 <exit>] at 0x78 diverges, so main never
   returns), and [exit]'s [c.jr ra] at 0x338 (same reason, one level down).
   [start]'s tail past 0x88 is dead for the same reason.

   Every AST below was READ OFF the model -- [vm_compute] of the decoder at
   the U-mode reference state [dstateU] (base) / [decode_c_pure] under the
   misa.C gate (compressed) -- never guessed.  In particular every jal/branch
   immediate is the decoder's POSITIVE residue: the backwards [jal ra,0x0]
   at 0x84 is 2097020 = 2^21 - 132, [bne]'s at 0x62 is 8156 = 2^13 - 36, and
   [c.bnez]'s at 0xf6 is 252 = 2^8 - 4 (a compressed branch immediate counts
   HALFwords).  The compressed words decode to the raw C_* constructors --
   the expansion into ITYPE/STORE/... happens in [execute], not here. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import UserPtTree.
Require Import WpDecodeBridge DecodeTotalU WpRvcBridge.
Require Import UmodeMem UmodeAbi.
From User Require EchoInstrs EchoData EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 The image and the layout premise.                                   *)
(* ===================================================================== *)

(* [M] contains the dumped text -- the generic image inclusion (UmodeAbi.v)
   at this program's text bytes.  An inclusion (not an equality), so a
   process image carrying rodata/bss/stack/argv on top still qualifies. *)
Definition echo_text_sub (M : gmap Z (bv 8)) : Prop :=
  uimg_sub EchoInstrs.echo_bytes M.

(* ... and the dumped RODATA.  echo's text image stops at 0x92b; the two
   string literals [" "] @0x930 and ["\n"] @0x938 that [main] hands to
   [write] are in [echo_data], so the readable-window lemma below needs THIS
   inclusion, not [echo_text_sub].  (They still share page 0 with the text,
   which is why one layout leaf serves both.) *)
Definition echo_data_sub (M : gmap Z (bv 8)) : Prop :=
  uimg_sub EchoData.echo_data M.

(* ... and the two together, so a spec carries ONE image premise.  The per-pc
   [uinstr] facts below deliberately take only [echo_text_sub]: an
   instruction fetch never reads the data half. *)
Definition echo_img_sub (M : gmap Z (bv 8)) : Prop :=
  echo_text_sub M /\ echo_data_sub M.

Lemma echo_img_text (M : gmap Z (bv 8)) : echo_img_sub M -> echo_text_sub M.
Proof. intros [ H _ ]. exact H. Qed.
Lemma echo_img_data (M : gmap Z (bv 8)) : echo_img_sub M -> echo_data_sub M.
Proof. intros [ _ H ]. exact H. Qed.

(* ---- the KEY RANGE of each dumped map ------------------------------- *)
(* Both halves of the image live on page 0 (text keys stop at 0x92a, data
   keys at 0xdcc), which is what lets a caller carry an inclusion across a
   frame store: [UmodeAbi.uM_only_img] wants exactly "the written window is
   disjoint from every key of [img]", and a stack store is at >= 4096. *)

Lemma list_key_lt {A : Type} (L : list (Z * A)) (B k : Z) (b : A) :
  forallb (fun kv => Z.ltb (fst kv) B) L = true -> In (k, b) L -> k < B.
Proof.
  induction L as [ | x xs IH ]; cbn [forallb In]; [ tauto | ].
  intros HF [ Hx | Hin ].
  - apply andb_prop in HF as [ H1 _ ]. subst x. cbn in H1.
    apply Z.ltb_lt in H1. exact H1.
  - apply andb_prop in HF as [ _ H2 ]. exact (IH H2 Hin).
Qed.

Lemma echo_bytes_key_lt (k : Z) (b : bv 8) :
  EchoInstrs.echo_bytes !! k = Some b -> k < 4096.
Proof.
  intro Hk.
  apply elem_of_list_to_map_2 in Hk.
  apply elem_of_list_In in Hk.
  refine (list_key_lt _ 4096 k b _ Hk).
  vm_compute. reflexivity.
Qed.

Lemma echo_data_key_lt (k : Z) (b : bv 8) :
  EchoData.echo_data !! k = Some b -> k < 4096.
Proof.
  intro Hk.
  apply elem_of_list_to_map_2 in Hk.
  apply elem_of_list_In in Hk.
  refine (list_key_lt _ 4096 k b _ Hk).
  vm_compute. reflexivity.
Qed.

(* The pure page-table premise.  TWO claims about the text page (the vpn of
   va 0, i.e. page 0, which carries all of echo's text AND its rodata):
   mapped with a leaf that permits instruction fetch, and with one that
   permits a user data LOAD.  The second is what makes the rodata strings
   legal [write] buffers ([uv_rd], UmodeAbi.v). *)
Record echo_layout (pt : uptd) : Prop := EchoLayout {
  el_text : exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int 0 : mword 64) = Some w /\
      uleaf_ok (InstructionFetch tt) w /\
      uleaf_ok (Load Data) w
}.

(* Every pc in this file is on the text page; the identification of its vpn
   with the text page's is one [vm_compute] per instance. *)
Lemma echo_layout_fetch (pt : uptd) (off : Z) :
  echo_layout pt ->
  svpn_of (mword_of_int off : mword 64) = svpn_of (mword_of_int 0 : mword 64) ->
  uva_fetch_leaf pt (mword_of_int off).
Proof.
  intros [ (w & Hl & Hok & _) ] Heq. exists w. rewrite Heq. split; assumption.
Qed.

(* the same leaf, in the shape [uv_rd]'s [urd_leaf] field wants *)
Lemma echo_layout_load (pt : uptd) (a : Z) :
  echo_layout pt ->
  svpn_of (mword_of_int a : mword 64) = svpn_of (mword_of_int 0 : mword 64) ->
  exists w : mword 64,
    ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\
    uleaf_ok (Load Data) w.
Proof.
  intros [ (w & Hl & _ & Hok) ] Heq. exists w. rewrite Heq. split; assumption.
Qed.

(* ONE readable byte of page-0 rodata -- the address is a parameter, so the
   two strings are two instances (and a future one costs a line). *)
Lemma echo_rodata_rd1 (pt : uptd) (M : gmap Z (bv 8)) (a : Z) (b : bv 8) :
  echo_layout pt -> echo_data_sub M ->
  0 <= a < 4096 ->
  svpn_of (mword_of_int a : mword 64) = svpn_of (mword_of_int 0 : mword 64) ->
  EchoData.echo_data !! a = Some b ->
  uv_rd pt M a 1.
Proof.
  intros Hl Hsub Ha Hvpn Hb. constructor.
  - lia.
  - lia.
  - change (2 ^ 38) with 274877906944. lia.
  - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.
    rewrite Z.add_0_r. exact (echo_layout_load pt a Hl Hvpn).
  - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.
    rewrite Z.add_0_r. exists b. exact (Hsub a b Hb).
Qed.

(* the two [write] buffers: [" "] @0x930 and ["\n"] @0x938 *)
Lemma echo_rodata_rd (pt : uptd) (M : gmap Z (bv 8)) :
  echo_layout pt -> echo_data_sub M ->
  uv_rd pt M 0x930 1 /\ uv_rd pt M 0x938 1.
Proof.
  intros Hl Hsub. split.
  - apply (echo_rodata_rd1 pt M 0x930 (Z_to_bv 8 0x20) Hl Hsub).
    + lia.
    + apply bv_eq; vm_compute; reflexivity.
    + vm_compute; f_equal; apply bv_eq; reflexivity.
  - apply (echo_rodata_rd1 pt M 0x938 (Z_to_bv 8 0x0a) Hl Hsub).
    + lia.
    + apply bv_eq; vm_compute; reflexivity.
    + vm_compute; f_equal; apply bv_eq; reflexivity.
Qed.

(* the addresses this file is about, as the dumper named them *)
Lemma echo_syms_pins :
  EchoSyms.main = 0x0 /\ EchoSyms.start = 0x7c /\ EchoSyms.strlen = 0xdc /\
  EchoSyms.exit = 0x332 /\ EchoSyms.write = 0x352.
Proof.
  unfold EchoSyms.main, EchoSyms.start, EchoSyms.strlen,
         EchoSyms.exit, EchoSyms.write.
  split_and!; reflexivity.
Qed.

(* ===================================================================== *)
(* §1 Per-WORD decode facts.                                              *)
(*                                                                        *)
(* One lemma per DISTINCT word (65 of them for 73 instructions), reused at *)
(* every pc where that word occurs.                                       *)
(*                                                                        *)
(* Base words: the concrete-state bridge at [dstateU] (WpDecodeBridge),    *)
(* transported to any state agreeing with it on the U-mode decode read set *)
(* [D_u] -- exactly the [udecode_base] shape [uinstr] wants.  The closing  *)
(* step descends the AST with [f_equal] and finishes each bitvector leaf   *)
(* with [bv_eq] (a bare [reflexivity] would have to match well-formedness  *)
(* proof terms).                                                          *)
(*                                                                        *)
(* Compressed words: [rvc_oneshot] under the misa.C premise.               *)
(* ===================================================================== *)

Ltac udec_base_bridge :=
  let s := fresh "s" in let Hag := fresh "Hag" in
  intros s Hag;
  apply (decode_state_bridge D_u _ dstateU);
  [ exact Hag
  | vm_compute; reflexivity
  | vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ] ].

Ltac udec_rvc_oneshot :=
  let s := fresh "s" in let Hm := fresh "Hm" in intros s Hm; rvc_oneshot s Hm.

(* ---- compressed ---- *)
(* 7139  c.addi16sp sp,-64 *)
Lemma udec_7139 :
  udecode_rvc (mword_of_int 0x7139) (C_ADDI16SP (mword_of_int 60 : mword 6)).
Proof. udec_rvc_oneshot. Qed.

(* fc06  c.sdsp ra,56(sp) *)
Lemma udec_fc06 :
  udecode_rvc (mword_of_int 0xfc06) (C_SDSP (mword_of_int 7 : mword 6, Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* f822  c.sdsp s0,48(sp) *)
Lemma udec_f822 :
  udecode_rvc (mword_of_int 0xf822) (C_SDSP (mword_of_int 6 : mword 6, Regidx (mword_of_int 8))).
Proof. udec_rvc_oneshot. Qed.

(* f426  c.sdsp s1,40(sp) *)
Lemma udec_f426 :
  udecode_rvc (mword_of_int 0xf426) (C_SDSP (mword_of_int 5 : mword 6, Regidx (mword_of_int 9))).
Proof. udec_rvc_oneshot. Qed.

(* f04a  c.sdsp s2,32(sp) *)
Lemma udec_f04a :
  udecode_rvc (mword_of_int 0xf04a) (C_SDSP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18))).
Proof. udec_rvc_oneshot. Qed.

(* ec4e  c.sdsp s3,24(sp) *)
Lemma udec_ec4e :
  udecode_rvc (mword_of_int 0xec4e) (C_SDSP (mword_of_int 3 : mword 6, Regidx (mword_of_int 19))).
Proof. udec_rvc_oneshot. Qed.

(* e852  c.sdsp s4,16(sp) *)
Lemma udec_e852 :
  udecode_rvc (mword_of_int 0xe852) (C_SDSP (mword_of_int 2 : mword 6, Regidx (mword_of_int 20))).
Proof. udec_rvc_oneshot. Qed.

(* e456  c.sdsp s5,8(sp) *)
Lemma udec_e456 :
  udecode_rvc (mword_of_int 0xe456) (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 21))).
Proof. udec_rvc_oneshot. Qed.

(* e05a  c.sdsp s6,0(sp) *)
Lemma udec_e05a :
  udecode_rvc (mword_of_int 0xe05a) (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 22))).
Proof. udec_rvc_oneshot. Qed.

(* e406  c.sdsp ra,8(sp) *)
Lemma udec_e406 :
  udecode_rvc (mword_of_int 0xe406) (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* e022  c.sdsp s0,0(sp) *)
Lemma udec_e022 :
  udecode_rvc (mword_of_int 0xe022) (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
Proof. udec_rvc_oneshot. Qed.

(* 0080  c.addi4spn s0,sp,64 *)
Lemma udec_0080 :
  udecode_rvc (mword_of_int 0x0080) (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 16 : mword 8)).
Proof. udec_rvc_oneshot. Qed.

(* 0800  c.addi4spn s0,sp,16 *)
Lemma udec_0800 :
  udecode_rvc (mword_of_int 0x0800) (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
Proof. udec_rvc_oneshot. Qed.

(* 1141  c.addi sp,sp,-16 *)
Lemma udec_1141 :
  udecode_rvc (mword_of_int 0x1141) (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
Proof. udec_rvc_oneshot. Qed.

(* 0141  c.addi sp,sp,16 *)
Lemma udec_0141 :
  udecode_rvc (mword_of_int 0x0141) (C_ADDI (mword_of_int 16 : mword 6, Regidx (mword_of_int 2))).
Proof. udec_rvc_oneshot. Qed.

(* 05c1  c.addi a1,a1,16 *)
Lemma udec_05c1 :
  udecode_rvc (mword_of_int 0x05c1) (C_ADDI (mword_of_int 16 : mword 6, Regidx (mword_of_int 11))).
Proof. udec_rvc_oneshot. Qed.

(* 04a1  c.addi s1,s1,8 *)
Lemma udec_04a1 :
  udecode_rvc (mword_of_int 0x04a1) (C_ADDI (mword_of_int 8 : mword 6, Regidx (mword_of_int 9))).
Proof. udec_rvc_oneshot. Qed.

(* 0785  c.addi a5,a5,1 *)
Lemma udec_0785 :
  udecode_rvc (mword_of_int 0x0785) (C_ADDI (mword_of_int 1 : mword 6, Regidx (mword_of_int 15))).
Proof. udec_rvc_oneshot. Qed.

(* 3579  c.addiw a0,a0,-2 *)
Lemma udec_3579 :
  udecode_rvc (mword_of_int 0x3579) (C_ADDIW (mword_of_int 62 : mword 6, Regidx (mword_of_int 10))).
Proof. udec_rvc_oneshot. Qed.

(* 4785  c.li a5,1 *)
Lemma udec_4785 :
  udecode_rvc (mword_of_int 0x4785) (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 15))).
Proof. udec_rvc_oneshot. Qed.

(* 4985  c.li s3,1 *)
Lemma udec_4985 :
  udecode_rvc (mword_of_int 0x4985) (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 19))).
Proof. udec_rvc_oneshot. Qed.

(* 4605  c.li a2,1 *)
Lemma udec_4605 :
  udecode_rvc (mword_of_int 0x4605) (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 12))).
Proof. udec_rvc_oneshot. Qed.

(* 4501  c.li a0,0 *)
Lemma udec_4501 :
  udecode_rvc (mword_of_int 0x4501) (C_LI (mword_of_int 0 : mword 6, Regidx (mword_of_int 10))).
Proof. udec_rvc_oneshot. Qed.

(* 4889  c.li a7,2   (SYS_exit) *)
Lemma udec_4889 :
  udecode_rvc (mword_of_int 0x4889) (C_LI (mword_of_int 2 : mword 6, Regidx (mword_of_int 17))).
Proof. udec_rvc_oneshot. Qed.

(* 48c1  c.li a7,16  (SYS_write) *)
Lemma udec_48c1 :
  udecode_rvc (mword_of_int 0x48c1) (C_LI (mword_of_int 16 : mword 6, Regidx (mword_of_int 17))).
Proof. udec_rvc_oneshot. Qed.

(* 864e  c.mv a2,s3 *)
Lemma udec_864e :
  udecode_rvc (mword_of_int 0x864e) (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 19))).
Proof. udec_rvc_oneshot. Qed.

(* 85da  c.mv a1,s6 *)
Lemma udec_85da :
  udecode_rvc (mword_of_int 0x85da) (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 22))).
Proof. udec_rvc_oneshot. Qed.

(* 854e  c.mv a0,s3 *)
Lemma udec_854e :
  udecode_rvc (mword_of_int 0x854e) (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 19))).
Proof. udec_rvc_oneshot. Qed.

(* 862a  c.mv a2,a0 *)
Lemma udec_862a :
  udecode_rvc (mword_of_int 0x862a) (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 10))).
Proof. udec_rvc_oneshot. Qed.

(* 85ca  c.mv a1,s2 *)
Lemma udec_85ca :
  udecode_rvc (mword_of_int 0x85ca) (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 18))).
Proof. udec_rvc_oneshot. Qed.

(* 854a  c.mv a0,s2 *)
Lemma udec_854a :
  udecode_rvc (mword_of_int 0x854a) (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 18))).
Proof. udec_rvc_oneshot. Qed.

(* 8532  c.mv a0,a2 *)
Lemma udec_8532 :
  udecode_rvc (mword_of_int 0x8532) (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 12))).
Proof. udec_rvc_oneshot. Qed.

(* 86be  c.mv a3,a5 *)
Lemma udec_86be :
  udecode_rvc (mword_of_int 0x86be) (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 15))).
Proof. udec_rvc_oneshot. Qed.

(* a809  c.j 0x4e   (+0x12) *)
Lemma udec_a809 :
  udecode_rvc (mword_of_int 0xa809) (C_J (mword_of_int 9 : mword 11)).
Proof. udec_rvc_oneshot. Qed.

(* bfdd  c.j 0xfc   (-0xa; 2^11-5) *)
Lemma udec_bfdd :
  udecode_rvc (mword_of_int 0xbfdd) (C_J (mword_of_int 2043 : mword 11)).
Proof. udec_rvc_oneshot. Qed.

(* cf91  c.beqz a5,0x104  (+0x1c) *)
Lemma udec_cf91 :
  udecode_rvc (mword_of_int 0xcf91) (C_BEQZ (mword_of_int 14 : mword 8, Cregidx (mword_of_int 7))).
Proof. udec_rvc_oneshot. Qed.

(* ff65  c.bnez a4,0xee   (-0x8; 2^8-4) *)
Lemma udec_ff65 :
  udecode_rvc (mword_of_int 0xff65) (C_BNEZ (mword_of_int 252 : mword 8, Cregidx (mword_of_int 6))).
Proof. udec_rvc_oneshot. Qed.

(* 60a2  c.ldsp ra,8(sp) *)
Lemma udec_60a2 :
  udecode_rvc (mword_of_int 0x60a2) (C_LDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* 6402  c.ldsp s0,0(sp) *)
Lemma udec_6402 :
  udecode_rvc (mword_of_int 0x6402) (C_LDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
Proof. udec_rvc_oneshot. Qed.

(* 8082  c.jr ra *)
Lemma udec_8082 :
  udecode_rvc (mword_of_int 0x8082) (C_JR (Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* ---- base ---- *)
(* 06a7d063  bge a5,a0,0x76   (0x16 -> +0x60) *)
Lemma udec_06a7d063 :
  udecode_base (mword_of_int 0x06a7d063) (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 10), Regidx (mword_of_int 15), BGE)).
Proof. udec_base_bridge. Qed.

(* 03448663  beq s1,s4,0x76   (0x4a -> +0x2c) *)
Lemma udec_03448663 :
  udecode_base (mword_of_int 0x03448663) (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 9), BEQ)).
Proof. udec_base_bridge. Qed.

(* fd549ee3  bne s1,s5,0x3e   (0x62 -> -0x24; 2^13-36) *)
Lemma udec_fd549ee3 :
  udecode_base (mword_of_int 0xfd549ee3) (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BNE)).
Proof. udec_base_bridge. Qed.

(* 00858493  addi s1,a1,8 *)
Lemma udec_00858493 :
  udecode_base (mword_of_int 0x00858493) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), ADDI)).
Proof. udec_base_bridge. Qed.

(* 00150793  addi a5,a0,1 *)
Lemma udec_00150793 :
  udecode_base (mword_of_int 0x00150793) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).
Proof. udec_base_bridge. Qed.

(* 8fcb0b13  addi s6,s6,-1796  (2^12-1796) *)
Lemma udec_8fcb0b13 :
  udecode_base (mword_of_int 0x8fcb0b13) (ITYPE (mword_of_int 2300 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADDI)).
Proof. udec_base_bridge. Qed.

(* 8d058593  addi a1,a1,-1840  (2^12-1840) *)
Lemma udec_8d058593 :
  udecode_base (mword_of_int 0x8d058593) (ITYPE (mword_of_int 2256 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
Proof. udec_base_bridge. Qed.

(* 02051793  slli a5,a0,0x20 *)
Lemma udec_02051793 :
  udecode_base (mword_of_int 0x02051793) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)).
Proof. udec_base_bridge. Qed.

(* 01d7d513  srli a0,a5,0x1d *)
Lemma udec_01d7d513 :
  udecode_base (mword_of_int 0x01d7d513) (SHIFTIOP (mword_of_int 29 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SRLI)).
Proof. udec_base_bridge. Qed.

(* 00a48ab3  add s5,s1,a0 *)
Lemma udec_00a48ab3 :
  udecode_base (mword_of_int 0x00a48ab3) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 21), ADD)).
Proof. udec_base_bridge. Qed.

(* 00a58a33  add s4,a1,a0 *)
Lemma udec_00a58a33 :
  udecode_base (mword_of_int 0x00a58a33) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 11), Regidx (mword_of_int 20), ADD)).
Proof. udec_base_bridge. Qed.

(* 40a6853b  subw a0,a3,a0 *)
Lemma udec_40a6853b :
  udecode_base (mword_of_int 0x40a6853b) (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 13), Regidx (mword_of_int 10), SUBW)).
Proof. udec_base_bridge. Qed.

(* 00001b17  auipc s6,0x1 *)
Lemma udec_00001b17 :
  udecode_base (mword_of_int 0x00001b17) (UTYPE (mword_of_int 1 : mword 20, Regidx (mword_of_int 22), AUIPC)).
Proof. udec_base_bridge. Qed.

(* 00001597  auipc a1,0x1 *)
Lemma udec_00001597 :
  udecode_base (mword_of_int 0x00001597) (UTYPE (mword_of_int 1 : mword 20, Regidx (mword_of_int 11), AUIPC)).
Proof. udec_base_bridge. Qed.

(* 30e000ef  jal ra,0x352 <write>  (0x44 -> +0x30e) *)
Lemma udec_30e000ef :
  udecode_base (mword_of_int 0x30e000ef) (JAL (mword_of_int 782 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 088000ef  jal ra,0xdc <strlen>  (0x54 -> +0x88) *)
Lemma udec_088000ef :
  udecode_base (mword_of_int 0x088000ef) (JAL (mword_of_int 136 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2f4000ef  jal ra,0x352 <write>  (0x5e -> +0x2f4) *)
Lemma udec_2f4000ef :
  udecode_base (mword_of_int 0x2f4000ef) (JAL (mword_of_int 756 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2e0000ef  jal ra,0x352 <write>  (0x72 -> +0x2e0) *)
Lemma udec_2e0000ef :
  udecode_base (mword_of_int 0x2e0000ef) (JAL (mword_of_int 736 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2ba000ef  jal ra,0x332 <exit>   (0x78 -> +0x2ba) *)
Lemma udec_2ba000ef :
  udecode_base (mword_of_int 0x2ba000ef) (JAL (mword_of_int 698 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* f7dff0ef  jal ra,0x0 <main>     (0x84 -> -0x84; 2^21-132) *)
Lemma udec_f7dff0ef :
  udecode_base (mword_of_int 0xf7dff0ef) (JAL (mword_of_int 2097020 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2aa000ef  jal ra,0x332 <exit>   (0x88 -> +0x2aa) *)
Lemma udec_2aa000ef :
  udecode_base (mword_of_int 0x2aa000ef) (JAL (mword_of_int 682 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 0004b903  ld s2,0(s1) *)
Lemma udec_0004b903 :
  udecode_base (mword_of_int 0x0004b903) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), false, 8)).
Proof. udec_base_bridge. Qed.

(* 00054783  lbu a5,0(a0) *)
Lemma udec_00054783 :
  udecode_base (mword_of_int 0x00054783) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), true, 1)).
Proof. udec_base_bridge. Qed.

(* fff7c703  lbu a4,-1(a5)  (2^12-1) *)
Lemma udec_fff7c703 :
  udecode_base (mword_of_int 0xfff7c703) (LOAD (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), true, 1)).
Proof. udec_base_bridge. Qed.

(* 00000073  ecall *)
Lemma udec_00000073 :
  udecode_base (mword_of_int 0x00000073) (ECALL tt).
Proof. udec_base_bridge. Qed.

(* ===================================================================== *)
(* §2 Per-PC [uinstr] facts.                                              *)
(*                                                                        *)
(* Shared shape: [ui_al2]/[ui_canon]/[ui_inpage] are [vm_compute]s on the  *)
(* concrete pc, [ui_leaf] comes from [echo_layout] through the svpn        *)
(* identification, and each byte of [ui_code]'s window is a concrete       *)
(* [echo_bytes] lookup transported by [echo_text_sub].                     *)
(*                                                                        *)
(* NOTE the RVC-at-4-ALIGNED extra obligation: the fetch of a compressed   *)
(* instruction at a 4-aligned pc is ONE 4-byte read, so [uinstr] also      *)
(* wants the two FOLLOWING bytes present (their values are irrelevant --   *)
(* they belong to the next instruction, and are quoted from the image).    *)
(* ===================================================================== *)

(* the four field goals that do not depend on the encoding *)
Ltac ui_frame off Hl :=
  constructor;
  [ vm_compute; reflexivity                                   (* ui_al2    *)
  | vm_compute; reflexivity                                   (* ui_canon  *)
  | apply (echo_layout_fetch _ off Hl);
    apply bv_eq; vm_compute; reflexivity                      (* ui_leaf   *)
  | apply Z.leb_le; vm_compute; reflexivity                   (* ui_inpage *)
  | idtac ].

(* one image byte, through [echo_text_sub] *)
Ltac ui_byte Hsub := apply Hsub; vm_compute; f_equal; apply bv_eq; reflexivity.

Ltac ui_bytes2 Hsub :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; do 2 (destruct j as [|j]; [ui_byte Hsub|]); lia.
Ltac ui_bytes4 Hsub :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; do 4 (destruct j as [|j]; [ui_byte Hsub|]); lia.

(* compressed at a 2-mod-4 pc: 2-byte fetch, no trailing-byte obligation *)
Ltac ui_rvc2 off Hl Hsub h dec :=
  let Hc := fresh "Hc" in
  ui_frame off Hl;
  exists h; split; [vm_compute; reflexivity|];
  split; [ui_bytes2 Hsub|];
  split; [exact dec|];
  intro Hc; vm_compute in Hc; discriminate.

(* compressed at a 4-aligned pc: 4-byte fetch, so [b2]/[b3] must be there *)
Ltac ui_rvc4 off Hl Hsub h dec b2 b3 :=
  ui_frame off Hl;
  exists h; split; [vm_compute; reflexivity|];
  split; [ui_bytes2 Hsub|];
  split; [exact dec|];
  intros _; exists b2, b3; split; ui_byte Hsub.

(* base (either alignment): 4 bytes of window *)
Ltac ui_base off Hl Hsub w dec :=
  ui_frame off Hl;
  exists w; split; [vm_compute; reflexivity|];
  split; [ui_bytes4 Hsub|]; exact dec.

Section UCodeEcho.
  Context (pt : uptd) (M : gmap Z (bv 8)).
  Context (Hl : echo_layout pt) (Hsub : echo_text_sub M).

  (* ---------------- <main> @ 0x0 ---------------- *)

  (* 0x0  c.addi16sp sp,-64  (RVC, 4-aligned) *)
  Lemma ui_echo_00 :
    uinstr pt M (mword_of_int 0x0) true
      (C_ADDI16SP (mword_of_int 60 : mword 6)).
  Proof. ui_rvc4 0x0 Hl Hsub (mword_of_int 0x7139 : mword 16) udec_7139
           (Z_to_bv 8 0x06) (Z_to_bv 8 0xfc). Qed.

  (* 0x2  c.sdsp ra,56(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_02 :
    uinstr pt M (mword_of_int 0x2) true
      (C_SDSP (mword_of_int 7 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0x2 Hl Hsub (mword_of_int 0xfc06 : mword 16) udec_fc06. Qed.

  (* 0x4  c.sdsp s0,48(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_04 :
    uinstr pt M (mword_of_int 0x4) true
      (C_SDSP (mword_of_int 6 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc4 0x4 Hl Hsub (mword_of_int 0xf822 : mword 16) udec_f822
           (Z_to_bv 8 0x26) (Z_to_bv 8 0xf4). Qed.

  (* 0x6  c.sdsp s1,40(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_06 :
    uinstr pt M (mword_of_int 0x6) true
      (C_SDSP (mword_of_int 5 : mword 6, Regidx (mword_of_int 9))).
  Proof. ui_rvc2 0x6 Hl Hsub (mword_of_int 0xf426 : mword 16) udec_f426. Qed.

  (* 0x8  c.sdsp s2,32(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_08 :
    uinstr pt M (mword_of_int 0x8) true
      (C_SDSP (mword_of_int 4 : mword 6, Regidx (mword_of_int 18))).
  Proof. ui_rvc4 0x8 Hl Hsub (mword_of_int 0xf04a : mword 16) udec_f04a
           (Z_to_bv 8 0x4e) (Z_to_bv 8 0xec). Qed.

  (* 0xa  c.sdsp s3,24(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_0a :
    uinstr pt M (mword_of_int 0xa) true
      (C_SDSP (mword_of_int 3 : mword 6, Regidx (mword_of_int 19))).
  Proof. ui_rvc2 0xa Hl Hsub (mword_of_int 0xec4e : mword 16) udec_ec4e. Qed.

  (* 0xc  c.sdsp s4,16(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_0c :
    uinstr pt M (mword_of_int 0xc) true
      (C_SDSP (mword_of_int 2 : mword 6, Regidx (mword_of_int 20))).
  Proof. ui_rvc4 0xc Hl Hsub (mword_of_int 0xe852 : mword 16) udec_e852
           (Z_to_bv 8 0x56) (Z_to_bv 8 0xe4). Qed.

  (* 0xe  c.sdsp s5,8(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_0e :
    uinstr pt M (mword_of_int 0xe) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 21))).
  Proof. ui_rvc2 0xe Hl Hsub (mword_of_int 0xe456 : mword 16) udec_e456. Qed.

  (* 0x10  c.sdsp s6,0(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_10 :
    uinstr pt M (mword_of_int 0x10) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 22))).
  Proof. ui_rvc4 0x10 Hl Hsub (mword_of_int 0xe05a : mword 16) udec_e05a
           (Z_to_bv 8 0x80) (Z_to_bv 8 0x00). Qed.

  (* 0x12  c.addi4spn s0,sp,64  (RVC, 2 mod 4) *)
  Lemma ui_echo_12 :
    uinstr pt M (mword_of_int 0x12) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 16 : mword 8)).
  Proof. ui_rvc2 0x12 Hl Hsub (mword_of_int 0x0080 : mword 16) udec_0080. Qed.

  (* 0x14  c.li a5,1  (RVC, 4-aligned) *)
  Lemma ui_echo_14 :
    uinstr pt M (mword_of_int 0x14) true
      (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 15))).
  Proof. ui_rvc4 0x14 Hl Hsub (mword_of_int 0x4785 : mword 16) udec_4785
           (Z_to_bv 8 0x63) (Z_to_bv 8 0xd0). Qed.

  (* 0x16  bge a5,a0,0x76   (0x16 -> +0x60)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_16 :
    uinstr pt M (mword_of_int 0x16) false
      (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 10), Regidx (mword_of_int 15), BGE)).
  Proof. ui_base 0x16 Hl Hsub (mword_of_int 0x06a7d063 : mword 32) udec_06a7d063. Qed.

  (* 0x1a  addi s1,a1,8  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_1a :
    uinstr pt M (mword_of_int 0x1a) false
      (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), ADDI)).
  Proof. ui_base 0x1a Hl Hsub (mword_of_int 0x00858493 : mword 32) udec_00858493. Qed.

  (* 0x1e  c.addiw a0,a0,-2  (RVC, 2 mod 4) *)
  Lemma ui_echo_1e :
    uinstr pt M (mword_of_int 0x1e) true
      (C_ADDIW (mword_of_int 62 : mword 6, Regidx (mword_of_int 10))).
  Proof. ui_rvc2 0x1e Hl Hsub (mword_of_int 0x3579 : mword 16) udec_3579. Qed.

  (* 0x20  slli a5,a0,0x20  (base, 4-aligned) *)
  Lemma ui_echo_20 :
    uinstr pt M (mword_of_int 0x20) false
      (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)).
  Proof. ui_base 0x20 Hl Hsub (mword_of_int 0x02051793 : mword 32) udec_02051793. Qed.

  (* 0x24  srli a0,a5,0x1d  (base, 4-aligned) *)
  Lemma ui_echo_24 :
    uinstr pt M (mword_of_int 0x24) false
      (SHIFTIOP (mword_of_int 29 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SRLI)).
  Proof. ui_base 0x24 Hl Hsub (mword_of_int 0x01d7d513 : mword 32) udec_01d7d513. Qed.

  (* 0x28  add s5,s1,a0  (base, 4-aligned) *)
  Lemma ui_echo_28 :
    uinstr pt M (mword_of_int 0x28) false
      (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 9), Regidx (mword_of_int 21), ADD)).
  Proof. ui_base 0x28 Hl Hsub (mword_of_int 0x00a48ab3 : mword 32) udec_00a48ab3. Qed.

  (* 0x2c  c.addi a1,a1,16  (RVC, 4-aligned) *)
  Lemma ui_echo_2c :
    uinstr pt M (mword_of_int 0x2c) true
      (C_ADDI (mword_of_int 16 : mword 6, Regidx (mword_of_int 11))).
  Proof. ui_rvc4 0x2c Hl Hsub (mword_of_int 0x05c1 : mword 16) udec_05c1
           (Z_to_bv 8 0x33) (Z_to_bv 8 0x8a). Qed.

  (* 0x2e  add s4,a1,a0  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_2e :
    uinstr pt M (mword_of_int 0x2e) false
      (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 11), Regidx (mword_of_int 20), ADD)).
  Proof. ui_base 0x2e Hl Hsub (mword_of_int 0x00a58a33 : mword 32) udec_00a58a33. Qed.

  (* 0x32  c.li s3,1  (RVC, 2 mod 4) *)
  Lemma ui_echo_32 :
    uinstr pt M (mword_of_int 0x32) true
      (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 19))).
  Proof. ui_rvc2 0x32 Hl Hsub (mword_of_int 0x4985 : mword 16) udec_4985. Qed.

  (* 0x34  auipc s6,0x1  (base, 4-aligned) *)
  Lemma ui_echo_34 :
    uinstr pt M (mword_of_int 0x34) false
      (UTYPE (mword_of_int 1 : mword 20, Regidx (mword_of_int 22), AUIPC)).
  Proof. ui_base 0x34 Hl Hsub (mword_of_int 0x00001b17 : mword 32) udec_00001b17. Qed.

  (* 0x38  addi s6,s6,-1796  (2^12-1796)  (base, 4-aligned) *)
  Lemma ui_echo_38 :
    uinstr pt M (mword_of_int 0x38) false
      (ITYPE (mword_of_int 2300 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADDI)).
  Proof. ui_base 0x38 Hl Hsub (mword_of_int 0x8fcb0b13 : mword 32) udec_8fcb0b13. Qed.

  (* 0x3c  c.j 0x4e   (+0x12)  (RVC, 4-aligned) *)
  Lemma ui_echo_3c :
    uinstr pt M (mword_of_int 0x3c) true
      (C_J (mword_of_int 9 : mword 11)).
  Proof. ui_rvc4 0x3c Hl Hsub (mword_of_int 0xa809 : mword 16) udec_a809
           (Z_to_bv 8 0x4e) (Z_to_bv 8 0x86). Qed.

  (* 0x3e  c.mv a2,s3  (RVC, 2 mod 4) *)
  Lemma ui_echo_3e :
    uinstr pt M (mword_of_int 0x3e) true
      (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 19))).
  Proof. ui_rvc2 0x3e Hl Hsub (mword_of_int 0x864e : mword 16) udec_864e. Qed.

  (* 0x40  c.mv a1,s6  (RVC, 4-aligned) *)
  Lemma ui_echo_40 :
    uinstr pt M (mword_of_int 0x40) true
      (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 22))).
  Proof. ui_rvc4 0x40 Hl Hsub (mword_of_int 0x85da : mword 16) udec_85da
           (Z_to_bv 8 0x4e) (Z_to_bv 8 0x85). Qed.

  (* 0x42  c.mv a0,s3  (RVC, 2 mod 4) *)
  Lemma ui_echo_42 :
    uinstr pt M (mword_of_int 0x42) true
      (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 19))).
  Proof. ui_rvc2 0x42 Hl Hsub (mword_of_int 0x854e : mword 16) udec_854e. Qed.

  (* 0x44  jal ra,0x352 <write>  (0x44 -> +0x30e)  (base, 4-aligned) *)
  Lemma ui_echo_44 :
    uinstr pt M (mword_of_int 0x44) false
      (JAL (mword_of_int 782 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x44 Hl Hsub (mword_of_int 0x30e000ef : mword 32) udec_30e000ef. Qed.

  (* 0x48  c.addi s1,s1,8  (RVC, 4-aligned) *)
  Lemma ui_echo_48 :
    uinstr pt M (mword_of_int 0x48) true
      (C_ADDI (mword_of_int 8 : mword 6, Regidx (mword_of_int 9))).
  Proof. ui_rvc4 0x48 Hl Hsub (mword_of_int 0x04a1 : mword 16) udec_04a1
           (Z_to_bv 8 0x63) (Z_to_bv 8 0x86). Qed.

  (* 0x4a  beq s1,s4,0x76   (0x4a -> +0x2c)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_4a :
    uinstr pt M (mword_of_int 0x4a) false
      (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 9), BEQ)).
  Proof. ui_base 0x4a Hl Hsub (mword_of_int 0x03448663 : mword 32) udec_03448663. Qed.

  (* 0x4e  ld s2,0(s1)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_4e :
    uinstr pt M (mword_of_int 0x4e) false
      (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), false, 8)).
  Proof. ui_base 0x4e Hl Hsub (mword_of_int 0x0004b903 : mword 32) udec_0004b903. Qed.

  (* 0x52  c.mv a0,s2  (RVC, 2 mod 4) *)
  Lemma ui_echo_52 :
    uinstr pt M (mword_of_int 0x52) true
      (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 18))).
  Proof. ui_rvc2 0x52 Hl Hsub (mword_of_int 0x854a : mword 16) udec_854a. Qed.

  (* 0x54  jal ra,0xdc <strlen>  (0x54 -> +0x88)  (base, 4-aligned) *)
  Lemma ui_echo_54 :
    uinstr pt M (mword_of_int 0x54) false
      (JAL (mword_of_int 136 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x54 Hl Hsub (mword_of_int 0x088000ef : mword 32) udec_088000ef. Qed.

  (* 0x58  c.mv a2,a0  (RVC, 4-aligned) *)
  Lemma ui_echo_58 :
    uinstr pt M (mword_of_int 0x58) true
      (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 10))).
  Proof. ui_rvc4 0x58 Hl Hsub (mword_of_int 0x862a : mword 16) udec_862a
           (Z_to_bv 8 0xca) (Z_to_bv 8 0x85). Qed.

  (* 0x5a  c.mv a1,s2  (RVC, 2 mod 4) *)
  Lemma ui_echo_5a :
    uinstr pt M (mword_of_int 0x5a) true
      (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 18))).
  Proof. ui_rvc2 0x5a Hl Hsub (mword_of_int 0x85ca : mword 16) udec_85ca. Qed.

  (* 0x5c  c.mv a0,s3  (RVC, 4-aligned) *)
  Lemma ui_echo_5c :
    uinstr pt M (mword_of_int 0x5c) true
      (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 19))).
  Proof. ui_rvc4 0x5c Hl Hsub (mword_of_int 0x854e : mword 16) udec_854e
           (Z_to_bv 8 0xef) (Z_to_bv 8 0x00). Qed.

  (* 0x5e  jal ra,0x352 <write>  (0x5e -> +0x2f4)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_5e :
    uinstr pt M (mword_of_int 0x5e) false
      (JAL (mword_of_int 756 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x5e Hl Hsub (mword_of_int 0x2f4000ef : mword 32) udec_2f4000ef. Qed.

  (* 0x62  bne s1,s5,0x3e   (0x62 -> -0x24; 2^13-36)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_62 :
    uinstr pt M (mword_of_int 0x62) false
      (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BNE)).
  Proof. ui_base 0x62 Hl Hsub (mword_of_int 0xfd549ee3 : mword 32) udec_fd549ee3. Qed.

  (* 0x66  c.li a2,1  (RVC, 2 mod 4) *)
  Lemma ui_echo_66 :
    uinstr pt M (mword_of_int 0x66) true
      (C_LI (mword_of_int 1 : mword 6, Regidx (mword_of_int 12))).
  Proof. ui_rvc2 0x66 Hl Hsub (mword_of_int 0x4605 : mword 16) udec_4605. Qed.

  (* 0x68  auipc a1,0x1  (base, 4-aligned) *)
  Lemma ui_echo_68 :
    uinstr pt M (mword_of_int 0x68) false
      (UTYPE (mword_of_int 1 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. ui_base 0x68 Hl Hsub (mword_of_int 0x00001597 : mword 32) udec_00001597. Qed.

  (* 0x6c  addi a1,a1,-1840  (2^12-1840)  (base, 4-aligned) *)
  Lemma ui_echo_6c :
    uinstr pt M (mword_of_int 0x6c) false
      (ITYPE (mword_of_int 2256 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. ui_base 0x6c Hl Hsub (mword_of_int 0x8d058593 : mword 32) udec_8d058593. Qed.

  (* 0x70  c.mv a0,a2  (RVC, 4-aligned) *)
  Lemma ui_echo_70 :
    uinstr pt M (mword_of_int 0x70) true
      (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 12))).
  Proof. ui_rvc4 0x70 Hl Hsub (mword_of_int 0x8532 : mword 16) udec_8532
           (Z_to_bv 8 0xef) (Z_to_bv 8 0x00). Qed.

  (* 0x72  jal ra,0x352 <write>  (0x72 -> +0x2e0)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_72 :
    uinstr pt M (mword_of_int 0x72) false
      (JAL (mword_of_int 736 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x72 Hl Hsub (mword_of_int 0x2e0000ef : mword 32) udec_2e0000ef. Qed.

  (* 0x76  c.li a0,0  (RVC, 2 mod 4) *)
  Lemma ui_echo_76 :
    uinstr pt M (mword_of_int 0x76) true
      (C_LI (mword_of_int 0 : mword 6, Regidx (mword_of_int 10))).
  Proof. ui_rvc2 0x76 Hl Hsub (mword_of_int 0x4501 : mword 16) udec_4501. Qed.

  (* 0x78  jal ra,0x332 <exit>   (0x78 -> +0x2ba)  (base, 4-aligned) *)
  Lemma ui_echo_78 :
    uinstr pt M (mword_of_int 0x78) false
      (JAL (mword_of_int 698 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x78 Hl Hsub (mword_of_int 0x2ba000ef : mword 32) udec_2ba000ef. Qed.

  (* ---------------- <start> @ 0x7c ---------------- *)

  (* 0x7c  c.addi sp,sp,-16  (RVC, 4-aligned) *)
  Lemma ui_echo_7c :
    uinstr pt M (mword_of_int 0x7c) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
  Proof. ui_rvc4 0x7c Hl Hsub (mword_of_int 0x1141 : mword 16) udec_1141
           (Z_to_bv 8 0x06) (Z_to_bv 8 0xe4). Qed.

  (* 0x7e  c.sdsp ra,8(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_7e :
    uinstr pt M (mword_of_int 0x7e) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0x7e Hl Hsub (mword_of_int 0xe406 : mword 16) udec_e406. Qed.

  (* 0x80  c.sdsp s0,0(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_80 :
    uinstr pt M (mword_of_int 0x80) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc4 0x80 Hl Hsub (mword_of_int 0xe022 : mword 16) udec_e022
           (Z_to_bv 8 0x00) (Z_to_bv 8 0x08). Qed.

  (* 0x82  c.addi4spn s0,sp,16  (RVC, 2 mod 4) *)
  Lemma ui_echo_82 :
    uinstr pt M (mword_of_int 0x82) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
  Proof. ui_rvc2 0x82 Hl Hsub (mword_of_int 0x0800 : mword 16) udec_0800. Qed.

  (* 0x84  jal ra,0x0 <main>     (0x84 -> -0x84; 2^21-132)  (base, 4-aligned) *)
  Lemma ui_echo_84 :
    uinstr pt M (mword_of_int 0x84) false
      (JAL (mword_of_int 2097020 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x84 Hl Hsub (mword_of_int 0xf7dff0ef : mword 32) udec_f7dff0ef. Qed.

  (* 0x88  jal ra,0x332 <exit>   (0x88 -> +0x2aa)  (base, 4-aligned) *)
  Lemma ui_echo_88 :
    uinstr pt M (mword_of_int 0x88) false
      (JAL (mword_of_int 682 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x88 Hl Hsub (mword_of_int 0x2aa000ef : mword 32) udec_2aa000ef. Qed.

  (* ---------------- <strlen> @ 0xdc ---------------- *)

  (* 0xdc  c.addi sp,sp,-16  (RVC, 4-aligned) *)
  Lemma ui_echo_dc :
    uinstr pt M (mword_of_int 0xdc) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
  Proof. ui_rvc4 0xdc Hl Hsub (mword_of_int 0x1141 : mword 16) udec_1141
           (Z_to_bv 8 0x06) (Z_to_bv 8 0xe4). Qed.

  (* 0xde  c.sdsp ra,8(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_de :
    uinstr pt M (mword_of_int 0xde) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0xde Hl Hsub (mword_of_int 0xe406 : mword 16) udec_e406. Qed.

  (* 0xe0  c.sdsp s0,0(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_e0 :
    uinstr pt M (mword_of_int 0xe0) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc4 0xe0 Hl Hsub (mword_of_int 0xe022 : mword 16) udec_e022
           (Z_to_bv 8 0x00) (Z_to_bv 8 0x08). Qed.

  (* 0xe2  c.addi4spn s0,sp,16  (RVC, 2 mod 4) *)
  Lemma ui_echo_e2 :
    uinstr pt M (mword_of_int 0xe2) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
  Proof. ui_rvc2 0xe2 Hl Hsub (mword_of_int 0x0800 : mword 16) udec_0800. Qed.

  (* 0xe4  lbu a5,0(a0)  (base, 4-aligned) *)
  Lemma ui_echo_e4 :
    uinstr pt M (mword_of_int 0xe4) false
      (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), true, 1)).
  Proof. ui_base 0xe4 Hl Hsub (mword_of_int 0x00054783 : mword 32) udec_00054783. Qed.

  (* 0xe8  c.beqz a5,0x104  (+0x1c)  (RVC, 4-aligned) *)
  Lemma ui_echo_e8 :
    uinstr pt M (mword_of_int 0xe8) true
      (C_BEQZ (mword_of_int 14 : mword 8, Cregidx (mword_of_int 7))).
  Proof. ui_rvc4 0xe8 Hl Hsub (mword_of_int 0xcf91 : mword 16) udec_cf91
           (Z_to_bv 8 0x93) (Z_to_bv 8 0x07). Qed.

  (* 0xea  addi a5,a0,1  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_ea :
    uinstr pt M (mword_of_int 0xea) false
      (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).
  Proof. ui_base 0xea Hl Hsub (mword_of_int 0x00150793 : mword 32) udec_00150793. Qed.

  (* 0xee  c.mv a3,a5  (RVC, 2 mod 4) *)
  Lemma ui_echo_ee :
    uinstr pt M (mword_of_int 0xee) true
      (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 15))).
  Proof. ui_rvc2 0xee Hl Hsub (mword_of_int 0x86be : mword 16) udec_86be. Qed.

  (* 0xf0  c.addi a5,a5,1  (RVC, 4-aligned) *)
  Lemma ui_echo_f0 :
    uinstr pt M (mword_of_int 0xf0) true
      (C_ADDI (mword_of_int 1 : mword 6, Regidx (mword_of_int 15))).
  Proof. ui_rvc4 0xf0 Hl Hsub (mword_of_int 0x0785 : mword 16) udec_0785
           (Z_to_bv 8 0x03) (Z_to_bv 8 0xc7). Qed.

  (* 0xf2  lbu a4,-1(a5)  (2^12-1)  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_echo_f2 :
    uinstr pt M (mword_of_int 0xf2) false
      (LOAD (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), true, 1)).
  Proof. ui_base 0xf2 Hl Hsub (mword_of_int 0xfff7c703 : mword 32) udec_fff7c703. Qed.

  (* 0xf6  c.bnez a4,0xee   (-0x8; 2^8-4)  (RVC, 2 mod 4) *)
  Lemma ui_echo_f6 :
    uinstr pt M (mword_of_int 0xf6) true
      (C_BNEZ (mword_of_int 252 : mword 8, Cregidx (mword_of_int 6))).
  Proof. ui_rvc2 0xf6 Hl Hsub (mword_of_int 0xff65 : mword 16) udec_ff65. Qed.

  (* 0xf8  subw a0,a3,a0  (base, 4-aligned) *)
  Lemma ui_echo_f8 :
    uinstr pt M (mword_of_int 0xf8) false
      (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 13), Regidx (mword_of_int 10), SUBW)).
  Proof. ui_base 0xf8 Hl Hsub (mword_of_int 0x40a6853b : mword 32) udec_40a6853b. Qed.

  (* 0xfc  c.ldsp ra,8(sp)  (RVC, 4-aligned) *)
  Lemma ui_echo_fc :
    uinstr pt M (mword_of_int 0xfc) true
      (C_LDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc4 0xfc Hl Hsub (mword_of_int 0x60a2 : mword 16) udec_60a2
           (Z_to_bv 8 0x02) (Z_to_bv 8 0x64). Qed.

  (* 0xfe  c.ldsp s0,0(sp)  (RVC, 2 mod 4) *)
  Lemma ui_echo_fe :
    uinstr pt M (mword_of_int 0xfe) true
      (C_LDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc2 0xfe Hl Hsub (mword_of_int 0x6402 : mword 16) udec_6402. Qed.

  (* 0x100  c.addi sp,sp,16  (RVC, 4-aligned) *)
  Lemma ui_echo_100 :
    uinstr pt M (mword_of_int 0x100) true
      (C_ADDI (mword_of_int 16 : mword 6, Regidx (mword_of_int 2))).
  Proof. ui_rvc4 0x100 Hl Hsub (mword_of_int 0x0141 : mword 16) udec_0141
           (Z_to_bv 8 0x82) (Z_to_bv 8 0x80). Qed.

  (* 0x102  c.jr ra  (RVC, 2 mod 4) *)
  Lemma ui_echo_102 :
    uinstr pt M (mword_of_int 0x102) true
      (C_JR (Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0x102 Hl Hsub (mword_of_int 0x8082 : mword 16) udec_8082. Qed.

  (* 0x104  c.li a0,0  (RVC, 4-aligned) *)
  Lemma ui_echo_104 :
    uinstr pt M (mword_of_int 0x104) true
      (C_LI (mword_of_int 0 : mword 6, Regidx (mword_of_int 10))).
  Proof. ui_rvc4 0x104 Hl Hsub (mword_of_int 0x4501 : mword 16) udec_4501
           (Z_to_bv 8 0xdd) (Z_to_bv 8 0xbf). Qed.

  (* 0x106  c.j 0xfc   (-0xa; 2^11-5)  (RVC, 2 mod 4) *)
  Lemma ui_echo_106 :
    uinstr pt M (mword_of_int 0x106) true
      (C_J (mword_of_int 2043 : mword 11)).
  Proof. ui_rvc2 0x106 Hl Hsub (mword_of_int 0xbfdd : mword 16) udec_bfdd. Qed.

  (* ---------------- <exit> @ 0x332 ---------------- *)

  (* 0x332  c.li a7,2   (SYS_exit)  (RVC, 2 mod 4) *)
  Lemma ui_echo_332 :
    uinstr pt M (mword_of_int 0x332) true
      (C_LI (mword_of_int 2 : mword 6, Regidx (mword_of_int 17))).
  Proof. ui_rvc2 0x332 Hl Hsub (mword_of_int 0x4889 : mword 16) udec_4889. Qed.

  (* 0x334  ecall  (base, 4-aligned) *)
  Lemma ui_echo_334 :
    uinstr pt M (mword_of_int 0x334) false
      (ECALL tt).
  Proof. ui_base 0x334 Hl Hsub (mword_of_int 0x00000073 : mword 32) udec_00000073. Qed.

  (* ---------------- <write> @ 0x352 ---------------- *)

  (* 0x352  c.li a7,16  (SYS_write)  (RVC, 2 mod 4) *)
  Lemma ui_echo_352 :
    uinstr pt M (mword_of_int 0x352) true
      (C_LI (mword_of_int 16 : mword 6, Regidx (mword_of_int 17))).
  Proof. ui_rvc2 0x352 Hl Hsub (mword_of_int 0x48c1 : mword 16) udec_48c1. Qed.

  (* 0x354  ecall  (base, 4-aligned) *)
  Lemma ui_echo_354 :
    uinstr pt M (mword_of_int 0x354) false
      (ECALL tt).
  Proof. ui_base 0x354 Hl Hsub (mword_of_int 0x00000073 : mword 32) udec_00000073. Qed.

  (* 0x358  c.jr ra  (RVC, 4-aligned) *)
  Lemma ui_echo_358 :
    uinstr pt M (mword_of_int 0x358) true
      (C_JR (Regidx (mword_of_int 1))).
  Proof. ui_rvc4 0x358 Hl Hsub (mword_of_int 0x8082 : mword 16) udec_8082
           (Z_to_bv 8 0xd5) (Z_to_bv 8 0x48). Qed.

End UCodeEcho.
