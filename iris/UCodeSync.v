(* UCodeSync.v -- the CODE CATALOG of the user program [sync].

   The verified-user tier (claude-notes/projects/user-verified.md) drives one
   step from one [uinstr] fact (UmodeMem.v): the pure statement that at a
   given user pc the program's bytes sit in the process image [M], the pc's
   page is mapped fetch-executable, and the fetched word decodes to a named
   AST on any U-mode machine.  This file proves those facts for the 18
   instructions of the four functions we verify, from the dumped image
   [User.SyncInstrs.sync_bytes].

   Two premises carry every lemma:

     [sync_text_sub M]   -- [M] contains the dumped text (so a proof may talk
                            about a process image that ALSO has data, bss and
                            a stack page in it);
     [sync_layout pt]    -- the one pure page-table fact: the text page is
                            mapped with a fetch-permitting leaf.  Every pc
                            below is < 0x400, hence on that page (page 0);
                            the [svpn_of] identifications are per-instance
                            [vm_compute]s.  Stack facts ride in the function
                            specs, not here.

   The disassembly (objdump on xv6-riscv/user/_sync; SyncSyms.main = 0x0,
   start = 0x12, exit = 0x2c8, sync = 0x368):

     <main> @0x0
       0x00  1141        c.addi    sp,sp,-16
       0x02  e406        c.sdsp    ra,8(sp)
       0x04  e022        c.sdsp    s0,0(sp)
       0x06  0800        c.addi4spn s0,sp,16
       0x08  360000ef    jal       ra,0x368 <sync>
       0x0c  4501        c.li      a0,0
       0x0e  2ba000ef    jal       ra,0x2c8 <exit>
     <start> @0x12
       0x12  1141        c.addi    sp,sp,-16
       0x14  e406        c.sdsp    ra,8(sp)
       0x16  e022        c.sdsp    s0,0(sp)
       0x18  0800        c.addi4spn s0,sp,16
       0x1a  fe7ff0ef    jal       ra,0x0 <main>
       0x1e  2aa000ef    jal       ra,0x2c8 <exit>
     <exit> @0x2c8
       0x2c8 4889        c.li      a7,2
       0x2ca 00000073    ecall              (the c.jr at 0x2ce is dead code)
     <sync> @0x368
       0x368 48d9        c.li      a7,22
       0x36a 00000073    ecall
       0x36e 8082        c.jr      ra

   Every AST below was READ OFF the model (vm_compute of the decoder at
   [dstateU]), never guessed: [jal]'s immediate is the decoder's positive
   21-bit residue (so 0x1a's backwards branch to 0 is 2097126, not -26), and
   the compressed words decode to the raw C_* constructors (the expansion
   into ITYPE/STORE/... happens in [execute], not here). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import CommonWalk UserPtTree.
Require Import WpDecodeBridge DecodeTotalU WpRvcBridge.
Require Import UmodeMem UmodeAbi.
From User Require SyncInstrs SyncSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 The image and the layout premise.                                   *)
(* ===================================================================== *)

(* [M] contains the dumped text -- the generic image inclusion (UmodeAbi.v)
   at this program's text bytes.  An inclusion (not an equality), so a
   process image carrying data/bss/stack on top still qualifies. *)
Definition sync_text_sub (M : gmap Z (bv 8)) : Prop :=
  uimg_sub SyncInstrs.sync_bytes M.

(* The pure page-table premise: the text page (vpn of any va in [0,0x1000),
   spelled at va 0) is mapped with a leaf that permits instruction fetch. *)
Record sync_layout (pt : uptd) : Prop := SyncLayout {
  sl_text : exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int 0 : mword 64) = Some w /\
      uleaf_ok (InstructionFetch tt) w
}.

(* Every pc in this file is on the text page; the identification of its vpn
   with the text page's is one [vm_compute] per instance. *)
Lemma sync_layout_fetch (pt : uptd) (off : Z) :
  sync_layout pt ->
  svpn_of (mword_of_int off : mword 64) = svpn_of (mword_of_int 0 : mword 64) ->
  uva_fetch_leaf pt (mword_of_int off).
Proof. intros [ (w & Hl & Hok) ] Heq. exists w. rewrite Heq. split; assumption. Qed.

(* the addresses this file is about, as the dumper named them *)
Lemma sync_syms_pins :
  SyncSyms.main = 0x0 /\ SyncSyms.start = 0x12 /\
  SyncSyms.exit = 0x2c8 /\ SyncSyms.sync = 0x368.
Proof.
  unfold SyncSyms.main, SyncSyms.start, SyncSyms.exit, SyncSyms.sync.
  split_and!; reflexivity.
Qed.

(* ===================================================================== *)
(* §1 Per-WORD decode facts.                                              *)
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
(* 1141  c.addi sp,sp,-16   (imm field 48 = -16 in 6 bits) *)
Lemma udec_1141 :
  udecode_rvc (mword_of_int 0x1141) (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
Proof. udec_rvc_oneshot. Qed.

(* e406  c.sdsp ra,8(sp) *)
Lemma udec_e406 :
  udecode_rvc (mword_of_int 0xe406) (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* e022  c.sdsp s0,0(sp) *)
Lemma udec_e022 :
  udecode_rvc (mword_of_int 0xe022) (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
Proof. udec_rvc_oneshot. Qed.

(* 0800  c.addi4spn s0,sp,16 *)
Lemma udec_0800 :
  udecode_rvc (mword_of_int 0x0800) (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
Proof. udec_rvc_oneshot. Qed.

(* 4501  c.li a0,0 *)
Lemma udec_4501 :
  udecode_rvc (mword_of_int 0x4501) (C_LI (mword_of_int 0 : mword 6, Regidx (mword_of_int 10))).
Proof. udec_rvc_oneshot. Qed.

(* 4889  c.li a7,2   (SYS_exit) *)
Lemma udec_4889 :
  udecode_rvc (mword_of_int 0x4889) (C_LI (mword_of_int 2 : mword 6, Regidx (mword_of_int 17))).
Proof. udec_rvc_oneshot. Qed.

(* 48d9  c.li a7,22  (SYS_sync) *)
Lemma udec_48d9 :
  udecode_rvc (mword_of_int 0x48d9) (C_LI (mword_of_int 22 : mword 6, Regidx (mword_of_int 17))).
Proof. udec_rvc_oneshot. Qed.

(* 8082  c.jr ra *)
Lemma udec_8082 :
  udecode_rvc (mword_of_int 0x8082) (C_JR (Regidx (mword_of_int 1))).
Proof. udec_rvc_oneshot. Qed.

(* ---- base ---- *)
(* 360000ef  jal ra, +0x360   (0x8 -> 0x368 <sync>) *)
Lemma udec_360000ef :
  udecode_base (mword_of_int 0x360000ef) (JAL (mword_of_int 864 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2ba000ef  jal ra, +0x2ba  (0xe -> 0x2c8 <exit>) *)
Lemma udec_2ba000ef :
  udecode_base (mword_of_int 0x2ba000ef) (JAL (mword_of_int 698 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* fe7ff0ef  jal ra, -0x1a   (0x1a -> 0x0 <main>); 2^21 - 26 = 2097126 *)
Lemma udec_fe7ff0ef :
  udecode_base (mword_of_int 0xfe7ff0ef) (JAL (mword_of_int 2097126 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 2aa000ef  jal ra, +0x2aa  (0x1e -> 0x2c8 <exit>) *)
Lemma udec_2aa000ef :
  udecode_base (mword_of_int 0x2aa000ef) (JAL (mword_of_int 682 : mword 21, Regidx (mword_of_int 1))).
Proof. udec_base_bridge. Qed.

(* 00000073  ecall *)
Lemma udec_00000073 :
  udecode_base (mword_of_int 0x00000073) (ECALL tt).
Proof. udec_base_bridge. Qed.

(* ===================================================================== *)
(* §2 Per-PC [uinstr] facts.                                              *)
(*                                                                        *)
(* Shared shape: [ui_al2]/[ui_canon]/[ui_inpage] are [vm_compute]s on the  *)
(* concrete pc, [ui_leaf] comes from [sync_layout] through the svpn        *)
(* identification, and each byte of [ui_code]'s window is a concrete       *)
(* [sync_bytes] lookup transported by [sync_text_sub].                     *)
(*                                                                        *)
(* NOTE the RVC-at-4-ALIGNED extra obligation: the fetch of a compressed   *)
(* instruction at a 4-aligned pc is ONE 4-byte read, so [uinstr] also      *)
(* wants the two FOLLOWING bytes present (their values are irrelevant --   *)
(* they belong to the next instruction).                                   *)
(* ===================================================================== *)

(* the four field goals that do not depend on the encoding *)
Ltac ui_frame off Hl :=
  constructor;
  [ vm_compute; reflexivity                                   (* ui_al2    *)
  | vm_compute; reflexivity                                   (* ui_canon  *)
  | apply (sync_layout_fetch _ off Hl);
    apply bv_eq; vm_compute; reflexivity                      (* ui_leaf   *)
  | apply Z.leb_le; vm_compute; reflexivity                   (* ui_inpage *)
  | idtac ].

(* one image byte, through [sync_text_sub] *)
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

Section UCodeSync.
  Context (pt : uptd) (M : gmap Z (bv 8)).
  Context (Hl : sync_layout pt) (Hsub : sync_text_sub M).

  (* ---------------- <main> @ 0x0 ---------------- *)

  (* 0x00  c.addi sp,sp,-16  (RVC, 4-aligned) *)
  Lemma ui_sync_00 :
    uinstr pt M (mword_of_int 0x00) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
  Proof. ui_rvc4 0x00 Hl Hsub (mword_of_int 0x1141 : mword 16) udec_1141
           (Z_to_bv 8 0x06) (Z_to_bv 8 0xe4). Qed.

  (* 0x02  c.sdsp ra,8(sp)  (RVC, 2 mod 4) *)
  Lemma ui_sync_02 :
    uinstr pt M (mword_of_int 0x02) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0x02 Hl Hsub (mword_of_int 0xe406 : mword 16) udec_e406. Qed.

  (* 0x04  c.sdsp s0,0(sp)  (RVC, 4-aligned) *)
  Lemma ui_sync_04 :
    uinstr pt M (mword_of_int 0x04) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc4 0x04 Hl Hsub (mword_of_int 0xe022 : mword 16) udec_e022
           (Z_to_bv 8 0x00) (Z_to_bv 8 0x08). Qed.

  (* 0x06  c.addi4spn s0,sp,16  (RVC, 2 mod 4) *)
  Lemma ui_sync_06 :
    uinstr pt M (mword_of_int 0x06) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
  Proof. ui_rvc2 0x06 Hl Hsub (mword_of_int 0x0800 : mword 16) udec_0800. Qed.

  (* 0x08  jal ra,0x368 <sync>  (base, 4-aligned) *)
  Lemma ui_sync_08 :
    uinstr pt M (mword_of_int 0x08) false
      (JAL (mword_of_int 864 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x08 Hl Hsub (mword_of_int 0x360000ef : mword 32) udec_360000ef. Qed.

  (* 0x0c  c.li a0,0  (RVC, 4-aligned) *)
  Lemma ui_sync_0c :
    uinstr pt M (mword_of_int 0x0c) true
      (C_LI (mword_of_int 0 : mword 6, Regidx (mword_of_int 10))).
  Proof. ui_rvc4 0x0c Hl Hsub (mword_of_int 0x4501 : mword 16) udec_4501
           (Z_to_bv 8 0xef) (Z_to_bv 8 0x00). Qed.

  (* 0x0e  jal ra,0x2c8 <exit>  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_sync_0e :
    uinstr pt M (mword_of_int 0x0e) false
      (JAL (mword_of_int 698 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x0e Hl Hsub (mword_of_int 0x2ba000ef : mword 32) udec_2ba000ef. Qed.

  (* ---------------- <start> @ 0x12 ---------------- *)

  (* 0x12  c.addi sp,sp,-16  (RVC, 2 mod 4) *)
  Lemma ui_sync_12 :
    uinstr pt M (mword_of_int 0x12) true
      (C_ADDI (mword_of_int 48 : mword 6, Regidx (mword_of_int 2))).
  Proof. ui_rvc2 0x12 Hl Hsub (mword_of_int 0x1141 : mword 16) udec_1141. Qed.

  (* 0x14  c.sdsp ra,8(sp)  (RVC, 4-aligned) *)
  Lemma ui_sync_14 :
    uinstr pt M (mword_of_int 0x14) true
      (C_SDSP (mword_of_int 1 : mword 6, Regidx (mword_of_int 1))).
  Proof. ui_rvc4 0x14 Hl Hsub (mword_of_int 0xe406 : mword 16) udec_e406
           (Z_to_bv 8 0x22) (Z_to_bv 8 0xe0). Qed.

  (* 0x16  c.sdsp s0,0(sp)  (RVC, 2 mod 4) *)
  Lemma ui_sync_16 :
    uinstr pt M (mword_of_int 0x16) true
      (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 8))).
  Proof. ui_rvc2 0x16 Hl Hsub (mword_of_int 0xe022 : mword 16) udec_e022. Qed.

  (* 0x18  c.addi4spn s0,sp,16  (RVC, 4-aligned) *)
  Lemma ui_sync_18 :
    uinstr pt M (mword_of_int 0x18) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4 : mword 8)).
  Proof. ui_rvc4 0x18 Hl Hsub (mword_of_int 0x0800 : mword 16) udec_0800
           (Z_to_bv 8 0xef) (Z_to_bv 8 0xf0). Qed.

  (* 0x1a  jal ra,0x0 <main>  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_sync_1a :
    uinstr pt M (mword_of_int 0x1a) false
      (JAL (mword_of_int 2097126 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x1a Hl Hsub (mword_of_int 0xfe7ff0ef : mword 32) udec_fe7ff0ef. Qed.

  (* 0x1e  jal ra,0x2c8 <exit>  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_sync_1e :
    uinstr pt M (mword_of_int 0x1e) false
      (JAL (mword_of_int 682 : mword 21, Regidx (mword_of_int 1))).
  Proof. ui_base 0x1e Hl Hsub (mword_of_int 0x2aa000ef : mword 32) udec_2aa000ef. Qed.

  (* ---------------- <exit> @ 0x2c8 ---------------- *)

  (* 0x2c8  c.li a7,2  (RVC, 4-aligned) *)
  Lemma ui_sync_2c8 :
    uinstr pt M (mword_of_int 0x2c8) true
      (C_LI (mword_of_int 2 : mword 6, Regidx (mword_of_int 17))).
  Proof. ui_rvc4 0x2c8 Hl Hsub (mword_of_int 0x4889 : mword 16) udec_4889
           (Z_to_bv 8 0x73) (Z_to_bv 8 0x00). Qed.

  (* 0x2ca  ecall  (base, 2 mod 4 -> split fetch); [exit] never returns, so
     the c.jr at 0x2ce is dead code and gets no fact. *)
  Lemma ui_sync_2ca :
    uinstr pt M (mword_of_int 0x2ca) false (ECALL tt).
  Proof. ui_base 0x2ca Hl Hsub (mword_of_int 0x00000073 : mword 32) udec_00000073. Qed.

  (* ---------------- <sync> @ 0x368 ---------------- *)

  (* 0x368  c.li a7,22  (RVC, 4-aligned) *)
  Lemma ui_sync_368 :
    uinstr pt M (mword_of_int 0x368) true
      (C_LI (mword_of_int 22 : mword 6, Regidx (mword_of_int 17))).
  Proof. ui_rvc4 0x368 Hl Hsub (mword_of_int 0x48d9 : mword 16) udec_48d9
           (Z_to_bv 8 0x73) (Z_to_bv 8 0x00). Qed.

  (* 0x36a  ecall  (base, 2 mod 4 -> split fetch) *)
  Lemma ui_sync_36a :
    uinstr pt M (mword_of_int 0x36a) false (ECALL tt).
  Proof. ui_base 0x36a Hl Hsub (mword_of_int 0x00000073 : mword 32) udec_00000073. Qed.

  (* 0x36e  c.jr ra  (RVC, 2 mod 4) *)
  Lemma ui_sync_36e :
    uinstr pt M (mword_of_int 0x36e) true (C_JR (Regidx (mword_of_int 1))).
  Proof. ui_rvc2 0x36e Hl Hsub (mword_of_int 0x8082 : mword 16) udec_8082. Qed.

End UCodeSync.
