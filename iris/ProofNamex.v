(* ProofNamex.v -- the whole-function proof of namex, fs.c's path walker.

   334 bytes, width 3, skipelem INLINED.  The CFG is NOT the address order
   (gcc reordered the blocks); in EXECUTION order it is

     entry     +0x1c..0x2a   s1=path,s6=npar,s5=name; lbu a4,0(a0); beq -> +0x48
     relative  +0x2e..0x3a   myproc; ld a0,336(a0); idup; s4=a0
     absolute  +0x48..0x52   li a1,1; mv a0,a1  (= iget(1,1)); s4=a0; j +0x3c
     consts    +0x3c..0x46   s3=47,s8=13,s9=14,s7=1; j +0xf4
   L_loop      +0xf4..0x106  while ( *s1=='/' ) s1++;  if ( *s1==0 ) -> L_done
     DEAD      +0x108..0x112 re-load *s1, re-test '/' and 0 (never taken)
     scan      +0x114..0x124 s2=s1; do s2++ while ( *s2!='/' && *s2!=0 )
   L_len       +0x96..0x9e   a2=s2-s1; s10=sext.w a2; bge s8,s10 -> L_short
     long      +0xa2..0xac   memmove(name,s1,14); NO terminator; s1=s2
     len0 DEAD +0x126..0x12a s2=s1; s10=0; a2=0   (never entered)
   L_short     +0x12c..0x13e memmove(name,s1,len); name[len]=0; s1=s2; j L_trail
   L_trail     +0xae..0xbc   while ( *s1=='/' ) s1++
               +0xc0..0xca   ilock(s4); lh a5,68(s4); bne a5,s7 -> L_notdir
               +0xce..0xd2   lh a5,74(s4); beqz a5 -> L_nlink        (9da28f5)
               +0xd4..0xdc   if(s6) { if ( *s1==0 ) -> L_par }
               +0xde..0xea   dirlookup(s4,s5,0) -> s2; beqz -> L_miss
     found     +0xec..0xf2   iunlockput(s4); s4=s2;  FALLS INTO L_loop
   L_notdir    +0x54..0x5a   iunlockput(s4); s4=0    FALLS INTO return
   L_nlink     +0x7a..0x82   iunlockput(s4); s4=0; j +0x5c            (9da28f5)
   L_par       +0x84..0x8a   iunlock(s4); j +0x5c
   L_miss      +0x8c..0x94   iunlockput(s4); s4=s2(=0); j +0x5c
   L_done      +0x140..0x14c if(!s6) j +0x5c; iput(s4); s4=0; j +0x5c
     return    +0x5c..0x78   a0=s4; twelve pops; c.addi16sp +96; c.jr ra

   ---- THE nlink GUARD (upstream 9da28f5, kernel-defects.md D2) ----------

   [L_nlink] is a FRESH BLOCK, not a share of [L_notdir]: gcc emitted a second
   copy of "iunlockput(ip); return 0" rather than branching into the one at
   +0x54, because +0x54 FALLS THROUGH into the return and a branch from +0xd2
   would have to jump.  So the two arms are instruction-for-instruction the
   same except for [L_nlink]'s trailing [c.j +0x5c] -- and the resource
   choreography is likewise [L_notdir]'s verbatim: the descriptor and the
   short parent are deposited by the same [iunlockput], and the walk ends at
   0, which the contract's failure arm already admits.  What is genuinely new
   is only the DECISION: [lh a5,74(s4)] reads the locked inode's [nlink], so
   the branch is decided by the descriptor's own field rather than by the
   path data.  (create gained the twin guard at [create+0x2a]; no proof walks
   create's instructions yet.)

   ---- THE PIECES -------------------------------------------------------

   Each block below hands control on through an [iAssert]ed continuation, and
   the BODY of every one of them is a named [nx_*_body] Definition above the
   capstone rather than spelled out at the [iAssert].  That is a performance
   requirement, not a style choice: nine of these statements are live at the
   deepest point, the proof term is the Iris context times the number of steps
   it survives, and naming them was 5:36 -> 3:48 and 118M -> 69M tree nodes.
   They must stay TRANSPARENT (never [Typeclasses Opaque]) or the [iApply]s
   below stop unifying -- see claude-notes/optimization.md, "RULE ONE".

   [Htail] -- the shared epilogue at +0x5c, a []-PERSISTENT [wp_next]-wrapped
   assertion with an ABSTRACT CONTINUATION (ProofDirlookup's shape).  FOUR
   arms reach it holding four different bundles, so it must speak only about
   the twelve frame slots and [nx_tregs].

   [Hloop] -- the walk at +0xf4, ProofKexit's [forall fuel, wp_next] shape over
   the measure [plen - off].  INSIDE it live three more of the same shape:
   the leading-'/' skip at +0xf4..+0x102, the element scan at +0x116..+0x122,
   and the trailing-'/' skip at +0xae..+0xbc (reached from BOTH memmove
   branches).  The contract's own continuation is threaded through [Hloop]
   as a spatial slot, exactly as ProofDirlookup threads [Hcont].

   ---- THE SHARE CHOREOGRAPHY, PER ELEMENT ------------------------------

   Destruct [inode_held] -> [inode_ref_shed] (q/2 + q/2) -> the share goes to
   ilock, the walk keeps [inode_ref_short k (q/2+q/2) (q/2)].  Exits:
   (not T_DIR) iunlockput deposits the descriptor and the short parent;
   (nameiparent /\ rest = []) iunlock hands the share back and
   [inode_ref_gather] re-forms the whole reference; (found) the child's
   reference comes out of dirlookup's FOUND arm and iunlockput retires the
   parent; (miss) iunlockput retires the parent and the walk ends at 0.

   ---- TWO EXITS, ONE RESOURCE BUNDLE -----------------------------------

   [Hmid] and [Hhead] each take TWO spatial continuations, and the walk's
   thirty-slot bundle cannot be split between them.  The way out is to
   DECIDE THE ARM ON THE DATA first -- [nx_first_ns] says whether anything
   but separators is left in [pfun] on [off, plen) -- give the whole bundle
   to the arm that actually runs, and REFUTE the other one from its own
   exit facts (exit A hands "every byte in [off,plen) is '/'", exit B hands
   a witness that is not).  The same move settles the [beq s6,zero] /
   [c.beqz a5] pair at +0xd4/+0xdc, decided by [npar] and [pfun off'].

   ---- TWO ROUTES, ONE BLOCK --------------------------------------------

   The converse problem -- one block reached from TWO places -- appears
   twice, and both times the block is stated ONCE as a nested [iAssert]
   that CONSUMES the induction hypothesis and the contract's continuation
   and takes the registers, the pc and the path as arguments:

     [Hrest]   +0xae onward, reached from both memmove branches;
     [Hdlblk]  +0xde onward, reached from the [npar] test's two arms.

   Without them the whole ilock / type-test / dirlookup / four-exit tail
   would have to be transcribed twice, and the dirlookup block four times. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import ByteCursor.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IregLinkNz.
Require Import IgetLic.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import SpecMyproc SpecIdup SpecIget SpecMemmove.
Require Import SpecIlock SpecIunlock SpecIunlockput SpecIput.
Require Import SpecDirlookup.
Require Import CodeNamex.
Require Import SpecNamex.
Require Import ProofDirlookupParts ProofNamexParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed facts over [Z] / [nat] -- the     *)
(*  route N3d recorded: never run [lia] inside the whole-function         *)
(*  context.                                                              *)
(* ===================================================================== *)

(* THE BUDGET INVARIANT'S FOUR MOVING PARTS (fs-log.md §G.24).  [ncur] is
   the reservation the walk still holds and [wc] its running "somebody has
   already paid for the bitmap block" bit; the walk is no longer priced per
   LEVEL, because every per-level [iunlockput] runs [crz := true] on the
   inode block and [crb := wc] on the bitmap.  What is left is ONE unit for
   the whole walk, and [wc] is the honest read of whether it is gone.

   The [crb = true -> w = false] premise below (§G.25) is what makes the
   step lemma true at all: without it a CREDITED level's post admits
   [w = true], i.e. that the level spent the unit the caller had already
   paid, and the invariant cannot be re-established. *)
Lemma nx_wi_iu (Lr ncur : nat) (wc : bool) :
  (0 < Lr)%nat ->
  ((0 < Lr)%nat -> (iput_units + (if wc then 0%nat else 1%nat) <= ncur)%nat) ->
  (iput_units <= ncur)%nat.
Proof. intros H1 H2. specialize (H2 H1). destruct wc; lia. Qed.

Lemma nx_wi_need (L n : nat) :
  (walk_need L <= n)%nat -> (0 < L)%nat -> (iput_units + 1 <= n)%nat.
Proof. destruct L; unfold walk_need, iput_units; lia. Qed.

(* ...and one iput's worth is in hand whatever the path length, which is
   what the arms that run at [Lr = 0] (the nameiparent-of-"/" iput) read *)
Lemma nx_wi_need0 (L n : nat) : (walk_need L <= n)%nat -> (iput_units <= n)%nat.
Proof. destruct L; unfold walk_need, iput_units; lia. Qed.

(* the back edge: a level that ran CREDITED on the inode block *)
Lemma nx_wi_step (Lr n ncur ncur' : nat) (wc w' : bool) :
  ((n - walk_spend wc)%nat <= ncur)%nat -> (ncur <= n)%nat ->
  (iput_units <= ncur)%nat ->
  ((0 < S Lr)%nat ->
     (iput_units + (if wc then 0%nat else 1%nat) <= ncur)%nat) ->
  (wc = true -> w' = false) ->
  ((ncur - ip_spend_w w' false true)%nat <= ncur')%nat ->
  (ncur' <= ncur)%nat ->
  ((n - walk_spend (wc || w')%bool)%nat <= ncur')%nat /\ (ncur' <= n)%nat
  /\ (iput_units <= ncur')%nat
  /\ ((0 < Lr)%nat ->
      (iput_units + (if (wc || w')%bool then 0%nat else 1%nat) <= ncur')%nat).
Proof.
  intros HA HB HD0 HC HD HE HF.
  assert (HC' : (iput_units + (if wc then 0%nat else 1%nat) <= ncur)%nat)
    by (apply HC; lia).
  destruct wc, w'; simpl in *;
    try (specialize (HD eq_refl); discriminate);
    unfold walk_spend, ip_spend_w, ip_bm, iput_units in *; simpl in *;
    (split_and!; [lia | lia | lia | intros _; lia]).
Qed.

(* a TERMINAL arm that spends one iput -- credited on the inode block
   ([cz = true], L_miss) or not ([cz = false], L_notdir / L_nlink / the
   nameiparent-of-"/" iput).  All three are the LAST call the walk makes,
   which is why the walk's failure figure is [walk_spend w + 1] and not
   [+ 1] per level. *)
Lemma nx_wi_spend (n ncur n' : nat) (wc w' cz : bool) :
  ((n - walk_spend wc)%nat <= ncur)%nat -> (ncur <= n)%nat ->
  (wc = true -> w' = false) ->
  ((ncur - ip_spend_w w' false cz)%nat <= n')%nat -> (n' <= ncur)%nat ->
  ((n - (walk_spend (wc || w')%bool + 1))%nat <= n')%nat /\ (n' <= n)%nat.
Proof.
  intros HA HB HD HE HF.
  destruct wc, w', cz; simpl in *;
    try (specialize (HD eq_refl); discriminate);
    unfold walk_spend, ip_spend_w, ip_bm in *; simpl in *; split; lia.
Qed.

(* an exit that spends NOTHING: [L_par]'s iunlock, and namei's plain
   return.  These are the SUCCESS arms, and they are why the walk's figure
   is indexed by [ok]. *)
Lemma nx_wi_free (n ncur : nat) (wc : bool) :
  ((n - walk_spend wc)%nat <= ncur)%nat -> (ncur <= n)%nat ->
  ((n - (walk_spend wc + 0))%nat <= ncur)%nat /\ (ncur <= n)%nat.
Proof. intros. split; lia. Qed.

(* the initial instance, at [ncur = n] and nothing paid *)
Lemma nx_wi_init (n : nat) : ((n - walk_spend false)%nat <= n)%nat.
Proof. unfold walk_spend. lia. Qed.

(* the nlink guard's fall-through, at the region's vocabulary: the mint
   wants the UNSIGNED field nonzero and the branch decided the halfword *)
Lemma nx_nlink_nz (t : mword 16) :
  t <> (mword_of_int 0 : mword 16) -> bv_unsigned t <> 0.
Proof.
  intros Hne Hz. apply Hne. apply bv_eq. rewrite Hz.
  vm_compute. reflexivity.
Qed.

(* K_namex's single premise, turned into the seven bounds the callees and
   the [sie_cap_gpr] pop want.  [dl_kb]'s analogue. *)
Lemma nx_kb (K : nat) : (K_namex <= K)%nat ->
  (10 <= K - 12)%nat /\ (K_idup <= K - 12)%nat /\ (K_iget <= K - 12)%nat
  /\ (2 <= K - 12)%nat /\ (K_ilock <= K - 12)%nat /\ (K_iunlock <= K - 12)%nat
  /\ (K_iunlockput <= K - 12)%nat /\ (K_dirlookup <= K - 12)%nat
  /\ (K_iput <= K - 12)%nat /\ ((K - 12) + 12 = K)%nat /\ (12 <= K)%nat.
Proof.
  
  intro H. split_and!; lia.
Qed.


(* ---- THE [addi a4,a5,-47] SLASH TEST at +0x10c and +0x11c (N4b trap 8).
   The immediate decodes as [4049 : mword 12] = -47, and [a4] is zero exactly
   when the loaded byte is the separator.  The route is [bv_unsigned]
   arithmetic, like the [nx_slash_*] family, with the wrap done by hand. *)
Lemma nx_m47_val :
  (sign_extend' 64 (mword_of_int 4049 : mword 12) : mword 64)
  = (mword_of_int 18446744073709551569 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma nx_a4_unsigned (v : mword 8) :
  bv_unsigned (add_vec (zero_extend' 64 v : mword 64)
                 (sign_extend' 64 (mword_of_int 4049 : mword 12)) : mword 64)
  = ((bv_unsigned v + 18446744073709551569) mod 18446744073709551616)%Z.
Proof.
  rewrite nx_m47_val add_vec64_unsigned nx_zext8_unsigned.
  assert (Hc : bv_unsigned (mword_of_int 18446744073709551569 : mword 64)
               = 18446744073709551569%Z) by (vm_compute; reflexivity).
  rewrite Hc. unfold bv_wrap.
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z)
    by (vm_compute; reflexivity).
  rewrite Hm. reflexivity.
Qed.

(* the wrap, over PLAIN [Z].  It has to be a separate lemma: with
   bitvector.tactics' zify hook in scope a goal mentioning [bv_unsigned]
   makes [lia] give up with "Cannot find witness" (ProofMemmove's
   [mm_overlap_arith] is the same split for the same reason). *)
Lemma nx_m47_arith (uv : Z) :
  (0 <= uv)%Z -> (uv < 256)%Z ->
  ((uv + 18446744073709551569) mod 18446744073709551616)%Z = 0%Z ->
  uv = 47%Z.
Proof.
  intros H0 H1 Hc.
  destruct (Z_lt_ge_dec uv 47) as [Hlt | Hge].
  - rewrite Z.mod_small in Hc; lia.
  - replace (uv + 18446744073709551569)%Z
      with ((uv - 47) + 1 * 18446744073709551616)%Z in Hc by lia.
    rewrite Z_mod_plus_full in Hc. rewrite Z.mod_small in Hc; lia.
Qed.

Lemma nx_a4_eq (v : mword 8) : v = SLASH ->
  eq_vec (add_vec (zero_extend' 64 v : mword 64)
            (sign_extend' 64 (mword_of_int 4049 : mword 12)) : mword 64)
         (zero_reg : mword 64) = true.
Proof.
  intros ->. apply (proj2 (eq_vec_true_iff _ _)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma nx_a4_ne (v : mword 8) : v <> SLASH ->
  eq_vec (add_vec (zero_extend' 64 v : mword 64)
            (sign_extend' 64 (mword_of_int 4049 : mword 12)) : mword 64)
         (zero_reg : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)). intro Hc.
  apply (f_equal bv_unsigned) in Hc. rewrite nx_a4_unsigned in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz in Hc.
  pose proof (bv_unsigned_in_range 8 v) as Hr.
  assert (Hm8 : bv_modulus 8 = 256%Z) by (vm_compute; reflexivity).
  rewrite Hm8 in Hr. destruct Hr as [Hlo Hhi].
  apply Hne. apply bv_eq. unfold SLASH.
  assert (H47 : bv_unsigned (mword_of_int 47 : mword 8) = 47%Z)
    by (vm_compute; reflexivity).
  rewrite H47. exact (nx_m47_arith (bv_unsigned v) Hlo Hhi Hc).
Qed.

(* [a4] in the [c.beqz] polarity is the same fact; both DEAD re-tests at
   +0x110 / +0x112 and the live +0x120 read it. *)

(* ===================================================================== *)
(*  THE PURE BRIDGE THE WALK'S BODY OWES: from "every byte in [off,a) is  *)
(*  a separator and the byte at [a] is not" to the suffix [nx_skipelem_at] *)
(*  computes at.  The loop invariant is stated over [drop off pl]; the    *)
(*  element starts at [a]; [pe_skip] is exactly the difference.           *)
(* ===================================================================== *)
Lemma nx_pe_skip_at (off a plen : nat) (f : nat -> bv 8) :
  (off <= a)%nat -> (a <= plen)%nat ->
  (forall i : nat, (off <= i)%nat -> (i < a)%nat -> f i = SLASH) ->
  f a <> SLASH ->
  pe_skip (drop off (bview plen f)) = drop a (bview plen f).
Proof.
  intros Hoa Hap Hsl Hns.
  remember (a - off)%nat as d eqn:Hd. revert off Hd Hoa Hsl.
  induction d as [|d IH]; intros off Hd Hoa Hsl.
  - assert (Ha : off = a) by lia. subst off.
    destruct (Nat.lt_ge_cases a plen) as [Hlt | Hge].
    + rewrite (nx_drop_cons a plen f Hlt) (pe_skip_ne (f a) _ Hns).
      reflexivity.
    + rewrite (nx_drop_nil a plen f Hge). reflexivity.
  - assert (Hlt : (off < a)%nat) by lia.
    assert (Hop : (off < plen)%nat) by lia.
    rewrite (nx_drop_cons off plen f Hop) (Hsl off ltac:(lia) Hlt).
    rewrite pe_skip_slash. apply (IH (S off)); [lia | lia |].
    intros i Hi1 Hi2. apply Hsl; lia.
Qed.

(* THE ARM DECISION, MADE ON THE DATA.  A block with two exits needs BOTH
   continuations supplied, and the walk's thirty-slot bundle cannot be
   split between them -- so the caller decides on [pfun] which arm runs and
   REFUTES the other from its own exit facts.  This is the decision the
   loop head makes: is there anything but separators left? *)
Lemma nx_first_ns (off plen : nat) (f : nat -> bv 8) :
  (off <= plen)%nat ->
  (forall i : nat, (off <= i)%nat -> (i < plen)%nat -> f i = SLASH)
  \/ (exists a : nat, (off <= a)%nat /\ (a < plen)%nat /\ f a <> SLASH).
Proof.
  remember (plen - off)%nat as d eqn:Hd. revert off Hd.
  induction d as [|d IH]; intros off Hd Hop.
  - left. intros i H1 H2. exfalso. lia.
  - destruct (decide (f off = SLASH)) as [He | Hne].
    + destruct (IH (S off) ltac:(lia) ltac:(lia))
        as [HL | (a & Ha1 & Ha2 & Ha3)].
      * left. intros i H1 H2. destruct (Nat.eq_dec i off) as [Hi | Hi];
          [rewrite Hi; exact He | apply HL; lia].
      * right. exists a. split; [lia | split; [lia | exact Ha3]].
    + right. exists off. split; [lia | split; [lia | exact Hne]].
Qed.

(* [skipelem]'s [take 14] on the LONG branch: the fourteen bytes the copy
   moved are the element's own fourteen. *)
Lemma nx_take14_lookup (u : list (bv 8)) (jj : nat) :
  (jj < 14)%nat -> take 14 u !!! jj = u !!! jj.
Proof.
  intro Hj. rewrite !list_lookup_total_alt.
  assert (Ht : take 14 u !! jj = u !! jj) by (apply lookup_take; lia).
  rewrite Ht. reflexivity.
Qed.


(* ---- THE LENGTH ARITHMETIC at +0x90/+0x94.  The [sext.w] is the
   identity because the contract now bounds [plen] below 2^31 (N4c2's
   premise B), and the SIGNED [bge] against 13 then decides [len <= 13]. *)
Lemma nx_sint_moi (z : Z) :
  (- 9223372036854775808 <= z < 9223372036854775808)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z)
    by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

Lemma nx_geb_s (x y : Z) :
  (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  (- 9223372036854775808 <= y < 9223372036854775808)%Z ->
  zopz0zKzJ_s (mword_of_int x : mword 64) (mword_of_int y : mword 64)
  = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_s.
  rewrite (nx_sint_moi x Hx) (nx_sint_moi y Hy). reflexivity.
Qed.

Lemma nx_sextw0 (r : nat) (o : mword 64) :
  o = (mword_of_int 0 : mword 64) ->
  (Z.of_nat r < 2147483648)%Z ->
  (sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat r) : mword 64) o) 31 0) : mword 64)
  = (mword_of_int (Z.of_nat r) : mword 64).
Proof.
  intros -> H31.
  pose proof (Nat2Z.is_nonneg r) as Hr0.
  assert (Hadd : bv_unsigned (add_vec (mword_of_int (Z.of_nat r) : mword 64)
                                (mword_of_int 0 : mword 64))
                 = Z.of_nat r).
  { rewrite add_vec64_unsigned (moi64_unsigned (Z.of_nat r)) (moi64_unsigned 0).
    rewrite (bvw64_small (Z.of_nat r)
               ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z; lia)).
    rewrite (bvw64_small 0
               ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z; lia)).
    rewrite Z.add_0_r.
    apply bvw64_small. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  rewrite sext32_64_moi.
  assert (Hsg : bv_signed (subrange_vec_dec
                   (add_vec (mword_of_int (Z.of_nat r) : mword 64)
                            (mword_of_int 0 : mword 64)) 31 0 : mword 32)
                = Z.of_nat r).
  { unfold bv_signed. rewrite subrange_31_0_unsigned Hadd.
    rewrite (Z.mod_small (Z.of_nat r) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648%Z) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [lia | rewrite Hhm; lia]. }
  rewrite Hsg. reflexivity.
Qed.

(* THE [bge s8,s10] AT +0x9e, both polarities, decided in a CLEAN context.
   In the walk's own context [lia] answers "Cannot find witness" (the trap
   the N4c2 ledger records for [bv_unsigned]; the same happens here with
   [2 ^ 31] in scope), so the whole decision is a closed lemma. *)
Lemma nx_bge13_le (r : nat) : (r <= 13)%nat ->
  zopz0zKzJ_s (mword_of_int 13 : mword 64)
              (mword_of_int (Z.of_nat r) : mword 64) = true.
Proof.
  intro H. pose proof (Nat2Z.is_nonneg r) as H0.
  assert (Hr : (Z.of_nat r <= 13)%Z) by lia.
  rewrite (nx_geb_s 13 (Z.of_nat r) ltac:(lia) ltac:(lia)).
  rewrite Z.geb_leb. apply (proj2 (Z.leb_le _ _)). exact Hr.
Qed.

Lemma nx_bge13_gt (r : nat) : (13 < r)%nat -> (Z.of_nat r < 2147483648)%Z ->
  zopz0zKzJ_s (mword_of_int 13 : mword 64)
              (mword_of_int (Z.of_nat r) : mword 64) = false.
Proof.
  intros H H31. pose proof (Nat2Z.is_nonneg r) as H0.
  assert (Hr : (13 < Z.of_nat r)%Z) by lia.
  rewrite (nx_geb_s 13 (Z.of_nat r) ltac:(lia) ltac:(lia)).
  rewrite Z.geb_leb. apply (proj2 (Z.leb_gt _ _)). exact Hr.
Qed.

(* memmove's own 2^32 bound, out of the walk's context *)
Lemma nx_len32 (r : nat) : (Z.of_nat r < 2147483648)%Z ->
  (Z.of_nat r < 2 ^ 32)%Z.
Proof. intro H. change (2 ^ 32)%Z with 4294967296%Z. lia. Qed.

(* the two immediate shapes namex's [sext.w]s actually carry -- stated with
   NO evar for the offset, because [ltac:] side conditions are elaborated
   before unification and [vm_compute] on an open [?o] kills coqc. *)
Lemma nx_sextw_i12 (r : nat) : (Z.of_nat r < 2147483648)%Z ->
  (sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat r) : mword 64)
        (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0) : mword 64)
  = (mword_of_int (Z.of_nat r) : mword 64).
Proof.
  intro H. apply nx_sextw0;
    [apply bv_eq; vm_compute; reflexivity | exact H].
Qed.

Lemma nx_sextw_i6 (r : nat) : (Z.of_nat r < 2147483648)%Z ->
  (sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat r) : mword 64)
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
     31 0) : mword 64)
  = (mword_of_int (Z.of_nat r) : mword 64).
Proof.
  intro H. apply nx_sextw0;
    [apply bv_eq; vm_compute; reflexivity | exact H].
Qed.

(* ---- the two callee-saved registers the walk writes INSIDE a turn and
   that [nx_regs] deliberately leaves out of its record: s2 (the element
   scanner, rewritten at +0xe8) and s10 (the length, at +0x9a).  Both are
   already excluded from the thread fact, so the bundle simply rides. *)
Lemma nx_regs_s2 (m : regfile) (sp0 s1v ipv nbv npv v : mword 64)
    (Ml : regfile) :
  nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v ipv nbv npv
    (<[Regidx (mword_of_int 18 : mword 5) := v]> Ml).
Proof.
  intros (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!;
    try (rewrite upd_ne; [assumption | vm_compute; discriminate]).
  intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
  rewrite upd_ne;
    [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
    | dlk_xne N18 ].
Qed.

Lemma nx_regs_s10 (m : regfile) (sp0 s1v ipv nbv npv v : mword 64)
    (Ml : regfile) :
  nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v ipv nbv npv
    (<[Regidx (mword_of_int 26 : mword 5) := v]> Ml).
Proof.
  intros (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!;
    try (rewrite upd_ne; [assumption | vm_compute; discriminate]).
  intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
  rewrite upd_ne;
    [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
    | dlk_xne N26 ].
Qed.

Module NamexProof (MP : MYPROC) (ID : IDUP) (IG : IGET) (MM : MEMMOVE)
                  (IL : ILOCK) (IU : IUNLOCK) (IUP : IUNLOCKPUT)
                  (DL : DIRLOOKUP) (IP : IPUT) : NAMEX.

Notation NX := KernelSyms.namex (only parsing).
Notation Rra  := (mword_of_int 1 : mword 5).
Notation Rs0  := (mword_of_int 8 : mword 5).
Notation Rs1  := (mword_of_int 9 : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).

Section ProofNamexMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* ONE byte out of a [seq 0 N] buffer, and the way back.  Already generic
     in [dqm], which is what the path's move to a caller-supplied fraction
     needs: the path is passed at [dqpv] (only READ), the name buffer at
     [DfracOwn 1] (WRITTEN). *)
  Lemma nx_buf_acc (a : mword 64) (dqm : dfrac) (f : nat -> bv 8) (N i : nat) :
    (i < N)%nat ->
    ([∗ list] ii ∈ seq 0 N, pa_add a ii ↦ₘ[KT1]{dqm} f ii) -∗
    (pa_add a i ↦ₘ[KT1]{dqm} f i)
    ∗ ((pa_add a i ↦ₘ[KT1]{dqm} f i) -∗
       [∗ list] ii ∈ seq 0 N, pa_add a ii ↦ₘ[KT1]{dqm} f ii).
  Proof.
    intro Hi. iIntros "Hbuf".
    iDestruct (big_sepL_lookup_acc _ (seq 0 N) i i with "Hbuf") as "[Hb Hback]".
    { rewrite lookup_seq_lt; [reflexivity | exact Hi]. }
    iFrame "Hb Hback".
  Qed.

  (* the escrow-family accessor, restated locally since the walk's slots are
     dirlookup's outputs.  The sleeplock family's accessor is
     [IcacheEscrow.ic_sleeplocks_lookup]. *)
  Lemma nx_esc_acc (cn : ic_names) (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : (k < NINODE)%nat ->
    (ic_escrows cn gfs gi cov logstart -∗ ic_escrow cn gfs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  (* the three-slot pool, split for the ONE slot ilock / dirlookup take.
     Stated as a WAND PAIR, not as an [⊣⊢]: rewriting with the equivalence
     inside an [iAssert] body makes ssreflect complain
     "_pattern_value_ is used in conclusion". *)
  Lemma nx_bs3_split :
    (bslots 3 : iProp Σ) -∗ bslot ∗ bslots 2.
  Proof.
    rewrite /bslot. change 3%nat with (1 + 2)%nat. rewrite bslots_op.
    iIntros "$".
  Qed.

  Lemma nx_bs3_join :
    (bslot : iProp Σ) -∗ bslots 2 -∗ bslots 3.
  Proof.
    iIntros "A B". rewrite /bslot. change 3%nat with (1 + 2)%nat.
    rewrite bslots_op. iFrame.
  Qed.

  (* ---- THE TWO MEMMOVE WINDOWS ------------------------------------
     A [seq 0 N] buffer splits at any [l], and the middle of it re-indexes
     from a shifted base -- which is the shape [SpecMemmove] states its
     SOURCE and DESTINATION in.  [nx_win_acc] is the source side (a window
     inside the path at [pv + a]); [nx_buf_split] / [nx_buf_join] are the
     destination side (the name buffer's first [len] bytes). *)
  Lemma nx_seq_split (l N : nat) : (l <= N)%nat ->
    seq 0 N = seq 0 l ++ seq l (N - l).
  Proof.
    intro H. replace N with (l + (N - l))%nat at 1 by lia.
    rewrite seq_app. reflexivity.
  Qed.

  Lemma nx_buf_split (q : mword 64) (g : nat -> bv 8) (l N : nat) :
    (l <= N)%nat ->
    ([∗ list] i ∈ seq 0 N, pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq 0 l, pa_add q i ↦ₘ[KT1] g i)
    ∗ ([∗ list] i ∈ seq l (N - l), pa_add q i ↦ₘ[KT1] g i).
  Proof.
    intro H. iIntros "Hb". rewrite (nx_seq_split l N H) big_sepL_app.
    iDestruct "Hb" as "[H1 H2]". iFrame.
  Qed.

  Lemma nx_buf_join (q : mword 64) (g : nat -> bv 8) (l N : nat) :
    (l <= N)%nat ->
    ([∗ list] i ∈ seq 0 l, pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq l (N - l), pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq 0 N, pa_add q i ↦ₘ[KT1] g i).
  Proof.
    intro H. iIntros "H1 H2". rewrite (nx_seq_split l N H) big_sepL_app.
    iFrame.
  Qed.

  (* the middle window, re-based: [seq a l] IS [(a +) <$> seq 0 l] *)
  Lemma nx_win_shift (q : mword 64) (dqm : dfrac) (g : nat -> bv 8) (a l : nat) :
    ([∗ list] i ∈ seq a l, pa_add q i ↦ₘ[KT1]{dqm} g i)
    ⊣⊢ ([∗ list] jj ∈ seq 0 l, pa_add (pa_add q a) jj ↦ₘ[KT1]{dqm} g (a + jj)%nat).
  Proof.
    replace (seq a l) with ((Nat.add a) <$> seq 0 l)
      by (rewrite fmap_add_seq Nat.add_0_r; reflexivity).
    rewrite big_sepL_fmap.
    apply big_sepL_proper. intros kk x _. rewrite pa_add_add. reflexivity.
  Qed.

  Lemma nx_seq_split2 (s l t : nat) : (l <= t)%nat ->
    seq s t = seq s l ++ seq (s + l) (t - l).
  Proof.
    intro H. replace t with (l + (t - l))%nat at 1 by lia.
    rewrite seq_app. reflexivity.
  Qed.

  Lemma nx_win_iff (q : mword 64) (dqm : dfrac) (g : nat -> bv 8) (a l N : nat) :
    (a + l <= N)%nat ->
    ([∗ list] i ∈ seq 0 N, pa_add q i ↦ₘ[KT1]{dqm} g i)
    ⊣⊢ (([∗ list] i ∈ seq 0 a, pa_add q i ↦ₘ[KT1]{dqm} g i)
        ∗ ([∗ list] jj ∈ seq 0 l, pa_add (pa_add q a) jj ↦ₘ[KT1]{dqm} g (a + jj)%nat)
        ∗ ([∗ list] i ∈ seq (a + l) (N - a - l), pa_add q i ↦ₘ[KT1]{dqm} g i)).
  Proof.
    intro H.
    rewrite (nx_seq_split a N ltac:(lia)) big_sepL_app.
    rewrite (nx_seq_split2 a l (N - a)%nat ltac:(lia)) big_sepL_app.
    rewrite (nx_win_shift q dqm g a l). reflexivity.
  Qed.

  (* the NAME buffer, split the way the SHORT branch writes it: [l] copied
     bytes, the terminator at [l], and whatever the copy did not touch *)
  Lemma nx_name_split (q : mword 64) (g : nat -> bv 8) (l : nat) :
    (l < 14)%nat ->
    ([∗ list] i ∈ seq 0 14, pa_add q i ↦ₘ[KT1] g i)
    ⊣⊢ (([∗ list] i ∈ seq 0 l, pa_add q i ↦ₘ[KT1] g i)
        ∗ (pa_add q l ↦ₘ[KT1] g l)
        ∗ ([∗ list] i ∈ seq (S l) (13 - l), pa_add q i ↦ₘ[KT1] g i)).
  Proof.
    intro H.
    rewrite (nx_seq_split l 14 ltac:(lia)) big_sepL_app.
    replace (14 - l)%nat with (S (13 - l)) by lia.
    rewrite -(cons_seq (13 - l) l) big_sepL_cons. reflexivity.
  Qed.

  Lemma nx_name_split_l (q : mword 64) (g : nat -> bv 8) (l : nat) :
    (l < 14)%nat ->
    ([∗ list] i ∈ seq 0 14, pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq 0 l, pa_add q i ↦ₘ[KT1] g i) ∗ (pa_add q l ↦ₘ[KT1] g l)
    ∗ ([∗ list] i ∈ seq (S l) (13 - l), pa_add q i ↦ₘ[KT1] g i).
  Proof. intro H. rewrite (nx_name_split q g l H). iIntros "$". Qed.

  Lemma nx_name_join (q : mword 64) (g : nat -> bv 8) (l : nat) :
    (l < 14)%nat ->
    ([∗ list] i ∈ seq 0 l, pa_add q i ↦ₘ[KT1] g i) -∗ (pa_add q l ↦ₘ[KT1] g l) -∗
    ([∗ list] i ∈ seq (S l) (13 - l), pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq 0 14, pa_add q i ↦ₘ[KT1] g i).
  Proof.
    intro H. iIntros "A B C". rewrite (nx_name_split q g l H). iFrame.
  Qed.

  (* re-labelling a window: the two memmoves leave the name buffer holding
     the element's bytes, and the walk names that content by a FUNCTION *)
  Lemma nx_buf_fun (q : mword 64) (g h : nat -> bv 8) (s t : nat) :
    (forall i : nat, (s <= i)%nat -> (i < s + t)%nat -> g i = h i) ->
    ([∗ list] i ∈ seq s t, pa_add q i ↦ₘ[KT1] g i) -∗
    ([∗ list] i ∈ seq s t, pa_add q i ↦ₘ[KT1] h i).
  Proof.
    intro H. iIntros "Hb". iApply (big_sepL_mono with "Hb").
    intros kk x Hx. apply lookup_seq in Hx. destruct Hx as [Hx Hk].
    rewrite Hx. rewrite (H (s + kk)%nat ltac:(lia) ltac:(lia)). done.
  Qed.

  (* THE SOURCE WINDOW, AT THE CALLER'S FRACTION.  This one carves the
     memmove's SOURCE out of the path, and the path arrives at [dqpv] because
     kexec's caller (forkret's [kexec("/init", (char *[]){"/init", 0})]) hands
     the same .rodata literal in twice.  The DESTINATION lemmas below
     ([nx_buf_split] / [nx_name_split] / [nx_buf_fun]) stay whole: namex
     WRITES the name buffer. *)
  Lemma nx_win_acc (q : mword 64) (dqm : dfrac) (g : nat -> bv 8) (a l N : nat) :
    (a + l <= N)%nat ->
    ([∗ list] i ∈ seq 0 N, pa_add q i ↦ₘ[KT1]{dqm} g i) -∗
    ([∗ list] jj ∈ seq 0 l, pa_add (pa_add q a) jj ↦ₘ[KT1]{dqm} g (a + jj)%nat)
    ∗ (([∗ list] jj ∈ seq 0 l, pa_add (pa_add q a) jj ↦ₘ[KT1]{dqm} g (a + jj)%nat) -∗
       [∗ list] i ∈ seq 0 N, pa_add q i ↦ₘ[KT1]{dqm} g i).
  Proof.
    intro H. iIntros "Hb".
    iEval (rewrite (nx_win_iff q dqm g a l N H)) in "Hb".
    iDestruct "Hb" as "(Hlo & Hmid & Hhi)". iFrame "Hmid".
    iIntros "Hmid". iEval (rewrite (nx_win_iff q dqm g a l N H)). iFrame.
  Qed.

  (* ---- THE BLOCK STATEMENTS, NAMED ------------------------------------

     Every one of these is a continuation the walk hands around, and
     spelled out at the [iAssert] they were ~200 lines of statement that
     EVERY proofmode step of the body re-embeds in the proof term twice
     (claude-notes/optimization.md, "WHY Qed IS EXPENSIVE": the term is
     the Iris context times the number of steps it survives).  Naming them
     makes each one constant applied to its arguments in the context.

     They are TRANSPARENT on purpose, and only the INNER function body is
     named: [iSpecialize ("Hsk1" $! plen CIDh2 ...)] still sees the [wp_next]
     and the [□] syntactically, and the following [iApply ("Hsk1" $! off M)]
     unifies through a transparent constant.  It does NOT unify through a
     [Typeclasses Opaque] one -- sealing them that way forces an
     [iEval (rewrite /...)] per use site, which is itself
     context-proportional and measured at +48% on this file. *)

  (* THE EXIT BUNDLE TAKES THE PER-CPU BUNDLE AND THE COMPLEMENT.  Its own
     crossing is legitimately [true] -- it ends at the contract's [ret_tgt]
     and namex parks -- so a caller cannot FRAME a hart-indexed resource
     across it once [eb] is free.  Threading them is Round 14's local-bundle
     rule (claude-notes/completed/eb-generic-sweep.md). *)
  Definition nx_tail_body
      (j : nat) (eb b : bool) (lks : gset string) (K : nat) (m : regfile)
      (sp0 ret_tgt : mword 64) (CIDt : CpuId) : iProp Σ :=
    (∀ (Mt : regfile) (rv : mword 64),
     ⌜nx_tregs m sp0 Mt⌝ -∗
     ⌜Mt !!! Regidx Rs4 = rv⌝ -∗
     sie_cap_gpr KT1 Mt (K - 12)%nat b (proc_addr j) -∗
     cpu_own 0 eb (proc_addr j) b lks -∗
     trap_csrs_ext KT1 eb -∗
     cpu_claim_ext eb (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0x5c)) -∗
     (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
     (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
     (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
     (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
     (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
     (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
     (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
     (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
     (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) -∗
     (pa_stk sp0 10) ↦₈[KT1] (m !!! Regidx Rs8 : mword 64) -∗
     (pa_stk sp0 11) ↦₈[KT1] (m !!! Regidx Rs9 : mword 64) -∗
     (pa_stk sp0 12) ↦₈[KT1] (m !!! Regidx Rs10 : mword 64) -∗
     (* the LITERAL [true]: this is the CONTRACT's continuation re-wrapped
        (it ends at [pc_is ret_tgt]), and namex parks. *)
     wp_next (CID0 := CIDt) true (proc_addr j) (fun CIDf : CpuId =>
       ∀ mf : regfile,
         ⌜callee_saved m mf⌝ -∗
         ⌜mf !!! Regidx Ra0 = rv⌝ -∗
         sie_cap_gpr KT1 mf K b (proc_addr j) -∗
         cpu_own 0 eb (proc_addr j) b lks -∗
         trap_csrs_ext KT1 eb -∗
         cpu_claim_ext eb (proc_addr j) -∗
         pc_is ret_tgt -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_skip_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (fuel : nat) (CIDs : CpuId) : iProp Σ :=
    (∀ (off : nat) (Ms : regfile),
     ⌜(plen - off <= fuel)%nat⌝ -∗
     ⌜(off < plen)%nat⌝ -∗
     ⌜pfun off = SLASH⌝ -∗
     ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
     ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xfc)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
       ∀ (off' : nat) (Ms' : regfile),
         ⌜(off < off')%nat⌝ -∗ ⌜(off' <= plen)%nat⌝ -∗
         ⌜forall i : nat, (off <= i)%nat -> (i < off')%nat ->
            pfun i = SLASH⌝ -∗
         ⌜pfun off' <> SLASH⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv off'⌝ -∗
         ⌜Ms' !!! Regidx Ra5
            = (zero_extend' 64 (pfun off' : mword 8) : mword 64)⌝ -∗
         ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0x106)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_skip2_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (fuel : nat) (CIDs : CpuId) : iProp Σ :=
    (∀ (off : nat) (Ms : regfile),
     ⌜(plen - off <= fuel)%nat⌝ -∗
     ⌜(off < plen)%nat⌝ -∗
     ⌜pfun off = SLASH⌝ -∗
     ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
     ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xb6)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
       ∀ (off' : nat) (Ms' : regfile),
         ⌜(off < off')%nat⌝ -∗ ⌜(off' <= plen)%nat⌝ -∗
         ⌜forall i : nat, (off <= i)%nat -> (i < off')%nat ->
            pfun i = SLASH⌝ -∗
         ⌜pfun off' <> SLASH⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv off'⌝ -∗
         ⌜Ms' !!! Regidx Ra5
            = (zero_extend' 64 (pfun off' : mword 8) : mword 64)⌝ -∗
         ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0xc0)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_scan_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (fuel : nat) (CIDs : CpuId) : iProp Σ :=
    (∀ (ii : nat) (Ms : regfile),
     ⌜(plen - ii <= fuel)%nat⌝ -∗
     ⌜(ii < plen)%nat⌝ -∗
     ⌜Ms !!! Regidx Rs2 = pa_add pv ii⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0x116)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
       ∀ (e : nat) (Ms' : regfile),
         ⌜(ii < e)%nat⌝ -∗ ⌜(e <= plen)%nat⌝ -∗
         ⌜forall jj : nat, (ii < jj)%nat -> (jj < e)%nat ->
            pfun jj <> SLASH⌝ -∗
         ⌜pfun e = SLASH \/ e = plen⌝ -∗
         ⌜Ms' !!! Regidx Rs2 = pa_add pv e⌝ -∗
         ⌜forall c : mword 5, c <> Rs2 -> c <> Ra5 -> c <> Ra4 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0x96)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_mid_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (CIDs : CpuId) : iProp Σ :=
    (∀ (a : nat) (Ms : regfile),
     ⌜(a <= plen)%nat⌝ -∗
     ⌜pfun a <> SLASH⌝ -∗
     ⌜Ms !!! Regidx Rs1 = pa_add pv a⌝ -∗
     ⌜Ms !!! Regidx Ra5
        = (zero_extend' 64 (pfun a : mword 8) : mword 64)⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0x106)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     (* EXIT A -- the string is exhausted, at +0x140 *)
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDa : CpuId =>
       ⌜(a = plen)%nat⌝ -∗
       sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
       pc_is (mword_of_int (NX + 0x140)) -∗
       ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
       WP (Loop : expr riscv_lang)) -∗
     (* EXIT B -- an element starts at [a], at +0x116 *)
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDb : CpuId =>
       ∀ Ms' : regfile,
         ⌜(a < plen)%nat⌝ -∗
         ⌜pfun a <> NUL⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv a⌝ -∗
         ⌜Ms' !!! Regidx Rs2 = pa_add pv a⌝ -∗
         ⌜forall c : mword 5, c <> Ra5 -> c <> Ra4 -> c <> Rs2 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0x116)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_head_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (CIDs : CpuId) : iProp Σ :=
    (∀ (off : nat) (Ms : regfile),
     ⌜(off <= plen)%nat⌝ -∗
     ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
     ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xf4)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     (* EXIT A -- nothing but separators left, at +0x140 *)
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDa : CpuId =>
       ∀ Ms' : regfile,
         ⌜forall i : nat, (off <= i)%nat -> (i < plen)%nat ->
            pfun i = SLASH⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv plen⌝ -∗
         ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0x140)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     (* EXIT B -- an element starts at [a], at +0x116 *)
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDb : CpuId =>
       ∀ (a : nat) (Ms' : regfile),
         ⌜(off <= a)%nat⌝ -∗ ⌜(a < plen)%nat⌝ -∗
         ⌜forall i : nat, (off <= i)%nat -> (i < a)%nat ->
            pfun i = SLASH⌝ -∗
         ⌜pfun a <> SLASH⌝ -∗ ⌜pfun a <> NUL⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv a⌝ -∗
         ⌜Ms' !!! Regidx Rs2 = pa_add pv a⌝ -∗
         ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 -> c <> Ra4 ->
            c <> Rs2 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0x116)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_trail_body
      (j : nat) (b : bool) (K plen : nat) (pfun : nat -> bv 8)
      (pv : mword 64) (dqpv : dfrac) (CIDs : CpuId) : iProp Σ :=
    (∀ (off : nat) (Ms : regfile),
     ⌜(off <= plen)%nat⌝ -∗
     ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
     ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
     sie_cap_gpr KT1 Ms (K - 12)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xae)) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
       ∀ (off' : nat) (Ms' : regfile),
         ⌜(off <= off')%nat⌝ -∗ ⌜(off' <= plen)%nat⌝ -∗
         ⌜forall i : nat, (off <= i)%nat -> (i < off')%nat ->
            pfun i = SLASH⌝ -∗
         ⌜pfun off' <> SLASH⌝ -∗
         ⌜Ms' !!! Regidx Rs1 = pa_add pv off'⌝ -∗
         ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
            Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ms' (K - 12)%nat b (proc_addr j) -∗
         pc_is (mword_of_int (NX + 0xc0)) -∗
         ([∗ list] i ∈ seq 0 (S plen),
            pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_loop_body
      (j : nat) (b : bool) (K : nat) (m : regfile)
      (sp0 pv nb ret_tgt : mword 64) (plen L : nat) (pfun : nat -> bv 8)
      (pl : list (bv 8)) (eb : bool)
      (g : log_names) (gfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (npar : bool) (n : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac) (fuel : nat) (CIDl : CpuId) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    (* THE GROWING SET (fs-sysfile GR-2b, retrofit 6).  [Sb] is the caller's,
       fixed; [Scur] is the loop's running set, existentially fresh at every
       turn because each iteration's iunlockput returns a set it chose.  The
       invariant carries only [Sb ⊆ Scur], and the back edge re-establishes
       it by ONE transitivity ([ProofNamexParts.nx_sub_trans], named so that
       no [set_solver] ever runs in this file's context).  Contrast itrunc's
       loops, whose set is CONSTANT -- there the retrofit was a threaded
       parameter; here it is a genuine invariant. *)
    (∀ (off : nat) (ipv : mword 64) (Ml : regfile) (ncur : nat)
     (Scur : gset Z) (es0 : list (list (bv 8))) (nf : nat -> bv 8)
     (wc : bool),
     ⌜(plen - off < fuel)%nat⌝ -∗
     ⌜(off <= plen)%nat⌝ -∗
     ⌜path_elems pl = es0 ++ path_elems (drop off pl)⌝ -∗
     (* THE BUDGET, RE-PRICED (fs-log.md §G.24).  Not linear in the path
        length any more: [wc] says whether the walk has already paid for
        the bitmap block, the spend so far is [walk_spend wc], and what a
        further level needs in hand is one iput's worth plus that unit if
        it is still unspent. *)
     ⌜((n - walk_spend wc)%nat <= ncur)%nat⌝ -∗
     ⌜(ncur <= n)%nat⌝ -∗
     ⌜(iput_units <= ncur)%nat⌝ -∗
     ⌜(0 < length (path_elems (drop off pl)))%nat ->
      (iput_units + (if wc then 0%nat else 1%nat) <= ncur)%nat⌝ -∗
     ⌜wc = true -> bmapstart ∈ Scur⌝ -∗
     ⌜Sb ⊆ Scur⌝ -∗
     ⌜nx_regs m sp0 (pa_add pv off) ipv nb
              (m !!! Regidx Ra1 : mword 64) Ml⌝ -∗
     sie_cap_gpr KT1 Ml (K - 12)%nat b (proc_addr j) -∗
     cpu_own 0 eb (proc_addr j) b lks -∗
     trap_csrs_ext KT1 eb -∗
     cpu_claim_ext eb (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xf4)) -∗
     (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
     (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
     (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
     (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
     (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
     (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
     (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
     (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
     (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) -∗
     (pa_stk sp0 10) ↦₈[KT1] (m !!! Regidx Rs8 : mword 64) -∗
     (pa_stk sp0 11) ↦₈[KT1] (m !!! Regidx Rs9 : mword 64) -∗
     (pa_stk sp0 12) ↦₈[KT1] (m !!! Regidx Rs10 : mword 64) -∗
     inode_held ipv -∗
     iref_slots 1 -∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
     proc_priv_bare (proc_addr j) pidv Vpr -∗
     inode_held (pv_cwd Vpr) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nf i) -∗
     bslots 3 -∗
     log_opS g ncur Scur -∗
     (* ---- THE CONTRACT'S OWN CONTINUATION, at the loop's hart.  Kept
        SEALED as [SpecNamex.namex_post]: spelled out here it would be
        twenty more wands inside the loop invariant, i.e. carried by
        every proofmode step of the body. ---- *)
     (* the LITERAL [true], matching SpecNamex's crossing: namex parks
        (through ilock, down to sleep), so the contract's own continuation
        is about an arbitrary hart. *)
     wp_next (CID0 := CIDl) true (proc_addr j) (fun CIDc : CpuId =>
       namex_postS (CID := CIDc) (proc_addr j) pv nb ret_tgt pl m K b eb lks
                   g gfs bn cov logstart bmapstart inodestart size
                   plen pfun npar n Sb pidv dq dqb dqs dqpv Vpr) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition nx_rest_body
      (j : nat) (b : bool) (K : nat) (m : regfile) (sp0 pv nb : mword 64)
      (plen a e : nat) (pfun : nat -> bv 8) (ipv : mword 64) (ncur : nat)
      (Scur : gset Z) (eb : bool)
      (g : log_names) (gfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart size : Z)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (CIDt : CpuId) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    (∀ (Mt : regfile) (nf' : nat -> bv 8),
     ⌜nx_regs m sp0 (pa_add pv e) ipv nb
        (m !!! Regidx Ra1 : mword 64) Mt⌝ -∗
     ⌜bname 14 nf'
      = take 14 (bview (e - a)%nat
                   (fun i => pfun (a + i)%nat))⌝ -∗
     sie_cap_gpr KT1 Mt (K - 12)%nat b (proc_addr j) -∗
     cpu_own 0 eb (proc_addr j) b lks -∗
     trap_csrs_ext KT1 eb -∗
     cpu_claim_ext eb (proc_addr j) -∗
     pc_is (mword_of_int (NX + 0xae)) -∗
     (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
     (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
     (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
     (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
     (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
     (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
     (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
     (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
     (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) -∗
     (pa_stk sp0 10) ↦₈[KT1] (m !!! Regidx Rs8 : mword 64) -∗
     (pa_stk sp0 11) ↦₈[KT1] (m !!! Regidx Rs9 : mword 64) -∗
     (pa_stk sp0 12) ↦₈[KT1] (m !!! Regidx Rs10 : mword 64) -∗
     inode_held ipv -∗
     iref_slots 1 -∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
     proc_priv_bare (proc_addr j) pidv Vpr -∗
     inode_held (pv_cwd Vpr) -∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
     ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nf' i) -∗
     bslots 3 -∗
     log_opS g ncur Scur -∗
     WP (Loop : expr riscv_lang))%I.

  (* THE WALK IS THE SET FORM (GR-2a finding 1).  The counted seal is
     after the proof. *)
  Lemma wp_namex_gen
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (npar : bool)
      (n : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_namex_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                        ga gf cov logstart bmapstart inodestart nib
                        size dev plen pfun nfun npar n Sb
                        pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_namex_gen_body].
    intros pcE pjv pv nb ret_tgt pl L
           HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
           Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hbud Hj Hgs Ha1 Hbelow.
    destruct (nx_kb K HK) as (Kmp & Kid & Kig & Kmm & Kil & Kiu & Kiup
                              & Kdl & Kip & Kpop & K12).
    (* N3d trap 1's whole-function fix: rename the [let]-bound [pj], fold
       [proc_addr j] into every resource ONCE, and never write [pjv] again. *)
    assert (Hpjd : proc_addr j = pjv) by reflexivity.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hropen #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              #Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog Hcont".
    (* PIN THE INDEX.  This contract still carries [eb = true ->], and at
       level 0 [cpu_own_eb_agree] gives [eb = b], so [b] IS the literal
       [true] here.  The crossings below are the literal [true] (this
       function parks), and a [b]-indexed [cpu_own_transport] cannot be
       discharged from a [true]-indexed guard -- [b = false] tells you
       nothing about the hart.  When this function is itself generalized,
       this derivation is what goes. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    iEval (rewrite -Hpjd) in "Hcg".
    iEval (rewrite -Hpjd) in "Hcnt".
    iEval (rewrite -Hpjd) in "Hppid".
    iEval (rewrite -Hpjd) in "Hcont".
    (* ===== +0x00 c.addi16sp sp,-96 : the 12-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12) by apply dlk_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m K 12 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (nxi_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    pose (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R1 upd_eq; exact Hpush).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    iDestruct "S11" as (u11) "Hb11". iDestruct "S12" as (u12) "Hb12".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply dlk_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply dlk_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply dlk_frm3).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply dlk_frm4).
    assert (Hf5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HR1sp; apply dlk_frm5).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply dlk_frm6).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply dlk_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply dlk_frm8).
    assert (Hf9 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite HR1sp; apply dlk_frm9).
    assert (Hf10 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 10) by (rewrite HR1sp; apply nx_frm10).
    assert (Hf11 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 11) by (rewrite HR1sp; apply nx_frm11).
    assert (Hf12 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 12) by (rewrite HR1sp; apply nx_frm12).
    iEval (rewrite -Hf1) in "Hb1".   iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3".   iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf5) in "Hb5".   iEval (rewrite -Hf6) in "Hb6".
    iEval (rewrite -Hf7) in "Hb7".   iEval (rewrite -Hf8) in "Hb8".
    iEval (rewrite -Hf9) in "Hb9".   iEval (rewrite -Hf10) in "Hb10".
    iEval (rewrite -Hf11) in "Hb11". iEval (rewrite -Hf12) in "Hb12".
    assert (Hpp002 : add_vec_int (pcE : mword 64) 2 = mword_of_int (NX + 0x2)) by pcw.
    iEval (rewrite Hpp002) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x02 .. +0x18 : the TWELVE saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x2)) (mword_of_int 11 : mword 6)
              Rra R1 (K - 12)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (nxi_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp004 : add_vec_int (mword_of_int (NX + 0x2) : mword 64) 2
                     = mword_of_int (NX + 0x4)) by pcw.
    iEval (rewrite Hpp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x4)) (mword_of_int 10 : mword 6)
              Rs0 R1 (K - 12)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (nxi_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp006 : add_vec_int (mword_of_int (NX + 0x4) : mword 64) 2
                     = mword_of_int (NX + 0x6)) by pcw.
    iEval (rewrite Hpp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x6)) (mword_of_int 9 : mword 6)
              Rs1 R1 (K - 12)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (nxi_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hpp008 : add_vec_int (mword_of_int (NX + 0x6) : mword 64) 2
                     = mword_of_int (NX + 0x8)) by pcw.
    iEval (rewrite Hpp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x8)) (mword_of_int 8 : mword 6)
              Rs2 R1 (K - 12)%nat u4 b with "Hcg Hpc [] Hb4").
    { iApply (nxi_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp00a : add_vec_int (mword_of_int (NX + 0x8) : mword 64) 2
                     = mword_of_int (NX + 0xa)) by pcw.
    iEval (rewrite Hpp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xa)) (mword_of_int 7 : mword 6)
              Rs3 R1 (K - 12)%nat u5 b with "Hcg Hpc [] Hb5").
    { iApply (nxi_00a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc Hb5".
    iEval (rgne; rewrite (HR1o Rs3 ltac:(nz)) Hf5) in "Hb5".
    assert (Hpp00c : add_vec_int (mword_of_int (NX + 0xa) : mword 64) 2
                     = mword_of_int (NX + 0xc)) by pcw.
    iEval (rewrite Hpp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xc)) (mword_of_int 6 : mword 6)
              Rs4 R1 (K - 12)%nat u6 b with "Hcg Hpc [] Hb6").
    { iApply (nxi_00c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hpp00e : add_vec_int (mword_of_int (NX + 0xc) : mword 64) 2
                     = mword_of_int (NX + 0xe)) by pcw.
    iEval (rewrite Hpp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0xe)) (mword_of_int 5 : mword 6)
              Rs5 R1 (K - 12)%nat u7 b with "Hcg Hpc [] Hb7").
    { iApply (nxi_00e with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp010 : add_vec_int (mword_of_int (NX + 0xe) : mword 64) 2
                     = mword_of_int (NX + 0x10)) by pcw.
    iEval (rewrite Hpp010) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x10)) (mword_of_int 4 : mword 6)
              Rs6 R1 (K - 12)%nat u8 b with "Hcg Hpc [] Hb8").
    { iApply (nxi_010 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp012 : add_vec_int (mword_of_int (NX + 0x10) : mword 64) 2
                     = mword_of_int (NX + 0x12)) by pcw.
    iEval (rewrite Hpp012) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x12)) (mword_of_int 3 : mword 6)
              Rs7 R1 (K - 12)%nat u9 b with "Hcg Hpc [] Hb9").
    { iApply (nxi_012 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc Hb9".
    iEval (rgne; rewrite (HR1o Rs7 ltac:(nz)) Hf9) in "Hb9".
    assert (Hpp014 : add_vec_int (mword_of_int (NX + 0x12) : mword 64) 2
                     = mword_of_int (NX + 0x14)) by pcw.
    iEval (rewrite Hpp014) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x14)) (mword_of_int 2 : mword 6)
              Rs8 R1 (K - 12)%nat u10 b with "Hcg Hpc [] Hb10").
    { iApply (nxi_014 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc Hb10".
    iEval (rgne; rewrite (HR1o Rs8 ltac:(nz)) Hf10) in "Hb10".
    assert (Hpp016 : add_vec_int (mword_of_int (NX + 0x14) : mword 64) 2
                     = mword_of_int (NX + 0x16)) by pcw.
    iEval (rewrite Hpp016) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x16)) (mword_of_int 1 : mword 6)
              Rs9 R1 (K - 12)%nat u11 b with "Hcg Hpc [] Hb11").
    { iApply (nxi_016 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc Hb11".
    iEval (rgne; rewrite (HR1o Rs9 ltac:(nz)) Hf11) in "Hb11".
    assert (Hpp018 : add_vec_int (mword_of_int (NX + 0x16) : mword 64) 2
                     = mword_of_int (NX + 0x18)) by pcw.
    iEval (rewrite Hpp018) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x18)) (mword_of_int 0 : mword 6)
              Rs10 R1 (K - 12)%nat u12 b with "Hcg Hpc [] Hb12").
    { iApply (nxi_018 with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc Hb12".
    iEval (rgne; rewrite (HR1o Rs10 ltac:(nz)) Hf12) in "Hb12".
    assert (Hpp01a : add_vec_int (mword_of_int (NX + 0x18) : mword 64) 2
                     = mword_of_int (NX + 0x1a)) by pcw.
    iEval (rewrite Hpp01a) in "Hpc".
    (* ===== +0x1a c.addi4spn s0,sp,96 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (NX + 0x1a))
              (Cregidx (mword_of_int 0)) (mword_of_int 24 : mword 8) Rs0
              R1 (K - 12)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (nxi_01a with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    pose (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply dlk_fp. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2o : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                     c <> Rs0 -> R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (HR2c : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 ->
                     R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (Hpp01c : add_vec_int (mword_of_int (NX + 0x1a) : mword 64) 2
                     = mword_of_int (NX + 0x1c)) by pcw.
    iEval (rewrite Hpp01c) in "Hpc".
    (* ================================================================= *)
    (*  THE SHARED EPILOGUE at +0x5c -- [c.mv a0,s4], twelve pops, the    *)
    (*  [c.addi16sp +96] and [c.jr ra].  FOUR arms reach it (not-a-dir,    *)
    (*  nameiparent hit, dirlookup miss, loop-done) with four different    *)
    (*  bundles, so it takes an ABSTRACT CONTINUATION and speaks only      *)
    (*  about the twelve frame slots, [nx_tregs] and the value of s4.      *)
    (* ================================================================= *)
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    iAssert (□ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDt : CpuId =>
                  nx_tail_body j eb b lks K m sp0 ret_tgt CIDt))%I
      with "[]" as "#Htail".
    { iModIntro.
      iIntros (CIDt Hst Mt rv) "%HTr %HTs4 Hcg Hcnt Hextc Hclmc Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
                                Hb8 Hb9 Hb10 Hb11 Hb12 Hqc".
      destruct HTr as [HTsp HTthr].
      (* +0x5c c.mv a0,s4 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x5c)) Ra0 Rs4 Mt (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (nxi_05c with "Htext"). }
      iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (P0 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Mt !!! Regidx Rs4))]> Mt).
      assert (HP0a0 : P0 !!! Regidx Ra0 = rv).
      { rewrite /P0 upd_eq. rewrite HTs4. apply add_vec_zero_l. }
      assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P0 upd_ne; [exact HTsp | nz]).
      assert (Hqq5e : add_vec_int (mword_of_int (NX + 0x5c) : mword 64) 2
                      = mword_of_int (NX + 0x5e)) by pcw.
      iEval (rewrite Hqq5e) in "Hpc".
      (* +0x5e .. +0x74 : the twelve pops *)
      assert (HT1 : add_vec (P0 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                    = pa_stk sp0 1) by (rewrite HP0sp; apply dlk_frm1).
      iEval (rewrite -HT1) in "Hb1".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x5e)) (mword_of_int 11 : mword 6)
                Rra P0 (K - 12)%nat (m !!! Regidx Rra : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb1").
      { iApply (nxi_05e with "Htext"). }
      iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
      pose (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P1 upd_ne; [exact HP0sp | nz]).
      assert (Hqq60 : add_vec_int (mword_of_int (NX + 0x5e) : mword 64) 2
                      = mword_of_int (NX + 0x60)) by pcw.
      iEval (rewrite Hqq60) in "Hpc".
      assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                    = pa_stk sp0 2) by (rewrite HP1sp; apply dlk_frm2).
      iEval (rewrite -HT2) in "Hb2".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x60)) (mword_of_int 10 : mword 6)
                Rs0 P1 (K - 12)%nat (m !!! Regidx Rs0 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb2").
      { iApply (nxi_060 with "Htext"). }
      iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
      pose (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
      assert (Hqq62 : add_vec_int (mword_of_int (NX + 0x60) : mword 64) 2
                      = mword_of_int (NX + 0x62)) by pcw.
      iEval (rewrite Hqq62) in "Hpc".
      assert (HT3 : add_vec (P2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite HP2sp; apply dlk_frm3).
      iEval (rewrite -HT3) in "Hb3".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x62)) (mword_of_int 9 : mword 6)
                Rs1 P2 (K - 12)%nat (m !!! Regidx Rs1 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb3").
      { iApply (nxi_062 with "Htext"). }
      iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
      pose (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
      assert (Hqq64 : add_vec_int (mword_of_int (NX + 0x62) : mword 64) 2
                      = mword_of_int (NX + 0x64)) by pcw.
      iEval (rewrite Hqq64) in "Hpc".
      assert (HT4 : add_vec (P3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite HP3sp; apply dlk_frm4).
      iEval (rewrite -HT4) in "Hb4".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x64)) (mword_of_int 8 : mword 6)
                Rs2 P3 (K - 12)%nat (m !!! Regidx Rs2 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb4").
      { iApply (nxi_064 with "Htext"). }
      iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
      pose (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
      assert (Hqq66 : add_vec_int (mword_of_int (NX + 0x64) : mword 64) 2
                      = mword_of_int (NX + 0x66)) by pcw.
      iEval (rewrite Hqq66) in "Hpc".
      assert (HT5 : add_vec (P4 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HP4sp; apply dlk_frm5).
      iEval (rewrite -HT5) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x66)) (mword_of_int 7 : mword 6)
                Rs3 P4 (K - 12)%nat (m !!! Regidx Rs3 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb5").
      { iApply (nxi_066 with "Htext"). }
      iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
      pose (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
      assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
      assert (Hqq68 : add_vec_int (mword_of_int (NX + 0x66) : mword 64) 2
                      = mword_of_int (NX + 0x68)) by pcw.
      iEval (rewrite Hqq68) in "Hpc".
      assert (HT6 : add_vec (P5 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk sp0 6) by (rewrite HP5sp; apply dlk_frm6).
      iEval (rewrite -HT6) in "Hb6".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x68)) (mword_of_int 6 : mword 6)
                Rs4 P5 (K - 12)%nat (m !!! Regidx Rs4 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb6").
      { iApply (nxi_068 with "Htext"). }
      iIntros (CIDT6 HqT6) "Hcg Hpc Hb6".
      pose (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
      assert (HP6sp : P6 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
      assert (Hqq6a : add_vec_int (mword_of_int (NX + 0x68) : mword 64) 2
                      = mword_of_int (NX + 0x6a)) by pcw.
      iEval (rewrite Hqq6a) in "Hpc".
      assert (HT7 : add_vec (P6 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 7) by (rewrite HP6sp; apply dlk_frm7).
      iEval (rewrite -HT7) in "Hb7".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6a)) (mword_of_int 5 : mword 6)
                Rs5 P6 (K - 12)%nat (m !!! Regidx Rs5 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb7").
      { iApply (nxi_06a with "Htext"). }
      iIntros (CIDT7 HqT7) "Hcg Hpc Hb7".
      pose (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
      assert (HP7sp : P7 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
      assert (Hqq6c : add_vec_int (mword_of_int (NX + 0x6a) : mword 64) 2
                      = mword_of_int (NX + 0x6c)) by pcw.
      iEval (rewrite Hqq6c) in "Hpc".
      assert (HT8 : add_vec (P7 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                    = pa_stk sp0 8) by (rewrite HP7sp; apply dlk_frm8).
      iEval (rewrite -HT8) in "Hb8".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6c)) (mword_of_int 4 : mword 6)
                Rs6 P7 (K - 12)%nat (m !!! Regidx Rs6 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb8").
      { iApply (nxi_06c with "Htext"). }
      iIntros (CIDT8 HqT8) "Hcg Hpc Hb8".
      pose (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
      assert (HP8sp : P8 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P8 upd_ne; [exact HP7sp | nz]).
      assert (Hqq6e : add_vec_int (mword_of_int (NX + 0x6c) : mword 64) 2
                      = mword_of_int (NX + 0x6e)) by pcw.
      iEval (rewrite Hqq6e) in "Hpc".
      assert (HT9 : add_vec (P8 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk sp0 9) by (rewrite HP8sp; apply dlk_frm9).
      iEval (rewrite -HT9) in "Hb9".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x6e)) (mword_of_int 3 : mword 6)
                Rs7 P8 (K - 12)%nat (m !!! Regidx Rs7 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb9").
      { iApply (nxi_06e with "Htext"). }
      iIntros (CIDT9 HqT9) "Hcg Hpc Hb9".
      pose (P9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P8).
      assert (HP9sp : P9 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P9 upd_ne; [exact HP8sp | nz]).
      assert (Hqq70 : add_vec_int (mword_of_int (NX + 0x6e) : mword 64) 2
                      = mword_of_int (NX + 0x70)) by pcw.
      iEval (rewrite Hqq70) in "Hpc".
      assert (HT10 : add_vec (P9 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                     = pa_stk sp0 10) by (rewrite HP9sp; apply nx_frm10).
      iEval (rewrite -HT10) in "Hb10".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x70)) (mword_of_int 2 : mword 6)
                Rs8 P9 (K - 12)%nat (m !!! Regidx Rs8 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb10").
      { iApply (nxi_070 with "Htext"). }
      iIntros (CIDT10 HqT10) "Hcg Hpc Hb10".
      pose (P10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> P9).
      assert (HP10sp : P10 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P10 upd_ne; [exact HP9sp | nz]).
      assert (Hqq72 : add_vec_int (mword_of_int (NX + 0x70) : mword 64) 2
                      = mword_of_int (NX + 0x72)) by pcw.
      iEval (rewrite Hqq72) in "Hpc".
      assert (HT11 : add_vec (P10 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                     = pa_stk sp0 11) by (rewrite HP10sp; apply nx_frm11).
      iEval (rewrite -HT11) in "Hb11".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x72)) (mword_of_int 1 : mword 6)
                Rs9 P10 (K - 12)%nat (m !!! Regidx Rs9 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb11").
      { iApply (nxi_072 with "Htext"). }
      iIntros (CIDT11 HqT11) "Hcg Hpc Hb11".
      pose (P11 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> P10).
      assert (HP11sp : P11 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P11 upd_ne; [exact HP10sp | nz]).
      assert (Hqq74 : add_vec_int (mword_of_int (NX + 0x72) : mword 64) 2
                      = mword_of_int (NX + 0x74)) by pcw.
      iEval (rewrite Hqq74) in "Hpc".
      assert (HT12 : add_vec (P11 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                     = pa_stk sp0 12) by (rewrite HP11sp; apply nx_frm12).
      iEval (rewrite -HT12) in "Hb12".
      iApply (wp_cldsp_s_sconf (mword_of_int (NX + 0x74)) (mword_of_int 0 : mword 6)
                Rs10 P11 (K - 12)%nat (m !!! Regidx Rs10 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hb12").
      { iApply (nxi_074 with "Htext"). }
      iIntros (CIDT12 HqT12) "Hcg Hpc Hb12".
      pose (P12 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> P11).
      assert (HP12sp : P12 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P12 upd_ne; [exact HP11sp | nz]).
      assert (Hqq76 : add_vec_int (mword_of_int (NX + 0x74) : mword 64) 2
                      = mword_of_int (NX + 0x76)) by pcw.
      iEval (rewrite Hqq76) in "Hpc".
      iEval (rewrite HT1) in "Hb1".   iEval (rewrite HT2) in "Hb2".
      iEval (rewrite HT3) in "Hb3".   iEval (rewrite HT4) in "Hb4".
      iEval (rewrite HT5) in "Hb5".   iEval (rewrite HT6) in "Hb6".
      iEval (rewrite HT7) in "Hb7".   iEval (rewrite HT8) in "Hb8".
      iEval (rewrite HT9) in "Hb9".   iEval (rewrite HT10) in "Hb10".
      iEval (rewrite HT11) in "Hb11". iEval (rewrite HT12) in "Hb12".
      iAssert (stack_own (KTR := KT1) sp0 12) with
        "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12]" as "Hstk".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
        iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
        iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
        iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
        iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
        iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
        iSplitL "Hb7"; [iExists _; iExact "Hb7" |].
        iSplitL "Hb8"; [iExists _; iExact "Hb8" |].
        iSplitL "Hb9"; [iExists _; iExact "Hb9" |].
        iSplitL "Hb10"; [iExists _; iExact "Hb10" |].
        iSplitL "Hb11"; [iExists _; iExact "Hb11" |].
        iSplitL "Hb12"; [iExists _; iExact "Hb12" |].
        done. }
      (* ===== +0x76 c.addi16sp sp,96 : the pop ===== *)
      assert (Hwv : add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                    = sp0) by (rewrite HP12sp; apply dlk_pop).
      assert (Hpop : (P12 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12)
        by (rewrite Hwv; exact HP12sp).
      iEval (rewrite -Hwv) in "Hstk".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (NX + 0x76))
                (mword_of_int 6 : mword 6) P12 (K - 12)%nat 12 b Hpop
                with "Hcg Hpc [] Hstk").
      { iApply (nxi_076 with "Htext"). }
      iIntros (CIDT13 HqT13) "Hcg Hpc".
      pose (P13 := <[Regidx csp_rs1 := regval_into_reg
                     (add_vec (P12 !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> P12).
      iEval (rewrite Kpop) in "Hcg".
      assert (Hqq78 : add_vec_int (mword_of_int (NX + 0x76) : mword 64) 2
                      = mword_of_int (NX + 0x78)) by pcw.
      iEval (rewrite Hqq78) in "Hpc".
      (* ===== +0x78 c.jr ra ===== *)
      assert (CPra : P13 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
        rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
        rewrite /P1 upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf (mword_of_int (NX + 0x78)) Rra P13 K b
                ltac:(nz) with "Hcg Hpc []").
      { iApply (nxi_078 with "Htext"). }
      iIntros (CIDT14 HqT14) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (P13 !!! Regidx Rra : mword 64) = ret_tgt)
        by (rewrite CPra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* ===== the callee-saved record ===== *)
      assert (CPsp : P13 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
      { rewrite /P13 upd_eq. rewrite Hwv. symmetry. exact Hspm. }
      assert (CPs0 : P13 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
        rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
      assert (CPs1 : P13 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
        rewrite /P3 upd_eq. reflexivity. }
      assert (CPs2 : P13 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
      assert (CPs3 : P13 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_eq. reflexivity. }
      assert (CPs4 : P13 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_eq. reflexivity. }
      assert (CPs5 : P13 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_eq. reflexivity. }
      assert (CPs6 : P13 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_eq. reflexivity. }
      assert (CPs7 : P13 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_eq. reflexivity. }
      assert (CPs8 : P13 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_eq. reflexivity. }
      assert (CPs9 : P13 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_eq. reflexivity. }
      assert (CPs10 : P13 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_eq. reflexivity. }
      assert (CPo : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
                c <> Rs9 -> c <> Rs10 ->
                P13 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
        rewrite /P13 upd_ne; [| dlk_xne N2].
        rewrite /P12 upd_ne; [| dlk_xne N26].
        rewrite /P11 upd_ne; [| dlk_xne N25].
        rewrite /P10 upd_ne; [| dlk_xne N24].
        rewrite /P9 upd_ne; [| dlk_xne N23].
        rewrite /P8 upd_ne; [| dlk_xne N22].
        rewrite /P7 upd_ne; [| dlk_xne N21].
        rewrite /P6 upd_ne; [| dlk_xne N20].
        rewrite /P5 upd_ne; [| dlk_xne N19].
        rewrite /P4 upd_ne; [| dlk_xne N18].
        rewrite /P3 upd_ne; [| dlk_xne N9].
        rewrite /P2 upd_ne; [| dlk_xne N8].
        rewrite /P1 upd_ne; [| dlk_rne2 Hcsra Hc].
        rewrite /P0 upd_ne;
          [ exact (HTthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
          | dlk_rne2 Hcsa0 Hc ]. }
      assert (CPa0 : P13 !!! Regidx Ra0 = rv).
      { rewrite /P13 upd_ne; [| nz]. rewrite /P12 upd_ne; [| nz].
        rewrite /P11 upd_ne; [| nz]. rewrite /P10 upd_ne; [| nz].
        rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
        rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
        rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
        rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
        rewrite /P1 upd_ne; [exact HP0a0 | nz]. }
      iDestruct (cpu_own_transport CIDt CIDT14 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDt CIDT14 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDt CIDT14 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iSpecialize ("Hqc" $! CIDT14 with "[%]"); [wp_next_chain |].
      iApply ("Hqc" $! P13 with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc").
      - unfold callee_saved. split_and!;
          first [ exact CPsp | exact CPs0 | exact CPs1 | exact CPs2 | exact CPs3
                | exact CPs4 | exact CPs5 | exact CPs6 | exact CPs7
                | exact CPs8 | exact CPs9 | exact CPs10
                | apply CPo; first [ vm_compute; reflexivity
                                   | vm_compute; discriminate ] ].
      - exact CPa0. }
    (* ================================================================= *)
    (*  THE THREE SCANS.  Each is a []-PERSISTENT, fuel-indexed assertion   *)
    (*  with an ABSTRACT CONTINUATION.  They touch only the path buffer,    *)
    (*  s1 (or s2), a5 -- and a4 in the element scan -- so stating them     *)
    (*  here keeps the walk's thirty-slot invariant out of all three loops  *)
    (*  (the single largest avoidable cost in this file).                   *)
    (* ================================================================= *)
    assert (Hnn : forall i : nat, (i < plen)%nat -> pfun i <> NUL)
      by (intros i Hi; exact (proj1 Hcstr i Hi)).
    assert (Hterm : pfun plen = NUL) by exact (proj2 Hcstr).
    assert (HSN : SLASH <> NUL).
    { intro Hq. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq.
      discriminate. }
    (* a separator is never the terminator, so a byte that IS one sits
       strictly inside the string *)
    assert (Hslt : forall i : nat, (i <= plen)%nat -> pfun i = SLASH ->
                     (i < plen)%nat).
    { intros i Hi Hs. destruct (Nat.eq_dec i plen) as [He | Hne].
      - exfalso. apply HSN. rewrite -Hs He. exact Hterm.
      - lia. }
    assert (Hnult : forall i : nat, (i <= plen)%nat -> pfun i <> NUL ->
                      (i < plen)%nat).
    { intros i Hi Hs. destruct (Nat.eq_dec i plen) as [He | Hne].
      - exfalso. apply Hs. rewrite He. exact Hterm.
      - lia. }
    (* ---- (1) the LEADING separator skip, inner loop at +0xfc ---------- *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_skip_body j b K plen pfun pv dqpv fuel CIDs))%I
      with "[]" as "#Hsk1".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHs".
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        (* +0xfc c.addi s1,s1,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0xfc)) Rs1
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_0fc with "Htext"). }
        iIntros (CIDk1 Hqk1) "Hcg Hpc".
        iEval (rgne; rewrite Hs1 (nx_addi1 pv off)) in "Hcg".
        pose (Q1 := <[Regidx Rs1 := regval_into_reg (pa_add pv (S off))]> Ms).
        assert (HQ1s1 : Q1 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /Q1; apply upd_eq).
        assert (HQ1s3 : Q1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /Q1 upd_ne; [exact Hs3 | nz]).
        assert (Hqee : add_vec_int (mword_of_int (NX + 0xfc) : mword 64) 2
                       = mword_of_int (NX + 0xfe)) by pcw.
        iEval (rewrite Hqee) in "Hpc".
        (* +0xfe lbu a5,0(s1) *)
        iDestruct (nx_buf_acc pv dqpv pfun (S plen) (S off) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xfe)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) Q1 (K - 12)%nat
                  (pfun (S off) : mword 8) b (dqm := dqpv)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
        { iApply (nxi_0fe with "Htext"). }
        { iEval (rgne; rewrite HQ1s1 addv_sext0). iExact "Hpb". }
        iIntros (CIDk2 Hqk2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HQ1s1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        pose (Q2 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun (S off) : mword 8))]> Q1).
        assert (HQ2a5 : Q2 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun (S off) : mword 8) : mword 64))
          by (rewrite /Q2; apply upd_eq).
        assert (HQ2s1 : Q2 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /Q2 upd_ne; [exact HQ1s1 | nz]).
        assert (HQ2s3 : Q2 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /Q2 upd_ne; [exact HQ1s3 | nz]).
        assert (HQ2o : forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
                  Q2 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
        { intros c N9 N15. rewrite /Q2 upd_ne; [| dlk_xne N15].
          rewrite /Q1 upd_ne; [reflexivity | dlk_xne N9]. }
        assert (Hqf2 : add_vec_int (mword_of_int (NX + 0xfe) : mword 64) 4
                       = mword_of_int (NX + 0x102)) by pcw.
        iEval (rewrite Hqf2) in "Hpc".
        assert (Htec : add_vec (mword_of_int (NX + 0x102) : mword 64)
                  (sign_extend' 64 (mword_of_int 8186 : mword 13))
                = mword_of_int (NX + 0xfc)) by pcw.
        destruct (decide (pfun (S off) = SLASH)) as [Hsl2 | Hsl2].
        + (* another separator: [beq s3,a5] back to +0xfc *)
          iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0x102))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 Q2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HQ2a5 HQ2s3;
                          exact (nx_slash_eq _ Hsl2))
                    ltac:(rewrite Htec; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (nxi_102 with "Htext"). }
          iIntros (CIDk3 Hqk3). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htec) in "Hpc".
          iSpecialize ("IHs" $! CIDk3 with "[%]"); [wp_next_chain |].
          iApply ("IHs" $! (S off) Q2
                    with "[%] [%] [%] [%] [%] Hcg Hpc Hpath [Hqc]").
          * lia.
          * exact (Hslt (S off) ltac:(lia) Hsl2).
          * exact Hsl2.
          * exact HQ2s1.
          * exact HQ2s3.
          * iIntros (CIDe Hqe off' Ms')
              "%A1 %A2 %A3 %A4 %A5 %A6 %A7 Hcg Hpc Hpath".
            iSpecialize ("Hqc" $! CIDe with "[%]"); [wp_next_chain |].
            iApply ("Hqc" $! off' Ms'
                      with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
            -- lia.
            -- lia.
            -- intros i Hi1 Hi2. destruct (Nat.eq_dec i off) as [He | Hne].
               ++ rewrite He. exact Hsl.
               ++ apply A3; lia.
            -- exact A4.
            -- exact A5.
            -- exact A6.
            -- intros c N9 N15. rewrite (A7 c N9 N15). exact (HQ2o c N9 N15).
        + (* the first non-separator: [beq] falls through to +0x106 *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0x102))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 Q2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HQ2a5 HQ2s3;
                          exact (nx_slash_ne _ Hsl2))
                    with "Hcg Hpc []").
          { iApply (nxi_102 with "Htext"). }
          iIntros (CIDk3 Hqk3) "Hcg Hpc".
          assert (Hqf6 : add_vec_int (mword_of_int (NX + 0x102) : mword 64) 4
                         = mword_of_int (NX + 0x106)) by pcw.
          iEval (rewrite Hqf6) in "Hpc".
          iSpecialize ("Hqc" $! CIDk3 with "[%]"); [wp_next_chain |].
          iApply ("Hqc" $! (S off) Q2
                    with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
          * lia.
          * lia.
          * intros i Hi1 Hi2. assert (He : i = off) by lia.
            rewrite He. exact Hsl.
          * exact Hsl2.
          * exact HQ2s1.
          * exact HQ2a5.
          * exact HQ2o. }
    (* ---- (2) the TRAILING separator skip, inner loop at +0xb6 ---------
       byte-identical to (1) at three different addresses; the exit is at
       +0xc0, where [ilock]'s argument setup begins. *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_skip2_body j b K plen pfun pv dqpv fuel CIDs))%I
      with "[]" as "#Hsk2".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHt".
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        (* +0xb6 c.addi s1,s1,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0xb6)) Rs1
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_0b6 with "Htext"). }
        iIntros (CIDt1 Hqt1) "Hcg Hpc".
        iEval (rgne; rewrite Hs1 (nx_addi1 pv off)) in "Hcg".
        pose (T1 := <[Regidx Rs1 := regval_into_reg (pa_add pv (S off))]> Ms).
        assert (HT1s1 : T1 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /T1; apply upd_eq).
        assert (HT1s3 : T1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /T1 upd_ne; [exact Hs3 | nz]).
        assert (Hqae : add_vec_int (mword_of_int (NX + 0xb6) : mword 64) 2
                       = mword_of_int (NX + 0xb8)) by pcw.
        iEval (rewrite Hqae) in "Hpc".
        (* +0xb8 lbu a5,0(s1) *)
        iDestruct (nx_buf_acc pv dqpv pfun (S plen) (S off) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xb8)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) T1 (K - 12)%nat
                  (pfun (S off) : mword 8) b (dqm := dqpv)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
        { iApply (nxi_0b8 with "Htext"). }
        { iEval (rgne; rewrite HT1s1 addv_sext0). iExact "Hpb". }
        iIntros (CIDt2 Hqt2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HT1s1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        pose (T2 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun (S off) : mword 8))]> T1).
        assert (HT2a5 : T2 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun (S off) : mword 8) : mword 64))
          by (rewrite /T2; apply upd_eq).
        assert (HT2s1 : T2 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /T2 upd_ne; [exact HT1s1 | nz]).
        assert (HT2s3 : T2 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /T2 upd_ne; [exact HT1s3 | nz]).
        assert (HT2o : forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
                  T2 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
        { intros c N9 N15. rewrite /T2 upd_ne; [| dlk_xne N15].
          rewrite /T1 upd_ne; [reflexivity | dlk_xne N9]. }
        assert (Hqb2 : add_vec_int (mword_of_int (NX + 0xb8) : mword 64) 4
                       = mword_of_int (NX + 0xbc)) by pcw.
        iEval (rewrite Hqb2) in "Hpc".
        assert (Htac : add_vec (mword_of_int (NX + 0xbc) : mword 64)
                  (sign_extend' 64 (mword_of_int 8186 : mword 13))
                = mword_of_int (NX + 0xb6)) by pcw.
        destruct (decide (pfun (S off) = SLASH)) as [Hsl2 | Hsl2].
        + iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0xbc))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 T2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HT2a5 HT2s3;
                          exact (nx_slash_eq _ Hsl2))
                    ltac:(rewrite Htac; vm_compute; reflexivity)
                    with "Hcg Hpc []").
        { iApply (nxi_0bc with "Htext"). }
          iIntros (CIDt3 Hqt3). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htac) in "Hpc".
          iSpecialize ("IHt" $! CIDt3 with "[%]"); [wp_next_chain |].
          iApply ("IHt" $! (S off) T2
                    with "[%] [%] [%] [%] [%] Hcg Hpc Hpath [Hqc]").
          * lia.
          * exact (Hslt (S off) ltac:(lia) Hsl2).
          * exact Hsl2.
          * exact HT2s1.
          * exact HT2s3.
          * iIntros (CIDe Hqe off' Ms')
              "%A1 %A2 %A3 %A4 %A5 %A6 %A7 Hcg Hpc Hpath".
            iSpecialize ("Hqc" $! CIDe with "[%]"); [wp_next_chain |].
            iApply ("Hqc" $! off' Ms'
                      with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
            -- lia.
            -- lia.
            -- intros i Hi1 Hi2. destruct (Nat.eq_dec i off) as [He | Hne].
               ++ rewrite He. exact Hsl.
               ++ apply A3; lia.
            -- exact A4.
            -- exact A5.
            -- exact A6.
            -- intros c N9 N15. rewrite (A7 c N9 N15). exact (HT2o c N9 N15).
        + iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0xbc))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 T2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HT2a5 HT2s3;
                          exact (nx_slash_ne _ Hsl2))
                    with "Hcg Hpc []").
            { iApply (nxi_0bc with "Htext"). }
          iIntros (CIDt3 Hqt3) "Hcg Hpc".
          assert (Hqb6 : add_vec_int (mword_of_int (NX + 0xbc) : mword 64) 4
                         = mword_of_int (NX + 0xc0)) by pcw.
          iEval (rewrite Hqb6) in "Hpc".
          iSpecialize ("Hqc" $! CIDt3 with "[%]"); [wp_next_chain |].
          iApply ("Hqc" $! (S off) T2
                    with "[%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
          * lia.
          * lia.
          * intros i Hi1 Hi2. assert (He : i = off) by lia.
            rewrite He. exact Hsl.
          * exact Hsl2.
          * exact HT2s1.
          * exact HT2a5.
          * exact HT2o. }
    (* ---- (3) the ELEMENT scan, inner loop at +0x116 -------------------
       [s2] runs forward until the byte it points at is a separator or the
       terminator; the [addi a4,a5,-47] at +0x11c is the separator test and
       the [c.bnez a5] at +0x122 the terminator test.  BOTH exits leave at
       +0x96, where the length is computed. *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_scan_body j b K plen pfun pv dqpv fuel CIDs))%I
      with "[]" as "#Hscn".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHe".
      - iModIntro.
        iIntros (CIDs Hss ii Ms) "%Hf %Hilt %Hs2 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss ii Ms) "%Hf %Hilt %Hs2 Hcg Hpc Hpath Hqc".
        (* +0x116 c.addi s2,s2,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0x116)) Rs2
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_116 with "Htext"). }
        iIntros (CIDe1 Hqe1) "Hcg Hpc".
        iEval (rgne; rewrite Hs2 (nx_addi1 pv ii)) in "Hcg".
        pose (E1 := <[Regidx Rs2 := regval_into_reg (pa_add pv (S ii))]> Ms).
        assert (HE1s2 : E1 !!! Regidx Rs2 = pa_add pv (S ii))
          by (rewrite /E1; apply upd_eq).
        assert (Hq108 : add_vec_int (mword_of_int (NX + 0x116) : mword 64) 2
                        = mword_of_int (NX + 0x118)) by pcw.
        iEval (rewrite Hq108) in "Hpc".
        (* +0x118 lbu a5,0(s2) *)
        iDestruct (nx_buf_acc pv dqpv pfun (S plen) (S ii) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0x118)) Ra5 Rs2
                  (mword_of_int 0 : mword 12) E1 (K - 12)%nat
                  (pfun (S ii) : mword 8) b (dqm := dqpv)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
        { iApply (nxi_118 with "Htext"). }
        { iEval (rgne; rewrite HE1s2 addv_sext0). iExact "Hpb". }
        iIntros (CIDe2 Hqe2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HE1s2 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        pose (E2 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun (S ii) : mword 8))]> E1).
        assert (HE2a5 : E2 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun (S ii) : mword 8) : mword 64))
          by (rewrite /E2; apply upd_eq).
        assert (HE2s2 : E2 !!! Regidx Rs2 = pa_add pv (S ii))
          by (rewrite /E2 upd_ne; [exact HE1s2 | nz]).
        assert (Hq10c : add_vec_int (mword_of_int (NX + 0x118) : mword 64) 4
                        = mword_of_int (NX + 0x11c)) by pcw.
        iEval (rewrite Hq10c) in "Hpc".
        (* +0x11c addi a4,a5,-47 *)
        iApply (wp_addi4_s_sconf (mword_of_int (NX + 0x11c)) Ra4 Ra5
                  (mword_of_int 4049 : mword 12) E2 (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_11c with "Htext"). }
        iIntros (CIDe3 Hqe3) "Hcg Hpc".
        iEval (rgne; rewrite HE2a5) in "Hcg".
        pose (E3 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (zero_extend' 64 (pfun (S ii) : mword 8) : mword 64)
                         (sign_extend' 64 (mword_of_int 4049 : mword 12)))]> E2).
        assert (HE3a4 : E3 !!! Regidx Ra4
                        = add_vec (zero_extend' 64 (pfun (S ii) : mword 8)
                                     : mword 64)
                            (sign_extend' 64 (mword_of_int 4049 : mword 12)))
          by (rewrite /E3; apply upd_eq).
        assert (HE3a5 : E3 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun (S ii) : mword 8) : mword 64))
          by (rewrite /E3 upd_ne; [exact HE2a5 | nz]).
        assert (HE3s2 : E3 !!! Regidx Rs2 = pa_add pv (S ii))
          by (rewrite /E3 upd_ne; [exact HE2s2 | nz]).
        assert (HE3o : forall c : mword 5, c <> Rs2 -> c <> Ra5 -> c <> Ra4 ->
                  E3 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
        { intros c N18 N15 N14. rewrite /E3 upd_ne; [| dlk_xne N14].
          rewrite /E2 upd_ne; [| dlk_xne N15].
          rewrite /E1 upd_ne; [reflexivity | dlk_xne N18]. }
        assert (Hq110 : add_vec_int (mword_of_int (NX + 0x11c) : mword 64) 4
                        = mword_of_int (NX + 0x120)) by pcw.
        iEval (rewrite Hq110) in "Hpc".
        assert (Ht8c : add_vec (mword_of_int (NX + 0x120) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 187 : mword 8) ('b"0"))))
                = mword_of_int (NX + 0x96)) by pcw.
        destruct (decide (pfun (S ii) = SLASH)) as [Hsl2 | Hsl2].
        + (* a separator: [c.beqz a4] leaves for +0x96 *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (NX + 0x120))
                    (mword_of_int 187 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                    E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HE3a4; exact (nx_a4_eq _ Hsl2))
                    ltac:(rewrite Ht8c; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (nxi_120 with "Htext"). }
          iIntros (CIDe4 Hqe4). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Ht8c) in "Hpc".
          iSpecialize ("Hqc" $! CIDe4 with "[%]"); [wp_next_chain |].
          iApply ("Hqc" $! (S ii) E3
                    with "[%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
          * lia.
          * lia.
          * intros jj Hj1 Hj2. exfalso. lia.
          * left. exact Hsl2.
          * exact HE3s2.
          * exact HE3o.
        + (* not a separator: [c.beqz a4] falls through to +0x122 *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x120))
                    (mword_of_int 187 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                    E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HE3a4; exact (nx_a4_ne _ Hsl2))
                    with "Hcg Hpc []").
          { iApply (nxi_120 with "Htext"). }
          iIntros (CIDe4 Hqe4) "Hcg Hpc".
          assert (Hq112 : add_vec_int (mword_of_int (NX + 0x120) : mword 64) 2
                          = mword_of_int (NX + 0x122)) by pcw.
          iEval (rewrite Hq112) in "Hpc".
          assert (Ht106 : add_vec (mword_of_int (NX + 0x122) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 250 : mword 8) ('b"0"))))
                  = mword_of_int (NX + 0x116)) by pcw.
          destruct (decide (pfun (S ii) = NUL)) as [Hnl2 | Hnl2].
          * (* the terminator: [c.bnez a5] falls through, +0x124 jumps *)
            iApply (wp_cbnez_fall_s_sconf (mword_of_int (NX + 0x122))
                      (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HE3a5; exact (nx_nnul_eq _ Hnl2))
                      with "Hcg Hpc []").
            { iApply (nxi_122 with "Htext"). }
            iIntros (CIDe5 Hqe5) "Hcg Hpc".
            assert (Hq114 : add_vec_int (mword_of_int (NX + 0x122) : mword 64) 2
                            = mword_of_int (NX + 0x124)) by pcw.
            iEval (rewrite Hq114) in "Hpc".
            assert (Ht8c2 : add_vec (mword_of_int (NX + 0x124) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1977 : mword 11) ('b"0"))))
                    = mword_of_int (NX + 0x96)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (NX + 0x124))
                      (sign_extend' 21
                         (concat_vec (mword_of_int 1977 : mword 11) ('b"0")))
                      E3 (K - 12)%nat b
                      ltac:(rewrite Ht8c2; vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (nxi_124 with "Htext"). }
            iIntros (CIDe6 Hqe6). iApply bi.later_intro. iIntros "Hcg Hpc".
            iEval (rewrite Ht8c2) in "Hpc".
            (* the terminator pins the index: [bb_cstr] has no earlier NUL *)
            assert (Hep : (S ii = plen)%nat).
            { destruct (Nat.eq_dec (S ii) plen) as [He | Hne]; [exact He |].
              exfalso. exact (Hnn (S ii) ltac:(lia) Hnl2). }
            iSpecialize ("Hqc" $! CIDe6 with "[%]"); [wp_next_chain |].
            iApply ("Hqc" $! (S ii) E3
                      with "[%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
            -- lia.
            -- lia.
            -- intros jj Hj1 Hj2. exfalso. lia.
            -- right. exact Hep.
            -- exact HE3s2.
            -- exact HE3o.
          * (* an ordinary byte: [c.bnez a5] loops back to +0x116 *)
            iApply (wp_cbnez_taken_s_sconf (mword_of_int (NX + 0x122))
                      (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HE3a5; exact (nx_nnul_ne _ Hnl2))
                      ltac:(rewrite Ht106; vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (nxi_122 with "Htext"). }
            iIntros (CIDe5 Hqe5). iApply bi.later_intro. iIntros "Hcg Hpc".
            iEval (rewrite Ht106) in "Hpc".
            iSpecialize ("IHe" $! CIDe5 with "[%]"); [wp_next_chain |].
            iApply ("IHe" $! (S ii) E3 with "[%] [%] [%] Hcg Hpc Hpath [Hqc]").
            -- lia.
            -- exact (Hnult (S ii) ltac:(lia) Hnl2).
            -- exact HE3s2.
            -- iIntros (CIDe7 Hqe7 e Ms')
                 "%B1 %B2 %B3 %B4 %B5 %B6 Hcg Hpc Hpath".
               iSpecialize ("Hqc" $! CIDe7 with "[%]"); [wp_next_chain |].
               iApply ("Hqc" $! e Ms'
                         with "[%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
               ++ lia.
               ++ lia.
               ++ intros jj Hj1 Hj2.
                  destruct (Nat.eq_dec jj (S ii)) as [He | Hne].
                  ** rewrite He. exact Hsl2.
                  ** apply B3; lia.
               ++ exact B4.
               ++ exact B5.
               ++ intros c N18 N15 N14. rewrite (B6 c N18 N15 N14).
                  exact (HE3o c N18 N15 N14). }
    (* ---- (4) +0x106 .. +0x114: the terminator test AND THE DEAD BLOCK ---
       Two exits, so TWO abstract continuations.  +0x108..+0x112 re-loads the
       byte and re-tests it against '/' and 0 -- both were just decided, so
       both [c.beqz]es fall through and +0x126 is unreachable. *)
    iAssert (□ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_mid_body j b K plen pfun pv dqpv CIDs))%I
      with "[]" as "#Hmid".
    { iModIntro.
      iIntros (CIDs Hss a Ms) "%Halt %Hns %Hs1 %Ha5 Hcg Hpc Hpath HqA HqB".
      assert (Ht130 : add_vec (mword_of_int (NX + 0x106) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 29 : mword 8) ('b"0"))))
              = mword_of_int (NX + 0x140)) by pcw.
      destruct (decide (pfun a = NUL)) as [Hnl | Hnl].
      - (* the terminator: [c.beqz a5] leaves the walk for +0x140 *)
        iClear "HqB".
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (NX + 0x106))
                  (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Ms (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Ha5; exact (nx_nul_eq _ Hnl))
                  ltac:(rewrite Ht130; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (nxi_106 with "Htext"). }
        iIntros (CIDm1 Hqm1). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Ht130) in "Hpc".
        assert (Hap : (a = plen)%nat).
        { destruct (Nat.eq_dec a plen) as [He | Hne]; [exact He |].
          exfalso. exact (Hnn a ltac:(lia) Hnl). }
        iSpecialize ("HqA" $! CIDm1 with "[%]"); [wp_next_chain |].
        iApply ("HqA" with "[%] Hcg Hpc Hpath"). exact Hap.
      - (* an element begins here: fall into the DEAD block *)
        iClear "HqA".
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x106))
                  (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Ms (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Ha5; exact (nx_nul_ne _ Hnl))
                  with "Hcg Hpc []").
        { iApply (nxi_106 with "Htext"). }
        iIntros (CIDm1 Hqm1) "Hcg Hpc".
        assert (Hqf8 : add_vec_int (mword_of_int (NX + 0x106) : mword 64) 2
                       = mword_of_int (NX + 0x108)) by pcw.
        iEval (rewrite Hqf8) in "Hpc".
        (* +0x108 lbu a5,0(s1) -- the SAME byte, read again *)
        iDestruct (nx_buf_acc pv dqpv pfun (S plen) a ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0x108)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                  (pfun a : mword 8) b (dqm := dqpv)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
        { iApply (nxi_108 with "Htext"). }
        { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
        iIntros (CIDm2 Hqm2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        pose (D1 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun a : mword 8))]> Ms).
        assert (HD1a5 : D1 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun a : mword 8) : mword 64))
          by (rewrite /D1; apply upd_eq).
        assert (HD1s1 : D1 !!! Regidx Rs1 = pa_add pv a)
          by (rewrite /D1 upd_ne; [exact Hs1 | nz]).
        assert (Hqfc : add_vec_int (mword_of_int (NX + 0x108) : mword 64) 4
                       = mword_of_int (NX + 0x10c)) by pcw.
        iEval (rewrite Hqfc) in "Hpc".
        (* +0x10c addi a4,a5,-47 *)
        iApply (wp_addi4_s_sconf (mword_of_int (NX + 0x10c)) Ra4 Ra5
                  (mword_of_int 4049 : mword 12) D1 (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_10c with "Htext"). }
        iIntros (CIDm3 Hqm3) "Hcg Hpc".
        iEval (rgne; rewrite HD1a5) in "Hcg".
        pose (D2 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (zero_extend' 64 (pfun a : mword 8) : mword 64)
                         (sign_extend' 64 (mword_of_int 4049 : mword 12)))]> D1).
        assert (HD2a4 : D2 !!! Regidx Ra4
                        = add_vec (zero_extend' 64 (pfun a : mword 8) : mword 64)
                            (sign_extend' 64 (mword_of_int 4049 : mword 12)))
          by (rewrite /D2; apply upd_eq).
        assert (HD2a5 : D2 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun a : mword 8) : mword 64))
          by (rewrite /D2 upd_ne; [exact HD1a5 | nz]).
        assert (HD2s1 : D2 !!! Regidx Rs1 = pa_add pv a)
          by (rewrite /D2 upd_ne; [exact HD1s1 | nz]).
        assert (Hq100 : add_vec_int (mword_of_int (NX + 0x10c) : mword 64) 4
                        = mword_of_int (NX + 0x110)) by pcw.
        iEval (rewrite Hq100) in "Hpc".
        (* +0x110 c.beqz a4 -- DEAD: the byte is not '/' *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x110))
                  (mword_of_int 11 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  D2 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD2a4; exact (nx_a4_ne _ Hns))
                  with "Hcg Hpc []").
        { iApply (nxi_110 with "Htext"). }
        iIntros (CIDm4 Hqm4) "Hcg Hpc".
        assert (Hq102 : add_vec_int (mword_of_int (NX + 0x110) : mword 64) 2
                        = mword_of_int (NX + 0x112)) by pcw.
        iEval (rewrite Hq102) in "Hpc".
        (* +0x112 c.beqz a5 -- DEAD: the byte is not the terminator *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x112))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  D2 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD2a5; exact (nx_nul_ne _ Hnl))
                  with "Hcg Hpc []").
        { iApply (nxi_112 with "Htext"). }
        iIntros (CIDm5 Hqm5) "Hcg Hpc".
        assert (Hq104 : add_vec_int (mword_of_int (NX + 0x112) : mword 64) 2
                        = mword_of_int (NX + 0x114)) by pcw.
        iEval (rewrite Hq104) in "Hpc".
        (* +0x114 c.mv s2,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x114)) Rs2 Rs1
                  D2 (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (nxi_114 with "Htext"). }
        iIntros (CIDm6 Hqm6) "Hcg Hpc". iEval (rgne) in "Hcg".
        iEval (rewrite HD2s1) in "Hcg".
        pose (D3 := <[Regidx Rs2 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (pa_add pv a))]> D2).
        assert (HD3s2 : D3 !!! Regidx Rs2 = pa_add pv a).
        { rewrite /D3 upd_eq. apply add_vec_zero_l. }
        assert (HD3s1 : D3 !!! Regidx Rs1 = pa_add pv a)
          by (rewrite /D3 upd_ne; [exact HD2s1 | nz]).
        assert (HD3o : forall c : mword 5, c <> Ra5 -> c <> Ra4 -> c <> Rs2 ->
                  D3 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
        { intros c N15 N14 N18. rewrite /D3 upd_ne; [| dlk_xne N18].
          rewrite /D2 upd_ne; [| dlk_xne N14].
          rewrite /D1 upd_ne; [reflexivity | dlk_xne N15]. }
        assert (Hq106 : add_vec_int (mword_of_int (NX + 0x114) : mword 64) 2
                        = mword_of_int (NX + 0x116)) by pcw.
        iEval (rewrite Hq106) in "Hpc".
        iSpecialize ("HqB" $! CIDm6 with "[%]"); [wp_next_chain |].
        iApply ("HqB" $! D3 with "[%] [%] [%] [%] [%] Hcg Hpc Hpath").
        + exact (Hnult a Halt Hnl).
        + exact Hnl.
        + exact HD3s1.
        + exact HD3s2.
        + exact HD3o. }
    (* ---- (5) +0xf4 .. +0x114: the whole loop head -------------------- *)
    iAssert (□ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_head_body j b K plen pfun pv dqpv CIDs))%I
      with "[]" as "#Hhead".
    { iModIntro.
      iIntros (CIDs Hss off Ms) "%Holt %Hs1 %Hs3 Hcg Hpc Hpath HqA HqB".
      (* +0xf4 lbu a5,0(s1) *)
      iDestruct (nx_buf_acc pv dqpv pfun (S plen) off ltac:(lia)
                   with "Hpath") as "[Hpb Hpback]".
      iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xf4)) Ra5 Rs1
                (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                (pfun off : mword 8) b (dqm := dqpv)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
      { iApply (nxi_0f4 with "Htext"). }
      { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
      iIntros (CIDh1 Hqh1) "Hcg Hpc Hpb".
      iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
      iDestruct ("Hpback" with "Hpb") as "Hpath".
      pose (H1 := <[Regidx Ra5 := regval_into_reg
                    (zero_extend' 64 (pfun off : mword 8))]> Ms).
      assert (HH1a5 : H1 !!! Regidx Ra5
                      = (zero_extend' 64 (pfun off : mword 8) : mword 64))
        by (rewrite /H1; apply upd_eq).
      assert (HH1s1 : H1 !!! Regidx Rs1 = pa_add pv off)
        by (rewrite /H1 upd_ne; [exact Hs1 | nz]).
      assert (HH1s3 : H1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
        by (rewrite /H1 upd_ne; [exact Hs3 | nz]).
      assert (HH1o : forall c : mword 5, c <> Ra5 ->
                H1 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
      { intros c N15. rewrite /H1 upd_ne; [reflexivity | dlk_xne N15]. }
      assert (Hqe8 : add_vec_int (mword_of_int (NX + 0xf4) : mword 64) 4
                     = mword_of_int (NX + 0xf8)) by pcw.
      iEval (rewrite Hqe8) in "Hpc".
      assert (Htf6 : add_vec (mword_of_int (NX + 0xf8) : mword 64)
                (sign_extend' 64 (mword_of_int 14 : mword 13))
              = mword_of_int (NX + 0x106)) by pcw.
      destruct (decide (pfun off = SLASH)) as [Hsl0 | Hsl0].
      - (* a separator: [bne] falls through into the skip at +0xfc *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xf8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 H1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HH1a5 HH1s3;
                        exact (nx_nslash_eq _ Hsl0))
                  with "Hcg Hpc []").
        { iApply (nxi_0f8 with "Htext"). }
        iIntros (CIDh2 Hqh2) "Hcg Hpc".
        assert (Hqec : add_vec_int (mword_of_int (NX + 0xf8) : mword 64) 4
                       = mword_of_int (NX + 0xfc)) by pcw.
        iEval (rewrite Hqec) in "Hpc".
        iSpecialize ("Hsk1" $! plen CIDh2 with "[%]"); [wp_next_chain |].
        iApply ("Hsk1" $! off H1
                  with "[%] [%] [%] [%] [%] Hcg Hpc Hpath [HqA HqB]").
        + lia.
        + exact (Hslt off Holt Hsl0).
        + exact Hsl0.
        + exact HH1s1.
        + exact HH1s3.
        + iIntros (CIDh3 Hqh3 a M2) "%A1 %A2 %A3 %A4 %A5 %A6 %A7 Hcg Hpc Hpath".
          iSpecialize ("Hmid" $! CIDh3 with "[%]"); [wp_next_chain |].
          iApply ("Hmid" $! a M2
                    with "[%] [%] [%] [%] Hcg Hpc Hpath [HqA] [HqB]").
          * exact A2.
          * exact A4.
          * exact A5.
          * exact A6.
          * iIntros (CIDh4 Hqh4) "%Hap Hcg Hpc Hpath".
            iSpecialize ("HqA" $! CIDh4 with "[%]"); [wp_next_chain |].
            iApply ("HqA" $! M2 with "[%] [%] [%] Hcg Hpc Hpath").
            -- intros i Hi1 Hi2. destruct (Nat.eq_dec i off) as [He | Hne].
               ++ rewrite He. exact Hsl0.
               ++ apply A3; lia.
            -- rewrite -Hap. exact A5.
            -- intros c N9 N15. rewrite (A7 c N9 N15). exact (HH1o c N15).
          * iIntros (CIDh4 Hqh4 M3) "%B1 %B2 %B3 %B4 %B5 Hcg Hpc Hpath".
            iSpecialize ("HqB" $! CIDh4 with "[%]"); [wp_next_chain |].
            iApply ("HqB" $! a M3
                      with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
            -- lia.
            -- exact B1.
            -- intros i Hi1 Hi2. destruct (Nat.eq_dec i off) as [He | Hne].
               ++ rewrite He. exact Hsl0.
               ++ apply A3; lia.
            -- exact A4.
            -- exact B2.
            -- exact B3.
            -- exact B4.
            -- intros c N9 N15 N14 N18.
               rewrite (B5 c N15 N14 N18). rewrite (A7 c N9 N15).
               exact (HH1o c N15).
      - (* not a separator: [bne] is taken straight to +0x106 *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (NX + 0xf8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 H1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HH1a5 HH1s3;
                        exact (nx_nslash_ne _ Hsl0))
                  ltac:(rewrite Htf6; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (nxi_0f8 with "Htext"). }
        iIntros (CIDh2 Hqh2). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htf6) in "Hpc".
        iSpecialize ("Hmid" $! CIDh2 with "[%]"); [wp_next_chain |].
        iApply ("Hmid" $! off H1
                  with "[%] [%] [%] [%] Hcg Hpc Hpath [HqA] [HqB]").
        + exact Holt.
        + exact Hsl0.
        + exact HH1s1.
        + exact HH1a5.
        + iIntros (CIDh3 Hqh3) "%Hap Hcg Hpc Hpath".
          iSpecialize ("HqA" $! CIDh3 with "[%]"); [wp_next_chain |].
          iApply ("HqA" $! H1 with "[%] [%] [%] Hcg Hpc Hpath").
          * intros i Hi1 Hi2. exfalso. lia.
          * rewrite -Hap. exact HH1s1.
          * intros c N9 N15. exact (HH1o c N15).
        + iIntros (CIDh3 Hqh3 M3) "%B1 %B2 %B3 %B4 %B5 Hcg Hpc Hpath".
          iSpecialize ("HqB" $! CIDh3 with "[%]"); [wp_next_chain |].
          iApply ("HqB" $! off M3
                    with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
          * lia.
          * exact B1.
          * intros i Hi1 Hi2. exfalso. lia.
          * exact Hsl0.
          * exact B2.
          * exact B3.
          * exact B4.
          * intros c N9 N15 N14 N18. rewrite (B5 c N15 N14 N18).
            exact (HH1o c N15). }
    (* ---- (6) +0xae .. +0xbc: skipelem's TRAILING separator skip -------
       reached from BOTH memmove branches, with [s1 = s2] the index just
       past the element; it ends at +0xc0, where ilock's argument is set up.
       Same two-instruction head as (5), one exit instead of two. *)
    iAssert (□ wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDs : CpuId =>
                  nx_trail_body j b K plen pfun pv dqpv CIDs))%I
      with "[]" as "#Htrail".
    { iModIntro.
      iIntros (CIDs Hss off Ms) "%Holt %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
      (* +0xae lbu a5,0(s1) *)
      iDestruct (nx_buf_acc pv dqpv pfun (S plen) off ltac:(lia)
                   with "Hpath") as "[Hpb Hpback]".
      iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xae)) Ra5 Rs1
                (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                (pfun off : mword 8) b (dqm := dqpv)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hpb]").
      { iApply (nxi_0ae with "Htext"). }
      { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
      iIntros (CIDr1 Hqr1) "Hcg Hpc Hpb".
      iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
      iDestruct ("Hpback" with "Hpb") as "Hpath".
      pose (G1 := <[Regidx Ra5 := regval_into_reg
                    (zero_extend' 64 (pfun off : mword 8))]> Ms).
      assert (HG1a5 : G1 !!! Regidx Ra5
                      = (zero_extend' 64 (pfun off : mword 8) : mword 64))
        by (rewrite /G1; apply upd_eq).
      assert (HG1s1 : G1 !!! Regidx Rs1 = pa_add pv off)
        by (rewrite /G1 upd_ne; [exact Hs1 | nz]).
      assert (HG1s3 : G1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
        by (rewrite /G1 upd_ne; [exact Hs3 | nz]).
      assert (HG1o : forall c : mword 5, c <> Ra5 ->
                G1 !!! Regidx c = (Ms !!! Regidx c : mword 64)).
      { intros c N15. rewrite /G1 upd_ne; [reflexivity | dlk_xne N15]. }
      assert (Hqa8 : add_vec_int (mword_of_int (NX + 0xae) : mword 64) 4
                     = mword_of_int (NX + 0xb2)) by pcw.
      iEval (rewrite Hqa8) in "Hpc".
      assert (Htb6 : add_vec (mword_of_int (NX + 0xb2) : mword 64)
                (sign_extend' 64 (mword_of_int 14 : mword 13))
              = mword_of_int (NX + 0xc0)) by pcw.
      destruct (decide (pfun off = SLASH)) as [Hsl0 | Hsl0].
      - iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xb2))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 G1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HG1a5 HG1s3;
                        exact (nx_nslash_eq _ Hsl0))
                  with "Hcg Hpc []").
      { iApply (nxi_0b2 with "Htext"). }
        iIntros (CIDr2 Hqr2) "Hcg Hpc".
        assert (Hqac : add_vec_int (mword_of_int (NX + 0xb2) : mword 64) 4
                       = mword_of_int (NX + 0xb6)) by pcw.
        iEval (rewrite Hqac) in "Hpc".
        iSpecialize ("Hsk2" $! plen CIDr2 with "[%]"); [wp_next_chain |].
        iApply ("Hsk2" $! off G1
                  with "[%] [%] [%] [%] [%] Hcg Hpc Hpath [Hqc]").
        + lia.
        + exact (Hslt off Holt Hsl0).
        + exact Hsl0.
        + exact HG1s1.
        + exact HG1s3.
        + iIntros (CIDr3 Hqr3 off' M2)
            "%A1 %A2 %A3 %A4 %A5 %A6 %A7 Hcg Hpc Hpath".
          iSpecialize ("Hqc" $! CIDr3 with "[%]"); [wp_next_chain |].
          iApply ("Hqc" $! off' M2
                    with "[%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
          * lia.
          * exact A2.
          * intros i Hi1 Hi2. destruct (Nat.eq_dec i off) as [He | Hne].
            -- rewrite He. exact Hsl0.
            -- apply A3; lia.
          * exact A4.
          * exact A5.
          * intros c N9 N15. rewrite (A7 c N9 N15). exact (HG1o c N15).
      - iApply (wp_bne_taken_s_sconf (mword_of_int (NX + 0xb2))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 G1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HG1a5 HG1s3;
                        exact (nx_nslash_ne _ Hsl0))
                  ltac:(rewrite Htb6; vm_compute; reflexivity)
                  with "Hcg Hpc []").
          { iApply (nxi_0b2 with "Htext"). }
        iIntros (CIDr2 Hqr2). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htb6) in "Hpc".
        iSpecialize ("Hqc" $! CIDr2 with "[%]"); [wp_next_chain |].
        iApply ("Hqc" $! off G1
                  with "[%] [%] [%] [%] [%] [%] Hcg Hpc Hpath").
        + lia.
        + exact Holt.
        + intros i Hi1 Hi2. exfalso. lia.
        + exact Hsl0.
        + exact HG1s1.
        + intros c N9 N15. exact (HG1o c N15). }
    (* ================================================================= *)
    (*  THE WALK at +0xf4.  ProofKexit's [forall fuel, wp_next] shape over *)
    (*  the measure [plen - off]; INSIDE it live three more of the same    *)
    (*  shape (the leading-sep skip, the element scan, the trailing skip). *)
    (*                                                                    *)
    (*  THE INVARIANT.  [off] is the path pointer's index, so [s1 =        *)
    (*  pa_add pv off] and what is left to walk is [drop off pl];          *)
    (*  [es0] is the prefix of elements already consumed, which is what    *)
    (*  turns the loop's local [path_elems (drop off pl) = [e]] into the   *)
    (*  contract's [nameiparent_of pl es0 e].  The budget travels as the   *)
    (*  three facts [nx_bi_step] / [nx_bi_spend] / [nx_bi_free] move it.   *)
    (*                                                                    *)
    (*  THE CONTRACT'S OWN CONTINUATION IS THREADED AS THE LAST SLOT       *)
    (*  (N3c's third architectural note): it is spatial, and four of the   *)
    (*  five exits need it.  It is stated at the LOOP's hart [CIDl], so    *)
    (*  a caller that has already made a call shifts it forward with       *)
    (*  [wp_next_shift] rather than needing it at the entry hart.          *)
    (* ================================================================= *)
    iAssert (∀ fuel : nat, wp_next (CID0 := CID) true (proc_addr j)
               (fun CIDl : CpuId =>
                  nx_loop_body j b K m sp0 pv nb ret_tgt plen L pfun pl eb
                               g gfs bn cov logstart bmapstart inodestart size
                               npar n Sb pidv dq dqb dqs dqpv fuel CIDl lks Vpr))%I
      with "[]" as "Hloop".
    { (* ---- local disequality helpers, used all through the body ---- *)
      assert (Hcsne : forall c r : mword 5,
                is_cs_idx c = true -> is_cs_idx r = false -> c <> r).
      { intros c r Hc Hr Hq. rewrite Hq Hr in Hc. discriminate. }
      assert (HnsA5 : forall c : mword 5, is_cs_idx c = true -> c <> Ra5)
        by (intros c Hc; exact (Hcsne c Ra5 Hc ltac:(vm_compute; reflexivity))).
      assert (HnsA4 : forall c : mword 5, is_cs_idx c = true -> c <> Ra4)
        by (intros c Hc; exact (Hcsne c Ra4 Hc ltac:(vm_compute; reflexivity))).
      assert (HpnS : pfun plen <> SLASH).
      { intro Hq. apply HSN. rewrite -Hq. exact Hterm. }
      assert (Hplen' : (Z.of_nat plen < 2147483648)%Z)
        by (change (2 ^ 31)%Z with 2147483648%Z in Hplen; exact Hplen).
      iIntros (fuel). iInduction fuel as [|fuel] "IHl".
      - iIntros (CIDl Hsl off ipv Ml ncur Scur es0 nf wc)
          "%Hfu %Hoff %Hes0 %HbA %HbB %HbD %HbC %HbW %Hsbc %Hregs Hcg Hcnt Hextc Hclmc Hpc
           Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
           Hip Hisl Hbmap Hinos Hppid Hcwdr Hpath Hname Hbslot
           Hlog Hcont".
        exfalso. lia.
      - iIntros (CIDl Hsl off ipv Ml ncur Scur es0 nf wc)
          "%Hfu %Hoff %Hes0 %HbA %HbB %HbD %HbC %HbW %Hsbc %Hregs Hcg Hcnt Hextc Hclmc Hpc
           Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
           Hip Hisl Hbmap Hinos Hppid Hcwdr Hpath Hname Hbslot
           Hlog Hcont".
        pose proof Hregs as Hregs'.
        destruct Hregs' as (G2 & G8 & G9 & G19 & G20 & G21 & G22 & G23 & G24
                            & G25 & Gthr).
        iSpecialize ("Hhead" $! CIDl with "[%]"); [wp_next_chain |].
        destruct (nx_first_ns off plen pfun Hoff)
          as [Hallsl | (afst & Hfa1 & Hfa2 & Hfa3)].
        + (* ================= EXIT A: nothing but separators left ======= *)
          iApply ("Hhead" $! off Ml with "[%] [%] [%] Hcg Hpc Hpath [-] []").
          * exact Hoff.
          * exact G9.
          * exact G19.
          * (* ---- the +0x140 tail ---- *)
            iIntros (CIDa Hsa Ma) "%HA1 %HA2 %HA3 Hcg Hpc Hpath".
            (* the suffix has no elements left *)
            assert (Hpes : pe_skip (drop off pl) = []).
            { rewrite (nx_pe_skip_at off plen plen pfun Hoff ltac:(lia)
                         HA1 HpnS).
              exact (nx_drop_nil plen plen pfun ltac:(lia)). }
            assert (Hpel : path_elems (drop off pl) = []).
            { apply (proj2 (path_elems_nil_iff (drop off pl))). exact Hpes. }
            assert (Hlr : length (path_elems (drop off pl)) = 0%nat)
              by (rewrite Hpel; reflexivity).
            rewrite Hlr in HbC.
            (* the register bundle the epilogue wants *)
            assert (HAs4 : Ma !!! Regidx Rs4 = ipv).
            { rewrite (HA3 Rs4 ltac:(nz) ltac:(nz)). exact G20. }
            assert (HAs6 : Ma !!! Regidx Rs6 = (m !!! Regidx Ra1 : mword 64)).
            { rewrite (HA3 Rs6 ltac:(nz) ltac:(nz)). exact G22. }
            assert (HAtr : nx_tregs m sp0 Ma).
            { split.
              - rewrite (HA3 csp_rs1 ltac:(nz) ltac:(nz)). exact G2.
              - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
                rewrite (HA3 c N9 (HnsA5 c Hc)).
                exact (Gthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                         N25 N26). }
            assert (Htg5c : add_vec (mword_of_int (NX + 0x140) : mword 64)
                      (sign_extend' 64 (mword_of_int 7964 : mword 13))
                    = mword_of_int (NX + 0x5c)) by pcw.
            destruct npar.
            -- (* nameiparent of a path with no elements left: iput, a0 = 0 *)
               iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (NX + 0x140))
                         (mword_of_int 7964 : mword 13) Rs6 Ma (K - 12)%nat b
                         ltac:(nz)
                         ltac:(rgne; rewrite HAs6; exact Ha1)
                         with "Hcg Hpc []").
               { iApply (nxi_140 with "Htext"). }
               iIntros (CIDA1 HqA1) "Hcg Hpc".
               assert (Hq134 : add_vec_int
                         (mword_of_int (NX + 0x140) : mword 64) 4
                       = mword_of_int (NX + 0x144)) by pcw.
               iEval (rewrite Hq134) in "Hpc".
               (* +0x144 c.mv a0,s4 *)
               iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x144)) Ra0 Rs4
                         Ma (K - 12)%nat b ltac:(nz) ltac:(rdok)
                         with "Hcg Hpc []").
               { iApply (nxi_144 with "Htext"). }
               iIntros (CIDA2 HqA2) "Hcg Hpc". iEval (rgne) in "Hcg".
               pose (T1 := <[Regidx Ra0 := regval_into_reg
                             (add_vec (zero_reg : mword 64)
                                (Ma !!! Regidx Rs4))]> Ma).
               assert (HT1a0 : T1 !!! Regidx Ra0 = ipv).
               { rewrite /T1 upd_eq. rewrite HAs4. apply add_vec_zero_l. }
               assert (Hq136 : add_vec_int
                         (mword_of_int (NX + 0x144) : mword 64) 2
                       = mword_of_int (NX + 0x146)) by pcw.
               iEval (rewrite Hq136) in "Hpc".
               (* +0x146 jal ra,iput *)
               assert (Htgip : add_vec (mword_of_int (NX + 0x146) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095528 : mword 21))
                       = mword_of_int KernelSyms.iput) by pcw.
               iApply (wp_jal_s_sconf (mword_of_int (NX + 0x146)) Rra
                         (mword_of_int 2095528 : mword 21) T1 (K - 12)%nat b
                         ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                         with "Hcg Hpc []").
               { iApply (nxi_146 with "Htext"). }
               iIntros (CIDA3 HqA3) "Hcg Hpc".
               iEval (rewrite Htgip) in "Hpc".
               pose (T2 := <[Regidx Rra := regval_into_reg
                             (add_vec_int
                                (mword_of_int (NX + 0x146) : mword 64) 4)]> T1).
               assert (HT2ra : T2 !!! Regidx Rra
                       = add_vec_int (mword_of_int (NX + 0x146) : mword 64) 4)
                 by (rewrite /T2; apply upd_eq).
               iDestruct "Hip" as (pk pq pinum) "(%Hpe & %Hpk & %Hpb & Href & Hru)".
               iEval (rewrite -Hdev) in "Href".
               assert (HT2a0 : T2 !!! Regidx Ra0 = ientry pk).
               { rewrite /T2 upd_ne; [| nz]. rewrite HT1a0. exact Hpe. }
               assert (Hpb' : bv_unsigned pinum < 16 * Z.of_nat nib)
                 by (rewrite Hnib; exact Hpb).
               destruct (Hiregb pinum Hpb') as [Hibc Hibl].
               iDestruct (nx_esc_acc cn gfs gi cov logstart pk Hpk with "Hesc")
                 as "#Hescp".
               iDestruct (ic_sleeplocks_lookup cn pk Hpk with "Hslks")
                 as (gilp gislp) "#Hslkp".
               iDestruct (cpu_own_transport CIDl CIDA3 0%nat eb (proc_addr j) b
                            ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
               iDestruct (trap_csrs_ext_transport CIDl CIDA3 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
               iDestruct (cpu_claim_ext_transport CIDl CIDA3 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
               iDestruct (wp_next_shift (b := true) (CIDa := CIDl) (CIDb := CIDA3)
                            ltac:(wp_next_chain) with "Hcont") as "Hcont".
               iDestruct (log_opS_named with "Hlog") as (enxA) "Hlog".
               iApply (IP.wp_iput_gen gs j gl gu gd gk pd pav pu bn g gfs gi
                         cn gtl gilp gislp cov logstart bmapstart inodestart
                         nib size dev pk pq pinum ncur Scur wc false
                         false enxA pidv dq dqb dqs
                         T2 (K - 12)%nat eb b
                         _ Vpr true Kip Hpk HbW ltac:(discriminate)
                         Hlg Hsize Hbmap0 Hbmapcov Hbmaplog Hinos0
                         Hibc Hibl Hpb' Hcovb HbD
                         Hj Hgs HT2a0 Hbelow
                         with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hitb2 Hitbl
                               Hescp Hireg [] Hslkp [$Href $Hru] Hbmap Hinos Hbits Hppid
                               Hprocs Hdev Hgeom Hdlk Hbslot [] Hlog").
               all: try lkbelow.
               (* RULING G: a runtime caller lends the SEALED arm. *)
               { iExact "Hropen". }
               { iEval (cbn beta iota). iEmpIntro. }
               iIntros (CIDip Hqip mip nip Sip wip)
                 "%Hcsip Hcg Hcnt Hextc Hclmc Hpc Hppid Hbmap Hinos Hbslot
                  %Hsip %Hwip %Hwipc %Hbdip Hlog Hisl2 _".
                 (* THE CREDITED BOUND IS STRONGER THAN THE COUNTED ONE, and
                    namex is stated at the counted one.  [ip_spend_w w false
                    false = 2] where [iput_units = 3] -- iput's own third unit
                    is the one it never needs uncredited -- so the gen post
                    gives [ncur - 2 <= nip], and every [nx_bi_*] budget lemma
                    below wants [ncur - iput_units <= nip].  Weaken ONCE, here,
                    and keep the hypothesis's name so nothing downstream
                    moves. *)
               assert (Hpc13a : ret_pc (T2 !!! Regidx Rra)
                       = mword_of_int (NX + 0x14a)).
               { rewrite HT2ra. pcw. }
               iEval (rewrite Hpc13a) in "Hpc".
               (* +0x14a c.li s4,0 *)
               iApply (wp_cli_s_sconf (mword_of_int (NX + 0x14a)) Rs4
                         (mword_of_int 0 : mword 6)
                         (mword_of_int 0 : mword 64) mip (K - 12)%nat b
                         ltac:(nz) ltac:(rdok) ltac:(pcw)
                         with "Hcg Hpc []").
               { iApply (nxi_14a with "Htext"). }
               iIntros (CIDA4 HqA4) "Hcg Hpc".
               pose (T3 := <[Regidx Rs4 := regval_into_reg
                             (mword_of_int 0 : mword 64)]> mip).
               assert (HT3s4 : T3 !!! Regidx Rs4 = (mword_of_int 0 : mword 64))
                 by (rewrite /T3; apply upd_eq).
               assert (HT2tr : nx_tregs m sp0 T2).
               { rewrite /T2 /T1.
                 apply (nx_tregs_caller m sp0 _ Rra _
                          ltac:(vm_compute; reflexivity)).
                 apply (nx_tregs_caller m sp0 _ Ra0 _
                          ltac:(vm_compute; reflexivity)).
                 exact HAtr. }
               assert (HT3tr : nx_tregs m sp0 T3).
               { destruct HT2tr as [U2 Uthr]. split.
                 - rewrite /T3 upd_ne; [| nz].
                   rewrite (callee_saved_lookup Hcsip csp_rs1
                              ltac:(vm_compute; reflexivity)). exact U2.
                 - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
                   rewrite /T3 upd_ne; [| dlk_xne N20].
                   rewrite (callee_saved_lookup Hcsip c Hc).
                   exact (Uthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                            N25 N26). }
               assert (Hq13c : add_vec_int
                         (mword_of_int (NX + 0x14a) : mword 64) 2
                       = mword_of_int (NX + 0x14c)) by pcw.
               iEval (rewrite Hq13c) in "Hpc".
               (* +0x14c c.j +0x5c *)
               assert (Htj5c : add_vec (mword_of_int (NX + 0x14c) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 1928 : mword 11) ('b"0"))))
                       = mword_of_int (NX + 0x5c)) by pcw.
               iApply (wp_cj_s_sconf (mword_of_int (NX + 0x14c))
                         (sign_extend' 21
                            (concat_vec (mword_of_int 1928 : mword 11) ('b"0")))
                         T3 (K - 12)%nat b
                         ltac:(rewrite Htj5c; vm_compute; reflexivity)
                         with "Hcg Hpc []").
               { iApply (nxi_14c with "Htext"). }
               iIntros (CIDA5 HqA5). iApply bi.later_intro. iIntros "Hcg Hpc".
               iEval (rewrite Htj5c) in "Hpc".
               iDestruct (cpu_own_transport CIDip CIDA5 0%nat eb (proc_addr j) b
                            ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
               iDestruct (trap_csrs_ext_transport CIDip CIDA5 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
               iDestruct (cpu_claim_ext_transport CIDip CIDA5 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
               iSpecialize ("Htail" $! CIDA5 with "[%]"); [wp_next_chain |].
               iApply ("Htail" $! T3 (mword_of_int 0 : mword 64)
                         with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                         Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                        ").
               ++ exact HT3tr.
               ++ exact HT3s4.
               ++ iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                  iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
                  iDestruct (iref_slots_combine 1 1 with "Hisl Hisl2")
                    as "Hisl".
                  iApply ("Hcont" $! mf nip Sip false nf
                            (mword_of_int 0 : mword 64) (wc || wip)%bool
                            with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid
                                  Hcwdr Hpath Hname Hbslot [%] [%] [%] Hlog
                                  [Hisl]").
                  ** exact Hcsf.
                  ** exact (nx_sub_trans _ _ _ Hsbc Hsip).
                  ** (* the report, at the set this arm's iput grew *)
                     intros Hw. destruct wc; destruct wip; simpl in Hw;
                       first [ exact (Hsip _ (HbW eq_refl))
                             | exact (Hwip eq_refl) | discriminate ].
                  ** exact (nx_wi_spend n ncur nip wc wip false
                              HbA HbB Hwipc (proj1 Hbdip) (proj2 Hbdip)).
                  ** iSplitR; [iPureIntro; exact Hfa0 |]. iExact "Hisl".
            -- (* namei: the walk's own reference IS the answer *)
               iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (NX + 0x140))
                         (mword_of_int 7964 : mword 13) Rs6 Ma (K - 12)%nat b
                         ltac:(nz)
                         ltac:(rgne; rewrite HAs6; exact Ha1)
                         ltac:(rewrite Htg5c; vm_compute; reflexivity)
                         with "Hcg Hpc []").
               { iApply (nxi_140 with "Htext"). }
               iIntros (CIDA1 HqA1). iApply bi.later_intro. iIntros "Hcg Hpc".
               iEval (rewrite Htg5c) in "Hpc".
               iDestruct (cpu_own_transport CIDl CIDA1 0%nat eb (proc_addr j) b
                            ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
               iDestruct (trap_csrs_ext_transport CIDl CIDA1 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
               iDestruct (cpu_claim_ext_transport CIDl CIDA1 eb (proc_addr j)
                            ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
               iSpecialize ("Htail" $! CIDA1 with "[%]"); [wp_next_chain |].
               iApply ("Htail" $! Ma ipv with
"[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                         Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                        ").
               ++ exact HAtr.
               ++ exact HAs4.
               ++ iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                  iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
                  iApply ("Hcont" $! mf ncur Scur true nf ipv wc
                            with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid
                                  Hcwdr Hpath Hname Hbslot [%] [%] [%] Hlog
                                  [Hip Hisl]").
                  ** exact Hcsf.
                  ** exact Hsbc.
                  ** exact HbW.
                  ** exact (nx_wi_free n ncur wc HbA HbB).
                  ** iSplitR; [| iFrame "Hip Hisl"].
                     iPureIntro. split; [exact Hfa0 |].
                     intro Hc. discriminate.
          * (* exit B is impossible: [afst] would be a non-separator *)
            iIntros (CIDb Hsb a Mb) "%B1 %B2 %B3 %B4 %B5 %B6 %B7 %B8
                                     Hcg Hpc Hpath".
            exfalso. exact (B4 (Hallsl a B1 B2)).
        + (* ================= EXIT B: an element starts here =========== *)
          iApply ("Hhead" $! off Ml with "[%] [%] [%] Hcg Hpc Hpath []").
          * exact Hoff.
          * exact G9.
          * exact G19.
          * (* exit A is impossible *)
            iIntros (CIDa Hsa Ma) "%HA1 %HA2 %HA3 Hcg Hpc Hpath".
            exfalso. exact (Hfa3 (HA1 afst Hfa1 Hfa2)).
          * iIntros (CIDb Hsb a Mb) "%B1 %B2 %B3 %B4 %B5 %B6 %B7 %B8
                                     Hcg Hpc Hpath".
            (* the register bundle, carried across the loop head *)
            assert (HBregs : nx_regs m sp0 (pa_add pv a) ipv nb
                               (m !!! Regidx Ra1 : mword 64) Mb).
            { unfold nx_regs. split_and!.
              - rewrite (B8 csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G2.
              - rewrite (B8 Rs0 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G8.
              - exact B6.
              - rewrite (B8 Rs3 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G19.
              - rewrite (B8 Rs4 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G20.
              - rewrite (B8 Rs5 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G21.
              - rewrite (B8 Rs6 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G22.
              - rewrite (B8 Rs7 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G23.
              - rewrite (B8 Rs8 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G24.
              - rewrite (B8 Rs9 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
                exact G25.
              - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
                rewrite (B8 c N9 (HnsA5 c Hc) (HnsA4 c Hc) N18).
                exact (Gthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                         N25 N26). }
            iSpecialize ("Hscn" $! plen CIDb with "[%]"); [wp_next_chain |].
            iApply ("Hscn" $! a Mb with "[%] [%] [%] Hcg Hpc Hpath").
            -- lia.
            -- exact B2.
            -- exact B7.
            -- iIntros (CIDe Hse e Me) "%E1 %E2 %E3 %E4 %E5 %E6
                                        Hcg Hpc Hpath".
               assert (HEregs : nx_regs m sp0 (pa_add pv a) ipv nb
                          (m !!! Regidx Ra1 : mword 64) Me).
               { destruct HBregs as (D2 & D8 & D9 & D19 & D20 & D21 & D22
                                     & D23 & D24 & D25 & Dthr).
                 unfold nx_regs. split_and!.
                 - rewrite (E6 csp_rs1 ltac:(nz) ltac:(nz) ltac:(nz)). exact D2.
                 - rewrite (E6 Rs0 ltac:(nz) ltac:(nz) ltac:(nz)). exact D8.
                 - rewrite (E6 Rs1 ltac:(nz) ltac:(nz) ltac:(nz)). exact D9.
                 - rewrite (E6 Rs3 ltac:(nz) ltac:(nz) ltac:(nz)). exact D19.
                 - rewrite (E6 Rs4 ltac:(nz) ltac:(nz) ltac:(nz)). exact D20.
                 - rewrite (E6 Rs5 ltac:(nz) ltac:(nz) ltac:(nz)). exact D21.
                 - rewrite (E6 Rs6 ltac:(nz) ltac:(nz) ltac:(nz)). exact D22.
                 - rewrite (E6 Rs7 ltac:(nz) ltac:(nz) ltac:(nz)). exact D23.
                 - rewrite (E6 Rs8 ltac:(nz) ltac:(nz) ltac:(nz)). exact D24.
                 - rewrite (E6 Rs9 ltac:(nz) ltac:(nz) ltac:(nz)). exact D25.
                 - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
                   rewrite (E6 c N18 (HnsA5 c Hc) (HnsA4 c Hc)).
                   exact (Dthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                            N25 N26). }
               pose proof HEregs as HEr.
               destruct HEr as (F2 & F8 & F9 & F19 & F20 & F21 & F22 & F23
                                & F24 & F25 & Fthr).
               (* ---- the ELEMENT, and the two [PathElems] facts ---- *)
               assert (Hae : (a <= e)%nat) by lia.
               assert (Hns : forall i : nat, (a <= i)%nat -> (i < e)%nat ->
                         pfun i <> SLASH).
               { intros i H1 H2. destruct (Nat.eq_dec i a) as [Hi | Hi];
                   [rewrite Hi; exact B4 | apply E3; lia]. }
               assert (Hstop : (e = plen \/ pfun e = SLASH))
                 by (destruct E4 as [Hq | Hq]; [right; exact Hq
                                               | left; exact Hq]).
               assert (Hske : skipelem (drop a pl)
                        = Some (take 14 (bview (e - a)%nat
                                           (fun i => pfun (a + i)%nat)),
                                pe_skip (drop e pl)))
                 by exact (nx_skipelem_at a e plen pfun E1 E2 Hns Hstop).
               assert (Hpsa : pe_skip (drop off pl) = drop a pl)
                 by exact (nx_pe_skip_at off a plen pfun B1 ltac:(lia) B3 B4).
               assert (Hnorm : pe_skip (drop a pl) = drop a pl).
               { rewrite -Hpsa. apply pe_skip_idem. }
               assert (Hskoff : skipelem (drop off pl) = skipelem (drop a pl)).
               { unfold skipelem. rewrite Hpsa Hnorm. reflexivity. }
               assert (Hpeoff : path_elems (drop off pl)
                        = take 14 (bview (e - a)%nat
                                     (fun i => pfun (a + i)%nat))
                          :: path_elems (pe_skip (drop e pl))).
               { apply path_elems_Some. rewrite Hskoff. exact Hske. }
               assert (Hulen : length (bview (e - a)%nat
                                 (fun i => pfun (a + i)%nat)) = (e - a)%nat)
                 by apply bview_length.
               assert (Hea31 : (Z.of_nat (e - a) < 2147483648)%Z) by lia.
               assert (He64 : (Z.of_nat e < 18446744073709551616)%Z) by lia.
               (* ---- +0x96 sub a2,s2,s1 : the element's length ---- *)
               assert (Hsub : sub_vec (pa_add pv e) (pa_add pv a)
                        = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                 by exact (pa_add_diff pv e a Hae He64).
               iApply (wp_sub_s_sconf (mword_of_int (NX + 0x96)) Ra2 Rs2 Rs1
                         (mword_of_int (Z.of_nat (e - a)) : mword 64)
                         Me (K - 12)%nat b
                         ltac:(vm_compute; discriminate) ltac:(rdok)
                         ltac:(rgne; rgne; rewrite E5 F9; exact Hsub)
                         with "Hcg Hpc []").
               { iApply (nxi_096 with "Htext"). }
               iIntros (CIDE1 HqE1) "Hcg Hpc".
               pose (M1 := <[Regidx Ra2 := regval_into_reg
                             (mword_of_int (Z.of_nat (e - a)) : mword 64)]> Me).
               assert (HM1a2 : M1 !!! Regidx Ra2
                        = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                 by (rewrite /M1; apply upd_eq).
               assert (HM1regs : nx_regs m sp0 (pa_add pv a) ipv nb
                          (m !!! Regidx Ra1 : mword 64) M1)
                 by exact (nx_regs_caller m sp0 _ _ _ _ Me Ra2 _
                             ltac:(vm_compute; reflexivity) HEregs).
               assert (Hq090 : add_vec_int
                         (mword_of_int (NX + 0x96) : mword 64) 4
                       = mword_of_int (NX + 0x9a)) by pcw.
               iEval (rewrite Hq090) in "Hpc".
               (* ---- +0x9a sext.w s10,a2 ---- *)
               iApply (wp_addiw_s_sconf (mword_of_int (NX + 0x9a)) Rs10 Ra2
                         (mword_of_int 0 : mword 12) M1 (K - 12)%nat b
                         ltac:(vm_compute; discriminate) ltac:(rdok)
                         with "Hcg Hpc []").
               { iApply (nxi_09a with "Htext"). }
               iIntros (CIDE2 HqE2) "Hcg Hpc".
               pose (M2 := <[Regidx Rs10 := regval_into_reg
                     (sign_extend' 64 (subrange_vec_dec
                        (add_vec (rget M1 Ra2)
                           (sign_extend' 64 (mword_of_int 0 : mword 12)))
                        31 0))]> M1).
               assert (HM2s10 : M2 !!! Regidx Rs10
                        = (mword_of_int (Z.of_nat (e - a)) : mword 64)).
               { rewrite /M2 upd_eq. rgne. rewrite HM1a2.
                 exact (nx_sextw_i12 (e - a)%nat Hea31). }
               assert (HM2a2 : M2 !!! Regidx Ra2
                        = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                 by (rewrite /M2 upd_ne; [exact HM1a2 | nz]).
               assert (HM2regs : nx_regs m sp0 (pa_add pv a) ipv nb
                          (m !!! Regidx Ra1 : mword 64) M2)
                 by exact (nx_regs_s10 m sp0 _ _ _ _ _ M1 HM1regs).
               pose proof HM2regs as HM2r.
               destruct HM2r as (P2 & P8 & P9 & P19 & P20 & P21 & P22 & P23
                                 & P24 & P25 & Pthr).
               assert (Htg11c : add_vec (mword_of_int (NX + 0x9e) : mword 64)
                         (sign_extend' 64 (mword_of_int 142 : mword 13))
                       = mword_of_int (NX + 0x12c)) by pcw.
               (* ================================================================
                  THE JOIN AT +0xae.  Both memmove branches arrive here with the
                  SAME bundle up to the name buffer's content function, and the
                  walk's resources cannot be split between two branches -- so the
                  whole tail (Htrail, ilock, the type test, the early stop,
                  dirlookup and the four exits) is stated ONCE, consuming the
                  induction hypothesis and the contract's continuation.
                  ================================================================ *)
               iAssert (wp_next (CID0 := CIDl) true (proc_addr j)
                          (fun CIDt : CpuId =>
                             nx_rest_body j b K m sp0 pv nb plen a e pfun ipv ncur
                                          Scur eb g gfs bn cov logstart bmapstart
                                          inodestart size pidv dq dqb dqs dqpv
                                          CIDt lks Vpr))%I
                 with "[IHl Hcont]" as "Hrest".
               { iIntros (CIDt Hst Mt nf') "%Hregt %Hviewt Hcg Hcnt Hextc Hclmc Hpc
                          Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                          Hip Hisl Hbmap Hinos Hppid Hcwdr
                          Hpath Hname Hbslot Hlog".
                 pose proof Hregt as Hrt.
                 destruct Hrt as (Q2 & Q8 & Q9 & Q19 & Q20 & Q21 & Q22 & Q23
                                  & Q24 & Q25 & Qthr).
                 iSpecialize ("Htrail" $! CIDt with "[%]"); [wp_next_chain |].
                 iApply ("Htrail" $! e Mt
                           with "[%] [%] [%] Hcg Hpc Hpath").
                 - exact E2.
                 - exact Q9.
                 - exact Q19.
                 - iIntros (CIDr Hsr o2 Mr) "%J1 %J2 %J3 %J4 %J5 %J6
                                             Hcg Hpc Hpath".
                   assert (Hpse : pe_skip (drop e pl) = drop o2 pl)
                     by exact (nx_pe_skip_at e o2 plen pfun J1 J2 J3 J4).
                   assert (Hpe2 : path_elems (drop off pl)
                            = take 14 (bview (e - a)%nat
                                         (fun i => pfun (a + i)%nat))
                              :: path_elems (drop o2 pl)).
                   { rewrite Hpeoff Hpse. reflexivity. }
                   assert (Hes2 : path_elems pl
                            = (es0 ++ [take 14 (bview (e - a)%nat
                                          (fun i => pfun (a + i)%nat))])
                              ++ path_elems (drop o2 pl)).
                   { rewrite -app_assoc. simpl. rewrite -Hpe2. exact Hes0. }
                   assert (Hlrs : length (path_elems (drop off pl))
                            = S (length (path_elems (drop o2 pl))))
                     by (rewrite Hpe2; reflexivity).
                   rewrite Hlrs in HbC.
                   assert (Hiu : (iput_units <= ncur)%nat) by exact HbD.
                   assert (HMrregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                              (m !!! Regidx Ra1 : mword 64) Mr).
                   { unfold nx_regs. split_and!.
                     - rewrite (J6 csp_rs1 ltac:(nz) ltac:(nz)). exact Q2.
                     - rewrite (J6 Rs0 ltac:(nz) ltac:(nz)). exact Q8.
                     - exact J5.
                     - rewrite (J6 Rs3 ltac:(nz) ltac:(nz)). exact Q19.
                     - rewrite (J6 Rs4 ltac:(nz) ltac:(nz)). exact Q20.
                     - rewrite (J6 Rs5 ltac:(nz) ltac:(nz)). exact Q21.
                     - rewrite (J6 Rs6 ltac:(nz) ltac:(nz)). exact Q22.
                     - rewrite (J6 Rs7 ltac:(nz) ltac:(nz)). exact Q23.
                     - rewrite (J6 Rs8 ltac:(nz) ltac:(nz)). exact Q24.
                     - rewrite (J6 Rs9 ltac:(nz) ltac:(nz)). exact Q25.
                     - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                              N25 N26.
                       rewrite (J6 c N9 (HnsA5 c Hc)).
                       exact (Qthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24
                                N25 N26). }
                   pose proof HMrregs as HMr.
                   destruct HMr as (W2 & W8 & W9 & W19 & W20 & W21 & W22 & W23
                                    & W24 & W25 & Wthr).
                   (* ---- THE SHED: ilock takes a share ---- *)
                   iDestruct "Hip" as (ik iq iinum)
                     "(%Hie & %Hik & %Hib & Href & Hru)".
                   iEval (rewrite -Hdev) in "Href".
                   rewrite inode_ref_shed.
                   iDestruct "Href" as "[Hkeep Hshr]".
                   assert (Hib' : bv_unsigned iinum < 16 * Z.of_nat nib)
                     by (rewrite Hnib; exact Hib).
                   destruct (Hiregb iinum Hib') as [Hibc Hibl].
                   iDestruct (nx_esc_acc cn gfs gi cov logstart ik Hik
                                with "Hesc") as "#Hesck".
                   iDestruct (ic_sleeplocks_lookup cn ik Hik with "Hslks")
                     as (gilk gislk) "#Hslkk".
                   iDestruct (nx_bs3_split with "Hbslot")
                     as "[Hbs1 Hbs2]".
                   (* +0xc0 c.mv a0,s4 *)
                   iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xc0)) Ra0 Rs4
                             Mr (K - 12)%nat b ltac:(nz) ltac:(rdok)
                             with "Hcg Hpc []").
                   { iApply (nxi_0c0 with "Htext"). }
                   iIntros (CIDV1 HqV1) "Hcg Hpc". iEval (rgne) in "Hcg".
                   pose (V1 := <[Regidx Ra0 := regval_into_reg
                         (add_vec (zero_reg : mword 64)
                            (Mr !!! Regidx Rs4))]> Mr).
                   assert (HV1a0 : V1 !!! Regidx Ra0 = ientry ik).
                   { rewrite /V1 upd_eq. rewrite W20 Hie.
                     apply add_vec_zero_l. }
                   assert (HV1regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                              (m !!! Regidx Ra1 : mword 64) V1)
                     by exact (nx_regs_caller m sp0 _ _ _ _ Mr Ra0 _
                                 ltac:(vm_compute; reflexivity) HMrregs).
                   assert (Hqb8 : add_vec_int
                             (mword_of_int (NX + 0xc0) : mword 64) 2
                           = mword_of_int (NX + 0xc2)) by pcw.
                   iEval (rewrite Hqb8) in "Hpc".
                   (* +0xc2 jal ra,ilock *)
                   assert (Htgil : add_vec
                             (mword_of_int (NX + 0xc2) : mword 64)
                             (sign_extend' 64
                                (mword_of_int 2095274 : mword 21))
                           = mword_of_int KernelSyms.ilock) by pcw.
                   iApply (wp_jal_s_sconf (mword_of_int (NX + 0xc2)) Rra
                             (mword_of_int 2095274 : mword 21) V1
                             (K - 12)%nat b ltac:(nz) ltac:(rdok)
                             ltac:(vm_compute; reflexivity)
                             with "Hcg Hpc []").
                   { iApply (nxi_0c2 with "Htext"). }
                   iIntros (CIDV2 HqV2) "Hcg Hpc".
                   iEval (rewrite Htgil) in "Hpc".
                   pose (V2 := <[Regidx Rra := regval_into_reg
                         (add_vec_int
                            (mword_of_int (NX + 0xc2) : mword 64) 4)]> V1).
                   assert (HV2ra : V2 !!! Regidx Rra
                            = add_vec_int
                                (mword_of_int (NX + 0xc2) : mword 64) 4)
                     by (rewrite /V2; apply upd_eq).
                   assert (HV2a0 : V2 !!! Regidx Ra0 = ientry ik)
                     by (rewrite /V2 upd_ne; [exact HV1a0 | nz]).
                   assert (HV2regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                              (m !!! Regidx Ra1 : mword 64) V2)
                     by exact (nx_regs_caller m sp0 _ _ _ _ V1 Rra _
                                 ltac:(vm_compute; reflexivity) HV1regs).
                   iDestruct (cpu_own_transport CIDt CIDV2 0%nat eb
                                (proc_addr j) b ltac:(wp_next_chain)
                                with "Hcnt") as "Hcnt".
                   iDestruct (trap_csrs_ext_transport CIDt CIDV2 eb (proc_addr j)
                                ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                   iDestruct (cpu_claim_ext_transport CIDt CIDV2 eb (proc_addr j)
                                ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                   iEval (rewrite inode_shr_gen_intro) in "Hshr".
                   iDestruct "Hshr" as (gsh) "Hshr".
                   (* NAME THE RETAINED PARENT'S GENERATION TOO (fs-log.md
                      §G.24).  The share and the short parent are two slices
                      of one slot, so [live_gen_agree] pins them to ONE
                      generation -- and that is the only way [L_par] can read
                      ilock's one-shot against the reference it re-forms,
                      since iunlock hands the share back generation-ERASED. *)
                   iEval (rewrite inode_ref_short_gen_intro) in "Hkeep".
                   iDestruct "Hkeep" as (gkp) "Hkeep".
                   iDestruct (inode_ref_short_shr_gen_agree with "Hkeep Hshr")
                     as %->.
                   iApply (IL.wp_ilock_sconf gs j gl gu gd gk pd pav pu bn
                             gfs gi cn gilk gislk cov logstart inodestart nib
                             ik (iq/2)%Qp gsh PlainK dev iinum pidv dq dqs
                             V2 (K - 12)%nat eb b lks Vpr
                             Kil Hik Hlg Hinos0 Hibc Hib' Hj Hgs HV2a0
                             ltac:(lkbelow)
                             with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hitbl Hesck
                                   Hireg Hslkk Hshr Hru Hinos Hppid Hprocs Hdev
                                   Hgeom Hdlk Hbs1").
                   all: try lkbelow.
                   iIntros (CIDil Hqil mil dnl bml fl_)
                     "%Hcsil Hcg Hcnt Hextc Hclmc Hpc Hppid Hinos Hbs1 Hslkd Hdep
                      Hidev Hiinum Hivalid Hload #Hshot Hfrz %Hfr_
                      Hru %Hilkp".
                   assert (Hpcbc : ret_pc (V2 !!! Regidx Rra)
                            = mword_of_int (NX + 0xc6)).
                   { rewrite HV2ra. pcw. }
                   iEval (rewrite Hpcbc) in "Hpc".
                   assert (Hmilregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                              (m !!! Regidx Ra1 : mword 64) mil)
                     by exact (nx_regs_cs m sp0 _ _ _ _ V2 mil Hcsil HV2regs).
                   pose proof Hmilregs as HmilR.
                   destruct HmilR as (Y2 & Y8 & Y9 & Y19 & Y20 & Y21 & Y22
                                      & Y23 & Y24 & Y25 & Ythr).
                   iDestruct "Hload" as (datl)
                     "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlnk & Hdiat & Hmeta & Haddrs & Hind &
                       Hblocks & Hdview & Hfview)".
                   iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
                   iEval (rewrite /i_type) in "Hity".
                   (* +0xc6 lh a5,68(s4) : ip->type *)
                   iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (NX + 0xc6)) Ra5 Rs4
                             (mword_of_int 68 : mword 12) mil (K - 12)%nat
                             (di_type dnl : mword 16) b
                             ltac:(nz) ltac:(rdok)
                             with "Hcg Hpc [] [Hity]").
                   { iApply (nxi_0c6 with "Htext"). }
                   { iEval (rgne; rewrite Y20 Hie). iExact "Hity". }
                   iIntros (CIDV3 HqV3) "Hcg Hpc Hity".
                   iEval (rgne; rewrite Y20 Hie) in "Hity".
                   pose (V3 := <[Regidx Ra5 := regval_into_reg
                         (sign_extend' 64 (di_type dnl : mword 16)
                          : mword 64)]> mil).
                   assert (HV3a5 : V3 !!! Regidx Ra5
                            = (sign_extend' 64 (di_type dnl : mword 16)
                               : mword 64))
                     by (rewrite /V3; apply upd_eq).
                   assert (HV3s7 : V3 !!! Regidx Rs7
                            = (mword_of_int 1 : mword 64))
                     by (rewrite /V3 upd_ne; [exact Y23 | nz]).
                   assert (HV3s4 : V3 !!! Regidx Rs4 = ipv)
                     by (rewrite /V3 upd_ne; [exact Y20 | nz]).
                   assert (HV3s6 : V3 !!! Regidx Rs6
                            = (m !!! Regidx Ra1 : mword 64))
                     by (rewrite /V3 upd_ne; [exact Y22 | nz]).
                   assert (HV3s1 : V3 !!! Regidx Rs1 = pa_add pv o2)
                     by (rewrite /V3 upd_ne; [exact Y9 | nz]).
                   assert (HV3s5 : V3 !!! Regidx Rs5 = nb)
                     by (rewrite /V3 upd_ne; [exact Y21 | nz]).
                   assert (HV3regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                              (m !!! Regidx Ra1 : mword 64) V3)
                     by exact (nx_regs_caller m sp0 _ _ _ _ mil Ra5 _
                                 ltac:(vm_compute; reflexivity) Hmilregs).
                   assert (Hqc0 : add_vec_int
                             (mword_of_int (NX + 0xc6) : mword 64) 4
                           = mword_of_int (NX + 0xca)) by pcw.
                   iEval (rewrite Hqc0) in "Hpc".
                   assert (Htg054 : add_vec
                             (mword_of_int (NX + 0xca) : mword 64)
                             (sign_extend' 64 (mword_of_int 8074 : mword 13))
                           = mword_of_int (NX + 0x54)) by pcw.
                   destruct (decide (di_type dnl = (mword_of_int 1 : mword 16)))
                     as [Hty | Hty].
                   + (* ============ IT IS A DIRECTORY ============ *)
                     iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xca))
                               (mword_of_int 8074 : mword 13) Rs7 Ra5
                               V3 (K - 12)%nat b ltac:(nz) ltac:(nz)
                               ltac:(rgne; rgne; rewrite HV3a5 HV3s7;
                                     exact (nx_tdir_eq _ Hty))
                               with "Hcg Hpc []").
                     { iApply (nxi_0ca with "Htext"). }
                     iIntros (CIDD0 HqD0) "Hcg Hpc".
                     (* ---- THE nlink GUARD (upstream 9da28f5) -------------
                        +0xce lh a5,74(s4) ; +0xd2 c.beqz a5 -> L_nlink.
                        The field resource is already in hand: [Hinl] is the
                        [i_nlink] conjunct of [Hmeta], destructed alongside
                        the [Hity] the type test just consumed, so the guard
                        needs no resource the walk did not already hold. *)
                     assert (Hqce : add_vec_int
                               (mword_of_int (NX + 0xca) : mword 64) 4
                             = mword_of_int (NX + 0xce)) by pcw.
                     iEval (rewrite Hqce) in "Hpc".
                     iEval (rewrite /i_nlink) in "Hinl".
                     iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (NX + 0xce)) Ra5 Rs4
                               (mword_of_int 74 : mword 12) V3 (K - 12)%nat
                               (di_nlink dnl : mword 16) b
                               ltac:(nz) ltac:(rdok)
                               with "Hcg Hpc [] [Hinl]").
                     { iApply (nxi_0ce with "Htext"). }
                     { iEval (rgne; rewrite HV3s4 Hie). iExact "Hinl". }
                     iIntros (CIDW0 HqW0) "Hcg Hpc Hinl".
                     iEval (rgne; rewrite HV3s4 Hie) in "Hinl".
                     pose (W0 := <[Regidx Ra5 := regval_into_reg
                           (sign_extend' 64 (di_nlink dnl : mword 16)
                            : mword 64)]> V3).
                     assert (HW0a5 : W0 !!! Regidx Ra5
                              = (sign_extend' 64 (di_nlink dnl : mword 16)
                                 : mword 64))
                       by (rewrite /W0; apply upd_eq).
                     assert (HW0s4 : W0 !!! Regidx Rs4 = ipv)
                       by (rewrite /W0 upd_ne; [exact HV3s4 | nz]).
                     assert (HW0s6 : W0 !!! Regidx Rs6
                              = (m !!! Regidx Ra1 : mword 64))
                       by (rewrite /W0 upd_ne; [exact HV3s6 | nz]).
                     assert (HW0s1 : W0 !!! Regidx Rs1 = pa_add pv o2)
                       by (rewrite /W0 upd_ne; [exact HV3s1 | nz]).
                     assert (HW0s5 : W0 !!! Regidx Rs5 = nb)
                       by (rewrite /W0 upd_ne; [exact HV3s5 | nz]).
                     assert (HW0regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) W0)
                       by exact (nx_regs_caller m sp0 _ _ _ _ V3 Ra5 _
                                   ltac:(vm_compute; reflexivity) HV3regs).
                     assert (Htg07an : add_vec
                               (mword_of_int (NX + 0xd2) : mword 64)
                               (sign_extend' 64 (sign_extend' 13
                                  (concat_vec (mword_of_int 212 : mword 8)
                                     ('b"0"))))
                             = mword_of_int (NX + 0x7a)) by pcw.
                     destruct (decide
                                 (di_nlink dnl = (mword_of_int 0 : mword 16)))
                       as [Hnl0 | Hnl0].
                     { (* ===== nlink == 0: THE GUARD FIRES (L_nlink) =====
                          Instruction-for-instruction [L_notdir]'s arm at a
                          different address, plus the [c.j] the copy needs
                          because +0x54 falls into the epilogue and +0x7a
                          cannot.  Same resources, same postcondition: the
                          walk ends at 0 with the inode released by the very
                          same [iunlockput], which the contract's failure arm
                          already admits.  kernel-defects.md D2. *)
                       iApply (wp_cbeqz_taken_s_sconf
                                 (mword_of_int (NX + 0xd2))
                                 (mword_of_int 212 : mword 8)
                                 (Cregidx (mword_of_int 7)) Ra5
                                 W0 (K - 12)%nat b
                                 ltac:(vm_compute; reflexivity) ltac:(nz)
                                 ltac:(rgne; rewrite HW0a5;
                                       exact (nx_nlz_eq _ Hnl0))
                                 ltac:(rewrite Htg07an; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (nxi_0d2 with "Htext"). }
                       iIntros (CIDN0 HqN0). iApply bi.later_intro. iIntros "Hcg Hpc".
                       iEval (rewrite Htg07an) in "Hpc".
                     iAssert (ic_loaded gfs gi cov logstart ik iinum dnl bml)
                       with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind
                              Hblocks Hdlnk Hdview Hfview]" as "Hload".
                     { rewrite /ic_loaded. iExists datl.
                       iSplitR; [iPureIntro; exact Hiok |].
                       iSplitR; [iPureIntro; exact Hdok |].
                       iSplitR; [iPureIntro; exact Hddix |].
                       iSplitR; [iPureIntro; exact Hdoc |].
                       iSplitR; [iPureIntro; exact Hduq |].
                       iSplitL "Hdlnk"; [iExact "Hdlnk" |].
                       iFrame "Hdiat".
                       iSplitL "Hity Himaj Himin Hinl Hisz".
                       - rewrite /inode_meta /i_type. iFrame.
                       - iFrame. }
                     iDestruct (nx_bs3_join with "Hbs1 Hbs2") as "Hbslot".
                     (* +0x54 c.mv a0,s4 *)
                     iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x7a)) Ra0 Rs4
                               W0 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                               with "Hcg Hpc []").
                     { iApply (nxi_07a with "Htext"). }
                     iIntros (CIDN1 HqN1) "Hcg Hpc". iEval (rgne) in "Hcg".
                     pose (ND1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (W0 !!! Regidx Rs4))]> W0).
                     assert (HND1a0 : ND1 !!! Regidx Ra0 = ientry ik).
                     { rewrite /ND1 upd_eq. rewrite HW0s4 Hie.
                       apply add_vec_zero_l. }
                     assert (HND1regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) ND1)
                       by exact (nx_regs_caller m sp0 _ _ _ _ W0 Ra0 _
                                   ltac:(vm_compute; reflexivity) HW0regs).
                     assert (Hq56 : add_vec_int
                               (mword_of_int (NX + 0x7a) : mword 64) 2
                             = mword_of_int (NX + 0x7c)) by pcw.
                     iEval (rewrite Hq56) in "Hpc".
                     (* +0x56 jal ra,iunlockput *)
                     assert (Htgup : add_vec
                               (mword_of_int (NX + 0x7c) : mword 64)
                               (sign_extend' 64
                                  (mword_of_int 2095940 : mword 21))
                             = mword_of_int KernelSyms.iunlockput) by pcw.
                     iApply (wp_jal_s_sconf (mword_of_int (NX + 0x7c)) Rra
                               (mword_of_int 2095940 : mword 21) ND1
                               (K - 12)%nat b ltac:(nz) ltac:(rdok)
                               ltac:(vm_compute; reflexivity)
                               with "Hcg Hpc []").
                     { iApply (nxi_07c with "Htext"). }
                     iIntros (CIDN2 HqN2) "Hcg Hpc".
                     iEval (rewrite Htgup) in "Hpc".
                     pose (ND2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int
                              (mword_of_int (NX + 0x7c) : mword 64) 4)]> ND1).
                     assert (HND2ra : ND2 !!! Regidx Rra
                              = add_vec_int
                                  (mword_of_int (NX + 0x7c) : mword 64) 4)
                       by (rewrite /ND2; apply upd_eq).
                     assert (HND2a0 : ND2 !!! Regidx Ra0 = ientry ik)
                       by (rewrite /ND2 upd_ne; [exact HND1a0 | nz]).
                     assert (HND2regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) ND2)
                       by exact (nx_regs_caller m sp0 _ _ _ _ ND1 Rra _
                                   ltac:(vm_compute; reflexivity) HND1regs).
                     iDestruct (cpu_own_transport CIDil CIDN2 0%nat eb
                                  (proc_addr j) b ltac:(wp_next_chain)
                                  with "Hcnt") as "Hcnt".
                     iDestruct (trap_csrs_ext_transport CIDil CIDN2 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                     iDestruct (cpu_claim_ext_transport CIDil CIDN2 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                     iDestruct (log_opS_named with "Hlog") as (enxB) "Hlog".
                     iDestruct (inode_ref_short_gen_forget with "Hkeep")
                       as "Hkeep2".
                     iApply (IUP.wp_iunlockput_gen gs j gl gu gd gk pd pav pu
                               bn g gfs gi cn gtl gilk gislk cov logstart
                               bmapstart inodestart nib size dev
                               ik (iq/2)%Qp (iq/2)%Qp gsh iinum dnl bml ncur
                               Scur wc false false enxB
                               pidv dq dqb dqs ND2 (K - 12)%nat eb b lks Vpr
                               Kiup Hik HbW ltac:(discriminate)
                               Hlg Hsize Hbmap0 Hbmapcov Hbmaplog
                               Hinos0 Hibc Hibl Hib' Hcovb Hiu Hj Hgs
                               HND2a0 Hbelow
                               with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc
                                     Hitb2 Hitbl Hesck Hireg [] Hslkk Hslkd
                                     Hdep Hidev Hiinum Hivalid Hload
                                     Hshot Hfrz [$Hkeep2 $Hru] Hbmap Hinos Hbits Hppid Hprocs
                                     Hdev Hgeom Hdlk Hbslot [] Hlog").
                     all: try lkbelow.
                     (* RULING G: a runtime caller lends the SEALED arm. *)
                     { iExact "Hropen". }
                     { iEval (cbn beta iota). iEmpIntro. }
                     iIntros (CIDup Hqup mup nup Sup wup)
                       "%Hcsup Hcg Hcnt Hextc Hclmc Hpc Hppid Hbmap Hinos
                        Hbslot %Hsup %Hwup %Hwupc %Hbdup Hlog Hisl2".
                     assert (Hpc5a : ret_pc (ND2 !!! Regidx Rra)
                              = mword_of_int (NX + 0x80)).
                     { rewrite HND2ra. pcw. }
                     iEval (rewrite Hpc5a) in "Hpc".
                     assert (Hmupregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) mup)
                       by exact (nx_regs_cs m sp0 _ _ _ _ ND2 mup Hcsup
                                   HND2regs).
                     (* +0x5a c.li s4,0, then FALL INTO the epilogue *)
                     iApply (wp_cli_s_sconf (mword_of_int (NX + 0x80)) Rs4
                               (mword_of_int 0 : mword 6)
                               (mword_of_int 0 : mword 64) mup (K - 12)%nat b
                               ltac:(nz) ltac:(rdok) ltac:(pcw)
                               with "Hcg Hpc []").
                     { iApply (nxi_080 with "Htext"). }
                     iIntros (CIDN3 HqN3) "Hcg Hpc".
                     pose (ND3 := <[Regidx Rs4 := regval_into_reg
                           (mword_of_int 0 : mword 64)]> mup).
                     assert (HND3s4 : ND3 !!! Regidx Rs4
                              = (mword_of_int 0 : mword 64))
                       by (rewrite /ND3; apply upd_eq).
                     assert (HND3tr : nx_tregs m sp0 ND3).
                     { pose proof (nx_tregs_of_regs m sp0 _ _ _ _ mup
                                     Hmupregs) as Hmt.
                       destruct Hmt as [U2 Uthr]. split.
                       - rewrite /ND3 upd_ne; [exact U2 | nz].
                       - intros c Hc T2' T8 T9 T18 T19 T20 T21 T22 T23 T24
                                T25 T26.
                         rewrite /ND3 upd_ne; [| dlk_xne T20].
                         exact (Uthr c Hc T2' T8 T9 T18 T19 T20 T21 T22 T23
                                  T24 T25 T26). }
                     assert (Hq82 : add_vec_int
                               (mword_of_int (NX + 0x80) : mword 64) 2
                             = mword_of_int (NX + 0x82)) by pcw.
                     iEval (rewrite Hq82) in "Hpc".
                     (* +0x82 c.j +0x5c -- the ONE instruction L_notdir does
                        not have: it falls into the epilogue, this copy jumps *)
                     assert (Htgj5c : add_vec
                               (mword_of_int (NX + 0x82) : mword 64)
                               (sign_extend' 64 (sign_extend' 21
                                  (concat_vec (mword_of_int 2029 : mword 11)
                                     ('b"0"))))
                             = mword_of_int (NX + 0x5c)) by pcw.
                     iApply (wp_cj_s_sconf (mword_of_int (NX + 0x82))
                               (sign_extend' 21
                                  (concat_vec (mword_of_int 2029 : mword 11)
                                     ('b"0")))
                               ND3 (K - 12)%nat b
                               ltac:(rewrite Htgj5c; vm_compute; reflexivity)
                               with "Hcg Hpc []").
                     { iApply (nxi_082 with "Htext"). }
                     iIntros (CIDN4 HqN4). iApply bi.later_intro. iIntros "Hcg Hpc".
                     iEval (rewrite Htgj5c) in "Hpc".
                     iDestruct (cpu_own_transport CIDup CIDN4 0%nat eb (proc_addr j) b
                                  ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                     iDestruct (trap_csrs_ext_transport CIDup CIDN4 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                     iDestruct (cpu_claim_ext_transport CIDup CIDN4 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                     iSpecialize ("Htail" $! CIDN4 with "[%]");
                       [wp_next_chain |].
                     iApply ("Htail" $! ND3 (mword_of_int 0 : mword 64)
                               with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                               Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11
                               Hb12 [-]").
                     * exact HND3tr.
                     * exact HND3s4.
                     * iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                       iSpecialize ("Hcont" $! CIDf with "[%]");
                         [wp_next_chain |].
                       iDestruct (iref_slots_combine 1 1 with "Hisl Hisl2")
                         as "Hisl".
                       iApply ("Hcont" $! mf nup Sup false nf'
                                 (mword_of_int 0 : mword 64) (wc || wup)%bool
                                 with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos
                                       Hppid Hcwdr Hpath Hname Hbslot
                                       [%] [%] [%] Hlog [Hisl]").
                       ** exact Hcsf.
                       ** exact (nx_sub_trans _ _ _ Hsbc Hsup).
                       ** intros Hw. destruct wc; destruct wup; simpl in Hw;
                            first [ exact (Hsup _ (HbW eq_refl))
                                  | exact (Hwup eq_refl) | discriminate ].
                       ** exact (nx_wi_spend n ncur nup wc wup false
                                   HbA HbB Hwupc (proj1 Hbdup) (proj2 Hbdup)).
                       ** iSplitR; [iPureIntro; exact Hfa0 |].
                          iExact "Hisl".
                     }
                     (* ===== nlink <> 0: fall through to the npar test ===== *)
                     iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0xd2))
                               (mword_of_int 212 : mword 8)
                               (Cregidx (mword_of_int 7)) Ra5
                               W0 (K - 12)%nat b
                               ltac:(vm_compute; reflexivity) ltac:(nz)
                               ltac:(rgne; rewrite HW0a5;
                                     exact (nx_nlz_ne _ Hnl0))
                               with "Hcg Hpc []").
                     { iApply (nxi_0d2 with "Htext"). }
                     iIntros (CIDW1 HqW1) "Hcg Hpc".
                     assert (Hqc4 : add_vec_int
                               (mword_of_int (NX + 0xd2) : mword 64) 2
                             = mword_of_int (NX + 0xd4)) by pcw.
                     iEval (rewrite Hqc4) in "Hpc".
                     (* ---- THE RECEIPT'S MINT (fs-log.md §G.18/§G.24) ----
                        The guard just decided this record's nlink NONZERO,
                        and the walk's own op is open at [enx], so the region
                        records "somebody observed a live link at [enx]" for
                        this inum.  Persistent and inum-keyed, so it simply
                        travels: the two iunlockputs BELOW the guard (the
                        found arm at +0xec and the miss arm at +0x8c) cash it
                        as [crz], and a later freeing iput of this very inode
                        can then absorb its inode block instead of paying for
                        it.  [L_notdir] (+0x54) and [L_nlink] (+0x7a) are the
                        two arms this mint cannot reach -- the first runs
                        before the guard, the second AT it -- and both are
                        terminal, which is what the contract's
                        [if ok then 0 else 1] pays for. *)
                     iDestruct (log_opS_named with "Hlog") as (enx) "Hlog".
                     iDestruct (log_opSe_lb with "Hlog") as "#Hlbnx".
                     iApply fupd_wp.
                     iMod (InodeRegion.ireg_obs_mint ⊤ gi gfs inodestart nib
                             iinum dnl g enx ltac:(solve_ndisj) Hib' Htlog
                             (nx_nlink_nz _ Hnl0)
                             with "Hireg Hdiat Hlbnx") as "[Hdiat #Hobs]".
                     iModIntro.
                     (* the [crz] premise the two credited sites present:
                        the observation plus the region's two ambient ties,
                        which this contract carries as premises (§G.25) *)
                     iAssert (nlz_obs (bv_unsigned iinum) enx ∗
                              ⌜g = icfg_log⌝ ∗ ⌜inodestart = icfg_ist⌝)%I
                       as "#Hcrz".
                     { iFrame "Hobs". iPureIntro. split; assumption. }
                     assert (Htg0ce : add_vec
                               (mword_of_int (NX + 0xd4) : mword 64)
                               (sign_extend' 64 (mword_of_int 10 : mword 13))
                             = mword_of_int (NX + 0xde)) by pcw.
                     assert (Htg07a : add_vec
                               (mword_of_int (NX + 0xdc) : mword 64)
                               (sign_extend' 64 (sign_extend' 13
                                  (concat_vec (mword_of_int 212 : mword 8)
                                     ('b"0"))))
                             = mword_of_int (NX + 0x84)) by pcw.
                     destruct (decide (npar = true /\ pfun o2 = NUL))
                       as [[Hnp Hnl] | Hoth].
                     * (* ---- NAMEIPARENT stops one level early: +0x84 ---- *)
                       iApply (wp_beqz_x0_fall_s_sconf
                                 (mword_of_int (NX + 0xd4))
                                 (mword_of_int 10 : mword 13) Rs6 W0
                                 (K - 12)%nat b ltac:(nz)
                                 ltac:(rgne; rewrite HW0s6; rewrite Ha1 Hnp;
                                       reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (nxi_0d4 with "Htext"). }
                       iIntros (CIDP1 HqP1) "Hcg Hpc".
                       assert (Hqc8 : add_vec_int
                                 (mword_of_int (NX + 0xd4) : mword 64) 4
                               = mword_of_int (NX + 0xd8)) by pcw.
                       iEval (rewrite Hqc8) in "Hpc".
                       (* +0xd8 lbu a5,0(s1) *)
                       iDestruct (nx_buf_acc pv dqpv pfun (S plen) o2
                                    ltac:(lia) with "Hpath")
                         as "[Hpb Hpback]".
                       iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xd8)) Ra5
                                 Rs1 (mword_of_int 0 : mword 12) W0
                                 (K - 12)%nat (pfun o2 : mword 8) b
                                 (dqm := dqpv)
                                 ltac:(nz) ltac:(rdok)
                                 with "Hcg Hpc [] [Hpb]").
                       { iApply (nxi_0d8 with "Htext"). }
                       { iEval (rgne; rewrite HW0s1 addv_sext0).
                         iExact "Hpb". }
                       iIntros (CIDP2 HqP2) "Hcg Hpc Hpb".
                       iEval (rgne; rewrite HW0s1 addv_sext0) in "Hpb".
                       iDestruct ("Hpback" with "Hpb") as "Hpath".
                       pose (NP1 := <[Regidx Ra5 := regval_into_reg
                             (zero_extend' 64 (pfun o2 : mword 8))]> W0).
                       assert (HP1a5 : NP1 !!! Regidx Ra5
                                = (zero_extend' 64 (pfun o2 : mword 8)
                                   : mword 64))
                         by (rewrite /NP1; apply upd_eq).
                       assert (HP1s4 : NP1 !!! Regidx Rs4 = ipv)
                         by (rewrite /NP1 upd_ne; [exact HW0s4 | nz]).
                       assert (HP1regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                  (m !!! Regidx Ra1 : mword 64) NP1)
                         by exact (nx_regs_caller m sp0 _ _ _ _ W0 Ra5 _
                                     ltac:(vm_compute; reflexivity) HW0regs).
                       assert (Hqcc : add_vec_int
                                 (mword_of_int (NX + 0xd8) : mword 64) 4
                               = mword_of_int (NX + 0xdc)) by pcw.
                       iEval (rewrite Hqcc) in "Hpc".
                       (* +0xdc c.beqz a5 -> +0x84 *)
                       iApply (wp_cbeqz_taken_s_sconf
                                 (mword_of_int (NX + 0xdc))
                                 (mword_of_int 212 : mword 8)
                                 (Cregidx (mword_of_int 7)) Ra5
                                 NP1 (K - 12)%nat b
                                 ltac:(vm_compute; reflexivity) ltac:(nz)
                                 ltac:(rgne; rewrite HP1a5;
                                       exact (nx_nul_eq _ Hnl))
                                 ltac:(rewrite Htg07a; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (nxi_0dc with "Htext"). }
                       iIntros (CIDP3 HqP3). iApply bi.later_intro. iIntros "Hcg Hpc".
                       iEval (rewrite Htg07a) in "Hpc".
                       (* +0x84 c.mv a0,s4 *)
                       iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x84)) Ra0
                                 Rs4 NP1 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                 with "Hcg Hpc []").
                       { iApply (nxi_084 with "Htext"). }
                       iIntros (CIDP4 HqP4) "Hcg Hpc". iEval (rgne) in "Hcg".
                       pose (NP2 := <[Regidx Ra0 := regval_into_reg
                             (add_vec (zero_reg : mword 64)
                                (NP1 !!! Regidx Rs4))]> NP1).
                       assert (HP2a0 : NP2 !!! Regidx Ra0 = ientry ik).
                       { rewrite /NP2 upd_eq. rewrite HP1s4 Hie.
                         apply add_vec_zero_l. }
                       assert (HP2regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                  (m !!! Regidx Ra1 : mword 64) NP2)
                         by exact (nx_regs_caller m sp0 _ _ _ _ NP1 Ra0 _
                                     ltac:(vm_compute; reflexivity) HP1regs).
                       assert (Hq7c : add_vec_int
                                 (mword_of_int (NX + 0x84) : mword 64) 2
                               = mword_of_int (NX + 0x86)) by pcw.
                       iEval (rewrite Hq7c) in "Hpc".
                       (* +0x86 jal ra,iunlock *)
                       assert (Htgiu : add_vec
                                 (mword_of_int (NX + 0x86) : mword 64)
                                 (sign_extend' 64
                                    (mword_of_int 2095508 : mword 21))
                               = mword_of_int KernelSyms.iunlock) by pcw.
                       iApply (wp_jal_s_sconf (mword_of_int (NX + 0x86)) Rra
                                 (mword_of_int 2095508 : mword 21) NP2
                                 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                 ltac:(vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (nxi_086 with "Htext"). }
                       iIntros (CIDP5 HqP5) "Hcg Hpc".
                       iEval (rewrite Htgiu) in "Hpc".
                       pose (NP3 := <[Regidx Rra := regval_into_reg
                             (add_vec_int
                                (mword_of_int (NX + 0x86) : mword 64) 4)]> NP2).
                       assert (HP3ra : NP3 !!! Regidx Rra
                                = add_vec_int
                                    (mword_of_int (NX + 0x86) : mword 64) 4)
                         by (rewrite /NP3; apply upd_eq).
                       assert (HP3a0 : NP3 !!! Regidx Ra0 = ientry ik)
                         by (rewrite /NP3 upd_ne; [exact HP2a0 | nz]).
                       assert (HP3regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                  (m !!! Regidx Ra1 : mword 64) NP3)
                         by exact (nx_regs_caller m sp0 _ _ _ _ NP2 Rra _
                                     ltac:(vm_compute; reflexivity) HP2regs).
                       iAssert (ic_loaded gfs gi cov logstart ik iinum dnl bml)
                         with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind
                                Hblocks Hdlnk Hdview Hfview]" as "Hload".
                       { rewrite /ic_loaded. iExists datl.
                         iSplitR; [iPureIntro; exact Hiok |].
                         iSplitR; [iPureIntro; exact Hdok |].
                         iSplitR; [iPureIntro; exact Hddix |].
                         iSplitR; [iPureIntro; exact Hdoc |].
                         iSplitR; [iPureIntro; exact Hduq |].
                         iSplitL "Hdlnk"; [iExact "Hdlnk" |].
                         iFrame "Hdiat".
                         iSplitL "Hity Himaj Himin Hinl Hisz".
                         - rewrite /inode_meta /i_type. iFrame.
                         - iFrame. }
                       iDestruct (cpu_own_transport CIDil CIDP5 0%nat eb
                                    (proc_addr j) b ltac:(wp_next_chain)
                                    with "Hcnt") as "Hcnt".
                       iDestruct (trap_csrs_ext_transport CIDil CIDP5 eb (proc_addr j)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                       iDestruct (cpu_claim_ext_transport CIDil CIDP5 eb (proc_addr j)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                       iApply (IU.wp_iunlock_sconf gs gfs gi cn gilk gislk
                                 cov logstart ik (iq/2)%Qp gsh dev iinum dnl bml
                                 pidv dq NP3 (K - 12)%nat eb (proc_addr j) b lks Vpr
                                 Kiu Hik HP3a0
                                 ltac:(lkbelow)
                                 with "Hcg Hcnt Htext Hpc Hitbl Hesck
                                       Hslkk Hslkd Hppid Hprocs Hdep
                                       Hidev Hiinum Hivalid Hload Hshot Hfrz").
                       all: try lkbelow.
                       iIntros (CIDiu Hqiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid
                                                  Hshr".
                       iDestruct (inode_shr_gen_forget with "Hshr")
                         as "Hshr".
                       assert (Hpc80 : ret_pc (NP3 !!! Regidx Rra)
                                = mword_of_int (NX + 0x8a)).
                       { rewrite HP3ra. pcw. }
                       iEval (rewrite Hpc80) in "Hpc".
                       (* THE REFERENCE IS WHOLE AGAIN, AND IT REMEMBERS
                          ITS GENERATION (fs-log.md §G.24).  iunlock hands
                          the share back generation-ERASED, so the name is
                          recovered by agreement against the short parent --
                          which has carried it since the shed -- and the
                          NAMED gather re-forms the reference at it.  That is
                          what lets this return carry ilock's own type
                          one-shot: create performs no parent type test, and
                          this is the fact that closes fs-sysfile's Blocker
                          B. *)
                       iEval (rewrite inode_shr_gen_intro) in "Hshr".
                       iDestruct "Hshr" as (gsh2) "Hshr".
                       iDestruct (inode_ref_short_shr_gen_agree
                                    with "Hkeep Hshr") as %<-.
                       iDestruct (inode_ref_gather_gen ik (iq/2)%Qp (iq/2)%Qp
                                    dev iinum gsh with "Hkeep Hshr") as "Href".
                       iEval (rewrite Qp.div_2) in "Href".
                       assert (HtydP : di_type dnl = T_DIR)
                         by (unfold T_DIR; exact Hty).
                       iAssert (inode_held_ty ipv T_DIR) with "[Href Hru]" as "Hip".
                       { rewrite /inode_held_ty. iExists ik, iq, iinum, gsh.
                         iSplitR; [iPureIntro; exact Hie |].
                         iSplitR; [iPureIntro; exact Hik |].
                         iSplitR; [iPureIntro; exact Hib |].
                         iSplitL "Href"; [rewrite -Hdev; iExact "Href" |].
                         iFrame "Hru". rewrite -HtydP. iExact "Hshot". }
                       assert (Hmiuregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                  (m !!! Regidx Ra1 : mword 64) miu)
                         by exact (nx_regs_cs m sp0 _ _ _ _ NP3 miu Hcsiu
                                     HP3regs).
                       pose proof Hmiuregs as HmiuR.
                       destruct HmiuR as (Z2 & _ & _ & _ & Z20 & _ & _ & _ & _
                                          & _ & Zthr).
                       assert (Hmiutr : nx_tregs m sp0 miu)
                         by exact (nx_tregs_of_regs m sp0 _ _ _ _ miu
                                     Hmiuregs).
                       iDestruct (nx_bs3_join with "Hbs1 Hbs2") as "Hbslot".
                       (* +0x8a c.j +0x5c *)
                       assert (Htj5cP : add_vec
                                 (mword_of_int (NX + 0x8a) : mword 64)
                                 (sign_extend' 64 (sign_extend' 21
                                    (concat_vec (mword_of_int 2025 : mword 11)
                                       ('b"0"))))
                               = mword_of_int (NX + 0x5c)) by pcw.
                       iApply (wp_cj_s_sconf (mword_of_int (NX + 0x8a))
                                 (sign_extend' 21
                                    (concat_vec (mword_of_int 2025 : mword 11)
                                       ('b"0")))
                                 miu (K - 12)%nat b
                                 ltac:(rewrite Htj5cP; vm_compute; reflexivity)
                                 with "Hcg Hpc []").
                       { iApply (nxi_08a with "Htext"). }
                       iIntros (CIDP6 HqP6). iApply bi.later_intro. iIntros "Hcg Hpc".
                       iEval (rewrite Htj5cP) in "Hpc".
                       iDestruct (cpu_own_transport CIDiu CIDP6 0%nat eb (proc_addr j) b
                                    ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                       (* iunlock threads [cpu_own] but not the complement, so
                          the pair is still at CIDP5 while [cpu_own] came back
                          at CIDiu. *)
                       iDestruct (trap_csrs_ext_transport CIDP5 CIDP6 eb (proc_addr j)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                       iDestruct (cpu_claim_ext_transport CIDP5 CIDP6 eb (proc_addr j)
                                    ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                       iSpecialize ("Htail" $! CIDP6 with "[%]");
                         [wp_next_chain |].
                       iApply ("Htail" $! miu ipv with
"[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                                 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                                 Hb11 Hb12").
                       ** exact Hmiutr.
                       ** exact Z20.
                       ** iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                          iSpecialize ("Hcont" $! CIDf with "[%]");
                            [wp_next_chain |].
                          (* L_par calls no iput, so the epoch the mint
                             opened is still open here: close it, since the
                             contract's post is [log_opS] (§G.20). *)
                          iDestruct (log_opSe_opS with "Hlog") as "Hlog".
                          iApply ("Hcont" $! mf ncur Scur true nf' ipv wc
                                    with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos
                                          Hppid Hcwdr Hpath Hname
                                          Hbslot [%] [%] [%] Hlog [Hip Hisl]").
                          --- exact Hcsf.
                          --- exact Hsbc.
                          --- exact HbW.
                          --- exact (nx_wi_free n ncur wc HbA HbB).
                          --- iSplitR; [| rewrite Hnp; cbn; iFrame "Hip Hisl"].
                              iPureIntro. split; [exact Hfa0 |].
                              intro Hc.
                              exists es0,
                                (take 14 (bview (e - a)%nat
                                   (fun i => pfun (a + i)%nat))).
                              split; [| exact Hviewt].
                              rewrite /nameiparent_of.
                              assert (Hnil : path_elems (drop o2 pl) = []).
                              { apply (proj2
                                   (path_elems_nil_iff (drop o2 pl))).
                                assert (Ho2 : (o2 = plen)%nat).
                                { destruct (Nat.eq_dec o2 plen) as [Hq | Hq];
                                    [exact Hq |].
                                  exfalso. exact (Hnn o2 ltac:(lia) Hnl). }
                                assert (Hd0 : drop o2 pl = []).
                                { rewrite Ho2.
                                  exact (nx_drop_nil plen plen pfun
                                           ltac:(lia)). }
                                rewrite Hd0. reflexivity. }
                              rewrite Hes2 Hnil app_nil_r. reflexivity.
                     * (* ---- everything else reaches dirlookup at +0xde ---- *)
                       assert (Htyd : di_type dnl = T_DIR)
                         by (unfold T_DIR; exact Hty).
                       (* licence (c)'s only demand on the record the ["."]
                          lookup returns: an allocated one (§7.1) *)
                       assert (Htydnz : bv_unsigned (di_type dnl) <> 0)
                         by (rewrite Htyd; vm_compute; discriminate).
                       assert (Hbwf : blkmap_wf cov logstart bml)
                         by (destruct Hiok as (Hq & _); exact Hq).
                       assert (Hbcov : bm_covers bml
                                 (bv_unsigned (di_size dnl)))
                         by (destruct Hiok as (_ & Hq & _); exact Hq).
                       assert (Hszb : bv_unsigned (di_size dnl)
                                 <= Z.of_nat MAXFILE * Z.of_nat BSIZE)
                         by (destruct Hiok as (_ & _ & _ & _ & Hq & _);
                             exact Hq).
                       assert (Hdio : dir_inums_ok datl
                                 (dir_nrec (bv_unsigned (di_size dnl))) nib).
                       { rewrite Hnib.
                         exact (dir_ok_dir icfg_nib dnl datl Hty Hdok). }
                       (* the block at +0xde is reached by TWO routes; it is
                          stated once, consuming everything but the registers,
                          the pc and the path. *)
                       iAssert (wp_next (CID0 := CIDD0) true (proc_addr j)
                                  (fun CIDz : CpuId =>
                          ∀ Mz : regfile,
                            ⌜nx_regs m sp0 (pa_add pv o2) ipv nb
                               (m !!! Regidx Ra1 : mword 64) Mz⌝ -∗
                            sie_cap_gpr KT1 Mz (K - 12)%nat b (proc_addr j) -∗
                            cpu_own 0 eb (proc_addr j) b lks -∗
                            trap_csrs_ext KT1 eb -∗
                            cpu_claim_ext eb (proc_addr j) -∗
                            pc_is (mword_of_int (NX + 0xde)) -∗
                            ([∗ list] i ∈ seq 0 (S plen),
                               pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
                            WP (Loop : expr riscv_lang)))%I
                         with "[IHl Hcont Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                                Hb10 Hb11 Hb12 Hisl Hbmap Hinos Hppid
                                Hcwdr Hname Hbs1 Hbs2 Hlog Hkeep Hru Hslkd
                                Hdep Hidev Hiinum Hivalid Hfrz Hdiat Hity
                                Himaj Himin Hinl Hisz Haddrs Hind Hblocks
                               Hdlnk Hdview Hfview]"
                         as "Hdlblk".
                       { iIntros (CIDz Hsz Mz) "%Hregz Hcg Hcnt Hextc Hclmc Hpc Hpath".
                         pose proof Hregz as Hrz.
                         destruct Hrz as (X2 & X8 & X9 & X19 & X20 & X21 & X22
                                          & X23 & X24 & X25 & Xthr).
                         (* +0xde c.li a2,0 *)
                         iApply (wp_cli_s_sconf (mword_of_int (NX + 0xde)) Ra2
                                   (mword_of_int 0 : mword 6)
                                   (mword_of_int 0 : mword 64) Mz
                                   (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                   ltac:(pcw) with "Hcg Hpc []").
                         { iApply (nxi_0de with "Htext"). }
                         iIntros (CIDG1 HqG1) "Hcg Hpc".
                         pose (GA1 := <[Regidx Ra2 := regval_into_reg
                               (mword_of_int 0 : mword 64)]> Mz).
                         assert (HGA1a2 : GA1 !!! Regidx Ra2
                                  = (mword_of_int 0 : mword 64))
                           by (rewrite /GA1; apply upd_eq).
                         assert (HGA1s5 : GA1 !!! Regidx Rs5 = nb)
                           by (rewrite /GA1 upd_ne; [exact X21 | nz]).
                         assert (HGA1s4 : GA1 !!! Regidx Rs4 = ipv)
                           by (rewrite /GA1 upd_ne; [exact X20 | nz]).
                         assert (HGA1regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                    (m !!! Regidx Ra1 : mword 64) GA1)
                           by exact (nx_regs_caller m sp0 _ _ _ _ Mz Ra2 _
                                       ltac:(vm_compute; reflexivity) Hregz).
                         assert (HqZ0 : add_vec_int
                                   (mword_of_int (NX + 0xde) : mword 64) 2
                                 = mword_of_int (NX + 0xe0)) by pcw.
                         iEval (rewrite HqZ0) in "Hpc".
                         (* +0xe0 c.mv a1,s5 *)
                         iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xe0)) Ra1
                                   Rs5 GA1 (K - 12)%nat b ltac:(nz)
                                   ltac:(rdok) with "Hcg Hpc []").
                         { iApply (nxi_0e0 with "Htext"). }
                         iIntros (CIDG2 HqG2) "Hcg Hpc". iEval (rgne) in "Hcg".
                         pose (GA2 := <[Regidx Ra1 := regval_into_reg
                               (add_vec (zero_reg : mword 64)
                                  (GA1 !!! Regidx Rs5))]> GA1).
                         assert (HGA2a1 : GA2 !!! Regidx Ra1 = nb).
                         { rewrite /GA2 upd_eq. rewrite HGA1s5.
                           apply add_vec_zero_l. }
                         assert (HGA2a2 : GA2 !!! Regidx Ra2
                                  = (mword_of_int 0 : mword 64))
                           by (rewrite /GA2 upd_ne; [exact HGA1a2 | nz]).
                         assert (HGA2s4 : GA2 !!! Regidx Rs4 = ipv)
                           by (rewrite /GA2 upd_ne; [exact HGA1s4 | nz]).
                         assert (HGA2regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                    (m !!! Regidx Ra1 : mword 64) GA2)
                           by exact (nx_regs_caller m sp0 _ _ _ _ GA1 Ra1 _
                                       ltac:(vm_compute; reflexivity)
                                       HGA1regs).
                         assert (HqZ2 : add_vec_int
                                   (mword_of_int (NX + 0xe0) : mword 64) 2
                                 = mword_of_int (NX + 0xe2)) by pcw.
                         iEval (rewrite HqZ2) in "Hpc".
                         (* +0xe2 c.mv a0,s4 *)
                         iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xe2)) Ra0
                                   Rs4 GA2 (K - 12)%nat b ltac:(nz)
                                   ltac:(rdok) with "Hcg Hpc []").
                         { iApply (nxi_0e2 with "Htext"). }
                         iIntros (CIDG3 HqG3) "Hcg Hpc". iEval (rgne) in "Hcg".
                         pose (GA3 := <[Regidx Ra0 := regval_into_reg
                               (add_vec (zero_reg : mword 64)
                                  (GA2 !!! Regidx Rs4))]> GA2).
                         assert (HGA3a0 : GA3 !!! Regidx Ra0 = ientry ik).
                         { rewrite /GA3 upd_eq. rewrite HGA2s4 Hie.
                           apply add_vec_zero_l. }
                         assert (HGA3a1 : GA3 !!! Regidx Ra1 = nb)
                           by (rewrite /GA3 upd_ne; [exact HGA2a1 | nz]).
                         assert (HGA3a2 : GA3 !!! Regidx Ra2
                                  = (mword_of_int 0 : mword 64))
                           by (rewrite /GA3 upd_ne; [exact HGA2a2 | nz]).
                         assert (HGA3regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                    (m !!! Regidx Ra1 : mword 64) GA3)
                           by exact (nx_regs_caller m sp0 _ _ _ _ GA2 Ra0 _
                                       ltac:(vm_compute; reflexivity)
                                       HGA2regs).
                         assert (HqZ4 : add_vec_int
                                   (mword_of_int (NX + 0xe2) : mword 64) 2
                                 = mword_of_int (NX + 0xe4)) by pcw.
                         iEval (rewrite HqZ4) in "Hpc".
                         (* +0xe4 jal ra,dirlookup *)
                         assert (Htgdl : add_vec
                                   (mword_of_int (NX + 0xe4) : mword 64)
                                   (sign_extend' 64
                                      (mword_of_int 2096752 : mword 21))
                                 = mword_of_int KernelSyms.dirlookup) by pcw.
                         iApply (wp_jal_s_sconf (mword_of_int (NX + 0xe4)) Rra
                                   (mword_of_int 2096752 : mword 21) GA3
                                   (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                   ltac:(vm_compute; reflexivity)
                                   with "Hcg Hpc []").
                         { iApply (nxi_0e4 with "Htext"). }
                         iIntros (CIDG4 HqG4) "Hcg Hpc".
                         iEval (rewrite Htgdl) in "Hpc".
                         pose (GA4 := <[Regidx Rra := regval_into_reg
                               (add_vec_int
                                  (mword_of_int (NX + 0xe4) : mword 64) 4)]>
                               GA3).
                         assert (HGA4ra : GA4 !!! Regidx Rra
                                  = add_vec_int
                                      (mword_of_int (NX + 0xe4) : mword 64) 4)
                           by (rewrite /GA4; apply upd_eq).
                         assert (HGA4a0 : GA4 !!! Regidx Ra0 = ientry ik)
                           by (rewrite /GA4 upd_ne; [exact HGA3a0 | nz]).
                         assert (HGA4a1 : GA4 !!! Regidx Ra1 = nb)
                           by (rewrite /GA4 upd_ne; [exact HGA3a1 | nz]).
                         assert (HGA4a2 : GA4 !!! Regidx Ra2
                                  = (mword_of_int 0 : mword 64))
                           by (rewrite /GA4 upd_ne; [exact HGA3a2 | nz]).
                         assert (HGA4regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                    (m !!! Regidx Ra1 : mword 64) GA4)
                           by exact (nx_regs_caller m sp0 _ _ _ _ GA3 Rra _
                                       ltac:(vm_compute; reflexivity)
                                       HGA3regs).
                         iAssert (inode_meta (ientry ik) dnl)
                           with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
                         { rewrite /inode_meta /i_type. iFrame. }
                         iAssert (inode_map gfs (ientry ik) bml)
                           with "[Haddrs Hind]" as "Hmap".
                         { rewrite /inode_map. iFrame. }
                         iDestruct (cpu_own_transport CIDz CIDG4 0%nat eb
                                      (proc_addr j) b ltac:(wp_next_chain)
                                      with "Hcnt") as "Hcnt".
                         iDestruct (trap_csrs_ext_transport CIDz CIDG4 eb (proc_addr j)
                                      ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                         iDestruct (cpu_claim_ext_transport CIDz CIDG4 eb (proc_addr j)
                                      ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                         iApply (DL.wp_dirlookup_sconf gs j gl gu gd gk
                                   pd pav pu bn gfs gi cn gtl ga gf cov
                                   logstart inodestart nib dev (ientry ik) iinum
                                   bml datl dnl dnl
                                   nf' false (mword_of_int 0 : mword 32)
                                   pidv dq (DfracOwn (1/2)) (DfracOwn 1)
                                   GA4 (K - 12)%nat eb b lks Vpr
                                   Kdl Htyd Hlg Hbwf Hbcov Hszb Hdio
                                   (* ---- THE LICENCE PREMISE, AND THIS IS
                                      THE SITE WHERE THE USER'S INVARIANT IS
                                      EARNED (fs-fragments.md §7.5.6, TRACE
                                      G).  The LEFT disjunct comes off
                                      [Hnl0] -- the [fs.c:693] guard
                                      [if(ip->nlink == 0) return 0] that the
                                      walk fell through two instructions
                                      ago.  That guard is the ONLY thing in
                                      xv6 stopping a chdir'd process from
                                      walking ".." out of an orphaned
                                      directory into a claim box (§7.5.4's
                                      trace), and turning it into this
                                      premise is what makes "the kernel
                                      never igets an inum in a disconnected
                                      subtree" a THEOREM of every licensed
                                      iget rather than a paragraph.  Note
                                      the ORDER the trace turns on: ilock
                                      happens BEFORE the guard, so the
                                      licence is HELD there and merely never
                                      DELIVERED -- which is why the
                                      enumeration lives at SpecIget and not
                                      on the payload. ---- *)
                                   (or_introl (nx_nlink_nz _ Hnl0))
                                   Hdoc Htydnz
                                   (* premise (6'), iclaim-ledger.md §3.3:
                                      region record = in-core record here *)
                                   eq_refl
                                   Hj Hgs
                                   HGA4a0
                                   ltac:(rewrite HGA4a2; vm_compute;
                                         reflexivity)
                                   with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hkenv
                                         Hidev Hmeta Hmap Hblocks [Hname] []
                                         Hppid Hprocs Hdev Hgeom Hdlk Hbs1
                                         Hitb2 Hitbl Hesc Hireg Hisl Hdlnk Hdiat").
                         all: try lkbelow.
                         (* dirlookup is eb-generic now; namex is still at
                            [eb = true], where the complement is [emp]. *)
                         { iEval (rewrite HGA4a1). iExact "Hname". }
                         { done. }
                         iIntros (CIDdl Hqdl mdl found kdir kslot qq)
                           "%Hcsdl Hcg Hcnt Hextc Hclmc Hpc Hidev Hmeta Hmap Hblocks
                            Hname Hppid Hbs1 Hdlnk Hdiat Harm".
                         iEval (rewrite HGA4a1) in "Hname".
                         assert (Hpcd8 : ret_pc (GA4 !!! Regidx Rra)
                                  = mword_of_int (NX + 0xe8)).
                         { rewrite HGA4ra. pcw. }
                         iEval (rewrite Hpcd8) in "Hpc".
                         assert (Hmdlregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                    (m !!! Regidx Ra1 : mword 64) mdl)
                           by exact (nx_regs_cs m sp0 _ _ _ _ GA4 mdl Hcsdl
                                       HGA4regs).
                         pose proof Hmdlregs as HmdlR.
                         destruct HmdlR as (Z2 & Z8 & Z9 & Z19 & Z20 & Z21
                                            & Z22 & Z23 & Z24 & Z25 & Zthr).
                         iEval (rewrite /inode_map) in "Hmap".
                         iDestruct "Hmap" as "[Haddrs Hind]".
                         iAssert (ic_loaded gfs gi cov logstart ik iinum dnl
                                    bml)
                           with "[Hdiat Hmeta Haddrs Hind Hblocks Hdlnk Hdview Hfview]"
                           as "Hload".
                         { rewrite /ic_loaded. iExists datl.
                           iSplitR; [iPureIntro; exact Hiok |].
                           iSplitR; [iPureIntro; exact Hdok |].
                           iSplitR; [iPureIntro; exact Hddix |].
                           iSplitR; [iPureIntro; exact Hdoc |].
                           iSplitR; [iPureIntro; exact Hduq |].
                           iSplitL "Hdlnk"; [iExact "Hdlnk" |].
                           iFrame "Hdiat Hmeta Haddrs Hind Hblocks Hdview Hfview". }
                         iDestruct (nx_bs3_join with "Hbs1 Hbs2") as "Hbslot".
                         destruct found.
                         - (* ============ FOUND: recurse on the child ==== *)
                           iDestruct "Harm"
                             as "((%Hsome & %Hkslot & %Hdla0) & Href2 & Hru2 & _)".
                           assert (Hklt : (kdir < dir_nrec
                                     (bv_unsigned (di_size dnl)))%nat)
                             by exact (dir_first_lt datl _ kdir
                                         (bname 14 nf') Hsome).
                           assert (Hklive : dir_live datl kdir)
                             by exact (dir_first_live datl _ kdir
                                         (bname 14 nf') Hsome).
                           assert (Hcinb : bv_unsigned
                                     (zero_extend' 32
                                        (dir_inum datl kdir : mword 16)
                                      : mword 32) < 16 * Z.of_nat nib).
                           { rewrite (dlk_zext32_unsigned
                                        (dir_inum datl kdir)).
                             exact (Hdio kdir Hklt Hklive). }
                           iAssert (inode_held (ientry kslot))
                             with "[Href2 Hru2]" as "Hip2".
                           { rewrite /inode_held.
                             iExists kslot, qq,
                               (zero_extend' 32
                                  (dir_inum datl kdir : mword 16)).
                             iSplitR; [done |].
                             iSplitR; [iPureIntro; exact Hkslot |].
                             iSplitR; [iPureIntro; rewrite -Hnib;
                                       exact Hcinb |].
                             iFrame "Hru2". rewrite -Hdev. iExact "Href2". }
                           (* +0xe8 c.mv s2,a0 *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xe8))
                                     Rs2 Ra0 mdl (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_0e8 with "Htext"). }
                           iIntros (CIDG5 HqG5) "Hcg Hpc".
                           iEval (rgne) in "Hcg".
                           pose (GB1 := <[Regidx Rs2 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (mdl !!! Regidx Ra0))]> mdl).
                           assert (HGB1s2 : GB1 !!! Regidx Rs2
                                    = ientry kslot).
                           { rewrite /GB1 upd_eq. rewrite Hdla0.
                             apply add_vec_zero_l. }
                           assert (HGB1a0 : GB1 !!! Regidx Ra0
                                    = ientry kslot)
                             by (rewrite /GB1 upd_ne; [exact Hdla0 | nz]).
                           assert (HGB1s4 : GB1 !!! Regidx Rs4 = ipv)
                             by (rewrite /GB1 upd_ne; [exact Z20 | nz]).
                           assert (HGB1regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GB1)
                             by exact (nx_regs_s2 m sp0 _ _ _ _ _ mdl
                                         Hmdlregs).
                           assert (HqZa : add_vec_int
                                     (mword_of_int (NX + 0xe8) : mword 64) 2
                                   = mword_of_int (NX + 0xea)) by pcw.
                           iEval (rewrite HqZa) in "Hpc".
                           (* +0xea c.beqz a0 -- not taken, a0 is an entry *)
                           iApply (wp_cbeqz_fall_s_sconf
                                     (mword_of_int (NX + 0xea))
                                     (mword_of_int 209 : mword 8)
                                     (Cregidx (mword_of_int 2)) Ra0
                                     GB1 (K - 12)%nat b
                                     ltac:(vm_compute; reflexivity) ltac:(nz)
                                     ltac:(rgne; rewrite HGB1a0;
                                           exact (proj2 (eq_vec_false_iff _ _)
                                                    (ientry_ne_zero kslot
                                                       ltac:(lia))))
                                     with "Hcg Hpc []").
                           { iApply (nxi_0ea with "Htext"). }
                           iIntros (CIDG6 HqG6) "Hcg Hpc".
                           assert (HqZc : add_vec_int
                                     (mword_of_int (NX + 0xea) : mword 64) 2
                                   = mword_of_int (NX + 0xec)) by pcw.
                           iEval (rewrite HqZc) in "Hpc".
                           (* +0xec c.mv a0,s4 *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xec))
                                     Ra0 Rs4 GB1 (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_0ec with "Htext"). }
                           iIntros (CIDG7 HqG7) "Hcg Hpc".
                           iEval (rgne) in "Hcg".
                           pose (GB2 := <[Regidx Ra0 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (GB1 !!! Regidx Rs4))]> GB1).
                           assert (HGB2a0 : GB2 !!! Regidx Ra0 = ientry ik).
                           { rewrite /GB2 upd_eq. rewrite HGB1s4 Hie.
                             apply add_vec_zero_l. }
                           assert (HGB2s2 : GB2 !!! Regidx Rs2
                                    = ientry kslot)
                             by (rewrite /GB2 upd_ne; [exact HGB1s2 | nz]).
                           assert (HGB2regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GB2)
                             by exact (nx_regs_caller m sp0 _ _ _ _ GB1 Ra0 _
                                         ltac:(vm_compute; reflexivity)
                                         HGB1regs).
                           assert (HqZe : add_vec_int
                                     (mword_of_int (NX + 0xec) : mword 64) 2
                                   = mword_of_int (NX + 0xee)) by pcw.
                           iEval (rewrite HqZe) in "Hpc".
                           (* +0xee jal ra,iunlockput *)
                           assert (Htgup2 : add_vec
                                     (mword_of_int (NX + 0xee) : mword 64)
                                     (sign_extend' 64
                                        (mword_of_int 2095826 : mword 21))
                                   = mword_of_int KernelSyms.iunlockput)
                             by pcw.
                           iApply (wp_jal_s_sconf (mword_of_int (NX + 0xee))
                                     Rra (mword_of_int 2095826 : mword 21)
                                     GB2 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                     ltac:(vm_compute; reflexivity)
                                     with "Hcg Hpc []").
                           { iApply (nxi_0ee with "Htext"). }
                           iIntros (CIDG8 HqG8) "Hcg Hpc".
                           iEval (rewrite Htgup2) in "Hpc".
                           pose (GB3 := <[Regidx Rra := regval_into_reg
                                 (add_vec_int
                                    (mword_of_int (NX + 0xee) : mword 64) 4)]>
                                 GB2).
                           assert (HGB3ra : GB3 !!! Regidx Rra
                                    = add_vec_int
                                        (mword_of_int (NX + 0xee) : mword 64)
                                        4)
                             by (rewrite /GB3; apply upd_eq).
                           assert (HGB3a0 : GB3 !!! Regidx Ra0 = ientry ik)
                             by (rewrite /GB3 upd_ne; [exact HGB2a0 | nz]).
                           assert (HGB3s2 : GB3 !!! Regidx Rs2
                                    = ientry kslot)
                             by (rewrite /GB3 upd_ne; [exact HGB2s2 | nz]).
                           assert (HGB3regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GB3)
                             by exact (nx_regs_caller m sp0 _ _ _ _ GB2 Rra _
                                         ltac:(vm_compute; reflexivity)
                                         HGB2regs).
                           iDestruct (cpu_own_transport CIDdl CIDG8 0%nat eb
                                        (proc_addr j) b
                                        ltac:(wp_next_chain)
                                        with "Hcnt") as "Hcnt".
                           iDestruct (trap_csrs_ext_transport CIDdl CIDG8 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                           iDestruct (cpu_claim_ext_transport CIDdl CIDG8 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                           iDestruct (inode_ref_short_gen_forget with "Hkeep")
                             as "Hkeep2".
                           iApply (IUP.wp_iunlockput_gen gs j gl gu gd gk
                                     pd pav pu bn g gfs gi cn gtl gilk gislk
                                     cov logstart bmapstart inodestart nib
                                     size dev ik (iq/2)%Qp (iq/2)%Qp gsh
                                     iinum dnl bml ncur Scur wc false true
                                     enx pidv dq dqb dqs
                                     GB3 (K - 12)%nat eb b lks Vpr
                                     Kiup Hik HbW ltac:(discriminate)
                                     Hlg Hsize Hbmap0 Hbmapcov
                                     Hbmaplog Hinos0 Hibc Hibl Hib' Hcovb
                                     Hiu Hj Hgs HGB3a0 Hbelow
                                     with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio
                                           Hlogc Hitb2 Hitbl Hesck Hireg []
                                           Hslkk Hslkd Hdep Hidev
                                           Hiinum Hivalid Hload Hshot Hfrz [$Hkeep2 $Hru] Hbmap
                                           Hinos Hbits Hppid Hprocs Hdev
                                           Hgeom Hdlk Hbslot Hcrz Hlog").
                           all: try lkbelow.
                           (* RULING G: a runtime caller lends the SEALED arm of
                              the borrowed regime and discards what comes back --
                              its own copy is persistent. *)
                           { iExact "Hropen". }
                           iIntros (CIDup Hqup mup nup Sup wup)
                             "%Hcsup Hcg Hcnt Hextc Hclmc Hpc Hppid Hbmap Hinos
                              Hbslot %Hsup %Hwup %Hwupc %Hbdup Hlog Hisl".
                           assert (Hpce2 : ret_pc (GB3 !!! Regidx Rra)
                                    = mword_of_int (NX + 0xf2)).
                           { rewrite HGB3ra. pcw. }
                           iEval (rewrite Hpce2) in "Hpc".
                           assert (Hmupregs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) mup)
                             by exact (nx_regs_cs m sp0 _ _ _ _ GB3 mup Hcsup
                                         HGB3regs).
                           assert (Hmups2 : mup !!! Regidx Rs2
                                    = ientry kslot).
                           { rewrite (callee_saved_lookup Hcsup Rs2
                                        ltac:(vm_compute; reflexivity)).
                             exact HGB3s2. }
                           (* +0xf2 c.mv s4,s2, then FALL into the walk *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xf2))
                                     Rs4 Rs2 mup (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_0f2 with "Htext"). }
                           iIntros (CIDG9 HqG9) "Hcg Hpc".
                           iEval (rgne; rewrite Hmups2) in "Hcg".
                           pose (GB4 := <[Regidx Rs4 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (ientry kslot))]> mup).
                           assert (HGB4regs : nx_regs m sp0 (pa_add pv o2)
                                      (ientry kslot) nb
                                      (m !!! Regidx Ra1 : mword 64) GB4).
                           { rewrite /GB4 add_vec_zero_l.
                             exact (nx_regs_s4 m sp0 (pa_add pv o2) ipv
                                      (ientry kslot) nb _ mup Hmupregs). }
                           assert (HqE4 : add_vec_int
                                     (mword_of_int (NX + 0xf2) : mword 64) 2
                                   = mword_of_int (NX + 0xf4)) by pcw.
                           iEval (rewrite HqE4) in "Hpc".
                           destruct (nx_wi_step
                                       (length (path_elems (drop o2 pl)))
                                       n ncur nup wc wup HbA HbB HbD HbC Hwupc
                                       (proj1 Hbdup) (proj2 Hbdup))
                             as (Hnb1 & Hnb2 & Hnb2b & Hnb3).
                           (* the report's membership rides the level's own
                              set growth *)
                           assert (Hnb4 : (wc || wup)%bool = true ->
                                     bmapstart ∈ Sup).
                           { intros Hw. destruct wc; destruct wup;
                               simpl in Hw;
                               first [ exact (Hsup _ (HbW eq_refl))
                                     | exact (Hwup eq_refl)
                                     | discriminate ]. }
                           iDestruct (cpu_own_transport CIDup CIDG9 0%nat eb
                                        (proc_addr j) b
                                        ltac:(wp_next_chain)
                                        with "Hcnt") as "Hcnt".
                           iDestruct (trap_csrs_ext_transport CIDup CIDG9 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                           iDestruct (cpu_claim_ext_transport CIDup CIDG9 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                           iDestruct (wp_next_shift (b := true) (CIDa := CIDl)
                                        (CIDb := CIDG9)
                                        ltac:(wp_next_chain)
                                        with "Hcont") as "Hcont".
                           iSpecialize ("IHl" $! CIDG9 with "[%]");
                             [wp_next_chain |].
                           iApply ("IHl" $! o2 (ientry kslot) GB4 nup Sup
                                     (es0 ++ [take 14 (bview (e - a)%nat
                                        (fun i => pfun (a + i)%nat))]) nf'
                                     (wc || wup)%bool
                                     with "[%] [%] [%] [%] [%] [%] [%] [%]
                                           [%] [%] Hcg Hcnt Hextc Hclmc Hpc
                                           Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                                           Hb9 Hb10 Hb11 Hb12 Hip2 Hisl
                                           Hbmap Hinos Hppid Hcwdr Hpath Hname Hbslot Hlog
                                           Hcont").
                           -- lia.
                           -- exact J2.
                           -- exact Hes2.
                           -- exact Hnb1.
                           -- exact Hnb2.
                           -- exact Hnb2b.
                           -- exact Hnb3.
                           -- exact Hnb4.
                           (* THE BACK EDGE'S set obligation, and the only one
                              the loop owes: the caller's set was inside the
                              turn's entry set, and this turn's iunlockput only
                              grew it. *)
                           -- exact (nx_sub_trans _ _ _ Hsbc Hsup).
                           -- exact HGB4regs.
                         - (* ============ MISS: iunlockput and return 0 === *)
                           iDestruct "Harm"
                             as "((%Hnone & %Hdla0) & Hisl2 & _)".
                           (* +0xe8 c.mv s2,a0 *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xe8))
                                     Rs2 Ra0 mdl (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_0e8 with "Htext"). }
                           iIntros (CIDG5 HqG5) "Hcg Hpc".
                           iEval (rgne) in "Hcg".
                           pose (GC1 := <[Regidx Rs2 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (mdl !!! Regidx Ra0))]> mdl).
                           assert (HGC1s2 : GC1 !!! Regidx Rs2
                                    = (mword_of_int 0 : mword 64)).
                           { rewrite /GC1 upd_eq. rewrite Hdla0.
                             apply add_vec_zero_l. }
                           assert (HGC1a0 : GC1 !!! Regidx Ra0
                                    = (mword_of_int 0 : mword 64))
                             by (rewrite /GC1 upd_ne; [exact Hdla0 | nz]).
                           assert (HGC1s4 : GC1 !!! Regidx Rs4 = ipv)
                             by (rewrite /GC1 upd_ne; [exact Z20 | nz]).
                           assert (HGC1regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GC1)
                             by exact (nx_regs_s2 m sp0 _ _ _ _ _ mdl
                                         Hmdlregs).
                           assert (HqZa : add_vec_int
                                     (mword_of_int (NX + 0xe8) : mword 64) 2
                                   = mword_of_int (NX + 0xea)) by pcw.
                           iEval (rewrite HqZa) in "Hpc".
                           assert (Htg082 : add_vec
                                     (mword_of_int (NX + 0xea) : mword 64)
                                     (sign_extend' 64 (sign_extend' 13
                                        (concat_vec
                                           (mword_of_int 209 : mword 8)
                                           ('b"0"))))
                                   = mword_of_int (NX + 0x8c)) by pcw.
                           (* +0xea c.beqz a0 -- taken *)
                           iApply (wp_cbeqz_taken_s_sconf
                                     (mword_of_int (NX + 0xea))
                                     (mword_of_int 209 : mword 8)
                                     (Cregidx (mword_of_int 2)) Ra0
                                     GC1 (K - 12)%nat b
                                     ltac:(vm_compute; reflexivity) ltac:(nz)
                                     ltac:(rgne; rewrite HGC1a0; vm_compute;
                                           reflexivity)
                                     ltac:(rewrite Htg082; vm_compute;
                                           reflexivity)
                                     with "Hcg Hpc []").
                           { iApply (nxi_0ea with "Htext"). }
                           iIntros (CIDG6 HqG6). iApply bi.later_intro. iIntros "Hcg Hpc".
                           iEval (rewrite Htg082) in "Hpc".
                           (* +0x8c c.mv a0,s4 *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x8c))
                                     Ra0 Rs4 GC1 (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_08c with "Htext"). }
                           iIntros (CIDG7 HqG7) "Hcg Hpc".
                           iEval (rgne) in "Hcg".
                           pose (GC2 := <[Regidx Ra0 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (GC1 !!! Regidx Rs4))]> GC1).
                           assert (HGC2a0 : GC2 !!! Regidx Ra0 = ientry ik).
                           { rewrite /GC2 upd_eq. rewrite HGC1s4 Hie.
                             apply add_vec_zero_l. }
                           assert (HGC2s2 : GC2 !!! Regidx Rs2
                                    = (mword_of_int 0 : mword 64))
                             by (rewrite /GC2 upd_ne; [exact HGC1s2 | nz]).
                           assert (HGC2regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GC2)
                             by exact (nx_regs_caller m sp0 _ _ _ _ GC1 Ra0 _
                                         ltac:(vm_compute; reflexivity)
                                         HGC1regs).
                           assert (Hq84 : add_vec_int
                                     (mword_of_int (NX + 0x8c) : mword 64) 2
                                   = mword_of_int (NX + 0x8e)) by pcw.
                           iEval (rewrite Hq84) in "Hpc".
                           (* +0x8e jal ra,iunlockput *)
                           assert (Htgup3 : add_vec
                                     (mword_of_int (NX + 0x8e) : mword 64)
                                     (sign_extend' 64
                                        (mword_of_int 2095922 : mword 21))
                                   = mword_of_int KernelSyms.iunlockput)
                             by pcw.
                           iApply (wp_jal_s_sconf (mword_of_int (NX + 0x8e))
                                     Rra (mword_of_int 2095922 : mword 21)
                                     GC2 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                                     ltac:(vm_compute; reflexivity)
                                     with "Hcg Hpc []").
                           { iApply (nxi_08e with "Htext"). }
                           iIntros (CIDG8 HqG8) "Hcg Hpc".
                           iEval (rewrite Htgup3) in "Hpc".
                           pose (GC3 := <[Regidx Rra := regval_into_reg
                                 (add_vec_int
                                    (mword_of_int (NX + 0x8e) : mword 64) 4)]>
                                 GC2).
                           assert (HGC3ra : GC3 !!! Regidx Rra
                                    = add_vec_int
                                        (mword_of_int (NX + 0x8e) : mword 64)
                                        4)
                             by (rewrite /GC3; apply upd_eq).
                           assert (HGC3a0 : GC3 !!! Regidx Ra0 = ientry ik)
                             by (rewrite /GC3 upd_ne; [exact HGC2a0 | nz]).
                           assert (HGC3s2 : GC3 !!! Regidx Rs2
                                    = (mword_of_int 0 : mword 64))
                             by (rewrite /GC3 upd_ne; [exact HGC2s2 | nz]).
                           assert (HGC3regs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) GC3)
                             by exact (nx_regs_caller m sp0 _ _ _ _ GC2 Rra _
                                         ltac:(vm_compute; reflexivity)
                                         HGC2regs).
                           iDestruct (cpu_own_transport CIDdl CIDG8 0%nat eb
                                        (proc_addr j) b
                                        ltac:(wp_next_chain)
                                        with "Hcnt") as "Hcnt".
                           iDestruct (trap_csrs_ext_transport CIDdl CIDG8 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                           iDestruct (cpu_claim_ext_transport CIDdl CIDG8 eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                           iDestruct (inode_ref_short_gen_forget with "Hkeep")
                             as "Hkeep2".
                           iApply (IUP.wp_iunlockput_gen gs j gl gu gd gk
                                     pd pav pu bn g gfs gi cn gtl gilk gislk
                                     cov logstart bmapstart inodestart nib
                                     size dev ik (iq/2)%Qp (iq/2)%Qp gsh
                                     iinum dnl bml ncur Scur wc false true
                                     enx pidv dq dqb dqs
                                     GC3 (K - 12)%nat eb b lks Vpr
                                     Kiup Hik HbW ltac:(discriminate)
                                     Hlg Hsize Hbmap0 Hbmapcov
                                     Hbmaplog Hinos0 Hibc Hibl Hib' Hcovb
                                     Hiu Hj Hgs HGC3a0 Hbelow
                                     with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio
                                           Hlogc Hitb2 Hitbl Hesck Hireg []
                                           Hslkk Hslkd Hdep Hidev
                                           Hiinum Hivalid Hload Hshot Hfrz [$Hkeep2 $Hru] Hbmap
                                           Hinos Hbits Hppid Hprocs Hdev
                                           Hgeom Hdlk Hbslot Hcrz Hlog").
                           all: try lkbelow.
                           (* RULING G: a runtime caller lends the SEALED arm of
                              the borrowed regime and discards what comes back --
                              its own copy is persistent. *)
                           { iExact "Hropen". }
                           iIntros (CIDup Hqup mup nup Sup wup)
                             "%Hcsup Hcg Hcnt Hextc Hclmc Hpc Hppid Hbmap Hinos
                              Hbslot %Hsup %Hwup %Hwupc %Hbdup Hlog Hisl3".
                           assert (Hpc88 : ret_pc (GC3 !!! Regidx Rra)
                                    = mword_of_int (NX + 0x92)).
                           { rewrite HGC3ra. pcw. }
                           iEval (rewrite Hpc88) in "Hpc".
                           assert (Hmupregs : nx_regs m sp0 (pa_add pv o2) ipv
                                      nb (m !!! Regidx Ra1 : mword 64) mup)
                             by exact (nx_regs_cs m sp0 _ _ _ _ GC3 mup Hcsup
                                         HGC3regs).
                           assert (Hmups2 : mup !!! Regidx Rs2
                                    = (mword_of_int 0 : mword 64)).
                           { rewrite (callee_saved_lookup Hcsup Rs2
                                        ltac:(vm_compute; reflexivity)).
                             exact HGC3s2. }
                           (* +0x92 c.mv s4,s2 *)
                           iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x92))
                                     Rs4 Rs2 mup (K - 12)%nat b ltac:(nz)
                                     ltac:(rdok) with "Hcg Hpc []").
                           { iApply (nxi_092 with "Htext"). }
                           iIntros (CIDG9 HqG9) "Hcg Hpc".
                           iEval (rgne; rewrite Hmups2) in "Hcg".
                           pose (GC4 := <[Regidx Rs4 := regval_into_reg
                                 (add_vec (zero_reg : mword 64)
                                    (mword_of_int 0 : mword 64))]> mup).
                           assert (HGC4s4 : GC4 !!! Regidx Rs4
                                    = (mword_of_int 0 : mword 64)).
                           { rewrite /GC4 upd_eq. apply add_vec_zero_l. }
                           assert (HGC4tr : nx_tregs m sp0 GC4).
                           { pose proof (nx_tregs_of_regs m sp0 _ _ _ _ mup
                                           Hmupregs) as Hmt.
                             destruct Hmt as [U2 Uthr]. split.
                             - rewrite /GC4 upd_ne; [exact U2 | nz].
                             - intros c Hc T2' T8 T9 T18 T19 T20 T21 T22 T23
                                      T24 T25 T26.
                               rewrite /GC4 upd_ne; [| dlk_xne T20].
                               exact (Uthr c Hc T2' T8 T9 T18 T19 T20 T21 T22
                                        T23 T24 T25 T26). }
                           assert (Hq8a : add_vec_int
                                     (mword_of_int (NX + 0x92) : mword 64) 2
                                   = mword_of_int (NX + 0x94)) by pcw.
                           iEval (rewrite Hq8a) in "Hpc".
                           (* +0x94 c.j +0x5c *)
                           assert (Htj5cM : add_vec
                                     (mword_of_int (NX + 0x94) : mword 64)
                                     (sign_extend' 64 (sign_extend' 21
                                        (concat_vec
                                           (mword_of_int 2020 : mword 11)
                                           ('b"0"))))
                                   = mword_of_int (NX + 0x5c)) by pcw.
                           iApply (wp_cj_s_sconf (mword_of_int (NX + 0x94))
                                     (sign_extend' 21
                                        (concat_vec
                                           (mword_of_int 2020 : mword 11)
                                           ('b"0")))
                                     GC4 (K - 12)%nat b
                                     ltac:(rewrite Htj5cM; vm_compute;
                                           reflexivity)
                                     with "Hcg Hpc []").
                           { iApply (nxi_094 with "Htext"). }
                           iIntros (CIDGa HqGa). iApply bi.later_intro. iIntros "Hcg Hpc".
                           iEval (rewrite Htj5cM) in "Hpc".
                           iDestruct (cpu_own_transport CIDup CIDGa 0%nat eb (proc_addr j) b
                                        ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                           iDestruct (trap_csrs_ext_transport CIDup CIDGa eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                           iDestruct (cpu_claim_ext_transport CIDup CIDGa eb (proc_addr j)
                                        ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                           iSpecialize ("Htail" $! CIDGa with "[%]");
                             [wp_next_chain |].
                           iApply ("Htail" $! GC4 (mword_of_int 0 : mword 64)
                                     with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                                     Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                                     Hb10 Hb11 Hb12").
                           -- exact HGC4tr.
                           -- exact HGC4s4.
                           -- iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                              iSpecialize ("Hcont" $! CIDf with "[%]");
                                [wp_next_chain |].
                              iDestruct (iref_slots_combine 1 1
                                           with "Hisl2 Hisl3") as "Hisl".
                              iApply ("Hcont" $! mf nup Sup false nf'
                                        (mword_of_int 0 : mword 64)
                                        (wc || wup)%bool
                                        with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos
                                              Hppid Hcwdr
                                              Hpath Hname Hbslot [%] [%] [%] Hlog
                                              [Hisl]").
                              ++ exact Hcsf.
                              ++ exact (nx_sub_trans _ _ _ Hsbc Hsup).
                              ++ intros Hw. destruct wc; destruct wup;
                                   simpl in Hw;
                                   first [ exact (Hsup _ (HbW eq_refl))
                                         | exact (Hwup eq_refl)
                                         | discriminate ].
                              ++ exact (nx_wi_spend n ncur nup wc wup true
                                          HbA HbB Hwupc
                                          (proj1 Hbdup) (proj2 Hbdup)).
                              ++ iSplitR; [iPureIntro; exact Hfa0 |].
                                 iExact "Hisl". }
                       (* ---- the two routes into +0xde ---- *)
                       destruct npar.
                       ** (* nameiparent, but the path continues *)
                          assert (Hnl : pfun o2 <> NUL).
                          { intro Hc. apply Hoth.
                            split; [reflexivity | exact Hc]. }
                          iApply (wp_beqz_x0_fall_s_sconf
                                    (mword_of_int (NX + 0xd4))
                                    (mword_of_int 10 : mword 13) Rs6 W0
                                    (K - 12)%nat b ltac:(nz)
                                    ltac:(rgne; rewrite HW0s6; exact Ha1)
                                    with "Hcg Hpc []").
                          { iApply (nxi_0d4 with "Htext"). }
                          iIntros (CIDQ1 HqQ1) "Hcg Hpc".
                          assert (Hqc8b : add_vec_int
                                    (mword_of_int (NX + 0xd4) : mword 64) 4
                                  = mword_of_int (NX + 0xd8)) by pcw.
                          iEval (rewrite Hqc8b) in "Hpc".
                          iDestruct (nx_buf_acc pv dqpv pfun (S plen)
                                       o2 ltac:(lia) with "Hpath")
                            as "[Hpb Hpback]".
                          iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (NX + 0xd8))
                                    Ra5 Rs1 (mword_of_int 0 : mword 12) W0
                                    (K - 12)%nat (pfun o2 : mword 8) b
                                    (dqm := dqpv)
                                    ltac:(nz) ltac:(rdok)
                                    with "Hcg Hpc [] [Hpb]").
                          { iApply (nxi_0d8 with "Htext"). }
                          { iEval (rgne; rewrite HW0s1 addv_sext0).
                            iExact "Hpb". }
                          iIntros (CIDQ2 HqQ2) "Hcg Hpc Hpb".
                          iEval (rgne; rewrite HW0s1 addv_sext0) in "Hpb".
                          iDestruct ("Hpback" with "Hpb") as "Hpath".
                          pose (QA1 := <[Regidx Ra5 := regval_into_reg
                                (zero_extend' 64 (pfun o2 : mword 8))]> W0).
                          assert (HQA1a5 : QA1 !!! Regidx Ra5
                                   = (zero_extend' 64 (pfun o2 : mword 8)
                                      : mword 64))
                            by (rewrite /QA1; apply upd_eq).
                          assert (HQA1regs : nx_regs m sp0 (pa_add pv o2) ipv
                                     nb (m !!! Regidx Ra1 : mword 64) QA1)
                            by exact (nx_regs_caller m sp0 _ _ _ _ W0 Ra5 _
                                        ltac:(vm_compute; reflexivity)
                                        HW0regs).
                          assert (Hqccb : add_vec_int
                                    (mword_of_int (NX + 0xd8) : mword 64) 4
                                  = mword_of_int (NX + 0xdc)) by pcw.
                          iEval (rewrite Hqccb) in "Hpc".
                          iApply (wp_cbeqz_fall_s_sconf
                                    (mword_of_int (NX + 0xdc))
                                    (mword_of_int 212 : mword 8)
                                    (Cregidx (mword_of_int 7)) Ra5
                                    QA1 (K - 12)%nat b
                                    ltac:(vm_compute; reflexivity) ltac:(nz)
                                    ltac:(rgne; rewrite HQA1a5;
                                          exact (nx_nul_ne _ Hnl))
                                    with "Hcg Hpc []").
                          { iApply (nxi_0dc with "Htext"). }
                          iIntros (CIDQ3 HqQ3) "Hcg Hpc".
                          assert (Hqceb : add_vec_int
                                    (mword_of_int (NX + 0xdc) : mword 64) 2
                                  = mword_of_int (NX + 0xde)) by pcw.
                          iEval (rewrite Hqceb) in "Hpc".
                          iDestruct (cpu_own_transport CIDil CIDQ3 0%nat eb
                                       (proc_addr j) b ltac:(wp_next_chain)
                                       with "Hcnt") as "Hcnt".
                          iDestruct (trap_csrs_ext_transport CIDil CIDQ3 eb (proc_addr j)
                                       ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                          iDestruct (cpu_claim_ext_transport CIDil CIDQ3 eb (proc_addr j)
                                       ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                          iSpecialize ("Hdlblk" $! CIDQ3 with "[%]");
                            [wp_next_chain |].
                          iApply ("Hdlblk" $! QA1
                                    with "[%] Hcg Hcnt Hextc Hclmc Hpc Hpath").
                          exact HQA1regs.
                       ** (* namei: the flag is zero, straight to dirlookup *)
                          assert (Htg0ceb : add_vec
                                    (mword_of_int (NX + 0xd4) : mword 64)
                                    (sign_extend' 64
                                       (mword_of_int 10 : mword 13))
                                  = mword_of_int (NX + 0xde)) by pcw.
                          iApply (wp_beqz_x0_taken_s_sconf
                                    (mword_of_int (NX + 0xd4))
                                    (mword_of_int 10 : mword 13) Rs6 W0
                                    (K - 12)%nat b ltac:(nz)
                                    ltac:(rgne; rewrite HW0s6; exact Ha1)
                                    ltac:(rewrite Htg0ceb; vm_compute;
                                          reflexivity)
                                    with "Hcg Hpc []").
                          { iApply (nxi_0d4 with "Htext"). }
                          iIntros (CIDQ1 HqQ1). iApply bi.later_intro. iIntros "Hcg Hpc".
                          iEval (rewrite Htg0ceb) in "Hpc".
                          iDestruct (cpu_own_transport CIDil CIDQ1 0%nat eb
                                       (proc_addr j) b ltac:(wp_next_chain)
                                       with "Hcnt") as "Hcnt".
                          iDestruct (trap_csrs_ext_transport CIDil CIDQ1 eb (proc_addr j)
                                       ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                          iDestruct (cpu_claim_ext_transport CIDil CIDQ1 eb (proc_addr j)
                                       ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                          iSpecialize ("Hdlblk" $! CIDQ1 with "[%]");
                            [wp_next_chain |].
                          iApply ("Hdlblk" $! W0
                                    with "[%] Hcg Hcnt Hextc Hclmc Hpc Hpath").
                          exact HW0regs.
                   + (* ============ NOT A DIRECTORY: +0x54 ============ *)
                     iApply (wp_bne_taken_s_sconf (mword_of_int (NX + 0xca))
                               (mword_of_int 8074 : mword 13) Rs7 Ra5
                               V3 (K - 12)%nat b ltac:(nz) ltac:(nz)
                               ltac:(rgne; rgne; rewrite HV3a5 HV3s7;
                                     exact (nx_tdir_ne _ Hty))
                               ltac:(rewrite Htg054; vm_compute; reflexivity)
                               with "Hcg Hpc []").
                     { iApply (nxi_0ca with "Htext"). }
                     iIntros (CIDN0 HqN0). iApply bi.later_intro. iIntros "Hcg Hpc".
                     iEval (rewrite Htg054) in "Hpc".
                     iAssert (ic_loaded gfs gi cov logstart ik iinum dnl bml)
                       with "[Hdiat Hity Himaj Himin Hinl Hisz Haddrs Hind
                              Hblocks Hdlnk Hdview Hfview]" as "Hload".
                     { rewrite /ic_loaded. iExists datl.
                       iSplitR; [iPureIntro; exact Hiok |].
                       iSplitR; [iPureIntro; exact Hdok |].
                       iSplitR; [iPureIntro; exact Hddix |].
                       iSplitR; [iPureIntro; exact Hdoc |].
                       iSplitR; [iPureIntro; exact Hduq |].
                       iSplitL "Hdlnk"; [iExact "Hdlnk" |].
                       iFrame "Hdiat".
                       iSplitL "Hity Himaj Himin Hinl Hisz".
                       - rewrite /inode_meta /i_type. iFrame.
                       - iFrame. }
                     iDestruct (nx_bs3_join with "Hbs1 Hbs2") as "Hbslot".
                     (* +0x54 c.mv a0,s4 *)
                     iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x54)) Ra0 Rs4
                               V3 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                               with "Hcg Hpc []").
                     { iApply (nxi_054 with "Htext"). }
                     iIntros (CIDN1 HqN1) "Hcg Hpc". iEval (rgne) in "Hcg".
                     pose (ND1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (zero_reg : mword 64)
                              (V3 !!! Regidx Rs4))]> V3).
                     assert (HND1a0 : ND1 !!! Regidx Ra0 = ientry ik).
                     { rewrite /ND1 upd_eq. rewrite HV3s4 Hie.
                       apply add_vec_zero_l. }
                     assert (HND1regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) ND1)
                       by exact (nx_regs_caller m sp0 _ _ _ _ V3 Ra0 _
                                   ltac:(vm_compute; reflexivity) HV3regs).
                     assert (Hq56 : add_vec_int
                               (mword_of_int (NX + 0x54) : mword 64) 2
                             = mword_of_int (NX + 0x56)) by pcw.
                     iEval (rewrite Hq56) in "Hpc".
                     (* +0x56 jal ra,iunlockput *)
                     assert (Htgup : add_vec
                               (mword_of_int (NX + 0x56) : mword 64)
                               (sign_extend' 64
                                  (mword_of_int 2095978 : mword 21))
                             = mword_of_int KernelSyms.iunlockput) by pcw.
                     iApply (wp_jal_s_sconf (mword_of_int (NX + 0x56)) Rra
                               (mword_of_int 2095978 : mword 21) ND1
                               (K - 12)%nat b ltac:(nz) ltac:(rdok)
                               ltac:(vm_compute; reflexivity)
                               with "Hcg Hpc []").
                     { iApply (nxi_056 with "Htext"). }
                     iIntros (CIDN2 HqN2) "Hcg Hpc".
                     iEval (rewrite Htgup) in "Hpc".
                     pose (ND2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int
                              (mword_of_int (NX + 0x56) : mword 64) 4)]> ND1).
                     assert (HND2ra : ND2 !!! Regidx Rra
                              = add_vec_int
                                  (mword_of_int (NX + 0x56) : mword 64) 4)
                       by (rewrite /ND2; apply upd_eq).
                     assert (HND2a0 : ND2 !!! Regidx Ra0 = ientry ik)
                       by (rewrite /ND2 upd_ne; [exact HND1a0 | nz]).
                     assert (HND2regs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) ND2)
                       by exact (nx_regs_caller m sp0 _ _ _ _ ND1 Rra _
                                   ltac:(vm_compute; reflexivity) HND1regs).
                     iDestruct (cpu_own_transport CIDil CIDN2 0%nat eb
                                  (proc_addr j) b ltac:(wp_next_chain)
                                  with "Hcnt") as "Hcnt".
                     iDestruct (trap_csrs_ext_transport CIDil CIDN2 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                     iDestruct (cpu_claim_ext_transport CIDil CIDN2 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                     iDestruct (log_opS_named with "Hlog") as (enxB) "Hlog".
                     iDestruct (inode_ref_short_gen_forget with "Hkeep")
                       as "Hkeep2".
                     iApply (IUP.wp_iunlockput_gen gs j gl gu gd gk pd pav pu
                               bn g gfs gi cn gtl gilk gislk cov logstart
                               bmapstart inodestart nib size dev
                               ik (iq/2)%Qp (iq/2)%Qp gsh iinum dnl bml ncur
                               Scur wc false false enxB
                               pidv dq dqb dqs ND2 (K - 12)%nat eb b lks Vpr
                               Kiup Hik HbW ltac:(discriminate)
                               Hlg Hsize Hbmap0 Hbmapcov Hbmaplog
                               Hinos0 Hibc Hibl Hib' Hcovb Hiu Hj Hgs
                               HND2a0 Hbelow
                               with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc
                                     Hitb2 Hitbl Hesck Hireg [] Hslkk Hslkd
                                     Hdep Hidev Hiinum Hivalid Hload
                                     Hshot Hfrz [$Hkeep2 $Hru] Hbmap Hinos Hbits Hppid Hprocs
                                     Hdev Hgeom Hdlk Hbslot [] Hlog").
                     all: try lkbelow.
                     (* RULING G: a runtime caller lends the SEALED arm. *)
                     { iExact "Hropen". }
                     { iEval (cbn beta iota). iEmpIntro. }
                     iIntros (CIDup Hqup mup nup Sup wup)
                       "%Hcsup Hcg Hcnt Hextc Hclmc Hpc Hppid Hbmap Hinos
                        Hbslot %Hsup %Hwup %Hwupc %Hbdup Hlog Hisl2".
                     assert (Hpc5a : ret_pc (ND2 !!! Regidx Rra)
                              = mword_of_int (NX + 0x5a)).
                     { rewrite HND2ra. pcw. }
                     iEval (rewrite Hpc5a) in "Hpc".
                     assert (Hmupregs : nx_regs m sp0 (pa_add pv o2) ipv nb
                                (m !!! Regidx Ra1 : mword 64) mup)
                       by exact (nx_regs_cs m sp0 _ _ _ _ ND2 mup Hcsup
                                   HND2regs).
                     (* +0x5a c.li s4,0, then FALL INTO the epilogue *)
                     iApply (wp_cli_s_sconf (mword_of_int (NX + 0x5a)) Rs4
                               (mword_of_int 0 : mword 6)
                               (mword_of_int 0 : mword 64) mup (K - 12)%nat b
                               ltac:(nz) ltac:(rdok) ltac:(pcw)
                               with "Hcg Hpc []").
                     { iApply (nxi_05a with "Htext"). }
                     iIntros (CIDN3 HqN3) "Hcg Hpc".
                     pose (ND3 := <[Regidx Rs4 := regval_into_reg
                           (mword_of_int 0 : mword 64)]> mup).
                     assert (HND3s4 : ND3 !!! Regidx Rs4
                              = (mword_of_int 0 : mword 64))
                       by (rewrite /ND3; apply upd_eq).
                     assert (HND3tr : nx_tregs m sp0 ND3).
                     { pose proof (nx_tregs_of_regs m sp0 _ _ _ _ mup
                                     Hmupregs) as Hmt.
                       destruct Hmt as [U2 Uthr]. split.
                       - rewrite /ND3 upd_ne; [exact U2 | nz].
                       - intros c Hc T2' T8 T9 T18 T19 T20 T21 T22 T23 T24
                                T25 T26.
                         rewrite /ND3 upd_ne; [| dlk_xne T20].
                         exact (Uthr c Hc T2' T8 T9 T18 T19 T20 T21 T22 T23
                                  T24 T25 T26). }
                     assert (Hq5c : add_vec_int
                               (mword_of_int (NX + 0x5a) : mword 64) 2
                             = mword_of_int (NX + 0x5c)) by pcw.
                     iEval (rewrite Hq5c) in "Hpc".
                     iDestruct (cpu_own_transport CIDup CIDN3 0%nat eb (proc_addr j) b
                                  ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                     iDestruct (trap_csrs_ext_transport CIDup CIDN3 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                     iDestruct (cpu_claim_ext_transport CIDup CIDN3 eb (proc_addr j)
                                  ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                     iSpecialize ("Htail" $! CIDN3 with "[%]");
                       [wp_next_chain |].
                     iApply ("Htail" $! ND3 (mword_of_int 0 : mword 64)
                               with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                               Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11
                               Hb12").
                     * exact HND3tr.
                     * exact HND3s4.
                     * iIntros (CIDf Hsf mf) "%Hcsf %Hfa0 Hcg Hcnt Hextc Hclmc Hpc".
                       iSpecialize ("Hcont" $! CIDf with "[%]");
                         [wp_next_chain |].
                       iDestruct (iref_slots_combine 1 1 with "Hisl Hisl2")
                         as "Hisl".
                       iApply ("Hcont" $! mf nup Sup false nf'
                                 (mword_of_int 0 : mword 64) (wc || wup)%bool
                                 with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos
                                       Hppid Hcwdr Hpath Hname Hbslot
                                       [%] [%] [%] Hlog [Hisl]").
                       ** exact Hcsf.
                       ** exact (nx_sub_trans _ _ _ Hsbc Hsup).
                       ** intros Hw. destruct wc; destruct wup; simpl in Hw;
                            first [ exact (Hsup _ (HbW eq_refl))
                                  | exact (Hwup eq_refl) | discriminate ].
                       ** exact (nx_wi_spend n ncur nup wc wup false
                                   HbA HbB Hwupc (proj1 Hbdup) (proj2 Hbdup)).
                       ** iSplitR; [iPureIntro; exact Hfa0 |].
                          iExact "Hisl". }
               (* ---- +0x9e bge s8,s10 : the SHORT/LONG split ---- *)
               destruct (Nat.le_gt_cases (e - a)%nat 13%nat)
                 as [Hshort | Hlong].
               ++ (* ================ SHORT: len <= 13 ================ *)
                  iApply (wp_bge_taken_s_sconf (mword_of_int (NX + 0x9e))
                            (mword_of_int 142 : mword 13) Rs10 Rs8
                            M2 (K - 12)%nat b ltac:(nz) ltac:(nz)
                            ltac:(rgne; rgne; rewrite P24 HM2s10;
                                  exact (nx_bge13_le (e - a)%nat Hshort))
                            ltac:(rewrite Htg11c; vm_compute; reflexivity)
                            with "Hcg Hpc []").
                  { iApply (nxi_09e with "Htext"). }
                  iIntros (CIDE3 HqE3). iApply bi.later_intro. iIntros "Hcg Hpc".
                  iEval (rewrite Htg11c) in "Hpc".
                  (* +0x12c c.addiw a2,a2,0 *)
                  iApply (wp_caddiw_s_sconf (mword_of_int (NX + 0x12c)) Ra2
                            (mword_of_int 0 : mword 6) M2 (K - 12)%nat b
                            ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
                  { iApply (nxi_12c with "Htext"). }
                  iIntros (CIDS1 HqS1) "Hcg Hpc".
                  pose (S1 := <[Regidx Ra2 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (rget M2 Ra2)
                              (sign_extend' 64
                                 (sign_extend' 12 (mword_of_int 0 : mword 6))))
                           31 0))]> M2).
                  assert (HS1a2 : S1 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64)).
                  { rewrite /S1 upd_eq. rgne. rewrite HM2a2.
                    exact (nx_sextw_i6 (e - a)%nat Hea31). }
                  assert (HS1regs : nx_regs m sp0 (pa_add pv a) ipv nb
                             (m !!! Regidx Ra1 : mword 64) S1)
                    by exact (nx_regs_caller m sp0 _ _ _ _ M2 Ra2 _
                                ltac:(vm_compute; reflexivity) HM2regs).
                  assert (HS1s10 : S1 !!! Regidx Rs10
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                    by (rewrite /S1 upd_ne; [exact HM2s10 | nz]).
                  assert (HS1s1 : S1 !!! Regidx Rs1 = pa_add pv a)
                    by (rewrite /S1 upd_ne; [exact P9 | nz]).
                  assert (HS1s5 : S1 !!! Regidx Rs5 = nb)
                    by (rewrite /S1 upd_ne; [exact P21 | nz]).
                  assert (HS1s2 : S1 !!! Regidx Rs2 = pa_add pv e).
                  { rewrite /S1 upd_ne; [| nz]. rewrite /M2 upd_ne; [| nz].
                    rewrite /M1 upd_ne; [exact E5 | nz]. }
                  assert (Hq11e : add_vec_int
                            (mword_of_int (NX + 0x12c) : mword 64) 2
                          = mword_of_int (NX + 0x12e)) by pcw.
                  iEval (rewrite Hq11e) in "Hpc".
                  (* +0x12e c.mv a1,s1 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x12e)) Ra1 Rs1
                            S1 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_12e with "Htext"). }
                  iIntros (CIDS2 HqS2) "Hcg Hpc". iEval (rgne) in "Hcg".
                  pose (S2 := <[Regidx Ra1 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (S1 !!! Regidx Rs1))]> S1).
                  assert (HS2a1 : S2 !!! Regidx Ra1 = pa_add pv a).
                  { rewrite /S2 upd_eq. rewrite HS1s1. apply add_vec_zero_l. }
                  assert (HS2a2 : S2 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                    by (rewrite /S2 upd_ne; [exact HS1a2 | nz]).
                  assert (HS2s5 : S2 !!! Regidx Rs5 = nb)
                    by (rewrite /S2 upd_ne; [exact HS1s5 | nz]).
                  assert (Hq120 : add_vec_int
                            (mword_of_int (NX + 0x12e) : mword 64) 2
                          = mword_of_int (NX + 0x130)) by pcw.
                  iEval (rewrite Hq120) in "Hpc".
                  (* +0x130 c.mv a0,s5 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x130)) Ra0 Rs5
                            S2 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_130 with "Htext"). }
                  iIntros (CIDS3 HqS3) "Hcg Hpc". iEval (rgne) in "Hcg".
                  pose (S3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (S2 !!! Regidx Rs5))]> S2).
                  assert (HS3a0 : S3 !!! Regidx Ra0 = nb).
                  { rewrite /S3 upd_eq. rewrite HS2s5. apply add_vec_zero_l. }
                  assert (HS3a1 : S3 !!! Regidx Ra1 = pa_add pv a)
                    by (rewrite /S3 upd_ne; [exact HS2a1 | nz]).
                  assert (HS3a2 : S3 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                    by (rewrite /S3 upd_ne; [exact HS2a2 | nz]).
                  assert (Hq122 : add_vec_int
                            (mword_of_int (NX + 0x130) : mword 64) 2
                          = mword_of_int (NX + 0x132)) by pcw.
                  iEval (rewrite Hq122) in "Hpc".
                  (* +0x132 jal ra,memmove *)
                  assert (Htgmm : add_vec
                            (mword_of_int (NX + 0x132) : mword 64)
                            (sign_extend' 64 (mword_of_int 2085662 : mword 21))
                          = mword_of_int KernelSyms.memmove) by pcw.
                  iApply (wp_jal_s_sconf (mword_of_int (NX + 0x132)) Rra
                            (mword_of_int 2085662 : mword 21) S3
                            (K - 12)%nat b
                            ltac:(nz) ltac:(rdok)
                            ltac:(vm_compute; reflexivity)
                            with "Hcg Hpc []").
                  { iApply (nxi_132 with "Htext"). }
                  iIntros (CIDS4 HqS4) "Hcg Hpc".
                  iEval (rewrite Htgmm) in "Hpc".
                  pose (S4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int
                           (mword_of_int (NX + 0x132) : mword 64) 4)]> S3).
                  assert (HS4ra : S4 !!! Regidx Rra
                           = add_vec_int
                               (mword_of_int (NX + 0x132) : mword 64) 4)
                    by (rewrite /S4; apply upd_eq).
                  assert (HS4a0 : S4 !!! Regidx Ra0 = nb)
                    by (rewrite /S4 upd_ne; [exact HS3a0 | nz]).
                  assert (HS4a1 : S4 !!! Regidx Ra1 = pa_add pv a)
                    by (rewrite /S4 upd_ne; [exact HS3a1 | nz]).
                  assert (HS4a2 : S4 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64))
                    by (rewrite /S4 upd_ne; [exact HS3a2 | nz]).
                  (* the two byte windows the copy needs *)
                  iDestruct (nx_win_acc pv dqpv pfun a (e - a)%nat (S plen)
                               ltac:(lia) with "Hpath") as "[Hsrc Hpback]".
                  assert (Hsh14 : ((e - a) < 14)%nat) by lia.
                  iDestruct (nx_name_split_l nb nf (e - a)%nat Hsh14
                               with "Hname") as "(Hdlo & Hdat & Hdhi)".
                  iApply (MM.wp_memmove_sconf KT1 KT1 KT1 S4 (K - 12)%nat (e - a)%nat
                            (fun jj => pfun (a + jj)%nat) nf dqpv b (proc_addr j)
                            Kmm (nx_len32 (e - a)%nat Hea31) HS4a2
                            with "Hcg Htext Hpc [Hsrc] [Hdlo]").
                  { iEval (rewrite HS4a1). iExact "Hsrc". }
                  { iEval (rewrite HS4a0). iExact "Hdlo". }
                  iIntros (CIDmm Hqmm mmf) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
                  iEval (rewrite HS4a1) in "Hsrc".
                  iDestruct ("Hpback" with "Hsrc") as "Hpath".
                  iEval (rewrite HS4a0) in "Hdst".
                  assert (Hmms10 : mmf !!! Regidx Rs10
                           = (mword_of_int (Z.of_nat (e - a)) : mword 64)).
                  { rewrite (callee_saved_lookup Hcsmm Rs10
                               ltac:(vm_compute; reflexivity)).
                    rewrite /S4 upd_ne; [| nz]. rewrite /S3 upd_ne; [| nz].
                    rewrite /S2 upd_ne; [exact HS1s10 | nz]. }
                  assert (Hmms5 : mmf !!! Regidx Rs5 = nb).
                  { rewrite (callee_saved_lookup Hcsmm Rs5
                               ltac:(vm_compute; reflexivity)).
                    rewrite /S4 upd_ne; [| nz]. rewrite /S3 upd_ne; [| nz].
                    rewrite /S2 upd_ne; [exact HS1s5 | nz]. }
                  assert (Hmms2 : mmf !!! Regidx Rs2 = pa_add pv e).
                  { rewrite (callee_saved_lookup Hcsmm Rs2
                               ltac:(vm_compute; reflexivity)).
                    rewrite /S4 upd_ne; [| nz]. rewrite /S3 upd_ne; [| nz].
                    rewrite /S2 upd_ne; [exact HS1s2 | nz]. }
                  assert (Hmmregs : nx_regs m sp0 (pa_add pv a) ipv nb
                             (m !!! Regidx Ra1 : mword 64) mmf).
                  { apply (nx_regs_cs m sp0 (pa_add pv a) ipv nb _ S4 mmf
                             Hcsmm).
                    rewrite /S4 /S3 /S2.
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Rra _
                             ltac:(vm_compute; reflexivity)).
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Ra0 _
                             ltac:(vm_compute; reflexivity)).
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Ra1 _
                             ltac:(vm_compute; reflexivity)).
                    exact HS1regs. }
                  assert (Hpc126 : ret_pc (S4 !!! Regidx Rra)
                           = mword_of_int (NX + 0x136)).
                  { rewrite HS4ra. pcw. }
                  iEval (rewrite Hpc126) in "Hpc".
                  (* +0x136 c.add s10,s10,s5 : &name[len] *)
                  iApply (wp_cadd_s_sconf (mword_of_int (NX + 0x136)) Rs10 Rs5
                            mmf (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_136 with "Htext"). }
                  iIntros (CIDS5 HqS5) "Hcg Hpc".
                  iEval (rgne; rgne; rewrite Hmms10 Hmms5
                           (pa_add_comm nb (e - a)%nat)) in "Hcg".
                  pose (S5 := <[Regidx Rs10 := regval_into_reg
                                (pa_add nb (e - a)%nat)]> mmf).
                  assert (HS5s10 : S5 !!! Regidx Rs10 = pa_add nb (e - a)%nat)
                    by (rewrite /S5; apply upd_eq).
                  assert (HS5s2 : S5 !!! Regidx Rs2 = pa_add pv e)
                    by (rewrite /S5 upd_ne; [exact Hmms2 | nz]).
                  assert (HS5regs : nx_regs m sp0 (pa_add pv a) ipv nb
                             (m !!! Regidx Ra1 : mword 64) S5)
                    by exact (nx_regs_s10 m sp0 _ _ _ _ _ mmf Hmmregs).
                  assert (Hq128 : add_vec_int
                            (mword_of_int (NX + 0x136) : mword 64) 2
                          = mword_of_int (NX + 0x138)) by pcw.
                  iEval (rewrite Hq128) in "Hpc".
                  (* +0x138 sb zero,0(s10) : name[len] = 0 *)
                  iDestruct (sie_cap_gpr_x0 S5 (K - 12)%nat b (proc_addr j)
                               (mword_of_int 0 : mword 5)
                               ltac:(vm_compute; reflexivity) with "Hcg")
                    as "[%Hz0 Hcg]".
                  iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (NX + 0x138))
                            (mword_of_int 0 : mword 5) Rs10
                            (mword_of_int 0 : mword 12) S5 (K - 12)%nat
                            (nf (e - a)%nat) b
                            with "Hcg Hpc [] [Hdat]").
                  { iApply (nxi_138 with "Htext"). }
                  { iEval (rgne; rewrite HS5s10 addv_sext0). iExact "Hdat". }
                  iIntros (CIDS6 HqS6) "Hcg Hpc Hdat".
                  iEval (rgne; rgne; rewrite HS5s10 addv_sext0 Hz0 trunc8_zero)
                    in "Hdat".
                  (* ---- the name buffer's new content function ---- *)
                  set (nf1 := fun jj : nat =>
                        if decide (jj < e - a)%nat then pfun (a + jj)%nat
                        else if decide (jj = (e - a)%nat) then NUL else nf jj).
                  assert (Hn1lo : forall i : nat, (i < e - a)%nat ->
                            nf1 i = pfun (a + i)%nat).
                  { intros i Hi. rewrite /nf1.
                    rewrite decide_True; [reflexivity | exact Hi]. }
                  assert (Hn1at : nf1 (e - a)%nat = NUL).
                  { rewrite /nf1. rewrite decide_False; [| lia].
                    rewrite decide_True; [reflexivity | reflexivity]. }
                  assert (Hn1hi : forall i : nat, (e - a < i)%nat ->
                            nf1 i = nf i).
                  { intros i Hi. rewrite /nf1.
                    rewrite decide_False; [| lia].
                    rewrite decide_False; [reflexivity | lia]. }
                  iDestruct (nx_buf_fun nb (fun jj => pfun (a + jj)%nat) nf1
                               0 (e - a)%nat
                               ltac:(intros i Hi1 Hi2;
                                     symmetry; apply Hn1lo; lia)
                               with "Hdst") as "Hdlo".
                  iDestruct (nx_buf_fun nb nf nf1 (S (e - a)) (13 - (e - a))%nat
                               ltac:(intros i Hi1 Hi2;
                                     symmetry; apply Hn1hi; lia)
                               with "Hdhi") as "Hdhi".
                  iAssert (pa_add nb (e - a)%nat ↦ₘ[KT1] nf1 (e - a)%nat)%I
                    with "[Hdat]" as "Hdat".
                  { rewrite Hn1at. iExact "Hdat". }
                  iDestruct (nx_name_join nb nf1 (e - a)%nat Hsh14
                               with "Hdlo Hdat Hdhi") as "Hname".
                  (* ---- the name-buffer VIEW, both memmove shapes' bridge ---- *)
                  assert (Htk : take 14 (bview (e - a)%nat
                                  (fun i => pfun (a + i)%nat))
                                = bview (e - a)%nat
                                    (fun i => pfun (a + i)%nat))
                    by (apply nx_take_short; rewrite Hulen; lia).
                  assert (Hview : bname 14 nf1
                          = take 14 (bview (e - a)%nat
                                       (fun i => pfun (a + i)%nat))).
                  { apply (skipelem_name_view (drop off pl) _
                             (pe_skip (drop e pl)) nf1).
                    - exact (nx_nonul_drop off plen pfun Hcstr).
                    - rewrite Hskoff. exact Hske.
                    - intros jj Hjj. rewrite Htk in Hjj. rewrite Hulen in Hjj.
                      rewrite Htk. rewrite (Hn1lo jj Hjj).
                      symmetry. exact (nx_elem_lookup a e jj pfun Hjj).
                    - intro Hlt. rewrite Htk. rewrite Htk in Hlt.
                      rewrite Hulen in Hlt. rewrite Hulen. exact Hn1at. }
                  assert (Hq12c : add_vec_int
                            (mword_of_int (NX + 0x138) : mword 64) 4
                          = mword_of_int (NX + 0x13c)) by pcw.
                  iEval (rewrite Hq12c) in "Hpc".
                  (* +0x13c c.mv s1,s2 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x13c)) Rs1 Rs2
                            S5 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_13c with "Htext"). }
                  iIntros (CIDS7 HqS7) "Hcg Hpc". iEval (rgne) in "Hcg".
                  iEval (rewrite HS5s2) in "Hcg".
                  pose (S6 := <[Regidx Rs1 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (pa_add pv e))]> S5).
                  assert (HS6regs : nx_regs m sp0 (pa_add pv e) ipv nb
                             (m !!! Regidx Ra1 : mword 64) S6).
                  { rewrite /S6. rewrite add_vec_zero_l.
                    exact (nx_regs_s1 m sp0 (pa_add pv a) (pa_add pv e) ipv nb
                             _ S5 HS5regs). }
                  assert (Hq12e : add_vec_int
                            (mword_of_int (NX + 0x13c) : mword 64) 2
                          = mword_of_int (NX + 0x13e)) by pcw.
                  iEval (rewrite Hq12e) in "Hpc".
                  (* +0x13e c.j +0xae *)
                  assert (Htj0a4 : add_vec
                            (mword_of_int (NX + 0x13e) : mword 64)
                            (sign_extend' 64 (sign_extend' 21
                               (concat_vec (mword_of_int 1976 : mword 11)
                                  ('b"0"))))
                          = mword_of_int (NX + 0xae)) by pcw.
                  iApply (wp_cj_s_sconf (mword_of_int (NX + 0x13e))
                            (sign_extend' 21
                               (concat_vec (mword_of_int 1976 : mword 11)
                                  ('b"0")))
                            S6 (K - 12)%nat b
                            ltac:(rewrite Htj0a4; vm_compute; reflexivity)
                            with "Hcg Hpc []").
                  { iApply (nxi_13e with "Htext"). }
                  iIntros (CIDS8 HqS8). iApply bi.later_intro. iIntros "Hcg Hpc".
                  iEval (rewrite Htj0a4) in "Hpc".
                  iDestruct (cpu_own_transport CIDl CIDS8 0%nat eb
                               (proc_addr j) b ltac:(wp_next_chain)
                               with "Hcnt") as "Hcnt".
                  iDestruct (trap_csrs_ext_transport CIDl CIDS8 eb (proc_addr j)
                               ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                  iDestruct (cpu_claim_ext_transport CIDl CIDS8 eb (proc_addr j)
                               ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                  iSpecialize ("Hrest" $! CIDS8 with "[%]"); [wp_next_chain |].
                  iApply ("Hrest" $! S6 nf1 with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                            Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                            Hip Hisl Hbmap Hinos Hppid Hcwdr
                            Hpath Hname Hbslot Hlog").
                  ** exact HS6regs.
                  ** exact Hview.
               ++ (* ================ LONG: 14 <= len ================= *)
                  iApply (wp_bge_fall_s_sconf (mword_of_int (NX + 0x9e))
                            (mword_of_int 142 : mword 13) Rs10 Rs8
                            M2 (K - 12)%nat b ltac:(nz) ltac:(nz)
                            ltac:(rgne; rgne; rewrite P24 HM2s10;
                                  exact (nx_bge13_gt (e - a)%nat Hlong Hea31))
                            with "Hcg Hpc []").
                  { iApply (nxi_09e with "Htext"). }
                  iIntros (CIDE3 HqE3) "Hcg Hpc".
                  assert (Hq098 : add_vec_int
                            (mword_of_int (NX + 0x9e) : mword 64) 4
                          = mword_of_int (NX + 0xa2)) by pcw.
                  iEval (rewrite Hq098) in "Hpc".
                  (* +0xa2 c.mv a2,s9 : the copy length is 14 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xa2)) Ra2 Rs9
                            M2 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_0a2 with "Htext"). }
                  iIntros (CIDL1 HqL1) "Hcg Hpc". iEval (rgne) in "Hcg".
                  pose (T1 := <[Regidx Ra2 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (M2 !!! Regidx Rs9))]> M2).
                  assert (HT1a2 : T1 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat 14) : mword 64)).
                  { rewrite /T1 upd_eq. rewrite P25 add_vec_zero_l.
                    change (Z.of_nat 14) with 14%Z. reflexivity. }
                  assert (HT1regs : nx_regs m sp0 (pa_add pv a) ipv nb
                             (m !!! Regidx Ra1 : mword 64) T1)
                    by exact (nx_regs_caller m sp0 _ _ _ _ M2 Ra2 _
                                ltac:(vm_compute; reflexivity) HM2regs).
                  assert (HT1s1 : T1 !!! Regidx Rs1 = pa_add pv a)
                    by (rewrite /T1 upd_ne; [exact P9 | nz]).
                  assert (HT1s5 : T1 !!! Regidx Rs5 = nb)
                    by (rewrite /T1 upd_ne; [exact P21 | nz]).
                  assert (HT1s2 : T1 !!! Regidx Rs2 = pa_add pv e).
                  { rewrite /T1 upd_ne; [| nz]. rewrite /M2 upd_ne; [| nz].
                    rewrite /M1 upd_ne; [exact E5 | nz]. }
                  assert (Hq09a : add_vec_int
                            (mword_of_int (NX + 0xa2) : mword 64) 2
                          = mword_of_int (NX + 0xa4)) by pcw.
                  iEval (rewrite Hq09a) in "Hpc".
                  (* +0xa4 c.mv a1,s1 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xa4)) Ra1 Rs1
                            T1 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_0a4 with "Htext"). }
                  iIntros (CIDL2 HqL2) "Hcg Hpc". iEval (rgne) in "Hcg".
                  pose (T2 := <[Regidx Ra1 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (T1 !!! Regidx Rs1))]> T1).
                  assert (HT2a1 : T2 !!! Regidx Ra1 = pa_add pv a).
                  { rewrite /T2 upd_eq. rewrite HT1s1. apply add_vec_zero_l. }
                  assert (HT2a2 : T2 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat 14) : mword 64))
                    by (rewrite /T2 upd_ne; [exact HT1a2 | nz]).
                  assert (HT2s5 : T2 !!! Regidx Rs5 = nb)
                    by (rewrite /T2 upd_ne; [exact HT1s5 | nz]).
                  assert (Hq09c : add_vec_int
                            (mword_of_int (NX + 0xa4) : mword 64) 2
                          = mword_of_int (NX + 0xa6)) by pcw.
                  iEval (rewrite Hq09c) in "Hpc".
                  (* +0xa6 c.mv a0,s5 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xa6)) Ra0 Rs5
                            T2 (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_0a6 with "Htext"). }
                  iIntros (CIDL3 HqL3) "Hcg Hpc". iEval (rgne) in "Hcg".
                  pose (T3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64)
                           (T2 !!! Regidx Rs5))]> T2).
                  assert (HT3a0 : T3 !!! Regidx Ra0 = nb).
                  { rewrite /T3 upd_eq. rewrite HT2s5. apply add_vec_zero_l. }
                  assert (HT3a1 : T3 !!! Regidx Ra1 = pa_add pv a)
                    by (rewrite /T3 upd_ne; [exact HT2a1 | nz]).
                  assert (HT3a2 : T3 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat 14) : mword 64))
                    by (rewrite /T3 upd_ne; [exact HT2a2 | nz]).
                  assert (Hq09e : add_vec_int
                            (mword_of_int (NX + 0xa6) : mword 64) 2
                          = mword_of_int (NX + 0xa8)) by pcw.
                  iEval (rewrite Hq09e) in "Hpc".
                  (* +0xa8 jal ra,memmove -- FOURTEEN bytes, no terminator *)
                  assert (Htgmm : add_vec
                            (mword_of_int (NX + 0xa8) : mword 64)
                            (sign_extend' 64 (mword_of_int 2085800 : mword 21))
                          = mword_of_int KernelSyms.memmove) by pcw.
                  iApply (wp_jal_s_sconf (mword_of_int (NX + 0xa8)) Rra
                            (mword_of_int 2085800 : mword 21) T3
                            (K - 12)%nat b
                            ltac:(nz) ltac:(rdok)
                            ltac:(vm_compute; reflexivity)
                            with "Hcg Hpc []").
                  { iApply (nxi_0a8 with "Htext"). }
                  iIntros (CIDL4 HqL4) "Hcg Hpc".
                  iEval (rewrite Htgmm) in "Hpc".
                  pose (T4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int
                           (mword_of_int (NX + 0xa8) : mword 64) 4)]> T3).
                  assert (HT4ra : T4 !!! Regidx Rra
                           = add_vec_int
                               (mword_of_int (NX + 0xa8) : mword 64) 4)
                    by (rewrite /T4; apply upd_eq).
                  assert (HT4a0 : T4 !!! Regidx Ra0 = nb)
                    by (rewrite /T4 upd_ne; [exact HT3a0 | nz]).
                  assert (HT4a1 : T4 !!! Regidx Ra1 = pa_add pv a)
                    by (rewrite /T4 upd_ne; [exact HT3a1 | nz]).
                  assert (HT4a2 : T4 !!! Regidx Ra2
                           = (mword_of_int (Z.of_nat 14) : mword 64))
                    by (rewrite /T4 upd_ne; [exact HT3a2 | nz]).
                  iDestruct (nx_win_acc pv dqpv pfun a 14%nat (S plen)
                               ltac:(lia) with "Hpath") as "[Hsrc Hpback]".
                  iApply (MM.wp_memmove_sconf KT1 KT1 KT1 T4 (K - 12)%nat 14%nat
                            (fun jj => pfun (a + jj)%nat) nf dqpv b (proc_addr j)
                            Kmm (nx_len32 14%nat ltac:(vm_compute; reflexivity))
                            HT4a2
                            with "Hcg Htext Hpc [Hsrc] [Hname]").
                  { iEval (rewrite HT4a1). iExact "Hsrc". }
                  { iEval (rewrite HT4a0). iExact "Hname". }
                  iIntros (CIDmm Hqmm mmf) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
                  iEval (rewrite HT4a1) in "Hsrc".
                  iDestruct ("Hpback" with "Hsrc") as "Hpath".
                  iEval (rewrite HT4a0) in "Hdst".
                  assert (Hmms2 : mmf !!! Regidx Rs2 = pa_add pv e).
                  { rewrite (callee_saved_lookup Hcsmm Rs2
                               ltac:(vm_compute; reflexivity)).
                    rewrite /T4 upd_ne; [| nz]. rewrite /T3 upd_ne; [| nz].
                    rewrite /T2 upd_ne; [exact HT1s2 | nz]. }
                  assert (Hmmregs : nx_regs m sp0 (pa_add pv a) ipv nb
                             (m !!! Regidx Ra1 : mword 64) mmf).
                  { apply (nx_regs_cs m sp0 (pa_add pv a) ipv nb _ T4 mmf
                             Hcsmm).
                    rewrite /T4 /T3 /T2.
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Rra _
                             ltac:(vm_compute; reflexivity)).
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Ra0 _
                             ltac:(vm_compute; reflexivity)).
                    apply (nx_regs_caller m sp0 _ _ _ _ _ Ra1 _
                             ltac:(vm_compute; reflexivity)).
                    exact HT1regs. }
                  assert (Hpc0a2 : ret_pc (T4 !!! Regidx Rra)
                           = mword_of_int (NX + 0xac)).
                  { rewrite HT4ra. pcw. }
                  iEval (rewrite Hpc0a2) in "Hpc".
                  (* ---- the name-buffer VIEW on the UNTERMINATED copy ---- *)
                  assert (Htk14 : length (take 14 (bview (e - a)%nat
                                    (fun i => pfun (a + i)%nat))) = 14%nat)
                    by (apply nx_take_long_len; rewrite Hulen; lia).
                  assert (Hview : bname 14 (fun jj => pfun (a + jj)%nat)
                          = take 14 (bview (e - a)%nat
                                       (fun i => pfun (a + i)%nat))).
                  { apply (skipelem_name_view (drop off pl) _
                             (pe_skip (drop e pl)) (fun jj => pfun (a + jj)%nat)).
                    - exact (nx_nonul_drop off plen pfun Hcstr).
                    - rewrite Hskoff. exact Hske.
                    - intros jj Hjj. rewrite Htk14 in Hjj.
                      rewrite (nx_take14_lookup _ jj Hjj).
                      symmetry.
                      exact (nx_elem_lookup a e jj pfun ltac:(lia)).
                    - intro Hlt. exfalso. rewrite Htk14 in Hlt. lia. }
                  (* +0xac c.mv s1,s2 *)
                  iApply (wp_cmv_s_sconf (mword_of_int (NX + 0xac)) Rs1 Rs2
                            mmf (K - 12)%nat b ltac:(nz) ltac:(rdok)
                            with "Hcg Hpc []").
                  { iApply (nxi_0ac with "Htext"). }
                  iIntros (CIDL5 HqL5) "Hcg Hpc". iEval (rgne) in "Hcg".
                  iEval (rewrite Hmms2) in "Hcg".
                  pose (T5 := <[Regidx Rs1 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (pa_add pv e))]> mmf).
                  assert (HT5regs : nx_regs m sp0 (pa_add pv e) ipv nb
                             (m !!! Regidx Ra1 : mword 64) T5).
                  { rewrite /T5. rewrite add_vec_zero_l.
                    exact (nx_regs_s1 m sp0 (pa_add pv a) (pa_add pv e) ipv nb
                             _ mmf Hmmregs). }
                  assert (Hq0a4 : add_vec_int
                            (mword_of_int (NX + 0xac) : mword 64) 2
                          = mword_of_int (NX + 0xae)) by pcw.
                  iEval (rewrite Hq0a4) in "Hpc".
                  iDestruct (cpu_own_transport CIDl CIDL5 0%nat eb
                               (proc_addr j) b ltac:(wp_next_chain)
                               with "Hcnt") as "Hcnt".
                  iDestruct (trap_csrs_ext_transport CIDl CIDL5 eb (proc_addr j)
                               ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
                  iDestruct (cpu_claim_ext_transport CIDl CIDL5 eb (proc_addr j)
                               ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
                  iSpecialize ("Hrest" $! CIDL5 with "[%]"); [wp_next_chain |].
                  iApply ("Hrest" $! T5 (fun jj => pfun (a + jj)%nat)
                            with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc
                            Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                            Hip Hisl Hbmap Hinos Hppid Hcwdr
                            Hpath Hdst Hbslot Hlog").
                  ** exact HT5regs.
                  ** exact Hview. }
    (* ===== +0x1c c.mv s1,a0 : s1 := path ===== *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = pv)
      by exact (HR2c Ra0 ltac:(nz) ltac:(nz)).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64))
      by exact (HR2c Ra1 ltac:(nz) ltac:(nz)).
    assert (HR2a2 : R2 !!! Regidx Ra2 = nb)
      by exact (HR2c Ra2 ltac:(nz) ltac:(nz)).
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1c)) Rs1 Ra0 R2 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (nxi_01c with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = pv).
    { rewrite /R3 upd_eq. rewrite HR2a0. apply add_vec_zero_l. }
    assert (Hpp01e : add_vec_int (mword_of_int (NX + 0x1c) : mword 64) 2
                     = mword_of_int (NX + 0x1e)) by pcw.
    iEval (rewrite Hpp01e) in "Hpc".
    (* ===== +0x1e c.mv s6,a1 : s6 := nameiparent ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1e)) Rs6 Ra1 R3 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (nxi_01e with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R4 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra1))]> R3).
    assert (HR3a1 : R3 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR4s6 : R4 !!! Regidx Rs6 = (m !!! Regidx Ra1 : mword 64)).
    { rewrite /R4 upd_eq. rewrite HR3a1. apply add_vec_zero_l. }
    assert (Hpp020 : add_vec_int (mword_of_int (NX + 0x1e) : mword 64) 2
                     = mword_of_int (NX + 0x20)) by pcw.
    iEval (rewrite Hpp020) in "Hpc".
    (* ===== +0x20 c.mv s5,a2 : s5 := name ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x20)) Rs5 Ra2 R4 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (nxi_020 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
    pose (R5 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra2))]> R4).
    assert (HR4a2 : R4 !!! Regidx Ra2 = nb).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [exact HR2a2 | nz]. }
    assert (HR5s5 : R5 !!! Regidx Rs5 = nb).
    { rewrite /R5 upd_eq. rewrite HR4a2. apply add_vec_zero_l. }
    assert (Hpp022 : add_vec_int (mword_of_int (NX + 0x20) : mword 64) 2
                     = mword_of_int (NX + 0x22)) by pcw.
    iEval (rewrite Hpp022) in "Hpc".
    (* ===== +0x22 lbu a4,0(a0) : the FIRST path byte ===== *)
    assert (HR5a0 : R5 !!! Regidx Ra0 = pv).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2a0 | nz]. }
    iDestruct (nx_buf_acc pv dqpv pfun (S plen) 0 ltac:(lia) with "Hpath")
      as "[Hp0 Hpback]".
    iEval (rewrite pa_add_0) in "Hp0".
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (NX + 0x22)) Ra4 Ra0
              (mword_of_int 0 : mword 12) R5 (K - 12)%nat (pfun 0%nat) b (dqm:=dqpv)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hp0]").
    { iApply (nxi_022 with "Htext"). }
    { iEval (rgne; rewrite HR5a0 addv_sext0). iExact "Hp0". }
    iIntros (CID18 Hq18) "Hcg Hpc Hp0".
    iEval (rgne; rewrite HR5a0 addv_sext0) in "Hp0".
    iEval (rewrite -(pa_add_0 pv)) in "Hp0".
    iDestruct ("Hpback" with "Hp0") as "Hpath".
    pose (R6 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (pfun 0%nat : mword 8))]> R5).
    assert (HR6a4 : R6 !!! Regidx Ra4
                    = (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64))
      by (rewrite /R6; apply upd_eq).
    assert (Hpp026 : add_vec_int (mword_of_int (NX + 0x22) : mword 64) 4
                     = mword_of_int (NX + 0x26)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ===== +0x26 li a5,47 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (NX + 0x26)) Ra5
              (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
              R6 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (nxi_026 with "Htext"). }
    iIntros (CID19 Hq19) "Hcg Hpc".
    pose (R7 := <[Regidx Ra5 := regval_into_reg (mword_of_int 47 : mword 64)]> R6).
    assert (HR7a5 : R7 !!! Regidx Ra5 = (mword_of_int 47 : mword 64))
      by (rewrite /R7; apply upd_eq).
    assert (HR7a4 : R7 !!! Regidx Ra4
                    = (zero_extend' 64 (pfun 0%nat : mword 8) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6a4 | nz]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = pv).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [exact HR3s1 | nz]. }
    assert (HR7s5 : R7 !!! Regidx Rs5 = nb).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [exact HR5s5 | nz]. }
    assert (HR7s6 : R7 !!! Regidx Rs6 = (m !!! Regidx Ra1 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4s6 | nz]. }
    assert (HR7s0 : R7 !!! Regidx Rs0 = sp0).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2s0 | nz]. }
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2sp | nz]. }
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (HR7o : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
              c <> Rs9 -> c <> Rs10 ->
              R7 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
      rewrite /R7 upd_ne; [| dlk_rne2 Hcsa5 Hc].
      rewrite /R6 upd_ne; [| dlk_rne2 Hcsa4 Hc].
      rewrite /R5 upd_ne; [| dlk_xne N21].
      rewrite /R4 upd_ne; [| dlk_xne N22].
      rewrite /R3 upd_ne; [| dlk_xne N9].
      exact (HR2o c Hc N2 N8). }
    assert (Hpp02a : add_vec_int (mword_of_int (NX + 0x26) : mword 64) 4
                     = mword_of_int (NX + 0x2a)) by pcw.
    iEval (rewrite Hpp02a) in "Hpc".
    (* the ledger: iget / idup want ONE unit, the walk keeps the other *)
    assert (Hsl2 : (2 = 1 + 1)%nat) by reflexivity.
    iEval (rewrite Hsl2) in "Hislot".
    iDestruct (iref_slots_split 1 1 with "Hislot") as "[Hisl1 Hisl2]".
    (* ================================================================= *)
    (*  +0x2a beq a4,a5 : THE ARM SPLIT                                   *)
    (* ================================================================= *)
    assert (Htgt048 : add_vec (mword_of_int (NX + 0x2a) : mword 64)
              (sign_extend' 64 (mword_of_int 30 : mword 13))
              = mword_of_int (NX + 0x48)) by pcw.
    destruct (decide (pfun 0%nat = SLASH)) as [Hsl0 | Hsl0].
    + (* ---------------- THE ABSOLUTE ARM: iget(ROOTDEV, ROOTINO) ------- *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0x2a))
                (mword_of_int 30 : mword 13) Ra5 Ra4 R7 (K - 12)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR7a4 HR7a5; exact (nx_slash_eq _ Hsl0))
                ltac:(rewrite Htgt048; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_02a with "Htext"). }
      iIntros (CID20 Hq20). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt048) in "Hpc".
      (* +0x48 c.li a1,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x48)) Ra1 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) R7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_048 with "Htext"). }
      iIntros (CID21 Hq21) "Hcg Hpc".
      pose (A1 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> R7).
      assert (HA1a1 : A1 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /A1; apply upd_eq).
      assert (Hpp04a : add_vec_int (mword_of_int (NX + 0x48) : mword 64) 2
                       = mword_of_int (NX + 0x4a)) by pcw.
      iEval (rewrite Hpp04a) in "Hpc".
      (* +0x4a c.mv a0,a1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x4a)) Ra0 Ra1 A1 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (nxi_04a with "Htext"). }
      iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (A2 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (A1 !!! Regidx Ra1))]> A1).
      assert (HA2a0 : A2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
      { rewrite /A2 upd_eq. rewrite HA1a1. apply add_vec_zero_l. }
      assert (HA2a1 : A2 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /A2 upd_ne; [exact HA1a1 | nz]).
      assert (Hpp04c : add_vec_int (mword_of_int (NX + 0x4a) : mword 64) 2
                       = mword_of_int (NX + 0x4c)) by pcw.
      iEval (rewrite Hpp04c) in "Hpc".
      (* +0x4c jal ra,iget *)
      assert (Htgtig : add_vec (mword_of_int (NX + 0x4c) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094466 : mword 21))
                       = mword_of_int KernelSyms.iget) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x4c)) Rra
                (mword_of_int 2094466 : mword 21) A2 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_04c with "Htext"). }
      iIntros (CID23 Hq23) "Hcg Hpc".
      iEval (rewrite Htgtig) in "Hpc".
      pose (A3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (NX + 0x4c) : mword 64) 4)]> A2).
      assert (HA3ra : A3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (NX + 0x4c) : mword 64) 4)
        by (rewrite /A3; apply upd_eq).
      assert (HA3a0 : A3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
      { rewrite /A3 upd_ne; [| nz]. rewrite HA2a0 Hroot.
        unfold ROOTDEV. pcw. }
      assert (HA3a1 : A3 !!! Regidx Ra1 = (sign_extend' 64 ROOTINO : mword 64)).
      { rewrite /A3 upd_ne; [| nz]. rewrite HA2a1. unfold ROOTINO. pcw. }
      assert (Hrino : bv_unsigned ROOTINO < 16 * Z.of_nat nib).
      { unfold ROOTINO.
        assert (Hu : bv_unsigned (mword_of_int 1 : mword 32) = 1)
          by (vm_compute; reflexivity).
        rewrite Hu. assert (Hnz : 1 <= Z.of_nat nib) by lia. lia. }
      iDestruct (cpu_own_transport CID CID23 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CID23 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CID23 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID23)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* THE LICENCE (increment C'-lite, fs-fragments.md §7.1), licence (f).
         namex's FIRST iget is the one nothing looked up: an absolute path
         starts at the root and the walk has read no directory yet.  What
         founds it is the landed ROOT CLAUSE -- [InodeRegion.ireg_root_ok]
         is (L1) MADE STRICT at [ireg_root], so the root's count is at
         least one and (L3) gives it a nonzero type
         ([IgetLic.iname_root_alloc]).  The licence is PURE: the evidence
         lives in the region's invariant, not in this walk's hands, which
         is why it costs the walk nothing. *)
      iAssert (iname gi gfs inodestart ROOTINO RootL) as "Hlicr";
        [rewrite /iname; iPureIntro; exact ireg_root_ROOTINO |].
      iApply (IG.wp_iget_sconf gtl cn gfs gi cov logstart inodestart nib dev ROOTINO
                RootL
                A3 0%nat eb (proc_addr j) (K - 12)%nat b lks
                Kig ltac:(vm_compute; reflexivity)
                Hrino HA3a0 HA3a1 ltac:(lkbelow)
                with "Hcg Hcnt Htext Hkd Hpc Hitb2 Hitbl Hesc Hireg Hpenv Hisl1
                      Hlicr").
      all: try lkbelow.
      iIntros (CIDig Hqig mig kig qig) "Hcg Hcnt Hpc %Higp [Href Hru] _".
      destruct Higp as (Hcsig & Hkig & Higa0).
      assert (Hpc050 : ret_pc (A3 !!! Regidx Rra) = mword_of_int (NX + 0x50)).
      { rewrite HA3ra. pcw. }
      iEval (rewrite Hpc050) in "Hpc".
      (* +0x50 c.mv s4,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x50)) Rs4 Ra0 mig (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (nxi_050 with "Htext"). }
      iIntros (CIDA1 HqA1) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (A4 := <[Regidx Rs4 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mig !!! Regidx Ra0))]> mig).
      assert (HA4s4 : A4 !!! Regidx Rs4 = ientry kig).
      { rewrite /A4 upd_eq. rewrite Higa0. apply add_vec_zero_l. }
      assert (Hpp052 : add_vec_int (mword_of_int (NX + 0x50) : mword 64) 2
                       = mword_of_int (NX + 0x52)) by pcw.
      iEval (rewrite Hpp052) in "Hpc".
      (* +0x52 c.j +0x3c *)
      assert (Htgt03c : add_vec (mword_of_int (NX + 0x52) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
                = mword_of_int (NX + 0x3c)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (NX + 0x52))
                (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
                A4 (K - 12)%nat b
                ltac:(rewrite Htgt03c; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_052 with "Htext"). }
      iIntros (CIDA2 HqA2). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt03c) in "Hpc".
      (* ---- the register facts iget's [callee_saved] carries over ---- *)
      assert (HA4sp : A4 !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite /A4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsig csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
        rewrite /A1 upd_ne; [exact HR7sp | nz]. }
      assert (HA4s0 : A4 !!! Regidx Rs0 = sp0).
      { rewrite /A4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsig Rs0 ltac:(vm_compute; reflexivity)).
        rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
        rewrite /A1 upd_ne; [exact HR7s0 | nz]. }
      assert (HA4s1 : A4 !!! Regidx Rs1 = pv).
      { rewrite /A4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsig Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
        rewrite /A1 upd_ne; [exact HR7s1 | nz]. }
      assert (HA4s5 : A4 !!! Regidx Rs5 = nb).
      { rewrite /A4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsig Rs5 ltac:(vm_compute; reflexivity)).
        rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
        rewrite /A1 upd_ne; [exact HR7s5 | nz]. }
      assert (HA4s6 : A4 !!! Regidx Rs6 = (m !!! Regidx Ra1 : mword 64)).
      { rewrite /A4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsig Rs6 ltac:(vm_compute; reflexivity)).
        rewrite /A3 upd_ne; [| nz]. rewrite /A2 upd_ne; [| nz].
        rewrite /A1 upd_ne; [exact HR7s6 | nz]. }
      assert (HA4o : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
                c <> Rs9 -> c <> Rs10 ->
                A4 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
        rewrite /A4 upd_ne; [| dlk_xne N20].
        rewrite (callee_saved_lookup Hcsig c Hc).
        rewrite /A3 upd_ne; [| dlk_rne2 Hcsra Hc].
        rewrite /A2 upd_ne; [| dlk_rne2 Hcsa0 Hc].
        assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
        rewrite /A1 upd_ne;
          [ exact (HR7o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
          | dlk_rne2 Hcsa1 Hc ]. }
      (* the walk's starting reference, in the loop's currency *)
      iAssert (inode_held (ientry kig)) with "[Href Hru]" as "Hip".
      { rewrite /inode_held. iExists kig, qig, ROOTINO.
        iSplitR; [done |]. iSplitR; [iPureIntro; exact Hkig |].
        iSplitR; [iPureIntro; rewrite -Hnib; exact Hrino |].
        iFrame "Hru". rewrite -Hdev. iExact "Href". }
      (* ===== +0x3c .. +0x46 : the four constants, then [c.j +0xf4] ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (NX + 0x3c)) Rs3
                (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
                A4 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (nxi_03c with "Htext"). }
      iIntros (CIDK1 HqK1) "Hcg Hpc".
      pose (A5 := <[Regidx Rs3 := regval_into_reg (mword_of_int 47 : mword 64)]> A4).
      assert (HpA040 : add_vec_int (mword_of_int (NX + 0x3c) : mword 64) 4
                       = mword_of_int (NX + 0x40)) by pcw.
      iEval (rewrite HpA040) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x40)) Rs8 (mword_of_int 13 : mword 6)
                (mword_of_int 13 : mword 64) A5 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_040 with "Htext"). }
      iIntros (CIDK2 HqK2) "Hcg Hpc".
      pose (A6 := <[Regidx Rs8 := regval_into_reg (mword_of_int 13 : mword 64)]> A5).
      assert (HpA042 : add_vec_int (mword_of_int (NX + 0x40) : mword 64) 2
                       = mword_of_int (NX + 0x42)) by pcw.
      iEval (rewrite HpA042) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x42)) Rs9 (mword_of_int 14 : mword 6)
                (mword_of_int 14 : mword 64) A6 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_042 with "Htext"). }
      iIntros (CIDK3 HqK3) "Hcg Hpc".
      pose (A7 := <[Regidx Rs9 := regval_into_reg (mword_of_int 14 : mword 64)]> A6).
      assert (HpA044 : add_vec_int (mword_of_int (NX + 0x42) : mword 64) 2
                       = mword_of_int (NX + 0x44)) by pcw.
      iEval (rewrite HpA044) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x44)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) A7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_044 with "Htext"). }
      iIntros (CIDK4 HqK4) "Hcg Hpc".
      pose (A8 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> A7).
      assert (HpA046 : add_vec_int (mword_of_int (NX + 0x44) : mword 64) 2
                       = mword_of_int (NX + 0x46)) by pcw.
      iEval (rewrite HpA046) in "Hpc".
      assert (HAregs : nx_regs m sp0 pv (ientry kig) nb
                           (m !!! Regidx Ra1 : mword 64) A8).
      { unfold nx_regs. split_and!.
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4sp | nz].
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s0 | nz].
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s1 | nz].
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_eq. reflexivity.
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s4 | nz].
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s5 | nz].
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_ne; [| nz]. rewrite /A5 upd_ne; [exact HA4s6 | nz].
        - rewrite /A8 upd_eq. reflexivity.
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_ne; [| nz].
          rewrite /A6 upd_eq. reflexivity.
        - rewrite /A8 upd_ne; [| nz]. rewrite /A7 upd_eq. reflexivity.
        - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
          rewrite /A8 upd_ne; [| dlk_xne N23].
          rewrite /A7 upd_ne; [| dlk_xne N25].
          rewrite /A6 upd_ne; [| dlk_xne N24].
          rewrite /A5 upd_ne; [| dlk_xne N19].
          exact (HA4o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26). }
      (* +0x46 c.j +0xf4 : into the walk *)
      assert (HtgtA0e4 : add_vec (mword_of_int (NX + 0x46) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 87 : mword 11) ('b"0"))))
                = mword_of_int (NX + 0xf4)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (NX + 0x46))
                (sign_extend' 21 (concat_vec (mword_of_int 87 : mword 11) ('b"0")))
                A8 (K - 12)%nat b
                ltac:(rewrite HtgtA0e4; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_046 with "Htext"). }
      iIntros (CIDK5 HqK5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite HtgtA0e4) in "Hpc".
      (* ---- ENTER THE WALK at off = 0, es0 = [], ncur = n ---- *)
      iDestruct (cpu_own_transport CIDig CIDK5 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* iget does not thread the complement, so its span starts at CID23 --
         where the pair was last put -- not at iget's return hart. *)
      iDestruct (trap_csrs_ext_transport CID23 CIDK5 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID23 CIDK5 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iDestruct (wp_next_shift (b := true) (CIDa := CID23) (CIDb := CIDK5)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iSpecialize ("Hloop" $! (S plen) CIDK5 with "[%]"); [wp_next_chain |].
      iApply ("Hloop" $! 0%nat (ientry kig) A8 n Sb [] nfun false
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hextc Hclmc Hpc
                      Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                      Hip Hisl2 Hbmap Hinos Hppid Hcwdr Hpath
                      Hname Hbslot Hlog Hcont").
      - lia.
      - lia.
      - rewrite drop_0. reflexivity.
      (* the budget invariant at entry: nothing paid yet *)
      - exact (nx_wi_init n).
      - lia.
      - exact (nx_wi_need0 _ _ Hbud).
      - rewrite drop_0. exact (nx_wi_need _ _ Hbud).
      - discriminate.
      (* entering the loop, the running set IS the caller's *)
      - reflexivity.
      - rewrite pa_add_0. exact HAregs.
    + (* ---------------- THE RELATIVE ARM: idup(myproc()->cwd) ---------- *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0x2a))
                (mword_of_int 30 : mword 13) Ra5 Ra4 R7 (K - 12)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR7a4 HR7a5; exact (nx_slash_ne _ Hsl0))
                with "Hcg Hpc []").
      { iApply (nxi_02a with "Htext"). }
      iIntros (CID20 Hq20) "Hcg Hpc".
      assert (Hpp02e : add_vec_int (mword_of_int (NX + 0x2a) : mword 64) 4
                       = mword_of_int (NX + 0x2e)) by pcw.
      iEval (rewrite Hpp02e) in "Hpc".
      (* +0x2e jal ra,myproc *)
      assert (Htgtmp : add_vec (mword_of_int (NX + 0x2e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2088994 : mword 21))
                       = mword_of_int KernelSyms.myproc) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x2e)) Rra
                (mword_of_int 2088994 : mword 21) R7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_02e with "Htext"). }
      iIntros (CID21 Hq21) "Hcg Hpc".
      iEval (rewrite Htgtmp) in "Hpc".
      pose (B1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (NX + 0x2e) : mword 64) 4)]> R7).
      assert (HB1ra : B1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (NX + 0x2e) : mword 64) 4)
        by (rewrite /B1; apply upd_eq).
      iDestruct (cpu_own_transport CID CID21 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CID21 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CID21 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID21)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (MP.wp_myproc_sconf B1 (K - 12)%nat 0%nat eb (proc_addr j) b _
                ltac:(vm_compute; reflexivity) Kmp
                with "Hcg Hcnt Htext Hpc").
      iIntros (CIDmp Hqmp msv mf1) "%Hmsf Hcg Hcnt Hpc %Hmpp".
      destruct Hmpp as [Hcsmp Hmpa0].
      assert (Hpc032 : ret_pc (B1 !!! Regidx Rra) = mword_of_int (NX + 0x32)).
      { rewrite HB1ra. pcw. }
      iEval (rewrite Hpc032) in "Hpc".
      (* +0x32 ld a0,336(a0) : a0 := p->cwd
         [p->cwd] IS ONE OF THE BLOCK'S OWN CELLS, so it is BORROWED for this
         one load and handed straight back on the next line -- the contract
         passes [proc_priv_bare] around and never a loose share of the cell.
         The value the load produces is the block's own [pv_cwd Vpr]. *)
      iDestruct (proc_priv_bare_cwd (proc_addr j) pidv Vpr with "Hppid")
        as "[Hcwdc Hcwdbk]".
      iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (NX + 0x32)) Ra0 Ra0
                (mword_of_int 336 : mword 12) mf1 (K - 12)%nat (pv_cwd Vpr) b
                (dqm := DfracOwn 1)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [Hcwdc]").
      { iApply (nxi_032 with "Htext"). }
      { iEval (rgne; rewrite Hmpa0 p_cwd_sext). iExact "Hcwdc". }
      iIntros (CID22 Hq22) "Hcg Hpc Hcwdc".
      iEval (rgne; rewrite Hmpa0 p_cwd_sext) in "Hcwdc".
      iDestruct ("Hcwdbk" $! (pv_cwd Vpr) with "Hcwdc") as "Hppid".
      rewrite upd_cwd_id.
      pose (B2 := <[Regidx Ra0 := regval_into_reg (pv_cwd Vpr)]> mf1).
      assert (HB2a0 : B2 !!! Regidx Ra0 = pv_cwd Vpr)
        by (rewrite /B2; apply upd_eq).
      assert (Hpp036 : add_vec_int (mword_of_int (NX + 0x32) : mword 64) 4
                       = mword_of_int (NX + 0x36)) by pcw.
      iEval (rewrite Hpp036) in "Hpc".
      (* ---- THE SHED: the cwd reference lends a share to idup ---- *)
      (* SIMP-2: the package travels WHOLE.  What is still read off it is
         the SLOT (the pointer [a0] is set to) and the two pure facts; the
         carve and the gather that used to bracket the call are inside
         [SpecIdup] now, and the cwd's fraction is untouched either way. *)
      iDestruct "Hcwdr" as (ck cq cinum) "(%Hcwde & %Hckl & %Hcinb & Hcrefp)".
      iAssert (inode_held (ientry ck)) with "[Hcrefp]" as "Hcheld".
      { iExists ck, cq, cinum.
        iSplitR; [done |]. iSplitR; [iPureIntro; exact Hckl |].
        iSplitR; [iPureIntro; exact Hcinb |]. iExact "Hcrefp". }
      (* +0x36 jal ra,idup *)
      assert (Htgtid : add_vec (mword_of_int (NX + 0x36) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095360 : mword 21))
                       = mword_of_int KernelSyms.idup) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x36)) Rra
                (mword_of_int 2095360 : mword 21) B2 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_036 with "Htext"). }
      iIntros (CID23 Hq23) "Hcg Hpc".
      iEval (rewrite Htgtid) in "Hpc".
      pose (B3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (NX + 0x36) : mword 64) 4)]> B2).
      assert (HB3ra : B3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (NX + 0x36) : mword 64) 4)
        by (rewrite /B3; apply upd_eq).
      assert (HB3a0 : B3 !!! Regidx Ra0 = ientry ck).
      { rewrite /B3 upd_ne; [| nz]. rewrite HB2a0. exact Hcwde. }
      (* the relative arm: myproc returned [cpu_own] at CIDmp, and it does not
         thread the complement, so the pair is still at CID21. *)
      iDestruct (cpu_own_transport CIDmp CID23 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID21 CID23 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID21 CID23 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID23)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* idup's contract widened in increment IVe (iclaim-ledger.md §3.19):
         its [ref++] is a ledger move, so it takes the region handle this
         walk already carries -- persistent, and the same [Hireg] the iget
         above was given. *)
      iApply (ID.wp_idup_sconf gtl cn gfs gi cov logstart inodestart nib
                ck dev B3 0%nat eb (proc_addr j) (K - 12)%nat b lks
                Kid ltac:(vm_compute; reflexivity) Hckl HB3a0 Hdev
                ltac:(lkbelow)
                with "Hcg Hcnt Htext Hpc Hitb2 Hitbl Hireg Hisl1 Hcheld").
      all: try lkbelow.
      iIntros (CIDid Hqid mid) "Hcg Hcnt Hpc %Hidp Hcwdr Hip0".
      destruct Hidp as [Hcsid Hida0].
      (* the cwd's own package, back whole -- the carve and the gather
         happened inside the call (SIMP-2). *)
      iEval (rewrite -Hcwde) in "Hcwdr".
      assert (Hpc03a : ret_pc (B3 !!! Regidx Rra) = mword_of_int (NX + 0x3a)).
      { rewrite HB3ra. pcw. }
      iEval (rewrite Hpc03a) in "Hpc".
      (* +0x3a c.mv s4,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x3a)) Rs4 Ra0 mid (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (nxi_03a with "Htext"). }
      iIntros (CIDBm1 HqBm1) "Hcg Hpc". iEval (rgne) in "Hcg".
      pose (B4 := <[Regidx Rs4 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mid !!! Regidx Ra0))]> mid).
      assert (HB4s4 : B4 !!! Regidx Rs4 = ientry ck).
      { rewrite /B4 upd_eq. rewrite Hida0. apply add_vec_zero_l. }
      (* the walk's starting reference: idup's second package, as it stands *)
      iRename "Hip0" into "Hip".
      (* ---- the register facts the two [callee_saved]s carry over ---- *)
      assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
      assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite /B4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsid csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsmp csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B1 upd_ne; [exact HR7sp | nz]. }
      assert (HB4s0 : B4 !!! Regidx Rs0 = sp0).
      { rewrite /B4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsid Rs0 ltac:(vm_compute; reflexivity)).
        rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsmp Rs0 ltac:(vm_compute; reflexivity)).
        rewrite /B1 upd_ne; [exact HR7s0 | nz]. }
      assert (HB4s1 : B4 !!! Regidx Rs1 = pv).
      { rewrite /B4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsid Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsmp Rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B1 upd_ne; [exact HR7s1 | nz]. }
      assert (HB4s5 : B4 !!! Regidx Rs5 = nb).
      { rewrite /B4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsid Rs5 ltac:(vm_compute; reflexivity)).
        rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsmp Rs5 ltac:(vm_compute; reflexivity)).
        rewrite /B1 upd_ne; [exact HR7s5 | nz]. }
      assert (HB4s6 : B4 !!! Regidx Rs6 = (m !!! Regidx Ra1 : mword 64)).
      { rewrite /B4 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsid Rs6 ltac:(vm_compute; reflexivity)).
        rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcsmp Rs6 ltac:(vm_compute; reflexivity)).
        rewrite /B1 upd_ne; [exact HR7s6 | nz]. }
      assert (HB4o : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
                c <> Rs9 -> c <> Rs10 ->
                B4 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
        rewrite /B4 upd_ne; [| dlk_xne N20].
        rewrite (callee_saved_lookup Hcsid c Hc).
        rewrite /B3 upd_ne; [| dlk_rne2 Hcsra Hc].
        rewrite /B2 upd_ne; [| dlk_rne2 Hcsa0 Hc].
        rewrite (callee_saved_lookup Hcsmp c Hc).
        rewrite /B1 upd_ne;
          [ exact (HR7o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
          | dlk_rne2 Hcsra Hc ]. }
      assert (Hpp03c : add_vec_int (mword_of_int (NX + 0x3a) : mword 64) 2
                       = mword_of_int (NX + 0x3c)) by pcw.
      iEval (rewrite Hpp03c) in "Hpc".
      (* ===== +0x3c .. +0x46 : the four constants, then [c.j +0xf4] ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (NX + 0x3c)) Rs3
                (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
                B4 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc []").
      { iApply (nxi_03c with "Htext"). }
      iIntros (CIDB1 HqB1) "Hcg Hpc".
      pose (B5 := <[Regidx Rs3 := regval_into_reg (mword_of_int 47 : mword 64)]> B4).
      assert (HpB040 : add_vec_int (mword_of_int (NX + 0x3c) : mword 64) 4
                       = mword_of_int (NX + 0x40)) by pcw.
      iEval (rewrite HpB040) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x40)) Rs8 (mword_of_int 13 : mword 6)
                (mword_of_int 13 : mword 64) B5 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_040 with "Htext"). }
      iIntros (CIDB2 HqB2) "Hcg Hpc".
      pose (B6 := <[Regidx Rs8 := regval_into_reg (mword_of_int 13 : mword 64)]> B5).
      assert (HpB042 : add_vec_int (mword_of_int (NX + 0x40) : mword 64) 2
                       = mword_of_int (NX + 0x42)) by pcw.
      iEval (rewrite HpB042) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x42)) Rs9 (mword_of_int 14 : mword 6)
                (mword_of_int 14 : mword 64) B6 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_042 with "Htext"). }
      iIntros (CIDB3 HqB3) "Hcg Hpc".
      pose (B7 := <[Regidx Rs9 := regval_into_reg (mword_of_int 14 : mword 64)]> B6).
      assert (HpB044 : add_vec_int (mword_of_int (NX + 0x42) : mword 64) 2
                       = mword_of_int (NX + 0x44)) by pcw.
      iEval (rewrite HpB044) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x44)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) B7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (nxi_044 with "Htext"). }
      iIntros (CIDB4 HqB4) "Hcg Hpc".
      pose (B8 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> B7).
      assert (HpB046 : add_vec_int (mword_of_int (NX + 0x44) : mword 64) 2
                       = mword_of_int (NX + 0x46)) by pcw.
      iEval (rewrite HpB046) in "Hpc".
      assert (HBregs : nx_regs m sp0 pv (ientry ck) nb
                           (m !!! Regidx Ra1 : mword 64) B8).
      { unfold nx_regs. split_and!.
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4sp | nz].
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4s0 | nz].
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4s1 | nz].
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_eq. reflexivity.
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4s4 | nz].
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4s5 | nz].
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [exact HB4s6 | nz].
        - rewrite /B8 upd_eq. reflexivity.
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
          rewrite /B6 upd_eq. reflexivity.
        - rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_eq. reflexivity.
        - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
          rewrite /B8 upd_ne; [| dlk_xne N23].
          rewrite /B7 upd_ne; [| dlk_xne N25].
          rewrite /B6 upd_ne; [| dlk_xne N24].
          rewrite /B5 upd_ne; [| dlk_xne N19].
          exact (HB4o c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26). }
      (* +0x46 c.j +0xf4 : into the walk *)
      assert (HtgtB0e4 : add_vec (mword_of_int (NX + 0x46) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 87 : mword 11) ('b"0"))))
                = mword_of_int (NX + 0xf4)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (NX + 0x46))
                (sign_extend' 21 (concat_vec (mword_of_int 87 : mword 11) ('b"0")))
                B8 (K - 12)%nat b
                ltac:(rewrite HtgtB0e4; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (nxi_046 with "Htext"). }
      iIntros (CIDB5 HqB5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite HtgtB0e4) in "Hpc".
      (* ---- ENTER THE WALK at off = 0, es0 = [], ncur = n ---- *)
      iDestruct (cpu_own_transport CIDid CIDB5 0%nat eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* idup does not thread the complement either. *)
      iDestruct (trap_csrs_ext_transport CID23 CIDB5 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID23 CIDB5 eb (proc_addr j)
                   ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
      iDestruct (wp_next_shift (b := true) (CIDa := CID23) (CIDb := CIDB5)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iSpecialize ("Hloop" $! (S plen) CIDB5 with "[%]"); [wp_next_chain |].
      iApply ("Hloop" $! 0%nat (ientry ck) B8 n Sb [] nfun false
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hextc Hclmc Hpc
                      Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                      Hip Hisl2 Hbmap Hinos Hppid Hcwdr Hpath
                      Hname Hbslot Hlog Hcont").
      - lia.
      - lia.
      - rewrite drop_0. reflexivity.
      (* the budget invariant at entry: nothing paid yet *)
      - exact (nx_wi_init n).
      - lia.
      - exact (nx_wi_need0 _ _ Hbud).
      - rewrite drop_0. exact (nx_wi_need _ _ Hbud).
      - discriminate.
      (* entering the loop, the running set IS the caller's *)
      - reflexivity.
      - rewrite pa_add_0. exact HBregs.
  Qed.

  (* ===================================================================== *)
  (*  THE COUNTED SEAL, at the [log_op] existential's own witness.          *)
  (*  namex takes no credit, so the budget clause is IDENTICAL on both      *)
  (*  sides and the seal is pure plumbing: destruct the reservation, run    *)
  (*  the walk at whatever set was hiding there, and forget the grown set   *)
  (*  again with [LogInv.log_opS_op].                                       *)
  (* ===================================================================== *)
  Lemma wp_namex_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (npar : bool)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_namex_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev plen pfun nfun npar n
                          pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_namex_sconf_body].
    intros pcE pjv pv nb ret_tgt pl L
           HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
           Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen Hbud Hj Hgs Ha1 Hbelow.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hropen #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              #Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog Hcont".
    (* THE WITNESS: the set the counted reservation was hiding *)
    iDestruct "Hlog" as (Sb0) "Hlog".
    iApply (wp_namex_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib size dev
              plen pfun nfun npar n Sb0 pidv dq dqb dqs dqpv m K eb b lks Vpr
              HK Hdev Hnib Htlog Htist Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov
              Hbmaplog Hinos0 Hcovb Hiregb Hcstr Hplen
              (walk_need_counted L n Hbud) Hj Hgs Ha1 Hbelow
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hkenv Hitb2 Hitbl
                    Hesc Hslks Hireg Hropen Hprocs Hdev Hgeom Hdlk Hbmap Hinos
                    Hbits Hppid Hcwdr Hpath Hname Hbslot Hislot Hlog
                    [Hcont]").
    all: try lkbelow.
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    rewrite /namex_postS.
    iIntros (mf n' Sb' ok nf ipv w)
      "%Hcs Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr Hpath
       Hname Hbslot %Hssub %Hwbm %Hbnd Hlog Harm".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    rewrite /namex_post.
    (* THE COUNTED SEAL DROPS BOTH HALVES OF THE GEN POST (fs-log.md §G.24):
       the paid-bitmap report goes ([walk_spend_counted] weakens the figure
       back to the counted one, which is why this statement did not move),
       and so does the parent's type witness -- a counted caller asked for
       [inode_held] and gets it by [inode_held_ty_forget]. *)
    iAssert (if ok
             then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv
                   /\ (npar = true ->
                       exists es e, nameiparent_of pl es e /\ bname 14 nf = e)⌝ ∗
                  inode_held ipv ∗ iref_slots 1
             else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
                   = (mword_of_int 0 : mword 64)⌝ ∗ iref_slots 2)%I
      with "[Harm]" as "Harm".
    { destruct ok; [| iExact "Harm"].
      iDestruct "Harm" as "(%Hf & Hip & Hsl)".
      iSplitR; [iPureIntro; exact Hf |]. iSplitR "Hsl"; [| iExact "Hsl"].
      destruct npar; [iApply (inode_held_ty_forget with "Hip") | iExact "Hip"]. }
    iApply ("Hcont" $! mf n' ok nf ipv
              with "[%] Hcg Hcnt Hextc Hclmc Hpc Hbmap Hinos Hppid Hcwdr
                    Hpath Hname Hbslot [%] [Hlog] Harm").
    { exact Hcs. }
    { split; [exact (walk_spend_counted L n n' w ok Hbud (proj1 Hbnd))
             | exact (proj2 Hbnd)]. }
    { iApply (log_opS_op with "Hlog"). }
  Qed.

End ProofNamexMain.

End NamexProof.
