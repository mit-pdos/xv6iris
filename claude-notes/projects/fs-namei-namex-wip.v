(* ===================================================================== *)
(*  PARKED WIP -- N4c2.  This file is NOT in iris/_CoqProject and is NOT  *)
(*  part of the build.  To resume: copy it to iris/ProofNamex.v and       *)
(*  compile it standalone against the mirror's .vo tree                   *)
(*  (bash ~/one.sh ProofNamex.v).  It was LAST GREEN at that command      *)
(*  (EXIT=0, 0 Error lines) with EXACTLY ONE stub.                        *)
(*                                                                        *)
(*  ##  READ THIS FIRST: THE CONTRACT AS FROZEN IS NOT PROVABLE.  ##      *)
(*                                                                        *)
(*  Two premises are MISSING from [SpecNamex.wp_namex_sconf_body] (and    *)
(*  from SpecNamei / SpecNameiparent, which copy them).  Neither is a     *)
(*  proof difficulty; each is a one-line change, and until they are made  *)
(*  the walk's two [memmove] call sites cannot be discharged AT ALL.      *)
(*                                                                        *)
(*  (A) THE PATH MUST BE OWNED OUTRIGHT.  The contract lends the path at  *)
(*      a parametric [dqp : dfrac]:                                       *)
(*        ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i)       *)
(*      but [SpecMemmove.wp_memmove_sconf_body] demands the SOURCE bytes  *)
(*      at FULL ownership:                                                *)
(*        ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ src_bytes j)       *)
(*      and namex's two memmoves (+0x9e and +0x122) pass [a1 = s1], a     *)
(*      pointer INTO the path.  So [dqp] cannot be instantiated by the    *)
(*      proof.  FIX, either:                                              *)
(*        * drop [dqp] from SpecNamex/SpecNamei/SpecNameiparent (write    *)
(*          [↦ₘ] instead of [↦ₘ{dqp}]) -- sound for every real caller,    *)
(*          whose path is a MAXPATH kernel array it owns outright; or     *)
(*        * generalise SpecMemmove's SOURCE to a [{dqm : dfrac}] (the     *)
(*          DESTINATION must stay full: ProofMemmove refutes the          *)
(*          descending loop by [mem_bytes_notin] on the two buffers, and  *)
(*          one full side is enough).  That touches ProofMemmove and the  *)
(*          nine existing MEMMOVE consumers.                              *)
(*                                                                        *)
(*  (B) THE PATH LENGTH MUST FIT IN A C [int].  +0x90 is                  *)
(*      [addiw s10,a2,0] -- a [sext.w] of [len = s2 - s1] -- and +0x94    *)
(*      is the SIGNED [bge s8,s10] against 13.  With [plen] unbounded the *)
(*      truncation is not the identity and the branch does not decide     *)
(*      [len <= 13]; the short branch then also fails memmove's own       *)
(*      [Z.of_nat len < 2^32] premise.  ADD                               *)
(*        (Z.of_nat plen < 2 ^ 31)%Z                                      *)
(*      to all three contracts.  [SpecFetchstr.v]'s header records the    *)
(*      identical premise for the identical reason (strlen's [subw]), so  *)
(*      the precedent and its justification already exist in this tree.   *)
(*                                                                        *)
(*  Nothing else was found unprovable: every callee premise, resource and *)
(*  register fact that the walk has been driven through fitted exactly.   *)
(*                                                                        *)
(*  WHAT IS PROVEN (everything except the walk's body):                   *)
(*    * the twelve-slot prologue +0x00..+0x1a and the frame carve;        *)
(*    * [Htail], the shared epilogue at +0x5c -- []-persistent, abstract  *)
(*      continuation, twelve pops, the [c.addi16sp +96] and [c.jr ra],    *)
(*      with the full [callee_saved] record (THIRTEEN conjuncts) and      *)
(*      [mf !!! a0 = Mt !!! s4] discharged;                               *)
(*    * the entry block +0x1c..+0x2a and the arm split on [pfun 0];       *)
(*    * the ABSOLUTE arm: [li a1,1; mv a0,a1] = iget(1,1), the call, and  *)
(*      [inode_held (ientry kig)] built from iget's mint;                 *)
(*    * the RELATIVE arm: myproc, [ld a0,336(a0)], the SHED, idup, the    *)
(*      GATHER (cwd's [inode_held] handed back whole at its own [cq]),    *)
(*      and [inode_held (ientry ck)] from idup's new reference;           *)
(*    * the constants block +0x3c..+0x46 in BOTH arms, ending with        *)
(*      [nx_regs m sp0 pv ipv nb (m !!! a1) _] established;               *)
(*    * the STATEMENT of [Hloop] (see below), and BOTH arms discharging   *)
(*      its eight pure obligations and handing over every resource;       *)
(*                                                                        *)
(*    * N4c2's ADDITION -- ALL SIX BYTE-SCANNING BLOCKS, as []-persistent *)
(*      assertions with ABSTRACT CONTINUATIONS, stated and proved BEFORE  *)
(*      [Hloop] and therefore usable from inside its induction.  Between  *)
(*      them they cover +0xe4..+0x114 and +0xa4..+0xb2 -- every           *)
(*      instruction of the inlined [skipelem] except the two memmoves and *)
(*      the length arithmetic.  In dependency order:                      *)
(*                                                                        *)
(*        [Hsk1]   +0xec..+0xf2, fuel-indexed: the LEADING '/' skip.      *)
(*                 In: [pfun off = SLASH], s1 = pv+off, s3 = 47.          *)
(*                 Out at +0xf6: [off'], every byte in [off,off') is '/', *)
(*                 [pfun off' <> SLASH], s1 = pv+off', a5 = the byte.     *)
(*        [Hsk2]   +0xac..+0xb2, the same loop at the same shape, exiting *)
(*                 at +0xb6 -- skipelem's TRAILING skip.                  *)
(*        [Hscn]   +0x106..+0x114, fuel-indexed: the ELEMENT scan.        *)
(*                 In: s2 = pv+ii, [ii < plen].  Out at +0x8c: [e > ii],  *)
(*                 no '/' strictly between, [pfun e = SLASH \/ e = plen], *)
(*                 s2 = pv+e.  BOTH exits (+0x110 taken, +0x114's [c.j])  *)
(*                 are proved.                                            *)
(*        [Hmid]   +0xf6..+0x104 with TWO continuations -- INCLUDING THE  *)
(*                 DEAD BLOCK +0xf8..+0x102, whose two [c.beqz]es are     *)
(*                 refuted from the byte facts +0xe8/+0xf2 and +0xf6 just *)
(*                 decided.  Exit A at +0x130 ([a = plen]); exit B at     *)
(*                 +0x106 (s1 = s2 = pv+a, [pfun a] neither '/' nor NUL). *)
(*        [Hhead]  +0xe4..+0x104, the WHOLE loop head: the [lbu]/[bne]    *)
(*                 pair, then [Hsk1] or straight to [Hmid].  Same two     *)
(*                 exits as [Hmid], with the [off]-relative facts         *)
(*                 ("every byte in [off,a) is '/'") added.                *)
(*        [Htrail] +0xa4..+0xb2, the trailing skip's head + [Hsk2], one   *)
(*                 exit at +0xb6.                                         *)
(*                                                                        *)
(*      The four exit facts of [Hhead]/[Hscn] are EXACTLY                 *)
(*      [ProofNamexParts.nx_skipelem_at]'s four hypotheses, at [a] the    *)
(*      element start and [e] the scan end.  The remaining bridge to the  *)
(*      loop invariant, which is stated over [drop off pl], is            *)
(*        skipelem (drop off pl) = skipelem (drop a pl)                   *)
(*      i.e. [pe_skip (drop off pl) = drop a pl] from "every byte in      *)
(*      [off,a) is '/' and [pfun a] is not"; that lemma is NOT yet        *)
(*      written (induction on [a - off] with [nx_drop_cons],              *)
(*      [pe_skip_slash], [pe_skip_ne]; then [skipelem]'s definition and   *)
(*      [pe_skip_idem] give the [skipelem] form).                         *)
(*                                                                        *)
(*    * the pure byte-test layer these need, all new in N4c2:             *)
(*      [nx_nslash_eq/ne], [nx_nnul_eq/ne] ([bne]/[bnez] polarity), and   *)
(*      N4b trap 8's OWED lemma: [nx_m47_val], [nx_a4_unsigned],          *)
(*      [nx_m47_arith], [nx_a4_eq], [nx_a4_ne] -- the [addi a4,a5,-47]    *)
(*      test at +0xfc and +0x10c.                                         *)
(*                                                                        *)
(*  WHAT IS OWED: the single [exact (cheat_ _)] that stands for the       *)
(*  proof of [Hloop].  With the six assertions above in hand what is left *)
(*  inside it is:                                                         *)
(*    1. drive [Hhead] at [off]; exit A is the +0x130 tail (the [beq      *)
(*       s6,zero] and, when nameiparent, [iput] then s4 := 0), exit B     *)
(*       hands the element start [a];                                     *)
(*    2. drive [Hscn] at [a]; then +0x8c [sub a2,s2,s1] / +0x90 [sext.w]  *)
(*       / +0x94 [bge s8,s10] -- BLOCKED ON PREMISE (B) ABOVE;            *)
(*    3. the two memmove branches -- BLOCKED ON PREMISE (A) ABOVE;        *)
(*    4. drive [Htrail]; then +0xb6..+0xda: ilock, the [lh a5,68(s4)]     *)
(*       type test, the nameiparent early stop, dirlookup, and the four   *)
(*       exits (+0x54, +0x7a, +0x82, +0xdc's fall into +0xe4).            *)
(*  Steps 1 and 4's callee choreography is design layer 6, unchanged.     *)
(*  Delete [Axiom cheat_] when it lands.                                  *)
(*                                                                        *)
(*  The park is recorded in claude-notes/projects/fs-namei.md, N4c2.      *)
(* ===================================================================== *)

(* ProofNamex.v -- the whole-function proof of namex, fs.c's path walker.

   318 bytes, width 3, skipelem INLINED.  The CFG is NOT the address order
   (gcc reordered the blocks); in EXECUTION order it is

     entry     +0x1c..0x2a   s1=path,s6=npar,s5=name; lbu a4,0(a0); beq -> +0x48
     relative  +0x2e..0x3a   myproc; ld a0,336(a0); idup; s4=a0
     absolute  +0x48..0x52   li a1,1; mv a0,a1  (= iget(1,1)); s4=a0; j +0x3c
     consts    +0x3c..0x46   s3=47,s8=13,s9=14,s7=1; j +0xe4
   L_loop      +0xe4..0xf6   while ( *s1=='/' ) s1++;  if ( *s1==0 ) -> L_done
     DEAD      +0xf8..0x102  re-load *s1, re-test '/' and 0 (never taken)
     scan      +0x104..0x114 s2=s1; do s2++ while ( *s2!='/' && *s2!=0 )
   L_len       +0x8c..0x94   a2=s2-s1; s10=sext.w a2; bge s8,s10 -> L_short
     long      +0x98..0xa2   memmove(name,s1,14); NO terminator; s1=s2
     len0 DEAD +0x116..0x11a s2=s1; s10=0; a2=0   (never entered)
   L_short     +0x11c..0x12e memmove(name,s1,len); name[len]=0; s1=s2; j L_trail
   L_trail     +0xa4..0xb2   while ( *s1=='/' ) s1++
               +0xb6..0xc0   ilock(s4); lh a5,68(s4); bne a5,s7 -> L_notdir
               +0xc4..0xcc   if(s6) { if ( *s1==0 ) -> L_par }
               +0xce..0xda   dirlookup(s4,s5,0) -> s2; beqz -> L_miss
     found     +0xdc..0xe2   iunlockput(s4); s4=s2;  FALLS INTO L_loop
   L_notdir    +0x54..0x5a   iunlockput(s4); s4=0
   L_par       +0x7a..0x80   iunlock(s4); j +0x5c
   L_miss      +0x82..0x8a   iunlockput(s4); s4=s2(=0); j +0x5c
   L_done      +0x130..0x13c if(!s6) j +0x5c; iput(s4); s4=0; j +0x5c
     return    +0x5c..0x78   a0=s4; twelve pops; c.addi16sp +96; c.jr ra

   ---- THE PIECES -------------------------------------------------------

   [Htail] -- the shared epilogue at +0x5c, a []-PERSISTENT [wp_next]-wrapped
   assertion with an ABSTRACT CONTINUATION (ProofDirlookup's shape).  FOUR
   arms reach it holding four different bundles, so it must speak only about
   the twelve frame slots and [nx_tregs].

   [Hloop] -- the walk at +0xe4, ProofKexit's [forall fuel, wp_next] shape over
   the measure [plen - off].  INSIDE it live three more of the same shape:
   the leading-'/' skip at +0xe4..+0xf2, the element scan at +0x106..+0x112,
   and the trailing-'/' skip at +0xa4..+0xb2 (reached from BOTH memmove
   branches).  The contract's own continuation is threaded through [Hloop]
   as a spatial slot, exactly as ProofDirlookup threads [Hcont].

   ---- THE SHARE CHOREOGRAPHY, PER ELEMENT ------------------------------

   Destruct [inode_held] -> [inode_ref_shed] (q/2 + q/2) -> the share goes to
   ilock, the walk keeps [inode_ref_short k (q/2+q/2) (q/2)].  Exits:
   (not T_DIR) iunlockput deposits the descriptor and the short parent;
   (nameiparent /\ rest = []) iunlock hands the share back and
   [inode_ref_gather] re-forms the whole reference; (found) the child's
   reference comes out of dirlookup's FOUND arm and iunlockput retires the
   parent; (miss) iunlockput retires the parent and the walk ends at 0.     *)
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
Require Import RiscvExtras.
Require Import RiscvFetchExec.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.
Require Import KptGhost.
Require Import SmodeCore.
Require Import KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSconfVc.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import PathElems.
Require Import DirView.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import SpecPanic.
Require Import SpecMyproc SpecIdup SpecIget SpecMemmove.
Require Import SpecIlock SpecIunlock SpecIunlockput SpecIput.
Require Import SpecDirlookup SpecDirlink.
Require Import CodeNamex.
Require Import SpecNamex.
Require Import ProofDirlookupParts ProofNamexParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  THE PURE SIDE-CONDITIONS, as closed facts over [Z] / [nat] -- the     *)
(*  route N3d recorded: never run [lia] inside the whole-function         *)
(*  context.                                                              *)
(* ===================================================================== *)

(* the budget invariant's three moving parts.  [ncur] is the reservation
   the walk still holds, [Lr] the elements still to consume. *)
Lemma nx_bi_step (L Lr n ncur ncur' : nat) :
  ((S Lr + 1) * iput_units <= ncur)%nat ->
  ((n - (L + 1) * iput_units)%nat <= (ncur - (S Lr + 1) * iput_units)%nat)%nat ->
  (ncur <= n)%nat ->
  ((ncur - iput_units)%nat <= ncur')%nat -> (ncur' <= ncur)%nat ->
  ((Lr + 1) * iput_units <= ncur')%nat
  /\ ((n - (L + 1) * iput_units)%nat <= (ncur' - (Lr + 1) * iput_units)%nat)%nat
  /\ (ncur' <= n)%nat.
Proof. unfold iput_units. lia. Qed.

(* an exit that spends ONE interval (iunlockput / iput) *)
Lemma nx_bi_spend (L Lr n ncur n' : nat) :
  ((Lr + 1) * iput_units <= ncur)%nat ->
  ((n - (L + 1) * iput_units)%nat <= (ncur - (Lr + 1) * iput_units)%nat)%nat ->
  (ncur <= n)%nat ->
  ((ncur - iput_units)%nat <= n')%nat -> (n' <= ncur)%nat ->
  ((n - (L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat.
Proof. unfold iput_units. lia. Qed.

(* an exit that spends NOTHING (iunlock, or the plain return) *)
Lemma nx_bi_free (L Lr n ncur : nat) :
  ((Lr + 1) * iput_units <= ncur)%nat ->
  ((n - (L + 1) * iput_units)%nat <= (ncur - (Lr + 1) * iput_units)%nat)%nat ->
  (ncur <= n)%nat ->
  ((n - (L + 1) * iput_units)%nat <= ncur)%nat /\ (ncur <= n)%nat.
Proof. unfold iput_units. lia. Qed.

(* the initial instance, at [ncur = n] and [Lr = L] *)
Lemma nx_bi_init (L n : nat) :
  ((L + 1) * iput_units <= n)%nat ->
  ((n - (L + 1) * iput_units)%nat <= (n - (L + 1) * iput_units)%nat)%nat
  /\ (n <= n)%nat.
Proof. intro. split; lia. Qed.

(* K_namex's single premise, turned into the seven bounds the callees and
   the [sie_cap_gpr] pop want.  [dl_kb]'s analogue. *)
Lemma nx_kb (K : nat) : (K_namex <= K)%nat ->
  (10 <= K - 12)%nat /\ (K_idup <= K - 12)%nat /\ (K_iget <= K - 12)%nat
  /\ (2 <= K - 12)%nat /\ (K_ilock <= K - 12)%nat /\ (K_iunlock <= K - 12)%nat
  /\ (K_iunlockput <= K - 12)%nat /\ (K_dirlookup <= K - 12)%nat
  /\ (K_iput <= K - 12)%nat /\ ((K - 12) + 12 = K)%nat /\ (12 <= K)%nat.
Proof.
  unfold K_namex, K_idup, K_iget, K_ilock, K_iunlock,
         K_iunlockput, K_dirlookup, K_iput.
  intro H. split_and!; lia.
Qed.

(* ---- the two BYTE TESTS namex performs, in both register orders ------
   [lbu] leaves [zero_extend' 64 v]; the separator is compared against the
   literal 47 (in [a5] at +0x26, in [s3] everywhere else) and the terminator
   against [x0].  The family of [ProofNamecmp.nc_byte_of_zero]: bv_unsigned
   arithmetic, no 256-way case split. *)
Lemma nx_zext8_unsigned (x : mword 8) :
  bv_unsigned (zero_extend' 64 x : mword 64) = bv_unsigned x.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  apply bv_zero_extend_unsigned. vm_compute. discriminate.
Qed.

Lemma nx_slash_eq (v : mword 8) : v = SLASH ->
  eq_vec (zero_extend' 64 v : mword 64) (mword_of_int 47 : mword 64) = true.
Proof.
  intros ->. apply (proj2 (eq_vec_true_iff _ _)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma nx_slash_ne (v : mword 8) : v <> SLASH ->
  eq_vec (zero_extend' 64 v : mword 64) (mword_of_int 47 : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)). intro Hc. apply Hne.
  apply (f_equal bv_unsigned) in Hc. rewrite nx_zext8_unsigned in Hc.
  apply bv_eq. rewrite Hc. vm_compute. reflexivity.
Qed.

Lemma nx_slash_eq' (v : mword 8) : v = SLASH ->
  eq_vec (mword_of_int 47 : mword 64) (zero_extend' 64 v : mword 64) = true.
Proof.
  intros ->. apply (proj2 (eq_vec_true_iff _ _)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma nx_slash_ne' (v : mword 8) : v <> SLASH ->
  eq_vec (mword_of_int 47 : mword 64) (zero_extend' 64 v : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)). intro Hc. apply Hne.
  apply (f_equal bv_unsigned) in Hc. rewrite nx_zext8_unsigned in Hc.
  apply bv_eq. rewrite -Hc. vm_compute. reflexivity.
Qed.

Lemma nx_nul_eq (v : mword 8) : v = NUL ->
  eq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64) = true.
Proof.
  intros ->. apply (proj2 (eq_vec_true_iff _ _)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma nx_nul_ne (v : mword 8) : v <> NUL ->
  eq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hne. apply (proj2 (eq_vec_false_iff _ _)). intro Hc. apply Hne.
  apply (f_equal bv_unsigned) in Hc. rewrite nx_zext8_unsigned in Hc.
  apply bv_eq. rewrite Hc. vm_compute. reflexivity.
Qed.

(* the [c.addi s1,s1,1] of all three separator skips, as an index step *)
Lemma nx_addi1 (p : mword 64) (i : nat) :
  add_vec (pa_add p i)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = pa_add p (S i).
Proof.
  assert (H1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                : mword 64) = mword_of_int 1)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H1. apply pa_add_S.
Qed.

(* ---- the same two tests in [bne]/[bnez] polarity.  [neq_vec] is
   [negb (eq_vec ...)], so each is one [unfold] away from its sibling. *)
Lemma nx_nslash_ne (v : mword 8) : v <> SLASH ->
  neq_vec (zero_extend' 64 v : mword 64) (mword_of_int 47 : mword 64) = true.
Proof. intro H. unfold neq_vec. rewrite (nx_slash_ne v H). reflexivity. Qed.

Lemma nx_nslash_eq (v : mword 8) : v = SLASH ->
  neq_vec (zero_extend' 64 v : mword 64) (mword_of_int 47 : mword 64) = false.
Proof. intro H. unfold neq_vec. rewrite (nx_slash_eq v H). reflexivity. Qed.

Lemma nx_nnul_ne (v : mword 8) : v <> NUL ->
  neq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64) = true.
Proof. intro H. unfold neq_vec. rewrite (nx_nul_ne v H). reflexivity. Qed.

Lemma nx_nnul_eq (v : mword 8) : v = NUL ->
  neq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64) = false.
Proof. intro H. unfold neq_vec. rewrite (nx_nul_eq v H). reflexivity. Qed.

(* ---- THE [addi a4,a5,-47] SLASH TEST at +0xfc and +0x10c (N4b trap 8).
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
   +0x100 / +0x102 and the live +0x110 read it. *)

(* THE STUB AT THE FRONTIER -- removed before the file lands. *)
Axiom cheat_ : forall (A : Type), A.

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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* ONE byte out of a [seq 0 N] buffer, and the way back.  Used for the
     path (at [dqp]) and for the name buffer (at full ownership). *)
  Lemma nx_buf_acc (a : mword 64) (dqm : dfrac) (f : nat -> bv 8) (N i : nat) :
    (i < N)%nat ->
    ([∗ list] ii ∈ seq 0 N, pa_add a ii ↦ₘ{dqm} f ii) -∗
    (pa_add a i ↦ₘ{dqm} f i)
    ∗ ((pa_add a i ↦ₘ{dqm} f i) -∗
       [∗ list] ii ∈ seq 0 N, pa_add a ii ↦ₘ{dqm} f ii).
  Proof.
    intro Hi. iIntros "Hbuf".
    iDestruct (big_sepL_lookup_acc _ (seq 0 N) i i with "Hbuf") as "[Hb Hback]".
    { rewrite lookup_seq_lt; [reflexivity | exact Hi]. }
    iFrame "Hb Hback".
  Qed.

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
      (used : gset Z)
      (cwdv : mword 64)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (npar : bool)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs dqc dqp : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_namex_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev used cwdv plen pfun nfun npar n
                          pidv dq dqb dqs dqc dqp m K eb C b.
  Proof.
    cbv beta delta [wp_namex_sconf_body].
    intros pcE pjv pv nb ret_tgt pl L
           HK Hdev Hnib Hroot Hnib0 Hlg Hsize Hbmap0 Hbmapcov Hbmaplog
           Hinos0 Hcovb Hiregb Hcstr Hbud Hj Hgs Ha1 Heb.
    destruct (nx_kb K HK) as (Kmp & Kid & Kig & Kmm & Kil & Kiu & Kiup
                              & Kdl & Kip & Kpop & K12).
    (* N3d trap 1's whole-function fix: rename the [let]-bound [pj], fold
       [proc_addr j] into every resource ONCE, and never write [pjv] again. *)
    assert (Hpjd : proc_addr j = pjv) by reflexivity.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlogc #Hkenv #Hitb2 #Hitbl
              #Hesc #Hslks #Hireg #Hprocs #Hdev #Hgeom #Hdlk Hbmap Hinos
              Hbits Hppid Hcwdc Hcwdr Hpath Hname Hbslot Hislot Hlog Hcont".
    iEval (rewrite -Hpjd) in "Hcg".
    iEval (rewrite -Hpjd) in "Hcnt".
    iEval (rewrite -Hpjd) in "Hppid".
    iEval (rewrite -Hpjd) in "Hcwdc".
    iEval (rewrite -Hpjd) in "Hcont".
    iPoseProof (nxi_000 with "Htext") as "Hi000".
    iPoseProof (nxi_002 with "Htext") as "Hi002".
    iPoseProof (nxi_004 with "Htext") as "Hi004".
    iPoseProof (nxi_006 with "Htext") as "Hi006".
    iPoseProof (nxi_008 with "Htext") as "Hi008".
    iPoseProof (nxi_00a with "Htext") as "Hi00a".
    iPoseProof (nxi_00c with "Htext") as "Hi00c".
    iPoseProof (nxi_00e with "Htext") as "Hi00e".
    iPoseProof (nxi_010 with "Htext") as "Hi010".
    iPoseProof (nxi_012 with "Htext") as "Hi012".
    iPoseProof (nxi_014 with "Htext") as "Hi014".
    iPoseProof (nxi_016 with "Htext") as "Hi016".
    iPoseProof (nxi_018 with "Htext") as "Hi018".
    iPoseProof (nxi_01a with "Htext") as "Hi01a".
    (* ===== +0x00 c.addi16sp sp,-96 : the 12-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12) by apply dlk_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m K 12 b
              ltac:(lia) Hpush with "Hcg Hpc Hi000").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R1 upd_eq; exact Hpush).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
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
    assert (Hpp002 : add_vec_int (pcE : mword 64) 2 = mword_of_int (NX + 0x02)) by pcw.
    iEval (rewrite Hpp002) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x02 .. +0x18 : the TWELVE saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x02)) (mword_of_int 11 : mword 6)
              Rra R1 (K - 12)%nat u1 b with "Hcg Hpc Hi002 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp004 : add_vec_int (mword_of_int (NX + 0x02) : mword 64) 2
                     = mword_of_int (NX + 0x04)) by pcw.
    iEval (rewrite Hpp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x04)) (mword_of_int 10 : mword 6)
              Rs0 R1 (K - 12)%nat u2 b with "Hcg Hpc Hi004 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp006 : add_vec_int (mword_of_int (NX + 0x04) : mword 64) 2
                     = mword_of_int (NX + 0x06)) by pcw.
    iEval (rewrite Hpp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x06)) (mword_of_int 9 : mword 6)
              Rs1 R1 (K - 12)%nat u3 b with "Hcg Hpc Hi006 Hb3").
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hpp008 : add_vec_int (mword_of_int (NX + 0x06) : mword 64) 2
                     = mword_of_int (NX + 0x08)) by pcw.
    iEval (rewrite Hpp008) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x08)) (mword_of_int 8 : mword 6)
              Rs2 R1 (K - 12)%nat u4 b with "Hcg Hpc Hi008 Hb4").
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp00a : add_vec_int (mword_of_int (NX + 0x08) : mword 64) 2
                     = mword_of_int (NX + 0x0a)) by pcw.
    iEval (rewrite Hpp00a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x0a)) (mword_of_int 7 : mword 6)
              Rs3 R1 (K - 12)%nat u5 b with "Hcg Hpc Hi00a Hb5").
    iIntros (CID6 Hq6) "Hcg Hpc Hb5".
    iEval (rgne; rewrite (HR1o Rs3 ltac:(nz)) Hf5) in "Hb5".
    assert (Hpp00c : add_vec_int (mword_of_int (NX + 0x0a) : mword 64) 2
                     = mword_of_int (NX + 0x0c)) by pcw.
    iEval (rewrite Hpp00c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x0c)) (mword_of_int 6 : mword 6)
              Rs4 R1 (K - 12)%nat u6 b with "Hcg Hpc Hi00c Hb6").
    iIntros (CID7 Hq7) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hpp00e : add_vec_int (mword_of_int (NX + 0x0c) : mword 64) 2
                     = mword_of_int (NX + 0x0e)) by pcw.
    iEval (rewrite Hpp00e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x0e)) (mword_of_int 5 : mword 6)
              Rs5 R1 (K - 12)%nat u7 b with "Hcg Hpc Hi00e Hb7").
    iIntros (CID8 Hq8) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp010 : add_vec_int (mword_of_int (NX + 0x0e) : mword 64) 2
                     = mword_of_int (NX + 0x10)) by pcw.
    iEval (rewrite Hpp010) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x10)) (mword_of_int 4 : mword 6)
              Rs6 R1 (K - 12)%nat u8 b with "Hcg Hpc Hi010 Hb8").
    iIntros (CID9 Hq9) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp012 : add_vec_int (mword_of_int (NX + 0x10) : mword 64) 2
                     = mword_of_int (NX + 0x12)) by pcw.
    iEval (rewrite Hpp012) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x12)) (mword_of_int 3 : mword 6)
              Rs7 R1 (K - 12)%nat u9 b with "Hcg Hpc Hi012 Hb9").
    iIntros (CID10 Hq10) "Hcg Hpc Hb9".
    iEval (rgne; rewrite (HR1o Rs7 ltac:(nz)) Hf9) in "Hb9".
    assert (Hpp014 : add_vec_int (mword_of_int (NX + 0x12) : mword 64) 2
                     = mword_of_int (NX + 0x14)) by pcw.
    iEval (rewrite Hpp014) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x14)) (mword_of_int 2 : mword 6)
              Rs8 R1 (K - 12)%nat u10 b with "Hcg Hpc Hi014 Hb10").
    iIntros (CID11 Hq11) "Hcg Hpc Hb10".
    iEval (rgne; rewrite (HR1o Rs8 ltac:(nz)) Hf10) in "Hb10".
    assert (Hpp016 : add_vec_int (mword_of_int (NX + 0x14) : mword 64) 2
                     = mword_of_int (NX + 0x16)) by pcw.
    iEval (rewrite Hpp016) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x16)) (mword_of_int 1 : mword 6)
              Rs9 R1 (K - 12)%nat u11 b with "Hcg Hpc Hi016 Hb11").
    iIntros (CID12 Hq12) "Hcg Hpc Hb11".
    iEval (rgne; rewrite (HR1o Rs9 ltac:(nz)) Hf11) in "Hb11".
    assert (Hpp018 : add_vec_int (mword_of_int (NX + 0x16) : mword 64) 2
                     = mword_of_int (NX + 0x18)) by pcw.
    iEval (rewrite Hpp018) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (NX + 0x18)) (mword_of_int 0 : mword 6)
              Rs10 R1 (K - 12)%nat u12 b with "Hcg Hpc Hi018 Hb12").
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
              with "Hcg Hpc Hi01a").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
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
    iAssert (□ wp_next (CID0 := CID) b (proc_addr j) (fun CIDt : CpuId =>
               ∀ (Mt : regfile) (rv : mword 64),
                 ⌜nx_tregs m sp0 Mt⌝ -∗
                 ⌜Mt !!! Regidx Rs4 = rv⌝ -∗
                 sie_cap_gpr Mt (K - 12)%nat b (proc_addr j) -∗
                 pc_is (mword_of_int (NX + 0x5c)) -∗
                 (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
                 (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
                 (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
                 (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
                 (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
                 (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
                 (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
                 (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
                 (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
                 (pa_stk sp0 10) ↦₈ (m !!! Regidx Rs8 : mword 64) -∗
                 (pa_stk sp0 11) ↦₈ (m !!! Regidx Rs9 : mword 64) -∗
                 (pa_stk sp0 12) ↦₈ (m !!! Regidx Rs10 : mword 64) -∗
                 wp_next (CID0 := CIDt) b (proc_addr j) (fun CIDf : CpuId =>
                   ∀ mf : regfile,
                     ⌜callee_saved m mf⌝ -∗
                     ⌜mf !!! Regidx Ra0 = rv⌝ -∗
                     sie_cap_gpr mf K b (proc_addr j) -∗
                     pc_is ret_tgt -∗
                     WP (Loop : expr riscv_lang)) -∗
                 WP (Loop : expr riscv_lang)))%I with "[]" as "#Htail".
    { iModIntro.
      iIntros (CIDt Hst Mt rv) "%HTr %HTs4 Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
                                Hb8 Hb9 Hb10 Hb11 Hb12 Hqc".
      destruct HTr as [HTsp HTthr].
      iPoseProof (nxi_05c with "Htext") as "Hj5c".
      iPoseProof (nxi_05e with "Htext") as "Hj5e".
      iPoseProof (nxi_060 with "Htext") as "Hj60".
      iPoseProof (nxi_062 with "Htext") as "Hj62".
      iPoseProof (nxi_064 with "Htext") as "Hj64".
      iPoseProof (nxi_066 with "Htext") as "Hj66".
      iPoseProof (nxi_068 with "Htext") as "Hj68".
      iPoseProof (nxi_06a with "Htext") as "Hj6a".
      iPoseProof (nxi_06c with "Htext") as "Hj6c".
      iPoseProof (nxi_06e with "Htext") as "Hj6e".
      iPoseProof (nxi_070 with "Htext") as "Hj70".
      iPoseProof (nxi_072 with "Htext") as "Hj72".
      iPoseProof (nxi_074 with "Htext") as "Hj74".
      iPoseProof (nxi_076 with "Htext") as "Hj76".
      iPoseProof (nxi_078 with "Htext") as "Hj78".
      (* +0x5c c.mv a0,s4 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x5c)) Ra0 Rs4 Mt (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj5c").
      iIntros (CIDT0 HqT0) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (P0 := <[Regidx Ra0 := regval_into_reg
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj5e Hb1").
      iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
      set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj60 Hb2").
      iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
      set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj62 Hb3").
      iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
      set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj64 Hb4").
      iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
      set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj66 Hb5").
      iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
      set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj68 Hb6").
      iIntros (CIDT6 HqT6) "Hcg Hpc Hb6".
      set (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6a Hb7").
      iIntros (CIDT7 HqT7) "Hcg Hpc Hb7".
      set (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6c Hb8").
      iIntros (CIDT8 HqT8) "Hcg Hpc Hb8".
      set (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6e Hb9").
      iIntros (CIDT9 HqT9) "Hcg Hpc Hb9".
      set (P9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P8).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj70 Hb10").
      iIntros (CIDT10 HqT10) "Hcg Hpc Hb10".
      set (P10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> P9).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj72 Hb11").
      iIntros (CIDT11 HqT11) "Hcg Hpc Hb11".
      set (P11 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> P10).
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
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj74 Hb12").
      iIntros (CIDT12 HqT12) "Hcg Hpc Hb12".
      set (P12 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> P11).
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
      iAssert (stack_own sp0 12) with
        "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12]" as "Hstk".
      { rewrite stack_own_slots. cbn [seq].
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
                with "Hcg Hpc Hj76 Hstk").
      iIntros (CIDT13 HqT13) "Hcg Hpc".
      set (P13 := <[Regidx csp_rs1 := regval_into_reg
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
                ltac:(nz) with "Hcg Hpc Hj78").
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
      iSpecialize ("Hqc" $! CIDT14 with "[%]"); [wp_next_chain |].
      iApply ("Hqc" $! P13 with "[%] [%] Hcg Hpc").
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
    (* ---- (1) the LEADING separator skip, inner loop at +0xec ---------- *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) b (proc_addr j)
               (fun CIDs : CpuId =>
                 ∀ (off : nat) (Ms : regfile),
                   ⌜(plen - off <= fuel)%nat⌝ -∗
                   ⌜(off < plen)%nat⌝ -∗
                   ⌜pfun off = SLASH⌝ -∗
                   ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
                   ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
                   sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                   pc_is (mword_of_int (NX + 0xec)) -∗
                   ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
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
                       sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                       pc_is (mword_of_int (NX + 0xf6)) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add pv i ↦ₘ{dqp} pfun i) -∗
                       WP (Loop : expr riscv_lang)) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "#Hsk1".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHs".
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        iPoseProof (nxi_0ec with "Htext") as "Hjec".
        iPoseProof (nxi_0ee with "Htext") as "Hjee".
        iPoseProof (nxi_0f2 with "Htext") as "Hjf2".
        (* +0xec c.addi s1,s1,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0xec)) Rs1
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjec").
        iIntros (CIDk1 Hqk1) "Hcg Hpc".
        iEval (rgne; rewrite Hs1 (nx_addi1 pv off)) in "Hcg".
        set (Q1 := <[Regidx Rs1 := regval_into_reg (pa_add pv (S off))]> Ms).
        assert (HQ1s1 : Q1 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /Q1; apply upd_eq).
        assert (HQ1s3 : Q1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /Q1 upd_ne; [exact Hs3 | nz]).
        assert (Hqee : add_vec_int (mword_of_int (NX + 0xec) : mword 64) 2
                       = mword_of_int (NX + 0xee)) by pcw.
        iEval (rewrite Hqee) in "Hpc".
        (* +0xee lbu a5,0(s1) *)
        iDestruct (nx_buf_acc pv dqp pfun (S plen) (S off) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xee)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) Q1 (K - 12)%nat
                  (pfun (S off) : mword 8) b (dqm := dqp)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjee [Hpb] [-]").
        { iEval (rgne; rewrite HQ1s1 addv_sext0). iExact "Hpb". }
        iIntros (CIDk2 Hqk2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HQ1s1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        set (Q2 := <[Regidx Ra5 := regval_into_reg
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
        assert (Hqf2 : add_vec_int (mword_of_int (NX + 0xee) : mword 64) 4
                       = mword_of_int (NX + 0xf2)) by pcw.
        iEval (rewrite Hqf2) in "Hpc".
        assert (Htec : add_vec (mword_of_int (NX + 0xf2) : mword 64)
                  (sign_extend' 64 (mword_of_int 8186 : mword 13))
                = mword_of_int (NX + 0xec)) by pcw.
        destruct (decide (pfun (S off) = SLASH)) as [Hsl2 | Hsl2].
        + (* another separator: [beq s3,a5] back to +0xec *)
          iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0xf2))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 Q2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HQ2a5 HQ2s3;
                          exact (nx_slash_eq _ Hsl2))
                    ltac:(rewrite Htec; vm_compute; reflexivity)
                    with "Hcg Hpc Hjf2").
          iIntros (CIDk3 Hqk3). iNext. iIntros "Hcg Hpc".
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
        + (* the first non-separator: [beq] falls through to +0xf6 *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0xf2))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 Q2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HQ2a5 HQ2s3;
                          exact (nx_slash_ne _ Hsl2))
                    with "Hcg Hpc Hjf2").
          iIntros (CIDk3 Hqk3) "Hcg Hpc".
          assert (Hqf6 : add_vec_int (mword_of_int (NX + 0xf2) : mword 64) 4
                         = mword_of_int (NX + 0xf6)) by pcw.
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
    (* ---- (2) the TRAILING separator skip, inner loop at +0xac ---------
       byte-identical to (1) at three different addresses; the exit is at
       +0xb6, where [ilock]'s argument setup begins. *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) b (proc_addr j)
               (fun CIDs : CpuId =>
                 ∀ (off : nat) (Ms : regfile),
                   ⌜(plen - off <= fuel)%nat⌝ -∗
                   ⌜(off < plen)%nat⌝ -∗
                   ⌜pfun off = SLASH⌝ -∗
                   ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
                   ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
                   sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                   pc_is (mword_of_int (NX + 0xac)) -∗
                   ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
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
                       sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                       pc_is (mword_of_int (NX + 0xb6)) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add pv i ↦ₘ{dqp} pfun i) -∗
                       WP (Loop : expr riscv_lang)) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "#Hsk2".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHt".
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss off Ms) "%Hf %Holt %Hsl %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
        iPoseProof (nxi_0ac with "Htext") as "Hjac".
        iPoseProof (nxi_0ae with "Htext") as "Hjae".
        iPoseProof (nxi_0b2 with "Htext") as "Hjb2".
        (* +0xac c.addi s1,s1,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0xac)) Rs1
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjac").
        iIntros (CIDt1 Hqt1) "Hcg Hpc".
        iEval (rgne; rewrite Hs1 (nx_addi1 pv off)) in "Hcg".
        set (T1 := <[Regidx Rs1 := regval_into_reg (pa_add pv (S off))]> Ms).
        assert (HT1s1 : T1 !!! Regidx Rs1 = pa_add pv (S off))
          by (rewrite /T1; apply upd_eq).
        assert (HT1s3 : T1 !!! Regidx Rs3 = (mword_of_int 47 : mword 64))
          by (rewrite /T1 upd_ne; [exact Hs3 | nz]).
        assert (Hqae : add_vec_int (mword_of_int (NX + 0xac) : mword 64) 2
                       = mword_of_int (NX + 0xae)) by pcw.
        iEval (rewrite Hqae) in "Hpc".
        (* +0xae lbu a5,0(s1) *)
        iDestruct (nx_buf_acc pv dqp pfun (S plen) (S off) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xae)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) T1 (K - 12)%nat
                  (pfun (S off) : mword 8) b (dqm := dqp)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjae [Hpb] [-]").
        { iEval (rgne; rewrite HT1s1 addv_sext0). iExact "Hpb". }
        iIntros (CIDt2 Hqt2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HT1s1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        set (T2 := <[Regidx Ra5 := regval_into_reg
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
        assert (Hqb2 : add_vec_int (mword_of_int (NX + 0xae) : mword 64) 4
                       = mword_of_int (NX + 0xb2)) by pcw.
        iEval (rewrite Hqb2) in "Hpc".
        assert (Htac : add_vec (mword_of_int (NX + 0xb2) : mword 64)
                  (sign_extend' 64 (mword_of_int 8186 : mword 13))
                = mword_of_int (NX + 0xac)) by pcw.
        destruct (decide (pfun (S off) = SLASH)) as [Hsl2 | Hsl2].
        + iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0xb2))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 T2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HT2a5 HT2s3;
                          exact (nx_slash_eq _ Hsl2))
                    ltac:(rewrite Htac; vm_compute; reflexivity)
                    with "Hcg Hpc Hjb2").
          iIntros (CIDt3 Hqt3). iNext. iIntros "Hcg Hpc".
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
        + iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0xb2))
                    (mword_of_int 8186 : mword 13) Rs3 Ra5 T2 (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HT2a5 HT2s3;
                          exact (nx_slash_ne _ Hsl2))
                    with "Hcg Hpc Hjb2").
          iIntros (CIDt3 Hqt3) "Hcg Hpc".
          assert (Hqb6 : add_vec_int (mword_of_int (NX + 0xb2) : mword 64) 4
                         = mword_of_int (NX + 0xb6)) by pcw.
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
    (* ---- (3) the ELEMENT scan, inner loop at +0x106 -------------------
       [s2] runs forward until the byte it points at is a separator or the
       terminator; the [addi a4,a5,-47] at +0x10c is the separator test and
       the [c.bnez a5] at +0x112 the terminator test.  BOTH exits leave at
       +0x8c, where the length is computed. *)
    iAssert (∀ fuel : nat, □ wp_next (CID0 := CID) b (proc_addr j)
               (fun CIDs : CpuId =>
                 ∀ (ii : nat) (Ms : regfile),
                   ⌜(plen - ii <= fuel)%nat⌝ -∗
                   ⌜(ii < plen)%nat⌝ -∗
                   ⌜Ms !!! Regidx Rs2 = pa_add pv ii⌝ -∗
                   sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                   pc_is (mword_of_int (NX + 0x106)) -∗
                   ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                   wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
                     ∀ (e : nat) (Ms' : regfile),
                       ⌜(ii < e)%nat⌝ -∗ ⌜(e <= plen)%nat⌝ -∗
                       ⌜forall jj : nat, (ii < jj)%nat -> (jj < e)%nat ->
                          pfun jj <> SLASH⌝ -∗
                       ⌜pfun e = SLASH \/ e = plen⌝ -∗
                       ⌜Ms' !!! Regidx Rs2 = pa_add pv e⌝ -∗
                       ⌜forall c : mword 5, c <> Rs2 -> c <> Ra5 -> c <> Ra4 ->
                          Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
                       sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                       pc_is (mword_of_int (NX + 0x8c)) -∗
                       ([∗ list] i ∈ seq 0 (S plen),
                          pa_add pv i ↦ₘ{dqp} pfun i) -∗
                       WP (Loop : expr riscv_lang)) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "#Hscn".
    { iIntros (fuel). iInduction fuel as [|fuel] "IHe".
      - iModIntro.
        iIntros (CIDs Hss ii Ms) "%Hf %Hilt %Hs2 Hcg Hpc Hpath Hqc".
        assert (Hbad : False) by lia. destruct Hbad.
      - iModIntro.
        iIntros (CIDs Hss ii Ms) "%Hf %Hilt %Hs2 Hcg Hpc Hpath Hqc".
        iPoseProof (nxi_106 with "Htext") as "Hj106".
        iPoseProof (nxi_108 with "Htext") as "Hj108".
        iPoseProof (nxi_10c with "Htext") as "Hj10c".
        iPoseProof (nxi_110 with "Htext") as "Hj110".
        iPoseProof (nxi_112 with "Htext") as "Hj112".
        iPoseProof (nxi_114 with "Htext") as "Hj114".
        (* +0x106 c.addi s2,s2,1 *)
        iApply (wp_caddi_s_sconf (mword_of_int (NX + 0x106)) Rs2
                  (mword_of_int 1 : mword 6) Ms (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj106").
        iIntros (CIDe1 Hqe1) "Hcg Hpc".
        iEval (rgne; rewrite Hs2 (nx_addi1 pv ii)) in "Hcg".
        set (E1 := <[Regidx Rs2 := regval_into_reg (pa_add pv (S ii))]> Ms).
        assert (HE1s2 : E1 !!! Regidx Rs2 = pa_add pv (S ii))
          by (rewrite /E1; apply upd_eq).
        assert (Hq108 : add_vec_int (mword_of_int (NX + 0x106) : mword 64) 2
                        = mword_of_int (NX + 0x108)) by pcw.
        iEval (rewrite Hq108) in "Hpc".
        (* +0x108 lbu a5,0(s2) *)
        iDestruct (nx_buf_acc pv dqp pfun (S plen) (S ii) ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0x108)) Ra5 Rs2
                  (mword_of_int 0 : mword 12) E1 (K - 12)%nat
                  (pfun (S ii) : mword 8) b (dqm := dqp)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj108 [Hpb] [-]").
        { iEval (rgne; rewrite HE1s2 addv_sext0). iExact "Hpb". }
        iIntros (CIDe2 Hqe2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite HE1s2 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        set (E2 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun (S ii) : mword 8))]> E1).
        assert (HE2a5 : E2 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun (S ii) : mword 8) : mword 64))
          by (rewrite /E2; apply upd_eq).
        assert (HE2s2 : E2 !!! Regidx Rs2 = pa_add pv (S ii))
          by (rewrite /E2 upd_ne; [exact HE1s2 | nz]).
        assert (Hq10c : add_vec_int (mword_of_int (NX + 0x108) : mword 64) 4
                        = mword_of_int (NX + 0x10c)) by pcw.
        iEval (rewrite Hq10c) in "Hpc".
        (* +0x10c addi a4,a5,-47 *)
        iApply (wp_addi4_s_sconf (mword_of_int (NX + 0x10c)) Ra4 Ra5
                  (mword_of_int 4049 : mword 12) E2 (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj10c").
        iIntros (CIDe3 Hqe3) "Hcg Hpc".
        iEval (rgne; rewrite HE2a5) in "Hcg".
        set (E3 := <[Regidx Ra4 := regval_into_reg
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
        assert (Hq110 : add_vec_int (mword_of_int (NX + 0x10c) : mword 64) 4
                        = mword_of_int (NX + 0x110)) by pcw.
        iEval (rewrite Hq110) in "Hpc".
        assert (Ht8c : add_vec (mword_of_int (NX + 0x110) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 190 : mword 8) ('b"0"))))
                = mword_of_int (NX + 0x8c)) by pcw.
        destruct (decide (pfun (S ii) = SLASH)) as [Hsl2 | Hsl2].
        + (* a separator: [c.beqz a4] leaves for +0x8c *)
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (NX + 0x110))
                    (mword_of_int 190 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                    E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HE3a4; exact (nx_a4_eq _ Hsl2))
                    ltac:(rewrite Ht8c; vm_compute; reflexivity)
                    with "Hcg Hpc Hj110").
          iIntros (CIDe4 Hqe4). iNext. iIntros "Hcg Hpc".
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
        + (* not a separator: [c.beqz a4] falls through to +0x112 *)
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x110))
                    (mword_of_int 190 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                    E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HE3a4; exact (nx_a4_ne _ Hsl2))
                    with "Hcg Hpc Hj110").
          iIntros (CIDe4 Hqe4) "Hcg Hpc".
          assert (Hq112 : add_vec_int (mword_of_int (NX + 0x110) : mword 64) 2
                          = mword_of_int (NX + 0x112)) by pcw.
          iEval (rewrite Hq112) in "Hpc".
          assert (Ht106 : add_vec (mword_of_int (NX + 0x112) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 250 : mword 8) ('b"0"))))
                  = mword_of_int (NX + 0x106)) by pcw.
          destruct (decide (pfun (S ii) = NUL)) as [Hnl2 | Hnl2].
          * (* the terminator: [c.bnez a5] falls through, +0x114 jumps *)
            iApply (wp_cbnez_fall_s_sconf (mword_of_int (NX + 0x112))
                      (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HE3a5; exact (nx_nnul_eq _ Hnl2))
                      with "Hcg Hpc Hj112").
            iIntros (CIDe5 Hqe5) "Hcg Hpc".
            assert (Hq114 : add_vec_int (mword_of_int (NX + 0x112) : mword 64) 2
                            = mword_of_int (NX + 0x114)) by pcw.
            iEval (rewrite Hq114) in "Hpc".
            assert (Ht8c2 : add_vec (mword_of_int (NX + 0x114) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 1980 : mword 11) ('b"0"))))
                    = mword_of_int (NX + 0x8c)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (NX + 0x114))
                      (sign_extend' 21
                         (concat_vec (mword_of_int 1980 : mword 11) ('b"0")))
                      E3 (K - 12)%nat b
                      ltac:(rewrite Ht8c2; vm_compute; reflexivity)
                      with "Hcg Hpc Hj114").
            iIntros (CIDe6 Hqe6). iNext. iIntros "Hcg Hpc".
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
          * (* an ordinary byte: [c.bnez a5] loops back to +0x106 *)
            iApply (wp_cbnez_taken_s_sconf (mword_of_int (NX + 0x112))
                      (mword_of_int 250 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      E3 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HE3a5; exact (nx_nnul_ne _ Hnl2))
                      ltac:(rewrite Ht106; vm_compute; reflexivity)
                      with "Hcg Hpc Hj112").
            iIntros (CIDe5 Hqe5). iNext. iIntros "Hcg Hpc".
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
    (* ---- (4) +0xf6 .. +0x104: the terminator test AND THE DEAD BLOCK ---
       Two exits, so TWO abstract continuations.  +0xf8..+0x102 re-loads the
       byte and re-tests it against '/' and 0 -- both were just decided, so
       both [c.beqz]es fall through and +0x116 is unreachable. *)
    iAssert (□ wp_next (CID0 := CID) b (proc_addr j) (fun CIDs : CpuId =>
               ∀ (a : nat) (Ms : regfile),
                 ⌜(a <= plen)%nat⌝ -∗
                 ⌜pfun a <> SLASH⌝ -∗
                 ⌜Ms !!! Regidx Rs1 = pa_add pv a⌝ -∗
                 ⌜Ms !!! Regidx Ra5
                    = (zero_extend' 64 (pfun a : mword 8) : mword 64)⌝ -∗
                 sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                 pc_is (mword_of_int (NX + 0xf6)) -∗
                 ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                 (* EXIT A -- the string is exhausted, at +0x130 *)
                 wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDa : CpuId =>
                   ⌜(a = plen)%nat⌝ -∗
                   sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                   pc_is (mword_of_int (NX + 0x130)) -∗
                   ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                   WP (Loop : expr riscv_lang)) -∗
                 (* EXIT B -- an element starts at [a], at +0x106 *)
                 wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDb : CpuId =>
                   ∀ Ms' : regfile,
                     ⌜(a < plen)%nat⌝ -∗
                     ⌜pfun a <> NUL⌝ -∗
                     ⌜Ms' !!! Regidx Rs1 = pa_add pv a⌝ -∗
                     ⌜Ms' !!! Regidx Rs2 = pa_add pv a⌝ -∗
                     ⌜forall c : mword 5, c <> Ra5 -> c <> Ra4 -> c <> Rs2 ->
                        Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
                     sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                     pc_is (mword_of_int (NX + 0x106)) -∗
                     ([∗ list] i ∈ seq 0 (S plen),
                        pa_add pv i ↦ₘ{dqp} pfun i) -∗
                     WP (Loop : expr riscv_lang)) -∗
                 WP (Loop : expr riscv_lang)))%I with "[]" as "#Hmid".
    { iModIntro.
      iIntros (CIDs Hss a Ms) "%Halt %Hns %Hs1 %Ha5 Hcg Hpc Hpath HqA HqB".
      iPoseProof (nxi_0f6 with "Htext") as "Hjf6".
      iPoseProof (nxi_0f8 with "Htext") as "Hjf8".
      iPoseProof (nxi_0fc with "Htext") as "Hjfc".
      iPoseProof (nxi_100 with "Htext") as "Hj100".
      iPoseProof (nxi_102 with "Htext") as "Hj102".
      iPoseProof (nxi_104 with "Htext") as "Hj104".
      assert (Ht130 : add_vec (mword_of_int (NX + 0xf6) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 29 : mword 8) ('b"0"))))
              = mword_of_int (NX + 0x130)) by pcw.
      destruct (decide (pfun a = NUL)) as [Hnl | Hnl].
      - (* the terminator: [c.beqz a5] leaves the walk for +0x130 *)
        iClear "HqB".
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (NX + 0xf6))
                  (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Ms (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Ha5; exact (nx_nul_eq _ Hnl))
                  ltac:(rewrite Ht130; vm_compute; reflexivity)
                  with "Hcg Hpc Hjf6").
        iIntros (CIDm1 Hqm1). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Ht130) in "Hpc".
        assert (Hap : (a = plen)%nat).
        { destruct (Nat.eq_dec a plen) as [He | Hne]; [exact He |].
          exfalso. exact (Hnn a ltac:(lia) Hnl). }
        iSpecialize ("HqA" $! CIDm1 with "[%]"); [wp_next_chain |].
        iApply ("HqA" with "[%] Hcg Hpc Hpath"). exact Hap.
      - (* an element begins here: fall into the DEAD block *)
        iClear "HqA".
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0xf6))
                  (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  Ms (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite Ha5; exact (nx_nul_ne _ Hnl))
                  with "Hcg Hpc Hjf6").
        iIntros (CIDm1 Hqm1) "Hcg Hpc".
        assert (Hqf8 : add_vec_int (mword_of_int (NX + 0xf6) : mword 64) 2
                       = mword_of_int (NX + 0xf8)) by pcw.
        iEval (rewrite Hqf8) in "Hpc".
        (* +0xf8 lbu a5,0(s1) -- the SAME byte, read again *)
        iDestruct (nx_buf_acc pv dqp pfun (S plen) a ltac:(lia)
                     with "Hpath") as "[Hpb Hpback]".
        iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xf8)) Ra5 Rs1
                  (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                  (pfun a : mword 8) b (dqm := dqp)
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjf8 [Hpb] [-]").
        { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
        iIntros (CIDm2 Hqm2) "Hcg Hpc Hpb".
        iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
        iDestruct ("Hpback" with "Hpb") as "Hpath".
        set (D1 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (pfun a : mword 8))]> Ms).
        assert (HD1a5 : D1 !!! Regidx Ra5
                        = (zero_extend' 64 (pfun a : mword 8) : mword 64))
          by (rewrite /D1; apply upd_eq).
        assert (HD1s1 : D1 !!! Regidx Rs1 = pa_add pv a)
          by (rewrite /D1 upd_ne; [exact Hs1 | nz]).
        assert (Hqfc : add_vec_int (mword_of_int (NX + 0xf8) : mword 64) 4
                       = mword_of_int (NX + 0xfc)) by pcw.
        iEval (rewrite Hqfc) in "Hpc".
        (* +0xfc addi a4,a5,-47 *)
        iApply (wp_addi4_s_sconf (mword_of_int (NX + 0xfc)) Ra4 Ra5
                  (mword_of_int 4049 : mword 12) D1 (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hjfc").
        iIntros (CIDm3 Hqm3) "Hcg Hpc".
        iEval (rgne; rewrite HD1a5) in "Hcg".
        set (D2 := <[Regidx Ra4 := regval_into_reg
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
        assert (Hq100 : add_vec_int (mword_of_int (NX + 0xfc) : mword 64) 4
                        = mword_of_int (NX + 0x100)) by pcw.
        iEval (rewrite Hq100) in "Hpc".
        (* +0x100 c.beqz a4 -- DEAD: the byte is not '/' *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x100))
                  (mword_of_int 11 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  D2 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD2a4; exact (nx_a4_ne _ Hns))
                  with "Hcg Hpc Hj100").
        iIntros (CIDm4 Hqm4) "Hcg Hpc".
        assert (Hq102 : add_vec_int (mword_of_int (NX + 0x100) : mword 64) 2
                        = mword_of_int (NX + 0x102)) by pcw.
        iEval (rewrite Hq102) in "Hpc".
        (* +0x102 c.beqz a5 -- DEAD: the byte is not the terminator *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (NX + 0x102))
                  (mword_of_int 10 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  D2 (K - 12)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HD2a5; exact (nx_nul_ne _ Hnl))
                  with "Hcg Hpc Hj102").
        iIntros (CIDm5 Hqm5) "Hcg Hpc".
        assert (Hq104 : add_vec_int (mword_of_int (NX + 0x102) : mword 64) 2
                        = mword_of_int (NX + 0x104)) by pcw.
        iEval (rewrite Hq104) in "Hpc".
        (* +0x104 c.mv s2,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x104)) Rs2 Rs1
                  D2 (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj104").
        iIntros (CIDm6 Hqm6) "Hcg Hpc". iEval (rgne) in "Hcg".
        iEval (rewrite HD2s1) in "Hcg".
        set (D3 := <[Regidx Rs2 := regval_into_reg
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
        assert (Hq106 : add_vec_int (mword_of_int (NX + 0x104) : mword 64) 2
                        = mword_of_int (NX + 0x106)) by pcw.
        iEval (rewrite Hq106) in "Hpc".
        iSpecialize ("HqB" $! CIDm6 with "[%]"); [wp_next_chain |].
        iApply ("HqB" $! D3 with "[%] [%] [%] [%] [%] Hcg Hpc Hpath").
        + exact (Hnult a Halt Hnl).
        + exact Hnl.
        + exact HD3s1.
        + exact HD3s2.
        + exact HD3o. }
    (* ---- (5) +0xe4 .. +0x104: the whole loop head -------------------- *)
    iAssert (□ wp_next (CID0 := CID) b (proc_addr j) (fun CIDs : CpuId =>
               ∀ (off : nat) (Ms : regfile),
                 ⌜(off <= plen)%nat⌝ -∗
                 ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
                 ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
                 sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                 pc_is (mword_of_int (NX + 0xe4)) -∗
                 ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                 (* EXIT A -- nothing but separators left, at +0x130 *)
                 wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDa : CpuId =>
                   ∀ Ms' : regfile,
                     ⌜forall i : nat, (off <= i)%nat -> (i < plen)%nat ->
                        pfun i = SLASH⌝ -∗
                     ⌜Ms' !!! Regidx Rs1 = pa_add pv plen⌝ -∗
                     ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
                        Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
                     sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                     pc_is (mword_of_int (NX + 0x130)) -∗
                     ([∗ list] i ∈ seq 0 (S plen),
                        pa_add pv i ↦ₘ{dqp} pfun i) -∗
                     WP (Loop : expr riscv_lang)) -∗
                 (* EXIT B -- an element starts at [a], at +0x106 *)
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
                     sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                     pc_is (mword_of_int (NX + 0x106)) -∗
                     ([∗ list] i ∈ seq 0 (S plen),
                        pa_add pv i ↦ₘ{dqp} pfun i) -∗
                     WP (Loop : expr riscv_lang)) -∗
                 WP (Loop : expr riscv_lang)))%I with "[]" as "#Hhead".
    { iModIntro.
      iIntros (CIDs Hss off Ms) "%Holt %Hs1 %Hs3 Hcg Hpc Hpath HqA HqB".
      iPoseProof (nxi_0e4 with "Htext") as "Hje4".
      iPoseProof (nxi_0e8 with "Htext") as "Hje8".
      (* +0xe4 lbu a5,0(s1) *)
      iDestruct (nx_buf_acc pv dqp pfun (S plen) off ltac:(lia)
                   with "Hpath") as "[Hpb Hpback]".
      iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xe4)) Ra5 Rs1
                (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                (pfun off : mword 8) b (dqm := dqp)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hje4 [Hpb] [-]").
      { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
      iIntros (CIDh1 Hqh1) "Hcg Hpc Hpb".
      iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
      iDestruct ("Hpback" with "Hpb") as "Hpath".
      set (H1 := <[Regidx Ra5 := regval_into_reg
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
      assert (Hqe8 : add_vec_int (mword_of_int (NX + 0xe4) : mword 64) 4
                     = mword_of_int (NX + 0xe8)) by pcw.
      iEval (rewrite Hqe8) in "Hpc".
      assert (Htf6 : add_vec (mword_of_int (NX + 0xe8) : mword 64)
                (sign_extend' 64 (mword_of_int 14 : mword 13))
              = mword_of_int (NX + 0xf6)) by pcw.
      destruct (decide (pfun off = SLASH)) as [Hsl0 | Hsl0].
      - (* a separator: [bne] falls through into the skip at +0xec *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xe8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 H1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HH1a5 HH1s3;
                        exact (nx_nslash_eq _ Hsl0))
                  with "Hcg Hpc Hje8").
        iIntros (CIDh2 Hqh2) "Hcg Hpc".
        assert (Hqec : add_vec_int (mword_of_int (NX + 0xe8) : mword 64) 4
                       = mword_of_int (NX + 0xec)) by pcw.
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
      - (* not a separator: [bne] is taken straight to +0xf6 *)
        iApply (wp_bne_taken_s_sconf (mword_of_int (NX + 0xe8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 H1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HH1a5 HH1s3;
                        exact (nx_nslash_ne _ Hsl0))
                  ltac:(rewrite Htf6; vm_compute; reflexivity)
                  with "Hcg Hpc Hje8").
        iIntros (CIDh2 Hqh2). iNext. iIntros "Hcg Hpc".
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
    (* ---- (6) +0xa4 .. +0xb2: skipelem's TRAILING separator skip -------
       reached from BOTH memmove branches, with [s1 = s2] the index just
       past the element; it ends at +0xb6, where ilock's argument is set up.
       Same two-instruction head as (5), one exit instead of two. *)
    iAssert (□ wp_next (CID0 := CID) b (proc_addr j) (fun CIDs : CpuId =>
               ∀ (off : nat) (Ms : regfile),
                 ⌜(off <= plen)%nat⌝ -∗
                 ⌜Ms !!! Regidx Rs1 = pa_add pv off⌝ -∗
                 ⌜Ms !!! Regidx Rs3 = (mword_of_int 47 : mword 64)⌝ -∗
                 sie_cap_gpr Ms (K - 12)%nat b (proc_addr j) -∗
                 pc_is (mword_of_int (NX + 0xa4)) -∗
                 ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                 wp_next (CID0 := CIDs) b (proc_addr j) (fun CIDe : CpuId =>
                   ∀ (off' : nat) (Ms' : regfile),
                     ⌜(off <= off')%nat⌝ -∗ ⌜(off' <= plen)%nat⌝ -∗
                     ⌜forall i : nat, (off <= i)%nat -> (i < off')%nat ->
                        pfun i = SLASH⌝ -∗
                     ⌜pfun off' <> SLASH⌝ -∗
                     ⌜Ms' !!! Regidx Rs1 = pa_add pv off'⌝ -∗
                     ⌜forall c : mword 5, c <> Rs1 -> c <> Ra5 ->
                        Ms' !!! Regidx c = (Ms !!! Regidx c : mword 64)⌝ -∗
                     sie_cap_gpr Ms' (K - 12)%nat b (proc_addr j) -∗
                     pc_is (mword_of_int (NX + 0xb6)) -∗
                     ([∗ list] i ∈ seq 0 (S plen),
                        pa_add pv i ↦ₘ{dqp} pfun i) -∗
                     WP (Loop : expr riscv_lang)) -∗
                 WP (Loop : expr riscv_lang)))%I with "[]" as "#Htrail".
    { iModIntro.
      iIntros (CIDs Hss off Ms) "%Holt %Hs1 %Hs3 Hcg Hpc Hpath Hqc".
      iPoseProof (nxi_0a4 with "Htext") as "Hja4".
      iPoseProof (nxi_0a8 with "Htext") as "Hja8".
      (* +0xa4 lbu a5,0(s1) *)
      iDestruct (nx_buf_acc pv dqp pfun (S plen) off ltac:(lia)
                   with "Hpath") as "[Hpb Hpback]".
      iApply (wp_lbu_s_sconf (mword_of_int (NX + 0xa4)) Ra5 Rs1
                (mword_of_int 0 : mword 12) Ms (K - 12)%nat
                (pfun off : mword 8) b (dqm := dqp)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hja4 [Hpb] [-]").
      { iEval (rgne; rewrite Hs1 addv_sext0). iExact "Hpb". }
      iIntros (CIDr1 Hqr1) "Hcg Hpc Hpb".
      iEval (rgne; rewrite Hs1 addv_sext0) in "Hpb".
      iDestruct ("Hpback" with "Hpb") as "Hpath".
      set (G1 := <[Regidx Ra5 := regval_into_reg
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
      assert (Hqa8 : add_vec_int (mword_of_int (NX + 0xa4) : mword 64) 4
                     = mword_of_int (NX + 0xa8)) by pcw.
      iEval (rewrite Hqa8) in "Hpc".
      assert (Htb6 : add_vec (mword_of_int (NX + 0xa8) : mword 64)
                (sign_extend' 64 (mword_of_int 14 : mword 13))
              = mword_of_int (NX + 0xb6)) by pcw.
      destruct (decide (pfun off = SLASH)) as [Hsl0 | Hsl0].
      - iApply (wp_bne_fall_s_sconf (mword_of_int (NX + 0xa8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 G1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HG1a5 HG1s3;
                        exact (nx_nslash_eq _ Hsl0))
                  with "Hcg Hpc Hja8").
        iIntros (CIDr2 Hqr2) "Hcg Hpc".
        assert (Hqac : add_vec_int (mword_of_int (NX + 0xa8) : mword 64) 4
                       = mword_of_int (NX + 0xac)) by pcw.
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
      - iApply (wp_bne_taken_s_sconf (mword_of_int (NX + 0xa8))
                  (mword_of_int 14 : mword 13) Rs3 Ra5 G1 (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HG1a5 HG1s3;
                        exact (nx_nslash_ne _ Hsl0))
                  ltac:(rewrite Htb6; vm_compute; reflexivity)
                  with "Hcg Hpc Hja8").
        iIntros (CIDr2 Hqr2). iNext. iIntros "Hcg Hpc".
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
    (*  THE WALK at +0xe4.  ProofKexit's [forall fuel, wp_next] shape over *)
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
    iAssert (∀ fuel : nat,
      wp_next (CID0 := CID) b (proc_addr j) (fun CIDl : CpuId =>
        ∀ (off : nat) (ipv : mword 64) (Ml : regfile) (ncur : nat)
          (usedc : gset Z) (es0 : list (list (bv 8))) (nf : nat -> bv 8),
          ⌜(plen - off <= fuel)%nat⌝ -∗
          ⌜(off <= plen)%nat⌝ -∗
          ⌜path_elems pl = es0 ++ path_elems (drop off pl)⌝ -∗
          ⌜((length (path_elems (drop off pl)) + 1) * iput_units <= ncur)%nat⌝ -∗
          ⌜((n - (L + 1) * iput_units)%nat
              <= (ncur - (length (path_elems (drop off pl)) + 1)
                         * iput_units)%nat)%nat⌝ -∗
          ⌜(ncur <= n)%nat⌝ -∗
          ⌜usedc ⊆ used⌝ -∗
          ⌜nx_regs m sp0 (pa_add pv off) ipv nb
                   (m !!! Regidx Ra1 : mword 64) Ml⌝ -∗
          sie_cap_gpr Ml (K - 12)%nat b (proc_addr j) -∗
          cpu_own 0 eb (proc_addr j) C b -∗
          pc_is (mword_of_int (NX + 0xe4)) -∗
          (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
          (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
          (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
          (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
          (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
          (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
          (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
          (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
          (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
          (pa_stk sp0 10) ↦₈ (m !!! Regidx Rs8 : mword 64) -∗
          (pa_stk sp0 11) ↦₈ (m !!! Regidx Rs9 : mword 64) -∗
          (pa_stk sp0 12) ↦₈ (m !!! Regidx Rs10 : mword 64) -∗
          inode_held ipv -∗
          iref_slots 1 -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          bitmap_res gfs bmapstart cov logstart size usedc -∗
          p_pid (proc_addr j) ↦₄{dq} pidv -∗
          p_cwd (proc_addr j) ↦₈{dqc} cwdv -∗
          inode_held cwdv -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
          ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nf i) -∗
          bslots bn 3 -∗
          log_op g ncur -∗
          (* ---- THE CONTRACT'S OWN CONTINUATION, at the loop's hart ---- *)
          wp_next (CID0 := CIDl) b (proc_addr j) (fun CIDc : CpuId =>
            ∀ (mf : regfile) (n' : nat) (used' : gset Z)
              (ok : bool) (nf' : nat -> bv 8) (ipr : mword 64),
                ⌜callee_saved m mf⌝ -∗
                sie_cap_gpr mf K b (proc_addr j) -∗
                cpu_own 0 eb (proc_addr j) C b -∗
                pc_is ret_tgt -∗
                sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                ⌜used' ⊆ used⌝ -∗
                bitmap_res gfs bmapstart cov logstart size used' -∗
                p_pid (proc_addr j) ↦₄{dq} pidv -∗
                p_cwd (proc_addr j) ↦₈{dqc} cwdv -∗
                inode_held cwdv -∗
                ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ{dqp} pfun i) -∗
                ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ nf' i) -∗
                bslots bn 3 -∗
                ⌜((n - (L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
                log_op g n' -∗
                (if ok
                 then ⌜mf !!! Regidx Ra0 = ipr
                       /\ (npar = true ->
                           exists es e, nameiparent_of pl es e
                                        /\ bname 14 nf' = e)⌝ ∗
                      inode_held ipr ∗
                      iref_slots 1
                 else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗
                      iref_slots 2) -∗
                WP (Loop : expr riscv_lang)) -∗
          WP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
    { exact (cheat_ _). }
    iPoseProof (nxi_01c with "Htext") as "Hi01c".
    iPoseProof (nxi_01e with "Htext") as "Hi01e".
    iPoseProof (nxi_020 with "Htext") as "Hi020".
    iPoseProof (nxi_022 with "Htext") as "Hi022".
    iPoseProof (nxi_026 with "Htext") as "Hi026".
    iPoseProof (nxi_02a with "Htext") as "Hi02a".
    iPoseProof (nxi_03c with "Htext") as "Hi03c".
    iPoseProof (nxi_040 with "Htext") as "Hi040".
    iPoseProof (nxi_042 with "Htext") as "Hi042".
    iPoseProof (nxi_044 with "Htext") as "Hi044".
    iPoseProof (nxi_046 with "Htext") as "Hi046".
    (* ===== +0x1c c.mv s1,a0 : s1 := path ===== *)
    assert (HR2a0 : R2 !!! Regidx Ra0 = pv)
      by exact (HR2c Ra0 ltac:(nz) ltac:(nz)).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64))
      by exact (HR2c Ra1 ltac:(nz) ltac:(nz)).
    assert (HR2a2 : R2 !!! Regidx Ra2 = nb)
      by exact (HR2c Ra2 ltac:(nz) ltac:(nz)).
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1c)) Rs1 Ra0 R2 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi01c").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = pv).
    { rewrite /R3 upd_eq. rewrite HR2a0. apply add_vec_zero_l. }
    assert (Hpp01e : add_vec_int (mword_of_int (NX + 0x1c) : mword 64) 2
                     = mword_of_int (NX + 0x1e)) by pcw.
    iEval (rewrite Hpp01e) in "Hpc".
    (* ===== +0x1e c.mv s6,a1 : s6 := nameiparent ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x1e)) Rs6 Ra1 R3 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi01e").
    iIntros (CID16 Hq16) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs6 := regval_into_reg
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
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi020").
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs5 := regval_into_reg
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
    iDestruct (nx_buf_acc pv dqp pfun (S plen) 0 ltac:(lia) with "Hpath")
      as "[Hp0 Hpback]".
    iEval (rewrite pa_add_0) in "Hp0".
    iApply (wp_lbu_s_sconf (mword_of_int (NX + 0x22)) Ra4 Ra0
              (mword_of_int 0 : mword 12) R5 (K - 12)%nat (pfun 0%nat) b (dqm:=dqp)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi022 [Hp0] [-]").
    { iEval (rgne; rewrite HR5a0 addv_sext0). iExact "Hp0". }
    iIntros (CID18 Hq18) "Hcg Hpc Hp0".
    iEval (rgne; rewrite HR5a0 addv_sext0) in "Hp0".
    iEval (rewrite -(pa_add_0 pv)) in "Hp0".
    iDestruct ("Hpback" with "Hp0") as "Hpath".
    set (R6 := <[Regidx Ra4 := regval_into_reg
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
              with "Hcg Hpc Hi026").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (R7 := <[Regidx Ra5 := regval_into_reg (mword_of_int 47 : mword 64)]> R6).
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
      iPoseProof (nxi_048 with "Htext") as "Hi048".
      iPoseProof (nxi_04a with "Htext") as "Hi04a".
      iPoseProof (nxi_04c with "Htext") as "Hi04c".
      iPoseProof (nxi_050 with "Htext") as "Hi050".
      iPoseProof (nxi_052 with "Htext") as "Hi052".
      iApply (wp_beq_taken_s_sconf (mword_of_int (NX + 0x2a))
                (mword_of_int 30 : mword 13) Ra5 Ra4 R7 (K - 12)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR7a4 HR7a5; exact (nx_slash_eq _ Hsl0))
                ltac:(rewrite Htgt048; vm_compute; reflexivity)
                with "Hcg Hpc Hi02a").
      iIntros (CID20 Hq20). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt048) in "Hpc".
      (* +0x48 c.li a1,1 *)
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x48)) Ra1 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) R7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi048").
      iIntros (CID21 Hq21) "Hcg Hpc".
      set (A1 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> R7).
      assert (HA1a1 : A1 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /A1; apply upd_eq).
      assert (Hpp04a : add_vec_int (mword_of_int (NX + 0x48) : mword 64) 2
                       = mword_of_int (NX + 0x4a)) by pcw.
      iEval (rewrite Hpp04a) in "Hpc".
      (* +0x4a c.mv a0,a1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x4a)) Ra0 Ra1 A1 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04a").
      iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A2 := <[Regidx Ra0 := regval_into_reg
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
                         (sign_extend' 64 (mword_of_int 2094838 : mword 21))
                       = mword_of_int KernelSyms.iget) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x4c)) Rra
                (mword_of_int 2094838 : mword 21) A2 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi04c").
      iIntros (CID23 Hq23) "Hcg Hpc".
      iEval (rewrite Htgtig) in "Hpc".
      set (A3 := <[Regidx Rra := regval_into_reg
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
      iDestruct (cpu_own_transport CID CID23 0%nat eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID23)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (IG.wp_iget_sconf gtl cn gfs gi cov logstart nib dev ROOTINO
                A3 0%nat eb (proc_addr j) C (K - 12)%nat b
                Kig ltac:(vm_compute; reflexivity)
                Hrino HA3a0 HA3a1
                with "Hcg Hcnt Htext Hpc Hitb2 Hitbl Hesc Hpanic Hisl1").
      iIntros (CIDig Hqig mig kig qig) "Hcg Hcnt Hpc %Higp Href".
      destruct Higp as (Hcsig & Hkig & Higa0).
      assert (Hpc050 : ret_pc (A3 !!! Regidx Rra) = mword_of_int (NX + 0x50)).
      { rewrite HA3ra. pcw. }
      iEval (rewrite Hpc050) in "Hpc".
      (* +0x50 c.mv s4,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x50)) Rs4 Ra0 mig (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi050").
      iIntros (CIDA1 HqA1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A4 := <[Regidx Rs4 := regval_into_reg
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
                with "Hcg Hpc Hi052").
      iIntros (CIDA2 HqA2). iNext. iIntros "Hcg Hpc".
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
      iAssert (inode_held (ientry kig)) with "[Href]" as "Hip".
      { rewrite /inode_held. iExists kig, qig, ROOTINO.
        iSplitR; [done |]. iSplitR; [iPureIntro; exact Hkig |].
        iSplitR; [iPureIntro; rewrite -Hnib; exact Hrino |].
        rewrite -Hdev. iExact "Href". }
      (* ===== +0x3c .. +0x46 : the four constants, then [c.j +0xe4] ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (NX + 0x3c)) Rs3
                (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
                A4 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi03c").
      iIntros (CIDK1 HqK1) "Hcg Hpc".
      set (A5 := <[Regidx Rs3 := regval_into_reg (mword_of_int 47 : mword 64)]> A4).
      assert (HpA040 : add_vec_int (mword_of_int (NX + 0x3c) : mword 64) 4
                       = mword_of_int (NX + 0x40)) by pcw.
      iEval (rewrite HpA040) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x40)) Rs8 (mword_of_int 13 : mword 6)
                (mword_of_int 13 : mword 64) A5 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi040").
      iIntros (CIDK2 HqK2) "Hcg Hpc".
      set (A6 := <[Regidx Rs8 := regval_into_reg (mword_of_int 13 : mword 64)]> A5).
      assert (HpA042 : add_vec_int (mword_of_int (NX + 0x40) : mword 64) 2
                       = mword_of_int (NX + 0x42)) by pcw.
      iEval (rewrite HpA042) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x42)) Rs9 (mword_of_int 14 : mword 6)
                (mword_of_int 14 : mword 64) A6 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi042").
      iIntros (CIDK3 HqK3) "Hcg Hpc".
      set (A7 := <[Regidx Rs9 := regval_into_reg (mword_of_int 14 : mword 64)]> A6).
      assert (HpA044 : add_vec_int (mword_of_int (NX + 0x42) : mword 64) 2
                       = mword_of_int (NX + 0x44)) by pcw.
      iEval (rewrite HpA044) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x44)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) A7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi044").
      iIntros (CIDK4 HqK4) "Hcg Hpc".
      set (A8 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> A7).
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
      (* +0x46 c.j +0xe4 : into the walk *)
      assert (HtgtA0e4 : add_vec (mword_of_int (NX + 0x46) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 79 : mword 11) ('b"0"))))
                = mword_of_int (NX + 0xe4)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (NX + 0x46))
                (sign_extend' 21 (concat_vec (mword_of_int 79 : mword 11) ('b"0")))
                A8 (K - 12)%nat b
                ltac:(rewrite HtgtA0e4; vm_compute; reflexivity)
                with "Hcg Hpc Hi046").
      iIntros (CIDK5 HqK5). iNext. iIntros "Hcg Hpc".
      iEval (rewrite HtgtA0e4) in "Hpc".
      (* ---- ENTER THE WALK at off = 0, es0 = [], ncur = n ---- *)
      iDestruct (cpu_own_transport CIDig CIDK5 0%nat eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID23) (CIDb := CIDK5)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iSpecialize ("Hloop" $! (S plen) CIDK5 with "[%]"); [wp_next_chain |].
      iApply ("Hloop" $! 0%nat (ientry kig) A8 n used [] nfun
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc
                      Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                      Hip Hisl2 Hbmap Hinos Hbits Hppid Hcwdc Hcwdr Hpath
                      Hname Hbslot Hlog Hcont").
      - lia.
      - lia.
      - rewrite drop_0. reflexivity.
      - rewrite drop_0. exact Hbud.
      - rewrite drop_0. lia.
      - lia.
      - reflexivity.
      - rewrite pa_add_0. exact HAregs.
    + (* ---------------- THE RELATIVE ARM: idup(myproc()->cwd) ---------- *)
      iPoseProof (nxi_02e with "Htext") as "Hi02e".
      iPoseProof (nxi_032 with "Htext") as "Hi032".
      iPoseProof (nxi_036 with "Htext") as "Hi036".
      iPoseProof (nxi_03a with "Htext") as "Hi03a".
      iApply (wp_beq_fall_s_sconf (mword_of_int (NX + 0x2a))
                (mword_of_int 30 : mword 13) Ra5 Ra4 R7 (K - 12)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HR7a4 HR7a5; exact (nx_slash_ne _ Hsl0))
                with "Hcg Hpc Hi02a").
      iIntros (CID20 Hq20) "Hcg Hpc".
      assert (Hpp02e : add_vec_int (mword_of_int (NX + 0x2a) : mword 64) 4
                       = mword_of_int (NX + 0x2e)) by pcw.
      iEval (rewrite Hpp02e) in "Hpc".
      (* +0x2e jal ra,myproc *)
      assert (Htgtmp : add_vec (mword_of_int (NX + 0x2e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2089136 : mword 21))
                       = mword_of_int KernelSyms.myproc) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x2e)) Rra
                (mword_of_int 2089136 : mword 21) R7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi02e").
      iIntros (CID21 Hq21) "Hcg Hpc".
      iEval (rewrite Htgtmp) in "Hpc".
      set (B1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (NX + 0x2e) : mword 64) 4)]> R7).
      assert (HB1ra : B1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (NX + 0x2e) : mword 64) 4)
        by (rewrite /B1; apply upd_eq).
      iDestruct (cpu_own_transport CID CID21 0%nat eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID21)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (MP.wp_myproc_sconf B1 (K - 12)%nat 0%nat eb (proc_addr j) C b
                ltac:(vm_compute; reflexivity) Kmp
                with "Hcg Hcnt Htext Hpc").
      iIntros (CIDmp Hqmp msv mf1) "%Hmsf Hcg Hcnt Hpc %Hmpp".
      destruct Hmpp as [Hcsmp Hmpa0].
      assert (Hpc032 : ret_pc (B1 !!! Regidx Rra) = mword_of_int (NX + 0x32)).
      { rewrite HB1ra. pcw. }
      iEval (rewrite Hpc032) in "Hpc".
      (* +0x32 ld a0,336(a0) : a0 := p->cwd *)
      iApply (wp_ld_s_sconf (mword_of_int (NX + 0x32)) Ra0 Ra0
                (mword_of_int 336 : mword 12) mf1 (K - 12)%nat cwdv b (dqm := dqc)
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi032 [Hcwdc] [-]").
      { iEval (rgne; rewrite Hmpa0 p_cwd_sext). iExact "Hcwdc". }
      iIntros (CID22 Hq22) "Hcg Hpc Hcwdc".
      iEval (rgne; rewrite Hmpa0 p_cwd_sext) in "Hcwdc".
      set (B2 := <[Regidx Ra0 := regval_into_reg cwdv]> mf1).
      assert (HB2a0 : B2 !!! Regidx Ra0 = cwdv)
        by (rewrite /B2; apply upd_eq).
      assert (Hpp036 : add_vec_int (mword_of_int (NX + 0x32) : mword 64) 4
                       = mword_of_int (NX + 0x36)) by pcw.
      iEval (rewrite Hpp036) in "Hpc".
      (* ---- THE SHED: the cwd reference lends a share to idup ---- *)
      iDestruct "Hcwdr" as (ck cq cinum) "(%Hcwde & %Hckl & %Hcinb & Hcref)".
      iEval (rewrite -Hdev) in "Hcref".
      rewrite inode_ref_shed.
      iDestruct "Hcref" as "[Hckeep Hcshr]".
      (* +0x36 jal ra,idup *)
      assert (Htgtid : add_vec (mword_of_int (NX + 0x36) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095432 : mword 21))
                       = mword_of_int KernelSyms.idup) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (NX + 0x36)) Rra
                (mword_of_int 2095432 : mword 21) B2 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi036").
      iIntros (CID23 Hq23) "Hcg Hpc".
      iEval (rewrite Htgtid) in "Hpc".
      set (B3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (NX + 0x36) : mword 64) 4)]> B2).
      assert (HB3ra : B3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (NX + 0x36) : mword 64) 4)
        by (rewrite /B3; apply upd_eq).
      assert (HB3a0 : B3 !!! Regidx Ra0 = ientry ck).
      { rewrite /B3 upd_ne; [| nz]. rewrite HB2a0. exact Hcwde. }
      iDestruct (cpu_own_transport CIDmp CID23 0%nat eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID21) (CIDb := CID23)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (ID.wp_idup_sconf gtl cn gfs gi cov logstart nib
                ck (cq/2)%Qp dev cinum
                B3 0%nat eb (proc_addr j) C (K - 12)%nat b
                Kid ltac:(vm_compute; reflexivity) Hckl HB3a0
                with "Hcg Hcnt Htext Hpc Hitb2 Hitbl Hpanic Hisl1 Hcshr").
      iIntros (CIDid Hqid mid) "Hcg Hcnt Hpc %Hidp Hcshr (%qn & Href)".
      destruct Hidp as [Hcsid Hida0].
      (* ---- THE GATHER: the cwd reference is whole again ---- *)
      iDestruct (inode_ref_gather ck (cq/2)%Qp (cq/2)%Qp dev cinum
                   with "Hckeep Hcshr") as "Hcref".
      iEval (rewrite Qp.div_2) in "Hcref".
      iAssert (inode_held cwdv) with "[Hcref]" as "Hcwdr".
      { rewrite /inode_held. iExists ck, cq, cinum.
        iSplitR; [iPureIntro; exact Hcwde |].
        iSplitR; [iPureIntro; exact Hckl |].
        iSplitR; [iPureIntro; exact Hcinb |]. rewrite -Hdev. iExact "Hcref". }
      assert (Hpc03a : ret_pc (B3 !!! Regidx Rra) = mword_of_int (NX + 0x3a)).
      { rewrite HB3ra. pcw. }
      iEval (rewrite Hpc03a) in "Hpc".
      (* +0x3a c.mv s4,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (NX + 0x3a)) Rs4 Ra0 mid (K - 12)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi03a").
      iIntros (CIDBm1 HqBm1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B4 := <[Regidx Rs4 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (mid !!! Regidx Ra0))]> mid).
      assert (HB4s4 : B4 !!! Regidx Rs4 = ientry ck).
      { rewrite /B4 upd_eq. rewrite Hida0. apply add_vec_zero_l. }
      (* the walk's starting reference *)
      iAssert (inode_held (ientry ck)) with "[Href]" as "Hip".
      { rewrite /inode_held. iExists ck, qn, cinum.
        iSplitR; [done |]. iSplitR; [iPureIntro; exact Hckl |].
        iSplitR; [iPureIntro; exact Hcinb |]. rewrite -Hdev. iExact "Href". }
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
      (* ===== +0x3c .. +0x46 : the four constants, then [c.j +0xe4] ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (NX + 0x3c)) Rs3
                (mword_of_int 47 : mword 12) (mword_of_int 47 : mword 64)
                B4 (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi03c").
      iIntros (CIDB1 HqB1) "Hcg Hpc".
      set (B5 := <[Regidx Rs3 := regval_into_reg (mword_of_int 47 : mword 64)]> B4).
      assert (HpB040 : add_vec_int (mword_of_int (NX + 0x3c) : mword 64) 4
                       = mword_of_int (NX + 0x40)) by pcw.
      iEval (rewrite HpB040) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x40)) Rs8 (mword_of_int 13 : mword 6)
                (mword_of_int 13 : mword 64) B5 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi040").
      iIntros (CIDB2 HqB2) "Hcg Hpc".
      set (B6 := <[Regidx Rs8 := regval_into_reg (mword_of_int 13 : mword 64)]> B5).
      assert (HpB042 : add_vec_int (mword_of_int (NX + 0x40) : mword 64) 2
                       = mword_of_int (NX + 0x42)) by pcw.
      iEval (rewrite HpB042) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x42)) Rs9 (mword_of_int 14 : mword 6)
                (mword_of_int 14 : mword 64) B6 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi042").
      iIntros (CIDB3 HqB3) "Hcg Hpc".
      set (B7 := <[Regidx Rs9 := regval_into_reg (mword_of_int 14 : mword 64)]> B6).
      assert (HpB044 : add_vec_int (mword_of_int (NX + 0x42) : mword 64) 2
                       = mword_of_int (NX + 0x44)) by pcw.
      iEval (rewrite HpB044) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (NX + 0x44)) Rs7 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) B7 (K - 12)%nat b
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi044").
      iIntros (CIDB4 HqB4) "Hcg Hpc".
      set (B8 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1 : mword 64)]> B7).
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
      (* +0x46 c.j +0xe4 : into the walk *)
      assert (HtgtB0e4 : add_vec (mword_of_int (NX + 0x46) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 79 : mword 11) ('b"0"))))
                = mword_of_int (NX + 0xe4)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (NX + 0x46))
                (sign_extend' 21 (concat_vec (mword_of_int 79 : mword 11) ('b"0")))
                B8 (K - 12)%nat b
                ltac:(rewrite HtgtB0e4; vm_compute; reflexivity)
                with "Hcg Hpc Hi046").
      iIntros (CIDB5 HqB5). iNext. iIntros "Hcg Hpc".
      iEval (rewrite HtgtB0e4) in "Hpc".
      (* ---- ENTER THE WALK at off = 0, es0 = [], ncur = n ---- *)
      iDestruct (cpu_own_transport CIDid CIDB5 0%nat eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID23) (CIDb := CIDB5)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iSpecialize ("Hloop" $! (S plen) CIDB5 with "[%]"); [wp_next_chain |].
      iApply ("Hloop" $! 0%nat (ientry ck) B8 n used [] nfun
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc
                      Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12
                      Hip Hisl2 Hbmap Hinos Hbits Hppid Hcwdc Hcwdr Hpath
                      Hname Hbslot Hlog Hcont").
      - lia.
      - lia.
      - rewrite drop_0. reflexivity.
      - rewrite drop_0. exact Hbud.
      - rewrite drop_0. lia.
      - lia.
      - reflexivity.
      - rewrite pa_add_0. exact HBregs.
  Qed.

End ProofNamexMain.

End NamexProof.
