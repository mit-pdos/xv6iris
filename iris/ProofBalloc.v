(* ProofBalloc.v -- balloc over the SIE-agnostic sconf world.

     static uint balloc(uint dev) {
       int b, bi, m;  struct buf *bp = 0;
       for(b = 0; b < sb.size; b += BPB){
         bp = bread(dev, BBLOCK(b, sb));
         for(bi = 0; bi < BPB && b + bi < sb.size; bi++){
           m = 1 << (bi % 8);
           if((bp->data[bi/8] & m) == 0){
             bp->data[bi/8] |= m;
             log_write(bp); brelse(bp); bzero(dev, b + bi);
             return b + bi; } }
         brelse(bp); }
       printf("balloc: out of blocks\n");
       return 0;
     }

   THE SHAPE OF THE PROOF.  Five block lemmas, entered strictly right to
   left, plus one induction:

     [ba_epilogue]  +0x7e .. +0x88   a0 := s1, pop ra/s0/s1, pop the frame,
                                     ret, and discharge the contract.  BOTH
                                     arms land here, each carrying its half
                                     of [ba_arms] as one resource.
     [ba_out]       +0xe8 .. +0x104  pop s2..s8, printk, s1 := 0, and jump
                                     back to +0x7e.
     [ba_alloc]     +0x38 .. +0x7c   set the bit, log_write, brelse, then
                                     the INLINED bzero (bread / memset /
                                     log_write / brelse), pop s2..s8.
     [ba_exhaust]   +0x8a .. +0x98   brelse, b += BPB, reload sb.size, and
                                     the [bgeu] that always jumps to +0xe8.
     [ba_scan]      +0xb6 .. +0xe6   THE ONLY LOOP, by induction on the fuel
                                     [Z.to_nat (BPB - bi)].
     [wp_balloc_sconf] +0x00 .. +0xb4

   ONE BITMAP BLOCK.  [FSSIZE = 2000 < BPB = 8192] and the contract premises
   [0 < size <= BPB], so the OUTER loop runs a single iteration: b starts at
   0, [sraiw a1,s5,0xd] at +0x9c yields 0 and BBLOCK collapses
   ([BitmapInv.BBLOCK_single]), and after [addw s5,s8,s5] at +0x90 we have
   b = BPB >= size, so the [bgeu] at +0x98 is ALWAYS taken.  Both dead arms
   are refuted rather than proved:

     - +0x12 [beqz a5,+0xf6] -- the [sb.size == 0] jump straight to the
       printk, which would skip the s2..s8 restore.  [0 < size] makes the
       loaded word nonzero, so the branch falls through.
     - +0x98's FALL-THROUGH (a second outer iteration).  [size <= BPB] makes
       [BPB >= size] unconditionally, so only the taken arm exists.

   THE OUT-OF-BLOCKS ARM IS LIVE and calls printk on its GENERAL path (at
   balloc time [panicking] is 0, so [SpecPrintk]'s panic-path contract does
   not apply).  Its contract arrives as the PURE hypothesis
   [SpecPrintk.printk_gen_contract] rather than as a functor argument,
   which is what keeps [Print Assumptions] on the linked theorem at the
   standing six: [LinkPrintk]'s only instance is itself an [Axiom], and a
   functor would import it here.  The format string is minted out of the
   [kernel_data] premise by [KernelDataInv.kernel_data_string]; it takes no
   varargs, so [descs = []].                                              *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers dfrac.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import ByteBuf.
Require Import PrintintArith.
Require Import PrintkFmt.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeSlot.
Require Import BitmapEnc BitmapInv.
Require Import CodeBalloc.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecPrintk.
Require Import SpecBread SpecBrelse SpecLogWrite SpecMemset.
Require Import ProofBallocParts.
Require Import SpecBalloc.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  The out-of-blocks format string, in .rodata just above etext.         *)
(*  [auipc a0,0x4 / addi a0,a0,1440] at +0xf6 resolves to it.             *)
(*  Hoisted as NAMED pure lemmas -- never an inline [ltac:] argument to    *)
(*  [kernel_data_string] (claude-notes/optimization.md).                   *)
(*                                                                        *)
(*  DERIVED FROM THE DUMPED SYMBOL, not transcribed: [etext] IS the base   *)
(*  of .rodata, so an image bump that only moves .text carries this        *)
(*  address for free -- as a literal it went stale on every such bump and  *)
(*  surfaced far away as a byte mismatch.  Same [ltac:(eval vm_compute)]   *)
(*  idiom as [PageGeom.kmem_lo], and for the same reason: the body is a    *)
(*  plain [Z] literal by the time anything downstream sees it, so the      *)
(*  [unfold ba_msg_addr; lia] below keeps working.  Only a .rodata         *)
(*  REORDERING moves the offset -- 1a70c2e -> 515391a did, gcc having      *)
(*  reordered fs.c's functions and taken their message strings along.     *)
(* ===================================================================== *)
Definition ba_msg : string :=
  ("balloc: out of blocks" ++ String (Ascii.ascii_of_nat 10) EmptyString)%string.
Definition ba_msg_addr : Z :=
  ltac:(let x := eval vm_compute in (KernelSyms.etext + 0x3e8)%Z in exact x).

Lemma ba_msg_bytes : forall j b, cstring_bytes ba_msg !! j = Some b ->
  KernelData.kernel_data !! (ba_msg_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 23 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma ba_msg_fmt : pk_kinds ba_msg = [] /\ nonul ba_msg = true /\
                   (Z.of_nat (String.length ba_msg) < 2147483645)%Z.
Proof.
  split_and!; [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity].
Qed.

Module BallocProof (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE) (MS : MEMSET) : BALLOC.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Rs7 := (mword_of_int 23 : mword 5).
Notation Rs8 := (mword_of_int 24 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac baidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame, the threading invariants, the two arms, the    *)
(*  continuation.                                                         *)
(* ===================================================================== *)
Section BallocDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* balloc's 80-byte frame: ra@72 s0@64 s1@56 s2@48 s3@40 s4@32 s5@24
     s6@16 s7@8 s8@0.  [pa_stk sp j] counts DOWN from the entry sp, so slot
     j holds the register saved at (newsp + 80 - 8j). *)
  Definition ba_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] (m !!! Regidx Rs8 : mword 64))%I.

  (* THE TWO ARMS, as ONE resource: what each of balloc's two exits carries
     into the shared epilogue.  [rv] is the value in s1 at +0x7e. *)
  Definition ba_arms (γfs : fs_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (u : nat) (cr : bool) (Sb : gset Z)
      (rv : mword 32) : iProp Σ :=
    ((⌜bv_unsigned rv = 0⌝ ∗
      bitmap_res γfs bmapstart cov logstart size used ∗
      log_opS γ (2 + u) Sb)
     ∨
     (⌜bv_unsigned rv <> 0⌝ ∗
      ⌜bv_unsigned rv ∈ cov⌝ ∗
      ⌜~ (bv_unsigned rv ∈ log_region_set logstart)⌝ ∗
      fsblock γfs (bv_unsigned rv) (replicate BSIZE (bv_0 8)) ∗
      blk_own γfs (bv_unsigned rv) ∗
      bitmap_res γfs bmapstart cov logstart size (used ∪ {[ bv_unsigned rv ]}) ∗
      log_opS γ (if cr then S u else u)
                (Sb ∪ {[bmapstart]} ∪ {[bv_unsigned rv]})))%I.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition ba_cont `{GEN : GenId} `{CID0 : CpuId}
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr j) pidv Vpr -∗
        sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        bslots bn 2 -∗
        ((⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗
          bitmap_res γfs bmapstart cov logstart size used ∗
          log_opS γ (2 + u) Sb)
         ∨
         (∃ blk : mword 32,
            ⌜mf !!! Regidx Ra0 = sign_extend' 64 blk⌝ ∗
            ⌜bv_unsigned blk <> 0⌝ ∗
            ⌜bv_unsigned blk ∈ cov⌝ ∗
            ⌜~ (bv_unsigned blk ∈ log_region_set logstart)⌝ ∗
            fsblock γfs (bv_unsigned blk) (replicate BSIZE (bv_0 8)) ∗
            blk_own γfs (bv_unsigned blk) ∗
            bitmap_res γfs bmapstart cov logstart size
                       (used ∪ {[ bv_unsigned blk ]}) ∗
            log_opS γ (if cr then S u else u)
                      (Sb ∪ {[bmapstart]} ∪ {[bv_unsigned blk]}))) -∗
        WP (Loop : expr riscv_lang))%I.

  (* ONE BYTE of a buffer's data area, borrowed and given back at a new byte
     list -- [ByteBuf.bb_byte_acc] over [buf_own]'s list form. *)
  Lemma ba_buf_byte (pb : mword 64) (bno dsk : mword 32)
      (l : list (bv 8)) (d : nat) :
    length l = 1024%nat -> (d < 1024)%nat ->
    buf_own pb bno dsk l -∗
      pa_add (b_data pb) d ↦ₘ (l !!! d) ∗
      (∀ l' : list (bv 8),
         ⌜length l' = 1024%nat⌝ -∗
         ⌜forall k, (k < 1024)%nat -> k <> d -> l' !!! k = l !!! k⌝ -∗
         pa_add (b_data pb) d ↦ₘ (l' !!! d) -∗
         buf_own pb bno dsk l').
  Proof.
    intros Hlen Hd.
    iIntros "(Hb & Hdk & %Hl & Hby)".
    iEval (rewrite (bb_bytes_of_list (b_data pb) l) Hlen) in "Hby".
    iDestruct (bb_byte_acc (b_data pb) 1024 d (fun jj => l !!! jj)
                 (DfracOwn 1) Hd with "Hby") as "[Hcell Hback]".
    iSplitL "Hcell"; [iExact "Hcell" |].
    iIntros (l') "%Hlen' %Hag Hcell".
    iDestruct ("Hback" $! (fun jj => l' !!! jj) with "[%] Hcell") as "Hby".
    { intros k Hk Hne. exact (Hag k Hk Hne). }
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb" |]. iSplitL "Hdk"; [iExact "Hdk" |].
    iSplitR; [iPureIntro; exact Hlen' |].
    iAssert (bb_bytes (b_data pb) (length l') (fun jj => l' !!! jj))
      with "[Hby]" as "Hby".
    { rewrite Hlen' /bb_bytes. iExact "Hby". }
    iEval (rewrite -(bb_bytes_of_list (b_data pb) l')) in "Hby".
    iExact "Hby".
  Qed.

  (* THE WHOLE data area, in the [∗ list] shape [SpecMemset] takes and
     gives back -- the inlined bzero's window. *)
  Lemma ba_buf_all (pb : mword 64) (bno dsk : mword 32) (l : list (bv 8)) :
    length l = 1024%nat ->
    buf_own pb bno dsk l -∗
      ([∗ list] jj ∈ seq 0 1024, pa_add (b_data pb) jj ↦ₘ (l !!! jj)) ∗
      (∀ f : nat -> bv 8,
         ([∗ list] jj ∈ seq 0 1024, pa_add (b_data pb) jj ↦ₘ f jj) -∗
         buf_own pb bno dsk (f <$> seq 0 1024)).
  Proof.
    intros Hlen.
    iIntros "(Hb & Hdk & %Hl & Hby)".
    iEval (rewrite (bb_bytes_of_list (b_data pb) l) Hlen /bb_bytes) in "Hby".
    iSplitL "Hby"; [iExact "Hby" |].
    iIntros (f) "Hby".
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb" |]. iSplitL "Hdk"; [iExact "Hdk" |].
    iSplitR; [iPureIntro; apply bb_fmap_len |].
    iEval (rewrite -/(bb_bytes (b_data pb) 1024 f)
                   (bb_bytes_to_list (b_data pb) 1024 f)) in "Hby".
    iExact "Hby".
  Qed.

End BallocDefs.

(* the two register-threading invariants.  [ba_thr3] excludes only the
   three registers still un-restored at the epilogue; [ba_thr9] also
   excludes s2..s8, which are live across the whole body. *)
Definition ba_thr3 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ba_thr9 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ba_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))).

(* ===================================================================== *)
(*  +0x7e .. +0x88 : THE JOIN.  a0 := s1, restore ra/s0/s1, pop, return.  *)
(* ===================================================================== *)
Section BallocEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_epilogue `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z) (u : nat) (cr : bool) (Sb : gset Z)
      (rv : mword 32)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    ba_sp m M ->
    ba_thr3 m M ->
    M !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64) ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0x7e) : mword 64) -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 2 -∗
    ba_arms γfs γ cov logstart bmapstart size used u cr Sb rv -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr Hs1.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hppid Hsbsz Hsbbm Hsl
              Harms Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iPoseProof (bai_07e with "Htext") as "Hi7e".
    iPoseProof (bai_080 with "Htext") as "Hi80".
    iPoseProof (bai_082 with "Htext") as "Hi82".
    iPoseProof (bai_084 with "Htext") as "Hi84".
    iPoseProof (bai_086 with "Htext") as "Hi86".
    iPoseProof (bai_088 with "Htext") as "Hi88".
    rewrite /ba_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 & Hf10)".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x7e c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x7e)) Ra0 Rs1
              M (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (P0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HP0a0 : P0 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64)).
    { rewrite /P0 upd_eq. rgne. rewrite Hs1. apply add_vec_zero_l. }
    assert (HP0sp : ba_sp m P0)
      by (rewrite /ba_sp /P0 upd_ne; [exact Hsp | nz]).
    assert (HP0thr : ba_thr3 m P0).
    { intros c Hcs N2 N8 N9.
      rewrite /P0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9). }
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x80)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ===== +0x80 c.ldsp ra,72(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x80))
              (mword_of_int 9 : mword 6) Rra
              P0 (K - 10)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hf1]").
    { iEval (rewrite HP0sp -Hsp Hc1). iExact "Hf1". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rewrite HP0sp -Hsp Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> P0).
    assert (HP1a0 : P1 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P1 upd_ne; [exact HP0a0 | nz]).
    assert (HP1sp : ba_sp m P1)
      by (rewrite /ba_sp /P1 upd_ne; [exact HP0sp | nz]).
    assert (HP1thr : ba_thr3 m P1).
    { intros c Hcs N2 N8 N9.
      rewrite /P1 upd_ne; [| regne]. exact (HP0thr c Hcs N2 N8 N9). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x80) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x82)) by pcw.
    iEval (rewrite Hpp82) in "Hpc".
    (* ===== +0x82 c.ldsp s0,64(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x82))
              (mword_of_int 8 : mword 6) Rs0
              P1 (K - 10)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2a0 : P2 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : ba_sp m P2)
      by (rewrite /ba_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : ba_thr3 m P2).
    { intros c Hcs N2 N8 N9.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x82) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x84)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    (* ===== +0x84 c.ldsp s1,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x84))
              (mword_of_int 7 : mword 6) Rs1
              P2 (K - 10)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hf3]").
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3a0 : P3 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (HP3sp : ba_sp m P3)
      by (rewrite /ba_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : ba_thr3 m P3).
    { intros c Hcs N2 N8 N9.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp86 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x84) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x86)) by pcw.
    iEval (rewrite Hpp86) in "Hpc".
    (* ===== +0x86 c.addi16sp sp,80 : pop ===== *)
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP3sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)) : mword 64)
                   = 18446744073709551536) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)) : mword 64)
                    = 80) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551536 + 80)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P3 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
    { rewrite Hwv HP3sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 10)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iExists _; iExact "Hf8"|].
      iSplitL "Hf9"; [iExists _; iExact "Hf9"|].
      iSplitL "Hf10"; [iExists _; iExact "Hf10"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.balloc + 0x86))
              (mword_of_int 5 : mword 6) P3 (K - 10)%nat 10 b Hpop
              with "Hcg Hpc Hi86 Hstk").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P3).
    assert (Hnk : ((K - 10) + 10)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x86) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x88)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x88 c.ret ===== *)
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.balloc + 0x88)) Rra P4 K b
              ltac:(nz) with "Hcg Hpc Hi88").
    iIntros (CID6 Hq6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P4 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_eq; exact Hwv).
    assert (Cs0 : P4 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Hfin : ba_thr3 m P4).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9). }
    assert (Cs2 : P4 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs3 : P4 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs4 : P4 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs5 : P4 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs6 : P4 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs7 : P4 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs8 : P4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (apply Hfin; baidx).
    assert (Cs9 : P4 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; baidx).
    assert (Cs10 : P4 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; baidx).
    assert (Cs11 : P4 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; baidx).
    assert (HP4a0 : P4 !!! Regidx Ra0 = (sign_extend' 64 rv : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3a0 | nz]).
   iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /ba_cont.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    rewrite /ba_arms.
    iDestruct "Harms" as "[(%Hz & Hbmr & Hop) | (%Hnz & %Hcv & %Hlg & Hfsb & Hown & Hbmr & Hop)]".
    - iApply ("Hcont" $! P4 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hsbsz Hsbbm
                       Hsl [Hbmr Hop]").
      { unfold callee_saved. split_and!; assumption. }
      { iLeft. iSplitR.
        { iPureIntro. rewrite HP4a0. exact (ba_sext_zero rv Hz). }
        iSplitL "Hbmr"; [iExact "Hbmr"|]. iExact "Hop". }
    - iApply ("Hcont" $! P4 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hsbsz Hsbbm
                       Hsl [Hfsb Hown Hbmr Hop]").
      { unfold callee_saved. split_and!; assumption. }
      { iRight. iExists rv.
        iSplitR; [iPureIntro; exact HP4a0|].
        iSplitR; [iPureIntro; exact Hnz|].
        iSplitR; [iPureIntro; exact Hcv|].
        iSplitR; [iPureIntro; exact Hlg|].
        iSplitL "Hfsb"; [iExact "Hfsb"|].
        iSplitL "Hown"; [iExact "Hown"|].
        iSplitL "Hbmr"; [iExact "Hbmr"|]. iExact "Hop". }
  Qed.

End BallocEpilogue.

(* ===================================================================== *)
(*  +0xe8 .. +0x104 : OUT OF BLOCKS.  Pop s2..s8, printk, s1 := 0, and    *)
(*  jump back into the shared epilogue.  Nothing was written, so the      *)
(*  bitmap and the whole reservation go back untouched.                   *)
(* ===================================================================== *)
Section BallocOut.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_out `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (γpr : gname) (γu : uart_names) (γd : disk_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z) (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    ba_sp m M ->
    ba_thr9 m M ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0xe8) : mword 64) -∗
    printk_env γpr γu γd -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 2 -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    log_opS γ (2 + u) Sb -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpk Hsp Hthr.
    pose proof HK as HK'. 
    pose proof ba_msg_fmt as (Hkmsg & Hnmsg & Hlmsg).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkdata Hpc #Hpenv Hframe Hppid
              Hsbsz Hsbbm Hsl Hbmr Hop Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iPoseProof (kernel_data_string ba_msg_addr ba_msg
                  (mword_of_int ba_msg_addr) eq_refl
                  ltac:(unfold text_end, ba_msg_addr; lia)
                  ltac:(vm_compute; discriminate) ba_msg_bytes
                  with "Hkdata") as "#Hstr".
    iPoseProof (bai_0e8 with "Htext") as "Hie8".
    iPoseProof (bai_0ea with "Htext") as "Hiea".
    iPoseProof (bai_0ec with "Htext") as "Hiec".
    iPoseProof (bai_0ee with "Htext") as "Hiee".
    iPoseProof (bai_0f0 with "Htext") as "Hif0".
    iPoseProof (bai_0f2 with "Htext") as "Hif2".
    iPoseProof (bai_0f4 with "Htext") as "Hif4".
    iPoseProof (bai_0f6 with "Htext") as "Hif6".
    iPoseProof (bai_0fa with "Htext") as "Hifa".
    iPoseProof (bai_0fe with "Htext") as "Hife".
    iPoseProof (bai_102 with "Htext") as "Hi102".
    iPoseProof (bai_104 with "Htext") as "Hi104".
    rewrite /ba_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 & Hf10)".
    (* the seven callee-save slot addresses, at M's sp *)
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc10 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0xe8 .. +0xf4 : the seven restores ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xe8))
              (mword_of_int 6 : mword 6) Rs2
              M (K - 10)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie8 [Hf4]").
    { iEval (rewrite Hc4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hc4) in "Hf4".
    set (Q1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> M).
    assert (HQ1sp : ba_sp m Q1)
      by (rewrite /ba_sp /Q1 upd_ne; [exact Hsp | nz]).
    assert (Hppea : add_vec_int (mword_of_int (KernelSyms.balloc + 0xe8) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xea)) by pcw.
    iEval (rewrite Hppea) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xea))
              (mword_of_int 5 : mword 6) Rs3
              Q1 (K - 10)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiea [Hf5]").
    { iEval (rewrite HQ1sp -Hsp Hc5). iExact "Hf5". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf5".
    iEval (rewrite HQ1sp -Hsp Hc5) in "Hf5".
    set (Q2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> Q1).
    assert (HQ2sp : ba_sp m Q2)
      by (rewrite /ba_sp /Q2 upd_ne; [exact HQ1sp | nz]).
    assert (Hppec : add_vec_int (mword_of_int (KernelSyms.balloc + 0xea) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xec)) by pcw.
    iEval (rewrite Hppec) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xec))
              (mword_of_int 4 : mword 6) Rs4
              Q2 (K - 10)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiec [Hf6]").
    { iEval (rewrite HQ2sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf6".
    iEval (rewrite HQ2sp -Hsp Hc6) in "Hf6".
    set (Q3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> Q2).
    assert (HQ3sp : ba_sp m Q3)
      by (rewrite /ba_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (Hppee : add_vec_int (mword_of_int (KernelSyms.balloc + 0xec) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xee)) by pcw.
    iEval (rewrite Hppee) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xee))
              (mword_of_int 3 : mword 6) Rs5
              Q3 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiee [Hf7]").
    { iEval (rewrite HQ3sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf7".
    iEval (rewrite HQ3sp -Hsp Hc7) in "Hf7".
    set (Q4 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> Q3).
    assert (HQ4sp : ba_sp m Q4)
      by (rewrite /ba_sp /Q4 upd_ne; [exact HQ3sp | nz]).
    assert (Hppf0 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xee) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xf0)) by pcw.
    iEval (rewrite Hppf0) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xf0))
              (mword_of_int 2 : mword 6) Rs6
              Q4 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif0 [Hf8]").
    { iEval (rewrite HQ4sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf8".
    iEval (rewrite HQ4sp -Hsp Hc8) in "Hf8".
    set (Q5 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> Q4).
    assert (HQ5sp : ba_sp m Q5)
      by (rewrite /ba_sp /Q5 upd_ne; [exact HQ4sp | nz]).
    assert (Hppf2 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xf0) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xf2)) by pcw.
    iEval (rewrite Hppf2) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xf2))
              (mword_of_int 1 : mword 6) Rs7
              Q5 (K - 10)%nat (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif2 [Hf9]").
    { iEval (rewrite HQ5sp -Hsp Hc9). iExact "Hf9". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf9".
    iEval (rewrite HQ5sp -Hsp Hc9) in "Hf9".
    set (Q6 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> Q5).
    assert (HQ6sp : ba_sp m Q6)
      by (rewrite /ba_sp /Q6 upd_ne; [exact HQ5sp | nz]).
    assert (Hppf4 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xf2) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xf4)) by pcw.
    iEval (rewrite Hppf4) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0xf4))
              (mword_of_int 0 : mword 6) Rs8
              Q6 (K - 10)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif4 [Hf10]").
    { iEval (rewrite HQ6sp -Hsp Hc10). iExact "Hf10". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf10".
    iEval (rewrite HQ6sp -Hsp Hc10) in "Hf10".
    set (Q7 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> Q6).
    assert (HQ7sp : ba_sp m Q7)
      by (rewrite /ba_sp /Q7 upd_ne; [exact HQ6sp | nz]).
    (* the seven registers are back, so the WIDE threading invariant
       collapses to the epilogue's narrow one *)
    assert (HQ7s2 : Q7 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_ne; [| nz].
      rewrite /Q5 upd_ne; [| nz]. rewrite /Q4 upd_ne; [| nz].
      rewrite /Q3 upd_ne; [| nz]. rewrite /Q2 upd_ne; [| nz].
      rewrite /Q1 upd_eq. reflexivity. }
    assert (HQ7s3 : Q7 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_ne; [| nz].
      rewrite /Q5 upd_ne; [| nz]. rewrite /Q4 upd_ne; [| nz].
      rewrite /Q3 upd_ne; [| nz]. rewrite /Q2 upd_eq. reflexivity. }
    assert (HQ7s4 : Q7 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_ne; [| nz].
      rewrite /Q5 upd_ne; [| nz]. rewrite /Q4 upd_ne; [| nz].
      rewrite /Q3 upd_eq. reflexivity. }
    assert (HQ7s5 : Q7 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_ne; [| nz].
      rewrite /Q5 upd_ne; [| nz]. rewrite /Q4 upd_eq. reflexivity. }
    assert (HQ7s6 : Q7 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_ne; [| nz].
      rewrite /Q5 upd_eq. reflexivity. }
    assert (HQ7s7 : Q7 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /Q7 upd_ne; [| nz]. rewrite /Q6 upd_eq. reflexivity. }
    assert (HQ7s8 : Q7 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /Q7 upd_eq; reflexivity).
    assert (HQ7thr9 : ba_thr9 m Q7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Q7 upd_ne; [| regne]. rewrite /Q6 upd_ne; [| regne].
      rewrite /Q5 upd_ne; [| regne]. rewrite /Q4 upd_ne; [| regne].
      rewrite /Q3 upd_ne; [| regne]. rewrite /Q2 upd_ne; [| regne].
      rewrite /Q1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (HQ7thr : ba_thr3 m Q7).
    { intros c Hcs N2 N8 N9.
      destruct (decide (c = Rs2)) as [->|Nx2]; [exact HQ7s2|].
      destruct (decide (c = Rs3)) as [->|Nx3]; [exact HQ7s3|].
      destruct (decide (c = Rs4)) as [->|Nx4]; [exact HQ7s4|].
      destruct (decide (c = Rs5)) as [->|Nx5]; [exact HQ7s5|].
      destruct (decide (c = Rs6)) as [->|Nx6]; [exact HQ7s6|].
      destruct (decide (c = Rs7)) as [->|Nx7]; [exact HQ7s7|].
      destruct (decide (c = Rs8)) as [->|Nx8]; [exact HQ7s8|].
      exact (HQ7thr9 c Hcs N2 N8 N9 Nx2 Nx3 Nx4 Nx5 Nx6 Nx7 Nx8). }
    iAssert (ba_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]"
      as "Hframe".
    { rewrite /ba_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
      iSplitL "Hf9"; [iExact "Hf9"|]. iExact "Hf10". }
    assert (Hppf6 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xf4) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0xf6)) by pcw.
    iEval (rewrite Hppf6) in "Hpc".
    (* ===== +0xf6 auipc a0,0x4 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.balloc + 0xf6)) Ra0
              (mword_of_int 4 : mword 20) Q7 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hif6").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (Q8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.balloc + 0xf6) : mword 64)
                     (auipc_off (mword_of_int 4 : mword 20)))]> Q7).
    assert (HQ8sp : ba_sp m Q8)
      by (rewrite /ba_sp /Q8 upd_ne; [exact HQ7sp | nz]).
    assert (HQ8thr : ba_thr3 m Q8).
    { intros c Hcs N2 N8 N9.
      rewrite /Q8 upd_ne; [| regne]. exact (HQ7thr c Hcs N2 N8 N9). }
    assert (Hppfa : add_vec_int (mword_of_int (KernelSyms.balloc + 0xf6) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0xfa)) by pcw.
    iEval (rewrite Hppfa) in "Hpc".
    (* ===== +0xfa addi a0,a0,1368 : a0 := &"balloc: out of blocks\n" ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.balloc + 0xfa)) Ra0 Ra0
              (mword_of_int 1440 : mword 12) Q8 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hifa").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (Q9 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget Q8 Ra0)
                     (sign_extend' 64 (mword_of_int 1440 : mword 12)))]> Q8).
    assert (HQ9a0 : Q9 !!! Regidx Ra0 = (mword_of_int ba_msg_addr : mword 64)).
    { rewrite /Q9 upd_eq. rgne. rewrite /Q8 upd_eq.
      unfold ba_msg_addr. pcw. }
    assert (HQ9sp : ba_sp m Q9)
      by (rewrite /ba_sp /Q9 upd_ne; [exact HQ8sp | nz]).
    assert (HQ9thr : ba_thr3 m Q9).
    { intros c Hcs N2 N8 N9.
      rewrite /Q9 upd_ne; [| regne]. exact (HQ8thr c Hcs N2 N8 N9). }
    assert (Hppfe : add_vec_int (mword_of_int (KernelSyms.balloc + 0xfa) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0xfe)) by pcw.
    iEval (rewrite Hppfe) in "Hpc".
    (* ===== +0xfe jal ra,printk ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0xfe)) Rra
              (mword_of_int 2086578 : mword 21) Q9 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hife").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (QA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0xfe) : mword 64) 4)]> Q9).
    assert (Htgtpk : add_vec (mword_of_int (KernelSyms.balloc + 0xfe) : mword 64)
                       (sign_extend' 64 (mword_of_int 2086578 : mword 21))
                     = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgtpk) in "Hpc".
    assert (HQAa0 : QA !!! Regidx Ra0 = (mword_of_int ba_msg_addr : mword 64))
      by (rewrite /QA upd_ne; [exact HQ9a0 | nz]).
    assert (HQAra : QA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0xfe) : mword 64) 4)
      by (rewrite /QA; apply upd_eq).
    assert (HQAsp : ba_sp m QA)
      by (rewrite /ba_sp /QA upd_ne; [exact HQ9sp | nz]).
    assert (HQAthr : ba_thr3 m QA).
    { intros c Hcs N2 N8 N9.
      rewrite /QA upd_ne; [| regne]. exact (HQ9thr c Hcs N2 N8 N9). }
    iDestruct (cpu_own_transport CID0 CID10 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID10) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* the panic tail runs at depth 0, so the held set is forced empty and
       printk's order premise ("pr", 14) needs no hypothesis here. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iApply (Hpk CID10 QA (K - 10)%nat eb (proc_addr j)
              DfracDiscarded ba_msg [] b _
              ltac:(lia) Hlmsg Hnmsg ltac:(rewrite Hkmsg; reflexivity)
              ltac:(cbn [length]; lia)
              with "Hcg Htext Hkdata Hpc Hcnt Hpenv [] [//]").
    all: try lkbelow.
    { rewrite HQAa0. iExact "Hstr". }
    iIntros (CID11 Hq11 mP) "Hcg Hpc %Hcsp Hcnt _ _".
    destruct Hcsp as (Hcs1 & Hraeq).
    assert (Hpc102 : ret_pc (QA !!! Regidx Rra : mword 64)
                     = mword_of_int (KernelSyms.balloc + 0x102))
      by (rewrite HQAra; pcw).
    iEval (rewrite Hpc102) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmPsp : ba_sp m mP).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQAsp. }
    assert (HmPthr : ba_thr3 m mP).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HQAthr c Hcs N2 N8 N9). }
    (* ===== +0x102 c.li s1,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.balloc + 0x102)) Rs1
              (mword_of_int 0 : mword 6) (sign_extend' 64 (mword_of_int 0 : mword 32))
              mP (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi102").
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (QB := <[Regidx Rs1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 32))]> mP).
    assert (HQBs1 : QB !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64))
      by (rewrite /QB; apply upd_eq).
    assert (HQBsp : ba_sp m QB)
      by (rewrite /ba_sp /QB upd_ne; [exact HmPsp | nz]).
    assert (HQBthr : ba_thr3 m QB).
    { intros c Hcs N2 N8 N9.
      rewrite /QB upd_ne; [| regne]. exact (HmPthr c Hcs N2 N8 N9). }
    assert (Hpp104 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x102) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x104)) by pcw.
    iEval (rewrite Hpp104) in "Hpc".
    (* ===== +0x104 c.j +0x7e ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.balloc + 0x104))
              (sign_extend' 21 (concat_vec (mword_of_int 1981 : mword 11) ('b"0")))
              QB (K - 10)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi104").
    iIntros (CID13 Hq13). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt : add_vec (mword_of_int (KernelSyms.balloc + 0x104) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 1981 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.balloc + 0x7e)) by pcw.
    iEval (rewrite Hjt) in "Hpc".
    iDestruct (cpu_own_transport CID11 CID13 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [Hpk]/printk does not thread the complement, so [Hextc]/[Hextm] are
       still at [CID0] -- one wide hop straight to the delivery hart. *)
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID13 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID13 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_epilogue (CID0 := CID13)  j γfs bn γ cov logstart bmapstart size
              used u cr Sb (mword_of_int 0 : mword 32) pidv dq dqb dqs m QB K eb b lks
              Vpr HK HQBsp HQBthr HQBs1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hppid Hsbsz Hsbbm Hsl
                    [Hbmr Hop] [Hcont]").
    { rewrite /ba_arms. iLeft.
      iSplitR; [iPureIntro; vm_compute; reflexivity|].
      iSplitL "Hbmr"; [iExact "Hbmr"|]. iExact "Hop". }
    { iApply (wp_next_shift (b := true) (CIDa := CID10) (CIDb := CID13) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BallocOut.

(* ===================================================================== *)
(*  +0x8a .. +0x98 : THE INNER SCAN CAME UP EMPTY.  brelse the bitmap     *)
(*  buffer, b += BPB, reload sb.size -- and the [bgeu] is ALWAYS taken,   *)
(*  because b is now BPB and [size <= BPB].  Its fall-through (a second   *)
(*  outer iteration) is the function's OTHER dead arm.                    *)
(* ===================================================================== *)
Section BallocExhaust.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_exhaust `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat)
      (γfs : fs_names) (γd : disk_names) (bn : bio_names) (γ : log_names)
      (γpr : gname) (γu : uart_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (u : nat) (cr : bool) (Sb : gset Z)
      (kk : nat) (bnoB : mword 32) (bsX bsdX : list (bv 8)) (dX : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    0 < size <= BPB ->
    ba_sp m M ->
    ba_thr9 m M ->
    M !!! Regidx Rs2 = bnode kk ->
    M !!! Regidx Rs5 = (mword_of_int 0 : mword 64) ->
    M !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64) ->
    M !!! Regidx Rs8 = (mword_of_int 8192 : mword 64) ->
    (kk < NBUF)%nat ->
    (* ba_exhaust's own cone touches only "bcache" (brelse) *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0x8a) : mword 64) -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    procs_inv γs -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 1 -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    log_opS γ (2 + u) Sb -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bnoB bsX bsdX dX -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpk Hsize Hsp Hthr Hs2 Hs5 Hs6 Hs8 Hkk Hbelow.
    pose proof HK as HK'. 
    pose proof Hsize as Hsize'. rewrite BPB_value in Hsize'.
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkdata Hpc #Hpenv #Hbio #Hprocs Hframe Hppid Hsbsz Hsbbm Hsl Hbmr Hop Hlk Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iPoseProof (bai_08a with "Htext") as "Hi8a".
    iPoseProof (bai_08c with "Htext") as "Hi8c".
    iPoseProof (bai_090 with "Htext") as "Hi90".
    iPoseProof (bai_094 with "Htext") as "Hi94".
    iPoseProof (bai_098 with "Htext") as "Hi98".
    (* ===== +0x8a c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x8a)) Ra0 Rs2
              M (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (E0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs2))]> M).
    assert (HE0a0 : E0 !!! Regidx Ra0 = bnode kk).
    { rewrite /E0 upd_eq. rgne. rewrite Hs2. apply add_vec_zero_l. }
    assert (HE0s5 : E0 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /E0 upd_ne; [exact Hs5 | nz]).
    assert (HE0s6 : E0 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /E0 upd_ne; [exact Hs6 | nz]).
    assert (HE0s8 : E0 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /E0 upd_ne; [exact Hs8 | nz]).
    assert (HE0sp : ba_sp m E0)
      by (rewrite /ba_sp /E0 upd_ne; [exact Hsp | nz]).
    assert (HE0thr : ba_thr9 m E0).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /E0 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x8a) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x8c)) by pcw.
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x8c jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x8c)) Rra
              (mword_of_int 2096776 : mword 21) E0 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi8c").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (E1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x8c) : mword 64) 4)]> E0).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.balloc + 0x8c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096776 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HE1a0 : E1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /E1 upd_ne; [exact HE0a0 | nz]).
    assert (HE1s5 : E1 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /E1 upd_ne; [exact HE0s5 | nz]).
    assert (HE1s6 : E1 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /E1 upd_ne; [exact HE0s6 | nz]).
    assert (HE1s8 : E1 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /E1 upd_ne; [exact HE0s8 | nz]).
    assert (HE1sp : ba_sp m E1)
      by (rewrite /ba_sp /E1 upd_ne; [exact HE0sp | nz]).
    assert (HE1ra : E1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x8c) : mword 64) 4)
      by (rewrite /E1; apply upd_eq).
    assert (HE1thr : ba_thr9 m E1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /E1 upd_ne; [| regne].
      exact (HE0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 10)%nat) by (lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bnoB dq E1 (K - 10)%nat eb (proc_addr j) bsX bsdX dX b lks Vpr
              HKbl Hkk HE1a0
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID3 Hq3 mR) "%Hcs1 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc90 : ret_pc (E1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x90))
      by (rewrite HE1ra; pcw).
    iEval (rewrite Hpc90) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmRs5 : mR !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HE1s5).
    assert (HmRs6 : mR !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HE1s6).
    assert (HmRs8 : mR !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs8 ltac:(vm_compute; reflexivity));
          exact HE1s8).
    assert (HmRsp : ba_sp m mR).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE1sp. }
    assert (HmRthr : ba_thr9 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HE1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    (* ===== +0x90 addw s5,s8,s5 : b += BPB ===== *)
    iApply (wp_addw4_s_sconf (mword_of_int (KernelSyms.balloc + 0x90)) Rs5 Rs8 Rs5
              mR (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (E2 := <[Regidx Rs5 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget mR Rs8) 31 0 : mword 32)
                              (subrange_vec_dec (rget mR Rs5) 31 0 : mword 32)))]> mR).
    assert (HE2s5 : E2 !!! Regidx Rs5 = (mword_of_int 8192 : mword 64)).
    { rewrite /E2 upd_eq. rgne. rgne. rewrite HmRs8 HmRs5. pcw. }
    assert (HE2s6 : E2 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /E2 upd_ne; [exact HmRs6 | nz]).
    assert (HE2sp : ba_sp m E2)
      by (rewrite /ba_sp /E2 upd_ne; [exact HmRsp | nz]).
    assert (HE2thr : ba_thr9 m E2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /E2 upd_ne; [| regne].
      exact (HmRthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x90) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 lw a5,4(s6) : a5 := sb.size ===== *)
    assert (Hszadr : add_vec (rget E2 Rs6) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = sb_size).
    { rgne. rewrite HE2s6. unfold sb_size, pa_add, add_vec_int. apply f_equal. pcw. }
    iEval (rewrite -Hszadr) in "Hsbsz".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.balloc + 0x94)) Ra5 Rs6
              (mword_of_int 4 : mword 12) E2 (K - 10)%nat
              (mword_of_int size : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi94 Hsbsz").
    iIntros (CID5 Hq5) "Hcg Hpc Hsbsz".
    iEval (rewrite Hszadr) in "Hsbsz".
    set (E3 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int size : mword 32))]> E2).
    assert (HE3a5 : E3 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
      by (rewrite /E3; apply upd_eq).
    assert (HE3s5 : E3 !!! Regidx Rs5 = (mword_of_int 8192 : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2s5 | nz]).
    assert (HE3sp : ba_sp m E3)
      by (rewrite /ba_sp /E3 upd_ne; [exact HE2sp | nz]).
    assert (HE3thr : ba_thr9 m E3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /E3 upd_ne; [| regne].
      exact (HE2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x94) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0x98)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x98 bgeu s5,a5 : ALWAYS TAKEN (b = BPB >= size) ===== *)
    assert (Hszsext : (sign_extend' 64 (mword_of_int size : mword 32) : mword 64)
                      = mword_of_int size).
    { apply sext32_64_small. change (2^31)%Z with 2147483648%Z. lia. }
    assert (Hcmp : zopz0zKzJ_u (rget E3 Rs5) (rget E3 Ra5) = true).
    { rgne. rgne. rewrite HE3s5 HE3a5 Hszsext.
      rewrite (ba_bgeu_moi 8192 size ltac:(lia) ltac:(lia)).
      apply Z.geb_le. lia. }
    iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.balloc + 0x98))
              (mword_of_int 80 : mword 13) Ra5 Rs5 E3 (K - 10)%nat b
              ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi98").
    iApply bi.later_intro. iIntros (CID6 Hq6) "Hcg Hpc".
    assert (Hjt : add_vec (mword_of_int (KernelSyms.balloc + 0x98) : mword 64)
                    (sign_extend' 64 (mword_of_int 80 : mword 13))
                  = mword_of_int (KernelSyms.balloc + 0xe8)) by pcw.
    iEval (rewrite Hjt) in "Hpc".
    iDestruct (cpu_own_transport CID3 CID6 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [brelse] does not thread the complement, so [Hextc]/[Hextm] are still
       at [CID0] -- one wide hop straight to [ba_out]'s entry hart. *)
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_out (CID0 := CID6)  j γfs bn γ γpr γu γd cov logstart bmapstart
              size used u cr Sb pidv dq dqb dqs m E3 K eb b lks Vpr HK Hpk HE3sp HE3thr
              with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hframe
                    Hppid Hsbsz Hsbbm Hsl Hbmr Hop [Hcont]").
    { iApply (wp_next_shift (b := true) (CIDa := CID2) (CIDb := CID6) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BallocExhaust.

(* ===================================================================== *)
(*  +0x70 .. +0x7c : the SUCCESS arm's s2..s8 restore, straight into the  *)
(*  shared epilogue carrying the allocated block.                         *)
(* ===================================================================== *)
Section BallocRestore.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_restore `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z) (bi : Z)
      (u : nat) (cr : bool) (Sb : gset Z) (rv : mword 32)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    ba_sp m M ->
    ba_thr9 m M ->
    M !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64) ->
    bv_unsigned rv <> 0 ->
    bv_unsigned rv ∈ cov ->
    ~ (bv_unsigned rv ∈ log_region_set logstart) ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0x70) : mword 64) -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 2 -∗
    fsblock γfs (bv_unsigned rv) (replicate BSIZE (bv_0 8)) -∗
    blk_own γfs (bv_unsigned rv) -∗
    bitmap_res γfs bmapstart cov logstart size (used ∪ {[ bv_unsigned rv ]}) -∗
    log_opS γ (if cr then S u else u) (Sb ∪ {[bmapstart]} ∪ {[bv_unsigned rv]}) -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr Hs1 Hnz Hcv Hlg.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hppid Hsbsz Hsbbm Hsl
              Hfsb Hown Hbmr Hop Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iPoseProof (bai_070 with "Htext") as "Hi70".
    iPoseProof (bai_072 with "Htext") as "Hi72".
    iPoseProof (bai_074 with "Htext") as "Hi74".
    iPoseProof (bai_076 with "Htext") as "Hi76".
    iPoseProof (bai_078 with "Htext") as "Hi78".
    iPoseProof (bai_07a with "Htext") as "Hi7a".
    iPoseProof (bai_07c with "Htext") as "Hi7c".
    rewrite /ba_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 & Hf10)".
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc10 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x70))
              (mword_of_int 6 : mword 6) Rs2
              M (K - 10)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi70 [Hf4]").
    { iEval (rewrite Hc4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hc4) in "Hf4".
    set (R1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> M).
    assert (HR1sp : ba_sp m R1)
      by (rewrite /ba_sp /R1 upd_ne; [exact Hsp | nz]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R1 upd_ne; [exact Hs1 | nz]).
    assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x70) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x72)) by pcw.
    iEval (rewrite Hpp72) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x72))
              (mword_of_int 5 : mword 6) Rs3
              R1 (K - 10)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi72 [Hf5]").
    { iEval (rewrite HR1sp -Hsp Hc5). iExact "Hf5". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf5".
    iEval (rewrite HR1sp -Hsp Hc5) in "Hf5".
    set (R2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> R1).
    assert (HR2sp : ba_sp m R2)
      by (rewrite /ba_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2s1 : R2 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1s1 | nz]).
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x72) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x74))
              (mword_of_int 4 : mword 6) Rs4
              R2 (K - 10)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi74 [Hf6]").
    { iEval (rewrite HR2sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf6".
    iEval (rewrite HR2sp -Hsp Hc6) in "Hf6".
    set (R3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> R2).
    assert (HR3sp : ba_sp m R3)
      by (rewrite /ba_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3s1 : R3 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s1 | nz]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x76))
              (mword_of_int 3 : mword 6) Rs5
              R3 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi76 [Hf7]").
    { iEval (rewrite HR3sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf7".
    iEval (rewrite HR3sp -Hsp Hc7) in "Hf7".
    set (R4 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> R3).
    assert (HR4sp : ba_sp m R4)
      by (rewrite /ba_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4s1 : R4 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x76) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x78)) by pcw.
    iEval (rewrite Hpp78) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x78))
              (mword_of_int 2 : mword 6) Rs6
              R4 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi78 [Hf8]").
    { iEval (rewrite HR4sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf8".
    iEval (rewrite HR4sp -Hsp Hc8) in "Hf8".
    set (R5 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> R4).
    assert (HR5sp : ba_sp m R5)
      by (rewrite /ba_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5s1 : R5 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.balloc + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x7a)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x7a))
              (mword_of_int 1 : mword 6) Rs7
              R5 (K - 10)%nat (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi7a [Hf9]").
    { iEval (rewrite HR5sp -Hsp Hc9). iExact "Hf9". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf9".
    iEval (rewrite HR5sp -Hsp Hc9) in "Hf9".
    set (R6 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> R5).
    assert (HR6sp : ba_sp m R6)
      by (rewrite /ba_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x7a) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x7c)) by pcw.
    iEval (rewrite Hpp7c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x7c))
              (mword_of_int 0 : mword 6) Rs8
              R6 (K - 10)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi7c [Hf10]").
    { iEval (rewrite HR6sp -Hsp Hc10). iExact "Hf10". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf10".
    iEval (rewrite HR6sp -Hsp Hc10) in "Hf10".
    set (R7 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> R6).
    assert (HR7sp : ba_sp m R7)
      by (rewrite /ba_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = (sign_extend' 64 rv : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s1 | nz]).
    assert (HR7s2 : R7 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_eq. reflexivity. }
    assert (HR7s3 : R7 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_eq. reflexivity. }
    assert (HR7s4 : R7 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_eq. reflexivity. }
    assert (HR7s5 : R7 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_eq. reflexivity. }
    assert (HR7s6 : R7 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_eq. reflexivity. }
    assert (HR7s7 : R7 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_eq. reflexivity. }
    assert (HR7s8 : R7 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /R7 upd_eq; reflexivity).
    assert (HR7thr9 : ba_thr9 m R7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R7 upd_ne; [| regne]. rewrite /R6 upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne]. rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne]. rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (HR7thr : ba_thr3 m R7).
    { intros c Hcs N2 N8 N9.
      destruct (decide (c = Rs2)) as [->|Nx2]; [exact HR7s2|].
      destruct (decide (c = Rs3)) as [->|Nx3]; [exact HR7s3|].
      destruct (decide (c = Rs4)) as [->|Nx4]; [exact HR7s4|].
      destruct (decide (c = Rs5)) as [->|Nx5]; [exact HR7s5|].
      destruct (decide (c = Rs6)) as [->|Nx6]; [exact HR7s6|].
      destruct (decide (c = Rs7)) as [->|Nx7]; [exact HR7s7|].
      destruct (decide (c = Rs8)) as [->|Nx8]; [exact HR7s8|].
      exact (HR7thr9 c Hcs N2 N8 N9 Nx2 Nx3 Nx4 Nx5 Nx6 Nx7 Nx8). }
    iAssert (ba_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]"
      as "Hframe".
    { rewrite /ba_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
      iSplitL "Hf9"; [iExact "Hf9"|]. iExact "Hf10". }
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.balloc + 0x7c) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x7e)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    iDestruct (cpu_own_transport CID0 CID7 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID7 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID7 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_epilogue (CID0 := CID7)  j γfs bn γ cov logstart bmapstart size
              used u cr Sb rv pidv dq dqb dqs m R7 K eb b lks Vpr HK HR7sp HR7thr HR7s1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hppid Hsbsz Hsbbm Hsl
                    [Hfsb Hown Hbmr Hop] [Hcont]").
    { rewrite /ba_arms. iRight.
      iSplitR; [iPureIntro; exact Hnz|].
      iSplitR; [iPureIntro; exact Hcv|].
      iSplitR; [iPureIntro; exact Hlg|].
      iSplitL "Hfsb"; [iExact "Hfsb"|].
      iSplitL "Hown"; [iExact "Hown"|].
      iSplitL "Hbmr"; [iExact "Hbmr"|]. iExact "Hop". }
    { iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID7) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BallocRestore.

(* ===================================================================== *)
(*  +0x4c .. +0x7c : THE INLINED bzero.  bread the freshly-allocated      *)
(*  block, memset its 1024 data bytes to zero, log_write it, brelse it,   *)
(*  pop s2..s8 and fall into the epilogue with s1 = b + bi.               *)
(* ===================================================================== *)
Section BallocBzero.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_bzero `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (bi : Z) (u : nat) (cr : bool) (Sb : gset Z) (bsD : list (bv 8))
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    0 < size <= BPB ->
    0 <= bi < size ->
    bi ∈ cov ->
    ~ (bi ∈ log_region_set logstart) ->
    bi <> 0 ->
    length bsD = BSIZE ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    ba_sp m M ->
    ba_thr9 m M ->
    M !!! Regidx Rs1 = (mword_of_int bi : mword 64) ->
    M !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64) ->
    (* ba_bzero's own cone touches "log" (log_write) and "bcache"
       (bread/brelse) -- "log" is the floor *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0x4c) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 2 -∗
    log_opS γ (S (if cr then S u else u)) (Sb ∪ {[bmapstart]}) -∗
    bitmap_res γfs bmapstart cov logstart size (used ∪ {[ bi ]}) -∗
    fsblock γfs bi bsD -∗
    blk_own γfs bi -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsize Hbirange Hbicov Hbilog Hbinz HbsDlen Hj Hgl Hsp Hthr Hs1 Hs7 Hbelow.
    pose proof HK as HK'. 
    assert (HbiBPB : 0 <= bi < BPB) by lia.
    destruct (ba_range bi ltac:(lia))
      as (Hbi0 & Hbi8192 & Hbi31 & Hbi32 & Hbi64 & Hrmod & Hqrange & Hbilt).
    set (bnoD := (mword_of_int bi : mword 32)).
    assert (HbnoD : uint bnoD = bi).
    { rewrite /bnoD bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (HbnoDlt : (uint bnoD < 2147483648)%Z) by (rewrite HbnoD; lia).
    assert (HbnoDcov : uint bnoD ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite HbnoD; exact Hbicov).
    assert (HbnoDsext : (sign_extend' 64 bnoD : mword 64) = mword_of_int bi).
    { rewrite /bnoD. apply sext32_64_small.
      change (2^31)%Z with 2147483648%Z. lia. }
    assert (HbnoDnz : bv_unsigned bnoD <> 0)
      by (rewrite -bb_uint32 HbnoD; exact Hbinz).
    assert (HbsD1024 : length bsD = 1024%nat)
      by (rewrite HbsDlen; unfold BSIZE; reflexivity).
    assert (Hlvl : (Z.of_nat 0 + 2 < 2 ^ 31)%Z)
      by (change (2^31)%Z with 2147483648%Z; lia).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hprocs Hframe Hppid Hsbsz Hsbbm #Hdevi #Hdgeom #Hdlock Hsl Hop
              Hbmr HfsbD Hown Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iPoseProof (bai_04c with "Htext") as "Hi4c".
    iPoseProof (bai_04e with "Htext") as "Hi4e".
    iPoseProof (bai_050 with "Htext") as "Hi50".
    iPoseProof (bai_054 with "Htext") as "Hi54".
    iPoseProof (bai_056 with "Htext") as "Hi56".
    iPoseProof (bai_05a with "Htext") as "Hi5a".
    iPoseProof (bai_05c with "Htext") as "Hi5c".
    iPoseProof (bai_060 with "Htext") as "Hi60".
    iPoseProof (bai_064 with "Htext") as "Hi64".
    iPoseProof (bai_066 with "Htext") as "Hi66".
    iPoseProof (bai_06a with "Htext") as "Hi6a".
    iPoseProof (bai_06c with "Htext") as "Hi6c".
    iPoseProof (bai_070 with "Htext") as "Hi70".
    iPoseProof (bai_072 with "Htext") as "Hi72".
    iPoseProof (bai_074 with "Htext") as "Hi74".
    iPoseProof (bai_076 with "Htext") as "Hi76".
    iPoseProof (bai_078 with "Htext") as "Hi78".
    iPoseProof (bai_07a with "Htext") as "Hi7a".
    iPoseProof (bai_07c with "Htext") as "Hi7c".
    (* ===== +0x4c c.mv a1,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x4c)) Ra1 Rs1
              M (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4c").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (Z0 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HZ0a1 : Z0 !!! Regidx Ra1 = (sign_extend' 64 bnoD : mword 64)).
    { rewrite /Z0 upd_eq. rgne. rewrite Hs1 HbnoDsext. apply add_vec_zero_l. }
    assert (HZ0s1 : Z0 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z0 upd_ne; [exact Hs1 | nz]).
    assert (HZ0s7 : Z0 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Z0 upd_ne; [exact Hs7 | nz]).
    assert (HZ0sp : ba_sp m Z0)
      by (rewrite /ba_sp /Z0 upd_ne; [exact Hsp | nz]).
    assert (HZ0thr : ba_thr9 m Z0).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z0 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.balloc + 0x4c) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    (* ===== +0x4e c.mv a0,s7 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x4e)) Ra0 Rs7
              Z0 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (Z1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget Z0 Rs7))]> Z0).
    assert (HZ1a0 : Z1 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /Z1 upd_eq. rgne. rewrite HZ0s7. apply add_vec_zero_l. }
    assert (HZ1a1 : Z1 !!! Regidx Ra1 = (sign_extend' 64 bnoD : mword 64))
      by (rewrite /Z1 upd_ne; [exact HZ0a1 | nz]).
    assert (HZ1s1 : Z1 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z1 upd_ne; [exact HZ0s1 | nz]).
    assert (HZ1sp : ba_sp m Z1)
      by (rewrite /ba_sp /Z1 upd_ne; [exact HZ0sp | nz]).
    assert (HZ1thr : ba_thr9 m Z1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z1 upd_ne; [| regne].
      exact (HZ0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x50 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x50)) Rra
              (mword_of_int 2096572 : mword 21) Z1 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (Z2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x50) : mword 64) 4)]> Z1).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.balloc + 0x50) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096572 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HZ2a0 : Z2 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /Z2 upd_ne; [exact HZ1a0 | nz]).
    assert (HZ2a1 : Z2 !!! Regidx Ra1 = (sign_extend' 64 bnoD : mword 64))
      by (rewrite /Z2 upd_ne; [exact HZ1a1 | nz]).
    assert (HZ2s1 : Z2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z2 upd_ne; [exact HZ1s1 | nz]).
    assert (HZ2sp : ba_sp m Z2)
      by (rewrite /ba_sp /Z2 upd_ne; [exact HZ1sp | nz]).
    assert (HZ2ra : Z2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x50) : mword 64) 4)
      by (rewrite /Z2; apply upd_eq).
    assert (HZ2thr : ba_thr9 m Z2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z2 upd_ne; [| regne].
      exact (HZ1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID0 CID3 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID3 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 10)%nat) by (lia).
    iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bnoD dq
              Z2 (K - 10)%nat eb b lks Vpr
              HKbr HbnoDlt eq_refl HbnoDcov eq_refl Hj Hgl HZ2a0 HZ2a1
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID4 Hq4 mB kk2 bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc54 : ret_pc (Z2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x54)) by (rewrite HZ2ra; pcw).
    iEval (rewrite Hpc54) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HZ2s1).
    assert (HmBsp : ba_sp m mB).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HZ2sp. }
    assert (HmBthr : ba_thr9 m mB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HZ2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    (* THE COUPLING: the bytes bread returned ARE the pool's opaque content *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk2.
    iEval (rewrite -HbnoD) in "HfsbD".
    iDestruct (iu_held_content with "HfsbD Hheld") as %Hbs0.
    subst bs0.
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (ba_buf_all (bpa kk2) bnoD (mword_of_int 0 : mword 32) bsD
                 HbsD1024 with "Hbuf") as "[Hby Hbyback]".
    (* ===== +0x54 c.mv s2,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x54)) Rs2 Ra0
              mB (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (Z3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HZ3s2 : Z3 !!! Regidx Rs2 = bnode kk2).
    { rewrite /Z3 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HZ3a0 : Z3 !!! Regidx Ra0 = bnode kk2)
      by (rewrite /Z3 upd_ne; [exact HmBa0 | nz]).
    assert (HZ3s1 : Z3 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z3 upd_ne; [exact HmBs1 | nz]).
    assert (HZ3sp : ba_sp m Z3)
      by (rewrite /ba_sp /Z3 upd_ne; [exact HmBsp | nz]).
    assert (HZ3thr : ba_thr9 m Z3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z3 upd_ne; [| regne].
      exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    (* ===== +0x56 li a2,1024 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.balloc + 0x56)) Ra2
              (mword_of_int 1024 : mword 12)
              (mword_of_int (Z.of_nat 1024) : mword 64)
              Z3 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi56").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (Z4 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 1024) : mword 64)]> Z3).
    assert (HZ4a2 : Z4 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat 1024) : mword 64))
      by (rewrite /Z4; apply upd_eq).
    assert (HZ4a0 : Z4 !!! Regidx Ra0 = bnode kk2)
      by (rewrite /Z4 upd_ne; [exact HZ3a0 | nz]).
    assert (HZ4s2 : Z4 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z4 upd_ne; [exact HZ3s2 | nz]).
    assert (HZ4s1 : Z4 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z4 upd_ne; [exact HZ3s1 | nz]).
    assert (HZ4sp : ba_sp m Z4)
      by (rewrite /ba_sp /Z4 upd_ne; [exact HZ3sp | nz]).
    assert (HZ4thr : ba_thr9 m Z4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z4 upd_ne; [| regne].
      exact (HZ3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.balloc + 0x56) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== +0x5a c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.balloc + 0x5a)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              Z4 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi5a").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (Z5 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> Z4).
    assert (HZ5a1 : Z5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /Z5; apply upd_eq).
    assert (HZ5a2 : Z5 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat 1024) : mword 64))
      by (rewrite /Z5 upd_ne; [exact HZ4a2 | nz]).
    assert (HZ5a0 : Z5 !!! Regidx Ra0 = bnode kk2)
      by (rewrite /Z5 upd_ne; [exact HZ4a0 | nz]).
    assert (HZ5s2 : Z5 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z5 upd_ne; [exact HZ4s2 | nz]).
    assert (HZ5s1 : Z5 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z5 upd_ne; [exact HZ4s1 | nz]).
    assert (HZ5sp : ba_sp m Z5)
      by (rewrite /ba_sp /Z5 upd_ne; [exact HZ4sp | nz]).
    assert (HZ5thr : ba_thr9 m Z5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z5 upd_ne; [| regne].
      exact (HZ4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    (* ===== +0x5c addi a0,a0,88 : a0 := bp->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.balloc + 0x5c)) Ra0 Ra0
              (mword_of_int 88 : mword 12) Z5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (Z6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget Z5 Ra0)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> Z5).
    assert (HZ6a0 : Z6 !!! Regidx Ra0 = b_data (bnode kk2)).
    { rewrite /Z6 upd_eq. rgne. rewrite HZ5a0. apply iu_data_addr. }
    assert (HZ6a1 : Z6 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /Z6 upd_ne; [exact HZ5a1 | nz]).
    assert (HZ6a2 : Z6 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat 1024) : mword 64))
      by (rewrite /Z6 upd_ne; [exact HZ5a2 | nz]).
    assert (HZ6s2 : Z6 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z6 upd_ne; [exact HZ5s2 | nz]).
    assert (HZ6s1 : Z6 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z6 upd_ne; [exact HZ5s1 | nz]).
    assert (HZ6sp : ba_sp m Z6)
      by (rewrite /ba_sp /Z6 upd_ne; [exact HZ5sp | nz]).
    assert (HZ6thr : ba_thr9 m Z6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z6 upd_ne; [| regne].
      exact (HZ5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x5c) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    (* ===== +0x60 jal ra,memset ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x60)) Rra
              (mword_of_int 2088648 : mword 21) Z6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi60").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (Z7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x60) : mword 64) 4)]> Z6).
    assert (Htgtms : add_vec (mword_of_int (KernelSyms.balloc + 0x60) : mword 64)
                       (sign_extend' 64 (mword_of_int 2088648 : mword 21))
                     = mword_of_int KernelSyms.memset) by pcw.
    iEval (rewrite Htgtms) in "Hpc".
    assert (HZ7a0 : Z7 !!! Regidx Ra0 = b_data (bnode kk2))
      by (rewrite /Z7 upd_ne; [exact HZ6a0 | nz]).
    assert (HZ7a1 : Z7 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /Z7 upd_ne; [exact HZ6a1 | nz]).
    assert (HZ7a2 : Z7 !!! Regidx Ra2
                    = (mword_of_int (Z.of_nat 1024) : mword 64))
      by (rewrite /Z7 upd_ne; [exact HZ6a2 | nz]).
    assert (HZ7s2 : Z7 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z7 upd_ne; [exact HZ6s2 | nz]).
    assert (HZ7s1 : Z7 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z7 upd_ne; [exact HZ6s1 | nz]).
    assert (HZ7sp : ba_sp m Z7)
      by (rewrite /ba_sp /Z7 upd_ne; [exact HZ6sp | nz]).
    assert (HZ7ra : Z7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x60) : mword 64) 4)
      by (rewrite /Z7; apply upd_eq).
    assert (HZ7thr : ba_thr9 m Z7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z7 upd_ne; [| regne].
      exact (HZ6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iEval (rewrite -HZ7a0) in "Hby".
    iApply (MS.wp_memset_sconf KT1 KT0 Z7 (K - 10)%nat 1024%nat
              (mword_of_int 0 : mword 64) (fun jj => bsD !!! jj) b (proc_addr j)
              ltac:(lia) ltac:(vm_compute; reflexivity) HZ7a1 HZ7a2
              with "Hcg Htext Hpc Hby").
    iIntros (CID10 Hq10 mM) "Hcg Hpc Hby %Hcs2".
    iEval (rewrite HZ7a0) in "Hby".
    assert (Hpc64 : ret_pc (Z7 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x64)) by (rewrite HZ7ra; pcw).
    iEval (rewrite Hpc64) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmMs2 : mM !!! Regidx Rs2 = bnode kk2)
      by (rewrite (callee_saved_lookup Hcs2_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HZ7s2).
    assert (HmMs1 : mM !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs2_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HZ7s1).
    assert (HmMsp : ba_sp m mM).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HZ7sp. }
    assert (HmMthr : ba_thr9 m mM).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HZ7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    (* ---- the zeroed buffer ---- *)
    iDestruct ("Hbyback" $! (fun _ : nat => ba_cbyte) with "Hby") as "Hbuf".
    iEval (rewrite ba_zero_block) in "Hbuf".
    iDestruct ("Hheldback" with "Hbuf") as "Hheld".
    (* ===== +0x64 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x64)) Ra0 Rs2
              mM (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi64").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (Z8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mM Rs2))]> mM).
    assert (HZ8a0 : Z8 !!! Regidx Ra0 = bnode kk2).
    { rewrite /Z8 upd_eq. rgne. rewrite HmMs2. apply add_vec_zero_l. }
    assert (HZ8s2 : Z8 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z8 upd_ne; [exact HmMs2 | nz]).
    assert (HZ8s1 : Z8 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z8 upd_ne; [exact HmMs1 | nz]).
    assert (HZ8sp : ba_sp m Z8)
      by (rewrite /ba_sp /Z8 upd_ne; [exact HmMsp | nz]).
    assert (HZ8thr : ba_thr9 m Z8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z8 upd_ne; [| regne].
      exact (HmMthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x64) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x66)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    (* ===== +0x66 jal ra,log_write ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x66)) Rra
              (mword_of_int 4182 : mword 21) Z8 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (Z9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x66) : mword 64) 4)]> Z8).
    assert (Htgtlw2 : add_vec (mword_of_int (KernelSyms.balloc + 0x66) : mword 64)
                        (sign_extend' 64 (mword_of_int 4182 : mword 21))
                      = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw2) in "Hpc".
    assert (HZ9a0 : Z9 !!! Regidx Ra0 = bnode kk2)
      by (rewrite /Z9 upd_ne; [exact HZ8a0 | nz]).
    assert (HZ9s2 : Z9 !!! Regidx Rs2 = bnode kk2)
      by (rewrite /Z9 upd_ne; [exact HZ8s2 | nz]).
    assert (HZ9s1 : Z9 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /Z9 upd_ne; [exact HZ8s1 | nz]).
    assert (HZ9sp : ba_sp m Z9)
      by (rewrite /ba_sp /Z9 upd_ne; [exact HZ8sp | nz]).
    assert (HZ9ra : Z9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x66) : mword 64) 4)
      by (rewrite /Z9; apply upd_eq).
    assert (HZ9thr : ba_thr9 m Z9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /Z9 upd_ne; [| regne].
      exact (HZ8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID4 CID12 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID3) (CIDb := CID12) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKlw2 : (K_log_write <= K - 10)%nat) by (lia).
    (* THE FRESH BLOCK'S log_write, UNCREDITED: a freshly allocated block is
       not one the caller can claim this op already logged.  What matters is
       the OUTPUT -- [bnoD] joins the op's set, which is what lets writei
       absorb its own later log_write of the very same block. *)
    iApply (LW.wp_log_write_gen bn γ γfs γd cov logstart dev kk2 pidv bnoD
              (replicate BSIZE (bv_0 8)) bsD bsd0 d0 (if cr then S u else u)
              false (Sb ∪ {[bmapstart]})
              Z9 0%nat eb (proc_addr j) (K - 10)%nat b lks
              HKlw2 Hlvl Hkk2 HZ9a0
              ltac:(rewrite HbnoD; exact Hbicov)
              ltac:(rewrite HbnoD; exact Hbilog)
              ltac:(discriminate)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hop HfsbD Hheld").
    all: try lkbelow.
    iIntros (CID13 Hq13 mL2) "Hcg Hcnt Hpc %Hcs3 Hop HfsbD Hlk Hsl".
    assert (HsetD : (Sb ∪ {[bmapstart]} ∪ {[uint bnoD]} : gset Z)
                    = Sb ∪ {[bmapstart]} ∪ {[bv_unsigned bnoD]})
      by (rewrite bb_uint32; reflexivity).
    iEval (rewrite HsetD) in "Hop".
    assert (Hpc6a : ret_pc (Z9 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x6a)) by (rewrite HZ9ra; pcw).
    iEval (rewrite Hpc6a) in "Hpc".
    iEval (rewrite HbnoD) in "HfsbD".
    pose proof Hcs3 as Hcs3_cs.
    assert (HmL2s2 : mL2 !!! Regidx Rs2 = bnode kk2)
      by (rewrite (callee_saved_lookup Hcs3_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HZ9s2).
    assert (HmL2s1 : mL2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs3_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HZ9s1).
    assert (HmL2sp : ba_sp m mL2).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HZ9sp. }
    assert (HmL2thr : ba_thr9 m mL2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs3_cs c Hcs).
      exact (HZ9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    (* ===== +0x6a c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x6a)) Ra0 Rs2
              mL2 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6a").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (ZA := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL2 Rs2))]> mL2).
    assert (HZAa0 : ZA !!! Regidx Ra0 = bnode kk2).
    { rewrite /ZA upd_eq. rgne. rewrite HmL2s2. apply add_vec_zero_l. }
    assert (HZAs1 : ZA !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /ZA upd_ne; [exact HmL2s1 | nz]).
    assert (HZAsp : ba_sp m ZA)
      by (rewrite /ba_sp /ZA upd_ne; [exact HmL2sp | nz]).
    assert (HZAthr : ba_thr9 m ZA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /ZA upd_ne; [| regne].
      exact (HmL2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x6a) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    (* ===== +0x6c jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x6c)) Rra
              (mword_of_int 2096808 : mword 21) ZA (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6c").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (ZB := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x6c) : mword 64) 4)]> ZA).
    assert (Htgtbl2 : add_vec (mword_of_int (KernelSyms.balloc + 0x6c) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096808 : mword 21))
                      = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl2) in "Hpc".
    assert (HZBa0 : ZB !!! Regidx Ra0 = bnode kk2)
      by (rewrite /ZB upd_ne; [exact HZAa0 | nz]).
    assert (HZBs1 : ZB !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /ZB upd_ne; [exact HZAs1 | nz]).
    assert (HZBsp : ba_sp m ZB)
      by (rewrite /ba_sp /ZB upd_ne; [exact HZAsp | nz]).
    assert (HZBra : ZB !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x6c) : mword 64) 4)
      by (rewrite /ZB; apply upd_eq).
    assert (HZBthr : ba_thr9 m ZB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /ZB upd_ne; [| regne].
      exact (HZAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID13 CID15 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID12) (CIDb := CID15) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl2 : (K_brelse <= K - 10)%nat) by (lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk2
              pidv dev bnoD dq ZB (K - 10)%nat eb (proc_addr j)
              (replicate BSIZE (bv_0 8)) bsd0 true b lks Vpr
              HKbl2 Hkk2 HZBa0
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID16 Hq16 mR2) "%Hcs4 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc70 : ret_pc (ZB !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x70)) by (rewrite HZBra; pcw).
    iEval (rewrite Hpc70) in "Hpc".
    pose proof Hcs4 as Hcs4_cs.
    assert (HmR2s1 : mR2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs4_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HZBs1).
    assert (HmR2sp : ba_sp m mR2).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs4_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HZBsp. }
    assert (HmR2thr : ba_thr9 m mR2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs4_cs c Hcs).
      exact (HZBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    (* [log_write]/[brelse] do not thread the complement, so [Hextc]/[Hextm]
       are still at [CID4] (bread's own delivery hart) -- one wide hop
       straight to [ba_restore]'s entry hart. *)
    iDestruct (IntrDefs.trap_csrs_ext_transport CID4 CID16 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID4 CID16 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_restore (CID0 := CID16)  j γfs bn γ cov logstart bmapstart size
              used bi u cr Sb bnoD pidv dq dqb dqs m mR2 K eb b lks
              Vpr HK HmR2sp HmR2thr ltac:(rewrite HmR2s1 HbnoDsext; reflexivity)
              HbnoDnz
              ltac:(rewrite -bb_uint32 HbnoD; exact Hbicov)
              ltac:(rewrite -bb_uint32 HbnoD; exact Hbilog)
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hppid Hsbsz Hsbbm Hsl
                    [HfsbD] [Hown] [Hbmr] Hop [Hcont]").
    { iEval (rewrite -bb_uint32 HbnoD). iExact "HfsbD". }
    { iEval (rewrite -bb_uint32 HbnoD). iExact "Hown". }
    { iEval (rewrite -bb_uint32 HbnoD). iExact "Hbmr". }
    { iApply (wp_next_shift (b := true) (CIDa := CID15) (CIDb := CID16) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BallocBzero.

(* ===================================================================== *)
(*  +0x38 .. +0x7c : FOUND A FREE BIT.  Set it, log_write + brelse the    *)
(*  bitmap block, then the INLINED bzero (bread / memset / log_write /    *)
(*  brelse) of the allocated block, then pop s2..s8 and fall into the     *)
(*  epilogue with s1 = b + bi.                                           *)
(* ===================================================================== *)
Section BallocAlloc.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_alloc `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (bi : Z) (u : nat) (cr : bool) (Sb : gset Z)
      (kk : nat) (bnoB : mword 32) (bsdX : list (bv 8)) (dX : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_balloc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bi < size ->
    bi ∉ used ->
    bitmap_ok cov logstart size used ->
    uint bnoB = bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    (kk < NBUF)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    ba_sp m M ->
    ba_thr9 m M ->
    M !!! Regidx Ra5 = (mword_of_int (bi `div` 8) : mword 64) ->
    M !!! Regidx Ra2 =
      (zero_extend' 64 (bm_byte used (bi `div` 8) : mword 8) : mword 64) ->
    M !!! Regidx Ra3 = (mword_of_int (2 ^ (bi `mod` 8)) : mword 64) ->
    M !!! Regidx Rs1 = (mword_of_int bi : mword 64) ->
    M !!! Regidx Rs2 = bnode kk ->
    M !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64) ->
    (* THE CREDIT'S PREMISE: the bitmap block is already in this op's set *)
    (cr = true -> bmapstart ∈ Sb) ->
    (* ba_alloc's own cone touches "log" (log_write, directly and via
       ba_bzero) and "bcache" (brelse, directly and via ba_bzero) -- "log"
       is the floor *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0x38) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 1 -∗
    log_opS γ (2 + u) Sb -∗
    fsblock γfs bmapstart (bitmap_bytes used) -∗
    free_pool γfs size used -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bnoB
       (bitmap_bytes used) bsdX dX -∗
    ba_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsize Hbirange Hbinu Hok HbnoB Hbmcov Hbmlog Hkk Hj Hgl
           Hsp Hthr Ha5 Ha2 Ha3 Hs1 Hs2 Hs7 Hcred Hbelow.
    pose proof HK as HK'. 
    destruct Hgeom as [Hcovok Hlogsub].
    (* ---- all the arithmetic, over plain [Z], before a single step ---- *)
    assert (HbiBPB : 0 <= bi < BPB) by lia.
    destruct (ba_range bi ltac:(lia))
      as (Hbi0 & Hbi8192 & Hbi31 & Hbi32 & Hbi64 & Hrmod & Hqrange & Hbilt).
    destruct (ba_range_lt bi HbiBPB) as [Hdlt Hdz].
    destruct (bitmap_ok_free cov logstart size used bi Hok Hbirange Hbinu)
      as [Hbicov Hbilog].
    assert (Hbinz : bi <> 0)
      by (exact (bitmap_ok_nonzero cov logstart size used bi Hcovok Hok
                   Hbirange Hbinu)).
    remember (bi `mod` 8) as r eqn:Hreq.
    remember (bi `div` 8) as q eqn:Hqeq.
    remember (Z.to_nat q) as d eqn:Hdeq.
    (* the allocated block's number, as the 32-bit word the ABI passes *)
    set (bnoD := (mword_of_int bi : mword 32)).
    assert (HbnoD : uint bnoD = bi).
    { rewrite /bnoD bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (HbnoDlt : (uint bnoD < 2147483648)%Z) by (rewrite HbnoD; lia).
    assert (HbnoDcov : uint bnoD ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite HbnoD; exact Hbicov).
    assert (HbnoDsext : (sign_extend' 64 bnoD : mword 64) = mword_of_int bi).
    { rewrite /bnoD. apply sext32_64_small.
      change (2^31)%Z with 2147483648%Z. lia. }
    assert (HbnoBlt : (Z.of_nat 0 + 2 < 2 ^ 31)%Z)
      by (change (2^31)%Z with 2147483648%Z; lia).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hprocs Hframe Hppid Hsbsz Hsbbm #Hdevi #Hdgeom #Hdlock Hsl Hop
              Hfsbm Hpool Hlk Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    (* ---- the block leaves the pool, with its content half and token ---- *)
    iDestruct (free_pool_take γfs size used bi Hbirange Hbinu with "Hpool")
      as "[Hblk Hpool]".
    iDestruct "Hblk" as (bsD) "(%HbsDlen & HfsbD & Hown)".
    (* ---- the bitmap buffer's byte ---- *)
    iEval (rewrite /bio_locked) in "Hlk".
    iDestruct (iu_held_swap with "Hlk") as "[Hbuf Hlkback]".
    assert (Hbmlen : length (bitmap_bytes used) = 1024%nat)
      by (rewrite bitmap_bytes_length; reflexivity).
    assert (Hbmlen' : length (bitmap_bytes (used ∪ {[ bi ]})) = 1024%nat)
      by (rewrite bitmap_bytes_length; reflexivity).
    assert (Hlkused : bitmap_bytes used !!! d = bm_byte used q).
    { rewrite (list_lookup_total_correct (bitmap_bytes used) d
                 (bm_byte used (Z.of_nat d))
                 (bitmap_bytes_lookup used d Hdlt)).
      rewrite Hdz. reflexivity. }
    assert (Hlknew : bitmap_bytes (used ∪ {[ bi ]}) !!! d
                     = bm_byte (used ∪ {[ bi ]}) q).
    { rewrite (list_lookup_total_correct (bitmap_bytes (used ∪ {[ bi ]})) d
                 (bm_byte (used ∪ {[ bi ]}) (Z.of_nat d))
                 (bitmap_bytes_lookup (used ∪ {[ bi ]}) d Hdlt)).
      rewrite Hdz. reflexivity. }
    iDestruct (ba_buf_byte (bpa kk) bnoB (mword_of_int 0 : mword 32)
                 (bitmap_bytes used) d Hbmlen Hdlt with "Hbuf")
      as "[Hbyte Hbyteback]".
    iEval (rewrite Hlkused) in "Hbyte".
    iPoseProof (bai_038 with "Htext") as "Hi38".
    iPoseProof (bai_03a with "Htext") as "Hi3a".
    iPoseProof (bai_03c with "Htext") as "Hi3c".
    iPoseProof (bai_040 with "Htext") as "Hi40".
    iPoseProof (bai_042 with "Htext") as "Hi42".
    iPoseProof (bai_046 with "Htext") as "Hi46".
    iPoseProof (bai_048 with "Htext") as "Hi48".
    iPoseProof (bai_04c with "Htext") as "Hi4c".
    iPoseProof (bai_04e with "Htext") as "Hi4e".
    iPoseProof (bai_050 with "Htext") as "Hi50".
    iPoseProof (bai_054 with "Htext") as "Hi54".
    iPoseProof (bai_056 with "Htext") as "Hi56".
    iPoseProof (bai_05a with "Htext") as "Hi5a".
    iPoseProof (bai_05c with "Htext") as "Hi5c".
    iPoseProof (bai_060 with "Htext") as "Hi60".
    iPoseProof (bai_064 with "Htext") as "Hi64".
    iPoseProof (bai_066 with "Htext") as "Hi66".
    iPoseProof (bai_06a with "Htext") as "Hi6a".
    iPoseProof (bai_06c with "Htext") as "Hi6c".
    (* ===== +0x38 c.add a5,a5,s2 : a5 := bp + bi/8 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.balloc + 0x38)) Ra5 Rs2
              M (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi38").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (A0 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget M Ra5) (rget M Rs2))]> M).
    assert (HA0a5 : A0 !!! Regidx Ra5
                    = add_vec (mword_of_int (Z.of_nat d)) (bnode kk)).
    { rewrite /A0 upd_eq. rgne. rgne. rewrite Ha5 Hs2 Hdz. reflexivity. }
    assert (HA0a2 : A0 !!! Regidx Ra2
                    = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /A0 upd_ne; [exact Ha2 | nz]).
    assert (HA0a3 : A0 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /A0 upd_ne; [exact Ha3 | nz]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A0 upd_ne; [exact Hs1 | nz]).
    assert (HA0s2 : A0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /A0 upd_ne; [exact Hs2 | nz]).
    assert (HA0s7 : A0 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A0 upd_ne; [exact Hs7 | nz]).
    assert (HA0sp : ba_sp m A0)
      by (rewrite /ba_sp /A0 upd_ne; [exact Hsp | nz]).
    assert (HA0thr : ba_thr9 m A0).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A0 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.balloc + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3a c.or a2,a2,a3 : the byte with the bit set ===== *)
    iApply (wp_cor_s_sconf (mword_of_int (KernelSyms.balloc + 0x3a)) Ra2 Ra2 Ra3
              (or_vec (zero_extend' 64 (bm_byte used q : mword 8) : mword 64)
                      (mword_of_int (2 ^ r) : mword 64))
              A0 (K - 10)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HA0a2 HA0a3; reflexivity)
              with "Hcg Hpc Hi3a").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (A1 := <[Regidx Ra2 := regval_into_reg
                  (or_vec (zero_extend' 64 (bm_byte used q : mword 8) : mword 64)
                          (mword_of_int (2 ^ r) : mword 64))]> A0).
    assert (HA1a2 : A1 !!! Regidx Ra2
                    = or_vec (zero_extend' 64 (bm_byte used q : mword 8) : mword 64)
                             (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /A1; apply upd_eq).
    assert (HA1a5 : A1 !!! Regidx Ra5
                    = add_vec (mword_of_int (Z.of_nat d)) (bnode kk))
      by (rewrite /A1 upd_ne; [exact HA0a5 | nz]).
    assert (HA1s1 : A1 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A1 upd_ne; [exact HA0s1 | nz]).
    assert (HA1s2 : A1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /A1 upd_ne; [exact HA0s2 | nz]).
    assert (HA1s7 : A1 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A1 upd_ne; [exact HA0s7 | nz]).
    assert (HA1sp : ba_sp m A1)
      by (rewrite /ba_sp /A1 upd_ne; [exact HA0sp | nz]).
    assert (HA1thr : ba_thr9 m A1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A1 upd_ne; [| regne].
      exact (HA0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c sb a2,88(a5) : bp->data[bi/8] |= m ===== *)
    assert (Hstadr : add_vec (rget A1 Ra5)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bpa kk)) d).
    { rgne. rewrite HA1a5. apply ba_data_off'. }
    iEval (rewrite -Hstadr) in "Hbyte".
    iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.balloc + 0x3c)) Ra2 Ra5
              (mword_of_int 88 : mword 12) A1 (K - 10)%nat
              (bm_byte used q) b with "Hcg Hpc Hi3c Hbyte").
    iIntros (CID3 Hq3) "Hcg Hpc Hbyte".
    iEval (rewrite Hstadr; rgne; rewrite HA1a2 Hqeq Hreq
                   (bal_sb_setbit used bi Hbi0) -Hqeq -Hlknew) in "Hbyte".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x3c) : mword 64) 4
                    = mword_of_int (KernelSyms.balloc + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ---- the buffer, at the image of [used ∪ {bi}] ---- *)
    iDestruct ("Hbyteback" $! (bitmap_bytes (used ∪ {[ bi ]}))
                 with "[%] [%] Hbyte") as "Hbuf".
    { exact Hbmlen'. }
    { intros k Hk Hne.
      rewrite -(bitmap_bytes_set_bit used bi HbiBPB) -Hqeq -Hdeq.
      rewrite !list_lookup_total_alt.
      rewrite list_lookup_insert_ne;
        [reflexivity | intro Hx; apply Hne; symmetry; exact Hx]. }
    iDestruct ("Hlkback" with "Hbuf") as "Hheld".
    (* ===== +0x40 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x40)) Ra0 Rs2
              A1 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi40").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (A2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget A1 Rs2))]> A1).
    assert (HA2a0 : A2 !!! Regidx Ra0 = bnode kk).
    { rewrite /A2 upd_eq. rgne. rewrite HA1s2. apply add_vec_zero_l. }
    assert (HA2s1 : A2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1s1 | nz]).
    assert (HA2s2 : A2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /A2 upd_ne; [exact HA1s2 | nz]).
    assert (HA2s7 : A2 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1s7 | nz]).
    assert (HA2sp : ba_sp m A2)
      by (rewrite /ba_sp /A2 upd_ne; [exact HA1sp | nz]).
    assert (HA2thr : ba_thr9 m A2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A2 upd_ne; [| regne].
      exact (HA1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 jal ra,log_write ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x42)) Rra
              (mword_of_int 4218 : mword 21) A2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi42").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x42) : mword 64) 4)]> A2).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.balloc + 0x42) : mword 64)
                       (sign_extend' 64 (mword_of_int 4218 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HA3a0 : A3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /A3 upd_ne; [exact HA2a0 | nz]).
    assert (HA3s1 : A3 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s1 | nz]).
    assert (HA3s2 : A3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /A3 upd_ne; [exact HA2s2 | nz]).
    assert (HA3s7 : A3 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s7 | nz]).
    assert (HA3sp : ba_sp m A3)
      by (rewrite /ba_sp /A3 upd_ne; [exact HA2sp | nz]).
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x42) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3thr : ba_thr9 m A3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A3 upd_ne; [| regne].
      exact (HA2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKlw : (K_log_write <= K - 10)%nat) by (lia).
    iEval (rewrite -HbnoB) in "Hfsbm".
    (* THE BITMAP BLOCK'S log_write, CREDITED: there is exactly ONE bitmap
       block, so a caller that has already logged it in this batch pays
       nothing here and the unit comes straight back. *)
    iApply (LW.wp_log_write_gen bn γ γfs γd cov logstart dev kk pidv bnoB
              (bitmap_bytes (used ∪ {[ bi ]})) (bitmap_bytes used) bsdX dX (1 + u)%nat
              cr Sb
              A3 0%nat eb (proc_addr j) (K - 10)%nat b lks
              HKlw HbnoBlt Hkk HA3a0
              ltac:(rewrite HbnoB; exact Hbmcov)
              ltac:(rewrite HbnoB; exact Hbmlog)
              ltac:(rewrite HbnoB; exact Hcred)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hop Hfsbm Hheld").
    all: try lkbelow.
    iIntros (CID6 Hq6 mL) "Hcg Hcnt Hpc %Hcs1 Hop Hfsbm Hlk Hsl".
    assert (HbudgeB : (if cr then S (1 + u) else (1 + u))%nat
                      = S (if cr then S u else u))
      by (destruct cr; reflexivity).
    assert (HsetB : (Sb ∪ {[uint bnoB]} : gset Z) = Sb ∪ {[bmapstart]})
      by (rewrite HbnoB; reflexivity).
    iEval (rewrite HbudgeB HsetB) in "Hop".
    assert (Hpc46 : ret_pc (A3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x46)) by (rewrite HA3ra; pcw).
    iEval (rewrite Hpc46) in "Hpc".
    iEval (rewrite HbnoB) in "Hfsbm".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmLs1 : mL !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HA3s1).
    assert (HmLs2 : mL !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HA3s2).
    assert (HmLs7 : mL !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs7 ltac:(vm_compute; reflexivity));
          exact HA3s7).
    assert (HmLsp : ba_sp m mL).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA3sp. }
    assert (HmLthr : ba_thr9 m mL).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HA3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    (* ===== +0x46 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x46)) Ra0 Rs2
              mL (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi46").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (A4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL Rs2))]> mL).
    assert (HA4a0 : A4 !!! Regidx Ra0 = bnode kk).
    { rewrite /A4 upd_eq. rgne. rewrite HmLs2. apply add_vec_zero_l. }
    assert (HA4s1 : A4 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A4 upd_ne; [exact HmLs1 | nz]).
    assert (HA4s7 : A4 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A4 upd_ne; [exact HmLs7 | nz]).
    assert (HA4sp : ba_sp m A4)
      by (rewrite /ba_sp /A4 upd_ne; [exact HmLsp | nz]).
    assert (HA4thr : ba_thr9 m A4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A4 upd_ne; [| regne].
      exact (HmLthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.balloc + 0x48)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    (* ===== +0x48 jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0x48)) Rra
              (mword_of_int 2096844 : mword 21) A4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi48").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0x48) : mword 64) 4)]> A4).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.balloc + 0x48) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096844 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HA5a0 : A5 !!! Regidx Ra0 = bnode kk)
      by (rewrite /A5 upd_ne; [exact HA4a0 | nz]).
    assert (HA5s1 : A5 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s1 | nz]).
    assert (HA5s7 : A5 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s7 | nz]).
    assert (HA5sp : ba_sp m A5)
      by (rewrite /ba_sp /A5 upd_ne; [exact HA4sp | nz]).
    assert (HA5ra : A5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0x48) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5thr : ba_thr9 m A5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /A5 upd_ne; [| regne].
      exact (HA4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID6 CID8 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID5) (CIDb := CID8) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 10)%nat) by (lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bnoB dq A5 (K - 10)%nat eb (proc_addr j)
              (bitmap_bytes (used ∪ {[ bi ]})) bsdX true b lks Vpr
              HKbl Hkk HA5a0
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID9 Hq9 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc4c : ret_pc (A5 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.balloc + 0x4c)) by (rewrite HA5ra; pcw).
    iEval (rewrite Hpc4c) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRs1 : mR !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs2_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HA5s1).
    assert (HmRs7 : mR !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcs2_cs Rs7 ltac:(vm_compute; reflexivity));
          exact HA5s7).
    assert (HmRsp : ba_sp m mR).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA5sp. }
    assert (HmRthr : ba_thr9 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HA5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    (* the bitmap is DONE: close the resource at the new used set *)
    assert (Hokadd : bitmap_ok cov logstart size (used ∪ {[ bi ]}))
      by (apply bitmap_ok_add; exact Hok).
    iDestruct (bitmap_res_close γfs bmapstart cov logstart size
                 (used ∪ {[ bi ]}) Hokadd with "Hfsbm Hpool") as "Hbmr".
    (* [log_write]/[brelse] do not thread the complement, so [Hextc]/[Hextm]
       are still at [CID0] -- one wide hop straight to [ba_bzero]'s entry
       hart. *)
    iDestruct (IntrDefs.trap_csrs_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_bzero (CID0 := CID9)  γs j γl γu γd γk pd pav pu γfs bn γ
              cov logstart bmapstart size dev used bi u cr Sb bsD
              pidv dq dqb dqs m mR K eb b lks
              Vpr HK Hsize Hbirange Hbicov Hbilog Hbinz HbsDlen Hj Hgl
              HmRsp HmRthr HmRs1 HmRs7 Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlctx Hprocs Hframe Hppid Hsbsz Hsbbm Hdevi Hdgeom Hdlock Hsl Hop
                    Hbmr HfsbD Hown [Hcont]").
    { iApply (wp_next_shift (b := true) (CIDa := CID8) (CIDb := CID9) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End BallocAlloc.


(* ===================================================================== *)
(*  +0xb6 .. +0xe6 : THE INNER BIT SCAN -- balloc's only loop.            *)
(*                                                                        *)
(*  By induction on the fuel [Z.to_nat (BPB - bi)].  The invariant is just *)
(*  [0 <= bi <= BPB] plus the register file: NOTHING has to be said about  *)
(*  the bits already scanned, because both exits hand the bitmap back      *)
(*  untouched and the success arm gets [bi ∉ used] from the branch itself. *)
(*                                                                        *)
(*  Three branches: the [bgeu] at +0xb6 (exit to +0x8a), the [c.beqz] at   *)
(*  +0xdc (a clear bit -- allocate, at +0x38), and the [bne] at +0xe2      *)
(*  (bi reached BPB -- exit through +0xe6 to +0x8a).                       *)
(* ===================================================================== *)
Section BallocScan.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Local Lemma ba_scan `{GEN : GenId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names) (γpr : gname)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (u : nat) (cr : bool) (Sb : gset Z)
      (kk : nat) (bnoB : mword 32) (bsdX : list (bv 8)) (dX : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) (fuel : nat) :
    (K_balloc <= K)%nat ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    uint bnoB = bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    bitmap_ok cov logstart size used ->
    (kk < NBUF)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (* THE CREDIT'S PREMISE: the bitmap block is already in this op's set *)
    (cr = true -> bmapstart ∈ Sb) ->
    forall (CIDx : CpuId) (bi : Z) (M : regfile),
    (Z.to_nat (BPB - bi) <= fuel)%nat ->
    0 <= bi <= BPB ->
    ba_sp m M ->
    ba_thr9 m M ->
    M !!! Regidx Ra0 = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64) ->
    M !!! Regidx Ra4 = (mword_of_int bi : mword 64) ->
    M !!! Regidx Rs1 = (mword_of_int bi : mword 64) ->
    M !!! Regidx Rs2 = bnode kk ->
    M !!! Regidx Rs3 = (mword_of_int 1 : mword 64) ->
    M !!! Regidx Rs4 = (mword_of_int 8192 : mword 64) ->
    M !!! Regidx Rs5 = (mword_of_int 0 : mword 64) ->
    M !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64) ->
    M !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64) ->
    M !!! Regidx Rs8 = (mword_of_int 8192 : mword 64) ->
    (* ba_scan's own cone touches "log" (via ba_alloc's log_write) and
       "bcache" (via bread's inlining in ba_alloc/ba_exhaust) -- "log" is
       the floor *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 10)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.balloc + 0xb6) : mword 64) -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    ba_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 1 -∗
    log_opS γ (2 + u) Sb -∗
    fsblock γfs bmapstart (bitmap_bytes used) -∗
    free_pool γfs size used -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bnoB
       (bitmap_bytes used) bsdX dX -∗
    ba_cont (CID0 := CIDx) γfs bn γ cov logstart bmapstart size used u cr Sb
            pidv dq dqb dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hpk Hgeom Hsize HbnoB Hbmcov Hbmlog Hok Hkk Hj Hgl Hcred.
    pose proof HK as HK'. 
    pose proof Hsize as Hsz'. rewrite BPB_value in Hsz'.
    pose proof Hgeom as [Hcovok Hlogsub].
    induction fuel as [|fuel IH];
      intros CIDx bi M Hfuel Hbi Hsp Hthr Ha0 Ha4 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hbelow;
      iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkdata Hpc #Hpenv #Hbio #Hlctx #Hprocs Hframe Hppid Hsbsz Hsbbm #Hdevi #Hdgeom
                #Hdlock Hsl Hop Hfsbm Hpool Hlk Hcont";
      iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm; cbn in Hbm;
      pose proof Hbi as Hbi'; rewrite BPB_value in Hbi';
      iPoseProof (bai_0b6 with "Htext") as "Hib6";
      iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv";
      assert (Hszsext : (sign_extend' 64 (mword_of_int size : mword 32) : mword 64)
                        = mword_of_int size)
        by (apply sext32_64_small; change (2^31)%Z with 2147483648%Z; lia).
    - (* ---- FUEL 0: the scan is at BPB, so [bgeu] is taken ---- *)
      assert (HbiB : bi = 8192) by (rewrite BPB_value in Hfuel; lia).
      assert (Hcmp : zopz0zKzJ_u (rget M Rs1) (rget M Ra0) = true).
      { rgne. rgne. rewrite Hs1 Ha0 Hszsext.
        rewrite (ba_bgeu_moi bi size ltac:(lia) ltac:(lia)).
        apply Z.geb_le. lia. }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.balloc + 0xb6))
                (mword_of_int 8148 : mword 13) Ra0 Rs1 M (K - 10)%nat b
                ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hib6").
      iApply bi.later_intro. iIntros (CID1 Hq1) "Hcg Hpc".
      assert (Hjt : add_vec (mword_of_int (KernelSyms.balloc + 0xb6) : mword 64)
                      (sign_extend' 64 (mword_of_int 8148 : mword 13))
                    = mword_of_int (KernelSyms.balloc + 0x8a)) by pcw.
      iEval (rewrite Hjt) in "Hpc".
      iDestruct (bitmap_res_close γfs bmapstart cov logstart size used Hok
                   with "Hfsbm Hpool") as "Hbmr".
      iDestruct (cpu_own_transport CIDx CID1 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (IntrDefs.trap_csrs_ext_transport CIDx CID1 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (IntrDefs.cpu_claim_ext_transport CIDx CID1 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iApply (ba_exhaust (CID0 := CID1)  γs j γfs γd bn γ γpr γu cov logstart
                bmapstart size dev used u cr Sb kk bnoB (bitmap_bytes used) bsdX dX
                pidv dq dqb dqs m M K eb b lks Vpr HK Hpk Hsize Hsp Hthr Hs2 Hs5 Hs6 Hs8 Hkk Hbelow
                with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hbio Hprocs Hframe Hppid Hsbsz Hsbbm Hsl Hbmr Hop Hlk [Hcont]").
      { iApply (wp_next_shift (b := true) (CIDa := CIDx) (CIDb := CID1) ltac:(wp_next_chain)
                  with "Hcont"). }
    - (* ---- FUEL S: the full loop body ---- *)
      destruct (Z.geb bi size) eqn:Hge.
      + (* +0xb6 TAKEN: b + bi >= sb.size, the scan is over *)
        assert (Hcmp : zopz0zKzJ_u (rget M Rs1) (rget M Ra0) = true).
        { rgne. rgne. rewrite Hs1 Ha0 Hszsext.
          rewrite (ba_bgeu_moi bi size ltac:(lia) ltac:(lia)). exact Hge. }
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.balloc + 0xb6))
                  (mword_of_int 8148 : mword 13) Ra0 Rs1 M (K - 10)%nat b
                  ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hib6").
        iApply bi.later_intro. iIntros (CID1 Hq1) "Hcg Hpc".
        assert (Hjt : add_vec (mword_of_int (KernelSyms.balloc + 0xb6) : mword 64)
                        (sign_extend' 64 (mword_of_int 8148 : mword 13))
                      = mword_of_int (KernelSyms.balloc + 0x8a)) by pcw.
        iEval (rewrite Hjt) in "Hpc".
        iDestruct (bitmap_res_close γfs bmapstart cov logstart size used Hok
                     with "Hfsbm Hpool") as "Hbmr".
        iDestruct (cpu_own_transport CIDx CID1 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (IntrDefs.trap_csrs_ext_transport CIDx CID1 eb (proc_addr j)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (IntrDefs.cpu_claim_ext_transport CIDx CID1 eb (proc_addr j)
                     ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
        iApply (ba_exhaust (CID0 := CID1)  γs j γfs γd bn γ γpr γu cov logstart
                  bmapstart size dev used u cr Sb kk bnoB (bitmap_bytes used) bsdX dX
                  pidv dq dqb dqs m M K eb b lks Vpr HK Hpk Hsize Hsp Hthr Hs2 Hs5 Hs6 Hs8 Hkk Hbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hbio Hprocs Hframe Hppid Hsbsz Hsbbm Hsl Hbmr Hop Hlk [Hcont]").
        { iApply (wp_next_shift (b := true) (CIDa := CIDx) (CIDb := CID1) ltac:(wp_next_chain)
                    with "Hcont"). }
      + (* +0xb6 FALL-THROUGH: bi < sb.size, so this bit is in range *)
        (* [Z.geb_gt] does not exist; the contrapositive of [Z.geb_le] is the
           way from the FALSE branch of a [bgeu] back to a strict bound. *)
        assert (Hbilt : bi < size).
        { destruct (Z.lt_ge_cases bi size) as [Hlt|Hc]; [exact Hlt|].
          exfalso. assert (Hc' : size <= bi) by lia.
          rewrite (proj2 (Z.geb_le bi size) Hc') in Hge. discriminate. }
        assert (Hbirange : 0 <= bi < size) by lia.
        assert (HbiBPB : 0 <= bi < BPB) by lia.
        destruct (ba_range bi ltac:(lia))
          as (Hbi0 & Hbi8192 & Hbi31 & Hbi32 & Hbi64 & Hrmod & Hqrange & Hbi31').
        destruct (ba_range_lt bi HbiBPB) as [Hdlt Hdz].
        assert (Hbisext : (mword_of_int bi : mword 64)
                          = sign_extend' 64 (mword_of_int bi : mword 32))
          by (symmetry; apply sext32_64_small;
              change (2^31)%Z with 2147483648%Z; lia).
        assert (Hbiu32 : bv_unsigned (mword_of_int bi : mword 32) = bi)
          by (apply moi32_small; change (2^32)%Z with 4294967296%Z; lia).
        remember (bi `mod` 8) as r eqn:Hreq.
        remember (bi `div` 8) as q eqn:Hqeq.
        remember (Z.to_nat q) as d eqn:Hdeq.
        assert (Hcmp : zopz0zKzJ_u (rget M Rs1) (rget M Ra0) = false).
        { rgne. rgne. rewrite Hs1 Ha0 Hszsext.
          rewrite (ba_bgeu_moi bi size ltac:(lia) ltac:(lia)). exact Hge. }
        iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.balloc + 0xb6))
                  (mword_of_int 8148 : mword 13) Ra0 Rs1 M (K - 10)%nat b
                  ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hib6").
        iIntros (CID1 Hq1) "Hcg Hpc".
        assert (Hppba : add_vec_int (mword_of_int (KernelSyms.balloc + 0xb6) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xba)) by pcw.
        iEval (rewrite Hppba) in "Hpc".
        iPoseProof (bai_0ba with "Htext") as "Hiba".
        iPoseProof (bai_0be with "Htext") as "Hibe".
        iPoseProof (bai_0c2 with "Htext") as "Hic2".
        iPoseProof (bai_0c6 with "Htext") as "Hic6".
        iPoseProof (bai_0ca with "Htext") as "Hica".
        iPoseProof (bai_0cc with "Htext") as "Hicc".
        iPoseProof (bai_0d0 with "Htext") as "Hid0".
        iPoseProof (bai_0d4 with "Htext") as "Hid4".
        iPoseProof (bai_0d8 with "Htext") as "Hid8".
        iPoseProof (bai_0dc with "Htext") as "Hidc".
        iPoseProof (bai_0de with "Htext") as "Hide".
        iPoseProof (bai_0e0 with "Htext") as "Hie0".
        iPoseProof (bai_0e2 with "Htext") as "Hie2".
        iPoseProof (bai_0e6 with "Htext") as "Hie6".
        (* ===== +0xba andi a3,a4,7 : a3 := bi % 8 ===== *)
        iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.balloc + 0xba)) Ra3 Ra4
                  (mword_of_int 7 : mword 12) (mword_of_int r : mword 64)
                  M (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rewrite Ha4 bal_andi7 moi64_unsigned
                          (bvw64_small bi ltac:(lia)) -Hreq; reflexivity)
                  with "Hcg Hpc Hiba").
        iIntros (CID2 Hq2) "Hcg Hpc".
        set (S0 := <[Regidx Ra3 := regval_into_reg (mword_of_int r : mword 64)]> M).
        assert (HS0a3 : S0 !!! Regidx Ra3 = (mword_of_int r : mword 64))
          by (rewrite /S0; apply upd_eq).
        assert (HS0a4 : S0 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S0 upd_ne; [exact Ha4 | nz]).
        assert (HS0a0 : S0 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S0 upd_ne; [exact Ha0 | nz]).
        assert (HS0s1 : S0 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs1 | nz]).
        assert (HS0s2 : S0 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S0 upd_ne; [exact Hs2 | nz]).
        assert (HS0s3 : S0 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs3 | nz]).
        assert (HS0s4 : S0 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs4 | nz]).
        assert (HS0s5 : S0 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs5 | nz]).
        assert (HS0s6 : S0 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs6 | nz]).
        assert (HS0s7 : S0 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs7 | nz]).
        assert (HS0s8 : S0 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S0 upd_ne; [exact Hs8 | nz]).
        assert (HS0sp : ba_sp m S0)
          by (rewrite /ba_sp /S0 upd_ne; [exact Hsp | nz]).
        assert (HS0thr : ba_thr9 m S0).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S0 upd_ne; [| regne].
          exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.balloc + 0xba) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xbe)) by pcw.
        iEval (rewrite Hppbe) in "Hpc".
        (* ===== +0xbe sllw a3,s3,a3 : a3 := m = 1 << (bi % 8) ===== *)
        iApply (wp_sllw_s_sconf (mword_of_int (KernelSyms.balloc + 0xbe)) Ra3 Rs3 Ra3
                  S0 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibe").
        iIntros (CID3 Hq3) "Hcg Hpc".
        set (S1 := <[Regidx Ra3 := regval_into_reg
                      (sign_extend' 64
                         (shift_bits_left
                            (subrange_vec_dec (rget S0 Rs3) 31 0 : mword 32)
                            (subrange_vec_dec
                               (subrange_vec_dec (rget S0 Ra3) 31 0 : mword 32)
                               4 0)))]> S0).
        assert (HS1a3 : S1 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64)).
        { rewrite /S1 upd_eq. rgne. rgne. rewrite HS0s3 HS0a3.
          apply bal_sllw_mask. exact Hrmod. }
        assert (HS1a4 : S1 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0a4 | nz]).
        assert (HS1a0 : S1 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0a0 | nz]).
        assert (HS1s1 : S1 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s1 | nz]).
        assert (HS1s2 : S1 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S1 upd_ne; [exact HS0s2 | nz]).
        assert (HS1s3 : S1 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s3 | nz]).
        assert (HS1s4 : S1 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s4 | nz]).
        assert (HS1s5 : S1 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s5 | nz]).
        assert (HS1s6 : S1 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s6 | nz]).
        assert (HS1s7 : S1 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s7 | nz]).
        assert (HS1s8 : S1 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S1 upd_ne; [exact HS0s8 | nz]).
        assert (HS1sp : ba_sp m S1)
          by (rewrite /ba_sp /S1 upd_ne; [exact HS0sp | nz]).
        assert (HS1thr : ba_thr9 m S1).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S1 upd_ne; [| regne].
          exact (HS0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xbe) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xc2)) by pcw.
        iEval (rewrite Hppc2) in "Hpc".
        (* ===== +0xc2 sraiw a5,a4,0x1f : the sign word, which is 0 ===== *)
        iApply (wp_sraiw_s_sconf (mword_of_int (KernelSyms.balloc + 0xc2)) Ra5 Ra4
                  (mword_of_int 31 : mword 5) (mword_of_int 0 : mword 64)
                  S1 (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rewrite HS1a4 Hbisext;
                        apply bal_sraiw31_zero; rewrite Hbiu32; lia)
                  with "Hcg Hpc Hic2").
        iIntros (CID4 Hq4) "Hcg Hpc".
        set (S2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> S1).
        assert (HS2a5 : S2 !!! Regidx Ra5 = (mword_of_int 0 : mword 64))
          by (rewrite /S2; apply upd_eq).
        assert (HS2a4 : S2 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1a4 | nz]).
        assert (HS2a3 : S2 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1a3 | nz]).
        assert (HS2a0 : S2 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1a0 | nz]).
        assert (HS2s1 : S2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s1 | nz]).
        assert (HS2s2 : S2 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S2 upd_ne; [exact HS1s2 | nz]).
        assert (HS2s3 : S2 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s3 | nz]).
        assert (HS2s4 : S2 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s4 | nz]).
        assert (HS2s5 : S2 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s5 | nz]).
        assert (HS2s6 : S2 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s6 | nz]).
        assert (HS2s7 : S2 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s7 | nz]).
        assert (HS2s8 : S2 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S2 upd_ne; [exact HS1s8 | nz]).
        assert (HS2sp : ba_sp m S2)
          by (rewrite /ba_sp /S2 upd_ne; [exact HS1sp | nz]).
        assert (HS2thr : ba_thr9 m S2).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S2 upd_ne; [| regne].
          exact (HS1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xc2) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xc6)) by pcw.
        iEval (rewrite Hppc6) in "Hpc".
        (* ===== +0xc6 srliw a5,a5,0x1d : the bias, still 0 ===== *)
        iApply (wp_srliw_s_sconf (mword_of_int (KernelSyms.balloc + 0xc6)) Ra5 Ra5
                  (mword_of_int 29 : mword 5) (mword_of_int 0 : mword 64)
                  S2 (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rewrite HS2a5; apply bal_srliw29_zero)
                  with "Hcg Hpc Hic6").
        iIntros (CID5 Hq5) "Hcg Hpc".
        set (S3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> S2).
        assert (HS3a5 : S3 !!! Regidx Ra5 = (mword_of_int 0 : mword 64))
          by (rewrite /S3; apply upd_eq).
        assert (HS3a4 : S3 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2a4 | nz]).
        assert (HS3a3 : S3 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2a3 | nz]).
        assert (HS3a0 : S3 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2a0 | nz]).
        assert (HS3s1 : S3 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s1 | nz]).
        assert (HS3s2 : S3 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S3 upd_ne; [exact HS2s2 | nz]).
        assert (HS3s3 : S3 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s3 | nz]).
        assert (HS3s4 : S3 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s4 | nz]).
        assert (HS3s5 : S3 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s5 | nz]).
        assert (HS3s6 : S3 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s6 | nz]).
        assert (HS3s7 : S3 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s7 | nz]).
        assert (HS3s8 : S3 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S3 upd_ne; [exact HS2s8 | nz]).
        assert (HS3sp : ba_sp m S3)
          by (rewrite /ba_sp /S3 upd_ne; [exact HS2sp | nz]).
        assert (HS3thr : ba_thr9 m S3).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S3 upd_ne; [| regne].
          exact (HS2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppca : add_vec_int (mword_of_int (KernelSyms.balloc + 0xc6) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xca)) by pcw.
        iEval (rewrite Hppca) in "Hpc".
        (* ===== +0xca c.addw a5,a5,a4 : add the zero bias back ===== *)
        iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.balloc + 0xca)) Ra5 Ra4
                  S3 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hica").
        iIntros (CID6 Hq6) "Hcg Hpc".
        set (S4 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64
                         (add_vec (subrange_vec_dec (rget S3 Ra5) 31 0 : mword 32)
                                  (subrange_vec_dec (rget S3 Ra4) 31 0 : mword 32)))]> S3).
        assert (HS4a5 : S4 !!! Regidx Ra5 = (mword_of_int bi : mword 64)).
        { rewrite /S4 upd_eq. rgne. rgne. rewrite HS3a5 HS3a4 Hbisext.
          rewrite bal_addw_zero_l. reflexivity. }
        assert (HS4a4 : S4 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3a4 | nz]).
        assert (HS4a3 : S4 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3a3 | nz]).
        assert (HS4a0 : S4 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3a0 | nz]).
        assert (HS4s1 : S4 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s1 | nz]).
        assert (HS4s2 : S4 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S4 upd_ne; [exact HS3s2 | nz]).
        assert (HS4s3 : S4 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s3 | nz]).
        assert (HS4s4 : S4 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s4 | nz]).
        assert (HS4s5 : S4 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s5 | nz]).
        assert (HS4s6 : S4 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s6 | nz]).
        assert (HS4s7 : S4 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s7 | nz]).
        assert (HS4s8 : S4 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S4 upd_ne; [exact HS3s8 | nz]).
        assert (HS4sp : ba_sp m S4)
          by (rewrite /ba_sp /S4 upd_ne; [exact HS3sp | nz]).
        assert (HS4thr : ba_thr9 m S4).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S4 upd_ne; [| regne].
          exact (HS3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppcc : add_vec_int (mword_of_int (KernelSyms.balloc + 0xca) : mword 64) 2
                        = mword_of_int (KernelSyms.balloc + 0xcc)) by pcw.
        iEval (rewrite Hppcc) in "Hpc".
        (* ===== +0xcc sraiw a5,a5,0x3 : a5 := bi / 8 ===== *)
        iApply (wp_sraiw_s_sconf (mword_of_int (KernelSyms.balloc + 0xcc)) Ra5 Ra5
                  (mword_of_int 3 : mword 5) (mword_of_int q : mword 64)
                  S4 (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rewrite HS4a5 Hbisext;
                        rewrite (bal_sraiw3_div8 (mword_of_int bi : mword 32)
                                   ltac:(rewrite Hbiu32; lia)) Hbiu32 -Hqeq;
                        reflexivity)
                  with "Hcg Hpc Hicc").
        iIntros (CID7 Hq7) "Hcg Hpc".
        set (S5 := <[Regidx Ra5 := regval_into_reg (mword_of_int q : mword 64)]> S4).
        assert (HS5a5 : S5 !!! Regidx Ra5 = (mword_of_int q : mword 64))
          by (rewrite /S5; apply upd_eq).
        assert (HS5a4 : S5 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4a4 | nz]).
        assert (HS5a3 : S5 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4a3 | nz]).
        assert (HS5a0 : S5 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4a0 | nz]).
        assert (HS5s1 : S5 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s1 | nz]).
        assert (HS5s2 : S5 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S5 upd_ne; [exact HS4s2 | nz]).
        assert (HS5s3 : S5 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s3 | nz]).
        assert (HS5s4 : S5 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s4 | nz]).
        assert (HS5s5 : S5 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s5 | nz]).
        assert (HS5s6 : S5 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s6 | nz]).
        assert (HS5s7 : S5 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s7 | nz]).
        assert (HS5s8 : S5 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S5 upd_ne; [exact HS4s8 | nz]).
        assert (HS5sp : ba_sp m S5)
          by (rewrite /ba_sp /S5 upd_ne; [exact HS4sp | nz]).
        assert (HS5thr : ba_thr9 m S5).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S5 upd_ne; [| regne].
          exact (HS4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppd0 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xcc) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xd0)) by pcw.
        iEval (rewrite Hppd0) in "Hpc".
        (* ===== +0xd0 add a2,s2,a5 : &bp->data[bi/8] - 88 ===== *)
        iApply (wp_add_s_sconf (mword_of_int (KernelSyms.balloc + 0xd0)) Ra2 Rs2 Ra5
                  (add_vec (bnode kk) (mword_of_int (Z.of_nat d)))
                  S5 (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite HS5s2 HS5a5 Hdz; reflexivity)
                  with "Hcg Hpc Hid0").
        iIntros (CID8 Hq8) "Hcg Hpc".
        set (S6 := <[Regidx Ra2 := regval_into_reg
                      (add_vec (bnode kk) (mword_of_int (Z.of_nat d)))]> S5).
        assert (HS6a2 : S6 !!! Regidx Ra2
                        = add_vec (bnode kk) (mword_of_int (Z.of_nat d)))
          by (rewrite /S6; apply upd_eq).
        assert (HS6a5 : S6 !!! Regidx Ra5 = (mword_of_int q : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5a5 | nz]).
        assert (HS6a4 : S6 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5a4 | nz]).
        assert (HS6a3 : S6 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5a3 | nz]).
        assert (HS6a0 : S6 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5a0 | nz]).
        assert (HS6s1 : S6 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s1 | nz]).
        assert (HS6s2 : S6 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S6 upd_ne; [exact HS5s2 | nz]).
        assert (HS6s3 : S6 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s3 | nz]).
        assert (HS6s4 : S6 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s4 | nz]).
        assert (HS6s5 : S6 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s5 | nz]).
        assert (HS6s6 : S6 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s6 | nz]).
        assert (HS6s7 : S6 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s7 | nz]).
        assert (HS6s8 : S6 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S6 upd_ne; [exact HS5s8 | nz]).
        assert (HS6sp : ba_sp m S6)
          by (rewrite /ba_sp /S6 upd_ne; [exact HS5sp | nz]).
        assert (HS6thr : ba_thr9 m S6).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S6 upd_ne; [| regne].
          exact (HS5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppd4 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xd0) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xd4)) by pcw.
        iEval (rewrite Hppd4) in "Hpc".
        (* ---- borrow the byte the [lbu] reads ---- *)
        assert (Hbmlen : length (bitmap_bytes used) = 1024%nat)
          by (rewrite bitmap_bytes_length; reflexivity).
        assert (Hlkused : bitmap_bytes used !!! d = bm_byte used q).
        { rewrite (list_lookup_total_correct (bitmap_bytes used) d
                     (bm_byte used (Z.of_nat d))
                     (bitmap_bytes_lookup used d Hdlt)).
          rewrite Hdz. reflexivity. }
        iEval (rewrite /bio_locked) in "Hlk".
        iDestruct (iu_held_swap with "Hlk") as "[Hbuf Hlkback]".
        iDestruct (ba_buf_byte (bpa kk) bnoB (mword_of_int 0 : mword 32)
                     (bitmap_bytes used) d Hbmlen Hdlt with "Hbuf")
          as "[Hbyte Hbyteback]".
        iEval (rewrite Hlkused) in "Hbyte".
        (* ===== +0xd4 lbu a2,88(a2) : a2 := bp->data[bi/8] ===== *)
        assert (Hbyadr : add_vec (rget S6 Ra2)
                           (sign_extend' 64 (mword_of_int 88 : mword 12))
                         = pa_add (b_data (bpa kk)) d).
        { rgne. rewrite HS6a2. apply ba_data_off. }
        iEval (rewrite -Hbyadr) in "Hbyte".
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.balloc + 0xd4)) Ra2 Ra2
                  (mword_of_int 88 : mword 12) S6 (K - 10)%nat
                  (bm_byte used q) b ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hid4 Hbyte").
        iIntros (CID9 Hq9) "Hcg Hpc Hbyte".
        iEval (rewrite Hbyadr) in "Hbyte".
        (* the buffer goes straight back: this iteration only READ it *)
        iDestruct ("Hbyteback" $! (bitmap_bytes used)
                     with "[%] [%] [Hbyte]") as "Hbuf".
        { exact Hbmlen. }
        { intros k Hk Hne. reflexivity. }
        { iEval (rewrite Hlkused). iExact "Hbyte". }
        iDestruct ("Hlkback" with "Hbuf") as "Hlk".
        set (S7 := <[Regidx Ra2 := regval_into_reg
                      (zero_extend' 64 (bm_byte used q : mword 8))]> S6).
        assert (HS7a2 : S7 !!! Regidx Ra2
                        = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
          by (rewrite /S7; apply upd_eq).
        assert (HS7a5 : S7 !!! Regidx Ra5 = (mword_of_int q : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6a5 | nz]).
        assert (HS7a4 : S7 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6a4 | nz]).
        assert (HS7a3 : S7 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6a3 | nz]).
        assert (HS7a0 : S7 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6a0 | nz]).
        assert (HS7s1 : S7 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s1 | nz]).
        assert (HS7s2 : S7 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S7 upd_ne; [exact HS6s2 | nz]).
        assert (HS7s3 : S7 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s3 | nz]).
        assert (HS7s4 : S7 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s4 | nz]).
        assert (HS7s5 : S7 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s5 | nz]).
        assert (HS7s6 : S7 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s6 | nz]).
        assert (HS7s7 : S7 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s7 | nz]).
        assert (HS7s8 : S7 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S7 upd_ne; [exact HS6s8 | nz]).
        assert (HS7sp : ba_sp m S7)
          by (rewrite /ba_sp /S7 upd_ne; [exact HS6sp | nz]).
        assert (HS7thr : ba_thr9 m S7).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S7 upd_ne; [| regne].
          exact (HS6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppd8 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xd4) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xd8)) by pcw.
        iEval (rewrite Hppd8) in "Hpc".
        (* ===== +0xd8 and a1,a3,a2 : THE BIT TEST ===== *)
        iApply (wp_and_s_sconf (mword_of_int (KernelSyms.balloc + 0xd8)) Ra1 Ra3 Ra2
                  (and_vec (mword_of_int (2 ^ r) : mword 64)
                           (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
                  S7 (K - 10)%nat b ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite HS7a3 HS7a2; reflexivity)
                  with "Hcg Hpc Hid8").
        iIntros (CID10 Hq10) "Hcg Hpc".
        set (S8 := <[Regidx Ra1 := regval_into_reg
                      (and_vec (mword_of_int (2 ^ r) : mword 64)
                         (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))]> S7).
        assert (HS8a1 : S8 !!! Regidx Ra1
                        = and_vec (mword_of_int (2 ^ r) : mword 64)
                            (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
          by (rewrite /S8; apply upd_eq).
        assert (HS8a2 : S8 !!! Regidx Ra2
                        = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7a2 | nz]).
        assert (HS8a5 : S8 !!! Regidx Ra5 = (mword_of_int q : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7a5 | nz]).
        assert (HS8a4 : S8 !!! Regidx Ra4 = (mword_of_int bi : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7a4 | nz]).
        assert (HS8a3 : S8 !!! Regidx Ra3 = (mword_of_int (2 ^ r) : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7a3 | nz]).
        assert (HS8a0 : S8 !!! Regidx Ra0
                        = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7a0 | nz]).
        assert (HS8s1 : S8 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s1 | nz]).
        assert (HS8s2 : S8 !!! Regidx Rs2 = bnode kk)
          by (rewrite /S8 upd_ne; [exact HS7s2 | nz]).
        assert (HS8s3 : S8 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s3 | nz]).
        assert (HS8s4 : S8 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s4 | nz]).
        assert (HS8s5 : S8 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s5 | nz]).
        assert (HS8s6 : S8 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s6 | nz]).
        assert (HS8s7 : S8 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s7 | nz]).
        assert (HS8s8 : S8 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
          by (rewrite /S8 upd_ne; [exact HS7s8 | nz]).
        assert (HS8sp : ba_sp m S8)
          by (rewrite /ba_sp /S8 upd_ne; [exact HS7sp | nz]).
        assert (HS8thr : ba_thr9 m S8).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
          rewrite /S8 upd_ne; [| regne].
          exact (HS7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
        assert (Hppdc : add_vec_int (mword_of_int (KernelSyms.balloc + 0xd8) : mword 64) 4
                        = mword_of_int (KernelSyms.balloc + 0xdc)) by pcw.
        iEval (rewrite Hppdc) in "Hpc".
        (* ===== +0xdc c.beqz a1 : a CLEAR bit means allocate ===== *)
        assert (Hbitval : and_vec (mword_of_int (2 ^ r) : mword 64)
                            (zero_extend' 64 (bm_byte used q : mword 8) : mword 64)
                          = (if bool_decide (bi ∈ used)
                             then (mword_of_int (2 ^ r) : mword 64)
                             else (mword_of_int 0 : mword 64))).
        { rewrite Hreq Hqeq. exact (bal_and_mask_byte used bi Hbi0). }
        destruct (decide (bi ∈ used)) as [Hin|Hnu].
        * (* the bit is SET: fall through and keep scanning *)
          assert (Hnz1 : eq_vec (rget S8 Ra1) zero_reg = false).
          { destruct (bal_pow_mod8_small bi Hbi0) as [Hp0 Hp1].
            rgne. rewrite HS8a1 Hbitval (bool_decide_eq_true_2 _ Hin).
            apply eq_vec_false_iff. intro Heq.
            assert (Hval : bv_unsigned (mword_of_int (2 ^ r) : mword 64) = 2 ^ r)
              by (rewrite Hreq; apply bal_mask_unsigned; exact Hbi0).
            rewrite Heq in Hval.
            assert (Hz0 : bv_unsigned (zero_reg : mword 64) = 0)
              by (vm_compute; reflexivity).
            rewrite Hz0 in Hval. rewrite -Hreq in Hp0. lia. }
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.balloc + 0xdc))
                    (mword_of_int 174 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                    S8 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz) Hnz1
                    with "Hcg Hpc Hidc").
          iIntros (CID11 Hq11) "Hcg Hpc".
          assert (Hppde : add_vec_int (mword_of_int (KernelSyms.balloc + 0xdc) : mword 64) 2
                          = mword_of_int (KernelSyms.balloc + 0xde)) by pcw.
          iEval (rewrite Hppde) in "Hpc".
          (* ===== +0xde c.addiw a4,a4,1 ===== *)
          iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.balloc + 0xde)) Ra4
                    (mword_of_int 1 : mword 6) S8 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hide").
          iIntros (CID12 Hq12) "Hcg Hpc".
          set (S9 := <[Regidx Ra4 := regval_into_reg
                        (sign_extend' 64
                           (subrange_vec_dec
                              (add_vec (rget S8 Ra4)
                                 (sign_extend' 64
                                    (sign_extend' 12 (mword_of_int 1 : mword 6))))
                              31 0))]> S8).
          assert (HS9a4 : S9 !!! Regidx Ra4 = (mword_of_int (bi + 1) : mword 64)).
          { rewrite /S9 upd_eq. rgne. rewrite HS8a4.
            apply ba_addiw1. lia. }
          assert (HS9s1 : S9 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s1 | nz]).
          assert (HS9a0 : S9 !!! Regidx Ra0
                          = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8a0 | nz]).
          assert (HS9s2 : S9 !!! Regidx Rs2 = bnode kk)
            by (rewrite /S9 upd_ne; [exact HS8s2 | nz]).
          assert (HS9s3 : S9 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s3 | nz]).
          assert (HS9s4 : S9 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s4 | nz]).
          assert (HS9s5 : S9 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s5 | nz]).
          assert (HS9s6 : S9 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s6 | nz]).
          assert (HS9s7 : S9 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s7 | nz]).
          assert (HS9s8 : S9 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
            by (rewrite /S9 upd_ne; [exact HS8s8 | nz]).
          assert (HS9sp : ba_sp m S9)
            by (rewrite /ba_sp /S9 upd_ne; [exact HS8sp | nz]).
          assert (HS9thr : ba_thr9 m S9).
          { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
            rewrite /S9 upd_ne; [| regne].
            exact (HS8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
          assert (Hppe0 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xde) : mword 64) 2
                          = mword_of_int (KernelSyms.balloc + 0xe0)) by pcw.
          iEval (rewrite Hppe0) in "Hpc".
          (* ===== +0xe0 c.addiw s1,s1,1 ===== *)
          iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.balloc + 0xe0)) Rs1
                    (mword_of_int 1 : mword 6) S9 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hie0").
          iIntros (CID13 Hq13) "Hcg Hpc".
          set (SA := <[Regidx Rs1 := regval_into_reg
                        (sign_extend' 64
                           (subrange_vec_dec
                              (add_vec (rget S9 Rs1)
                                 (sign_extend' 64
                                    (sign_extend' 12 (mword_of_int 1 : mword 6))))
                              31 0))]> S9).
          assert (HSAs1 : SA !!! Regidx Rs1 = (mword_of_int (bi + 1) : mword 64)).
          { rewrite /SA upd_eq. rgne. rewrite HS9s1. apply ba_addiw1. lia. }
          assert (HSAa4 : SA !!! Regidx Ra4 = (mword_of_int (bi + 1) : mword 64))
            by (rewrite /SA upd_ne; [exact HS9a4 | nz]).
          assert (HSAa0 : SA !!! Regidx Ra0
                          = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
            by (rewrite /SA upd_ne; [exact HS9a0 | nz]).
          assert (HSAs2 : SA !!! Regidx Rs2 = bnode kk)
            by (rewrite /SA upd_ne; [exact HS9s2 | nz]).
          assert (HSAs3 : SA !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s3 | nz]).
          assert (HSAs4 : SA !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s4 | nz]).
          assert (HSAs5 : SA !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s5 | nz]).
          assert (HSAs6 : SA !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s6 | nz]).
          assert (HSAs7 : SA !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s7 | nz]).
          assert (HSAs8 : SA !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
            by (rewrite /SA upd_ne; [exact HS9s8 | nz]).
          assert (HSAsp : ba_sp m SA)
            by (rewrite /ba_sp /SA upd_ne; [exact HS9sp | nz]).
          assert (HSAthr : ba_thr9 m SA).
          { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
            rewrite /SA upd_ne; [| regne].
            exact (HS9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
          assert (Hppe2 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xe0) : mword 64) 2
                          = mword_of_int (KernelSyms.balloc + 0xe2)) by pcw.
          iEval (rewrite Hppe2) in "Hpc".
          (* ===== +0xe2 bne a4,s4 : keep scanning unless bi reached BPB ===== *)
          destruct (Z.eqb (bi + 1) 8192) eqn:Heqb.
          -- (* bi + 1 = BPB: fall through to the +0xe6 jump *)
             apply Z.eqb_eq in Heqb.
             assert (Hne : neq_vec (rget SA Ra4) (rget SA Rs4) = false).
             { rgne. rgne. rewrite HSAa4 HSAs4.
               rewrite (ba_neq_moi (bi + 1) 8192 ltac:(lia) ltac:(lia)).
               rewrite Heqb. reflexivity. }
             iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.balloc + 0xe2))
                       (mword_of_int 8148 : mword 13) Rs4 Ra4 SA (K - 10)%nat b
                       ltac:(nz) ltac:(nz) Hne with "Hcg Hpc Hie2").
             iIntros (CID14 Hq14) "Hcg Hpc".
             assert (Hppe6 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xe2) : mword 64) 4
                             = mword_of_int (KernelSyms.balloc + 0xe6)) by pcw.
             iEval (rewrite Hppe6) in "Hpc".
             iPoseProof (bai_0e6 with "Htext") as "Hie6'".
             iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.balloc + 0xe6))
                       (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")))
                       SA (K - 10)%nat b ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc Hie6'").
             iIntros (CID15 Hq15). iApply bi.later_intro. iIntros "Hcg Hpc".
             assert (Hjt2 : add_vec (mword_of_int (KernelSyms.balloc + 0xe6) : mword 64)
                              (sign_extend' 64 (sign_extend' 21
                                 (concat_vec (mword_of_int 2002 : mword 11) ('b"0"))))
                            = mword_of_int (KernelSyms.balloc + 0x8a)) by pcw.
             iEval (rewrite Hjt2) in "Hpc".
             iDestruct (bitmap_res_close γfs bmapstart cov logstart size used Hok
                          with "Hfsbm Hpool") as "Hbmr".
             iDestruct (cpu_own_transport CIDx CID15 0 eb (proc_addr j) b
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (IntrDefs.trap_csrs_ext_transport CIDx CID15 eb (proc_addr j)
                          ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
             iDestruct (IntrDefs.cpu_claim_ext_transport CIDx CID15 eb (proc_addr j)
                          ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
             iApply (ba_exhaust (CID0 := CID15)  γs j γfs γd bn γ γpr γu cov logstart
                       bmapstart size dev used u cr Sb kk bnoB (bitmap_bytes used) bsdX dX
                       pidv dq dqb dqs m SA K eb b lks Vpr HK Hpk Hsize HSAsp HSAthr HSAs2
                       HSAs5 HSAs6 HSAs8 Hkk Hbelow
                       with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hbio Hprocs Hframe Hppid Hsbsz Hsbbm Hsl Hbmr Hop Hlk [Hcont]").
             { iApply (wp_next_shift (b := true) (CIDa := CIDx) (CIDb := CID15)
                         ltac:(wp_next_chain) with "Hcont"). }
          -- (* bi + 1 < BPB: branch back to +0xb6, one fuel unit down *)
             apply Z.eqb_neq in Heqb.
             assert (Hne : neq_vec (rget SA Ra4) (rget SA Rs4) = true).
             { rgne. rgne. rewrite HSAa4 HSAs4.
               rewrite (ba_neq_moi (bi + 1) 8192 ltac:(lia) ltac:(lia)).
               destruct (Z.eqb (bi + 1) 8192) eqn:Ex;
                 [apply Z.eqb_eq in Ex; exfalso; exact (Heqb Ex) | reflexivity]. }
             iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.balloc + 0xe2))
                       (mword_of_int 8148 : mword 13) Rs4 Ra4 SA (K - 10)%nat b
                       ltac:(nz) ltac:(nz) Hne ltac:(vm_compute; reflexivity)
                       with "Hcg Hpc Hie2").
             iApply bi.later_intro. iIntros (CID14 Hq14) "Hcg Hpc".
             assert (Hjt3 : add_vec (mword_of_int (KernelSyms.balloc + 0xe2) : mword 64)
                              (sign_extend' 64 (mword_of_int 8148 : mword 13))
                            = mword_of_int (KernelSyms.balloc + 0xb6)) by pcw.
             iEval (rewrite Hjt3) in "Hpc".
             iDestruct (cpu_own_transport CIDx CID14 0 eb (proc_addr j) b
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             iDestruct (IntrDefs.trap_csrs_ext_transport CIDx CID14 eb (proc_addr j)
                          ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
             iDestruct (IntrDefs.cpu_claim_ext_transport CIDx CID14 eb (proc_addr j)
                          ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
             iApply (IH CID14 (bi + 1) SA
                       ltac:(exact (proj1 (ba_scan_step bi size fuel
                                             Hfuel Hbi Hbilt Hsize)))
                       ltac:(exact (proj2 (ba_scan_step bi size fuel
                                             Hfuel Hbi Hbilt Hsize)))
                       HSAsp HSAthr HSAa0 HSAa4 HSAs1
                       HSAs2 HSAs3 HSAs4 HSAs5 HSAs6 HSAs7 HSAs8 Hbelow
                       with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hbio Hlctx Hprocs Hframe Hppid Hsbsz Hsbbm Hdevi Hdgeom
                             Hdlock Hsl Hop Hfsbm Hpool Hlk [Hcont]").
             { iApply (wp_next_shift (b := true) (CIDa := CIDx) (CIDb := CID14)
                         ltac:(wp_next_chain) with "Hcont"). }
        * (* the bit is CLEAR: take the branch to +0x38 and allocate *)
          assert (Hz1 : eq_vec (rget S8 Ra1) zero_reg = true).
          { rgne. rewrite HS8a1 Hbitval (bool_decide_eq_false_2 _ Hnu).
            apply eq_vec_true_iff. pcw. }
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.balloc + 0xdc))
                    (mword_of_int 174 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                    S8 (K - 10)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz) Hz1
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hidc").
          iApply bi.later_intro. iIntros (CID11 Hq11) "Hcg Hpc".
          assert (Hjt4 : add_vec (mword_of_int (KernelSyms.balloc + 0xdc) : mword 64)
                           (sign_extend' 64 (sign_extend' 13
                              (concat_vec (mword_of_int 174 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.balloc + 0x38)) by pcw.
          iEval (rewrite Hjt4) in "Hpc".
          iDestruct (cpu_own_transport CIDx CID11 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (IntrDefs.trap_csrs_ext_transport CIDx CID11 eb (proc_addr j)
                       ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (IntrDefs.cpu_claim_ext_transport CIDx CID11 eb (proc_addr j)
                       ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
          iApply (ba_alloc (CID0 := CID11)  γs j γl γu γd γk pd pav pu γfs bn γ
                    cov logstart bmapstart size dev used bi u cr Sb kk bnoB bsdX dX
                    pidv dq dqb dqs m S8 K eb b lks
                    Vpr HK Hgeom Hsize Hbirange Hnu Hok HbnoB Hbmcov Hbmlog Hkk Hj Hgl
                    HS8sp HS8thr ltac:(rewrite HS8a5 Hqeq; reflexivity)
                    ltac:(rewrite HS8a2 Hqeq; reflexivity)
                    ltac:(rewrite HS8a3 Hreq; reflexivity)
                    HS8s1 HS8s2 HS8s7 Hcred Hbelow
                    with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hlctx Hprocs Hframe Hppid Hsbsz Hsbbm Hdevi Hdgeom Hdlock Hsl Hop
                          Hfsbm Hpool Hlk [Hcont]").
          { iApply (wp_next_shift (b := true) (CIDa := CIDx) (CIDb := CID11)
                      ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End BallocScan.


(* ===================================================================== *)
(*  +0x00 .. +0xb4 : THE PROLOGUE and the outer loop's ONLY head.         *)
(*                                                                        *)
(*  The 80-byte frame goes down in two batches -- ra/s0/s1 first, then     *)
(*  s2..s8 -- because the [beqz a5,+0xf6] at +0x12 sits between them.      *)
(*  That arm is DEAD ([0 < size]) and is REFUTED at the fall-through, not  *)
(*  proved; it matters because it would reach the printk WITHOUT the       *)
(*  s2..s8 restore, i.e. with a different frame story altogether.          *)
(*                                                                        *)
(*  [size <= BPB] then makes the outer loop straight-line: b = 0, so the   *)
(*  [sraiw a1,s5,0xd] at +0x9c is 0, BBLOCK collapses to [bmapstart], and  *)
(*  the bread at +0xa8 fetches the ONE bitmap block.  The scan is entered  *)
(*  once, at [bi = 0], with the full [Z.to_nat BPB] of fuel.               *)
(* ===================================================================== *)
Section BallocMain.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [ba_main] IS THE ONE CORE both top-level lemmas below build on: the
     credited/[cr]/[Sb] shape, eb-generic.  Its statement now coincides
     with [wp_balloc_gen_body] (that body was generalized along with this
     proof -- see the banner there), so [wp_balloc_gen] is a bare [exact]
     and [wp_balloc_sconf] is the set-forgetting instance at [cr := false] lks Vpr.
     Keeping the CREDITED form eb-generic is not a luxury: bmap's credited
     path routes through it, and pinning it at [eb = true] would have
     forced a second, independent proof of bmap's 70 instructions.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  Lemma ba_main
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (γpr : gname)
      (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : let pcE : mword 64 := mword_of_int KernelSyms.balloc in
      let pj := proc_addr j in
      let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
      (K_balloc <= K)%nat ->
      log_geom_ok cov logstart ->
      printk_gen_contract (kt := KT1) γpr γu γd ->
      0 < size <= BPB ->
      0 <= bmapstart ->
      bmapstart ∈ cov ->
      ~ (bmapstart ∈ log_region_set logstart) ->
      (cr = true -> bmapstart ∈ Sb) ->
      (j < NPROC)%nat ->
      γs !! j = Some γl ->
      m !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 dev ->
      (* ba_main's own cone touches "log" (log_write, via ba_scan's
         ba_alloc) and "bcache" (bread, directly and via ba_scan) -- "log"
         is the floor *)
      locks_below lks "log" ->
      sie_cap_gpr KT1 m K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      kernel_text -∗ pc_is pcE -∗
      kernel_data -∗
      printk_env γpr γu γd -∗
      bio_ctx bn (fs_view γfs γd dev cov) -∗
      log_ctx γ bn γfs cov logstart dev -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      bitmap_res γfs bmapstart cov logstart size used -∗
      procs_inv γs -∗
      dev_inv γu γd -∗
      disk_geom γd pd pav pu -∗
      is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
      bslots bn 2 -∗
      log_opS γ (2 + u) Sb -∗
      wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
          ⌜callee_saved m mf⌝ -∗
          sie_cap_gpr KT1 mf K b pj -∗
          cpu_own 0 eb pj b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb pj -∗
          pc_is ret_tgt -∗
          proc_priv_bare pj pidv Vpr -∗
          sb_size ↦₄{dqs} (mword_of_int size : mword 32) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          bslots bn 2 -∗
          ((⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ ∗
            bitmap_res γfs bmapstart cov logstart size used ∗
            log_opS γ (2 + u) Sb)
           ∨
           (∃ blk : mword 32,
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 blk⌝ ∗
              ⌜bv_unsigned blk <> 0⌝ ∗
              ⌜bv_unsigned blk ∈ cov⌝ ∗
              ⌜~ (bv_unsigned blk ∈ log_region_set logstart)⌝ ∗
              fsblock γfs (bv_unsigned blk) (replicate BSIZE (bv_0 8)) ∗
              blk_own γfs (bv_unsigned blk) ∗
              bitmap_res γfs bmapstart cov logstart size
                         (used ∪ {[ bv_unsigned blk ]}) ∗
              log_opS γ (if cr then S u else u)
                        (Sb ∪ {[bmapstart]} ∪ {[bv_unsigned blk]}))) -∗
          WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros pcE pj ret_tgt HK Hgeom Hpk Hsize Hbm0 Hbmcov Hbmlog Hcred Hj Hgl Ha0 Hbelow.
    pose proof HK as HK'. 
    pose proof Hsize as Hsz'. rewrite BPB_value in Hsz'.
    pose proof Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hbmcov) as [Hbmpos Hbmlt].
    destruct (ba_bm_range bmapstart Hbmpos Hbmlt) as (Hbm31 & Hbm32 & Hbm64).
    (* the bitmap block number, as the 32-bit word the ABI passes *)
    set (bnoB := (mword_of_int bmapstart : mword 32)).
    assert (HbnoB : uint bnoB = bmapstart).
    { rewrite /bnoB bb_uint32 moi32_unsigned. apply bvw32_small. exact Hbm32. }
    assert (HbnoBlt : (uint bnoB < 2147483648)%Z) by (rewrite HbnoB; lia).
    assert (HbnoBcov : uint bnoB ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite HbnoB; exact Hbmcov).
    assert (Hszsext : (sign_extend' 64 (mword_of_int size : mword 32) : mword 64)
                      = mword_of_int size)
      by (apply sext32_64_small; change (2^31)%Z with 2147483648%Z; lia).
    (* THE +0x12 REFUTATION, as a pure fact, before a single instruction *)
    assert (Hszne0 : eq_vec (mword_of_int size : mword 64) (zero_reg : mword 64)
                     = false)
      by (apply ba_moi64_nonzero; lia).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hkdata #Hpenv #Hbio #Hlctx Hppid
              Hsbsz Hsbbm Hbmr #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm.
    iAssert (ba_cont (CID0 := CID) γfs bn γ cov logstart bmapstart size used u cr Sb
               pidv dq dqb dqs j m K eb b lks Vpr)%I with "[Hcont]" as "Hcont";
      [rewrite /ba_cont; iExact "Hcont" |].
    iDestruct (bitmap_res_open with "Hbmr") as "(%Hok & Hfsbm & Hpool)".
    iPoseProof (bai_000 with "Htext") as "Hi000".
    iPoseProof (bai_002 with "Htext") as "Hi002".
    iPoseProof (bai_004 with "Htext") as "Hi004".
    iPoseProof (bai_006 with "Htext") as "Hi006".
    iPoseProof (bai_008 with "Htext") as "Hi008".
    iPoseProof (bai_00a with "Htext") as "Hi00a".
    iPoseProof (bai_00e with "Htext") as "Hi00e".
    iPoseProof (bai_012 with "Htext") as "Hi012".
    iPoseProof (bai_016 with "Htext") as "Hi016".
    iPoseProof (bai_018 with "Htext") as "Hi018".
    iPoseProof (bai_01a with "Htext") as "Hi01a".
    iPoseProof (bai_01c with "Htext") as "Hi01c".
    iPoseProof (bai_01e with "Htext") as "Hi01e".
    iPoseProof (bai_020 with "Htext") as "Hi020".
    iPoseProof (bai_022 with "Htext") as "Hi022".
    iPoseProof (bai_024 with "Htext") as "Hi024".
    iPoseProof (bai_026 with "Htext") as "Hi026".
    iPoseProof (bai_028 with "Htext") as "Hi028".
    iPoseProof (bai_02c with "Htext") as "Hi02c".
    iPoseProof (bai_030 with "Htext") as "Hi030".
    iPoseProof (bai_032 with "Htext") as "Hi032".
    iPoseProof (bai_034 with "Htext") as "Hi034".
    iPoseProof (bai_036 with "Htext") as "Hi036".
    (* ===== +0x00 c.addi16sp sp,-80 : the 10-slot frame ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 59 : mword 6) m K 10 b
              ltac:(lia) Hpush with "Hcg Hpc Hi000").
    iIntros (CIDb01 Hq01) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    assert (HR1sp : ba_sp m R1) by (rewrite /ba_sp /R1 upd_eq; reflexivity).
    assert (HR1thr : ba_thr9 m R1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe"
      as "(T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & _)".
    iDestruct "T1" as (v1) "Hf1".   iDestruct "T2" as (v2) "Hf2".
    iDestruct "T3" as (v3) "Hf3".   iDestruct "T4" as (v4) "Hf4".
    iDestruct "T5" as (v5) "Hf5".   iDestruct "T6" as (v6) "Hf6".
    iDestruct "T7" as (v7) "Hf7".   iDestruct "T8" as (v8) "Hf8".
    iDestruct "T9" as (v9) "Hf9".   iDestruct "T10" as (v10) "Hf10".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".
    assert (Hpp002 : add_vec_int (pcE : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x2)) by pcw.
    iEval (rewrite Hpp002) in "Hpc".
    (* ===== +0x02 .. +0x06 : ra, s0, s1 ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x2))
              (mword_of_int 9 : mword 6) Rra
              R1 (K - 10)%nat v1 b with "Hcg Hpc Hi002 Hf1").
    iIntros (CIDb02 Hq02) "Hcg Hpc Hf1".
    assert (Hpp004 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x2) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x4)) by pcw.
    iEval (rewrite Hpp004) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x4))
              (mword_of_int 8 : mword 6) Rs0
              R1 (K - 10)%nat v2 b with "Hcg Hpc Hi004 Hf2").
    iIntros (CIDb03 Hq03) "Hcg Hpc Hf2".
    assert (Hpp006 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x4) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x6)) by pcw.
    iEval (rewrite Hpp006) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x6))
              (mword_of_int 7 : mword 6) Rs1
              R1 (K - 10)%nat v3 b with "Hcg Hpc Hi006 Hf3").
    iIntros (CIDb04 Hq04) "Hcg Hpc Hf3".
    assert (Hpp008 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x6) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x8)) by pcw.
    iEval (rewrite Hpp008) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    (* ===== +0x08 c.addi4spn s0,sp,80 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.balloc + 0x8))
              (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi008").
    iIntros (CIDb05 Hq05) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    assert (HR2sp : ba_sp m R2)
      by (rewrite /ba_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2thr : ba_thr9 m R2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R2 upd_ne; [| regne].
      exact (HR1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp00a : add_vec_int (mword_of_int (KernelSyms.balloc + 0x8) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xa)) by pcw.
    iEval (rewrite Hpp00a) in "Hpc".
    (* ===== +0x0a auipc a5,0x1e ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.balloc + 0xa)) Ra5
              (mword_of_int 30 : mword 20) R2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi00a").
    iIntros (CIDb06 Hq06) "Hcg Hpc".
    set (R3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.balloc + 0xa) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    assert (HR3a5 : R3 !!! Regidx Ra5
                    = add_vec (mword_of_int (KernelSyms.balloc + 0xa) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : ba_sp m R3)
      by (rewrite /ba_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : ba_thr9 m R3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp00e : add_vec_int (mword_of_int (KernelSyms.balloc + 0xa) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0xe)) by pcw.
    iEval (rewrite Hpp00e) in "Hpc".
    (* ===== +0x0e lw a5,-1370(a5) : a5 := sb.size ===== *)
    assert (Hszadr1 : add_vec (rget R3 Ra5)
                        (sign_extend' 64 (mword_of_int 2920 : mword 12))
                      = sb_size).
    { rgne. rewrite HR3a5. rewrite /sb_size /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hszadr1) in "Hsbsz".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.balloc + 0xe)) Ra5 Ra5
              (mword_of_int 2920 : mword 12) R3 (K - 10)%nat
              (mword_of_int size : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi00e Hsbsz").
    iIntros (CIDb07 Hq07) "Hcg Hpc Hsbsz".
    iEval (rewrite Hszadr1) in "Hsbsz".
    set (R4 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int size : mword 32))]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : R4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [exact Ha0 | nz]. }
    assert (HR4sp : ba_sp m R4)
      by (rewrite /ba_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : ba_thr9 m R4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R4 upd_ne; [| regne].
      exact (HR3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp012 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xe) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0x12)) by pcw.
    iEval (rewrite Hpp012) in "Hpc".
    (* ===== +0x12 beqz a5,+0xf6 : THE DEAD ARM.  0 < size, so it falls
       through -- the arm is REFUTED, never proved (it would reach the
       printk without restoring s2..s8). ===== *)
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.balloc + 0x12))
              (mword_of_int 228 : mword 13) Ra5 R4 (K - 10)%nat b ltac:(nz)
              ltac:(rgne; rewrite HR4a5 Hszsext; exact Hszne0)
              with "Hcg Hpc Hi012").
    iIntros (CIDb08 Hq08) "Hcg Hpc".
    assert (Hpp016 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x12) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0x16)) by pcw.
    iEval (rewrite Hpp016) in "Hpc".
    (* ===== +0x16 .. +0x22 : s2 .. s8 ===== *)
    assert (Hb4 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb5 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb6 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb7 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb8 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb9 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb10 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HR4sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb4) in "Hf4".   iEval (rewrite -Hb5) in "Hf5".
    iEval (rewrite -Hb6) in "Hf6".   iEval (rewrite -Hb7) in "Hf7".
    iEval (rewrite -Hb8) in "Hf8".   iEval (rewrite -Hb9) in "Hf9".
    iEval (rewrite -Hb10) in "Hf10".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x16))
              (mword_of_int 6 : mword 6) Rs2
              R4 (K - 10)%nat v4 b with "Hcg Hpc Hi016 Hf4").
    iIntros (CIDb09 Hq09) "Hcg Hpc Hf4".
    assert (Hpp018 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x16) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x18)) by pcw.
    iEval (rewrite Hpp018) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x18))
              (mword_of_int 5 : mword 6) Rs3
              R4 (K - 10)%nat v5 b with "Hcg Hpc Hi018 Hf5").
    iIntros (CIDb10 Hq10) "Hcg Hpc Hf5".
    assert (Hpp01a : add_vec_int (mword_of_int (KernelSyms.balloc + 0x18) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x1a)) by pcw.
    iEval (rewrite Hpp01a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x1a))
              (mword_of_int 4 : mword 6) Rs4
              R4 (K - 10)%nat v6 b with "Hcg Hpc Hi01a Hf6").
    iIntros (CIDb11 Hq11) "Hcg Hpc Hf6".
    assert (Hpp01c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x1a) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x1c)) by pcw.
    iEval (rewrite Hpp01c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x1c))
              (mword_of_int 3 : mword 6) Rs5
              R4 (K - 10)%nat v7 b with "Hcg Hpc Hi01c Hf7").
    iIntros (CIDb12 Hq12) "Hcg Hpc Hf7".
    assert (Hpp01e : add_vec_int (mword_of_int (KernelSyms.balloc + 0x1c) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x1e)) by pcw.
    iEval (rewrite Hpp01e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x1e))
              (mword_of_int 2 : mword 6) Rs6
              R4 (K - 10)%nat v8 b with "Hcg Hpc Hi01e Hf8").
    iIntros (CIDb13 Hq13) "Hcg Hpc Hf8".
    assert (Hpp020 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x1e) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x20)) by pcw.
    iEval (rewrite Hpp020) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x20))
              (mword_of_int 1 : mword 6) Rs7
              R4 (K - 10)%nat v9 b with "Hcg Hpc Hi020 Hf9").
    iIntros (CIDb14 Hq14) "Hcg Hpc Hf9".
    assert (Hpp022 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x20) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x22)) by pcw.
    iEval (rewrite Hpp022) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.balloc + 0x22))
              (mword_of_int 0 : mword 6) Rs8
              R4 (K - 10)%nat v10 b with "Hcg Hpc Hi022 Hf10").
    iIntros (CIDb15 Hq15) "Hcg Hpc Hf10".
    assert (Hpp024 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x22) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x24)) by pcw.
    iEval (rewrite Hpp024) in "Hpc".
    (* the frame, restated at the ENTRY register file *)
    assert (HR4s2 : (R4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s3 : (R4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s4 : (R4 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s5 : (R4 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s6 : (R4 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s7 : (R4 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR4s8 : (R4 !!! Regidx Rs8 : mword 64) = (m !!! Regidx Rs8 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [reflexivity | nz]. }
    iEval (rewrite Hb4; rgne; rewrite HR4s2) in "Hf4".
    iEval (rewrite Hb5; rgne; rewrite HR4s3) in "Hf5".
    iEval (rewrite Hb6; rgne; rewrite HR4s4) in "Hf6".
    iEval (rewrite Hb7; rgne; rewrite HR4s5) in "Hf7".
    iEval (rewrite Hb8; rgne; rewrite HR4s6) in "Hf8".
    iEval (rewrite Hb9; rgne; rewrite HR4s7) in "Hf9".
    iEval (rewrite Hb10; rgne; rewrite HR4s8) in "Hf10".
    iAssert (ba_frame m)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]" as "Hframe".
    { rewrite /ba_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
      iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
      iSplitL "Hf9"; [iExact "Hf9" |]. iExact "Hf10". }
    (* ===== +0x24 c.mv s7,a0 : s7 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0x24)) Rs7 Ra0
              R4 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi024").
    iIntros (CIDb16 Hq16) "Hcg Hpc".
    set (R5 := <[Regidx Rs7 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R4 Ra0))]> R4).
    assert (HR5s7 : R5 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R5 upd_eq. rgne. rewrite HR4a0. apply add_vec_zero_l. }
    assert (HR5sp : ba_sp m R5)
      by (rewrite /ba_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : ba_thr9 m R5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R5 upd_ne; [| regne].
      exact (HR4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp026 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x24) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x26)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ===== +0x26 c.li s5,0 : b := 0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.balloc + 0x26)) Rs5
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              R5 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi026").
    iIntros (CIDb17 Hq17) "Hcg Hpc".
    set (R6 := <[Regidx Rs5 := regval_into_reg (mword_of_int 0 : mword 64)]> R5).
    assert (HR6s5 : R6 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R6; apply upd_eq).
    assert (HR6s7 : R6 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5s7 | nz]).
    assert (HR6sp : ba_sp m R6)
      by (rewrite /ba_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : ba_thr9 m R6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R6 upd_ne; [| regne].
      exact (HR5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp028 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x26) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x28)) by pcw.
    iEval (rewrite Hpp028) in "Hpc".
    (* ===== +0x28 auipc s6,0x1e ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.balloc + 0x28)) Rs6
              (mword_of_int 30 : mword 20) R6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi028").
    iIntros (CIDb18 Hq18) "Hcg Hpc".
    set (R7 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.balloc + 0x28) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R6).
    assert (HR7s6 : R7 !!! Regidx Rs6
                    = add_vec (mword_of_int (KernelSyms.balloc + 0x28) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /R7; apply upd_eq).
    assert (HR7s5 : R7 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s5 | nz]).
    assert (HR7s7 : R7 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s7 | nz]).
    assert (HR7sp : ba_sp m R7)
      by (rewrite /ba_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : ba_thr9 m R7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R7 upd_ne; [| regne].
      exact (HR6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp02c : add_vec_int (mword_of_int (KernelSyms.balloc + 0x28) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0x2c)) by pcw.
    iEval (rewrite Hpp02c) in "Hpc".
    (* ===== +0x2c addi s6,s6,-1322 : s6 := &sb ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.balloc + 0x2c)) Rs6 Rs6
              (mword_of_int 2886 : mword 12) R7 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi02c").
    iIntros (CIDb19 Hq19) "Hcg Hpc".
    set (R8 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (rget R7 Rs6)
                     (sign_extend' 64 (mword_of_int 2886 : mword 12)))]> R7).
    assert (HR8s6 : R8 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64)).
    { rewrite /R8 upd_eq. rgne. rewrite HR7s6. pcw. }
    assert (HR8s5 : R8 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s5 | nz]).
    assert (HR8s7 : R8 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s7 | nz]).
    assert (HR8sp : ba_sp m R8)
      by (rewrite /ba_sp /R8 upd_ne; [exact HR7sp | nz]).
    assert (HR8thr : ba_thr9 m R8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R8 upd_ne; [| regne].
      exact (HR7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp030 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x2c) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0x30)) by pcw.
    iEval (rewrite Hpp030) in "Hpc".
    (* ===== +0x30 c.li s3,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.balloc + 0x30)) Rs3
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              R8 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi030").
    iIntros (CIDb20 Hq20) "Hcg Hpc".
    set (R9 := <[Regidx Rs3 := regval_into_reg (mword_of_int 1 : mword 64)]> R8).
    assert (HR9s3 : R9 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R9; apply upd_eq).
    assert (HR9s5 : R9 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s5 | nz]).
    assert (HR9s6 : R9 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s6 | nz]).
    assert (HR9s7 : R9 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s7 | nz]).
    assert (HR9sp : ba_sp m R9)
      by (rewrite /ba_sp /R9 upd_ne; [exact HR8sp | nz]).
    assert (HR9thr : ba_thr9 m R9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R9 upd_ne; [| regne].
      exact (HR8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp032 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x30) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x32)) by pcw.
    iEval (rewrite Hpp032) in "Hpc".
    (* ===== +0x32 c.lui s4,0x2 : s4 := BPB ===== *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.balloc + 0x32)) Rs4
              (sign_extend' 20 (mword_of_int 2 : mword 6))
              (mword_of_int 8192 : mword 64)
              R9 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi032").
    iIntros (CIDb21 Hq21) "Hcg Hpc".
    set (R10 := <[Regidx Rs4 := regval_into_reg (mword_of_int 8192 : mword 64)]> R9).
    assert (HR10s4 : R10 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R10; apply upd_eq).
    assert (HR10s3 : R10 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R10 upd_ne; [exact HR9s3 | nz]).
    assert (HR10s5 : R10 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R10 upd_ne; [exact HR9s5 | nz]).
    assert (HR10s6 : R10 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R10 upd_ne; [exact HR9s6 | nz]).
    assert (HR10s7 : R10 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R10 upd_ne; [exact HR9s7 | nz]).
    assert (HR10sp : ba_sp m R10)
      by (rewrite /ba_sp /R10 upd_ne; [exact HR9sp | nz]).
    assert (HR10thr : ba_thr9 m R10).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R10 upd_ne; [| regne].
      exact (HR9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp034 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x32) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x34)) by pcw.
    iEval (rewrite Hpp034) in "Hpc".
    (* ===== +0x34 c.lui s8,0x2 ===== *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.balloc + 0x34)) Rs8
              (sign_extend' 20 (mword_of_int 2 : mword 6))
              (mword_of_int 8192 : mword 64)
              R10 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi034").
    iIntros (CIDb22 Hq22) "Hcg Hpc".
    set (R11 := <[Regidx Rs8 := regval_into_reg (mword_of_int 8192 : mword 64)]> R10).
    assert (HR11s8 : R11 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /R11; apply upd_eq).
    assert (HR11s4 : R11 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R11 upd_ne; [exact HR10s4 | nz]).
    assert (HR11s3 : R11 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R11 upd_ne; [exact HR10s3 | nz]).
    assert (HR11s5 : R11 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R11 upd_ne; [exact HR10s5 | nz]).
    assert (HR11s6 : R11 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R11 upd_ne; [exact HR10s6 | nz]).
    assert (HR11s7 : R11 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R11 upd_ne; [exact HR10s7 | nz]).
    assert (HR11sp : ba_sp m R11)
      by (rewrite /ba_sp /R11 upd_ne; [exact HR10sp | nz]).
    assert (HR11thr : ba_thr9 m R11).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R11 upd_ne; [| regne].
      exact (HR10thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp036 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x34) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0x36)) by pcw.
    iEval (rewrite Hpp036) in "Hpc".
    (* ===== +0x36 c.j +0x9c : into the outer loop's head ===== *)
    assert (Htgtj : add_vec (mword_of_int (KernelSyms.balloc + 0x36) : mword 64)
                      (sign_extend' 64
                         (sign_extend' 21
                            (concat_vec (mword_of_int 51 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.balloc + 0x9c)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.balloc + 0x36))
              (sign_extend' 21 (concat_vec (mword_of_int 51 : mword 11) ('b"0")))
              R11 (K - 10)%nat b
              ltac:(rewrite Htgtj; vm_compute; reflexivity)
              with "Hcg Hpc Hi036").
    iIntros (CIDb23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgtj) in "Hpc".
    iPoseProof (bai_09c with "Htext") as "Hi09c".
    iPoseProof (bai_0a0 with "Htext") as "Hi0a0".
    iPoseProof (bai_0a4 with "Htext") as "Hi0a4".
    iPoseProof (bai_0a6 with "Htext") as "Hi0a6".
    iPoseProof (bai_0a8 with "Htext") as "Hi0a8".
    (* ===== +0x9c sraiw a1,s5,0xd : b / BPB, and b IS 0 ===== *)
    iApply (wp_sraiw_s_sconf (mword_of_int (KernelSyms.balloc + 0x9c)) Ra1 Rs5
              (mword_of_int 13 : mword 5) (mword_of_int 0 : mword 64)
              R11 (K - 10)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HR11s5; exact bal_sraiw13_zero)
              with "Hcg Hpc Hi09c").
    iIntros (CIDb24 Hq24) "Hcg Hpc".
    set (R12 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> R11).
    assert (HR12a1 : R12 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /R12; apply upd_eq).
    assert (HR12s3 : R12 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s3 | nz]).
    assert (HR12s4 : R12 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s4 | nz]).
    assert (HR12s5 : R12 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s5 | nz]).
    assert (HR12s6 : R12 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s6 | nz]).
    assert (HR12s7 : R12 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s7 | nz]).
    assert (HR12s8 : R12 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /R12 upd_ne; [exact HR11s8 | nz]).
    assert (HR12sp : ba_sp m R12)
      by (rewrite /ba_sp /R12 upd_ne; [exact HR11sp | nz]).
    assert (HR12thr : ba_thr9 m R12).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R12 upd_ne; [| regne].
      exact (HR11thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0a0 : add_vec_int (mword_of_int (KernelSyms.balloc + 0x9c) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0xa0)) by pcw.
    iEval (rewrite Hpp0a0) in "Hpc".
    (* ===== +0xa0 lw a5,28(s6) : a5 := sb.bmapstart ===== *)
    assert (Hbmadr : add_vec (rget R12 Rs6)
                       (sign_extend' 64 (mword_of_int 28 : mword 12))
                     = sb_bmapstart).
    { rgne. rewrite HR12s6. unfold sb_bmapstart, pa_add, add_vec_int.
      apply f_equal. pcw. }
    iEval (rewrite -Hbmadr) in "Hsbbm".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.balloc + 0xa0)) Ra5 Rs6
              (mword_of_int 28 : mword 12) R12 (K - 10)%nat
              (mword_of_int bmapstart : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a0 Hsbbm").
    iIntros (CIDb25 Hq25) "Hcg Hpc Hsbbm".
    iEval (rewrite Hbmadr) in "Hsbbm".
    set (R13 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int bmapstart : mword 32))]> R12).
    assert (HR13a5 : R13 !!! Regidx Ra5
                     = (sign_extend' 64 (mword_of_int bmapstart : mword 32) : mword 64))
      by (rewrite /R13; apply upd_eq).
    assert (HR13a1 : R13 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12a1 | nz]).
    assert (HR13s3 : R13 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s3 | nz]).
    assert (HR13s4 : R13 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s4 | nz]).
    assert (HR13s5 : R13 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s5 | nz]).
    assert (HR13s6 : R13 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s6 | nz]).
    assert (HR13s7 : R13 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s7 | nz]).
    assert (HR13s8 : R13 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /R13 upd_ne; [exact HR12s8 | nz]).
    assert (HR13sp : ba_sp m R13)
      by (rewrite /ba_sp /R13 upd_ne; [exact HR12sp | nz]).
    assert (HR13thr : ba_thr9 m R13).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R13 upd_ne; [| regne].
      exact (HR12thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0a4 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xa0) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0xa4)) by pcw.
    iEval (rewrite Hpp0a4) in "Hpc".
    (* ===== +0xa4 c.addw a1,a1,a5 : a1 := BBLOCK(0,sb) = bmapstart ===== *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.balloc + 0xa4)) Ra1 Ra5
              R13 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a4").
    iIntros (CIDb26 Hq26) "Hcg Hpc".
    set (R14 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget R13 Ra1) 31 0 : mword 32)
                              (subrange_vec_dec (rget R13 Ra5) 31 0 : mword 32)))]> R13).
    assert (HR14a1 : R14 !!! Regidx Ra1 = (sign_extend' 64 bnoB : mword 64)).
    { rewrite /R14 upd_eq. rgne. rgne. rewrite HR13a1 HR13a5.
      rewrite /bnoB. apply bal_addw_zero_l. }
    assert (HR14s3 : R14 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s3 | nz]).
    assert (HR14s4 : R14 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s4 | nz]).
    assert (HR14s5 : R14 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s5 | nz]).
    assert (HR14s6 : R14 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s6 | nz]).
    assert (HR14s7 : R14 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s7 | nz]).
    assert (HR14s8 : R14 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /R14 upd_ne; [exact HR13s8 | nz]).
    assert (HR14sp : ba_sp m R14)
      by (rewrite /ba_sp /R14 upd_ne; [exact HR13sp | nz]).
    assert (HR14thr : ba_thr9 m R14).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R14 upd_ne; [| regne].
      exact (HR13thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0a6 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xa4) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xa6)) by pcw.
    iEval (rewrite Hpp0a6) in "Hpc".
    (* ===== +0xa6 c.mv a0,s7 : a0 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0xa6)) Ra0 Rs7
              R14 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0a6").
    iIntros (CIDb27 Hq27) "Hcg Hpc".
    set (R15 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R14 Rs7))]> R14).
    assert (HR15a0 : R15 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R15 upd_eq. rgne. rewrite HR14s7. apply add_vec_zero_l. }
    assert (HR15a1 : R15 !!! Regidx Ra1 = (sign_extend' 64 bnoB : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14a1 | nz]).
    assert (HR15s3 : R15 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s3 | nz]).
    assert (HR15s4 : R15 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s4 | nz]).
    assert (HR15s5 : R15 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s5 | nz]).
    assert (HR15s6 : R15 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s6 | nz]).
    assert (HR15s7 : R15 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s7 | nz]).
    assert (HR15s8 : R15 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /R15 upd_ne; [exact HR14s8 | nz]).
    assert (HR15sp : ba_sp m R15)
      by (rewrite /ba_sp /R15 upd_ne; [exact HR14sp | nz]).
    assert (HR15thr : ba_thr9 m R15).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /R15 upd_ne; [| regne].
      exact (HR14thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0a8 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xa6) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xa8)) by pcw.
    iEval (rewrite Hpp0a8) in "Hpc".
    (* ===== +0xa8 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.balloc + 0xa8)) Rra
              (mword_of_int 2096484 : mword 21) R15 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a8").
    iIntros (CIDb28 Hq28) "Hcg Hpc".
    set (RA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.balloc + 0xa8) : mword 64) 4)]> R15).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.balloc + 0xa8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096484 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HRAra : RA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.balloc + 0xa8) : mword 64) 4)
      by (rewrite /RA; apply upd_eq).
    assert (HRAa0 : RA !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR15a0 | nz]).
    assert (HRAa1 : RA !!! Regidx Ra1 = (sign_extend' 64 bnoB : mword 64))
      by (rewrite /RA upd_ne; [exact HR15a1 | nz]).
    assert (HRAs3 : RA !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s3 | nz]).
    assert (HRAs4 : RA !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s4 | nz]).
    assert (HRAs5 : RA !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s5 | nz]).
    assert (HRAs6 : RA !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s6 | nz]).
    assert (HRAs7 : RA !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s7 | nz]).
    assert (HRAs8 : RA !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /RA upd_ne; [exact HR15s8 | nz]).
    assert (HRAsp : ba_sp m RA)
      by (rewrite /ba_sp /RA upd_ne; [exact HR15sp | nz]).
    assert (HRAthr : ba_thr9 m RA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /RA upd_ne; [| regne].
      exact (HR15thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    iDestruct (cpu_own_transport CID CIDb28 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CID CIDb28 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CID CIDb28 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDb28) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 10)%nat) by (lia).
    iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bnoB dq
              RA (K - 10)%nat eb b lks Vpr
              HKbr HbnoBlt eq_refl HbnoBcov eq_refl Hj Hgl HRAa0 HRAa1
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpanenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CIDb29 Hq29 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc0ac : ret_pc (RA !!! Regidx Rra : mword 64)
                     = mword_of_int (KernelSyms.balloc + 0xac))
      by (rewrite HRAra; pcw).
    iEval (rewrite Hpc0ac) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs3 : mB !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HRAs3).
    assert (HmBs4 : mB !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HRAs4).
    assert (HmBs5 : mB !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HRAs5).
    assert (HmBs6 : mB !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HRAs6).
    assert (HmBs7 : mB !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs7 ltac:(vm_compute; reflexivity));
          exact HRAs7).
    assert (HmBs8 : mB !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs8 ltac:(vm_compute; reflexivity));
          exact HRAs8).
    assert (HmBsp : ba_sp m mB).
    { rewrite /ba_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HRAsp. }
    assert (HmBthr : ba_thr9 m mB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HRAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    (* THE COUPLING: the buffer's bytes ARE the bitmap's image of [used] *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iEval (rewrite -HbnoB) in "Hfsbm".
    iDestruct (iu_held_content with "Hfsbm Hheld") as %Hbs0.
    subst bs0.
    iEval (rewrite HbnoB) in "Hfsbm".
    iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bnoB
               (bitmap_bytes used) bsd0 d0) with "[Hheld]" as "Hlk";
      [rewrite /bio_locked; iExact "Hheld" |].
    iPoseProof (bai_0ac with "Htext") as "Hi0ac".
    iPoseProof (bai_0ae with "Htext") as "Hi0ae".
    iPoseProof (bai_0b2 with "Htext") as "Hi0b2".
    iPoseProof (bai_0b4 with "Htext") as "Hi0b4".
    (* ===== +0xac c.mv s2,a0 : s2 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0xac)) Rs2 Ra0
              mB (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0ac").
    iIntros (CIDb30 Hq30) "Hcg Hpc".
    set (W1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HW1s2 : W1 !!! Regidx Rs2 = bnode kk).
    { rewrite /W1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HW1s3 : W1 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs3 | nz]).
    assert (HW1s4 : W1 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs4 | nz]).
    assert (HW1s5 : W1 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs5 | nz]).
    assert (HW1s6 : W1 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs6 | nz]).
    assert (HW1s7 : W1 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs7 | nz]).
    assert (HW1s8 : W1 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /W1 upd_ne; [exact HmBs8 | nz]).
    assert (HW1sp : ba_sp m W1)
      by (rewrite /ba_sp /W1 upd_ne; [exact HmBsp | nz]).
    assert (HW1thr : ba_thr9 m W1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /W1 upd_ne; [| regne].
      exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0ae : add_vec_int (mword_of_int (KernelSyms.balloc + 0xac) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xae)) by pcw.
    iEval (rewrite Hpp0ae) in "Hpc".
    (* ===== +0xae lw a0,4(s6) : a0 := sb.size ===== *)
    assert (Hszadr2 : add_vec (rget W1 Rs6)
                        (sign_extend' 64 (mword_of_int 4 : mword 12))
                      = sb_size).
    { rgne. rewrite HW1s6. unfold sb_size, pa_add, add_vec_int.
      apply f_equal. pcw. }
    iEval (rewrite -Hszadr2) in "Hsbsz".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.balloc + 0xae)) Ra0 Rs6
              (mword_of_int 4 : mword 12) W1 (K - 10)%nat
              (mword_of_int size : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0ae Hsbsz").
    iIntros (CIDb31 Hq31) "Hcg Hpc Hsbsz".
    iEval (rewrite Hszadr2) in "Hsbsz".
    set (W2 := <[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int size : mword 32))]> W1).
    assert (HW2a0 : W2 !!! Regidx Ra0
                    = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
      by (rewrite /W2; apply upd_eq).
    assert (HW2s2 : W2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /W2 upd_ne; [exact HW1s2 | nz]).
    assert (HW2s3 : W2 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s3 | nz]).
    assert (HW2s4 : W2 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s4 | nz]).
    assert (HW2s5 : W2 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s5 | nz]).
    assert (HW2s6 : W2 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s6 | nz]).
    assert (HW2s7 : W2 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s7 | nz]).
    assert (HW2s8 : W2 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s8 | nz]).
    assert (HW2sp : ba_sp m W2)
      by (rewrite /ba_sp /W2 upd_ne; [exact HW1sp | nz]).
    assert (HW2thr : ba_thr9 m W2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /W2 upd_ne; [| regne].
      exact (HW1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0b2 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xae) : mword 64) 4
                     = mword_of_int (KernelSyms.balloc + 0xb2)) by pcw.
    iEval (rewrite Hpp0b2) in "Hpc".
    (* ===== +0xb2 c.mv s1,s5 : bi := b = 0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.balloc + 0xb2)) Rs1 Rs5
              W2 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0b2").
    iIntros (CIDb32 Hq32) "Hcg Hpc".
    set (W3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget W2 Rs5))]> W2).
    assert (HW3s1 : W3 !!! Regidx Rs1 = (mword_of_int 0 : mword 64)).
    { rewrite /W3 upd_eq. rgne. rewrite HW2s5. apply add_vec_zero_l. }
    assert (HW3a0 : W3 !!! Regidx Ra0
                    = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2a0 | nz]).
    assert (HW3s2 : W3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /W3 upd_ne; [exact HW2s2 | nz]).
    assert (HW3s3 : W3 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s3 | nz]).
    assert (HW3s4 : W3 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s4 | nz]).
    assert (HW3s5 : W3 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s5 | nz]).
    assert (HW3s6 : W3 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s6 | nz]).
    assert (HW3s7 : W3 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s7 | nz]).
    assert (HW3s8 : W3 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s8 | nz]).
    assert (HW3sp : ba_sp m W3)
      by (rewrite /ba_sp /W3 upd_ne; [exact HW2sp | nz]).
    assert (HW3thr : ba_thr9 m W3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /W3 upd_ne; [| regne].
      exact (HW2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0b4 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xb2) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xb4)) by pcw.
    iEval (rewrite Hpp0b4) in "Hpc".
    (* ===== +0xb4 c.li a4,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.balloc + 0xb4)) Ra4
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              W3 (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi0b4").
    iIntros (CIDb33 Hq33) "Hcg Hpc".
    set (W4 := <[Regidx Ra4 := regval_into_reg (mword_of_int 0 : mword 64)]> W3).
    assert (HW4a4 : W4 !!! Regidx Ra4 = (mword_of_int 0 : mword 64))
      by (rewrite /W4; apply upd_eq).
    assert (HW4a0 : W4 !!! Regidx Ra0
                    = (sign_extend' 64 (mword_of_int size : mword 32) : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3a0 | nz]).
    assert (HW4s1 : W4 !!! Regidx Rs1 = (mword_of_int 0 : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s1 | nz]).
    assert (HW4s2 : W4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /W4 upd_ne; [exact HW3s2 | nz]).
    assert (HW4s3 : W4 !!! Regidx Rs3 = (mword_of_int 1 : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s3 | nz]).
    assert (HW4s4 : W4 !!! Regidx Rs4 = (mword_of_int 8192 : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s4 | nz]).
    assert (HW4s5 : W4 !!! Regidx Rs5 = (mword_of_int 0 : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s5 | nz]).
    assert (HW4s6 : W4 !!! Regidx Rs6 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s6 | nz]).
    assert (HW4s7 : W4 !!! Regidx Rs7 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s7 | nz]).
    assert (HW4s8 : W4 !!! Regidx Rs8 = (mword_of_int 8192 : mword 64))
      by (rewrite /W4 upd_ne; [exact HW3s8 | nz]).
    assert (HW4sp : ba_sp m W4)
      by (rewrite /ba_sp /W4 upd_ne; [exact HW3sp | nz]).
    assert (HW4thr : ba_thr9 m W4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
      rewrite /W4 upd_ne; [| regne].
      exact (HW3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22 N23 N24). }
    assert (Hpp0b6 : add_vec_int (mword_of_int (KernelSyms.balloc + 0xb4) : mword 64) 2
                     = mword_of_int (KernelSyms.balloc + 0xb6)) by pcw.
    iEval (rewrite Hpp0b6) in "Hpc".
    (* ===== +0xb6 : INTO THE SCAN, at bi = 0 with the full tank ===== *)
    iDestruct (cpu_own_transport CIDb29 CIDb33 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (IntrDefs.trap_csrs_ext_transport CIDb29 CIDb33 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (IntrDefs.cpu_claim_ext_transport CIDb29 CIDb33 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iApply (ba_scan γs j γl γu γd γk pd pav pu γfs bn γ γpr cov logstart
              bmapstart size dev used u cr Sb kk bnoB bsd0 d0 pidv dq dqb dqs
              m K eb b lks Vpr (Z.to_nat BPB)
              HK Hpk Hgeom Hsize HbnoB Hbmcov Hbmlog Hok Hkk Hj Hgl Hcred
              CIDb33 0 W4 ba_fuel_full ba_bi_zero HW4sp HW4thr
              HW4a0 HW4a4 HW4s1 HW4s2 HW4s3 HW4s4 HW4s5 HW4s6 HW4s7 HW4s8 Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hkdata Hpc Hpenv Hbio Hlctx Hprocs Hframe Hppid Hsbsz Hsbbm Hdevi Hdgeom
                    Hdlock Hsl Hop Hfsbm Hpool Hlk [Hcont]").
    { iApply (wp_next_shift (b := true) (CIDa := CIDb28) (CIDb := CIDb33)
                ltac:(wp_next_chain) with "Hcont"). }
  Qed.

  (* THE CREDITED CONTRACT.  Since [wp_balloc_gen_body] became eb-generic
     too (bmap's credited path routes here, and a core pinned at
     [eb = true] would have cost a second proof of bmap's 70 instructions),
     this IS [ba_main] -- the statements coincide and the derivation is a
     bare [iApply] with nothing to discharge. *)
  Lemma wp_balloc_gen
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (γpr : gname)
      (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_balloc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart bmapstart size dev used γpr u cr Sb
                         pidv dq dqb dqs m K eb b lks Vpr.
  Proof.
    exact (ba_main γs j γl γu γd γk pd pav pu bn γ γfs
             cov logstart bmapstart size dev used γpr u cr Sb
             pidv dq dqb dqs m K eb b lks Vpr).
  Qed.

  (* THE SET-FORGETTING CONTRACT, at [cr = false].  Every existing caller
     threads [log_op] and is unchanged; only a caller that is allocating
     SEVERAL blocks in one transaction -- bmap under writei -- reaches for
     the credited form. *)
  Lemma wp_balloc_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (γpr : gname)
      (u : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_balloc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart bmapstart size dev used γpr u
                           pidv dq dqb dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_balloc_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hpk Hsize Hbm0 Hbmcov Hbmlog Hj Hgl Ha0 Hbelow.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hkdata #Hpenv #Hbio #Hlctx Hppid
              Hsbsz Hsbbm Hbmr #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    rewrite /log_op. iDestruct "Hop" as (Sb) "Hop".
    (* [ba_main] is the eb-generic core both top-level lemmas share -- see
       its header comment -- so [wp_balloc_sconf], which genuinely needs
       [eb = false], applies it directly instead of routing through
       [wp_balloc_gen] (whose OWN statement stays pinned at [eb = true]). *)
    iApply (ba_main γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart bmapstart size dev used γpr u false Sb
              pidv dq dqb dqs m K eb b lks
              Vpr HK Hgeom Hpk Hsize Hbm0 Hbmcov Hbmlog ltac:(discriminate)
              Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hkdata Hpenv Hbio Hlctx Hppid
                    Hsbsz Hsbbm Hbmr Hprocs Hdevi Hdgeom Hdlock Hsl Hop [Hcont]").
    iIntros (CIDx) "%Hchain". iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hchain|].
    iIntros (mf) "%Hcs Hsie Hcnt Htc Hclm Hpc Hppid Hsbsz Hsbbm Hsl Harms".
    iApply ("Hcont" $! mf with "[%] Hsie Hcnt Htc Hclm Hpc Hppid Hsbsz Hsbbm Hsl [Harms]");
      [exact Hcs|].
    iDestruct "Harms" as "[(%Hz & Hbmr & Hop) | Hr]".
    - iLeft. iSplitR; [iPureIntro; exact Hz|]. iFrame "Hbmr".
      iApply (log_opS_op with "Hop").
    - iDestruct "Hr" as (blk) "(%Ha & %Hnz & %Hcv & %Hlg & Hfsb & Hown & Hbmr & Hop)".
      iRight. iExists blk.
      iSplitR; [iPureIntro; exact Ha|].
      iSplitR; [iPureIntro; exact Hnz|].
      iSplitR; [iPureIntro; exact Hcv|].
      iSplitR; [iPureIntro; exact Hlg|].
      iFrame "Hfsb Hown Hbmr".
      iApply (log_opS_op with "Hop").
  Qed.

End BallocMain.

End BallocProof.
