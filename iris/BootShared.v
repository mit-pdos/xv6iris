(* ====================================================================== *)
(* BootShared.v -- THE SHARED BOOT CONTEXT.                                *)
(*                                                                        *)
(* [BootChain.v] states one hart's whole life, twice ([boot_hart_primary]  *)
(* for the boot hart, [boot_hart_secondary] for the other seven), over     *)
(* [boot_hart_res] plus a handful of SHARED persistents plus -- on the     *)
(* boot arm -- the whole boot supply.  This file produces all of that,     *)
(* ONCE, out of what a power-on actually hands a client                    *)
(* ([RiscvAdequacy.power_boot_res]).  With it, the system theorem is       *)
(* "allocation once + the chain eight times" and nothing else.             *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import csum excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
Require Import HartTp.
Require Import KMap KptPt KptGhost.
Require Import StackOwn.
Require Import KernelText KernelDataInv.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom SwtchCtx SchedCtx.
Require Import WpLock KallocInv FdSlots.
Require Import FileInvDefs.
Require Import VirtioProto VirtioModel VirtioQueue DiskPtsto.
Require Import PlicPlan WpUart WireInv.
Require Import SpecConsoleinit SpecIinit.
Require Import SpecFreerange KvmSpec BcacheInv.
Require Import StartedInv SpecPanic LinkPanic.
Require Import SpecMain SpecMainSecondary.
Require Import BootConfig PowerBoot.
Require Import BootCarve BootCarveMain.
Require Import BootChain.
Require Import MbootVocab.
Require Import RiscvAdequacy.
Require Import BootReset.   (* the garbage-anchored register clause's bridge *)
From Kernel Require KernelData.
From Kernel Require KernelSyms.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import TicksInv UartTxInv.
Local Open Scope Z_scope.

(* a syscall-altitude goal contains [ProcInv.tf_page]'s 4096-conjunct big-op:
   without this a one-line mistake prints for tens of minutes instead of
   reporting (durable-notes). *)
Set Printing Depth 40.

(* ====================================================================== *)
(* §1  THE PURE BRIDGES.                                                   *)
(* ====================================================================== *)

(* [boot_facts]' memory clauses, in the two spellings every carve entry point
   asks for: "nothing outside RAM" as [addr_is_ram] (BootCarve §3/§4) and "all
   of RAM, holding the loaded image" in the [pa_of_z] form (§6 onwards). *)
(* the [uint]-free arithmetic step, over a plain [Z] VARIABLE: with the
   [bv_unsigned] in context [lia] answers "Cannot find witness" under
   [bitvector.tactics]' zify hook (durable-notes), and this file is deep under
   that hook. *)
Lemma z_ram_of (u : Z) :
  ram_lo <= u < ram_hi -> ram_base <= u < ram_base + ram_size.
Proof. unfold ram_lo, ram_hi, ram_base, ram_size. lia. Qed.

Lemma boot_ram_of_facts (g : gstate) :
  boot_facts g -> forall a b, g.(gmem) !! a = Some b -> addr_is_ram a.
Proof.
  intros (_ & Hin & _) a b Hlk.
  exact (z_ram_of (uint a) (Hin a b Hlk)).
Qed.

Lemma boot_mem_of_facts (g : gstate) :
  boot_facts g ->
  forall x : Z, ram_lo <= x < ram_hi -> g.(gmem) !! pa_of_z x = Some (boot_byte x).
Proof. intros (_ & _ & Hmem & _) x Hx. exact (Hmem x Hx). Qed.

(* [boot_facts]' register clause is a run of the boot program over ARBITRARY
   power-on garbage (the board's explicit writes + the spec's validated reset); [BootReset.reset_regs_of_run] is the bridge to the
   fifteen-way fact set every consumer above asks for by name.  This is that
   bridge's only caller, which is why the whole chain above is unchanged. *)
Lemma boot_regs_of_facts (g : gstate) :
  boot_facts g -> forall c : CPU, reset_regs c (g.(gregs) c).
Proof.
  intros (_ & _ & _ & Hr & _) c.
  destruct (Hr c) as (rs0 & rs1 & Hrun & Heq).
  rewrite Heq. exact (BootReset.reset_regs_of_run c rs0 rs1 Hrun).
Qed.

(* THE CUT CURSOR, and it is the whole shape of the .bss chain: the client owns
   ONE range and walks it in ADDRESS order, taking each bundle's window and
   keeping the tail.  The skipped prefix is DROPPED -- every gap in the layout
   table (tx_chan, ticks, sb, log, a record's padding) is claimed by
   nobody, and [boot_raw_ran] is affine.  With this, one bundle is one line. *)
Lemma bss_cut `{!riscvGS Σ} (g : gstate) (lo a b hi : Z) :
  lo <= a -> a <= b -> b <= hi ->
  boot_raw_ran g lo hi ⊢ boot_raw_ran g a b ∗ boot_raw_ran g b hi.
Proof.
  intros H1 H2 H3. iIntros "H".
  iDestruct (boot_ran_split g lo a hi H1 ltac:(lia) with "H") as "[_ H]".
  iDestruct (boot_ran_split g a b hi H2 H3 with "H") as "[H1 H2]".
  iFrame "H1 H2".
Qed.

(* THE HART ENUMERATION AS AN INDEX RANGE.  Every per-hart .bss object is an
   element of a STRIDE FAMILY over [seq 0 NCPU] (stack0's eight 4096-byte
   slices, cpus[]'s eight 128-byte records), while every consumer wants a
   [[∗ list] c ∈ enum CPU].  This is the one bridge, and it is what lets
   BootCarve §11's family serve the per-hart carve with no per-hart copies. *)
Lemma fin_to_nat_fin_enum (n : nat) : fin_to_nat <$> fin_enum n = seq 0 n.
Proof.
  induction n as [|k IH]; [reflexivity |].
  (* the [FS]-shift, by plain induction rather than by [list_fmap_compose]:
     the composed form does not match after [cbn [fin_enum]]. *)
  assert (Hc : forall l : list (fin k),
            fin_to_nat <$> (FS <$> l) = S <$> (fin_to_nat <$> l)).
  { intro l. induction l as [|x l IHl]; [reflexivity |]. cbn. by rewrite IHl. }
  cbn [fin_enum]. rewrite fmap_cons Hc IH fmap_S_seq. reflexivity.
Qed.

Lemma big_sepL_cpu_of_nat {PROP : bi} (Φ : nat -> PROP) :
  ([∗ list] i ∈ seq 0 NCPU, Φ i) ⊢ [∗ list] c ∈ enum CPU, Φ (fin_to_nat c).
Proof.
  rewrite -(fin_to_nat_fin_enum NCPU) big_sepL_fmap. done.
Qed.

(* ====================================================================== *)
(* §2  THE PER-HART .bss ADDRESSES.                                        *)
(*                                                                        *)
(* [IntrDefs.cpu_cells] names its four cells through [ProcGeom]'s          *)
(* [mycpu_ret]-derived field addresses at [cid_word]; the carve produces    *)
(* them at [pa_of_z (cpus + 128*h + off)].  These four equations are that   *)
(* bridge, and being CLOSED once the hart index is, each is eight           *)
(* [vm_compute]s and needs no [lia] (BootChain §1's discipline).            *)
(* ====================================================================== *)

Definition cpu_slot (n : nat) : Z := KernelSyms.cpus + 128 * Z.of_nat n.

Lemma a_cpu_proc_of_z (n : nat) :
  (n < NCPU)%nat ->
  a_cpu_proc (mword_of_int (Z.of_nat n) : mword 64) = pa_of_z (cpu_slot n).
Proof.
  unfold NCPU, cpu_slot. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma a_cpu_ctx_of_z (n : nat) :
  (n < NCPU)%nat ->
  a_cpu_ctx (mword_of_int (Z.of_nat n) : mword 64)
  = add_vec (pa_of_z (cpu_slot n)) (mword_of_int 8 : mword 64).
Proof.
  unfold NCPU, cpu_slot. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma a_cpu_noff_of_z (n : nat) :
  (n < NCPU)%nat ->
  a_cpu_noff (mword_of_int (Z.of_nat n) : mword 64)
  = add_vec (pa_of_z (cpu_slot n)) (mword_of_int 120 : mword 64).
Proof.
  unfold NCPU, cpu_slot. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma a_cpu_int_of_z (n : nat) :
  (n < NCPU)%nat ->
  a_cpu_int (mword_of_int (Z.of_nat n) : mword 64)
  = add_vec (pa_of_z (cpu_slot n)) (mword_of_int 124 : mword 64).
Proof.
  unfold NCPU, cpu_slot. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...and the same four at [cid_word_of h], which is the spelling every
   consumer uses ([cid_word_of i] IS [mword_of_int (Z.of_nat (fin_to_nat i))],
   so these are the four above with the hart bound rather than assumed). *)
Lemma a_cpu_proc_cid (h : CPU) :
  a_cpu_proc (cid_word_of h) = pa_of_z (cpu_slot (fin_to_nat h)).
Proof. rewrite /cid_word_of. exact (a_cpu_proc_of_z _ (fin_to_nat_lt h)). Qed.

Lemma a_cpu_ctx_cid (h : CPU) :
  a_cpu_ctx (cid_word_of h)
  = add_vec (pa_of_z (cpu_slot (fin_to_nat h))) (mword_of_int 8 : mword 64).
Proof. rewrite /cid_word_of. exact (a_cpu_ctx_of_z _ (fin_to_nat_lt h)). Qed.

Lemma a_cpu_noff_cid (h : CPU) :
  a_cpu_noff (cid_word_of h)
  = add_vec (pa_of_z (cpu_slot (fin_to_nat h))) (mword_of_int 120 : mword 64).
Proof. rewrite /cid_word_of. exact (a_cpu_noff_of_z _ (fin_to_nat_lt h)). Qed.

Lemma a_cpu_int_cid (h : CPU) :
  a_cpu_int (cid_word_of h)
  = add_vec (pa_of_z (cpu_slot (fin_to_nat h))) (mword_of_int 124 : mword 64).
Proof. rewrite /cid_word_of. exact (a_cpu_int_of_z _ (fin_to_nat_lt h)). Qed.

(* the hart's stack slice: [_entry] computes sp = &stack0 + 4096*(h+1), so the
   slice BELOW it is the family's own window at index h. *)
Lemma sp_of_slice (n : nat) :
  KernelSyms.stack0 + 4096 * Z.of_nat n + 4096 = sp_of n.
Proof. unfold sp_of. lia. Qed.

(* the plain-[Z] arithmetic the two per-hart families need, over VARIABLES and
   at the top level, so no [uint]/[bv_unsigned] is ever in scope when [lia]
   runs (durable-notes' zify hook: this file requires [SpecFreerange]). *)
Lemma z_stk_lo (A : Z) :
  ram_lo <= A -> ram_lo + 8 * Z.of_nat boot_stack_depth <= A + 4096.
Proof. unfold boot_stack_depth. lia. Qed.

Lemma z_stk_base (A : Z) : A = A + 4096 - 8 * Z.of_nat boot_stack_depth.
Proof. unfold boot_stack_depth. lia. Qed.

Lemma z_stk_top (A : Z) : A + 4096 <= ram_hi -> A + 4096 <= ram_hi.
Proof. exact (fun H => H). Qed.

(* ====================================================================== *)
(* §3  THE PER-HART .bss, AS TWO STRIDE FAMILIES.                          *)
(*                                                                        *)
(* stack0's eight 4096-byte slices and cpus[]'s eight 128-byte records are  *)
(* index families, so BootCarve §11 gives each of them out of ONE range     *)
(* with the per-element carve written once -- there is no per-hart copy of  *)
(* anything here.  §1's [big_sepL_cpu_of_nat] then re-indexes the two       *)
(* [seq 0 NCPU] big-ops by [enum CPU], which is the spelling every consumer *)
(* (and the chain) asks for.                                              *)
(* ====================================================================== *)

Section BootBss.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
            !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  (* ---- the stack family.  The per-element shape is NAMED (a lambda [Φ]
         leaves the family's per-element goal a beta-redex [iApply] will not
         see through), and it is stated at the slice's TOP because that is
         where [_entry]'s sp lands: the hart's own 4096 bytes are
         [uint sp0 - 8*512, uint sp0). *)
  Local Definition hart_stack_raw (a : Arch.pa) : iProp Σ :=
    stack_own_phys (add_vec a (mword_of_int 4096 : mword 64)) boot_stack_depth.

  Lemma boot_hart_stack_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    ram_lo <= A -> A + 4096 < ram_hi -> A mod 8 = 0 ->
    boot_raw_ran g A (A + 4096) ⊢ hart_stack_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hhi Hal.
    rewrite /hart_stack_raw off_of_z.
    assert (Hu : uint (pa_of_z (A + 4096)) = A + 4096)
      by (apply boot_uint_pa; lia).
    iIntros "H".
    iApply (boot_stack_own_phys g (pa_of_z (A + 4096)) boot_stack_depth Hmem
              ltac:(rewrite Hu; exact (z_stk_lo A Hlo))
              ltac:(rewrite Hu; exact (z_stk_top A ltac:(lia)))
              ltac:(rewrite Hu; exact (z_mod_addo 8 A 4096 Hal eq_refl))).
    iApply (boot_ran_eq g A (A + 4096)
              (uint (pa_of_z (A + 4096)) - 8 * Z.of_nat boot_stack_depth)
              (uint (pa_of_z (A + 4096)))
              ltac:(rewrite Hu; exact (z_stk_base A))
              ltac:(rewrite Hu; reflexivity) with "H").
  Qed.

  (* ---- the cpus[] family.  ONE 128-byte record gives all four cells
         [IntrDefs.cpu_cells] names: [proc] at +0 (a PINNED .bss zero, handed
         out WHOLE here and split into the bridge's half and main's half per
         hart below), the 14-word scheduler context at +8, [noff] at +120
         (pinned zero -- [cpu_own 0] is what the bridge produces) and
         [intena] at +124 (contents-existential: nothing reads it before
         push_off writes it). *)
  Local Definition cpu_slot_raw (a : Arch.pa) : iProp Σ :=
    (a ↦₈ (zero_reg : mword 64) ∗
     own_ctx (add_vec a (mword_of_int 8 : mword 64)) ∗
     (add_vec a (mword_of_int 120 : mword 64)) ↦₄ noff_val 0 ∗
     (∃ iv : mword 32, (add_vec a (mword_of_int 124 : mword 64)) ↦₄ iv))%I.

  Lemma boot_cpu_slot_raw (g : gstate) (A : Z) :
    (forall x : Z, ram_lo <= x < ram_hi ->
       g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
    text_end <= A -> img_end <= A -> A + 128 <= ram_hi -> A mod 8 = 0 ->
    kmap_static_claims -∗ boot_raw_ran g A (A + 128) -∗ cpu_slot_raw (pa_of_z A).
  Proof.
    intros Hmem Hlo Hbss Hhi Hal. iIntros "#Hcl H".
    iDestruct (bss_cut g A A (A + 8) (A + 128)
                 ltac:(lia) ltac:(lia) ltac:(lia) with "H") as "[H0 H]".
    iDestruct (bss_cut g (A + 8) (A + 8) (A + 8 + 112) (A + 128)
                 ltac:(lia) ltac:(lia) ltac:(lia) with "H") as "[H1 H]".
    iDestruct (bss_cut g (A + 8 + 112) (A + 120) (A + 120 + 4) (A + 128)
                 ltac:(lia) ltac:(lia) ltac:(lia) with "H") as "[H2 H]".
    iDestruct (bss_cut g (A + 120 + 4) (A + 124) (A + 124 + 4) (A + 128)
                 ltac:(lia) ltac:(lia) ltac:(lia) with "H") as "[H3 _]".
    iDestruct (boot_ran_cell8_bss g A (zero_reg : mword 64) Hmem Hlo Hbss
                 ltac:(lia) Hal nth_byte_zero8 with "Hcl H0") as "H0".
    iDestruct (boot_own_ctx g (A + 8) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 8 A 8 Hal eq_refl)) with "Hcl H1")
      as "H1".
    iDestruct (boot_ran_cell4_bss g (A + 120) (noff_val 0) Hmem
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 120 (z_mod8_mod4 A Hal) eq_refl))
                 ltac:(intros j _; apply nth_byte_zero;
                       vm_compute; reflexivity) with "Hcl H2") as "H2".
    iDestruct (boot_ran_cell4 g (A + 124) Hmem ltac:(lia) ltac:(lia)
                 ltac:(exact (z_mod_addo 4 A 124 (z_mod8_mod4 A Hal) eq_refl))
                 with "Hcl H3") as (iv) "H3".
    rewrite /cpu_slot_raw !off_of_z.
    iFrame "H0 H1 H2". iExists iv. iExact "H3".
  Qed.

End BootBss.

(* ====================================================================== *)
(* §4  THE .bss CHAIN.                                                     *)
(*                                                                        *)
(* Everything above [img_end] is ZERO in the loaded image and OWNED by the  *)
(* client, as ONE range; every bundle main and the chain ask for is a       *)
(* window of it.  So the whole of this section is §1's cursor walked in     *)
(* ADDRESS order (the layout table in claude-notes/completed/crash.md is    *)
(* that order, boundary by boundary), handing each window to its carve      *)
(* lemma.  Nothing here is a proof: a wrong boundary is a unification       *)
(* failure at the next cut, which is exactly what makes the walk safe.      *)
(* ====================================================================== *)

Local Ltac zlit := vm_compute; discriminate.
Local Ltac zeq := vm_compute; reflexivity.

Lemma z_strict (x y : Z) : x <= y - 1 -> x < y.
Proof. lia. Qed.

(* kinit's free-page run, as [SpecMain]'s premises spell it: the cursor
   [PGROUNDUP(end) + PGSIZE], PHYSTOP, and the page count that puts the cursor
   exactly one page past PHYSTOP. *)
Definition s1entry_val : mword 64 :=
  add_vec (and_vec (add_vec (mword_of_int 0x80023558 : mword 64)
     (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv.
Definition phystop_val : mword 64 := mword_of_int 0x88000000.
Definition kinit_pages : nat := 32732%nat.

Lemma s1entry_uint : uint s1entry_val = 0x80025000.
Proof. vm_compute. reflexivity. Qed.
Lemma phystop_uint : uint phystop_val = 0x88000000.
Proof. vm_compute. reflexivity. Qed.
(* NB not [lia]: a nat literal this large elaborates as an
   [Init.Nat.of_num_uint] application (Rocq's own stack-overflow guard, which
   it warns about at the [Definition] above), and [lia] cannot see through it.
   Go through [Nat.ltb] so the whole comparison is one [vm_compute]. *)
Lemma kinit_budget : (K_kvmmake + 64 + 3 < kinit_pages)%nat.
Proof.
  apply (proj1 (Nat.ltb_lt _ _)).
  unfold K_kvmmake, kinit_pages. vm_compute. reflexivity.
Qed.

Section BootBssChain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ,
            !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  (* ONE hart's memory share, exactly as [BootChain.boot_hart_res] spells it
     (its stack slice and its four [cpus[h]] cells; the image word it also
     takes is PERSISTENT and shared, so it is not here).

     [cpus[h].proc] is carved WHOLE and stays whole: it is private to hart
     [h] (no invariant and no lock reads it), so it lives in that hart's
     [IntrDefs.cpu_cells] and the scheduler's two stores to it are plain
     stores to memory it already owns. *)
  Definition boot_hart_bss (h : CPU) : iProp Σ :=
    (stack_own_phys (mword_of_int (sp_of (fin_to_nat h))) boot_stack_depth ∗
     a_cpu_noff (cid_word_of h) ↦₄ noff_val 0 ∗
     (∃ iv : mword 32, a_cpu_int (cid_word_of h) ↦₄ iv) ∗
     a_cpu_proc (cid_word_of h) ↦₈ (zero_reg : mword 64) ∗
     own_ctx (a_cpu_ctx (cid_word_of h)))%I.

  (* the two families' per-element outputs, restated in the consumer's
     vocabulary. *)
  Lemma boot_hart_bss_of_raw (h : CPU) :
    hart_stack_raw
      (pa_of_z (KernelSyms.stack0 + 4096 * Z.of_nat (fin_to_nat h))) -∗
    cpu_slot_raw (pa_of_z (cpu_slot (fin_to_nat h))) -∗
    boot_hart_bss h.
  Proof.
    iIntros "Hst (Hp & Hctx & Hnoff & Hint)".
    iEval (rewrite /hart_stack_raw off_of_z sp_of_slice) in "Hst".
    rewrite /boot_hart_bss a_cpu_ctx_cid a_cpu_noff_cid a_cpu_int_cid
            a_cpu_proc_cid.
    iSplitL "Hst"; [iExact "Hst" |].
    iFrame "Hnoff Hint Hp Hctx".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE WALK.                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_bss_carve (g : gstate) :
    boot_facts g ->
    kmap_static_claims -∗
    fd_slots FDSLOTS -∗
    (* the iref supply's PROC-LAYER SHARE.  The remaining [NFILE] units of
       [IrefSlots.IREFSLOTS] belong to the file table, which does not park
       them yet ([FileInv.file_payload]'s FD_INODE arm is still a
       placeholder), so boot mints the whole supply and routes this part;
       the file share is dropped at the mint site, marked there. *)
    iref_slots (NPROC * (1 + IREFSPARE)) -∗
    boot_raw_ran g img_end ram_hi -∗
      started_addr ↦₄ started_clear ∗
      main_locks_raw ∗
      main_globals_raw ∗
      ([∗ list] h ∈ enum CPU, boot_hart_bss h) ∗
      (∃ ps : list (mword 64),
         ⌜prun phystop_val s1entry_val ps⌝ ∗
         ⌜(K_kvmmake + 64 + 3 < length ps)%nat⌝ ∗
         ([∗ list] p ∈ ps, page_own p)).
  Proof.
    intro Hbf. pose proof (boot_mem_of_facts g Hbf) as Hmem.
    iIntros "#Hcl Hfd Hir H".
    (* ---- 0x8000a220 panicked, 0x8000a224 panicking ---- *)
    iDestruct (bss_cut g img_end KernelSyms.panicked (KernelSyms.panicked + 4)
                 ram_hi ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H")
      as "[Hpkd H]".
    iDestruct (boot_ran_cell4 g KernelSyms.panicked Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zeq) with "Hcl Hpkd") as (vpkd) "Hpkd".
    iDestruct (bss_cut g (KernelSyms.panicked + 4) KernelSyms.panicking
                 (KernelSyms.panicking + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hpki H]".
    iDestruct (boot_ran_cell4 g KernelSyms.panicking Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hpki") as (vpki) "Hpki".
    (* [tx_chan] (panicking + 4) is NOT carved: ae96fd0 deleted [tx_busy], so
       the word after [panicking] is the sleep channel, whose ADDRESS is all
       anyone uses -- the cell itself is never read or written and belongs to
       nobody (UartTxInv.v).  It is one of the gaps this chain skips. *)
    (* ---- 0x8000a2ac started: PINNED zero, the escrow's left disjunct ---- *)
    iDestruct (bss_cut g (KernelSyms.panicking + 4) KernelSyms.started
                 (KernelSyms.started + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hst H]".
    iDestruct (boot_ran_cell4_bss g KernelSyms.started started_clear Hmem
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 ltac:(intros j _; apply nth_byte_zero; zeq)
                 with "Hcl Hst") as "Hst".
    (* ---- 0x8000a238 kernel_pagetable, 0x8000a270 initproc ---- *)
    iDestruct (bss_cut g (KernelSyms.started + 4) KernelSyms.kernel_pagetable
                 (KernelSyms.kernel_pagetable + 8) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hkpt H]".
    iDestruct (boot_ran_cell8 g KernelSyms.kernel_pagetable Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hkpt") as (vkpt) "Hkpt".
    iDestruct (bss_cut g (KernelSyms.kernel_pagetable + 8) KernelSyms.initproc
                 (KernelSyms.initproc + 8) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hip H]".
    iDestruct (boot_ran_cell8 g KernelSyms.initproc Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hip") as (vip) "Hip".
    (* ---- 0x8000a248 ticks: the tick counter tickslock protects.  main needs
           it to ALLOCATE that lock (is_tickslock = is_lock … ticks_res), which
           is what the handler contract's [tick_keeper] asks of the tick
           hart. ---- *)
    iDestruct (bss_cut g (KernelSyms.initproc + 8) KernelSyms.ticks
                 (KernelSyms.ticks + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Htk H]".
    iDestruct (boot_ran_cell4 g KernelSyms.ticks Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Htk") as (vtk) "Htk".
    (* ---- 0x8000a280 stack0[8][4096]: the per-hart stack family ---- *)
    iDestruct (bss_cut g (KernelSyms.ticks + 4) KernelSyms.stack0
                 (KernelSyms.stack0 + 4096 * Z.of_nat NCPU) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hstk H]".
    iDestruct (boot_stride_family_seq g hart_stack_raw KernelSyms.stack0 4096 NCPU
                 ltac:(lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side KernelSyms.stack0 4096 NCPU 4096
                                   ram_lo (ram_hi - 1) i A Hi HA
                                   ltac:(lia) ltac:(zlit) ltac:(zlit)
                                   ltac:(zeq) ltac:(zeq)) as (Q1 & Q2 & Q3);
                       iIntros "#Hcl2 Hw";
                       iApply (boot_hart_stack_raw g A Hmem Q1
                                 (z_strict _ _ Q2) Q3 with "Hw"))
                 with "Hcl Hstk") as "Hstk".
    (* ---- the six .bss spinlocks up to cpus[], and kmem's free-list head ---- *)
    iDestruct (bss_cut g (KernelSyms.stack0 + 4096 * Z.of_nat NCPU)
                 KernelSyms.cons (KernelSyms.cons + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk1 H]".
    iDestruct (bss_cut g (KernelSyms.cons + 24) KernelSyms.pr
                 (KernelSyms.pr + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk2 H]".
    iDestruct (bss_cut g (KernelSyms.pr + 24) KernelSyms.tx_lock
                 (KernelSyms.tx_lock + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk3 H]".
    iDestruct (bss_cut g (KernelSyms.tx_lock + 24) KernelSyms.kmem
                 (KernelSyms.kmem + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk4 H]".
    iDestruct (bss_cut g (KernelSyms.kmem + 24) (KernelSyms.kmem + 24)
                 (KernelSyms.kmem + 24 + 8) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hkm H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.kmem + 24)
                 (mword_of_int 0 : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq)
                 ltac:(intros j _; apply nth_byte_zero; zeq) with "Hcl Hkm")
      as "Hkm".
    iDestruct (bss_cut g (KernelSyms.kmem + 24 + 8) KernelSyms.pid_lock
                 (KernelSyms.pid_lock + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk5 H]".
    iDestruct (bss_cut g (KernelSyms.pid_lock + 24) KernelSyms.wait_lock
                 (KernelSyms.wait_lock + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk6 H]".
    (* ---- 0x80012378 cpus[8]: the per-hart cell family ---- *)
    iDestruct (bss_cut g (KernelSyms.wait_lock + 24) KernelSyms.cpus
                 (KernelSyms.cpus + 128 * Z.of_nat NCPU) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hcpus H]".
    iDestruct (boot_stride_family_seq g cpu_slot_raw KernelSyms.cpus 128 NCPU
                 ltac:(lia)
                 ltac:(intros i A Hi HA _ _;
                       destruct (z_stride_side KernelSyms.cpus 128 NCPU 128
                                   img_end ram_hi i A Hi HA
                                   ltac:(lia) ltac:(zlit) ltac:(zlit)
                                   ltac:(zeq) ltac:(zeq)) as (Q1 & Q2 & Q3);
                       iApply (boot_cpu_slot_raw g A Hmem
                                 (z_lo_trans text_end img_end A
                                    ltac:(zlit) Q1) Q1 Q2 Q3))
                 with "Hcl Hcpus") as "Hcpus".
    (* ---- 0x80012778 proc[64] ---- *)
    iDestruct (bss_cut g (KernelSyms.cpus + 128 * Z.of_nat NCPU) KernelSyms.proc
                 (KernelSyms.proc + proc_size * Z.of_nat NPROC) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hprocs H]".
    iDestruct (boot_procs_raw g Hmem with "Hcl Hprocs") as "[Hpr1 Hpr2]".
    (* ---- tickslock, bcache.lock, the 30 buffers, the list sentinel ---- *)
    iDestruct (bss_cut g (KernelSyms.proc + proc_size * Z.of_nat NPROC)
                 KernelSyms.tickslock (KernelSyms.tickslock + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk7 H]".
    iDestruct (bss_cut g (KernelSyms.tickslock + 24) KernelSyms.bcache
                 (KernelSyms.bcache + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk8 H]".
    iDestruct (bss_cut g (KernelSyms.bcache + 24) buf_base
                 (buf_base + buf_stride * Z.of_nat NBUF) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hbufs H]".
    iDestruct (boot_bcache_nodes g Hmem with "Hcl Hbufs") as "[Hbsl Hbln]".
    iDestruct (bss_cut g (buf_base + buf_stride * Z.of_nat NBUF)
                 (buf_base + buf_stride * Z.of_nat NBUF + 72)
                 (buf_base + buf_stride * Z.of_nat NBUF + 88) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hhd H]".
    iDestruct (boot_blink_raw g (buf_base + buf_stride * Z.of_nat NBUF) Hmem
                 ltac:(zlit) ltac:(zlit) ltac:(zeq) with "Hcl Hhd") as "Hhd".
    (* ---- itable.lock, then the 50 ENTRIES: one window, one family, both
           of [main_globals_raw]'s inode conjuncts.  The window is the entry
           ARRAY's ([itable+24], ending exactly at the next symbol), not the
           sleeplock cursor's -- which started 16 bytes later and ran 16
           bytes past the array's end. ---- *)
    iDestruct (bss_cut g (buf_base + buf_stride * Z.of_nat NBUF + 88)
                 KernelSyms.itable (KernelSyms.itable + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk9 H]".
    iDestruct (bss_cut g (KernelSyms.itable + 24) inode_entry_base
                 (inode_entry_base + inode_stride * Z.of_nat NINODE) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hino H]".
    iDestruct (boot_inode_entries g Hmem with "Hcl Hino") as "[Hino Hient]".
    (* ---- devsw[1]'s read/write slots ---- *)
    iDestruct (bss_cut g (inode_entry_base + inode_stride * Z.of_nat NINODE)
                 (KernelSyms.devsw + 16) (KernelSyms.devsw + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdr H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.devsw + 16) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hdr") as (vdr) "Hdr".
    iDestruct (bss_cut g (KernelSyms.devsw + 24) (KernelSyms.devsw + 24)
                 (KernelSyms.devsw + 32) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdw H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.devsw + 24) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hdw") as (vdw) "Hdw".
    (* ---- ftable.lock ---- *)
    iDestruct (bss_cut g (KernelSyms.devsw + 32) KernelSyms.ftable
                 (KernelSyms.ftable + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk10 H]".
    (* ---- the static [struct disk] ---- *)
    iDestruct (bss_cut g (KernelSyms.ftable + 24) KernelSyms.disk
                 (KernelSyms.disk + 8) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdd H]".
    iDestruct (boot_ran_cell8 g KernelSyms.disk Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zeq) with "Hcl Hdd") as (vdd) "Hdd".
    iDestruct (bss_cut g (KernelSyms.disk + 8) (KernelSyms.disk + 8)
                 (KernelSyms.disk + 16) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hda H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.disk + 8) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hda") as (vda) "Hda".
    iDestruct (bss_cut g (KernelSyms.disk + 16) (KernelSyms.disk + 16)
                 (KernelSyms.disk + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdu H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.disk + 16) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hdu") as (vdu) "Hdu".
    iDestruct (bss_cut g (KernelSyms.disk + 24) (KernelSyms.disk + 24)
                 (KernelSyms.disk + 24 + Z.of_nat 8%nat) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdf H]".
    iDestruct (boot_ran_mem_run g (KernelSyms.disk + 24) 8%nat Hmem ltac:(zlit)
                 ltac:(zlit) with "Hcl Hdf") as "Hdf".
    iDestruct (bss_cut g (KernelSyms.disk + 24 + Z.of_nat 8%nat)
                 (KernelSyms.disk + 32) (KernelSyms.disk + 34) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdi H]".
    iDestruct (boot_ran_cell2_bss g (KernelSyms.disk + 32) (wrap16 0%nat) Hmem
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 ltac:(intros j _; apply nth_byte_zero; zeq) with "Hcl Hdi")
      as "Hdi".
    iDestruct (bss_cut g (KernelSyms.disk + 34) (KernelSyms.disk + 40)
                 (KernelSyms.disk + 40 + 16 * Z.of_nat 8%nat) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdinfo H]".
    iDestruct (bss_cut g (KernelSyms.disk + 40 + 16 * Z.of_nat 8%nat)
                 (KernelSyms.disk + 168)
                 (KernelSyms.disk + 168 + 16 * Z.of_nat 8%nat) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hdops H]".
    iDestruct (boot_disk_slots g Hmem with "Hcl Hdinfo Hdops") as "Hslots".
    iDestruct (bss_cut g (KernelSyms.disk + 168 + 16 * Z.of_nat 8%nat)
                 (KernelSyms.disk + 296) (KernelSyms.disk + 296 + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk11 H]".
    (* ---- and kinit's free-page run, to PHYSTOP ---- *)
    iDestruct (bss_cut g (KernelSyms.disk + 296 + 24) 0x80024000 ram_hi ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hrun _]".
    iDestruct (boot_ran_eq g 0x80024000 ram_hi
                 (uint s1entry_val - 4096) (uint phystop_val)
                 ltac:(rewrite s1entry_uint; zeq)
                 ltac:(rewrite phystop_uint; zeq) with "Hrun") as "Hrun".
    iDestruct (boot_kinit_run g phystop_val s1entry_val kinit_pages Hmem
                 ltac:(rewrite s1entry_uint phystop_uint; zeq)
                 ltac:(rewrite s1entry_uint; zlit)
                 ltac:(rewrite s1entry_uint; zlit)
                 ltac:(rewrite s1entry_uint; zeq)
                 ltac:(rewrite phystop_uint; zlit)
                 (* the no-wrap bound is STRICT: [Z.lt] is [(x ?= y) = Lt], so
                    it closes by [reflexivity], not by [discriminate]. *)
                 ltac:(rewrite phystop_uint; zeq)
                 with "Hcl Hrun") as "(%Hprun & %Hplen & Hpages)".
    (* ================================================================ *)
    (* everything is carved; assemble.                                   *)
    (* ================================================================ *)
    iSplitL "Hst"; [iExact "Hst" |].
    iSplitL "Hlk1 Hlk2 Hlk3 Hlk4 Hlk5 Hlk6 Hlk7 Hlk8 Hlk9 Hlk10 Hlk11".
    { iApply (boot_main_locks_raw g Hmem with
                "Hcl Hlk1 Hlk2 Hlk3 Hlk4 Hlk5 Hlk6 Hlk7 Hlk8 Hlk9 Hlk10 Hlk11"). }
    iSplitL "Hdr Hdw Hpkd Hpki Hkm Hkpt Hpr1 Hpr2 Hfd Hir Hip Htk Hbsl Hbln Hhd Hino
             Hient Hdd Hda Hdu Hdf Hdi Hslots".
    { rewrite /main_globals_raw.
      iSplitL "Hdr Hdw".
      { iExists vdr, vdw. rewrite /devsw_console_read /devsw_console_write.
        iFrame "Hdr Hdw". }
      iSplitL "Hpki Hpkd"; [iExists vpki, vpkd; iFrame "Hpki Hpkd" |].
      iSplitL "Hkm"; [iExact "Hkm" |].
      iSplitL "Hkpt"; [iExists vkpt; iExact "Hkpt" |].
      iSplitL "Hpr1"; [iExact "Hpr1" |].
      iSplitL "Hpr2"; [iExact "Hpr2" |].
      iSplitL "Hfd"; [iExact "Hfd" |].
      iSplitL "Hir"; [iExact "Hir" |].
      iSplitL "Hip"; [iExists vip; iExact "Hip" |].
      iSplitL "Htk"; [iExists vtk; rewrite /a_ticks; iExact "Htk" |].
      iSplitL "Hbsl"; [iExact "Hbsl" |].
      iSplitL "Hbln"; [iExact "Hbln" |].
      iSplitL "Hhd"; [rewrite bhead_of_z; iExact "Hhd" |].
      iSplitL "Hino"; [iExact "Hino" |].
      iSplitL "Hient"; [iExact "Hient" |].
      iSplitL "Hdd Hda Hdu".
      { iExists vdd, vda, vdu.
        rewrite disk_desc_of_z disk_avail_of_z disk_used_of_z.
        iFrame "Hdd Hda Hdu". }
      iSplitL "Hdf".
      { iExists (fun j : nat => boot_byte (KernelSyms.disk + 24 + Z.of_nat j)).
        rewrite disk_free_of_z. iExact "Hdf". }
      iSplitL "Hdi"; [rewrite d_used_idx_of_z; iExact "Hdi" |].
      iExact "Hslots". }
    iDestruct (big_sepL_sep with "[Hstk Hcpus]") as "Hharts";
      [iSplitL "Hstk"; [iExact "Hstk" | iExact "Hcpus"] |].
    iAssert ([∗ list] i ∈ seq 0 NCPU,
               (hart_stack_raw (pa_of_z (KernelSyms.stack0 + 4096 * Z.of_nat i)) ∗
                cpu_slot_raw (pa_of_z (cpu_slot i))))%I with "[Hharts]" as "Hharts".
    { iApply (big_sepL_mono with "Hharts"). iIntros (k i _) "[Ha Hb]".
      rewrite /cpu_slot. iFrame "Ha Hb". }
    iDestruct (big_sepL_cpu_of_nat
                 (fun i => hart_stack_raw
                             (pa_of_z (KernelSyms.stack0 + 4096 * Z.of_nat i)) ∗
                           cpu_slot_raw (pa_of_z (cpu_slot i)))%I
                 with "Hharts") as "Hharts".
    iAssert ([∗ list] h ∈ enum CPU, boot_hart_bss h)%I
      with "[Hharts]" as "Hharts".
    { iApply (big_sepL_mono with "Hharts"). iIntros (k h _) "[Ha Hb]".
      iApply (boot_hart_bss_of_raw h with "Ha Hb"). }
    iSplitL "Hharts"; [iExact "Hharts" |].
    iExists (pg_run s1entry_val kinit_pages).
    iSplitR; [iPureIntro; exact Hprun |].
    iSplitR; [iPureIntro; rewrite Hplen; exact kinit_budget |].
    iExact "Hpages".
  Qed.

End BootBssChain.

(* ====================================================================== *)
(* §5  THE SHARED ALLOCATION.                                              *)
(*                                                                        *)
(* [boot_shared_alloc] is M6c's companion to the per-hart chain: ONE fupd   *)
(* that turns [RiscvAdequacy.power_boot_res] into                          *)
(*                                                                        *)
(*   - the SHARED PERSISTENTS both chain arms take: the image              *)
(*     ([kernel_text]/[kernel_data]), [panic_wp_any], the handover channel  *)
(*     [started_inv (main_deposit γd γv Φ)], the device fabric [dev_inv],   *)
(*     the wire invariant, [crash_inv] and [gen_cert];                     *)
(*   - EIGHT per-hart [boot_hart_res] bundles;                             *)
(*   - the BOOT HART's supply, which is everything main's boot arm         *)
(*     consumes.                                                          *)
(*                                                                        *)
(* THREE THINGS ARE FORCED TO HAPPEN HERE RATHER THAN PER HART, and each    *)
(* is a control-flow fact, not a taste:                                    *)
(*   - [WireInv.wire_inv_alloc] wants ALL EIGHT harts' [sig_seip]/         *)
(*     [sig_meip] at once and must run before any hart's WP, so            *)
(*     [BootChain.boot_entry_pre] is called per hart INSIDE this fupd and  *)
(*     the sixteen pins are kept (which is exactly why [boot_hart_res]     *)
(*     excludes them);                                                     *)
(*   - each [cpus[h].proc] cell is split in half, one half into that       *)
(*     hart's [BootBridge.boot_bridge] and the other eight into main       *)
(*     (M6c (2a)); hart 0 could not collect them any later;                *)
(*   - [started_inv] is allocated ONCE, at the CONCRETE payload            *)
(*     [SpecMainSecondary.main_deposit γd γv Φ], because a secondary hart   *)
(*     may reach its first [lw started] before hart 0 has run at all.      *)
(*                                                                        *)
(* [fdslotG] is the one client class that carries a GHOST NAME, so it is    *)
(* allocated here and appears under the existential; the other seven       *)
(* ([lockG]/[kallocG]/[fileG]/[sieG]/[uartGhostG]/[diskGhostG] and the      *)
(* pre-class) are capacity only and are in [Σ] from the start.              *)
(* ====================================================================== *)

Section BootAlloc.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ}.
  (* NO [icacheG] BINDER: [fileG] already carries it, and [IcacheRef.icfg]
     with it (FileInv.v's header -- two instance paths print identically and
     do not unify).  The itable's authority gname is CANONICAL, a field of
     that ambient [icfg], so unlike the fd- and iref-slot supplies there is
     nothing to mint here. *)
  Context `{!fdslotGpreS Σ, !irefslotGpreS Σ,
            !uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  (* The two PER-HART GHOST BUNDLES, NAMED -- and the naming is load-bearing:
     the per-element body of the zipped family below is a four-way conjunction
     whose 2nd and 3rd components are THEMSELVES conjunctions, and [rewrite
     !big_sepL_sep] would split those too, leaving [iFrame] unable to match the
     paired big-op [power_boot_res] actually hands over. *)
  Definition hart_strans (c : CPU) : iProp Σ :=
    (ghost_var (strans_name c) (1/2)%Qp strans_bit_bare ∗
     ghost_var (strans_name c) (1/2)%Qp strans_bit_bare)%I.

  Definition hart_sie (c : CPU) : iProp Σ :=
    (ghost_var (sie_name c) (1/2)%Qp sie_bit_off ∗
     ghost_var (sie_name c) (1/4)%Qp sie_bit_off ∗
     ghost_var (sie_name c) (1/4)%Qp sie_bit_off)%I.

  (* the SPP mirror's two halves, as adequacy mints them.  Its own family
     rather than a conjunct of [hart_sie]: [power_boot_res] hands the two
     out as separate big-ops, and the unpacking below is pure conversion. *)
  Definition hart_spp (c : CPU) : iProp Σ :=
    (ghost_var (spp_name c) (1/2)%Qp sie_bit_off ∗
     ghost_var (spp_name c) (1/2)%Qp sie_bit_off)%I.

  Definition hart_spie (c : CPU) : iProp Σ :=
    (ghost_var (spie_name c) (1/2)%Qp sie_bit_off ∗
     ghost_var (spie_name c) (1/2)%Qp sie_bit_off)%I.

  (* [power_boot_res] is stated in ERA-EXPLICIT ghost forms; every ambient
     form ([reg_pointsto_at], [kmap_auth], [uart_frag], [hart_full], ...) IS
     that form at [riscv_eraGS] BY DELTA (RiscvPtsto §"the era's names"), so
     the unpacking is pure conversion and there is nothing to prove. *)
  Lemma power_boot_res_unpack (g : gstate) (ndisk : nat) :
    power_boot_res riscv_eraGS gen_id boot_D NPROC ndisk g ⊢
      ([∗ list] c ∈ enum CPU, boot_reg_res (CID := c) (g.(gregs) c)) ∗
      boot_raw_bytes g ∗
      kmap_auth kmap_M0 ∗
      ([∗ map] vpn ↦ pc ∈ kmap_M0,
         ghost_map_elem kmap_name vpn (DfracOwn 1) pc) ∗
      kpt_unset ∗
      ([∗ list] c ∈ enum CPU, hart_strans c) ∗
      ([∗ list] c ∈ enum CPU, hart_sie c) ∗
      ([∗ list] c ∈ enum CPU, hart_spp c) ∗
      ([∗ list] c ∈ enum CPU, hart_spie c) ∗
      ([∗ list] j ∈ seq 0 NPROC, hart_full j (0%fin : CPU)) ∗
      ([∗ list] j ∈ seq 0 NPROC, pstate_full j UNUSED) ∗
      uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic)) ∗
      virtio_frag (g.(gdev).(dvirtio)) ∗
      (* the BOOT MINT: this era's whole disk image, in fragments
         (claude-notes/design/fs-log.md, stage 4).  [disk_img_name] is the
         ambient era's image gname -- the one [disk_ghosts_alloc] constructs
         [dn_img] at, so these ARE [disk_bytes γv 0 …] once that record
         exists. *)
      disk_img_bytes disk_img_name 0
        (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk) ∗
      (* the era's LOG-REGION MIRROR variable, whole (phase C2b/D1 stage 3):
         [initlog] splits it, keeping one half in [LogInv.log_batch] and
         handing the other to [FsCrash.P_fs]'s arm at its swap *)
      ghost_var mirror_name 1 (MkLogMirror (0%nat, []) (fun _ => [])) ∗
      crash_inv ∗ gen_cert.
  Proof. iIntros "H". iExact "H". Qed.

  (* ZIPPING THE FOUR PER-HART FAMILIES: DO IT HERE, NOT AT THE USE SITE.
     [big_sepL_sep] is a [⊣⊢], so [rewrite !big_sepL_sep] is a SETOID rewrite
     over the whole [envs_entails Δ Q] -- and although the use site's [iAssert
     ... with "[Hregs Hstrans Hsie Hharts]"] narrows the SPATIAL context to four
     hypotheses, the INTUITIONISTIC one is untouched and at boot it is enormous
     (the claims bundle, [gen_cert], the device invariant, the kernel text).
     That one line measured 12.7 s of BootShared's 27 s -- and BootShared sits
     on the build's critical-path TAIL ([BootChain] -> [BootShared] ->
     [SystemAdequacy] all run at 1x parallelism), so it was wall time, not just
     CPU.  Proved here, with an empty proofmode context, the same rewrite is
     free; the call site becomes one first-order [iApply].  Same family as the
     [wp_next_off] -> [wp_next_off_intro] rule in claude-notes/optimization.md:
     never leave a big-op/KernelSyms.binit identity to a setoid rewrite inside a large goal. *)
  Lemma boot_hart_pre_combine (g : gstate) :
    ([∗ list] c ∈ enum CPU, boot_reg_res (CID := c) (g.(gregs) c)) -∗
    ([∗ list] c ∈ enum CPU, hart_strans c) -∗
    ([∗ list] c ∈ enum CPU, hart_sie c) -∗
    ([∗ list] c ∈ enum CPU, hart_spp c) -∗
    ([∗ list] c ∈ enum CPU, hart_spie c) -∗
    ([∗ list] c ∈ enum CPU, boot_hart_bss c) -∗
    [∗ list] c ∈ enum CPU,
      (boot_reg_res (CID := c) (g.(gregs) c) ∗ hart_strans c ∗ hart_sie c ∗
       hart_spp c ∗ hart_spie c ∗ boot_hart_bss c).
  Proof.
    (* THREE [iApply]s OF THE WAND FORM, NOT [rewrite !big_sepL_sep].
       [big_sepL_sep] is a [⊣⊢], so rewriting with it is SETOID rewriting, and
       its cost scales with the size of the CONCRETE predicates it has to build
       [Proper] proofs over -- here [boot_reg_res] / [hart_sie] / [boot_hart_bss]
       at eight harts.  Measured: the rewrite spelling costs 11.8 s and, unlike
       the usual context-size traps, hoisting it into this empty-context lemma
       does NOT help (11.76 s here vs 12.7 s at the use site) -- the size is in
       the predicates, not the goal around them.  [big_sepL_sep_2] is the wand
       form of the same fact; [iApply] matches it by head and never enters the
       setoid machinery. *)
    iIntros "H1 H2 H3 H4 H5 H6".
    iApply (big_sepL_sep_2 with "H1 [H2 H3 H4 H5 H6]").
    iApply (big_sepL_sep_2 with "H2 [H3 H4 H5 H6]").
    iApply (big_sepL_sep_2 with "H3 [H4 H5 H6]").
    iApply (big_sepL_sep_2 with "H4 [H5 H6]").
    iApply (big_sepL_sep_2 with "H5 H6").
  Qed.

  (* ONE hart's register side, run inside the shared fupd so the two PLIC wire
     pins can be kept back for [wire_inv]. *)
  Lemma boot_hart_pre (h : CPU) (g : gstate) (E : coPset) :
    boot_facts g ->
    kmap_static_claims -∗ gen_cert -∗ (mb_ld_ea ↦ₚ₈□ v_stack0) -∗
    boot_reg_res (CID := h) (g.(gregs) h) -∗
    hart_strans h -∗
    hart_sie h -∗
    hart_spp h -∗
    hart_spie h -∗
    boot_hart_bss h
    ={E}=∗
      (∃ iv : mword 32,
         boot_hart_res (CID := h) (g.(gregs) h) iv DfracDiscarded) ∗
      reg_pointsto_at h sig_seip (DfracOwn 1)
        (register_lookup sig_seip (g.(gregs) h)) ∗
      reg_pointsto_at h sig_meip (DfracOwn 1)
        (register_lookup sig_meip (g.(gregs) h)).
  Proof.
    intro Hbf.
    rewrite /hart_strans /hart_sie /hart_spp /hart_spie /boot_hart_bss.
    iIntros "#Hcl #Hcert #Hword Hregs [Hs1 Hs2] (Hg2 & Hg4a & Hg4b)
             [Hspp1 Hspp2] [Hspie1 Hspie2]
             (Hstk & Hnoff & Hint & Hproc & Hctx)".
    iMod (boot_entry_pre (CID := h) E (g.(gregs) h)
            (boot_regs_of_facts g Hbf h) with "Hcl Hcert Hregs") as
      "(Hmm & Hpmpc & Hpmpa & Hpc & Hfile & Hmh & Hmepc & Hsatp & Hmede & Hmdl &
        Hmie & Hmenv & Hmcen & Hstc & Htlb & Hstvec & Hsepc & Hscause & Hstval &
        Hseip & Hmeip)".
    iModIntro. iFrame "Hseip Hmeip".
    iDestruct "Hint" as (iv) "Hint".
    iExists iv.
    rewrite /boot_hart_res /strans_bit /sie_gname /sret_bits /spp_gname
            /spie_gname /cpu_ctx_free /cid_word.
    iEval (rewrite /own_ctx) in "Hctx".
    iFrame "Hmm Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
            Hmcen Hstc Htlb Hstvec Hsepc Hscause Hstval Hword Hstk
            Hs1 Hs2 Hg2 Hg4a Hg4b Hspp1 Hspie1 Hspp2 Hspie2 Hnoff Hint Hproc
            Hctx".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE COMPANION LEMMA.                                               *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_shared_alloc (g : gstate) (ndisk : nat) :
    boot_facts g ->
    power_boot_res riscv_eraGS gen_id boot_D NPROC ndisk g
    ={⊤}=∗ ∃ (_ : fdslotG Σ) (_ : irefslotG Σ)
             (γd : uart_names) (γv : disk_names),
      ⌜dn_img γv = disk_img_name⌝ ∗
      (* --- the shared persistents --- *)
      kernel_text ∗ kernel_data ∗ panic_wp_any ∗
      started_inv (main_deposit γd γv) ∗
      dev_inv γd γv ∗ wire_inv ∗ crash_inv ∗ gen_cert ∗
      (* --- one bundle per hart --- *)
      ([∗ list] c ∈ enum CPU,
         ∃ iv : mword 32,
           boot_hart_res (CID := c) (g.(gregs) c) iv DfracDiscarded) ∗
      (* --- the BOOT hart's supply --- *)
      main_locks_raw ∗ main_globals_raw ∗
      ([∗ list] i ∈ seq 0 NPROC, hart_full i (0%fin : CPU)) ∗
      ([∗ list] i ∈ seq 0 NPROC, pstate_full i UNUSED) ∗
      (∃ l0 : list (bv 8),
         uart_tx_own γd l0 ∗ uart_sent γd l0 ∗ uart_out_lb γd l0) ∗
      (∃ b0 : bool, uart_dlab_is γd (DfracOwn (1/2)) b0) ∗
      (∃ c0 : virtio_cfg,
         ⌜virtio_live c0 = false⌝ ∗ disk_cfg_is γv (DfracOwn (1/2)) c0) ∗
      ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) ∗
      disk_done_lb γv 0%nat ∗
      kpt_unset ∗ kmap_auth kmap_M0 ∗
      (* THE BOOT MINT, restated at the disk names this lemma just allocated:
         the whole image, in exclusive byte fragments.  Nothing consumes it
         yet -- it is what the FS layer's block views will be carved out of
         (claude-notes/design/fs-log.md, stage 4). *)
      disk_bytes γv 0 (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk) ∗
      (* the era's log-region mirror variable, straight through: the FS boot
         client hands it to [initlog] (its [LogInv.log_mirror_full] premise) *)
      ghost_var mirror_name 1 (MkLogMirror (0%nat, []) (fun _ => [])) ∗
      (∃ ps : list (mword 64),
         ⌜prun phystop_val s1entry_val ps⌝ ∗
         ⌜(K_kvmmake + 64 + 3 < length ps)%nat⌝ ∗
         ([∗ list] p ∈ ps, page_own p)).
  Proof.
    intro Hbf.
    pose proof (boot_ram_of_facts g Hbf) as Hram.
    pose proof (boot_mem_of_facts g Hbf) as Hmem.
    pose proof Hbf as Hbf'.
    destruct Hbf' as (Hpow & Hin & Hmemf & Hregsf & Hu0 & Hp0 & Hv0').
    destruct Hv0' as (v0 & Hv0).
    iIntros "H".
    iDestruct (power_boot_res_unpack g ndisk with "H") as
      "(Hregs & Hbytes & Hkauth & Hkfrags & Hkpt & Hstrans & Hsie & Hspp & Hspie &
        Hpark & Hpst & Huf & Hpf & Hvf & Hdimg & Hmir & #Hcinv & #Hcert)".
    (* ---- the claims bundle FIRST: both image halves need it ---- *)
    iMod (kmap_static_claims_intro with "Hkfrags") as "#Hcl".
    (* ---- the image: text persisted, data persisted up to [img_end] ---- *)
    iDestruct (boot_bytes_split g with "Hbytes") as "[Htext Hdata]".
    iMod (boot_text_persist g Hram with "Hcl Htext") as "Htext".
    iDestruct (kernel_text_intro g Hmemf with "Htext") as "#Hktext".
    iDestruct (boot_data_ran g Hram with "Hdata") as "Hdata".
    iDestruct (bss_cut g text_end text_end img_end ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hdata")
      as "[Himg Hbss]".
    iDestruct (boot_ran_own g text_end img_end Hram ltac:(zlit)
                 with "Hcl Himg") as "Himg".
    iMod (boot_ran_persist g text_end img_end with "Himg") as "#Himg".
    iDestruct (kernel_data_intro g Hmem with "Himg") as "#Hkdata".
    (* ---- [_entry]'s GOT slot: the &stack0 word, at [DfracDiscarded] so all
           eight harts share it ---- *)
    iDestruct (kernel_data_phys_word entry_got v_stack0 mb_ld_ea
                 entry_ld_ea_addr ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 entry_got_bytes with "Hcl Hkdata") as "#Hword".
    (* ---- the fd-slot supply (no memory footprint: a pure ghost) ---- *)
    iMod fd_slots_alloc as (Hfd) "[_ Hfdslots]".
    (* ---- the iref-slot supply, likewise a pure ghost ---- *)
    iMod iref_slots_alloc as (Hir) "[_ Hirslots]".
    (* ### THE FILE TABLE'S NFILE UNITS ARE DROPPED HERE. ###
       [IREFSLOTS = NPROC*(1 + IREFSPARE) + NFILE]; the proc layer's share
       is routed through [main_globals_raw], and the [NFILE] units belong to
       the ftable, one per FD_INODE file's inode reference.  Nothing holds
       them yet because [FileInv.file_payload]'s inode arm is still a
       placeholder, so they go nowhere.  When that arm becomes real, split
       them out here and hand them to [SpecFileinit] the way [fd_slots] are
       handed to procinit.  claude-notes/projects/cwd-ref.md, "STILL TO DO
       -- the consumers". *)
    iEval (rewrite /IREFSLOTS) in "Hirslots".
    iDestruct (iref_slots_split (NPROC * (1 + IREFSPARE)) NFILE with "Hirslots")
      as "[Hirslots _]".
    (* ---- the .bss, in address order ---- *)
    iDestruct (boot_bss_carve g Hbf with "Hcl Hfdslots Hirslots Hbss") as
      "(Hstartcell & Hlocks & Hglobals & Hharts & Hpages)".
    (* ---- the device fabric ---- *)
    iMod (uart_ghosts_alloc (g.(gdev).(duart))) as (γd)
      "(Hacc & Hout & Htxa & Hdla & Htx & Hsent & Hdlab)".
    iDestruct (uart_out_auth_lb γd (g.(gdev).(duart)) with "Hout")
      as "[Hout #Hlb]".
    assert (Hacceq : uart_acc (g.(gdev).(duart)) = u_out (g.(gdev).(duart)))
      by (rewrite Hu0; reflexivity).
    iEval (rewrite -Hacceq) in "Hlb".
    iMod (disk_ghosts_alloc gen_id (g.(gdev).(dvirtio))
            ltac:(rewrite Hv0; apply virtio_reset_not_live)
            ltac:(rewrite Hv0; apply virtio_reset_seen)
            ltac:(rewrite Hv0; apply virtio_reset_used_idx))
      as (γv) "(%Himg & Hproto & Hcfg & Hclaim & #Hdone & Hpbody)".
    iMod (dev_inv_alloc ⊤ γd γv
            with "[Huf Hpf Hvf Hacc Hout Htxa Hdla Hproto] Hpbody")
      as "#Hdev".
    { rewrite /dev_inv_body.
      iExists (g.(gdev).(duart)), (g.(gdev).(dplic)), (g.(gdev).(dvirtio)).
      iFrame "Hacc Hout Htxa Hdla".
      iSplitL "Huf"; [iExact "Huf" |].
      iSplitL "Hpf"; [iExact "Hpf" |].
      iSplitL "Hvf"; [iExact "Hvf" |].
      iSplitL "Hproto"; [iExact "Hproto" |].
      iSplit; [iPureIntro; rewrite Hp0; exact plic_ok_plic0
              | iPureIntro; rewrite Hv0; exact (virtio_isr_ok_reset v0)]. }
    (* ---- the eight harts' register sides, and the sixteen wire pins ---- *)
    iAssert ([∗ list] c ∈ enum CPU,
               (boot_reg_res (CID := c) (g.(gregs) c) ∗
                hart_strans c ∗ hart_sie c ∗ hart_spp c ∗ hart_spie c ∗
                boot_hart_bss c))%I
      with "[Hregs Hstrans Hsie Hspp Hspie Hharts]" as "Hpre".
    { iApply (boot_hart_pre_combine with "Hregs Hstrans Hsie Hspp Hspie Hharts"). }
    iAssert ([∗ list] c ∈ enum CPU, |={⊤}=>
               ((∃ iv : mword 32,
                   boot_hart_res (CID := c) (g.(gregs) c) iv DfracDiscarded) ∗
                reg_pointsto_at c sig_seip (DfracOwn 1)
                  (register_lookup sig_seip (g.(gregs) c)) ∗
                reg_pointsto_at c sig_meip (DfracOwn 1)
                  (register_lookup sig_meip (g.(gregs) c))))%I
      with "[Hpre]" as "Hpre".
    (* [big_sepL_impl], not [big_sepL_mono]: the per-element goal must still see
       the intuitionistic context (the claims bundle, [gen_cert] and the image
       word are all shared), and [_mono]'s goal is a fresh entailment. *)
    { iApply (big_sepL_impl with "Hpre").
      iIntros "!>" (k c _) "(Hr & Hs & Hg & Hsp & Hspe & Hb)".
      iApply (boot_hart_pre c g ⊤ Hbf with "Hcl Hcert Hword Hr Hs Hg Hsp Hspe Hb"). }
    iMod (big_sepL_fupd with "Hpre") as "Hpre".
    iEval (rewrite big_sepL_sep) in "Hpre".
    iDestruct "Hpre" as "[Hres Hpins]".
    iMod (wire_inv_alloc ⊤ (fun c => register_lookup sig_seip (g.(gregs) c))
            (fun c => register_lookup sig_meip (g.(gregs) c)) with "[Hpins]")
      as "#Hwinv".
    { iApply RiscvAdequacy.big_sepL_enum_to_set. iExact "Hpins". }
    (* ---- the handover channel, at the settled payload ---- *)
    iMod (started_inv_alloc ⊤ (main_deposit γd γv) with "Hstartcell")
      as "#Hstarted".
    (* ================================================================ *)
    iModIntro. iExists Hfd, Hir, γd, γv.
    iSplitR; [iPureIntro; exact Himg |].
    iSplitR; [iExact "Hktext" |].
    iSplitR; [iExact "Hkdata" |].
    iSplitR; [iApply panic_wp_any_holds |].
    iSplitR; [iExact "Hstarted" |].
    iSplitR; [iExact "Hdev" |].
    iSplitR; [iExact "Hwinv" |].
    iSplitR; [iExact "Hcinv" |].
    iSplitR; [iExact "Hcert" |].
    iSplitL "Hres"; [iExact "Hres" |].
    iSplitL "Hlocks"; [iExact "Hlocks" |].
    iSplitL "Hglobals"; [iExact "Hglobals" |].
    iSplitL "Hpark"; [iExact "Hpark" |].
    iSplitL "Hpst"; [iExact "Hpst" |].
    iSplitL "Htx Hsent".
    { iExists (uart_acc (g.(gdev).(duart))). iFrame "Htx Hsent Hlb". }
    iSplitL "Hdlab"; [iExists (uart_dlab (g.(gdev).(duart))); iExact "Hdlab" |].
    iSplitL "Hcfg".
    { iExists (v_cfg (g.(gdev).(dvirtio))).
      iSplitR; [iPureIntro; rewrite Hv0; apply virtio_reset_not_live |].
      iExact "Hcfg". }
    iSplitL "Hclaim"; [iExact "Hclaim" |].
    iSplitR; [iExact "Hdone" |].
    iSplitL "Hkpt"; [iExact "Hkpt" |].
    iSplitL "Hkauth"; [iExact "Hkauth" |].
    (* the boot mint, re-spelled at [γv]: [disk_bytes γv] IS
       [disk_img_bytes (dn_img γv)], and [Himg] says that gname is the era's *)
    iSplitL "Hdimg".
    { rewrite /disk_bytes. iEval (rewrite -Himg) in "Hdimg". iExact "Hdimg". }
    iSplitL "Hmir"; [iExact "Hmir" |].
    iExact "Hpages".
  Qed.

End BootAlloc.
