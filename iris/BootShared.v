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
Require Import RiscvModelBytes.  (* [nth_byte], for [first_bytes] below *)
Require Import RiscvLang RiscvPtsto.
(* durable-disk 2b-A / B3: the two file-system-state capacity classes
   ([fsLinkG]/[fsTopG]) this file's [Context] binds, so that their instance
   fields are ACTIVE here.  Required EARLY on purpose: [FsState] exports four
   names that collide with live ones ([fs_view], [link_auth], [byte_range],
   [blk_owned]), and the later imports are what shadow them again. *)
Require Import HartTp.
Require Import KMap KptPt KptGhost.
Require Import StackOwn.
Require Import KernelText KernelDataInv.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom SwtchCtx SchedCtx.
Require Import KallocInv FdSlots.
Require Import LockSet.
Require Import FileInvDefs.
Require Import VirtioProto VirtioModel VirtioQueue DiskPtsto.
Require Import PlicPlan WpUart WireInv.
Require Import SpecConsoleinit SpecIinit.
Require Import SpecFreerange KvmSpec BcacheInv.
Require Import StartedInv.
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
Require Import TicksInv.
Require Import WaitInv.        (* [wait_res_of_cells] -- the parent cells, gathered *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* THE FILE SYSTEM'S BOOT-ERA MINT (claude-notes/projects/fs-cfg-boot.md
   stage (d2b)).  [FsCfgBoot.fs_cfg_alloc] is what finally gives
   [IcacheRef.icfg] and [FsCfg.fscfg] VALUES, and it has to run here: the
   two records reach every proof as superclass fields of
   [FileInvDefs.fileG], so they must exist before the first hart's WP, and
   this file's fupd is the only thing that runs earlier.  The disk mint it
   consumes is [power_boot_res]'s own ([power_boot_res_unpack]'s [Hdimg]),
   which this lemma used to hand back untouched and its one caller dropped
   on the floor. *)
Require Import Xv6Cameras.        (* the mirror's camera: kit-2's row (B) *)
Require Import LogDefs.           (* [log_mirror_born]: kit-2's row (B) *)
Require Import BioDefs.        (* [fs_blocks] *)
Require Import FsBoot.         (* [fs_cov_in] *)
Require Import FsImg.          (* the image sweeps' vocabulary *)
Require Import FsCfgBoot.      (* [fs_cfg_alloc] and the two boot kits *)
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
   sixteen-way fact set every consumer above asks for by name.  This is that
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
Proof. lia. Qed.

Lemma z_stk_base (A : Z) : A = A + 4096 - 8 * Z.of_nat boot_stack_depth.
Proof. lia. Qed.

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
  (* NO [fileG] BINDER: nothing in this file's carve mentions the file table
     or either configuration record, and after stage (d2b) the only [fileG]
     in the file is the one [boot_shared_alloc] BUILDS (see §5). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            !irefslotG Σ}.
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
   exactly one page past PHYSTOP.  [PageGeom.kmem_lo] IS the dumped `end`
   symbol (computed from [KernelSyms.end_] into a [Z] literal at its own
   definition), so [s1entry_uint] below tracks the image instead of a
   transcription of it. *)
Definition s1entry_val : mword 64 :=
  add_vec (and_vec (add_vec (mword_of_int kmem_lo : mword 64)
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
  unfold kinit_pages. vm_compute. reflexivity.
Qed.

Section BootBssChain.
  (* NO [fileG] BINDER -- see [BootBss]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            !irefslotG Σ}.
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
    (* ...and the OPEN-FILE TABLE'S share: one whole unit per free slot.  A
       free slot's payload is untyped and an untyped payload IS its iref unit
       ([FileInvDefs.file_core_none]); sys_open spends it retyping to
       FD_INODE and fileclose puts it back.  These are the [NFILE] units
       [IrefSlots.IREFSLOTS] is sized for, and they used to be dropped at the
       mint below because nothing could hold them: the table's entries were
       not carved. *)
    iref_slots NFILE -∗
    (* ...and the fd-slot AUTHORITY, which [FileInv.ftable_res] holds because
       the table is where the one-unit-per-reference conservation law is
       checked.  Minted once, at the fan-out below, and dropped there before
       the table had a producer. *)
    fd_slots_auth -∗
    (* ...and the bio supply's PROC-LAYER SHARE, three units per process.
       Unlike the two above this is a genuine slice: [3 * NPROC = 192] of
       [BioDefs.BSLOTS = 1024], the remainder staying with the file system.
       procinit routes it so a DORMANT slot owns three -- see
       [ProcDefs.proc_dormant]'s note for the ledger it opens. *)
    bslots (NPROC * 3) -∗
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
    iIntros "#Hcl Hfd Hir Hirf Hfda Hbss H".
    (* THE FLAG CELLS ARE GONE.  This chain used to open with two 4-byte cuts
       for [panicked] and [panicking]; upstream d80e61c5 deleted both globals
       from printk.c, so there is no such symbol and nothing to carve.  .bss
       now BEGINS at [tx_chan] ([img_end] is exactly its address), and
       [tx_chan] is itself not carved: only its ADDRESS is used, as the sleep
       channel -- the cell is never read or written and belongs to nobody
       (UartTxInv.v).  So the first thing the walk takes is [started], four
       bytes above it, and the leading gap is that one word.
       ---- started: PINNED zero, the escrow's left disjunct ---- *)
    iDestruct (bss_cut g img_end KernelSyms.started
                 (KernelSyms.started + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hst H]".
    iDestruct (boot_ran_cell4_bss g KernelSyms.started started_clear Hmem
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 ltac:(intros j _; apply nth_byte_zero; zeq)
                 with "Hcl Hst") as "Hst".
    (* ---- 0x8000a238 kernel_pagetable, 0x8000a260 initproc ---- *)
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
    (* ---- 0x8000a270 stack0[8][4096]: the per-hart stack family ---- *)
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
    (* the console RING, immediately after cons.lock's own 24 bytes: the
       128 input bytes and the three index words, i.e. [ConsoleInv.cons_res].
       Four bytes of padding separate its end from [pr]. *)
    iDestruct (bss_cut g (KernelSyms.cons + 24) (KernelSyms.cons + 24)
                 (KernelSyms.cons + 164) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hring H]".
    iDestruct (boot_cons_res g Hmem ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 with "Hcl Hring") as "Hring".
    iDestruct (bss_cut g (KernelSyms.cons + 164) KernelSyms.pr
                 (KernelSyms.pr + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk2 H]".
    (* tx_lock's window is 24 bytes like the rest: it is a [struct spinlock],
       and [boot_main_locks_raw] discharges it with [boot_lk_raw].  The
       linker left exactly 24 bytes between [pr] and [kmem]'s neighbour, so
       the cut is tight on both sides -- [main_lock_windows] is that check. *)
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
    (* ---- 0x80012368 cpus[8]: the per-hart cell family ---- *)
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
    (* ---- 0x80012768 proc[64] ---- *)
    iDestruct (bss_cut g (KernelSyms.cpus + 128 * Z.of_nat NCPU) KernelSyms.proc
                 (KernelSyms.proc + proc_size * Z.of_nat NPROC) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hprocs H]".
    iDestruct (boot_procs_raw g Hmem with "Hcl Hprocs")
      as "[Hpr1 [Hpr2 Hpar]]".
    (* the parent cells, gathered into wait_lock's resource.  The carve hands
       one existential per slot; [WaitInv.wait_res] is one list. *)
    iDestruct (WaitInv.wait_res_of_cells with "Hpar") as "Hwres".
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
    iDestruct (boot_bcache_nodes g Hmem with "Hcl Hbufs")
      as "[Hbsl [Hbln Hbpay]]".
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
    (* ---- ROWS (A), part 1: the 32 bytes of the static [struct
           superblock].  &sb sits in the .bss gap between the buffer cache
           and the itable and was DROPPED by this walk before stage (f);
           it is what fsinit's [memmove] kills.  Contents-existential, as
           the [disk_free] run above is. ---- *)
    iDestruct (bss_cut g (buf_base + buf_stride * Z.of_nat NBUF + 88)
                 KernelSyms.sb (KernelSyms.sb + Z.of_nat 32%nat) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hsbb H]".
    iDestruct (boot_ran_mem_run g KernelSyms.sb 32%nat Hmem ltac:(zlit)
                 ltac:(zlit) with "Hcl Hsbb") as "Hsbb".
    iDestruct (bss_cut g (KernelSyms.sb + Z.of_nat 32%nat)
                 KernelSyms.itable (KernelSyms.itable + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk9 H]".
    iDestruct (bss_cut g (KernelSyms.itable + 24) inode_entry_base
                 (inode_entry_base + inode_stride * Z.of_nat NINODE) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hino H]".
    iDestruct (boot_inode_entries g Hmem with "Hcl Hino") as "[Hino Hient]".
    (* ---- ROWS (A), part 2: the whole static [struct log], likewise a
           dropped gap before stage (f).  It sits BETWEEN the itable entries
           and &devsw -- [KernelSyms.log + 168] IS [KernelSyms.devsw]
           (0x80022388 + 0xa8 = 0x80022430) -- so the devsw walk below now
           starts from the log's end rather than from the inode array's. ---- *)
    iDestruct (bss_cut g (inode_entry_base + inode_stride * Z.of_nat NINODE)
                 KernelSyms.log (KernelSyms.log + 168) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlog H]".
    iDestruct (boot_log_raw g Hmem with "Hcl Hlog") as "Hlog".
    (* ---- devsw[0 .. NDEV): THE WHOLE TABLE, not just CONSOLE's entry.
       consoleinit is about to overwrite entry CONSOLE's two cells, so those
       come out at arbitrary values; the other eighteen are handed over ZERO,
       via [boot_ran_cell8_bss].  That is what [ConsoleInv.devsw_rest] states,
       and it is what lets [ConsoleInv.devsw_table] say what each slot HOLDS
       rather than "null or consoleread" -- the BSS being zero is a fact the
       carve has, so there is no reason to weaken the table to a disjunction
       and make every reader case-split. ---- *)
    iDestruct (bss_cut g (KernelSyms.log + 168)
                 (KernelSyms.devsw + 0) (KernelSyms.devsw + 8) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd0r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 0)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd0r")
      as "Hd0r".
    iDestruct (bss_cut g (KernelSyms.devsw + 8)
                 (KernelSyms.devsw + 8) (KernelSyms.devsw + 16) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd0w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 8)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd0w")
      as "Hd0w".
    iDestruct (bss_cut g (KernelSyms.devsw + 16)
                 (KernelSyms.devsw + 16) (KernelSyms.devsw + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd1r H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.devsw + 16) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hd1r") as (vdr) "Hdr".
    iDestruct (bss_cut g (KernelSyms.devsw + 24)
                 (KernelSyms.devsw + 24) (KernelSyms.devsw + 32) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd1w H]".
    iDestruct (boot_ran_cell8 g (KernelSyms.devsw + 24) Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hd1w") as (vdw) "Hdw".
    iDestruct (bss_cut g (KernelSyms.devsw + 32)
                 (KernelSyms.devsw + 32) (KernelSyms.devsw + 40) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd2r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 32)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd2r")
      as "Hd2r".
    iDestruct (bss_cut g (KernelSyms.devsw + 40)
                 (KernelSyms.devsw + 40) (KernelSyms.devsw + 48) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd2w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 40)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd2w")
      as "Hd2w".
    iDestruct (bss_cut g (KernelSyms.devsw + 48)
                 (KernelSyms.devsw + 48) (KernelSyms.devsw + 56) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd3r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 48)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd3r")
      as "Hd3r".
    iDestruct (bss_cut g (KernelSyms.devsw + 56)
                 (KernelSyms.devsw + 56) (KernelSyms.devsw + 64) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd3w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 56)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd3w")
      as "Hd3w".
    iDestruct (bss_cut g (KernelSyms.devsw + 64)
                 (KernelSyms.devsw + 64) (KernelSyms.devsw + 72) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd4r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 64)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd4r")
      as "Hd4r".
    iDestruct (bss_cut g (KernelSyms.devsw + 72)
                 (KernelSyms.devsw + 72) (KernelSyms.devsw + 80) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd4w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 72)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd4w")
      as "Hd4w".
    iDestruct (bss_cut g (KernelSyms.devsw + 80)
                 (KernelSyms.devsw + 80) (KernelSyms.devsw + 88) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd5r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 80)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd5r")
      as "Hd5r".
    iDestruct (bss_cut g (KernelSyms.devsw + 88)
                 (KernelSyms.devsw + 88) (KernelSyms.devsw + 96) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd5w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 88)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd5w")
      as "Hd5w".
    iDestruct (bss_cut g (KernelSyms.devsw + 96)
                 (KernelSyms.devsw + 96) (KernelSyms.devsw + 104) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd6r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 96)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd6r")
      as "Hd6r".
    iDestruct (bss_cut g (KernelSyms.devsw + 104)
                 (KernelSyms.devsw + 104) (KernelSyms.devsw + 112) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd6w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 104)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd6w")
      as "Hd6w".
    iDestruct (bss_cut g (KernelSyms.devsw + 112)
                 (KernelSyms.devsw + 112) (KernelSyms.devsw + 120) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd7r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 112)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd7r")
      as "Hd7r".
    iDestruct (bss_cut g (KernelSyms.devsw + 120)
                 (KernelSyms.devsw + 120) (KernelSyms.devsw + 128) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd7w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 120)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd7w")
      as "Hd7w".
    iDestruct (bss_cut g (KernelSyms.devsw + 128)
                 (KernelSyms.devsw + 128) (KernelSyms.devsw + 136) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd8r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 128)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd8r")
      as "Hd8r".
    iDestruct (bss_cut g (KernelSyms.devsw + 136)
                 (KernelSyms.devsw + 136) (KernelSyms.devsw + 144) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd8w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 136)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd8w")
      as "Hd8w".
    iDestruct (bss_cut g (KernelSyms.devsw + 144)
                 (KernelSyms.devsw + 144) (KernelSyms.devsw + 152) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd9r H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 144)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd9r")
      as "Hd9r".
    iDestruct (bss_cut g (KernelSyms.devsw + 152)
                 (KernelSyms.devsw + 152) (KernelSyms.devsw + 160) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hd9w H]".
    iDestruct (boot_ran_cell8_bss g (KernelSyms.devsw + 152)
                 (zero_reg : mword 64) Hmem ltac:(zlit) ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) nth_byte_zero8 with "Hcl Hd9w")
      as "Hd9w".
    (* the eighteen, as the [big_sepL] [ConsoleInv.devsw_rest] is.  The
       reduction lives in ConsoleInv.v; this file only applies the lemma. *)
    iDestruct (ConsoleInv.devsw_rest_intro with "Hd0r Hd0w Hd2r Hd2w Hd3r Hd3w Hd4r Hd4w Hd5r Hd5w Hd6r Hd6w Hd7r Hd7w Hd8r Hd8w Hd9r Hd9w") as "Hdevrest".
    (* ---- ftable.lock ---- *)
    iDestruct (bss_cut g (KernelSyms.devsw + 160) KernelSyms.ftable
                 (KernelSyms.ftable + 24) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hlk10 H]".
    (* ---- the ftable's HUNDRED ENTRIES.  The array starts just past the
           table's own spinlock and ends EXACTLY at the next symbol (<disk>),
           so this cut consumes the whole gap that used to be dropped between
           [ftable+24] and <disk> -- 4000 bytes, and with them every hope of
           ever building [FileInv.ftable_res].  See
           [BootCarveMain.boot_file_entries]. ---- *)
    iDestruct (bss_cut g (KernelSyms.ftable + 24) file_base
                 (file_base + file_stride * Z.of_nat NFILE) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "H") as "[Hfent H]".
    iDestruct (boot_file_entries g Hmem with "Hcl Hfent") as "Hfent".
    (* ---- the static [struct disk] ---- *)
    iDestruct (bss_cut g (file_base + file_stride * Z.of_nat NFILE)
                 KernelSyms.disk (KernelSyms.disk + 8) ram_hi
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
    (* ---- and kinit's free-page run, to PHYSTOP ----
       [0x80024000] here is PGROUNDUP(end) = [uint s1entry_val - 4096], NOT a
       transcription of the `end` symbol: it is a page BOUNDARY, so it only
       moves when [KernelSyms.end_] crosses one.  It is kept a literal because
       [bss_cut]'s ordering side conditions are closed by [zlit] on literals,
       and it is self-checking -- [s1entry_uint] (which now computes from the
       dumped symbol) and the [boot_ran_eq] equation just below both fail to
       compile if [end] ever lands in a different page. *)
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
    iSplitL "Hdr Hdw Hdevrest Hkm Hkpt Hpr1 Hpr2 Hwres Hfd Hir Hfent Hirf Hfda
             Hbss Hip Htk Hbsl Hbln Hhd
             Hbpay Hsbb Hino Hient Hlog Hdd Hda Hdu Hdf Hdi Hslots Hring".
    { rewrite /main_globals_raw.
      iSplitL "Hdr Hdw".
      { iExists vdr, vdw. rewrite /devsw_console_read /devsw_console_write.
        iFrame "Hdr Hdw". }
      iSplitL "Hdevrest"; [iExact "Hdevrest" |].
      iSplitL "Hkm"; [iExact "Hkm" |].
      iSplitL "Hkpt"; [iExists vkpt; iExact "Hkpt" |].
      iSplitL "Hpr1"; [iExact "Hpr1" |].
      iSplitL "Hpr2"; [iExact "Hpr2" |].
      iSplitL "Hwres"; [iExact "Hwres" |].
      iSplitL "Hfd"; [iExact "Hfd" |].
      iSplitL "Hir"; [iExact "Hir" |].
      iSplitL "Hfent"; [iExact "Hfent" |].
      iSplitL "Hirf"; [iExact "Hirf" |].
      iSplitL "Hfda"; [iExact "Hfda" |].
      iSplitL "Hbss"; [iExact "Hbss" |].
      iSplitL "Hip"; [iExists vip; iExact "Hip" |].
      iSplitL "Htk"; [iExists vtk; rewrite /a_ticks; iExact "Htk" |].
      iSplitL "Hbsl"; [iExact "Hbsl" |].
      iSplitL "Hbln"; [iExact "Hbln" |].
      iSplitL "Hhd"; [rewrite bhead_of_z; iExact "Hhd" |].
      iSplitL "Hbpay"; [iExact "Hbpay" |].
      iSplitL "Hsbb".
      { rewrite /main_sb_raw.
        iExists (fun j : nat => boot_byte (KernelSyms.sb + Z.of_nat j)).
        iExact "Hsbb". }
      iSplitL "Hino"; [iExact "Hino" |].
      iSplitL "Hient"; [iExact "Hient" |].
      iSplitL "Hlog"; [iExact "Hlog" |].
      iSplitL "Hdd Hda Hdu".
      { iExists vdd, vda, vdu.
        rewrite disk_desc_of_z disk_avail_of_z disk_used_of_z.
        iFrame "Hdd Hda Hdu". }
      iSplitL "Hdf".
      { iExists (fun j : nat => boot_byte (KernelSyms.disk + 24 + Z.of_nat j)).
        rewrite disk_free_of_z. iExact "Hdf". }
      iSplitL "Hdi"; [rewrite d_used_idx_of_z; iExact "Hdi" |].
      iSplitL "Hslots"; [iExact "Hslots" |].
      iExact "Hring". }
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
(*     ([kernel_text]/[kernel_data]), the handover channel               *)
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
(* FIVE CLIENT CLASSES CARRY PER-BOOT VALUES, so all five are allocated    *)
(* here and appear under the existential: [fdslotG], [irefslotG] and        *)
(* [bioslotG] carry a ghost name, [pavG] carries one, and [fileG] carries   *)
(* the file table's                                                         *)
(* camera TOGETHER WITH the two configuration records                       *)
(* ([IcacheRef.icfg], [FsCfg.fscfg]) -- which is why it could not be a      *)
(* functor constraint either (fs-cfg-boot.md stage 3/(d2b)).  Everything    *)
(* else the boot needs is capacity only and is in [Σ] from the start.       *)
(* ====================================================================== *)

(* the reverse of [RiscvAdequacy.big_sepL_enum_to_set]: [power_boot_res]
   hands the reservation mirrors out over the SET (that is the spelling the
   era interpretation uses), while every per-hart family here is over the
   LIST, so the zip needs them in list form. *)
Local Lemma big_sepS_enum_to_list {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ set] c ∈ (fin_to_set CPU : gset CPU), Φ c) ⊢ [∗ list] c ∈ enum CPU, Φ c.
Proof.
  rewrite /fin_to_set big_sepS_list_to_set; [done | apply NoDup_enum].
Qed.

(* THE WRITABLE INITIALIZED GLOBALS -- the part of the image in
   [rodata_end, img_end) that anything will want to name.  These two cells
   are the reason [KernelDataInv.kernel_data] stops at [rodata_end]: xv6
   STORES to both (`first = 0` in forkret, `nextpid = nextpid + 1` in
   allocpid), so neither can ever be part of a persistent image bundle --
   see that file's header and durable-notes.md.

   Contents-EXISTENTIAL, like every other cell the boot carve hands out (the
   loader leaves 1 in each, but no client has read one yet).  Nothing
   consumes this bundle today; it is here so that narrowing [kernel_data]
   does not drop the bytes on the floor, and it is what [SpecForkret]'s
   `first` premise and [SpecAllocpid.nextpid_res] get threaded from when
   those land ([main_globals_raw] is where they will end up). *)
(* THE IMAGE'S TWO WRITABLE INITIALIZED GLOBALS.

   [first] IS AT A PINNED VALUE and [nextpid] is not, and the asymmetry is
   the point.  Nobody reasons about [nextpid]'s initial contents -- it is
   spent immediately on [SpecAllocpid.nextpid_res], whose own shape is
   [∃ v, alp_nextpid ↦₄ v].  [first] is different: forkret's [if (first)]
   branch is decided by that cell, so a holder of [∃ w, first ↦₄ w] cannot
   tell which arm it is in and the boot arm becomes unprovable.  The image
   says 1 ([KernelData], via [boot_ran_cell4_at]), and pinning it here is
   what lets the FIRST process carry the right to run that arm. *)
(* [first]'s FOUR IMAGE BYTES, as a named lemma.  It is named for the reason
   [BootChain.entry_got_bytes] is: the discharge is a [vm_compute] over an
   image map, and inlining one into a proof context normalises
   [boot_byte] -- the filtered union of BOTH image maps -- rather than a
   single lookup.  Named, it is paid once.

   [vm_compute; reflexivity] does not close these on its own: the two sides
   are [Some <the same bv literal>] with DIFFERENT [BvWf] proofs and print
   identically (durable-notes' [bv_eq] trap, one [option] layer up). *)
Lemma first_bytes (j : nat) :
  (j < 4)%nat ->
  KernelData.kernel_data !! (KernelSyms.first_1 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 1 : mword 32) j).
Proof.
  intro Hj.
  destruct j as [|[|[|[|j']]]]; [.. | cbn in Hj; lia];
    vm_compute; apply (f_equal Some), bv_eq; reflexivity.
Qed.

Definition main_data_raw `{!riscvGS Σ} : iProp Σ :=
  ((pa_of_z KernelSyms.first_1) ↦₄ (mword_of_int 1 : mword 32) ∗
   (∃ w : bv 32, (pa_of_z KernelSyms.nextpid)  ↦₄ w))%I.

(* [fs_boot_image_wf] MOVED DOWN to [FsCfgBoot.v] (fs-cfg-boot.md (f-2)),
   for the reason [fs_boot_supply] did: [SpecMain] takes it as a pure
   premise now -- [ProofMain] is what turns it into [FsReady.fs_geom_ok] and
   [FirstTok.first_fsinit_pures] -- and [SpecMain] sits BELOW this file.
   The body is unchanged; this file still names it, unqualified. *)

(* ---------------------------------------------------------------------- *)
(* THE FILE SYSTEM'S BOOT-ERA OUTPUT is [FsCfgBoot.fs_boot_supply].        *)
(*                                                                        *)
(* It USED to be defined here.  Stage (e) threads it through [SpecMain] -> *)
(* [BootChain] into [ProofMain.mn_grp_fs], and both of those files sit     *)
(* BELOW this one, so the definition moved down to [FsCfgBoot.v] (which    *)
(* this file already imports) where all three can name it.  Its body is    *)
(* unchanged and still byte-identical to [fs_cfg_alloc]'s conclusion, so   *)
(* the wiring below is still one [iExact].                                 *)
(* ---------------------------------------------------------------------- *)

Section BootAlloc.
  Context `{!riscvGS Σ, !xv6G Σ}.
  (* NO [icacheG] AND NO [fileG] BINDER.  [fileG] carries the two
     configuration records, and NOTHING in this file can be stated at them
     before they exist -- so the class is not assumed here, it is BUILT:
     [FsCfgBoot.fs_cfg_alloc] mints an [icfg] and an [fscfg] inside the fupd
     below and [FileInvDefs.fileG_of] reassembles the class at [FGP]'s
     camera, exactly as [fdslotG]/[irefslotG]/[pavG] are minted and returned
     existentially.  The itable's authority gname is a field of that minted
     [icfg], so there is nothing separate to mint for it.
     THE INSTANCE IS BUILT EXPLICITLY, never resolved: a site that asks
     resolution for a [fileG Σ] with no closed [icfg]/[fscfg] in scope walks
     [subG_fileΣ -> fscfg -> file_fscfg -> fileG] forever (measured at
     400 GB resident, no error and no progress -- the hazard the deleted
     [SystemAdequacy.adequacy_fscfg] existed to block).  [fileGpreS] has no
     such cycle: its only instance is [subG] on the functor list. *)
  Context `{FGP : fileGpreS Σ}.
  Context `{!fdslotGpreS Σ, !irefslotGpreS Σ, !pavGpreS Σ, !bioslotGpreS Σ}.
  (* durable-disk 2b-A / B3: [FsCfgBoot.fs_cfg_alloc] allocates the era's
     link family and top map.  Both capacity classes are [Xv6G.xv6G]
     MEMBERS since 2b-inode-3 / 2b-inode-4, so this file -- above the
     bundle -- binds neither. *)
  Context `{GEN : GenId}.

  (* The two PER-HART GHOST BUNDLES, NAMED -- and the naming is load-bearing:
     the per-element body of the zipped family below is a four-way conjunction
     whose 2nd and 3rd components are THEMSELVES conjunctions, and [rewrite
     !big_sepL_sep] would split those too, leaving [iFrame] unable to match the
     paired big-op [power_boot_res] actually hands over. *)
  Definition hart_strans (c : CPU) : iProp Σ :=
    (strans_pending_at (strans_name c) ∗
     strans_pending_at (strans_name c))%I.

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

  (* this hart's HELD-LOCK AUTHORITY at the empty set (LockSet.v), as
     adequacy mints it -- its own family for the same reason [hart_spp] is
     one: [power_boot_res] hands it out as a separate big-op. *)
  Definition hart_locks (c : CPU) : iProp Σ :=
    lk_auth c ∅.

  (* this hart's RESERVATION MIRROR at [None], as adequacy mints it: a hart
     that has executed nothing holds no reservation.  It goes into that
     hart's [InstrBytes.pc_is] via [BootChain.boot_entry_pre]
     (claude-notes/projects/main-cycle-port.md §3a), which is why it is a
     per-hart family here rather than an output of this file. *)
  Definition hart_resv (c : CPU) : iProp Σ :=
    resv_frag c None.

  (* [power_boot_res] is stated in ERA-EXPLICIT ghost forms; every ambient
     form ([reg_pointsto_at], [kmap_auth], [uart_frag], [hart_full], ...) IS
     that form at [riscv_eraGS] BY DELTA (RiscvPtsto §"the era's names"), so
     the unpacking is pure conversion and there is nothing to prove. *)
  Lemma power_boot_res_unpack (g : gstate) (ndisk : nat) :
    power_boot_res riscv_eraGS gen_id boot_D NPROC ndisk
      (fun dk => FsCrash.mirror_of (FsCrash.fs_blocks dk)) g ⊢
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
      ([∗ list] c ∈ enum CPU, hart_locks c) ∗
      ([∗ list] j ∈ seq 0 NPROC, hart_full j (0%fin : CPU)) ∗
      ([∗ list] j ∈ seq 0 NPROC, pstate_full j UNUSED) ∗
      (* every hart's reservation mirror at [None] (design §3a) *)
      ([∗ set] c ∈ (fin_to_set CPU : gset CPU), resv_frag c None) ∗
      uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic)) ∗
      virtio_frag (g.(gdev).(dvirtio)) ∗
      (* the BOOT MINT: this era's whole disk image, in fragments
         (claude-notes/design/fs-log.md, stage 4).  [disk_img_name] is the
         ambient era's image gname -- the one [disk_ghosts_alloc] constructs
         [dn_img] at, so these ARE [disk_bytes γv 0 …] once that record
         exists. *)
      disk_img_bytes disk_img_name 0
        (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk) ∗
      (* the era's LOG-REGION MIRROR, BORN TRUE AND IN CUSTODY
         (durable-disk 1a): PowerOn allocated the variable at the picture of
         the disk this era boots on and handed the OTHER half to
         [FsCrash.P_fs]'s custody arm in the same fupd, so what comes out
         here is the era's half at a NAMED picture plus the swap receipt.
         SPELLED as two rows, not as [LogDefs.log_mirror_born]: this lemma
         is pure conversion, and the bundle would re-associate the pair
         against [power_boot_res]'s own right-nested chain. *)
      log_mirror_half (FsCrash.mirror_of
         (FsCrash.fs_blocks (v_disk (g.(gdev).(dvirtio))))) ∗
      swap_lb (S gen_id) ∗
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
    ([∗ list] c ∈ enum CPU, hart_locks c) -∗
    ([∗ list] c ∈ enum CPU, hart_resv c) -∗
    ([∗ list] c ∈ enum CPU, boot_hart_bss c) -∗
    [∗ list] c ∈ enum CPU,
      (boot_reg_res (CID := c) (g.(gregs) c) ∗ hart_strans c ∗ hart_sie c ∗
       hart_spp c ∗ hart_spie c ∗ hart_locks c ∗ hart_resv c ∗
       boot_hart_bss c).
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
    iIntros "H1 H2 H3 H4 H5 H6 H7 H8".
    iApply (big_sepL_sep_2 with "H1 [H2 H3 H4 H5 H6 H7 H8]").
    iApply (big_sepL_sep_2 with "H2 [H3 H4 H5 H6 H7 H8]").
    iApply (big_sepL_sep_2 with "H3 [H4 H5 H6 H7 H8]").
    iApply (big_sepL_sep_2 with "H4 [H5 H6 H7 H8]").
    iApply (big_sepL_sep_2 with "H5 [H6 H7 H8]").
    iApply (big_sepL_sep_2 with "H6 [H7 H8]").
    iApply (big_sepL_sep_2 with "H7 H8").
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
    hart_locks h -∗
    hart_resv h -∗
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
    rewrite /hart_strans /hart_sie /hart_spp /hart_spie /hart_locks
            /hart_resv /boot_hart_bss.
    iIntros "#Hcl #Hcert #Hword Hregs [Hs1 Hs2] (Hg2 & Hg4a & Hg4b)
             [Hspp1 Hspp2] [Hspie1 Hspie2] Hlks Hresv
             (Hstk & Hnoff & Hint & Hproc & Hctx)".
    iMod (boot_entry_pre (CID := h) E (g.(gregs) h)
            (boot_regs_of_facts g Hbf h) with "Hcl Hcert Hresv Hregs") as
      "(Hmm & Hpmpc & Hpmpa & Hpc & Hfile & Hmh & Hmepc & Hsatp & Hmede & Hmdl &
        Hmie & Hmenv & Hmcen & Hstc & Htlb & Hstvec & Hsepc & Hscause & Hstval &
        Hssc & Hmse & Hsse & Hseip & Hmeip)".
    iModIntro. iFrame "Hseip Hmeip".
    iDestruct "Hint" as (iv) "Hint".
    iExists iv.
    rewrite /boot_hart_res /strans_pending /sie_gname /sret_bits /spp_gname
            /spie_gname /cpu_ctx_free /cid_word.
    iEval (rewrite /own_ctx) in "Hctx".
    iFrame "Hmm Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
            Hmcen Hstc Htlb Hstvec Hsepc Hscause Hstval Hssc Hmse Hsse
            Hword Hstk
            Hs1 Hs2 Hg2 Hg4a Hg4b Hspp1 Hspie1 Hspp2 Hspie2 Hnoff Hint Hproc
            Hlks Hctx".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE COMPANION LEMMA.                                               *)
  (* ------------------------------------------------------------------ *)
  Lemma boot_shared_alloc (g : gstate) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    boot_facts g ->
    (* THE ERA'S DISK IS THE FILE SYSTEM'S (fs-cfg-boot.md (d2b)).  It is a
       hypothesis about THIS era's disk image, and it has to be: the mint
       [power_boot_res] hands over is at [v_disk (g.(gdev).(dvirtio))], and
       nothing in [boot_facts] says what those bytes are. *)
    fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) ndisk sb nib cov ->
    power_boot_res riscv_eraGS gen_id boot_D NPROC ndisk
      (fun dk => FsCrash.mirror_of (FsCrash.fs_blocks dk)) g
    ={⊤}=∗ ∃ (HFd : fdslotG Σ) (HIr : irefslotG Σ) (HPav : pavG Σ)
             (HBs : bioslotG Σ)
             (HF : fileG Σ) (γd : uart_names) (γv : disk_names),
      ⌜dn_img γv = disk_img_name⌝ ∗
      (* --- the shared persistents --- *)
      kernel_text ∗ kernel_data ∗
      started_inv (main_deposit γd γv) ∗
      dev_inv γd γv ∗ wire_inv ∗ crash_inv ∗ gen_cert ∗
      (* --- one bundle per hart --- *)
      ([∗ list] c ∈ enum CPU,
         ∃ iv : mword 32,
           boot_hart_res (CID := c) (g.(gregs) c) iv DfracDiscarded) ∗
      (* --- the BOOT hart's supply --- *)
      main_locks_raw ∗ main_globals_raw ∗
      (* the image's WRITABLE initialized globals, which [kernel_data] no
         longer claims -- see [main_data_raw] *)
      main_data_raw ∗
      ([∗ list] i ∈ seq 0 NPROC, hart_full i (0%fin : CPU)) ∗
      ([∗ list] i ∈ seq 0 NPROC, pstate_full i UNUSED) ∗
      (* THE PROC TABLE'S COUNTED REGIME, at the whole table: every slot is
         UNUSED at boot, so allocproc cannot come back empty and a caller
         that does not test its result -- userinit -- can be proved
         ([ProcAvail.v], and [SpecUserinit.v]'s contract, which takes
         [procs_avail (Some (S k))] and hands back [Some k]).  Threaded to
         [main] through [BootChain.boot_hart_primary]; main carries it to
         the userinit call site. *)
      procs_avail (Some NPROC) ∗
      (* NO RESERVATION MIRRORS COME OUT: every hart's is threaded into that
         hart's [InstrBytes.pc_is] here, inside [boot_hart_pre] (design
         §3a), so the boot client never names one. *)
      (∃ l0 : list (bv 8),
         uart_tx_own γd l0 ∗ uart_sent γd l0 ∗ uart_out_lb γd l0) ∗
      (∃ b0 : bool, uart_dlab_is γd (DfracOwn (1/2)) b0) ∗
      (∃ c0 : virtio_cfg,
         ⌜virtio_live c0 = false⌝ ∗ disk_cfg_is γv (DfracOwn (1/2)) c0) ∗
      ([∗ map] i ↦ st ∈ gset_to_gmap HInactive (set_seq 0 8 : gset nat),
         i ↪[dn_head γv] st) ∗
      ghost_map_auth (dn_claim γv) 1 (∅ : gmap nat dclaim) ∗
      disk_done_lb γv 0%nat ∗
      kpt_unset ∗ kmap_auth kmap_M0 ∗
      (* THE BOOT MINT IS GONE FROM THIS INTERFACE, and that is stage (d2b):
         [disk_bytes γv 0 (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk)]
         used to leave here and be dropped by the one caller.  It is now
         SPENT below, by [FsCfgBoot.fs_cfg_alloc], which is what turns those
         bytes into the file system's block ghosts (fs-log.md stage 4). *)
      (* the era's log-region mirror, straight through: it is kit 2's
         row (B) -- [FsCfgBoot.fs_kit_fsinit_ghost]'s header says so and
         says why the era fupd must NOT try to mint it -- and since
         durable-disk 1a it is VALUE-BEARING all the way to [initlog]: the
         era's half at the picture of its own disk, plus the swap receipt
         its custody-at-birth earned. *)
      log_mirror_born (FsCrash.mirror_of
         (FsCrash.fs_blocks (v_disk (g.(gdev).(dvirtio))))) ∗
      (∃ ps : list (mword 64),
         ⌜prun phystop_val s1entry_val ps⌝ ∗
         ⌜(K_kvmmake + 64 + 3 < length ps)%nat⌝ ∗
         ([∗ list] p ∈ ps, page_own p)) ∗
      (* ---- THE FILE SYSTEM'S BOOT-ERA MINT (stage (d2b)) ---- *)
      (* row (P4) of [fs_kit_icache]'s header: the iref-slot AUTHORITY, which
         [IcacheBoot.icache_boot_at] takes and which only [iref_slots_alloc]
         -- run here, beside the [irefslotG] instance it returns -- can
         produce.  It used to be dropped on the floor at that call. *)
      iref_slots_auth ∗
      (* ...and TWO iref-slot UNITS, row (C) of [FirstTok.first_fsinit]:
         fsinit's ireclaim borrows ONE for its iget/iput pair and hands it
         back, and [SpecKexec] -- which forkret's [if (first)] arm reaches
         next, on the same token -- takes [iref_slots 2].  Both are split
         off the file table's [NFILE] share, which nothing holds yet. *)
      iref_slots 2 ∗
      (* the ten config ties and the two boot kits, AT THE INSTANCE the
         chain arms above are applied at.  Stage (e) is the consumer:
         kit 1 in [ProofMain.mn_grp_fs], kit 2 through [SpecUserinit] to
         forkret's first arm. *)
      fs_boot_supply (@file_icfg Σ HF) (@file_fscfg Σ HF)
        (v_disk (g.(gdev).(dvirtio))) sb nib cov γd γv.
  Proof.
    intros Hbf Himg.
    destruct Himg as (Hwf & Hrw & Hnin & Hnib32 & Hnib0 & Hnibeq &
                      Hcovin & Hcovmeta & Hcovdata & Hparse & Hush & Hnd & Hleq &
                      Hbare & Hnoself).
    pose proof (boot_ram_of_facts g Hbf) as Hram.
    pose proof (boot_mem_of_facts g Hbf) as Hmem.
    pose proof Hbf as Hbf'.
    destruct Hbf' as (Hpow & Hin & Hmemf & Hregsf & Hu0 & Hp0 & Hv0' & _).
    destruct Hv0' as (v0 & Hv0).
    iIntros "H".
    iDestruct (power_boot_res_unpack g ndisk with "H") as
      "(Hregs & Hbytes & Hkauth & Hkfrags & Hkpt & Hstrans & Hsie & Hspp & Hspie &
        Hlkauth & Hpark & Hpst & Hresv & Huf & Hpf & Hvf & Hdimg & Hmir & #Hswlb &
        #Hcinv & #Hcert)".
    (* ---- the claims bundle FIRST: both image halves need it ---- *)
    iMod (kmap_static_claims_intro with "Hkfrags") as "#Hcl".
    (* ---- the image: text persisted, data persisted up to [rodata_end] ---- *)
    iDestruct (boot_bytes_split g with "Hbytes") as "[Htext Hdata]".
    iMod (boot_text_persist g Hram with "Hcl Htext") as "Htext".
    iDestruct (kernel_text_intro g Hmemf with "Htext") as "#Hktext".
    iDestruct (boot_data_ran g Hram with "Hdata") as "Hdata".
    (* THE SECOND CUT IS AT [rodata_end], NOT AT [img_end].  [rodata_end,
       img_end) is the image's WRITABLE initialized data (`.data`, `.got`,
       `.got.plt`), and the kernel stores into `.data`; persisting it would
       make [kernel_data] contradict any ownership of `first`/`nextpid` and
       so make every contract carrying it vacuous.  Only the read-only
       material [text_end, rodata_end) becomes [kernel_data]. *)
    iDestruct (bss_cut g text_end text_end rodata_end ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hdata")
      as "[Hro Hrw]".
    iDestruct (boot_ran_own g text_end rodata_end Hram ltac:(zlit)
                 with "Hcl Hro") as "Hro".
    iMod (boot_ran_persist g text_end rodata_end with "Hro") as "#Hro".
    iDestruct (kernel_data_intro g Hmem with "Hro") as "#Hkdata".
    (* ---- [rodata_end, ram_hi), walked in ADDRESS order exactly like the
           .bss walk below: `first`, `nextpid`, [_entry]'s GOT slot, and the
           .bss tail.  The gaps (`.data`'s leading and trailing padding, the
           rest of `.got`/`.got.plt`) are claimed by nobody and dropped, as
           everywhere else in this walk. ---- *)
    iDestruct (bss_cut g rodata_end KernelSyms.first_1
                 (KernelSyms.first_1 + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hrw")
      as "[Hfirst Hrw]".
    iDestruct (bss_cut g (KernelSyms.first_1 + 4) KernelSyms.nextpid
                 (KernelSyms.nextpid + 4) ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hrw")
      as "[Hnext Hrw]".
    iDestruct (bss_cut g (KernelSyms.nextpid + 4) entry_got (entry_got + 8)
                 ram_hi ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hrw")
      as "[Hgot Hrw]".
    iDestruct (bss_cut g (entry_got + 8) img_end ram_hi ram_hi
                 ltac:(zlit) ltac:(zlit) ltac:(zlit) with "Hrw") as "[Hbss _]".
    (* pinned, not existential -- see [main_data_raw]'s note.  The byte
       premise goes through [first_bytes], a NAMED lemma: proving it inline
       makes [vm_compute] normalise [boot_byte], i.e. the filtered union of
       both 17932-entry image maps, inside this proof's context -- which is
       not slow but non-terminating in practice. *)
    iDestruct (boot_ran_cell4_at g KernelSyms.first_1 (mword_of_int 1)
                 Hmem ltac:(zlit) ltac:(zlit) ltac:(zeq)
                 (boot_byte_data_run KernelSyms.first_1
                    (mword_of_int 1 : mword 32) 4%nat ltac:(zlit) first_bytes)
                 with "Hcl Hfirst") as "Hfirst".
    iDestruct (boot_ran_cell4 g KernelSyms.nextpid Hmem ltac:(zlit)
                 ltac:(zlit) ltac:(zeq) with "Hcl Hnext") as "Hnext".
    (* ---- [_entry]'s GOT slot: the &stack0 word, at [DfracDiscarded] so all
           eight harts share it.  It is in `.got`, i.e. ABOVE [rodata_end],
           so it is persisted here as ONE cell rather than claimed wholesale
           by [kernel_data] -- nothing ever writes the GOT (xv6 is statically
           linked and non-PIE), but the section flags cannot say so. ---- *)
    iMod (boot_ran_phys_word g entry_got v_stack0 mb_ld_ea entry_ld_ea_addr
            Hmem ltac:(zlit) ltac:(zlit) ltac:(zeq)
            (boot_byte_data_run entry_got v_stack0 8%nat ltac:(zlit)
               entry_got_bytes) with "Hcl Hgot") as "#Hword".
    (* ---- the fd-slot supply (no memory footprint: a pure ghost) ---- *)
    (* the proc table's COUNTED regime, at the whole table: every slot is
       UNUSED at boot, so [userinit]'s allocproc cannot come back empty
       ([ProcAvail.v]).  Minted here, with the ghost name handed out
       existentially, for [InodeRef.iref_name_alloc]'s reason: a class that
       carries a gname cannot be a functor constraint adequacy assumes. *)
    iMod procs_avail_alloc as (Hpav) "Hprocsavail".
    (* THE AUTHORITY IS KEPT NOW.  [FileInv.ftable_res] holds it -- the
       table is where the one-unit-per-reference conservation law is checked
       -- and nothing else in the tree can make it. *)
    iMod fd_slots_alloc as (Hfd) "[Hfdauth Hfdslots]".
    (* ---- the iref-slot supply, likewise a pure ghost.  THE AUTHORITY IS
           KEPT NOW: [icache_boot_at] takes it (row (P4) of
           [FsCfgBoot.fs_kit_icache]'s header) and nothing else can make
           it. ---- *)
    iMod iref_slots_alloc as (Hir) "[Hirauth Hirslots]".
    (* ---- and the BIO slot supply, on the same footing.  Its ghost name is
           canonical ([Xv6Cameras.bioslot_name]), so it is minted HERE with
           the other name-carrying classes rather than inside [bio_init]:
           the name has to exist before the bcache invariant that owns the
           authority does.  [FsCfgBoot.fs_cfg_alloc] takes both halves and
           parks them in [BioInitAt.bio_free_tok]. ---- *)
    iMod bslots_alloc as (Hbs) "(Hbsauth & Hbsproc & Hbslots)".
    (* THE SUPPLY, IN ITS THREE SHARES, AND NOTHING IS DROPPED ANY MORE.
       [IREFSLOTS = NPROC*(1 + IREFSPARE) + NFILE + IREFBOOT]: the proc
       layer's share and the FILE TABLE'S both go through
       [main_globals_raw], the table's one unit per free slot; the boot
       chain's own [IREFBOOT] are row (C) of [FirstTok.first_fsinit]
       ([SpecFsinit] takes one for ireclaim's iget/iput pair and hands it
       back -- fs-cfg-boot.md (f-2) -- and [SpecKexec], which forkret's boot
       arm calls next off the same token, takes two).

       Those last two are their OWN row and not a slice of the table's:
       neither is handed back to the ftable, so carving them out of [NFILE]
       would leave the table unable to start with all [NFILE] slots free.
       See [IrefSlots.IREFBOOT]. *)
    iEval (rewrite /IREFSLOTS) in "Hirslots".
    iDestruct (iref_slots_split (NPROC * (1 + IREFSPARE) + NFILE) IREFBOOT
                 with "Hirslots") as "[Hirslots Hirslot]".
    iDestruct (iref_slots_split (NPROC * (1 + IREFSPARE)) NFILE with "Hirslots")
      as "[Hirslots Hirfile]".
    iEval (rewrite /IREFBOOT) in "Hirslot".
    (* ---- the .bss, in address order ---- *)
    iDestruct (boot_bss_carve g Hbf
                 with "Hcl Hfdslots Hirslots Hirfile Hfdauth Hbsproc Hbss") as
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
            ltac:(rewrite Hv0; apply virtio_reset_used_idx)
            ltac:(rewrite Hv0; apply virtio_reset_cache)
            ltac:(rewrite Hv0; apply virtio_reset_taken)
            ltac:(rewrite Hv0; apply virtio_reset_inflight)
            ltac:(rewrite Hv0; apply virtio_reset_wce))
      as (γv) "(%Himg & Hproto & Hcfg & Hcmauth & #Hdone & Hheads & Hpbody)".
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
    (* ================================================================ *)
    (* ---- THE FILE SYSTEM'S BOOT-ERA MINT (fs-cfg-boot.md (d2b)) ---- *)
    (* It runs HERE, after the device ghosts: [fs_cfg_alloc] REUSES [γd] and
       [γv] as [fsc_uart]/[fsc_disk] rather than re-minting them (its step
       1), so it cannot run before [uart_ghosts_alloc]/[disk_ghosts_alloc];
       and it must run before the harts' WPs exist, which is everything
       below.  The boot mint is the only resource it takes. *)
    iAssert (disk_bytes γv 0
               (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk))
      with "[Hdimg]" as "Hdimg".
    { (* [disk_bytes γv] IS [disk_img_bytes (dn_img γv)], and [Himg] says
         that gname is the era's -- the same one-line restatement this
         lemma's postcondition used to do at its very end *)
      rewrite /disk_bytes. iEval (rewrite -Himg) in "Hdimg". iExact "Hdimg". }
    (* durable-disk lane E-unpin: [fs_cfg_alloc]'s post is the ten ties and
       the two kits, nothing else.  It used to lead with root's dview pin
       and /init's fview pin (N-5.1 W5a / N-5.2A), which this proof received
       and immediately dropped; those era-0 image-CONTENT facts are off the
       boot chain now, so there is no pin to drop and no mask premise to
       thread (the mask was [dv_lend_mint]'s).  See
       claude-notes/projects/namei-pinned-lookup.md's banner. *)
    iMod (fs_cfg_alloc γd γv (v_disk (g.(gdev).(dvirtio))) ndisk sb cov nib ⊤
            Hwf Hrw Hbare Hnin Hnib32 Hnib0 Hnibeq Hcovin Hcovmeta Hcovdata
            with "Hdimg Hbsauth Hbslots") as (ICFG FSC) "Hfs".
    (* durable-disk 2b-inode-3 / 2b-inode-4: NEITHER ERA GHOST ARRIVES HERE
       ANY MORE.  The top map's authority is [InodeRegion.ftop_inv] (carried
       by [ireg_inv]) and its per-inum fragments are the free pool's; the
       LINK family's per-inum authorities and their token piles are the
       inode REGION's ([InodeRegion.ireg_lnk]).  Both are routed inside
       [fs_cfg_alloc], so nothing is dropped here. *)
    (* [fileG_of]'s two projections ARE the two minted records, by iota.
       Named, so the postcondition's row needs no conversion step inside the
       proofmode. *)
    assert (Hpi : @file_icfg Σ (fileG_of FGP ICFG FSC) = ICFG)
      by reflexivity.
    assert (Hpf : @file_fscfg Σ (fileG_of FGP ICFG FSC) = FSC)
      by reflexivity.
    (* ================================================================ *)
    (* ---- the eight harts' register sides, and the sixteen wire pins ---- *)
    iDestruct (big_sepS_enum_to_list hart_resv with "Hresv") as "Hresv".
    iAssert ([∗ list] c ∈ enum CPU,
               (boot_reg_res (CID := c) (g.(gregs) c) ∗
                hart_strans c ∗ hart_sie c ∗ hart_spp c ∗ hart_spie c ∗
                hart_locks c ∗ hart_resv c ∗ boot_hart_bss c))%I
      with "[Hregs Hstrans Hsie Hspp Hspie Hlkauth Hresv Hharts]" as "Hpre".
    { iApply (boot_hart_pre_combine with
                "Hregs Hstrans Hsie Hspp Hspie Hlkauth Hresv Hharts"). }
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
      iIntros "!>" (k c _) "(Hr & Hs & Hg & Hsp & Hspe & Hlk & Hrv & Hb)".
      iApply (boot_hart_pre c g ⊤ Hbf with
                "Hcl Hcert Hword Hr Hs Hg Hsp Hspe Hlk Hrv Hb"). }
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
    (* [Hprocsavail] -- [procs_avail (Some NPROC)] -- now leaves in the
       postcondition: userinit is proven and its contract
       ([SpecUserinit.v]) takes exactly this. *)
    iModIntro. iExists Hfd, Hir, Hpav, Hbs, (fileG_of FGP ICFG FSC), γd, γv.
    iSplitR; [iPureIntro; exact Himg |].
    iSplitR; [iExact "Hktext" |].
    iSplitR; [iExact "Hkdata" |].
    iSplitR; [iExact "Hstarted" |].
    iSplitR; [iExact "Hdev" |].
    iSplitR; [iExact "Hwinv" |].
    iSplitR; [iExact "Hcinv" |].
    iSplitR; [iExact "Hcert" |].
    iSplitL "Hres"; [iExact "Hres" |].
    iSplitL "Hlocks"; [iExact "Hlocks" |].
    iSplitL "Hglobals"; [iExact "Hglobals" |].
    iSplitL "Hfirst Hnext"; [rewrite /main_data_raw; iFrame "Hfirst Hnext" |].
    iSplitL "Hpark"; [iExact "Hpark" |].
    iSplitL "Hpst"; [iExact "Hpst" |].
    iSplitL "Hprocsavail"; [iExact "Hprocsavail" |].
    iSplitL "Htx Hsent".
    { iExists (uart_acc (g.(gdev).(duart))). iFrame "Htx Hsent Hlb". }
    iSplitL "Hdlab"; [iExists (uart_dlab (g.(gdev).(duart))); iExact "Hdlab" |].
    iSplitL "Hcfg".
    { iExists (v_cfg (g.(gdev).(dvirtio))).
      iSplitR; [iPureIntro; rewrite Hv0; apply virtio_reset_not_live |].
      iExact "Hcfg". }
    iSplitL "Hheads"; [iExact "Hheads" |].
    iSplitL "Hcmauth"; [iExact "Hcmauth" |].
    iSplitR; [iExact "Hdone" |].
    iSplitL "Hkpt"; [iExact "Hkpt" |].
    iSplitL "Hkauth"; [iExact "Hkauth" |].
    iSplitL "Hmir".
    { rewrite /log_mirror_born.
      iSplitL "Hmir"; [iExact "Hmir" | iExact "Hswlb"]. }
    iSplitL "Hpages"; [iExact "Hpages" |].
    iSplitL "Hirauth"; [iExact "Hirauth" |].
    iSplitL "Hirslot"; [iExact "Hirslot" |].
    (* the ten ties and the two kits, restated at [fileG_of]'s projections *)
    rewrite /fs_boot_supply Hpi Hpf. iExact "Hfs".
  Qed.

End BootAlloc.
