(* RiscvFetchExec.v -- exec-level fetch reduction + the conditioned Hne engine. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import list_monad bitvector.definitions.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Require Import KMap.   (* kmap_static_claims, carried in hw_config *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(* The PMP configuration used throughout the boot WPs: every PMP entry is  *)
(* UNLOCKED (L = 0).  In M-mode this grants every access that fits in one   *)
(* aligned 4-byte grain cell (all instruction fetches: 4-byte at 4-aligned  *)
(* pc, 2-byte at 2-aligned pc), INDEPENDENT of the entries' A-fields and    *)
(* of the pmpaddr register values: a matching entry with L = 0 allows an    *)
(* M-mode access outright, and with no matching entry M-mode defaults to    *)
(* allow.  (The cell-fit proviso rules out PARTIAL matches, which fault     *)
(* even in M-mode; see exec_pmpCheck_machine_unlocked in RiscvTryStep.v.)   *)
(* Unlike the previous "every A-field is OFF" definition, this survives     *)
(* xv6's `csrw pmpcfg0` with a5=0xf, which legalizes entry 0 to             *)
(* A=TOR/RWX=111/L=0 and entries 1..7 to 0x00 -- all unlocked (see          *)
(* pmp_allows_all_written in WpGprCsrwC.v).                                 *)
(* ====================================================================== *)
Definition pmp_allows_all (cfg : type_of_register pmpcfg_n) : Prop :=
  forall i, pmpLocked (vec_access_dec cfg i) = false.

(* ====================================================================== *)
(* The stronger, pre-pmpcfg0-write PMP configuration -- every entry OFF     *)
(* (disabled) AND unlocked -- is [RiscvLang.pmp_all_off], and it lives      *)
(* THERE because [RiscvLang.reset_regs] states the reset machine's PMP      *)
(* obligation as that predicate rather than as a pinned register value.     *)
(* Read its comment for why the 8-byte data-access WPs need it and the      *)
(* unlocked-ness above does not suffice.  All that is left here is the      *)
(* projection to the weaker predicate.                                      *)
(* ====================================================================== *)
Lemma pmp_all_off_allows_all (cfg : type_of_register pmpcfg_n) :
  pmp_all_off cfg -> pmp_allows_all cfg.
Proof. intros H i. exact (proj2 (H i)). Qed.

(* ====================================================================== *)
(* THE PLATFORM'S PMA TABLE, AS THE TOWER CONSUMES IT: what the table must   *)
(* grant, PER ADDRESS CLASS.                                                *)
(*                                                                          *)
(* [pma_allows_all] used to be one obligation quantified over ALL addresses  *)
(* -- "some region matches and grants R/W/X, atomics and PTE access" -- and  *)
(* that is not a property any real table has: the platform's own table       *)
(* ([RiscvLang.pma_boot], the model's, tied to it by                        *)
(* [ColdBoot.cold_boot_pma]) has a boot ROM window, an MMIO band, the DRAM   *)
(* bank, and HOLES between them.  So the obligation is split along the two   *)
(* classes of address the kernel actually accesses, with the attributes each *)
(* class's towers consume and no more:                                       *)
(*                                                                          *)
(*   [pma_allows_ram] -- kernel RAM (instruction fetch, every data access,   *)
(*      page-table slots, the lock word).  Needs R, W, X, every AMO the      *)
(*      decoder can produce and both PTE permissions: this is the class the  *)
(*      whole M-/S-/U-mode memory tower is stated over.                     *)
(*   [pma_allows_io] -- the device band (UART / PLIC / virtio-mmio).  Needs   *)
(*      R and W only.  The band is NOT executable and supports NEITHER       *)
(*      atomics NOR PTE access, and asking for those here would make the     *)
(*      obligation unsatisfiable -- which is exactly the point of splitting: *)
(*      the device leaves never needed them (each takes [PMA_readable] /     *)
(*      [PMA_writable] of an ABSTRACT matched region and nothing else).      *)
(*                                                                          *)
(* [pma_allows_all] IS STILL ONE PROPOSITION -- the class is an INDEX it     *)
(* quantifies over, not a conjunction -- so [hw_config] and the ~130 WPs that *)
(* merely thread the premise are textually unchanged, and an applier projects *)
(* the class it is in with [pma_all_ram] / [pma_all_io].  THE ∀ IS DELIBERATE: *)
(* a conjunction would be taken apart by the [repeat split; assumption] that   *)
(* every bundle-preservation proof over a config record ends with             *)
(* ([UserMemClassify.cfg_okR_pres] and friends), leaving two goals that the    *)
(* bundled hypothesis no longer matches -- for a fact nothing there is about.  *)
(*                                                                          *)
(* THE ADDRESS PREMISES ([RiscvExtras.pma_ram_access] / [pma_io_access])     *)
(* carry the model's own side conditions on a [matching_pma_region] lookup:  *)
(* the width proviso [1 <= n <= 4096] from the Sail source, and the two      *)
(* bounds [range_subset] tests -- base at or above the region's base, END    *)
(* at or below the region's end.  Both are load-bearing: without the width   *)
(* bound and without the END bound the predicate holds of NO table (an       *)
(* access whose byte range wraps the space, or runs off the top of DRAM,     *)
(* matches nothing), and every spec taking it as a premise would be          *)
(* vacuously satisfiable.                                                    *)
(* ====================================================================== *)

Inductive pma_class : Set := PmaRam | PmaIo.

Definition pma_class_access (c : pma_class) (a : mword 64) (n : Z) : Prop :=
  match c with
  | PmaRam => pma_ram_access a n
  | PmaIo  => pma_io_access a n
  end.

(* WHAT THE TABLE MUST GRANT, per class.  ONE home for the two attribute
   lists: the class predicates below are this, at a constructor. *)
Definition pma_class_grants (c : pma_class) (r : PMA_Region) : Prop :=
  match c with
  | PmaRam =>
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_executable) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_readable) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_writable) = true /\
      (* THE ATOMIC CONJUNCT, STATED AS WHAT THE TOWER CONSUMES rather than as
         a support LEVEL.  Every AMO the decoder can produce is an [amoop] at
         one of the widths [1;2;4;8;16] ([word_width_wide]), so this is the
         whole of what any AMO leaf ever needs -- the M-/S-mode leaves take
         [pma_allows_atomic_op … AMOSWAP 4 = true] and the U-mode classifier
         needs it at the op and width it was handed.  It is a [∀], not a pinned
         level, because a pinned level is a platform detail that then leaks
         into every consumer: pinning [= AMOSwap] is exactly what made the
         U-mode classifier CONCLUDE A FAULT for a user-mode [amoadd], which is
         false of the machine (the model's DRAM carries [AMOCASQ], where every
         op at every width up to 16 is permitted).  The width premise is a
         [Z.leb] so a literal-width call site discharges it with [eq_refl]. *)
      (forall (op : amoop) (n : Z), Z.leb n 16 = true ->
         pma_allows_atomic_op
           (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_atomic_support) op n
         = true) /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_read) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_write) = true /\
      (* THE MISALIGNED CONJUNCT.  A misaligned plain load/store is NOT a fault
         on this platform: the region's own [PMAMisalignedExceptions_load_store]
         is [None], so [mag_pma_check] always answers a PLAN (one operation if
         the access fits in the region's Misaligned Atomicity Granule, a split
         otherwise) rather than an exception.  Without it a misaligned user load
         would have to be classified as an access fault, which is false of the
         machine -- and the whole misaligned pipeline in UserMemClassify rests on
         this one field.  Nothing here pins the GRANULE: the split derivation
         handles either answer, so the granule stays a platform detail. *)
      ((override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None /\
      (* THE RESERVABILITY CONJUNCT.  DRAM supports LR/SC on this platform
         ([RsrvEventual]), and this is the field [pmaCheck]'s LoadReserved /
         StoreConditional / (via [mem_write_ea]) atomic arms gate on.  Without
         it an SC to an owned RAM page would have to be classified as an access
         fault, which is false of the machine -- and, worse, the [vmem_write_addr]
         reservation-HIT path runs [mem_write_ea] BEFORE [mem_write_value], so a
         composer that cannot rule the denial out cannot even state the write.
         Stated as the [generic_neq … RsrvNone] the model itself computes, so a
         call site rewrites with it rather than case-splitting. *)
      generic_neq (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_reservability)
        RsrvNone = true
  | PmaIo =>
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_readable) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_writable) = true
  end.

Definition pma_allows_class (c : pma_class) (regions : list PMA_Region) : Prop :=
  forall (a : mword 64) (n : Z),
    pma_class_access c a n ->
    exists r,
      matching_pma_region regions (Physaddr a) n = Some r /\ pma_class_grants c r.

Definition pma_allows_ram (regions : list PMA_Region) : Prop :=
  pma_allows_class PmaRam regions.
Definition pma_allows_io (regions : list PMA_Region) : Prop :=
  pma_allows_class PmaIo regions.

Definition pma_allows_all (regions : list PMA_Region) : Prop :=
  forall c : pma_class, pma_allows_class c regions.

Lemma pma_all_ram {regions : list PMA_Region} :
  pma_allows_all regions -> pma_allows_ram regions.
Proof. exact (fun H => H PmaRam). Qed.

Lemma pma_all_io {regions : list PMA_Region} :
  pma_allows_all regions -> pma_allows_io regions.
Proof. exact (fun H => H PmaIo). Qed.

Lemma pma_allows_all_intro {regions : list PMA_Region} :
  pma_allows_ram regions -> pma_allows_io regions -> pma_allows_all regions.
Proof. intros Hr Hi c. destruct c; [exact Hr | exact Hi]. Qed.

(* the boot table serves 8-byte PTE reads AT A RAM ADDRESS -- a direct
   projection now that [pma_allows_ram] pins [PMA_supports_pte_read].  The
   RAM restriction is the honest one: a page table outside DRAM would not
   support a PTE read on this platform, and [PtTree.pt_slot_mem] (what every
   applier holds of a slot) carries exactly the two [addr_is_ram] facts the
   class needs. *)
Lemma pma_allows_all_pte_read (pmar0 : list PMA_Region) :
  pma_allows_all pmar0 -> KptPt.pma_allows_pte_read pmar0.
Proof.
  intros H a Hram.
  destruct (pma_all_ram H a 8 Hram) as (r & Hm & _ & _ & _ & _ & Hpr & _).
  exists r. split; [exact Hm | exact Hpr].
Qed.

(* ====================================================================== *)
(* hw_config: the immutable hardware configuration the boot relies on,      *)
(* bundled into ONE *persistent* proposition.  These registers are never    *)
(* written by the boot, so they are owned PERSISTENTLY ([↦ᵣ□]): a WP that   *)
(* only READS them takes [hw_config] in its precondition and -- because it   *)
(* is [Persistent] -- need neither thread a fresh copy nor RETURN it in its  *)
(* continuation.  This replaces, on every WP, the cluster of per-register    *)
(* points-to facts (misa / mseccfg / mcountinhibit / minstretcfg /          *)
(* pma_regions / htif_tohost_base) AND the [pma_allows_all] / [_get_Misa_S]  *)
(* side-conditions with a single hypothesis.                                 *)
(*   NB the *mutable* config (pmpcfg_n, mstatus, mie, elp, pmpaddr, ...) is  *)
(*   NOT here: those genuinely change during boot and stay linearly threaded.*)
(* ====================================================================== *)

(* Concrete reference config values for the decode bridge (WpDecodeBridge).
   [MISA_C] is the platform misa (S/C/U/M/A/I/D/F set, MXL=2); read-only, never
   written by the kernel.
   NOT A HAND-PICKED CONSTANT: it is what the model's own [reset_misa] writes,
   one bit per [hartSupports] answer, and [ColdBoot.cold_boot_misa] is the
   compiled proof of that -- so this literal cannot drift from the model without
   breaking the build.  It reads as it does because B and V are DISABLED in
   model-xv6iris/sail-config-rv64d.json (the config's header says why): the
   kernel is rv64gc and contains no B or V instruction, and with them enabled
   [DecodeSetU.decodable_u] would stop being the complete U-mode decode image.
   [MENVCFG_S] is the S-mode menvcfg AFTER the two M-mode
   boot writes ([start.c]: [menvcfg |= MENVCFG_ADUE] then, in [timerinit],
   [menvcfg |= MENVCFG_STCE]) legalize from the all-zero reset -- i.e. the ADUE
   bit (61) and the STCE bit (63) set, 0xA000000000000000.  The kernel never
   writes menvcfg again, so this value is constant throughout S-mode execution.
   Both are consistent with the bit-level facts pinned by [hw_config] /
   [smode_config] (which constrain PBMTE/PMM/LPE/FIOM -- none of them bit 61).
   ADUE=1 is Svadu: an access that needs an A/D update has the bit written back
   rather than page-faulting.  The kernel's page tables carry A/D preset, so no
   live walk ever needs an update (every walk lemma takes [update_PTE_Bits = None]
   and short-circuits before the ADUE gate), and the value of ADUE is invisible
   to them -- it matters only to the boot proof that produces this constant. *)
Definition MISA_C : mword 64 := mword_of_int 0x800000000014112D.
Definition MENVCFG_S : mword 64 := mword_of_int 0xA000000000000000.

(* THE INTERRUPT-ENABLE MASK THIS KERNEL RUNS AT, from [start] onward and
   forever: [start] writes [sie] exactly once (`w_sie(r_sie() | SIE_SEIE |
   SIE_STIE)`, bits 9 and 5), never writes [mie] at all, and [mie] is 0 at
   reset.  It sits beside [MENVCFG_S] for exactly the same reason: both are
   boot-established constants that the M-mode boot proof PRODUCES
   ([WpStartNew.st_boot_csr_facts]) and the S-mode config bundle
   ([IntrDefs.sconf]) then PINS, so the constant has to be nameable from
   both sides of the M->S bridge.

   What pinning it buys: the S-mode dispatch set is masked by [mie], so at
   this value only S-timer (5) and S-external (9) can ever be delivered --
   which is exactly the pair [devintr] recognises, and hence what keeps
   kerneltrap's [printk] arm dead.  See claude-notes/completed/kerneltrap.md. *)
Definition MIE_S : mword 64 := mword_of_int 0x220.

(* [cfg_ok s]: the config precondition the fast concrete-state decode bridge
   (WpDecodeBridge) needs -- either a Machine state with mseccfg = 0, or a
   Supervisor state with menvcfg = MENVCFG_S (the constant post-boot value).
   Supplied to the [instr] decode obligation by the M-/S-mode step engines from
   [hw_config] / [smode_config]; consumed by the per-word bridge lemmas. *)
(* the config disjunction, over the REGISTER FILE.  The [mstate] form below
   is definitionally this one at [s.(sregs)] -- which is what lets the
   footprinted decode characterization ([instr]'s [decode_hval]) drop σ
   entirely: it needs the register VALUES, never the machine. *)
Definition cfg_ok_rs (rs : regstate) : Prop :=
  (register_lookup cur_privilege rs = Machine /\
   register_lookup mseccfg rs = mword_of_int 0)
  \/ (register_lookup cur_privilege rs = Supervisor /\
      register_lookup menvcfg rs = MENVCFG_S).

Definition cfg_ok (s : mstate) : Prop := cfg_ok_rs s.(sregs).

Section HwConfig.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* mcountinhibit / minstretcfg are bundled here AGAIN.  They were removed
     when the exec-shaped [should_inc] turned out to be total and not to need
     their values; the [swp] wrapper's [swp_should_inc_minstret] DOES read
     them, and it reads them in S-mode as much as in M-mode -- so they belong
     in the bundle both modes already carry, not in [mmode_config].  Nothing
     in the tree or in the kernel ever writes either, so [↦ᵣ□] is sound and
     they cost no threading at all.  [elp] IS bundled,
     persistently and existentially, pinned to NOT [LP_EXPECTED] so it discharges
     the landing-pad side condition [eq_vec elp (landing_pad_bits_backwards
     LP_EXPECTED) = false] that the run_hart_active / fetch WPs require.
     [senvcfg] is bundled at a PINNED literal (not existentially, unlike misa/
     mseccfg/elp): like mseccfg it is a board obligation ([RiscvLang.reset_regs]),
     never written again -- xv6 has no line that touches senvcfg -- so it is the
     sixth frozen cell, held the same way [htif_tohost_base] is. *)
  (* the two frozen counter-permission cells, as one named conjunct so that
     appending them to [hw_config] adds no top-level existential binder --
     every existing [iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0) "..."]
     keeps its four. *)
  Definition counter_caps : iProp Σ :=
    (∃ (scen : mword 32) (hpm : type_of_register mhpmcounter),
       (R_bitvector_32 scounteren) ↦ᵣ□ scen ∗ mhpmcounter ↦ᵣ□ hpm)%I.

  Global Instance counter_caps_persistent : Persistent counter_caps.
  Proof. apply _. Qed.

  Definition hw_config : iProp Σ :=
    (∃ (misa0 mseccfg0 : mword 64) (pmar0 : list PMA_Region) (elp0 : mword 1),
     misa ↦ᵣ□ misa0 ∗ mseccfg ↦ᵣ□ mseccfg0 ∗
     pma_regions ↦ᵣ□ pmar0 ∗ htif_tohost_base ↦ᵣ□ None ∗
     elp ↦ᵣ□ elp0 ∗ senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
     ⌜ eq_vec (_get_Misa_S misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_C misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_U misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_M misa0) ('b"1") = true ⌝ ∗
     ⌜ pma_allows_all pmar0 ⌝ ∗
     ⌜ pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ⌝ ∗
     ⌜ bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ⌝ ∗
     ⌜ eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ⌝ ∗
     ⌜ eq_vec (_get_Misa_A misa0) ('b"1") = true ⌝ ∗
     (* Full-value pins for the concrete-state decode bridge (WpDecodeBridge):
        the read-frame congruence compares WHOLE register values, so it needs
        misa/mseccfg pinned to the [dstate] reference.  Both are CONSISTENT with
        the bit pins above: MISA_C = 0x800000000014112D has S/C/U/M/A set, and
        mseccfg = 0 gives PMM = Disabled and MLPE = false. *)
     ⌜ misa0 = MISA_C ⌝ ∗
     ⌜ mseccfg0 = mword_of_int 0 ⌝ ∗
     (* the static kernel-mapping claims bundle (KMap, uniform-claims):
        persistent, minted at adequacy init -- the ambient source of
        identity-mapping fragments (device vas, boot-time image) *)
     kmap_static_claims ∗
     (* the generation certificate rides here: persistent, and common to
        [mmode_config] and the S-mode bundles alike, so neither has to carry
        its own copy (it used to arrive bundled inside [minstret_inv], which
        is gone). *)
     gen_cert ∗
     (* THE TWO COUNTER-PERMISSION CELLS.  A U-mode [csrr] of a counter CSR
        reads scounteren unconditionally and the hpm path reads mhpmcounter;
        under per-node stepping every read the cycle makes must be answerable
        from an OWNED cell, so both are in the U tier's read footprint
        ([UserTotalU.Du_r_scen] / [Du_r_hpm]).  Nothing in the tree or in the
        kernel writes either -- there is no [csrw scounteren] anywhere -- so
        [↦ᵣ□] is sound and they ride the bundle both modes already carry
        rather than being threaded (ruled 2026-08-18; the alternative,
        parking them in [IntrDefs.hart_csrs], would have made every caller
        between boot and userret carry them).  Their VALUES are existential:
        the U-mode CSR arm is total whatever the permission bits say, since a
        denied counter read is Illegal_Instruction, a [u_result_ok] outcome.
        [mcounteren] is deliberately NOT here -- timerinit WRITES it, so it
        cannot be frozen at [hw_config_intro] time; its persistent form is
        [TimerCap.sstc_enabled], minted after timerinit. *)
     counter_caps)%I.

  Global Instance hw_config_persistent : Persistent hw_config.
  Proof. apply _. Qed.

  (* the accessor lives in [UserExec] ([hw_config_counters]): this file has no
     proofmode import, and the only consumer is the U tier. *)
End HwConfig.


(* ===== RiscvModelADDfinal ===== *)
(* ====================================================================== *)
(* RiscvModelADDfinal.v                                                    *)
(*                                                                         *)
(* The [ADDfinal] section below bundles the boot-config hypotheses for the *)
(* ADD cycle (Machine mode, no pending interrupt, the fetched word w      *)
(* decoding to `add a2,a0,a1`, GPR indices a0/a1/a2).                     *)
(*                                                                        *)
(* The exec-level hart-active reduction itself is proven as               *)
(* [exec_hart_active_progress] in RiscvTryStep.v, by threading the        *)
(* functional exec-leaves (exec_read_reg / exec_write_reg reduce by       *)
(* [reflexivity]) through run_hart_active's F_Base/ADD body; the [exec]   *)
(* fetch twin is [exec_fetch_done] (RiscvModelFetchExec section below).   *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* exec-leaf helpers ([exec_read_reg] / [exec_write_reg]) *)
(* -- useful for threading exec through the try_step wrapper.               *)
(* ---------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------- *)
(* Step 2a: the exec-level hart-active reduction is proven as   *)
(* [exec_hart_active_progress] (RiscvTryStep.v); the [ADDfinal] section *)
(* below only bundles its boot-config hypotheses.         *)
(* ---------------------------------------------------------------------- *)

Section ADDfinal.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (rs2 rs1 rd : mword 5).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpend : run (getPendingSet Machine) s None s.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Help  :
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hfetch : run (fetch tt) s (F_Base w) s.
  Hypothesis Hdec :
    run (ext_decode w) s (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) s.
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  Let s1 : mstate := set_reg s nextPC (add_vec_int pc 4).
  Let s_exec : mstate :=
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).


End ADDfinal.

(* ===== RiscvModelFetchExec ===== *)
(* ====================================================================== *)
(* RiscvModelFetchExec.v                                                   *)
(*                                                                         *)
(* The fetch value-sensitive exec-mirror: exec (fetch tt) s <> None, hence *)
(* exec (fetch tt) s = Some (F_Base w, s) (via exec_fetch_done).  This is *)
(* the FETCH leaf of Hne.  Each sub-lemma (exec_translateAddr_identity /    *)
(* exec_mem_read_fetch / exec_fetch_done) reduces the corresponding fetch            *)
(* stage at the functional [exec]/[execR] level.               *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* execR bind collapsers (analogues of exec_bind_Some). *)
Lemma execR_bind_Some {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s a s' :
  execR m s = Some (inr a, s') -> execR (Defs.bind m f) s = execR (f a) s'.
Proof. intro H. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_bind0_Some {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s s' :
  execR m s = Some (inr tt, s') -> execR (Defs.bind0 m n) s = execR n s'.
Proof. intro H. unfold Defs.bind0. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_returnR_fwd {R X} (x : X) s :
  execR (Defs.returnR R x) s = Some (inr x, s).
Proof. reflexivity. Qed.

(* exec on a MemRead/MemWrite node, one bus-decode step: given which way the
   address routes ([dev_addr]), the outcome reduces to the RAM byte match /
   the device transaction.  ([cbn [exec]] only expands the single concrete
   outcome branch; the request's record projections stay untouched.) *)
Lemma exec_MemRead {X} (n : N) (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.ReadReq.pa req) = false ->
  exec (Interface.Next (Interface.MemRead n req) k) s
  = match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
    | Some w => exec (k (inl (w, None))) s
    | None => None
    end.
Proof. intros Hd. cbn [exec]. rewrite Hd. reflexivity. Qed.

Lemma exec_MemRead_dev {X} (n : N) (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.ReadReq.pa req) = true ->
  exec (Interface.Next (Interface.MemRead n req) k) s
  = match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
    | Some (w, d') => exec (k (inl (w, None))) (MState s.(sregs) s.(mem) d')
    | None => None
    end.
Proof. intros Hd. cbn [exec]. rewrite Hd. reflexivity. Qed.

Lemma exec_MemWrite {X} (n : N) (req : Interface.WriteReq.t n)
    (k : (option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.WriteReq.pa req) = false ->
  exec (Interface.Next (Interface.MemWrite n req) k) s
  = exec (k (inl None))
         (MState s.(sregs)
            (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                         (Interface.WriteReq.value req)) s.(mdev)).
Proof. intros Hd. cbn [exec]. rewrite Hd. reflexivity. Qed.

Lemma exec_MemWrite_dev {X} (n : N) (req : Interface.WriteReq.t n)
    (k : (option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.WriteReq.pa req) = true ->
  exec (Interface.Next (Interface.MemWrite n req) k) s
  = match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req) with
    | Some d' => exec (k (inl None)) (MState s.(sregs) s.(mem) d')
    | None => None
    end.
Proof. intros Hd. cbn [exec]. rewrite Hd. reflexivity. Qed.

(* read_bytes is non-None when all n bytes are present (was previously
   located among the now-removed choose_free helpers). *)
Lemma read_bytes_ne mm pa n (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N ->
     mm !! RiscvModelBytes.pa_add pa j = Some (RiscvModelBytes.nth_byte w j)) ->
  read_bytes mm pa n <> None.
Proof.
  intros Hb. unfold read_bytes.
  case_match eqn:Hm.
  - congruence.
  - exfalso.
    apply mapM_None_1, Exists_exists in Hm.
    destruct Hm as (j & Hj & Hnone).
    apply in_seq in Hj.
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    rewrite (Hb j Hjn) in Hnone. congruence.
Qed.

(* A one-iteration [untilMT]: the body runs once and the condition then holds.
   Every memory access these proofs perform is naturally aligned, so
   [checked_mem_read]/[checked_mem_write]'s split loop is always this case.
   (Lives here, not with its consumers: the fetch path needs it too.) *)
Lemma execR_untilMT_1 {R Vars} (vars vars' : Vars) (measure : Vars -> Z)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars) s s' :
  measure vars = 1 ->
  execR (body vars) s = Some (inr vars', s') ->
  execR (cond vars') s' = Some (inr true, s') ->
  execR (Defs.untilMT vars measure cond body) s = Some (inr vars', s').
Proof.
  intros Hm Hb Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge]; [| exfalso; rewrite Hm in Hge; lia ].
  rewrite (execR_bind_Some _ _ _ _ _ Hb).
  rewrite (execR_bind_Some _ _ _ _ _ Hc).
  cbn match.
  apply execR_returnR_fwd.
Qed.



(* read_ram (4 bytes present) reduces -- via the run-fact + read_bytes <> None. *)
Lemma exec_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 4 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_4_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  (* collapse [Defs.bind (Next (MemRead ..) k) matchK] to a single Next, then
     expose the read_bytes match via exec_MemRead. *)
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - (* read_bytes = Some _: the continuation is a Ret-chain, hence Some <> None *)
    cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - (* read_bytes = None: impossible, the 4 bytes are present *)
    exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* ---------------------------------------------------------------------- *)
(* Easy exec sub-twins (pure returnM).                                     *)
(* ---------------------------------------------------------------------- *)

Lemma exec_effectivePrivilege_fetch (m : mword 64) (p : Privilege) s :
  exec (effectivePrivilege (InstructionFetch tt) m p) s = Some (p, s).
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_translationMode_M s :
  exec (translationMode Machine) s = Some (Bare, s).
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_is_shadow_stack_fetch s :
  exec (is_shadow_stack_access (InstructionFetch tt)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

(* ---------------------------------------------------------------------- *)
(* translateAddr = identity (M-mode), exec version.                        *)
(* ---------------------------------------------------------------------- *)

Lemma exec_translateAddr_identity (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind.
  cbn match. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Fetch-shaped corollaries of exec_pmpCheck_machine_unlocked: a 4-byte    *)
(* instruction fetch at a 4-aligned pc / a 2-byte fetch at a 2-aligned pc  *)
(* fits in one aligned 4-byte grain cell, so unlocked entries suffice.     *)
(* ---------------------------------------------------------------------- *)

Lemma exec_pmpCheck_machine_unlocked_ifetch4 (addr : mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  exec (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) s = Some (None, s).
Proof.
  intros HL Halign.
  apply exec_pmpCheck_machine_unlocked; [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
  rewrite Hk. replace (4 * k) with (k * 4) by lia. rewrite Z_mod_mult. lia.
Qed.

Lemma exec_pmpCheck_machine_unlocked_ifetch2 (addr : mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  exec (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s = Some (None, s).
Proof.
  intros HL Halign.
  apply exec_pmpCheck_machine_unlocked; [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 2)) with 2 by (vm_compute; reflexivity).
  rewrite Hk.
  pose proof (Z.mod_pos_bound (2 * k) 4 ltac:(lia)).
  pose proof (Z.div_mod (2 * k) 4 ltac:(lia)).
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* pmaCheck = the aligned access plan (RAM), exec version.                 *)
(*                                                                        *)
(* [pmaCheck] is an early-return body now (the no-matching-region arm      *)
(* escapes), so it is peeled at the [execR] level: read the region list,   *)
(* resolve the match to the region's overridden attributes, resolve the    *)
(* access arm to its [canAccess] field, then run [mag_pma_check], which an  *)
(* aligned access answers with [CannotSplit] (RiscvExtras).                *)
(* ---------------------------------------------------------------------- *)

Lemma exec_pmaCheck_ram (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hexec.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hexec (exec_is_mag_applicable_fetch 4 s) Halign.
Qed.

(* ---------------------------------------------------------------------- *)
(* checked_mem_read = Ok (w, meta), exec version.                          *)
(* ---------------------------------------------------------------------- *)

Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Local Lemma avi0_mul2 (a : mword 64) : add_vec_int a (0 * 2) = a.
Proof. change (0 * 2)%Z with 0%Z. apply avi0. Qed.

Lemma exec_checked_mem_read_ram (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  (* the PMA/PMP decision, with the PMA answer prioritised on failure *)
  assert (Hcp : exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt Machine
                        (Physaddr addr) 4 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM. }
  (* within_mmio_readable = false *)
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (read_kind_of_flags false false false) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  cbn beta.
  (* the split loop: ONE iteration at offset 0 (see RiscvExtras' pma_ok_aligned) *)
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul4.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_machine_unlocked_ifetch4 addr s Hpmp Halign)). cbn beta.
    cbn match.
    (* the pmpCheck arm is a [bind0] seq into within_mmio_readable *)
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    (* the RAM read, whose own bind returns just the data (the meta is dropped) *)
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_32.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_returnR. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* mem_read = Ok w, exec version.                                          *)
(* ---------------------------------------------------------------------- *)

Lemma exec_mem_read_fetch (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Ziccif = true, exec version (Acc twins).           *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_Ziccif s : exec (hartSupports Ext_Ziccif) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Ziccif s :
  exec (currentlyEnabled Ext_Ziccif) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  cbn match. apply exec_hartSupports_Ziccif.
Qed.

(* ---------------------------------------------------------------------- *)
(* fetch_bytes -> FetchBytes_Success, exec version.                        *)
(* ---------------------------------------------------------------------- *)

Section FetchExec.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  (* A single PC-alignment fact; the paddr-aligned and low-bit-zero forms the
     Sail fetch path checks are all derived from this (see align4_low_bits). *)
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.

  (* fetch_bytes assembly: the two liftR sub-computations [translateAddr] and
     [mem_read] are PROVEN above (exec_translateAddr_identity / exec_mem_read_fetch),
     both = Some.  The rest is the execR plumbing through fetch_bytes' / fetch's
     catch_early_return + liftR + or_boolM/and_boolM gating, discharged with the
     execR_bind_Some / execR_bind0_Some / execR_returnR_fwd toolkit. *)
  Lemma exec_fetch_bytes_4 :
    exec (fetch_bytes pc pc 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    assert (Halign : is_aligned_paddr (Physaddr addr) 4 = true)
      by (unfold addr; rewrite fetch_pa_id; exact Hvalign).
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* exec (fetch tt) s = Some (F_Base w, s): the outer fetch around fetch_bytes
     (read PC, ext_fetch_check_pc=None, or_boolM/and_boolM extension gating with
     Ext_Zca short-circuited and Ext_Ziccif=true, isRVC=false).  Closes via the
     execR plumbing on top of exec_fetch_bytes_4. *)
  Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.

  Lemma exec_fetch_done : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* (returnR tt >> or_boolM ..) >>= fun w7 => REST ; or_boolM = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w7=false -> and_boolM (is_aligned) (Ext_Ziccif) >>= fun w11 => .. ; w11=true *)
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    (* w11=true -> read PC twice, fetch_bytes pc pc 4 -> FetchBytes_Success w -> F_Base w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.


End FetchExec.

(* ===== RiscvModelFetchPre ===== *)
(* ====================================================================== *)
(* RiscvModelFetchPre.v                                                    *)
(*                                                                         *)
(* The bounded fetch sub-lemmas that once discharged the carried PMP/PMA   *)
(* hypotheses from concrete boot CSRs have been removed; instead,    *)
(*   the fetch WPs now discharge PMP/PMA functionally via the exec-level     *)
(*   [exec_pmpCheck_machine_none] / [exec_pmaCheck_ram] lemmas above, *)
(*                          taking the concrete boot-CSR facts (all-PMP-off, the RAM region  *)
(*                          match) as hypotheses at their use sites.                            *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Task 1: all PMP entries OFF when every pmpcfg byte is zero.             *)
(* pmpcfg_n : vec (mword 8) 64 ; _get_Pmpcfg_ent_A v = subrange v 4 3 ;     *)
(* pmpAddrMatchType_encdec_backwards 0#2 = OFF.                            *)
(* ---------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------- *)
(* Task 2: a concrete executable RAM region (base 0x80000000, size         *)
(* 0x10000000).  matching_pma_region [region] addr 4 reduces to         *)
(*   if range_subset .. then Some region else None,                     *)
(* so given the range_subset geometric fact it yields Some region;      *)
(* PMA_executable is true by construction (override_PMA keeps it).         *)
(* ---------------------------------------------------------------------- *)




(* ===== RiscvModelFinal ===== *)
(* ====================================================================== *)
(* RiscvModelFinal.v                                                       *)
(*                                                                         *)
(* The CONDITIONED Hne: exec (run_hart_active 0) s <> None, assembled from  *)
(* the proven leaf exec-facts via exec_hart_active_progress.  Unlike        *)
(* wp_add_real_closed'' 's `Hne_gen` (the UNCONDITIONAL `forall s, exec     *)
(* (run_hart_active 0) s <> None`, which is over-strong / unsatisfiable for *)
(* arbitrary s), this carries the boot-config preconditions explicitly.     *)
(* ====================================================================== *)


Local Open Scope Z_scope.

Section HneClosed.
  Context (s : mstate) (pc : mword 64) (w : mword 32)
          (rs1 rs2 rd : mword 5) (cES : bool).

  (* GPR indices = a0/a1/a2. *)
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  (* booting-Machine register state. *)
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis HpcS  : register_lookup (R_bitvector_64 PC) s.(sregs) = pc.
  Hypothesis HecES : exec (currentlyEnabled Ext_S) s = Some (cES, s).
  Hypothesis HcEStrue : cES = true.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1" : mword 1) = false.

  (* fetch leaf, carried as the (proven, via exec_fetch_done) fetch exec-fact. *)
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s).

  (* the decode wall: the bytes at the PC decode to `add a2,a0,a1`. *)
  Hypothesis Hdec :
    exec (ext_decode w) s
      = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).

  (* landing-pad: elp <> EXPECTED (Zicfilp off at boot). *)
  Hypothesis Hlpad :
    eq_vec (register_lookup elp s.(sregs))
           (landing_pad_bits_backwards LP_EXPECTED) = false.

  (* dispatchInterrupt leaf, via the getPendingSet keystone. *)
  Let Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s) :=
    exec_dispatchInterrupt_none s
      (exec_getPendingSet_machine_none s cES HecES HcEStrue HmIE).

  (* the execute leaf at s_pc := set_reg s nextPC (pc+4). *)
  Let Hexec :
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
         (set_reg s nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s nextPC (add_vec_int pc 4)) (R_bitvector_64 x12)
              (regval_into_reg
                 (add_vec
                    (register_lookup (R_bitvector_64 x10)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))
                    (register_lookup (R_bitvector_64 x11)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))))).
  Proof.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    exact (exec_execute_ADD rd rs1 rs2 _ Hrs1 Hrs2 Hrd).
  Defined.


End HneClosed.

(* ====================================================================== *)
(* Pure fetch reductions (F_RVC 4-aligned and                                *)
(* the width-2 read stack for the non-4-aligned F_RVC path), so downstream  *)
(* memory-resource fetch lemmas can reach them without a WP-family import.  *)
(* ====================================================================== *)

(* ---- FetchRVC / exec_fetch_RVC_4 ---- *)
Section FetchRVC.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_RVC_4 : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_4 pc region w s HpcPC Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hdev Hbytes Hvalign)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End FetchRVC.

(* ---- the Zca enablement chain ---- *)
Lemma exec_hartSupports_Zca s : exec (hartSupports Ext_Zca) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* reduce one const-arm hartSupports leaf [_rec_hartSupports X k acc] to Some(b,s). *)
Ltac ehs_leaf s :=
  match goal with
  | |- exec (_rec_hartSupports ?e ?k ?a) s = _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] =>
        replace (Z.geb x 0) with true by (vm_compute; reflexivity) end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s));
      apply exec_returnM
  end.

(* hartSupports Ext_C = true at the exec level (whole nested capability tree). *)
Lemma exec_hartSupports_C s : exec (hartSupports Ext_C) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* and_boolM Zca (and_boolM A B) ; Zca = true *)
  erewrite exec_and_boolM_Some; [| ehs_leaf s]. cbn match.
  (* and_boolM A B *)
  erewrite exec_and_boolM_Some.
  2:{ (* A = or_boolM Zcf (or_boolM (F>>=not) (returnM (neq xlen 32))) *)
      erewrite exec_or_boolM_Some; [| ehs_leaf s]. cbn match.   (* Zcf=false *)
      erewrite exec_or_boolM_Some.
      2:{ erewrite exec_bind_Some; [| ehs_leaf s]. apply exec_returnM. }   (* F=true -> not=false *)
      cbn match. apply exec_returnM. }
  (* A's value is [neq_int xlen 32]; make it concrete then take B *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  (* B = or_boolM Zcd (..) = true (Zcd = true) *)
  erewrite exec_or_boolM_Some; [| ehs_leaf s]. reflexivity.
Qed.

(* currentlyEnabled Ext_C = (misa.C bit), at any Acc level. *)
Lemma exec_rec_cE_C_misa (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_C k acc) s
    = Some (eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_C s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zca s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s).
Proof.
  intro HC. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zca s)). cbn match.
  rewrite (exec_or_boolM_Some _ _ _ _ _
            (exec_rec_cE_C_misa (currentlyEnabled_measure Ext_Zca - 1) _ s
               ltac:(vm_compute; reflexivity))).
  rewrite HC. cbn match. reflexivity.
Qed.

(* ---- moved from WpAdd.v: exec twins of currentlyEnabled Ext_S (value =
   misa.S bit), needed to discharge the getPendingSet / dispatchInterrupt
   keystone during M-mode execution. ---- *)
Lemma exec_hartSupports_S s : exec (hartSupports Ext_S) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicsr s : exec (hartSupports Ext_Zicsr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_currentlyEnabled_S s :
  exec (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)).
  rewrite (exec_and_boolM_Some _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_rec_cE_Zicsr.
  - reflexivity.
Qed.

(* priv_mSU: the non-virtualized privileges.  In any of these, the decoder's
   Zicfilp LPAD-clause guard [get_xLPE] reduces to SOME boolean (M reads
   mseccfg.MLPE, S reads menvcfg.LPE, U reads senvcfg/menvcfg.LPE); only the
   virtualized modes hit internal_error.  This is the decode-side privilege
   hypothesis: the decode walkers only need the guard to REDUCE (its value is
   discarded via [b && false = false] for every non-lpad word), so membership
   here is all a decode lemma ever needs. *)
Definition priv_mSU (p : Privilege) : bool :=
  match p with
  | Machine | Supervisor | User => true
  | VirtualSupervisor | VirtualUser => false
  end.

(* ---- the width-2 mem-read stack + exec_fetch_bytes_2 ---- *)
Lemma autocast_mword_id_16 (w : bv 16) :
  autocast (T := mword) (m := 8 * 2) (n := 2 * 8) w = w.
Proof.
  unfold autocast.
  destruct (Z.eq_dec (8 * 2) (2 * 8)) as [e | ne].
  - apply cast_Z_refl.
  - exfalso; apply ne; reflexivity.
Qed.

Lemma run_read_ram_plain_2_pin (addr : mword 64) (w : bv 16) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 2 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_2 (addr : mword 64) (w : bv 16) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 2 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_2_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 2) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

Lemma exec_pmaCheck_ram_2 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 2 (InstructionFetch tt) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hexec.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hexec (exec_is_mag_applicable_fetch 2 s) Halign.
Qed.

Lemma exec_checked_mem_read_ram_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt Machine
                        (Physaddr addr) 2 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 2 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (read_kind_of_flags false false false) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul2.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_machine_unlocked_ifetch2 addr s Hpmp Halign)). cbn beta.
    cbn match.
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_16.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_returnR. reflexivity.
Qed.

Lemma exec_mem_read_fetch_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2 with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section FetchBytes2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma exec_fetch_bytes_2 :
    exec (fetch_bytes pc pc 2) s = Some (@FetchBytes_Success 2 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 2 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2 PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchBytes2.

(* ---- FetchRVC2 / exec_fetch_RVC_2 ---- *)
Section FetchRVC2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.

  Lemma exec_fetch_RVC_2 : exec (fetch tt) s = Some (F_RVC w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* w__7 (align error) = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w__11 (4-aligned & Ziccif) = false because not 4-aligned *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> FetchBytes_Success w -> F_RVC w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc region w s HpcPC Hpriv Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchRVC2.


(* ---- the 2-aligned 32-bit fetch (2+2 read) ---- *)
(* ---------------------------------------------------------------------- *)
(* 2-aligned 32-bit fetch: reads 2 bytes (ilo) at pc, isRVC=false, then 2  *)
(* more (ihi) at pc+2, returns F_Base (concat ihi ilo).  The 2-aligned     *)
(* analog of exec_fetch_done above.  For csrr@0xa, jal@0x16.               *)
(* ---------------------------------------------------------------------- *)
Section FetchFBase2.
  Context (pc : mword 64) (regl regh : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.
  Let addrh := fetch_pa (add_vec_int pc 2).
  Let ilo : mword 16 := subrange_vec_dec w 15 0.
  Let ihi : mword 16 := subrange_vec_dec w 31 16.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatchl : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some regl.
  Hypothesis Hmatchh : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addrh) 2 = Some regh.
  Hypothesis Halignl : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Halignh : is_aligned_paddr (Physaddr addrh) 2 = true.
  Hypothesis Hexecl : (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hexech : (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hcl : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsigl : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hhl : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hch : exec (within_clint (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hsigh : exec (within_sig (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hhh : exec (within_htif_readable (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hdevl : dev_addr addr = false.
  Hypothesis Hdevh : dev_addr addrh = false.
  Hypothesis Hbytesl : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte ilo j).
  Hypothesis Hbytesh : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addrh j) = Some (nth_byte ihi j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HnotRVC : isRVC ilo = false.
  Hypothesis Hconcat : concat_vec ihi ilo = w.

  Lemma exec_fetch_F_Base_2 : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    assert (HrdPC2 : exec (Defs.read_reg PC) s = Some (pc, s)) by exact HrdPC.
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> Success ilo *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc regl ilo s HpcPC Hpriv Hpmp Hmatchl Halignl Hexecl Hcl Hsigl Hhl Hdevl Hbytesl)).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    (* isRVC false: read PC twice, fetch_bytes pc (pc+2) 2 -> Success ihi -> F_Base (concat ihi ilo) *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    assert (Hfb2hi : exec (fetch_bytes pc (add_vec_int pc 2) 2) s
                     = Some (@FetchBytes_Success 2 ihi, s)).
    { unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc pc (add_vec_int pc 2)) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr addrh, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite (exec_translateAddr_identity (add_vec_int pc 2) s Hpriv).
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addrh, PBMT_PMA) s)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addrh) 2 false false false)) s
             = Some (inr (Ok ihi), s))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_2 PBMT_PMA addrh regh ihi s
                     Hpmp Hmatchh Halignh Hexech Hch Hsigh Hhh Hdevh Hbytesh Hpriv).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hfb2hi).
    cbv iota beta. rewrite execR_returnR_fwd. cbn match.
    rewrite Hconcat. reflexivity.
  Qed.
End FetchFBase2.



(* ---- the F_RVC run_hart_active reduction ---- *)
(* ---------------------------------------------------------------------- *)
(* run_hart_active reduction for the F_RVC (compressed) branch.            *)
(* Mirror of exec_hart_active_progress; nextPC := pc+2, decode via         *)
(* ext_decode_compressed, gated on currentlyEnabled Ext_Zca = true.        *)
(* ---------------------------------------------------------------------- *)

Section HartActiveRVC.
  Context (s s_x : mstate) (h : mword 16) (instr other : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_RVC h, s).
  Hypothesis Hdec : exec (ext_decode_compressed h) s = Some (instr, s).
  Hypothesis Hlpad : eq_vec (register_lookup elp s.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis HpcF : register_lookup PC s.(sregs) = pc.
  Hypothesis Hzca : exec (currentlyEnabled Ext_Zca) s = Some (true, s).
  Let s_pc : mstate := set_reg s nextPC (add_vec_int pc 2).
  (* RVC instructions expand via [ExecuteAs] to a base instruction [other]. *)
  Hypothesis Hexec : exec (execute instr) s_pc = Some (ExecuteAs other, s_pc).
  Hypothesis Hexec2 : exec (execute other) s_pc = Some (resf, s_x).


End HartActiveRVC.


