# Step 3 plan — wpd_release / wpd_acquire / wpd_allocpid → allocpid_prefixes → Theorem 1/2 (v2, 2026-10-05)

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../../claude-notes/LEAN.md)).

Advisor plan (read-only survey of AxSpinE8/Hd*/PO*/CertP*/XP*/J*/U*/X*, AxCert*, AxClsStep, KptPt,
Code{Acquire,Release,Allocpid}). Workers: (am) amoswap CertB + `Xx_amoswap`; (rl) wpd_release; (aq) wpd_acquire;
(ap) allocpid leaves. Interface decisions **[ID-n]** are listed in §8. Offsets were checked against the shape
lengths (`myc_sh` 19, `po_sh` 65/89, `pp_sh` 42/45, `hold_sh` 44/6 items, each INCLUDING its pinned return fetch).

## 0. Facts the plan rests on (checked in the tree)

- Landed convention (E8/HdA/PO4/PO6): `Row_f k row …` = `RowSh k row sh` over `ritem` (RF n | RP pa n | RS pa n |
  RL pa n); the shape's LAST item is the pinned return fetch `RP pret nret` and the continuation sits at exactly
  that position, boundary state `AThread (PHart cpu (Ret tt) rs' None ib') k'`; pure post = one ⌜…⌝ (regime,
  PC = ret, TLB kept, exact GPRs + "others kept", `graph_data` of stores, `graph_value` of loads); annotations
  handed on (`(i,kr) ↦ₐ ⌜RLfact GT i pa kr vw⌝` per private reload; `Olk`/`Ocpu` output predicates).
- **Release has NO amoswap**: `sd zero,16(s1); fence rw,w (LFence true true false true); sw zero,0(s1)`.
- **The store class never enters the WPd**: `AStepWrite` checks `aident` (class erased); `wpd_dwr_nodeM` /
  `CResM` / `CResW` forget the Cert's `CSt _ c`; `fx_release'` is selected by the GRAPH label's class, i.e. by the
  ROW. The Cert's release flag `r` is threaded through `CertB … d0 r0 PX` / `XBkW` but nothing consumes it.
- Private class = WOK + row fact; `fx_priv_readn` is n-byte for any `Cw` with `priv L a i` (cpu fields included via
  `cpu_own`); `fx_priv_read0` is the genesis arm. `Xx_ld4` deposits nothing only because the latest earlier store
  lies outside the instruction's window.
- The claim annotation must be deposited PRE-SPLIT (`wpd_acquire_x`'s `LK ∗ RP ⊢ R1 ∗ R2`; `dflowO_draw` deposits
  two): `RNP e`/`RCPU e` are usable only from an annotation AT anchor `e`, and LK must stay at the claim (only the
  `.aq` RMW is ppo-before every later access). `wpd_annot_split` (AxSpinH5) splits a deposited `P ∗ Q` later.
- `fence_gob` (AxSpinProt3) / `fence_lobp` (AxSpinProt5) already give: any hart-i memory event before a
  `fence rw,w` is gob/lobp-before a store after it. `R_pid e = R_cpu e ∗ R_np e` definitionally.
- `u_alloc2_joint` (AxSpinJ2) proves distinctness by issued-FRAGMENT exclusivity through the joint adequacy,
  with no row-shape dichotomy — position-independent, hence the route for real rows.
- `KptPt`/`KptTree` hold the kvmmake-faithful kernel table (identity DRAM map, 4 KiB leaves, A/D preset variant).

## 1. CPS statement shapes

**[ID-1]** Shapes are `list ritem`, extended by `RB pr pw sr sw` (fence item, `aident lb = IFence …`) and
`RSc pa n cls` (store with PINNED class). Composition by `++` (`RowSh_app_l/_r`). (rl) publishes FIRST, in
`AxSpinRs.v`: `hold_sh hb …` + `Row_holding_of : RowSh k row (hold_sh …) → lk_branch row k hb → Row_holding k row hb …`
(hb=true: `lshape` items 0..14, `myc_sh` at 15, items 34..42, RP; hb=false: 5 items + RP), and `rel_sh`. (aq)
publishes `acq_sh`, (ap) `alloc_sh`. Value conditions (`lk_branch`, RMW read values, arm bits) stay separate Prop
conjuncts next to `RowSh`, as in `Row_holding`.
**[ID-2]** Handles are explicit named premises/arguments `(i,k) ↦ₐ P` with anchor positions as Rocq variables;
frames default to `True`; `FRAG nm w8` stays in its own annotation at the `sw nextpid`.
**[ID-3]** Reload annotations travel as `RLbag i l := [∗ list] '(kr,pa,vw) ∈ l, (i,kr) ↦ₐ ⌜RLfact GT i pa kr vw⌝`,
with `rl_f k rs0 … := rl_callee … ++ [(k+…, uint Pra, st_bytes 8 (gpr_val rs0 r1)); …]` INCLUDING callees' lists
(mycpu's inner reloads no longer dropped — needed for the value-level integrity conjunct). E8/HdA/PO4/PO6 get
thin wrapper corollaries re-packaging their explicit annotations (no re-proof).

### wpd_release (rl)
```
k+0 RF2 | k+1 RF2, k+2 RS Pra 8 | k+3 RF2, k+4 RS Ps0 8 | k+5 RF2, k+6 RS Ps1 8 | k+7 RF2 | k+8 RF2 | k+9 RF4 (jal holding)
k+10..k+52 hold_sh true … (lk read k+11, lk->cpu read k+22, mycpu at k+25)      k+53 RP p10 2 (c.beqz)
k+54 RP p12 4 (sd zero,16(s1); arm pinned)  k+55 RS pcl 8  k+56 RF4  k+57 RB true true false true  k+58 RF4  k+59 RSc plk 4 WCrel
k+60 RF4 (jal pop_off)  k+61.. pp_sh c (42|45)  → krp := k+102 (+3 if ¬c): RP p22 2, RL Pra 8, RF2, RL Ps0 8, RF2, RL Ps1 8, RF2, RF2, RP pret nret
rel_len c := 111 + (if c then 0 else 3); continuation at k + rel_len c − 1.
```
```
Theorem wpd_release k c rs0 ib0 ret pret nret (own/holding/pop_off slots, Pn Pi) (pinned PAs) (kc kw : nat) (val : bv 64) (knp : nat) :
  RowSh k row (rel_sh c …) → lk_branch row (k+10) true →
  well-formedness (row_w8, no_rmw8 slots, row_wle/no_rmwn fields, row_wle row plk 4, no 8-byte RMW at xl_lk L+16) →
  ctrl_ok rs0 → PC rs0 = prl 0 → warm TLB (prl 0, pch 0, pcm 0, ppp 0, a0v, data pages) →
  lock translations (a0v ↦ Plk = xl_lk L at 4; a0v+16 ↦ Pcl = xl_lk L+16 at 8, both ways) → slot8/fld4 bundles → alldj → fpin facts →
  row !! kc = Some (LRmw true false (xl_lk L) tsc rvsc wvsc clsc) → (kc < k)%nat → nolk (xl_lk L) G0 (i,kc) (i,k+11) →
  row !! kw = Some (LStore false (xl_lk L+16) (wbytes 8 val) cls) → (kw < k)%nat →          (* val GENERIC *)
  (∀ w a v', a ∈ clb L → gwrites_byte G0 w a v' → gpo G0 (i,kw) w → gpo G0 w (i,k+22) → False) →
  (knp < k)%nat → (∃ l, row !! knp = Some l ∧ lb_is_mem l = true) →
  (i,kc) ↦ₐ LK i (i,kc) -∗ (i,kw) ↦ₐ RVLc (i,kw) (wbytes 8 val) -∗ (i,knp) ↦ₐ RNP (i,knp) -∗
  (∀ vlk vcpu vn vi … rs' ib',
     ⌜ctrl_ok rs' ∧ PC rs' = ret ∧ tlb kept ∧ sp = sp0 ∧ r10 = mycpu_ret tp ∧ r1/r8/r9 = ld_res of the reloads ∧ (∀ r ∉ {1,2,8,9,10,15}, kept) ∧
      spills' graph_data ∧ graph_data (i,k+55) = st_bytes 8 0 ∧ graph_data (i,k+59) = st_bytes 4 0 ∧ graph_value (i,k+11) = vlk ∧
      graph_value (i,k+22) = vcpu ∧ vcpu = wbytes 8 val ∧ hres … ≠ 0 (non-panic arm) ∧ pop_off's pure facts ∧ reload values⌝ -∗
     (i,k+59) ↦ₐ NH i -∗                                                           (* the result *)
     (i,k+11) ↦ₐ ⌜∀ t b, greads_byte G0 (i,k+11) (xl_lk L) t b → b ≠ B0⌝ -∗           (* D4 release arm, lock half *)
     (i,k+22) ↦ₐ ⌜∀ j a t b, clb L !! j = Some a → greads_byte G0 (i,k+22) a t b → wbytes 8 val !! j = Some b⌝ -∗
     FLDann_pop … -∗ RLbag i (rl_release k c rs0 …) -∗ WPd (boundary at k + rel_len c − 1) {{Ψ}}) -∗
  WPd (boundary at k, rs0) {{Ψ}}.
```
Internals: `holding_from_release'` at k+10 (Qc = Qw = True; OOwn's re-tied handle `∃ e', e' = (i,kw) ∨ e' = (i,k+22)`
feeds `Xx_sd_cpu` at k+54/55 — a positional 8-byte leaf on `fx_cpu_write` (value 0 admitted) depositing
`(i,k+55) ↦ₐ RVLc (i,k+55) (wbytes 8 0)`); `Xx_fence` (XBkW over a BFin twin of `AxCert4.cert_execute_fence`, e = 1,
`PX d r := d = CPend ∧ r = true`, GPRs unchanged; `wpd_fence_nodeM` needs no flow resource); `Xx_sw_rel` (4-byte
plain-store XBkW leaf whose resource `FstRel` is `fx_release'` with `Rs := [R_cpu; R_np]` at anchors (i,k+55),
(i,knp), `locked` from the OHeld output at (i,k+11); `gob`/`lobp` via `fence_gob`/`fence_lobp`); `wpd_pop_off` at
k+61; tail leaves + pinned return. The panic arm is not in this lemma (the row pins p12) — §4.

### wpd_acquire (aq)
```
k+0..k+8 as release; k+9 RF4 (jal push_off); k+10.. po_sh b … → kp := k+74 (+24 if b): RP p10 2 (c.mv a0,s1); kp+1 RF4 (jal holding)
kp+2.. hold_sh hb … → kh := kp+7 (hb=false) | kp+45 (hb=true): RP p16 2 (c.li a4,1); kh+1 RF2 (c.bnez a0, not taken)
iteration j = 0..n, it_j := kh+2+5j:  RP p1a 2 (c.mv a5,a4) | RF4 (amoswap) | RMW item (IRmw true false plk 4; value ≠ 0 for j<n, = 0 at n) | RF2 (sext.w) | RF2 (c.bnez a5)
km := kh+2+5(n+1): RP p24 4 (jal mycpu); km+1.. myc_sh → km+19 RP p28 2 (c.sd a0,16(s1)); km+20 RS pcl 8
km+21 RF2, km+22 RL Pra 8 | km+23 RF2, km+24 RL Ps0 8 | km+25 RF2, km+26 RL Ps1 8 | km+27 RF2 | km+28 RF2 (c.ret) | km+29 RP pret nret
acq_len b hb n := km+30−k;  kA := kh+4+5n (the claim RMW).
```
```
Theorem wpd_acquire k b hb n rs0 ib0 ret pret nret (slots: 3 own, push_off's 5 + Pn Pi, holding's 5, mycpu's 2) (pinned PAs) :
  RowSh k row (acq_sh b hb n …) → lk_branch row (kp+2) hb → spin_vals row kh n → well-formedness → entry/warm TLB → translations → alldj → fpin →
  ISL -∗ NH i -∗
  (∀ … rs' ib', ⌜… r10 = mycpu_ret tp ∧ r14 = 1 ∧ r15 = 0 ∧ r1/r8/r9 reloaded ∧ (∀ r ∉ {1,2,8,9,10,14,15}, kept) ∧
      graph_data (i,km+20) = st_bytes 8 (mycpu_ret tp) ∧ RMW graph facts at every it_j+2 ∧ push_off's/holding's pure facts⌝ -∗
     (i,kA) ↦ₐ LK i (i,kA) -∗ (i,kA) ↦ₐ RNP (i,kA) -∗ (i,km+20) ↦ₐ RVLc (i,km+20) (wbytes 8 (mycpu_ret tp)) -∗
     (hb = true → (i,kp+14) ↦ₐ ⌜rd_fact (clb L) cvx G0 (i,kp+14)⌝) -∗                     (* ORacy: D4 acquire arm *)
     FLDann_push … -∗ RLbag i (rl_acquire …) -∗ WPd (boundary at km+29) {{Ψ}}) -∗
  WPd (boundary at k, rs0) {{Ψ}}.
```
Spin: `wpd_spin j n : NH i -∗ (claim continuation at it_(n+1) with the handles) -∗ WPd (boundary it_j, a4 = 1)`,
ordinary induction on `n − j` (the row pins n; no Löb). Failed iteration = Xx_reg, `Xx_amoswap` (fail arm returns
`NH i`), Xx_reg, `Xx_pin` (target p1a); the claim iteration ends with `Xx_pin` to p24. The claim's `RP` is split
into `RCPU ∗ RNP` by `wpd_annot_split`; RCPU feeds the `c.sd a0,16(s1)` (`Xx_sd_cpu`, value `mycpu_ret tp`).

### wpd_allocpid (ap, after aq/rl)
```
k+0..k+7 as above; k+8 RF4, k+9 RF4 (a0 := &pid_lock), k+10 RF4 (jal acquire); k+11.. acq_sh → ka := k+11+acq_len−1: RP p16 4 (auipc a5)
ka+1 RF4, ka+2 RF2 (c.lw s1), ka+3 RL pnp 4, ka+4 RF4 (addiw), ka+5 RF2 (c.sw), ka+6 RS pnp 4, ka+7 RF4, ka+8 RF4, ka+9 RF4 (jal release)
ka+10.. rel_sh c → kr := ka+10+rel_len c−1: RP p32 2 (c.mv a0,s1); kr+1 RF2, kr+2 RL Pra 8, kr+3 RF2, kr+4 RL Ps0 8, kr+5 RF2, kr+6 RL Ps1 8, kr+7 RF2, kr+8 RF2 (c.ret), kr+9 RP pret nret
```
Pre `ISL ∗ NH i`. Continuation at kr+9 receives ⌜a0 = ld_res 8 (release's s1 reload bytes) ∧ …⌝, `(i,ka+3) ↦ₐ NPh (i,ka+3) w8`,
`(i,ka+3) ↦ₐ ⌜np_src …⌝`, `(i,ka+6) ↦ₐ FRAG nm w8`, `(i,ka+69) ↦ₐ NH i`, the D4 annotations, `RLbag` (the pid readback:
s1 spilled at ka+16, reloaded at kr−3; its `RLfact` gives a0 = sext32 w8 after readback). (ap)'s leaves now: `Xx_lw_np`
(4-byte XBkW load, `FldMW` from `fxu_np_read` with anchor `(i,kA) ↦ₐ RNP (i,kA)`; `gmo_lt (i,kA) r` by `acq_gob`+`gob_gmo`;
"no po-earlier nextpid write" is a row fact), `Xx_sw_np` (`fxu_np_incr`, premise `bv_unsigned w8 + 1 < 2^32`, deposits
`RNP (i,ka+6)` and `FRAG nm w8`), `allocpid_text`, `alloc_sh`, and the pure `nolk`/`kc < k` facts for release from `alloc_sh`.

## 2. The amoswap-leaf interface (am) ↔ (aq) — release does not use it

**[ID-4]** (am) publishes in `AxSpinAm*.v`, in AxSpinXP2's Section context (σi T satp0 Hmode Hasid Hppn i cpu; L GT nm Ψ):
```
Definition XAmo k pc rs2 rs1 rd vb (Out : list (bv 8) → iProp Σ) : iProp Σ :=
  ∀ s rs, ⌜RetX cpu rs k s ∧ ctrl_ok rs ∧ PC rs = pc ∧ hitW rs pc ∧ gpr_val rs rs1 = vb ∧ hitW rs vb ∧ (k + 2 ≤ LEN)%nat⌝ -∗
    (∀ rvs rs' ib', ⌜length rvs = 4%nat⌝ -∗ ⌜GoodB T satp0 rs pc false None (Some (rd, amo_ldv 4 rvs)) rs'⌝ -∗
       ⌜∃ ts wvs cls, grow GD0 i !! S k = Some (LRmw true false (uint pa) ts rvs wvs cls) ∧ wvs = wrb 4 (amo_stv 4 (gpr_val rs rs2))⌝ -∗
       Out rvs -∗ WPd (boundary at k+2) {{Ψ}}) -∗ WPd s @ MaybeStuck; i {{ Ψ }}.
Lemma Xx_amoswap k pc rs2 rs1 rd vb pa Out :
  text_okB σi T satp0 pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) → uint rd ≠ 0 →
  data_at_S σi T (acc_amo true) vb 4 pa → ¬ xl_text L (uint pa) →
  (∀ k' lb aq b m, (k ≤ k' < k+2)%nat → grow GD0 i !! k' = Some lb → aident_rd (aident lb) = Some (aq, uint pa, m) → False) →   (* HnoSplit, window *)
  FstRmwW (dok_atP (uint pa) 4) i Out k (k+2) -∗ XAmo k pc rs2 rs1 rd vb Out.
```
`FstRmwW` = the window form of the write-half resource (`wpd_xwr_nodeM` consumes `Fst dok i Out`, hands
`Out k (written bytes)`; it is `CResW`'s `CRmwR` arm). (am) states `amo_ldv`/`wrb`/`amo_stv` as `CertB` yields them
(from `AxLeafS.CertXT_amoswap_S`, `ow_amo`). **[ID-5]** The acquire resource, pre-split two ways:
`OAcq R1 R2 kA wvs := match grow GD0 i !! kA with Some (LRmw _ _ _ _ rvs _ _) => if decide (rvs = z4) then (i,kA) ↦ₐ R1 ∗ (i,kA) ↦ₐ R2 else NH i | _ => True end`
(claim/fail read off GD0's label, as `OHeld` does) and
`FstAcq_nh : (LK i (i,kA) ∗ RP (i,kA) ⊢ R1 ∗ R2) → ISL -∗ NH i -∗ FstRmwW (dok_atP (xl_lk L) 4) i (OAcq R1 R2) kA (kA+2)`
(claim `fx_claim`, fail `fx_neutral`). (aq) uses R1 := LK, R2 := RP. A `FstAcq_h` (notheld via `(i,kw) ↦ₐ NH i`,
`fx_claim'`) is not needed for allocpid — deferred. Until (am) lands, (aq) takes `Xx_amoswap` + `FstAcq_nh` as Section
hypotheses with EXACTLY these statements.

## 3. Release ordering → prot_xv6   **[ID-6] decided: row-pinned class; no state flag, no fused leaf**

(i) `rel_sh` pins k+59 as `RSc plk 4 WCrel` and k+57 as `RB true true false true`; `Xx_sw_rel`'s resource is
`fx_release'`, selected by that label. (ii) `Xx_fence` is a plain 2-item leaf (its `PX` may report `r = true`;
nobody consumes it). (iii) HONESTY as a pure row lemma (same file as the Hdeps bridge):
`relp_at row k := foldl (λ r lb, relp_upd (wlabel_of lb) r) false (take k row)`;
`row_cls_honest row := ∀ k lb, row !! k = Some lb → store lb → lb_cls lb = (if relp_at row k then WCrel else WCplain)`;
`∀ row ∈ allocpid_prefixes i, row_cls_honest row` (the only fence is at k+57, k+58 is a fetch). This is exactly
`AxClsStep.cls_step`'s class condition, so the rows Theorem 1 quantifies over are the ones the program realises.

## 4. D4 field reads, panic-prefix rows, mycpu annotations

**[ID-7] Field leaves (worker po).** `Xx_ld4R` = `Xx_ld` at 4 bytes: premises `grow GD0 i !! kw = Some (LStore false pa vw cls)`,
`kw < S k`, no write to pa in (kw, S k) — ROW facts the COMPOSER supplies even when kw is outside the window (push_off's
noff store feeding pop_off's load); deposits `(i,S k) ↦ₐ ⌜RLfact4 GT i pa (S k) vw⌝`. `Xx_ld4G` = genesis arm
(`fx_priv_read0`; premise "no po-earlier store to pa in the row"; deposits `⌜∀ j a t v, cl_range pa 4 !! j = Some a →
greads_byte G0 (i,S k) a t v → t = 0 ∧ gx_img G0 a = Some v⌝`). `wpd_push_off_ann`/`wpd_pop_off_ann` twins take
`(kwn,vwn)`/`(kwi,vwi)` or the genesis flag and hand on `FLDann_push := (i,k+30) ↦ₐ …G ∗ (i,tk+20) ↦ₐ …G`,
`FLDann_pop := (i,k'+29) ↦ₐ ⌜RLfact4 … Pn … vwn⌝ ∗ (c = false → (i,k'+36) ↦ₐ ⌜RLfact4 … Pi … vwi⌝)` — the same
PO1..PO6 scripts with `Xx_ld4` swapped. Chain at Theorem 1's row end: genesis (Himg noff = 0) → push_off stores 1 →
pop_off reads 1 ⇒ ¬(0 ≥ noff); intena: push_off stores 0 ⇒ the `c = false` arm reads 0.

**[ID-8] Prefix tolerance and panic cuts — STAGED.** (aq)/(rl)/(ap) write FULL-shape lemmas now (`RowSh`; an
off-path row does not match the pinned `RP`, so wpd_f never faces a cut). Prefix rows need every leaf to accept
`LEN` anywhere at a boundary: one engine hook plus mechanical twins, a separate stage after Theorem 1 on complete rows:
- `RowShP k row sh := (∀ j it, sh !! j = Some it → (k+j < LEN)%nat → ∃ lb, row !! (k+j) = Some lb ∧ ishape it lb) ∧ (LEN ≤ k + length sh → (LEN − k) ∈ bnd sh)` (ends at boundaries only, so `HΨmid` stays vacuous);
- Section parameter `Des : nat → Prop` (designated ends = off-path cuts + the complete end) and hook
  `HΨend : ∀ k' rs' ib', ¬ Des k' → k' = LEN → ⊢ post_lifting Ψ i (AThread (PHart cpu (Ret tt) rs' None ib') k')`;
  engine lemma `wpd_bnd k : ¬ Des k → ((k + 2 ≤ LEN)%nat → WPd (boundary k)) → WPd (boundary k)`;
- P-twins: `RowSh` → `RowShP`, premise `∀ j ∈ bnd sh \ cuts sh, ¬ Des (k+j)`, one `Kpanic_j` per cut
  (`∀ rs' ib', ⌜facts so far ∧ the gate value takes the off arm⌝ -∗ annotations so far -∗ post_lifting Ψ (boundary k+j)`);
  proof = the same script with `wpd_bnd` at each boundary. Cuts: acquire's `c.bnez a0` (kh+2), release's `c.beqz a0`
  (k+54), pop_off's `noff<1` and `intena≠0` arms; push_off none.
- Theorem 1's post makes `HΨend` free (`post_lifting` of a pure-true Φ needs no resources):
  `Φ i s := ⌜¬ cut_at row (at_k s)⌝ ∗ (⌜complete_at row (at_k s)⌝ -∗ ∃ w8, ⌜gpr_val (regs s) r10 = sext32 w8 ∧ reload_integrity GD i⌝ ∗ FRAG nm w8)`
  (a0 and integrity derived inside `post_lifting` from `RLbag` + `graph_value`). Each `Kpanic_j` derives False by
  reading back the gate load's annotation (release: k+22's bytes = val = `mycpu_ret tp` vs the taken beqz; acquire:
  ORacy + `cpu_read_not_mine` ⇒ bytes ≠ cpus_ptr i vs the taken bnez; pop_off: the noff chain).

## 5. allocpid_prefixes and the Hdeps bridge

`alloc_full i := { row | ∃ b hb n c addrs, RowSh 0 row (alloc_sh …) ∧ length row = length (alloc_sh …) ∧ value conditions
(lk_branch ×2, spin_vals, pop_off arm bits) ∧ fetch values = gx_img at their own address ∧ walker reads = gx_img (HAD) }`,
addresses from the layout (stk_i slots, cpus[i] fields, xl_lk L, xl_np L, text PAs); `alloc_cut i` := the shape truncated
at a cut with the gate value flipped; `allocpid_prefixes i := { take m row | row ∈ alloc_full i ∪ alloc_cut i, m ∈ bnd (alloc_sh …) }`;
`complete row := row ∈ alloc_full`, `enters_panic row := row ∈ alloc_cut` at a panic arm (the intr_on arm is a cut too, also refuted).
`prog_deps_xv6 GT` from the positions: `(gate read, every po-later store, DTctrl)` for holding's lw/ld (×2), push_off's
first noff load, pop_off's noff/intena loads and every c.ret's ra reload; `(s1 reload, store, DTaddr)` for release's sd/sw
(s1 from holding+0x26) and acquire's amoswap/sd (s1 from push_off+0x26) — ctrl-closed by construction.
**[ID-9]** The bridge `prog_deps_xv6 ⊆ row_deps_t` and `row_cls_honest` are discharged per CERTIFICATE WITNESS by
vm_compute (the certificates' rows come from the emission); the general ∀-row lemmas are follow-ups, named as such in
Theorem 1's header.

## 6. Retargeting AxSpinJ2's capstones to real code

Keep `u_alloc2_joint`'s route (FRAG exclusivity + `tierA_adequacy_ann_gate_joint_t` + `upost_joint`), Σ := xv6Σ.
DISAPPEAR: `HrA/HrB : grow … = u_row …` (→ `Hrow : grow GD i ∈ allocpid_prefixes i`), the hand layout `Lx`/fetch
region `Tf` (→ one real layout `xlay_xv6 A B …` with `xlay_ok`, `xl_text` = the lock text), `Himgc/Himgn` as separate
items (→ `Himg`). REMAIN: `Hcons_t`, `Hcl`, `Hharts`, `Hnowrap` (from n0 ≤ 2³²−3), `Hrun`. NEW: `Himg` (text bytes of
the 7 functions via `*_text`; lock = 0; lk->cpu = 0; nextpid = n0; noff = 0), `Hlayout` (disjointness/privacy, cid
injectivity, `tp i = cid_word_of i`; `cl_aligned` from the rows), the table `T`/`satp0` with `data_at_S` for every data
page and `fpin` for every pinned fetch PA, `Hentry` (pc/sp/tp/ra, SIE = 0, warm TLB for every page touched — a stated
scope restriction), `va_first_read` (the one Sail premise), `text_fixed`, `HΨmid`. Conclusion:
`(∀ i ∈ [A;B], ¬ enters_panic (grow GD i)) ∧ (complete A → complete B → a0 (σf A) ≠ a0 (σf B)) ∧ reload_integrity`;
first landing restricted to `Hrow ∈ alloc_full` (conjunct 2 + integrity), the prefix stage adds conjunct 1 proper.
Theorem 2 delta: harts [A;B;C], `HwpC` at `xlay_xv6` extended with C (no C-private bytes, as `L3`), `Φ C := True`.

## 7. Files, ordering, parallelism

Stage A (now, parallel). (am) `AxSpinAm{1..3}.v`: BFin `CertB` for `amoswap.w.aq`, `Xx_amoswap`, `FstAcq_nh`, a
stuck/not-stuck + satisfiability certificate on a real fetch node. (rl) `AxSpinRs.v` FIRST, then `AxSpinRl*.v`
(`Xx_fence`, `Xx_sd_cpu`, `Xx_sw_rel`, composition; 10–14 files at ≤ 250 s each). (aq) `AxSpinAq*.v` (`acq_sh`,
`wpd_spin`, composition; 12–16 files; `Xx_sd_cpu` shared with (rl) — whoever lands first, the other imports).
(ap) `AxSpinAp*.v` (`allocpid_text`, `Xx_lw_np`, `Xx_sw_np`, `alloc_sh`, row-fact lemmas).
Stage B. (ap) `wpd_allocpid`. In parallel (po): [ID-7] leaves + PO twins + `RLbag` wrappers of E8/HdA/PO4/PO6.
Stage C (parallel from now, one worker): certificate infrastructure — `T_xv6 : ptree` from `KptTree.kpt_tree_spec_gen`
(A/D preset per HAD; covers pid_lock, nextpid, cpus, stack0 slices, text; the spike's table lacked pid_lock); `fpin`/`Hinj`
against it (kvmmake's only text alias is the TRAMPOLINE page — not the spinlock pages; kstacks are data); `stk_i` :=
stack0 slices; a cold warm-up then WARM 2-hart run through `AxScRun3`'s joint tracer + `graph_of_sc` + `drive2`
producing the two complete rows for (a) and the `Hrow`/`row_cls_honest`/deps-bridge facts by vm_compute.
Stage D. `AxSpinT1*.v`: `xlay_xv6`, `allocpid_prefixes` (complete rows), Φ, `allocpid2_distinct_complete`,
certificates (a)(b)(c)(d) ((b) = J2's `ur3` race retargeted; (d) `Print Assumptions` = 5 Sail params + funext,
`va_first_read` shows unless assembled — optional parallel task).
Stage E. [ID-8]: hook + P-twins (4 workers, one per function) → conjunct 1 + cuts → Theorem 1 full; certificate (a-)
(B spinning while A is mid-CS) lands here.
Stage F. Theorem 2 (`allocpid_open`) + (a′)(b)(c′)(d).
Critical path: (am) → (aq) → (ap) wpd_allocpid → D → E → F; (rl), (po), C are off it.

## 8. Interface decisions (the list workers follow)
- ID-1 shapes are `list ritem` (+ `RB`, `RSc`), last item = pinned return fetch, continuation AT that position; (rl) publishes `AxSpinRs.v` (`hold_sh`, `Row_holding_of`, `rel_sh`) first.
- ID-2 named handles with explicit anchor positions, frames `True`; FRAG stays at the `sw nextpid` annotation.
- ID-3 reload annotations handed on as `RLbag i (rl_f …)`, callees' lists included; old lemmas get wrapper corollaries.
- ID-4 `Xx_amoswap` / `XAmo` exactly as in §2 (window HnoSplit, `FstRmwW`, fused RMW = one row item at S k).
- ID-5 `OAcq R1 R2` reads claim/fail off GD0's label and returns `NH i` on failure; `FstAcq_nh` from `NH i`; R1 = LK, R2 = RP, split by `wpd_annot_split`.
- ID-6 release class is ROW-PINNED (`RSc plk 4 WCrel`, `RB true true false true`); no boundary flag, no fused leaf; `row_cls_honest` as a pure row lemma.
- ID-7 4-byte private field leaves `Xx_ld4R`/`Xx_ld4G` with annotations; `_ann` twins of push_off/pop_off hand them on.
- ID-8 FULL-shape lemmas now; prefix tolerance = `RowShP` + `Des`/`HΨend` hook + P-twins with `Kpanic_j`, later stage.
- ID-9 Hdeps bridge and class honesty per certificate witness by vm_compute; general lemmas are named follow-ups.
- ID-10 Theorem 1 distinctness via joint adequacy + FRAG exclusivity (J2's route), complete rows first; Σ := xv6Σ; one real layout `xlay_xv6`; page table from KptTree.
