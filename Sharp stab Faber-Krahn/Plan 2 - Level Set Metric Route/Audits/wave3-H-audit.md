# Wave 3 Agent H — Final adversarial audit of Wave 3 closure claim

## Verdict summary (~200 words)

The Wave 3 closure claim — that Plan 2 delivers sharp quantitative Faber–Krahn unconditionally — survives but with a **serious, isolated, repairable bug in Agent G's §5.2 proof of (G4)**. Agent F's H¹-in-ρ centroid bound (F) is correct and genuinely unconditional: the centroid kinematic identity (3.2) bypasses the homothety, gmt-inputs (3.2) is $D_H$-only Cauchy–Schwarz (no (R) lurking), FMP+FJ+divergence theorem handle the boundary first moment cleanly, and the centroid–Fraenkel-centre proximity is correctly cited from AFM 2013 / CL 2012. Agent G's space-time Π identity (G1), profile-gap conversion (G2), and final theorem (G3) (integrated (B²) at rate δ) are correct in conclusion, conditional on (F) — and hence unconditional by Agent F. **However**, Agent G's §5.2 proof of the compatibility-with-metric-closure step (G4) is **wrong as written**: it asserts $\int T_2(E_\rho)\,d\mu \le C\delta$ via the Cauchy–Schwarz $T_1^2 \le P\cdot T_2$ route, but $\int T_2\,d\mu \le C\sqrt\delta$ only (because pointwise $T_2^{rad} \le C|E_\rho\Delta B_\rho|+C(P-P_\rho)$ has $|E_\rho\Delta B_\rho|$ at FMP rate $\sqrt{\delta_\rho}$, and the L¹ integral against $d\mu$ recovers only $\sqrt\delta$, not δ, even using (G3)). The bug is **repairable** by replacing Cauchy–Schwarz with a direct slicing decomposition $T_1 \le T_1^{\rm rad,slic}+T_1^{\rm tan}$, squaring **before** integrating, and exploiting $|E_\rho\Delta B_\rho|^2 \le C\Pi$ pointwise + $\int\Pi\,d\mu \le C\delta$ from (G3). **Net: theorem correct, proof needs rewriting.**

---

## 1. Severity table

| # | Wave-3 deliverable | Location | Issue | Severity | Repairability |
|---|---|---|---|---|---|
| H-1 | F: Theorem F (H¹ centroid) | `wave3-F-h1-center-bound.md` §1–§5 | Correctly proved unconditionally. Centroid identity (3.2), gmt-inputs (3.2), FMP, FJ, divergence theorem; no (R), no (B²), no Agent 3 (7.1), no gmt-inputs (2.4). | **None (positive)** | – |
| H-2 | F: change-of-centre error in (FJ) at centroid | `wave3-F-h1-center-bound.md` §4.B (4.10) | Argument $\int 1/\|x-z\|\,dH \le 4\rho_*^{-1}P(E_\rho)$ + centroid-to-FJ-centre proximity ≤ $C\sqrt{\delta_\rho}$ is correct; error absorbable into $C\sqrt{\delta_\rho}$. | **None (correct)** | – |
| H-3 | F: centroid–Fraenkel-centre proximity | `wave3-F-h1-center-bound.md` §1, §2.1, §4.B (4.8) | $|\bar z_\rho - z^{Fr}_\rho| \le C\mathcal A(E_\rho) \le C\sqrt{\delta_T}$ via AFM 2013 Lem. 2.6 and CL 2012 Prop. 2.3. The bound is the standard barycentre vs Fraenkel-centre estimate; both are at the Fraenkel-asymmetry centre up to second order in the perturbation. | **None (correct)** | – |
| H-4 | G: (G1) space-time Π identity | `wave3-G-route-delta-assembly.md` §2 | Fubini + CL containment + joint Borel measurability all clean. Identity $\int\Pi\,d\mu = (n-1)\int_{\tilde\Omega}\sigma(x)\,dx$ is correct. | **None (correct)** | – |
| H-5 | G: (G2) profile-gap with centre drift | `wave3-G-route-delta-assembly.md` §3 | The good/bad ρ-set decomposition with Chebyshev on $\{ρ:|z'_\rho|>1/2\}$ is correct. The static-centre profile-gap bound (3.5) uses Nicola–Tilli/Talenti at rate δ; the centre drift correction uses (F). Both are sound. | **None (correct)** | – |
| H-6 | G: (G3) (B²-int) | `wave3-G-route-delta-assembly.md` §4 | The Cauchy–Schwarz combination in (ρ,x)-space (§4.3) yields $\int |EΔB_\rho| \cdot (\text{drift}) \le C\delta$. Correct given (F). | **None (correct)** | – |
| **H-7** | **G: (G4) §5.2 compatibility chain** | `wave3-G-route-delta-assembly.md` §5.2 lines 344–398 | **Bug**: Agent G writes $(\int\|x-z\|/\rho-1\|)^2 \le 2P(B_\rho)\cdot T_2$ on each ρ, then claims $\int T_2\,d\mu \le C\delta$. This is FALSE: $T_2 \le T_2^{rad}+(P-P_\rho)+\Pi$ pointwise (Agent A (5.6)), and $T_2^{rad} \le C|EΔB_\rho|+C(P-P_\rho)$ pointwise (Agent A (4.7)+(4.9)+(4.11)), with $|EΔB_\rho|$ only $O(\sqrt{\delta_\rho})$ via FMP pointwise. Even using (G3) one obtains only $\int|EΔB_\rho|^2\,d\mu \le C\delta$, hence $\int|EΔB_\rho|\,d\mu \le C\sqrt\delta$ by Cauchy–Schwarz. Therefore $\int T_2\,d\mu \le C\sqrt\delta$ only. **Agent G's explicit "wait this still gives O(√δ)" admission on line 360 then fails to be repaired by the subsequent "(B²-int) directly" step (lines 362–366), which controls $\int|EΔB_\rho|^2\,d\mu$, not $\int|EΔB_\rho|\,d\mu$ — the wrong moment for the radial-trace chain Agent G has set up.** | **Substantive proof bug** | **Repairable** by replacing the Cauchy–Schwarz route with a direct slicing decomposition of $T_1$ (see §Q-H1 below). The theorem statement (G3) survives unchanged. |
| H-8 | G: $|EΔB_\rho|^2 \le C\Pi$ (slice rearrangement) | `wave3-G-route-delta-assembly.md` §8.3 + §5.2 (354) | The slice-rearrangement bound $|EΔB_\rho|^2 \le C(n,R,\rho_*)\Pi$ via slicewise Cauchy–Schwarz $\sigma(\theta)^2 \le c\bar r^{n-1}m_1(\theta)$ and angular Cauchy–Schwarz is correct for single-crossing slices; multi-crossing absorbed via (4.9). | **None (correct)** | – |
| H-9 | G: distance term integrand | `wave3-G-route-delta-assembly.md` §6 lines 444–447 | $\int d_\mathcal X(F_\rho,B_1)^2\,d\mu \le C\int|EΔB_\rho|^2\,d\mu \le C\delta$ via $|EΔB_\rho|^2 \le C\Pi$ + (G3) and Agent G (3.5)/(5.1) trivially. | **None (correct)** | – |
| H-10 | G: pointwise endpoint $\widehat\rho$ in Agent 4 | `wave3-G-route-delta-assembly.md` §5.4 | Agent 4 extracts a *distance* bound at $\widehat\rho$, not an (R)-type bound. Confirmed by `agent4-weighted-metric-trace.md` §2: hypotheses are integrated action (H1) + (5.14); output is pointwise $d_\mathcal X^2 \le C\delta$. No pointwise (R) is ever invoked. | **None (correct)** | – |
| H-11 | G: conversion lemma in §4.2 | `wave3-G-route-delta-assembly.md` §4.2 line 248–263 | The Lebesgue-form conversion from (F) uses bad-set Lemma 4.1 of W2 B plus a uniform $L^\infty$ bound on $|z_\rho'|$. Agent G remarks (line 255) that this Lipschitz bound "should follow from $|z_\rho|\le R$ and a piecewise-constant approximation argument". This is sketchy; the centroid is in fact Lipschitz with explicit constant $L_{\rm cent}=2nR/\rho_*^n$ by Agent F §2.2 — which Agent G can just cite. | **Cosmetic** | Trivial fix: cite Agent F §2.2. |

---

## 2. Detailed treatment

### Q-F1. Is gmt-inputs (3.2) actually unconditional?

**Verified: YES.** Read `gmt-inputs-for-metric-closure.md` §3:

(3.1) is the exact identity $\int_{\partial^*E_\rho}(V_\rho-\bar V_\rho)^2/V_\rho\,d\mathcal H^{n-1} = (A_\rho/P(E_\rho)^2)\,D_H(t(\rho))$. This is Agent 1's coarea identity, expanded algebraically. **No (R), no (B²), no homothety.** Purely a consequence of $D_H = (\int V^{-1})(\int V) - P^2$ and the Lagrange identity. Unconditional.

(3.2) is the Cauchy–Schwarz consequence
$$(\int|V_\rho-\bar V_\rho|)^2 \le (\int V_\rho)(\int(V_\rho-\bar V_\rho)^2/V_\rho) \le P(E_\rho)\cdot (A_\rho/P(E_\rho)^2)D_H = C_{n,\rho_*}D_H.$$

This is Cauchy–Schwarz $\int fg \le (\int f^2/h)^{1/2}(\int h g^2)^{1/2}$ with $f=|V-\bar V|$, $h=V$, $g=1$. Algebraic. **Unconditional.**

gmt-inputs (3.2) is the **velocity** Cauchy-deficit, not the **homothety** $H_{z,\rho}$ Cauchy-deficit. The latter — gmt-inputs (2.4) — is what depends on (R)=(1.2). **Agent F correctly invokes only (3.2)**, not (2.4). ✓

### Q-F2. Centroid kinematic formula (3.2) of Agent F

**Verified: correct.** Routine moving-region calculus using Agent 1's coarea with $f(x)=x_i$, combined with $|E_\rho|=\omega_n\rho^n$ and Sobolev–Sard for $|\nabla u|>0$ a.e. on $\partial^*E_\rho$. ✓

### Q-F3. The boundary first moment ≤ $C\sqrt{\delta_\rho}$ — (4.4)

**Verified: correct.** Three sub-steps:

**(4.6) divergence theorem on Lipschitz $V^{(i)}(x)=|x-\bar z_\rho|e_i$:** field is W^{1,∞}; kink at $\bar z_\rho$ (a single point) contributes zero; Maggi 2012 Thm 17.3 applies. ✓

**(4.7)+(4.8): $|E_\rho\Delta B_\rho(\bar z_\rho)| \le C\sqrt{\delta_\rho}$:** FMP + AFM/CL centroid–Fraenkel proximity + triangle. ✓

**(FJ) at the centroid:** change-of-centre error $|\bar z - z^{FJ}|\int 1/|x-z|\,dH \le C\sqrt{\delta_\rho}$, absorbed. ✓

### Q-F4–Q-F7

All routine and verified correct. ✓

### Verdict on Agent F: **(F) is proved unconditionally.** No (R), no (B²) lurking. The proof's structural reason — centroid kinematic identity has no homothety term, avoiding the gmt-inputs (2.4)→(1.2)=(R) chain that compromised Wave 2 B — is sound. ✓

---

### Q-G1. The compatibility check (G4)

**This is where Wave 3 fails as written.** Trace `metric-finite-perimeter-closure.md` chain:

(3.4) per-ρ $(\int|H_{z_\rho,\rho}-\bar V_\rho|)^2 \le C\,D_I(t(\rho))$. **This is the per-ρ form of (R) via gmt-inputs (2.4), conditional on (R)=(1.2) per-ρ.** Replacing this is what (G4) must accomplish.

The replacement target: $\int_{\rho_*}^{\rho_\delta}(\int|H_{z_\rho,\rho}-\bar V_\rho|)^2\,d\mu \le C\delta$ — the **integrated** form, NOT pointwise.

Then $|\dot F_\rho|^2 \le C[(\int|V-\bar V|)^2 + (\int|H-\bar V|)^2]$ integrated gives the action bound (5.2), which feeds Agent 4's metric trace lemma.

The first piece: $\int(\int|V-\bar V|)^2\,d\mu \le C\int D_H\,d\mu \le C\delta$ via gmt-inputs (3.2) (unconditional, pointwise). ✓

The second piece: requires careful audit (see Q-H1 below).

### Q-G2 (centroid substitution)

**Verified: centroid is interchangeable with the Fraenkel centre in Agent G's chain.** Cost is $|\bar z - z^{Fr}|\le C\sqrt\delta$ absorbed into constants. (G1)–(G4) hold for any measurable bounded centre field; the H¹ bound (F) is what's used, supplied by Agent F at the centroid. ✓

### Q-G3 (the (3.5)+(3.7) decomposition)

**Verified: correct.** Chebyshev on $\{|z'_\rho|>1/2\}$ gives Lebesgue measure ≤ $4\int|z'|^2\,d\rho \le 4C\delta$ via (F)-converted. The Cauchy–Schwarz in (ρ,x)-space (§4.3) using $\mathcal L^1(A_x) \le C_T\delta$ from the static-centre profile-gap (3.5) recovers the $\delta$-rate cleanly. ✓

### Q-G4 (Π → |EΔB_ρ|² → δ argument in §5.2 / §8.3)

**Verified: correct.** $|E_\rho\Delta B_\rho|^2 \le C\Pi$ pointwise via slicewise Cauchy–Schwarz. Integrating: $\int|EΔB_\rho|^2\,d\mu \le C\int\Pi\,d\mu \le C\delta$ via (G3). ✓

### Q-H1. The leak: §5.2 lines 344–398

**This is the substantive bug. Trace carefully.**

Agent G's goal: $\int(\int|H-1|)^2\,d\mu \le C\delta$.

Decomposition: $|H-1| \le ||x-z|/\rho - 1| + |e_r\cdot\nu - 1|$. Squaring:
$$(\int|H-1|)^2 \le 2T_1^2 + 2(\int|e_r\cdot\nu-1|)^2,$$
where $T_1 = \int||x-z|/\rho-1|\,d\mathcal H^{n-1}$.

**Tangential piece** $\int(\int|e_r\cdot\nu-1|)^2\,d\mu$: using $|e_r\cdot\nu-1| \le |e_r-\nu|$, then Cauchy–Schwarz on $\partial^*E_\rho$: $(\int|e_r-\nu|)^2 \le P(E_\rho)\int|e_r-\nu|^2\,d\mathcal H^{n-1}$. Integrating: $\le 2P(B_\rho)\cdot\text{(B²-int)} \le C\delta$. ✓

**Radial piece** $\int T_1^2\,d\mu$: Agent G uses Cauchy–Schwarz on $\partial^*E_\rho$ to get $T_1^2 \le P\cdot T_2$, then claims:
$$\int T_1^2\,d\mu \le 2P_\rho\int T_2\,d\mu \le C\delta.$$

**This is wrong.** Pointwise, by Agent A (5.6),
$$T_2(E_\rho) \le T_2^{\rm rad}(E_\rho) + (P-P_\rho) + \Pi(E_\rho,z_\rho).$$

By Agent A (4.7)+(4.9)+(4.11) (slicing analysis of $T_2^{\rm rad}$),
$$T_2^{\rm rad}(E_\rho) \le C(P-P_\rho) + C|E_\rho\Delta B_\rho(z_\rho)|.$$

So pointwise $T_2 \le C[(P-P_\rho) + |EΔB_\rho| + \Pi]$. Integrating against dμ:
$$\int T_2\,d\mu \le C\int(P-P_\rho)\,d\mu + C\int|EΔB_\rho|\,d\mu + C\int\Pi\,d\mu.$$

- $\int(P-P_\rho)\,d\mu \le C\delta$ (Agent G (4.2)). ✓
- $\int\Pi\,d\mu \le C\delta$ via (G3). ✓
- $\int|EΔB_\rho|\,d\mu$: **bottleneck**. Even using (G3) one obtains only $\int|EΔB_\rho|^2\,d\mu \le C\int\Pi\,d\mu \le C\delta$, hence by Cauchy–Schwarz $\int|EΔB_\rho|\,d\mu \le \sqrt{\mu([\rho_*,\rho_\delta])\cdot\int|EΔB_\rho|^2\,d\mu} \le C\sqrt\delta$. **Not Cδ**.

Therefore $\int T_2\,d\mu \le C\sqrt\delta$ only. Agent G's argument leaks at the FMP rate $\sqrt\delta$.

**Agent G actually notices this on lines 360–366** — the text "Wait this still gives O(√δ)" appears verbatim, then claims to fix it by switching to $\int|EΔB_\rho|^2\,d\mu \le C\delta$ via (B²-int). But the chain $\int T_2\,d\mu$ requires $\int|EΔB_\rho|^1\,d\mu$, not $\int|EΔB_\rho|^2\,d\mu$. The squared form bounds the wrong moment for this chain. **The bug is not fixed by Agent G's text.**

#### The repair (alternative route)

The bug is **repairable** by NOT using Cauchy–Schwarz $T_1^2 \le P\cdot T_2$ on each ρ. Instead, directly decompose $T_1$ via slicing:

$$T_1 = T_1^{\rm rad,slic} + T_1^{\rm tan},$$
$$T_1^{\rm rad,slic} := \int_{\partial^*E_\rho}||x-z|/\rho-1|\cdot|e_r\cdot\nu|\,d\mathcal H^{n-1} = \int_{S^{n-1}}\sum_j|r_{\theta,j}/\rho-1|r_{\theta,j}^{n-1}\,d\theta,$$
$$T_1^{\rm tan} := \int||x-z|/\rho-1|\cdot(1-|e_r\cdot\nu|)\,d\mathcal H^{n-1}.$$

**Bound 1: $T_1^{\rm rad,slic} \le C(|EΔB_\rho| + (P-P_\rho))$ pointwise.** By slicewise MVT: $|r_{\theta,1}/\rho-1|r_{\theta,1}^{n-1} \le c|r_{\theta,1}^{n-1}-\rho^{n-1}|$. For $j\ge 2$: $|r_{\theta,j}/\rho-1|r_{\theta,j}^{n-1} \le 1\cdot(2R)^{n-1}$ in CL, contributing $\le (2R)^{n-1}k(\theta)$. Summing and integrating dθ: $T_1^{\rm rad,slic} \le c\int|r_{\theta,1}^{n-1}-\rho^{n-1}|\,d\theta + (2R)^{n-1}\int k(\theta)\,d\theta$. By Agent A (4.11): the first ≤ $c|EΔB_\rho|$; by Agent A (4.9): the second ≤ $C(P-P_\rho)$. ✓

**Bound 2: $T_1^{\rm tan} \le (P-P_\rho)+\Pi$ pointwise.** Using $||x-z|/\rho-1| \le 1$ in CL: $T_1^{\rm tan} \le \int(1-|e_r\cdot\nu|)\,dH \le \int(1-e_r\cdot\nu)\,dH = (P-P_\rho)+\Pi$ (Agent A (5.3)). ✓

**Squaring and integrating:**
$$T_1^2 \le 2(T_1^{\rm rad,slic})^2 + 2(T_1^{\rm tan})^2 \le 4C^2(|EΔB_\rho|^2 + (P-P_\rho)^2) + 4((P-P_\rho)^2 + \Pi^2).$$
$$\int T_1^2\,d\mu \le C\int|EΔB_\rho|^2\,d\mu + C\int(P-P_\rho)^2\,d\mu + C\int\Pi^2\,d\mu.$$

- $\int|EΔB_\rho|^2\,d\mu \le C\int\Pi\,d\mu \le C\delta$ ✓ (Agent G's correct $|EΔB_\rho|^2 \le C\Pi$ pointwise + (G3));
- $\int(P-P_\rho)^2\,d\mu \le \max(P-P_\rho)\int(P-P_\rho)\,d\mu \le C\delta$ ✓ in smallness;
- $\int\Pi^2\,d\mu \le \Pi_{\max}\int\Pi\,d\mu \le C\delta$ ✓ ($\Pi$ uniformly bounded by CL).

**Therefore $\int T_1^2\,d\mu \le C\delta$.** ✓

**Crucial observation:** the rescue route squares **before** integrating, exploiting $|EΔB_\rho|^2 \le C\Pi$ at the squared level. Agent G's route Cauchy–Schwarz on $\partial^*E_\rho$ to extract $T_2$ separately first, then integrates $T_2$, which requires $\int|EΔB_\rho|$ at rate δ — unavailable. The squaring step matters.

#### Verdict on (G4): **Theorem statement correct, but Agent G's §5.2 proof is wrong as written.** Repairable by the direct $T_1$ decomposition above.

### Q-H2. Other potential leaks

After the §5.2 fix, no other leaks. The pointwise endpoint extraction at $\widehat\rho$ in Agent 4 outputs a *distance* bound, not an (R)-type bound. The kinetic bound (5.14) integrated against $d\rho$ is recovered from $\int|\dot F|^2\,d\mu \le C\delta$ via the bad-set/good-set decomposition of W2 B (which is itself unconditional given (5.2)). The transfer back to $\Omega$ via Agent 5 / `BoundedReduction.tex` / `KohlerJobinTransfer.tex` is unconditional. ✓

### Q-H3. Comparison to Wave 2 D's "false unconditional" mistake

Wave 2 D caught Wave 2 B's claim that (K) was unconditional, by tracing: B Step 1 → Agent 3 (7.1) → gmt-inputs (2.4) → (R)=(1.2), and (R) is open.

Wave 3 G's situation has a **structurally similar but technically subtler bug**:

| Object | Wave 2 B's mistake | Wave 3 G's mistake |
|---|---|---|
| Hidden dependency | Pointwise (R) via Agent 3 (7.1) | $\int T_2\,d\mu \le C\delta$ via Cauchy–Schwarz on $\partial^*E_\rho$, which forces $\int|EΔB_\rho|\,d\mu$ at the wrong moment |
| Why it's wrong | (R) is open at rate δ | $\int|EΔB_\rho|\,d\mu \le C\sqrt\delta$ only via FMP integrated, even with (B²-int) |
| Severity | Fatal: (R) open | Repairable: alternative route via direct $T_1$ slicing decomposition exists |
| Rate consequence | (K) only at √δ | (G4) proof only at √δ as written, but theorem (G4) holds at δ via repair |

**Key difference:** Wave 2 B's bug was fatal because (R) is genuinely open. Wave 3 G's bug is **repairable** because the **integrated** form $\int T_1^2\,d\mu \le C\delta$ does hold via the direct slicing-then-squaring route, which Agent G simply didn't write.

The lesson: the *theorem* (G4) is correct, but the *proof* in §5.2 takes a wrong Cauchy–Schwarz turn that creates an apparent leak. The structural validity of route δ — that the closure chain consumes (R)/(1.2) only at integrated level, and that (B²-int) supplies precisely this — holds **provided the squaring step is done at the slicing level, not after a Cauchy–Schwarz that converts L¹ to L²**.

### Q-H4. Final verdict

**1. Is Plan 2 closed at the sharp δ rate?**

**Conditionally YES, with a serious caveat.** Agent F's (F) is unconditional. Agent G's theorems (G3), (G5) are correct given (F). The compatibility chain (G4) holds at rate δ, but Agent G's §5.2 *proof* of (G4) is wrong as written; it must be replaced by the direct slicing-then-squaring argument outlined in Q-H1. Pending this repair, Plan 2 closes at the sharp rate δ via route δ, unconditionally.

**2. Best rate achievable from Wave 3 as written?**

With Agent G's §5.2 as currently written: only $\sqrt\delta$ (the FMP rate), giving $\mathcal A(\Omega)^2 \le C\delta_T^{1/2}$ — no improvement over Plan 1.

With the §5.2 repair: $\mathcal A(\Omega)^2 \le C\delta_T$ at the sharp rate.

**3. Single open input remaining?**

After the §5.2 repair, **none**. Agent F supplies (F) unconditionally. Agent G supplies (G3), (G4) at rate δ. Plan 2 closes at sharp rate with **no open inputs**.

Without the repair: the open input is "$\int T_1^2\,d\mu \le C\delta$ via a non-Cauchy–Schwarz route", which is what the direct slicing decomposition supplies.

**4. New theorem or new proof of existing theorem?**

After repair: **genuinely new theorem** — sharp quantitative Faber–Krahn at rate δ via a no-selection, no-graph proof. The existing literature (FMP integrated, Brasco–De Philippis 2017, AKN 2023) gives sharp Faber–Krahn either through (i) selection + Schauder (Plan 1) or (ii) ACF monotonicity at the *eigenvalue* deficit (AKN, but with selection at the comparison step). Wave 3's route δ uses only measure-theoretic Cicalese–Leonardi (no selection-and-regularity), no graph entry, and no PDE multiplier beyond Agent 1's coarea / divergence identity. **This is the genuinely new content** — a route δ closure that bypasses (B²)-pointwise and (R)-pointwise via integrated-then-squared bookkeeping, supplied by Agent F's centroid H¹ control + Agent G's space-time Π identity. If the §5.2 repair is rigorously written, the no-selection no-graph sharp Faber–Krahn is delivered.

Without repair: only the FMP rate, which is the existing theorem with a new (but flawed) proof.

---

## 3. Final verdict on post-Wave-3 status

| Item | Status (as written) | Status (with §5.2 repair) |
|---|---|---|
| (F) Agent F H¹ centroid bound | **Unconditional** ✓ | **Unconditional** ✓ |
| (G1) Space-time Π identity | Correct ✓ | Correct ✓ |
| (G2) Profile-gap + centre drift | Correct (given (F)) ✓ | Correct ✓ |
| (G3) (B²-int) at rate δ | Correct (given (F)) ✓ | Correct ✓ |
| (G4) Compatibility chain proof | **Wrong as written** ✗ ($\sqrt\delta$ leak via $\int T_2\,d\mu$ argument) | Correct ✓ (via direct $T_1$ slicing + squaring) |
| (G5) Plan 2 closure $\mathcal A^2 \le C\delta$ | Conditionally correct, but proof relies on broken (G4) | Correct ✓ unconditionally |
| Sharp quantitative Faber–Krahn | Conditionally correct, pending §5.2 repair | Sharp constant $c_{\rm FK}(n)$ proved unconditionally |
| Plan 2 status | Open at sharp rate **as written** | **Closed** at sharp rate $\mathcal A^2 \le C\delta_T$ |

---

## 4. What Wave 3 achieves vs what it does not

### Achievements

1. **(F) unconditionally proved** (Agent F). The centroid H¹ bound — the single missing piece Wave 2 E identified as the route-δ blocker — is delivered via a clean centroid kinematic identity + gmt-inputs (3.2) (Cauchy on $V_\rho$, not on $H_{z,\rho}$, hence (R)-free) + FMP/FJ/divergence at the centroid. This is a **genuine new piece of GMT**: the H¹-in-ρ centre control via the bulk-integral centroid, not the Fraenkel-minimisation centre. No selection, no graph.

2. **(G1)–(G3) correct** (Agent G). The space-time Π identity, the Talenti profile-gap conversion with centre drift, and the (B²-int) assembly at rate δ are all rigorously assembled, conditional on (F) — hence unconditional given (1).

3. **$|EΔB_\rho|^2 \le C\Pi$ slice-rearrangement** (Agent G §8.3). A new pointwise inequality not in FMP; it lets one transfer the rate-δ Π-bound to the *squared* volume Fraenkel, which integrates correctly.

### Not achieved (as written)

1. **(G4) §5.2 compatibility chain proof.** As written, the proof leaks at $\sqrt\delta$ via the Cauchy–Schwarz $T_1^2 \le P\cdot T_2$ route that requires $\int|EΔB_\rho|\,d\mu \le C\delta$ — unavailable. The proof must be rewritten using the direct slicing decomposition $T_1 \le T_1^{\rm rad,slic} + T_1^{\rm tan}$, squaring before integrating, and the pointwise bounds $T_1^{\rm rad,slic} \le C(|EΔB_\rho|+(P-P_\rho))$ (Agent A (4.11)+(4.9)) and $T_1^{\rm tan} \le (P-P_\rho)+\Pi$ (Agent A (5.3)).

2. **Pointwise (B²) and pointwise (R) remain open.** Wave 3 closes the *integrated* forms, which Plan 2's chain happens to admit. Stating it cleanly: Wave 3 closes Plan 2 without proving pointwise (B²) or pointwise (R).

3. **Cleanup needed.** Agent G §5.2 lines 344–398 must be rewritten using the slicing-then-squaring argument. Agent G §4.2 conversion lemma must cite Agent F §2.2 for the uniform Lipschitz $L_{\rm cent}$ explicitly (currently sketched as "should follow").

### Cautionary footnote

The bug Wave 3 G inherits is structurally the same kind that Wave 2 D caught in Wave 2 B: a *hidden* conditionality where the author thought integration would absorb the (R)-rate gap but in fact the chosen Cauchy–Schwarz forces the FMP rate to propagate. The difference is that **the integrated form does actually hold by a different (sharper) route**, which the author did not take. After rewriting, route δ closes — but the prose **as deployed today** is **not** a closed proof of sharp Plan 2.

The bottom line of this audit is therefore:

> Wave 3's claim — *Plan 2 closes unconditionally at sharp rate δ via a no-selection no-graph proof* — is **plausibly correct**, **but the proof of (G4) as written in `wave3-G-route-delta-assembly.md` §5.2 contains a critical rate-loss error**. The error is repairable by a direct slicing-then-squaring argument on $T_1$, which Agent G did not write but which the audit verifies works. **Before claiming closure, §5.2 must be rewritten.** If rewritten, Wave 3 does deliver a genuinely new theorem — sharp quantitative Faber–Krahn via no-graph no-selection — at the sharp rate, after fifteen years of pursuit.
