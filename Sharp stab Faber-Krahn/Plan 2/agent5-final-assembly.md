# Agent 5 — Bounded reduction and final assembly: conditional sharp Faber–Krahn

**Author:** Agent 5, Wave 1 audit of Plan 2 (metric level-set route).
**Date:** 2026-05.
**Status:** Conditional on Conjecture 3.6 (Agent 2) and bound (5.14) (Agent 4); structurally complete modulo those two inputs and the Wave 1 results of Agents 1 and 3.

This note assembles the chain

  Plan 2 metric route  →  Bounded reduction  →  Kohler–Jobin transfer

into a single conditional sharp quantitative Faber–Krahn theorem, with every dependency made explicit. It does **not** attempt a proof of Conjecture 3.6 or of bound (5.14); those are the open items that Wave 2 must address.

---

## 1. The three intermediate theorems

### 1.1 Plan 2 metric output (bounded class)

**Theorem A (bounded sharp Saint–Venant via metric Plan 2).**
*Let* $n\ge 2$, $R\ge 2$, $\rho_*\in(0,1)$ *fixed. Assume:*

- **(I1)** Agent 1's finite-perimeter level-set deficit identity holds: for every open $\Omega$ with $|\Omega|<\infty$,
$$
\tfrac{2}{|\Omega|}\bigl(E(\Omega)-E(B)\bigr)=\tfrac{1}{|\Omega|}\int_0^{\|u\|_\infty}\frac{D_H(t)+D_I(t)}{n^2\omega_n^{2/n}m(t)^{1-2/n}}\,dt,
$$
on a.e. reduced-boundary level (`Plan 2/agent1-finite-perimeter-identity.md`, Thm §0).
- **(I2)** Agent 3's metric first variation modulo translations:
$$
|\dot F_\rho|_{\mathcal X}\le C_{n,\rho_*,R}\inf_{a\in\mathbb R^n}\int_{\partial^*E_\rho}\bigl|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho\bigr|\,d\mathcal H^{n-1}
\quad\text{for a.e.\ }\rho,
$$
(`Plan 2/agent3-metric-first-variation.md`, Thm §2 (T)).
- **(C3.6)** Conjecture 3.6 of `Plan 2/agent2-homothetic-velocity-defect.md`:
$$
\int_{\partial^*E}\frac{|e_r\!\cdot\!\nu_E|}{|x-z_E|^{n-1}}\,d\mathcal H^{n-1}-n\omega_n\le C_{n,\rho_*,R}\bigl(P(E)-P(B_\rho)\bigr).
$$
Equivalently the radial $L^1$-trace (R) and hence the homothetic velocity defect lemma (3.2) of `Plan 2/metric-finite-perimeter-closure.md`.
- **(K5.14)** The integrated $L^2(d\rho)$ kinetic bound of `Plan 2/agent4-weighted-metric-trace.md`, §1:
$$
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|(\rho)^2\,d\rho\le C'\delta,
$$
or equivalently the second-order profile-gap refinement $M-c=O(\delta)$.

*Then for every open $\Omega\subset B_R$ with $|\Omega|=\omega_n$,*
$$
\boxed{\quad\mathcal A(\Omega)^2\le C_{\rm P2}(n,R)\,\delta_T(\Omega),\qquad \delta_T(\Omega):=E(\Omega)-E(B_1).\quad}
\tag{A}
$$

*Source.* This is (6.1) of `Plan 2/metric-finite-perimeter-closure.md`, conditioned on the two open inputs above. The closure chain is (2.4)+(3.4)$\Rightarrow$(4.2)$\Rightarrow$(5.2)$\Rightarrow$(5.3)$\Rightarrow$(6.1). The Agent 4 trace step (5.3) is exactly the application of the weighted metric trace lemma, which itself depends on (K5.14).

### 1.2 Bounded reduction (Final block)

**Theorem B (Bounded reduction; `Final/BoundedReduction.tex`, Thm. 5.1).**
*For every $n\ge 2$, if the bounded-class sharp Saint–Venant inequality $(A)$ holds with constant $C_{\rm P2}(n,R_*(n))$ at the dimensional radius*
$$
R_*(n):=\max\{d(n),2\},
$$
*where $d(n)$ is the BDV Lemma 5.3 diameter constant, then for every open $\Omega\subset\mathbb R^n$ with $|\Omega|=\omega_n$,*
$$
\boxed{\quad E(\Omega)-E(B_1)\;\ge\;c_{\rm SV}^{\rm glob}(n)\,\mathcal A(\Omega)^2,\quad}
\tag{B}
$$
*with*
$$
c_{\rm SV}^{\rm glob}(n)=\min\Bigl\{c_{\rm near}^{\rm glob}(n),\,\omega_n^{(n+2)/n}\delta(n)/16\Bigr\},
$$
*and the near-branch constant*
$$
c_{\rm near}^{\rm glob}(n)=\frac{\omega_n^{(n+2)/n}}{4C_9(n)\bigl(1/\widetilde c_{\rm SV}(n)+C_9(n)\bigr)},\qquad \widetilde c_{\rm SV}(n)=\omega_n^{-(n+2)/n}c_{\rm SV}(n,R_*(n)).
$$
*Here $c_{\rm SV}(n,R)$ is the bounded constant produced by either the upstream `SaintVenantAssembly` block (Plan 1) or — in the present chain — by Theorem A applied at $R=R_*(n)$. $C_9(n),\delta(n),d(n)$ are BDV Lemmas 5.1–5.3 constants.*

*Source.* `Final/BoundedReduction.tex`, Theorem 5.1 (`thm:main`); the consumption of the upstream bounded constant at $R=R_*(n)$ appears in the proof of Lemma 4.2 (`lem:near`).

### 1.3 Kohler–Jobin transfer (Final block)

**Theorem C (Kohler–Jobin transfer; `Final/KohlerJobinTransfer.tex`, Thm. 6.1).**
*Assume sharp Saint–Venant in energy form: there exists $c_{\rm SV}(n)>0$ with*
$$
E(\Omega)-E(B^*)\ge c_{\rm SV}(n)\Bigl(\frac{|B^*|}{|B_1|}\Bigr)^{(n+2)/n}\mathcal A(\Omega)^2,\qquad 0<|\Omega|=|B^*|<\infty.
$$
*Then*
$$
\boxed{\quad\Bigl(\frac{|\Omega|}{|B_1|}\Bigr)^{2/n}\bigl(\lambda_1(\Omega)-\lambda_1(B^*)\bigr)\ge c_{\rm FK}(n)\,\mathcal A(\Omega)^2,\quad}
\tag{C}
$$
*with*
$$
c_{\rm FK}(n)=\min\!\left\{\frac{4L_n\,c_{\rm SV}(n)}{(n+2)T_n},\;\frac{L_n(2^{2/(n+2)}-1)}{4}\right\},
$$
*where $L_n=\lambda_1(B_1)$, $T_n=T(B_1)=\omega_n/(n(n+2))$.*

*Source.* `Final/KohlerJobinTransfer.tex`, Theorem 6.1 (`thm:main`); see also `Plan 1/faber-krahn-transfer.md` §3.

---

## 2. The final conditional theorem

**Theorem D (sharp quantitative Faber–Krahn via the metric Plan 2 route — conditional).**
*Let $n\ge 2$. Conditional on:*

1. *Conjecture 3.6 of `Plan 2/agent2-homothetic-velocity-defect.md` (the radial L¹-trace estimate (R)/(C3.6) closing the homothetic velocity defect lemma);*
2. *The auxiliary kinetic bound (5.14) of `Plan 2/agent4-weighted-metric-trace.md` (equivalently the second-order profile-gap refinement $M-c=O(\delta)$);*
3. *The Lipschitz-truncation flux identity of `Plan 2/agent1-finite-perimeter-identity.md` (established);*
4. *The metric first variation theorem (T) of `Plan 2/agent3-metric-first-variation.md` (established);*

*there exists a dimensional constant $c_{\rm FK}(n)>0$ such that, for every open $\Omega\subset\mathbb R^n$ with $0<|\Omega|<\infty$,*
$$
\boxed{\quad\Bigl(\frac{|\Omega|}{|B_1|}\Bigr)^{2/n}\bigl(\lambda_1(\Omega)-\lambda_1(B^*)\bigr)\ge c_{\rm FK}(n)\,\mathcal A(\Omega)^2.\quad}
\tag{D}
$$
*The exponent $2$ is sharp, saturated by ellipsoidal perturbations of $B^*$.*

*Proof of (D) from (A) + (B) + (C).*

*Step 1.* Conditional inputs (1)–(4) supply Theorem A with constant $C_{\rm P2}(n,R)$ for every $R\ge 2$ (and in particular for $R=R_*(n)$). Setting
$$
c_{\rm SV}(n,R):=\omega_n^{(n+2)/n}\bigl/C_{\rm P2}(n,R)\quad\text{i.e.}\quad E-E(B_1)\ge c_{\rm SV}(n,R)\mathcal A^2\text{ on }\{\Omega\subset B_R,|\Omega|=\omega_n\},
$$
Theorem A becomes a valid input to `Final/BoundedReduction.tex` (replacing Theorem 1.1 there, which would otherwise be supplied by `Final/SaintVenantAssembly.tex`).

*Step 2.* Apply Theorem B at $R_*(n)$. The bounded reduction internalises the $R$-dependence and emits the dimensional global constant $c_{\rm SV}^{\rm glob}(n)>0$. After Remark 3.4 (`rem:scaling`) of `BoundedReduction.tex`, the global statement holds at arbitrary volume in the scale-invariant form
$$
E(\Omega)-E(B^*)\ge c_{\rm SV}^{\rm glob}(n)\Bigl(\frac{|B^*|}{|B_1|}\Bigr)^{(n+2)/n}\mathcal A(\Omega)^2,\qquad 0<|\Omega|=|B^*|<\infty.
$$
This is exactly the hypothesis of Theorem C with $c_{\rm SV}(n)=c_{\rm SV}^{\rm glob}(n)$.

*Step 3.* Apply Theorem C. The output is (D) with
$$
c_{\rm FK}(n)=\min\!\left\{\frac{4L_n\,c_{\rm SV}^{\rm glob}(n)}{(n+2)T_n},\;\frac{L_n(2^{2/(n+2)}-1)}{4}\right\}.
$$
$\square$

---

## 3. Constants chain with R-dependence tracking

| Stage | Constant | R-dependence | Source |
|-------|----------|--------------|--------|
| Agent 1 identity | (none introduced) | n only | `agent1-finite-perimeter-identity.md` Thm §0 |
| Agent 3 first variation | $C_{n,\rho_*,R}$ | n, $\rho_*$, R | `agent3-metric-first-variation.md` Thm §2 |
| Agent 2 hom. velocity defect | $C_{n,\rho_*,R}\sim R^{n-1}$ | n, $\rho_*$, R | `agent2-homothetic-velocity-defect.md` (cond. C3.6) |
| Agent 4 weighted trace | $C_*(n,R,\rho_*,\kappa,M,c)$ | n, R, kinematic params | `agent4-weighted-metric-trace.md` Thm §2 |
| Plan 2 output (A) | $C_{\rm P2}(n,R)$ | n, R | `metric-finite-perimeter-closure.md` (6.1) |
| Plan 2 ↔ Final reciprocal | $c_{\rm SV}(n,R)=\omega_n^{(n+2)/n}/C_{\rm P2}(n,R)$ | n, R | reformulation |
| Bounded-reduction radius | $R_*(n)=\max\{d(n),2\}$ | n only | `BoundedReduction.tex` (4.1) |
| BDV truncation | $C_9(n),\delta(n),d(n)$ | n only | `BoundedReduction.tex` Lemma 3.1 |
| Near-branch glob const | $c_{\rm near}^{\rm glob}(n)=\omega_n^{(n+2)/n}/\bigl[4C_9(1/\widetilde c_{\rm SV}+C_9)\bigr]$ | **n only** | `BoundedReduction.tex` (4.6) |
| Far-branch glob const | $\omega_n^{(n+2)/n}\delta(n)/16$ | n only | `BoundedReduction.tex` Lemma 3.1 |
| **Global SV constant** | $c_{\rm SV}^{\rm glob}(n)$ | **n only** | `BoundedReduction.tex` (5.1) |
| KJ multiplier | $2L_n/((n+2)T_n)=2nL_n/\omega_n$ | n only | `KohlerJobinTransfer.tex` §5 |
| KJ large-deficit gap | $L_n(2^{2/(n+2)}-1)/4$ | n only | `KohlerJobinTransfer.tex` Lemma 6 |
| **Final FK constant** | $c_{\rm FK}(n)=\min\{4L_n c_{\rm SV}^{\rm glob}/((n+2)T_n),\,L_n(2^{2/(n+2)}-1)/4\}$ | **n only** | (cfk) of `KohlerJobinTransfer.tex` |

**R-dependence verdict.** The R-dependence accumulated by Theorems A and its sub-pieces (Agents 2, 3, 4) is internalised in `BoundedReduction.tex` by evaluating the bounded-class input at the dimensional radius $R_*(n)$. The output $c_{\rm SV}^{\rm glob}(n)$ and thus $c_{\rm FK}(n)$ depend only on $n$. **No R-leakage** is observed.

There is one bookkeeping subtlety: the Plan 2 internal parameter $\rho_*\in(0,1)$ is *not* an external degree of freedom — it is chosen once and for all (e.g. $\rho_*=1/2$) as part of the foliation argument, and absorbed into the dimensional constants on the same footing as $R$. With $\rho_*$ fixed and $R=R_*(n)$ dimensional, the entire chain collapses to dimension dependence only.

---

## 4. Normalisation conventions

| Convention | Choice | Where it lives |
|------------|--------|----------------|
| Torsion energy sign | $E(\Omega)=-T(\Omega)/2$, so $E(\Omega)\ge E(B^*)$ and $\delta_T(\Omega):=E(\Omega)-E(B^*)\ge 0$ | `BoundedReduction.tex` §1; `KohlerJobinTransfer.tex` §1 |
| Saint–Venant deficit (energy form) | $\delta_T(\Omega)=E(\Omega)-E(B^*)=\tfrac12\bigl(T(B^*)-T(\Omega)\bigr)$ | `metric-finite-perimeter-closure.md` §0; KJ Rmk on energy norm. |
| Torsion deficit (T form) | $\delta_{\rm SV}(\Omega):=T(B^*)-T(\Omega)=2\,\delta_T(\Omega)$ | `KohlerJobinTransfer.tex` §4 |
| Volume normalisation | $|\Omega|=|B^*|$; for proofs in Final we take $|\Omega|=\omega_n$, and the master statement is restored by scale-invariance of $D(\Omega):=E(\Omega)|\Omega|^{-(n+2)/n}-E(B_1)|B_1|^{-(n+2)/n}$ | `BoundedReduction.tex` §1, Rmk 5.2 |
| Fraenkel asymmetry | $\mathcal A(\Omega):=\inf_{x_0}|\Omega\Delta(x_0+B^*)|/|B^*|\in[0,2)$, scale-invariant | `BoundedReduction.tex` §1; `KohlerJobinTransfer.tex` §1; `metric-finite-perimeter-closure.md` (implicit) |
| Volume radius parametrisation | $|E_\rho|=\omega_n\rho^n$, $\rho\in[\rho_*,1]$ | `metric-finite-perimeter-closure.md` §0 |
| Cutoff radius | $\rho_\delta=1-\kappa\sqrt{\delta_T(\Omega)}$ | `metric-finite-perimeter-closure.md` §5 |
| Metric space | $\mathcal X=\{1_A:|A|<\infty\}/\mathbb R^n$; $d_{\mathcal X}([A],[C])=\inf_a|A\Delta(C+a)|$ | `agent3-metric-first-variation.md` §1 |
| Spectral deficit (FK output) | scale-invariant form $(|\Omega|/|B_1|)^{2/n}(\lambda_1(\Omega)-\lambda_1(B^*))$ | `KohlerJobinTransfer.tex` (fkout) |
| Sign of spectral gap | $\lambda_1(\Omega)-\lambda_1(B^*)\ge 0$ (Faber–Krahn); equality iff $\Omega=B^*$ up to translation/null set | `KohlerJobinTransfer.tex` §2 |
| KJ scaling exponent | $\beta=(n+2)/2$; $\Psi(\Omega)=T(\Omega)\lambda_1(\Omega)^\beta$ scale-invariant | `KohlerJobinTransfer.tex` Rmk 2.2 |

**Compatibility check.** All three statements (A)/(B)/(C) are quoted at the common volume normalisation $|\Omega|=\omega_n$ inside the proofs, and at $|\Omega|=|B^*|$ in the final statements via scale invariance of $\mathcal A$, $D$, and $\Psi$. The energy sign convention $E=-T/2$ is consistent across Plan 2 notes and Final blocks. The factor 2 between $\delta_T$ and $\delta_{\rm SV}$ is correctly absorbed in the constant $4L_n/((n+2)T_n)$ of the small-deficit branch of $c_{\rm FK}$ (`KohlerJobinTransfer.tex` Rmk on energy norm; cf. `Plan 1/faber-krahn-transfer.md` §4).

---

## 5. Compatibility check: bounded reduction vs. Plan 2 bookkeeping

`Final/BoundedReduction.tex` produces the bounded surrogate $\widetilde\Omega$ with three quantitative losses (cf. Lemma 3.1, BDV Lemma 5.3):
$$
|\widetilde\Omega|=\omega_n,\quad \operatorname{diam}(\widetilde\Omega)\le d(n),\quad D(\widetilde\Omega)\le C_9(n)D(\Omega),\quad \mathcal A(\Omega)\le\mathcal A(\widetilde\Omega)+C_9(n)D(\Omega).
$$
The relevant rates are:

- **Deficit loss:** $D(\widetilde\Omega)\le C_9(n)D(\Omega)$ — multiplicative, hence consumes (A) cleanly: $\mathcal A(\widetilde\Omega)^2\le C_{\rm P2}(n,d(n))\,D(\widetilde\Omega)\le C_{\rm P2}\,C_9\,D(\Omega)$.
- **Asymmetry loss:** $\mathcal A(\Omega)\le\mathcal A(\widetilde\Omega)+C_9D(\Omega)$ — additive, with $O(D)$ (not $O(\sqrt{D})$) tail. After squaring, $\mathcal A(\Omega)^2\le 2\mathcal A(\widetilde\Omega)^2+2C_9^2D(\Omega)^2\le 2\mathcal A(\widetilde\Omega)^2+2C_9^2\delta(n)D(\Omega)$ in the small-deficit regime. This is the exact computation `BoundedReduction.tex` Lemma 4.2 performs.

These rates are **compatible** with Plan 2's bookkeeping: Plan 2 produces the bounded-class inequality $\mathcal A(\widetilde\Omega)^2\le C_{\rm P2}\,D(\widetilde\Omega)$ (after scale normalisation), and the reduction inflates the constant only by the explicit factor $4C_9(1/\widetilde c_{\rm SV}+C_9)$. The internal cost of Plan 2's own $O(\sqrt{\delta_T})$ layer (the transfer from $E_{\widehat\rho}$ to $\Omega$ at the end of `metric-finite-perimeter-closure.md` §6) is **internal to (A)**; it is *already absorbed in* $C_{\rm P2}(n,R)$. It is **not** a separate stage that the bounded reduction has to undo. There is no double counting.

**Verdict.** No missing rate at the (A)→(B) interface. The bounded reduction is dimensional-radius dimensional-constant (R-internalising) and rate-preserving (preserves the exponent 2 on $\mathcal A$ and the linear-in-$D$ gain).

---

## 6. Open issues (inputs not yet fully proved in this repo)

| # | Item | File | Status |
|---|------|------|--------|
| 1 | **Conjecture 3.6 (radial weighted perimeter excess)** $\int\!|e_r\!\cdot\!\nu_E|/|x-z_E|^{n-1}-n\omega_n\le C(P(E)-P(B_\rho))$; equivalently the radial $L^1$-trace (R). | `Plan 2/agent2-homothetic-velocity-defect.md` §3.6 | **Open.** Agent 2 explicitly notes the FMP/Fusco–Julin package does not imply (R), and the divergence-theorem route gives only the signed radial moment. Three repair strategies are listed in §5 there: (a) quantitative spherical $H^{1/2}$ trace via Cicalese–Leonardi Lipschitz parametrisation; (b) Fusco–Julin Hausdorff containment $\eta=O(\sqrt{P-P(B_\rho)})$; (c) replace (R) by an $L^2$ form. The deployment brief flagged this as the most likely vulnerable point and Agent 2 confirms it. |
| 2 | **Bound (5.14) of Agent 4** (integrated $L^2(d\rho)$ kinetic bound, equivalently second-order profile-gap refinement $M-c=O(\delta)$). | `Plan 2/agent4-weighted-metric-trace.md` §5 | **Open / repairable.** The naked (H1)+(H2) hypotheses of the deployment brief yield only the $O(\sqrt{\delta})$ rate; the sharp rate needs the auxiliary kinetic bound. Agent 4 argues both holds *for free* in the torsion application via the exact Cauchy–deficit identity for $D_H$, pointing to `outer-foliation-entry-proof-attempt.md` §4 for the bookkeeping — but this hand-off is not yet a fully written theorem. |
| 3 | **Agent 3 metric first variation (T)** | `Plan 2/agent3-metric-first-variation.md` | Established under the standing hypothesis $\Omega\subset B_R$, with FvHT center gluing. Treated here as input. |
| 4 | **Agent 1 finite-perimeter level-set deficit identity** | `Plan 2/agent1-finite-perimeter-identity.md` | Established (no extra hypotheses beyond $|\Omega|<\infty$). Treated here as input. |
| 5 | **FvHT center gluing (lateral input to Agents 2, 3)** | `Plan 2/fvht-center-gluing-import.md` | Not re-audited here; treated as established. Agent 6 must verify it controls centers at $O(\sqrt\delta)$, no better. |
| 6 | **Bounded reduction `BoundedReduction.tex`** | `Final/BoundedReduction.tex` | Established (BDV Lemmas 5.1–5.3 are black-boxed but published). |
| 7 | **Kohler–Jobin transfer `KohlerJobinTransfer.tex`** | `Final/KohlerJobinTransfer.tex` | Established (Brasco 2014 black box plus elementary one-variable inequality). |
| 8 | **Boundary-layer transfer $E_{\widehat\rho}\to\Omega$** | `Plan 2/metric-finite-perimeter-closure.md` §6 | The $O(\sqrt\delta)$ volume removed gives $O(\delta)$ squared asymmetry loss. Internal to Plan 2; should be re-checked by Agent 6 against the sharpness of the exponent. |

Items 1 and 2 are the **only substantive conjectural inputs** in this chain. The remainder are either established here (3, 4), established elsewhere (5, 6, 7), or arithmetic (8).

---

## 7. What this assembly proves vs. what it conditions on

**Proves (unconditionally, in this repo).** The *reduction* of sharp quantitative Faber–Krahn stability to the conjunction of:
- Agent 1's level-set identity,
- Agent 3's metric first-variation estimate,
- Conjecture 3.6 of Agent 2,
- Bound (5.14) of Agent 4,
- BDV Lemmas 5.1–5.3 (published),
- Kohler–Jobin (1978) + the elementary linearisation.

The reduction is rate-preserving (exponent 2), R-internalising (the final constant depends only on $n$), and constants-explicit at every stage.

**Conditions on.** The unconditional sharp quantitative Faber–Krahn inequality
$$
(|\Omega|/|B_1|)^{2/n}\bigl(\lambda_1(\Omega)-\lambda_1(B^*)\bigr)\ge c_{\rm FK}(n)\,\mathcal A(\Omega)^2
$$
via the Plan 2 metric route is **not** established in this repo as of Wave 1. The two missing inputs are Conjecture 3.6 (Agent 2) and (5.14) (Agent 4); both are flagged as *substantive, not fatal, and repairable in principle*.

**Comparison.** The Plan 1 route (via the `SaintVenantAssembly` block in `Final/` and `quantitative-selection-principle.md` etc.) reaches the same Faber–Krahn conclusion through a selection principle, graph entry, Schauder interpolation, and BDV's nearly spherical theorem. That route is reported as unconditional in `Plan 1/PLAN1_AGENT_REPORT.md`. The Plan 2 route is a *no-selection, no-graph-entry, no-nearly-spherical-theorem* alternative; its value is that it stays intrinsic to the actual torsion level sets. Closing items 1 and 2 above would make Plan 2 an independent proof of sharp quantitative Faber–Krahn stability.

---

## 8. Pointers to next actions

For Wave 2 / Agent 6 / the user:

- **Highest priority:** settle Conjecture 3.6, ideally via remediation (b) of Agent 2 §5 (Fusco–Julin Hausdorff containment), which is measure-theoretic and respects the brief's "no graph" constraint.
- **Second priority:** make the (K5.14) hand-off from the Cauchy–deficit identity to the integrated $L^2(d\rho)$ kinetic bound a fully written theorem (currently sketched in `outer-foliation-entry-proof-attempt.md` §4). Either route — (5.14) directly or the $M-c=O(\delta)$ profile-gap refinement — closes Agent 4 at the sharp rate.
- **Audit:** Agent 6 should re-verify items 5 (FvHT centers, no over-control) and 8 (boundary-layer transfer, exponent preservation) of the open-issues table.

Closing items 1 and 2 makes Theorem D unconditional and yields a genuine no-selection-principle proof of sharp quantitative Faber–Krahn stability.
