# Sharp Faber–Krahn Stability via Plan 2 / Route δ — Handoff for Independent Verification

This document is a self-contained briefing for an independent reviewer (or a separate AI system) to (a) audit the current state of the Plan 2 / Route δ proof, and (b) attempt to close the one residual conditionality — a quantitative lower bound on the gradient of the torsion function on level surfaces.

The chain of 7 LaTeX files lives in this directory (`Plan 2/WIP/`); each compiles independently to a PDF.

---

## 1. The target theorem

**Theorem (Sharp quantitative Faber–Krahn, Plan 2).** There exists a dimensional constant $c_{\rm FK}(n) > 0$ such that for every open $\Omega \subset \mathbb{R}^n$ with $0 < |\Omega| < \infty$,
$$\Big(\frac{|\Omega|}{|B_1|}\Big)^{2/n}\big(\lambda_1(\Omega) - \lambda_1(B^*)\big) \;\ge\; c_{\rm FK}(n)\,\mathcal{A}(\Omega)^2,$$
where $B^*$ is the ball with $|B^*| = |\Omega|$ and $\mathcal{A}(\Omega)$ is the Fraenkel asymmetry. The exponent 2 is sharp.

The theorem is known unconditionally — Brasco–De Philippis–Velichkov (Duke 2015) and Allen–Kriventsov–Neumayer (2023). The contribution of Plan 2 is a **structurally novel proof** that avoids: (i) the Cicalese–Leonardi / BDV selection principle, (ii) graph-entry via free-boundary regularity, (iii) Schauder bootstrap interpolation, and (iv) the nearly-spherical Fuglede closure theorem. In their place: a finite-perimeter level-set deficit identity, a metric foliation of level sets, and a Sobolev-style pairing of two integrated defects $D_H$ and $D_I$.

---

## 2. The seven building blocks

| # | Block | Role |
|---|-------|------|
| I | `LevelSetIdentity` | Exact deficit identity $\frac{2}{|\Omega|}(E(\Omega)-E(B)) = \int (D_H + D_I)/\text{weight}\,dt$. |
| II | `MetricFramework` | Metric space $\mathcal{X}$ of $L^1$-classes modulo translation; metric first variation (Theorem T). |
| III | `CentroidBound` | Centroid kinematic identity (auxiliary). |
| IV | `SpaceTimeIdentity` | Space-time $\Pi$ identity, slicing-then-squaring (auxiliary). |
| V | `WeightedMetricTrace` | **Load-bearing.** Fusco–Julin centre + radial $L^1$ trace + Markov/kinetic combination → pointwise $d_{\mathcal X}(F_{\rho_\delta}, B_1)^2 \le C_*\delta_T$ at the deficit endpoint. |
| VI | `BoundaryLayerTransfer` | Transfer from $E_{\rho_\delta}$ back to $\Omega$ via Lemma 8.3. |
| VII | `GlobalAssembly` | Stage 1 (bounded Saint–Venant) → Stage 2 (BDV bounded reduction) → Stage 3 (Kohler–Jobin) → sharp Faber–Krahn. |

The proof is **conditional on one standing hypothesis** (Hyp-G, §6 below). Everything else is unconditional.

---

## 3. The key structural idea (Pass 6 fix)

The chain originally tried to extract a single level $\hat\rho$ where the level set $E_{\hat\rho}$ is close to a ball, via Markov on $\int |E_\rho \Delta B_\rho|^2\,d\mu \le C\delta$. This produces a $\delta^{2/3}$ exponent, not the sharp $\delta$, because the boundary-layer transfer requires $\hat\rho$ near the upper endpoint $\rho_\delta$ but Markov on a small window degrades.

**The fix:** combine two integrated inputs that the deficit identity supplies for free:

- **Input A** ($D_I$ via Fusco–Julin): $\int d_{\mathcal X}(F_\rho, B_1)^2\,d\mu \le C\delta$ ("many levels are close to balls").
- **Input B** ($D_H$ via metric first variation): $\int |\dot F_\rho|_{\mathcal X}^2\,d\rho \le C'\delta$ ("the levels don't curve away faster than $\sqrt{\delta}$ in $L^2$").

Their pairing, via 1D Sobolev embedding $H^1(J^*) \hookrightarrow L^\infty(J^*)$ on the order-one window $J^* = [\rho_\delta - L^*, \rho_\delta]$ (equivalently: Markov on $A$ + Cauchy–Schwarz kinetic transport on $B$ + triangle inequality), yields the **uniform pointwise bound**
$$\sup_{\rho \in J^*} d_{\mathcal X}(F_\rho, B_1)^2 \;\le\; C_*\,\delta_T.$$

Specialising to $\rho = \rho_\delta$ (the deficit endpoint, where the boundary-layer thickness $1 - \rho_\delta = \kappa\sqrt{\delta_T}$ matches the sharp exponent), the boundary-layer transfer of Block VI delivers $\mathcal{A}(\Omega)^2 \le C\delta_T$.

The exposition lives in:
- **Block V Remark 5.7** ("Why two inputs are needed: the $D_H/D_I$ pairing") — the structural explanation.
- **Block I §7** — the load-bearing variance bound (see §5 below).

---

## 4. Where to look in the PDFs

| Concept | File | Location |
|---------|------|----------|
| Overall architecture | `WIP_master.pdf` | §3 + §6 |
| Deficit identity $D_H + D_I$ | `WIP_LevelSetIdentity.pdf` | Theorem 5.1 (boxed) |
| **Unit-weight variance bound** | `WIP_LevelSetIdentity.pdf` | **§7 (Hyp-G, Prop 7.3, Cor 7.4)** |
| Fusco–Julin centre package | `WIP_WeightedMetricTrace.pdf` | Lemma 2.1 |
| Radial $L^1$ trace | `WIP_WeightedMetricTrace.pdf` | Lemma 2.2 |
| Integrated action bound | `WIP_WeightedMetricTrace.pdf` | Theorem 1.1 (proof at §3) |
| **The $D_H/D_I$ pairing** | `WIP_WeightedMetricTrace.pdf` | **Theorem 5.6 + Remark 5.7** |
| Boundary-layer transfer | `WIP_BoundaryLayerTransfer.pdf` | §3–4 |
| Final assembly | `WIP_GlobalAssembly.pdf` | §1–4 |

To audit the load-bearing argument, read `WIP_LevelSetIdentity.pdf` §7 first, then `WIP_WeightedMetricTrace.pdf` Lemma 2.1 → 2.2 → 2.3 → Theorem 3.1 proof → Theorem 5.6 → Remark 5.7.

---

## 5. The one residual conditionality: Hyp-G (lower bound)

The entire chain is rigorous **given** the following standing hypothesis, stated as Hypothesis 7.1 in `WIP_LevelSetIdentity.tex`:

> **(Hyp-G)** There exist constants $0 < m_0 \le M_0 < \infty$ depending only on $n, R, \rho_*$ such that, for $\mathcal L^1$-a.e. $\rho \in [\rho_*, \rho_\delta]$,
> $$m_0 \le |\nabla u(x)| \le M_0$$
> for $\mathcal H^{n-1}$-a.e. $x \in \partial^* E_\rho$.

Here $u = u_\Omega$ is the variational torsion function ($-\Delta u = 1$ in $\Omega$, $u = 0$ on $\partial\Omega$), $E_\rho = \{u > t(\rho)\}$ with $|E_\rho| = \omega_n\rho^n$, and $[\rho_*, \rho_\delta]$ is the deficit window with $\rho_\delta = 1 - \kappa\sqrt{\delta_T(\Omega)}$.

### Upper bound $M_0$ — unconditional

Cianchi–Maz'ya (JEMS 2011) for the linear case $p=2$, applied to $-\Delta u = 1 \in L^\infty \subset L^q$ for $q > n$, gives $\|\nabla u\|_{L^\infty(\Omega)} \le K_n R$ for $\Omega \subset B_R$ in the bounded reduction class produced by BDV's Lemma 5.3. (Alternatively: Stampacchia, or Talenti's rearrangement followed by boundary regularity transfer.)

### Lower bound $m_0$ — the residual conditionality

What is **expected but not yet proven**: a quantitative pointwise positive lower bound $|\nabla u| \ge m_0(n, \rho_*) > 0$ on $\partial^* E_\rho$ for a.e. $\rho \in [\rho_*, \rho_\delta]$, uniform in $\rho$ and in $\Omega$ within the small-deficit bounded-reduction class.

What is **known**:
- **Brothers–Ziemer (1988)**: $|\nabla u| > 0$ $\mathcal H^{n-1}$-a.e. on $\partial^* E_\rho$ — qualitative, not quantitative.
- **Talenti (1976)**: pointwise upper bound on the *rearranged* gradient $|\nabla u^*|(\rho) \le \rho/n$. This is the wrong direction — it bounds the rearranged gradient from above, and rearrangement does not preserve pointwise gradient sizes.

What is **plausible**:
- In the small-deficit regime $\delta_T \le \delta_0(n, R, \rho_*)$, the level set $\partial^* E_\rho$ is close to the sphere $\partial B_\rho$, where $|\nabla u_B| = \rho/n \ge \rho_*/n > 0$.
- A **Caffarelli-type non-degeneracy estimate** on annular shells $E_\rho \setminus E_{\rho + \varepsilon}$, exploiting the non-zero driving term $-\Delta u = 1$, should yield the quantitative bound.

### Why this is the *only* residual conditionality

The chain is structured so that:
- Block I §7 derives the load-bearing inequality $(\int |V_\rho - \bar V_\rho|)^2 \le D_H(t(\rho))/(n^2 m_0^2)$ **conditional on Hyp-G** (Proposition 7.3).
- Blocks V, VI, VII all carry constants depending polynomially on $(M_0/m_0)^2$ via this inequality.
- No other step in the chain requires Hyp-G or any other unproven input.

So closing Hyp-G(lower) makes the entire chain unconditional.

---

## 6. Concrete attack strategies for Hyp-G(lower)

### Strategy A: Caffarelli non-degeneracy on annular shells

Standard non-degeneracy lemma for $-\Delta u = f$ with $f \ge c > 0$ and $u \ge 0$: in a shell $A_r(x_0) = B_r(x_0) \setminus B_{r/2}(x_0)$ contained in $\{u > 0\}$, $|\nabla u|$ is comparable to $r$.

Applied to $E_\rho$ vs $E_{\rho + \varepsilon}$ in the small-deficit regime: pick $x \in \partial^* E_\rho$, consider the shell $E_\rho \setminus E_{\rho + \varepsilon}$ containing $x$ for $\varepsilon$ small. Width of the shell $\asymp \varepsilon$ (in volume measure) or $\asymp \varepsilon/|\nabla u|$ (in geometric measure). For the shell to satisfy a non-degeneracy estimate, one needs uniform interior thickness — which is exactly where $|\nabla u| \ge m_0$ enters.

**References to consult:**
- Caffarelli, *Rev. Mat. Iberoam.* 1987–89 (Harnack-inequality approach).
- Alt–Caffarelli, *J. Reine Angew.* 1981 (one-phase free boundary).
- Caffarelli–Cabré, AMS Colloq. 43, 1995, §7.

### Strategy B: Stability transfer from Talenti

If $\Omega$ is close to a ball in $L^1$ (Fraenkel asymmetry $\le \varepsilon$), and $|\nabla u_B|$ is the radial torsion gradient with $|\nabla u_B(\rho)| = \rho/n$, then by elliptic stability $|\nabla u - \nabla u_B|$ is small in $L^p$ for some $p$. This would imply $|\nabla u| \ge \rho/n - O(\varepsilon)$ pointwise on $\partial^* E_\rho$, *if* the convergence is pointwise (not just in $L^p$).

Pointwise convergence requires regularity (e.g., $C^{1,\alpha}$ stability), which is what the BDV bounded reduction provides in some form. But the present chain explicitly avoids using $C^{1,\alpha}$ regularity of $\partial\Omega$ (one of the four classical tools the Plan 2 chain bypasses), so this strategy must be careful not to reintroduce it through the back door.

**References to consult:**
- Magnanini–Poggesi (various 2019–2023 papers on stability of overdetermined Serrin).
- Brasco–De Philippis (Duke 2015, especially their stability lemmas).
- Cianchi–Esposito–Fusco–Trombetti (gradient rearrangement).

### Strategy C: BV-coarea + Brothers–Ziemer quantitative

The Brothers–Ziemer theorem can be made quantitative: the measure of $\{|\nabla u| \le \tau\}$ in $\partial^* E_\rho$ is bounded by something computable in terms of geometric quantities ($P(E_\rho)$, $|\Omega|$, etc.). If this quantitative bound is sharp enough in the small-deficit regime, it might give a pointwise lower bound after Sobolev-type averaging.

**References to consult:**
- Brothers–Ziemer, *J. Reine Angew.* 384 (1988), 153–179.
- Cianchi, *Indiana Univ. Math. J.* 45 (1996), 71–98 (quantitative Brothers–Ziemer).

### Strategy D: Direct argument using the bounded reduction

The bounded reduction class produced by `BDV-BoundedReduction-Plan1` (cited as `\cite{BDV-BoundedReduction-Plan1}` in Block VII) constructs $\Omega' \subset B_{R_*(n)}$ inheriting structural properties from the BDV procedure (which involves penalisation, selection, and Hausdorff convergence to a near-ball). These properties likely include enough regularity to apply *direct* boundary regularity theorems (e.g., $C^{1,\alpha}$ at the boundary via Caffarelli's free-boundary results). Examining what regularity the bounded reduction *implicitly* provides may yield $m_0$ directly.

**This is the most likely route to a clean proof,** but requires excavating the BDV bounded reduction (which lives in the Plan 1 Final/ library, outside the Plan 2 WIP/ files).

---

## 7. Audit prompts to deploy

Below are prompt templates an independent reviewer can use with their AI of choice, or that GPT can use to deploy subagents.

### Audit Prompt 1: Verify Block I §7 rigour

```
You are auditing a load-bearing proposition in a sharp Faber–Krahn stability paper.
Read the file:
  Plan 2/WIP/WIP_LevelSetIdentity.tex
Focus on Section 7 ("Gradient regularity on level surfaces and the unit-weight variance bound").

Verify each step of Proposition 7.3 (Velocity defect from D_H under Hyp-G):
1. The Cauchy–Schwarz step (eq:CSstep): standard.
2. The variance expansion (eq:varexp): algebraic, verify.
3. The double-integral form (eq:dbl1) for P∫1/f² − α²: verify by expanding the
   symmetric integrand and using ∫1/f(x)² dxdy = P·∫1/f² etc.
4. The double-integral form (eq:dbl2) for D_H = (1/2)∬ (f(x)−f(y))²/(f(x)f(y)):
   verify this is the standard Cauchy–Schwarz defect formula.
5. The pointwise ratio comparison (eq:ratio): integrand of (eq:dbl1) is
   1/(f(x)f(y)) times that of (eq:dbl2); under f ≥ m_0, this is ≤ 1/m_0².
6. The Talenti |t'| ≤ 1/n derivation in Step 5: verify by substituting
   s = ω_n ρⁿ into (u_B*)'(s) = -s^{2/n-1}/(n²ω_n^{2/n}).
7. The final constant (M_0/m_0)²/n² (with M_0 ≥ 1 in the application).

Flag any algebraic errors, hidden hypotheses, or steps that don't follow.
Report in under 800 words.
```

### Audit Prompt 2: Verify the D_H/D_I pairing argument

```
You are auditing the load-bearing pairing of two integrated defects in a
sharp Faber–Krahn stability proof.
Read the file:
  Plan 2/WIP/WIP_WeightedMetricTrace.tex
Focus on:
  - Theorem 1.1 (Integrated action bound) and its proof at §3.
  - Theorem 5.6 (Abstract weighted metric trace) and Remark 5.7.

Verify:
1. The proof of Theorem 1.1 decomposes |dot F_ρ|² ≤ C[(∫|V−V̄|)² + (∫|H−V̄|)²]
   correctly from MetricFramework Thm T (a=0, triangle inequality, (a+b)²
   bookkeeping).
2. The first term is bounded via Proposition 7.3 of LevelSetIdentity (cited as
   eq:V-bar-V).
3. The second term is bounded via Lemma 2.3 (good-level homothetic trace,
   eq:htrace-good).
4. The bad set B_I has μ-measure ≤ Cδ and contributes O(δ) via the uniform
   Lipschitz bound (A0).
5. Theorem 5.6's proof: Markov on H1 produces ρ_0 with d²(γ(ρ_0), B_1) ≤ K_1·δ;
   kinetic Cauchy–Schwarz transports to any ρ ∈ J* at cost L*·C'·δ; triangle
   inequality yields uniform-on-J* bound 2K_1·δ + 2L*C'δ.
6. Specialising to ρ = ρ_δ gives the endpoint d²(γ(ρ_δ), B_1) ≤ C*·δ.

Flag any gaps. Report in under 800 words.
```

### Audit Prompt 3: Attempt Hyp-G(lower)

```
You are attempting to prove the residual hypothesis Hyp-G(lower) for a sharp
Faber–Krahn stability proof.

Setup:
- Ω ⊂ B_{R*(n)} open with |Ω| = ω_n in the BDV bounded reduction class.
- u = u_Ω the variational torsion function: -Δu = 1 in Ω, u = 0 on ∂Ω.
- E_ρ := {u > t(ρ)} with |E_ρ| = ω_n ρⁿ, ρ ∈ [ρ_*, ρ_δ] where
  ρ_δ = 1 − κ√δ_T(Ω).
- δ_T(Ω) := E(Ω) − E(B*) is the Saint–Venant deficit, assumed
  ≤ δ_0(n, R, ρ_*).

Goal: prove there exists m_0 = m_0(n, ρ_*) > 0 such that for a.e.
ρ ∈ [ρ_*, ρ_δ],
   |∇u(x)| ≥ m_0  for H^{n-1}-a.e. x ∈ ∂*E_ρ.

Constraints:
- May NOT use C^{1,α} regularity of ∂Ω (one of the four classical tools
  Plan 2 avoids).
- May use: BV coarea, finite-perimeter / De Giorgi structure theorems,
  Brothers–Ziemer non-degeneracy, Talenti pointwise/rearrangement
  comparison, isoperimetric inequality, BDV bounded reduction
  *structural* properties (but NOT its boundary regularity output).

Strategies to consider (see HANDOFF.md §6):
- Caffarelli-type non-degeneracy on annular shells E_ρ \ E_{ρ+ε}.
- Quantitative Brothers–Ziemer (Cianchi 1996).
- Direct argument using BDV bounded reduction structural properties.

If you can prove it: write a Lemma statement + full proof.
If you cannot: identify the precise sub-step that fails and which
auxiliary result would close it.
```

---

## 8. Repository access

The full repository is at `https://github.com/joaopgramos95/Math-projects`. The Plan 2 WIP files are in `Sharp stab Faber-Krahn/Plan 2/WIP/`. The most recent commit (as of this writing) is `520b13f` on `main`, "Plan 2 / Route δ: close Markov bottleneck + tighten Fusco-Julin chain".

The 8 LaTeX files of Plan 2 compile independently. Two-pass `pdflatex` produces clean PDFs with no undefined references, no multiply-defined labels, and no LaTeX warnings.

---

## 9. Pointers to prior work

For context on the unconditional proofs of sharp Faber–Krahn that Plan 2 aims to re-derive structurally:

- **Brasco, De Philippis, Velichkov**, *Faber–Krahn inequalities in sharp quantitative form*, Duke Math. J. **164** (2015), 1777–1831 (arXiv:1306.0392).
- **Allen, Kriventsov, Neumayer**, *Sharp quantitative Faber–Krahn inequalities and the Alt–Caffarelli–Friedman monotonicity formula*, Ars Inveniendi Analytica (2023).
- **Fusco, Maggi, Pratelli**, *The sharp quantitative isoperimetric inequality*, Ann. of Math. **168** (2008), 941–980.
- **Fusco, Julin**, *A strong form of the quantitative isoperimetric inequality*, Calc. Var. PDE **50** (2014), 925–937.

For the metric framework and rearrangement tools:

- **Ambrosio, Gigli, Savaré**, *Gradient Flows in Metric Spaces and in the Space of Probability Measures*, Birkhäuser, 2008.
- **Talenti**, *Elliptic equations and rearrangements*, Ann. Mat. Pura Appl. **110** (1976), 353–372.
- **Brothers, Ziemer**, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math. **384** (1988), 153–179.

For the elliptic regularity used in Hyp-G(upper):

- **Cianchi, Maz'ya**, *Global Lipschitz regularity for a class of quasilinear elliptic equations*, J. Eur. Math. Soc. **13** (2011), 247–292.

---

## 10. What success looks like

The handoff is "complete" when:

1. **Independent audit confirms** the Pass 6+7 chain is rigorous (modulo Hyp-G), at the level of detail expected for an Annals/Duke-grade research paper.
2. **Hyp-G(lower) is proven** (or definitively reduced to a known result in the literature) — turning the entire chain into an unconditional proof.

Either outcome (audit confirmation OR a closing of Hyp-G) is a substantial step forward. Independent failure to close Hyp-G via the strategies in §6 is also informative — it would identify where additional novel work is needed.

End of handoff.
