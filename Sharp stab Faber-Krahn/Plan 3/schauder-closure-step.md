# Schauder interpolation: closing the `C^{1,γ}` → small `C^{2,γ_0}` gap

**Purpose.** Discharge audit issue **G6** (`AUDIT_BRANDOLINI_ROUTE.md`) and
issue **C7** (first-mode neutralisation). Combine Cor 2.2 of
`BRANDOLINI_GRAPH_ENTRY_ROUTE.md` with interior Schauder for `−Δu = 1`
and an `L^∞`–`C^{3,γ}` interpolation on `∂B_1` to produce a graph
parametrisation `h` of `∂E_{\hat t}` satisfying

\[
   \|h\|_{C^{2,\gamma_0}(\partial B_1)}
   \;\le\; \delta_{\rm sph}(n,\gamma_0),
\]

the smallness hypothesis (eq. `normal`) of
`Final/NearlySphericalClosure.tex`, Theorem `thm:NS`. Once that bound is
in hand, `thm:NS` produces
`Asym(E_{\hat t})^2 \le C \, (E(E_{\hat t}) - E(B_1))` and Plan 3 closes
at the level of `E_{\hat t}`.

**Conventions.** Plan 2 PDE sign convention `−Δu = 1`. Dimension
`n \ge 2`. Fix `γ_0 ∈ (0, 1)` (parameter of `thm:NS`). Choose
`γ ∈ (γ_0, 1)`; `α := γ` for interior Schauder.

**Notation.** `B_R \subset \mathbb R^n` outer ball produced by bounded
reduction. `ρ_* \in (0, 1)` fixed parameter of the outer collar
`[ρ_*, 1]`. `\hat t` the good level produced by Agent 1 inside that
collar. `E_{\hat t} = \{u > \hat t\}`. Throughout `C(\cdot)` denotes a
positive constant depending only on the indicated parameters; its value
may change line to line.

---

## 1. What Corollary 2.2 of the route delivers

After rescaling `E_{\hat t}` to unit volume (the scaling map is recorded
in `AUDIT_BRANDOLINI_ROUTE.md` §G4; the rescaling factor
`λ = (|E_{\hat t}|/\omega_n)^{1/n}` is bounded above and below by
constants depending on `(n, R, ρ_*)` because `\hat t \in [ρ_*, 1]`),
Cor 2.2 produces a centre `x_*` (the inscribed-ball centre supplied by
Brandolini Corollary 9 + Lemma 10) and a parametrisation

\[
   \partial E_{\hat t} \;=\; \bigl\{\, x_* + (1 + h(\theta))\,\theta
   \;:\; \theta \in \partial B_1 \,\bigr\}
\]

with

\begin{align}
   \|h\|_{L^\infty(\partial B_1)}
   &\;\le\; C_{\rm sq}(n, R, \rho_*) \, \eta^{\kappa \mu}
   \;=:\; \varepsilon, \tag{1.1}\\
   \|h\|_{C^{1,\gamma}(\partial B_1)}
   &\;\le\; C_{1,\gamma}(n, R, \rho_*), \tag{1.2}
\end{align}

where:

- `η` is the level-set defect `(D_H + D_I)(\hat t) \le η`;
- `κ = α / (2α + n − 1)` (the corrected interpolation exponent of audit
  item **G2**, not the route document's `α/(2(n−1+α))`);
- `μ = 1 / (2(4n+9)(n−1))` is Brandolini's explicit exponent
  (`brandolini.pdf` end of proof of Theorem 2);
- `C_{\rm sq}, C_{1,\gamma}` depend on `(n, R, ρ_*)` only.

The combination `κμ > 0` is positive, finite, and `< 1`; the explicit
lower bound `κμ \ge α / \bigl(2(2α + n − 1)(4n+9)(n−1)\bigr)` is
recorded for bookkeeping only — sharp rate is not the target here.

The `C^{1,γ}` bound (1.2) is **not small**; only the `L^∞` bound (1.1)
carries the smallness in `η`.

---

## 2. Upgrade to bounded `C^{3,γ}` norm of `h`

The bound (1.2) is more than enough for the qualitative graph property
of Cor 2.2, but it falls short of the (eq:normal) hypothesis of
`thm:NS`. We first observe that, on the outer collar, the `C^{1,γ}`
regularity already automatically upgrades to `C^{3,γ}` at no smallness
cost, by interior Schauder for the torsion PDE.

### 2.1 Interior Schauder for `u`

Let `v` denote the rescaled torsion function on the unit-volume copy of
`E_{\hat t}`. From the rescaling laws of audit §G4, `v` satisfies
`−Δv = λ²` (with `λ ∈ [c(ρ_*), C(R)]` bounded above and below) on a
neighbourhood of `\overline{B_2} \setminus B_{1/2}` (the relevant collar
after rescaling), and `v(x_* + (1+h(\theta))\theta) = \hat t` along the
graph.

Choose a slightly thinner shell `\mathcal A := \overline{B_{3/2}}
\setminus B_{2/3}` strictly inside `B_2 \setminus B_{1/2}`. On the outer
collar `ρ ∈ [ρ_*, 1]` (i.e. for `\hat t` whose level surface in
unrescaled coordinates is bounded away from `∂Ω` by a distance
`≥ c(n, R, ρ_*)`), the rescaled torsion `v` is a classical solution of a
linear PDE with smooth right-hand side. **Interior Schauder**
(Gilbarg–Trudinger Theorem 6.2, iterated once on shrinking subdomains)
gives

\[
   \|v\|_{C^{3,\alpha}(\mathcal A)}
   \;\le\; C_S(n, R, \rho_*)\,\bigl(\|v\|_{L^\infty(B_2)} + \lambda^2\bigr)
   \;\le\; M_v(n, R, \rho_*). \tag{2.1}
\]

The `L^∞` bound on `v` itself comes from comparison with the torsion of
`B_R`, scaled.

### 2.2 Implicit function theorem transfer to `h`

On the spherical chart `θ ↦ h(θ)`, the defining relation is
`v(x_* + (1 + h(\theta))\theta) = \hat t`. The radial derivative
`∂_r v` at the level set equals `−|∇v|` up to sign (the rescaled level
is regular by the Brandolini non-degeneracy `|∇v| − 1` is `O(δ)` on
`∂E_{\hat t}`, so `|∇v| ≥ 1/2` once `δ ≤ 1/2`, hence `|∇v|` bounded
below by `q_-(n, R, ρ_*) > 0`). By the implicit function theorem on the
manifold `∂B_1`, `h` inherits the regularity of `v` modulo division by
`∂_r v`:

\[
   \|h\|_{C^{3,\gamma}(\partial B_1)}
   \;\le\; C_{\rm IFT}\bigl(n, R, \rho_*, \|v\|_{C^{3,\alpha}(\mathcal A)},
                            q_-^{-1}\bigr)
   \;\le\; \mathcal M(n, R, \gamma, \rho_*). \tag{2.2}
\]

Concretely, the chain rule expresses `∂_θ^k h` in terms of spatial
derivatives of `v` up to order `k`, divided by `(∂_r v)^k` (generic
Faà di Bruno expansion). With `\|v\|_{C^{3,\alpha}} ≤ M_v` and
`|∂_r v| ≥ q_-`, each derivative is bounded, and the `C^{0,γ}`-seminorm
of `∂_θ^3 h` is controlled by the product. The final bound is

\[
\boxed{\;
   \|h\|_{C^{3,\gamma}(\partial B_1)}
   \;\le\; \mathcal M(n, R, \rho_*, \gamma)
   \;=:\; \mathcal M. \;} \tag{$\mathcal M$}
\]

This is **bounded but not small**: it does not depend on `η`, only on
`(n, R, ρ_*, γ)`.

### 2.3 Comparison with `Final/SchauderInterpolation.tex`

`Final/SchauderInterpolation.tex` carries out a directly analogous
bootstrap: §2 (hodograph straightening following Kinderlehrer–Nirenberg)
and §3 (Lieberman Schauder for the oblique BVP) produce, by Proposition
`prop:bootstrap` (its eq. `bootstrap`), a uniform Schauder bound

\[
   \|g\|_{C^{m,\gamma}(\mathbb S^{N-1})} \;\le\; M_m(N, R),
\]

valid for every `m ≥ 1`. The constants `M_m(N, R)` are constructively
iterated, but the **only** input the bootstrap uses is the initial
`C^{1,γ}` bound (its (a)) and the BDV regularity package (Lipschitz
nondegeneracy `L_u`, Bernoulli `q_-, q_+, L_q`).

In the Brandolini route, the **same** initial `C^{1,γ}` bound comes from
Cor 2.2 (our (1.2)), and the Bernoulli / nondegeneracy data come from
`−Δu = 1` interior Schauder on the **outer** collar (no need for BDV's
free-boundary regularity, since `Σ_{\hat t}` is strictly interior).
Therefore the bootstrap of `SchauderInterpolation.tex`
`prop:bootstrap` applies *verbatim*, with the constants `M_m(N, R)`
replaced by `M_m(n, R, ρ_*, γ)`. The bound ($\mathcal M$) above is the
case `m = 3`.

**Reuse statement.** `Final/SchauderInterpolation.tex` is the
ready-to-use external reference for §2.1–§2.2 of the present note. The
only adjustments are: (a) replace its `(N, R)` constants by
`(n, R, ρ_*, γ)`; (b) replace its appeal to BDV's free-boundary
Lipschitz/Bernoulli (its Lemmas 4.12, 4.16) by interior Schauder on the
outer collar, which holds because
`dist(Σ_{\hat t}, ∂Ω) ≥ c(n, R, ρ_*) > 0`.

---

## 3. Hölder interpolation on `∂B_1`

`SchauderInterpolation.tex` §4 records exactly the inequality we need.
We re-state it in the form best matched to our application.

### 3.1 The interpolation inequality

**Lemma 3.1 (Hölder interpolation on the sphere).** Let `n ≥ 2`,
`m ≥ 1` integer, `0 ≤ k ≤ m`, `γ_0 ∈ (0, γ]`, `γ ∈ (0, 1]`, with
`(k, γ_0) ≠ (m, γ)`. There exists
`C_{\rm GN} = C_{\rm GN}(n, m, k, γ, γ_0) > 0` such that for every
`f ∈ C^{m, γ}(∂B_1)`,

\[
   \|f\|_{C^{k, γ_0}(\partial B_1)}
   \;\le\; C_{\rm GN}\,
   \|f\|_{L^\infty(\partial B_1)}^{\,1 - \theta}\,
   \|f\|_{C^{m, γ}(\partial B_1)}^{\,\theta}, \qquad
   \theta \;=\; \theta_{m,k} \;:=\; \frac{k + γ_0}{m + γ}\;\in\;(0, 1).
\tag{3.1}
\]

This is the standard convexity of Hölder norms (Gilbarg–Trudinger
Lemma 6.32; Bergh–Löfström Theorem 6.4.5) transported to a compact
`(n-1)`-manifold by a finite partition of unity and bilipschitz
straightening of `∂B_1`; the explicit version is recorded as
`SchauderInterpolation.tex` `lem:interp`, eq. `interp`, with the same
`θ_{m, k}` formula.

### 3.2 Application to `h`

Apply Lemma 3.1 with `f = h`, `m = 3`, `k = 2`, choose `γ ∈ (γ_0, 1)`.
Then

\[
   \theta \;=\; \theta_{3, 2}
   \;=\; \frac{2 + \gamma_0}{3 + \gamma} \;\in\; (0, 1), \qquad
   1 - \theta \;=\; \frac{1 + \gamma - \gamma_0}{3 + \gamma}
   \;\ge\; \frac{1 + \gamma - \gamma_0}{4} \;>\; 0. \tag{3.2}
\]

(With `γ_0 = γ/2`, say, `θ = (2 + γ/2)/(3 + γ) ≤ 2/3` and `1 − θ ≥ 1/3`;
an explicit positive lower bound `1 − θ ≥ (1 − γ_0)/4` is uniform in
`γ ∈ [γ_0, 1]`.)

Inserting (1.1) and ($\mathcal M$):

\[
\boxed{\;
   \|h\|_{C^{2, \gamma_0}(\partial B_1)}
   \;\le\; C_{\rm GN}\, \varepsilon^{\,1 - \theta}\, \mathcal M^{\,\theta}
   \;=\;   C_{\rm GN}\, \mathcal M^{\,\theta}\,
           C_{\rm sq}^{\,1 - \theta}\, \eta^{\,(1 - \theta)\,\kappa\mu}.
\;} \tag{3.3}
\]

Define

\[
   C_*(n, R, \rho_*, \gamma_0) \;:=\;
   C_{\rm GN}(n, 3, 2, \gamma, \gamma_0)\,
   \mathcal M(n, R, \rho_*, \gamma)^{\theta}\,
   C_{\rm sq}(n, R, \rho_*)^{1 - \theta}. \tag{3.4}
\]

Then (3.3) reads `\|h\|_{C^{2, γ_0}} ≤ C_*\, η^{(1−θ)κμ}`.

**Remark on `m = 3` vs. `m = 5`.** `SchauderInterpolation.tex` chooses
`m = 5` (its Theorem `thm:sph-entry`) to make
`θ_{5, 2} = (2 + γ_0)/(5 + γ) ≤ 1/2` for any `γ ∈ [γ_0, 1]`, recovering
the sharp `1/2` exponent on `L^∞`. For the present application sharpness
is not the target; the minimal `m = 3` suffices since `\mathcal M` is
already controlled at that level by one extra interior-Schauder step.
If one wishes to quote `SchauderInterpolation.tex` verbatim (`m = 5`),
one bootstraps two more times — `M_4, M_5` are finite by Lieberman, and
(3.3) becomes `\|h\|_{C^{2, γ_0}} ≤ C_{\rm GN}\,M_5^{θ_{5,2}}\,
ε^{1 − θ_{5,2}}`, with `1 − θ_{5,2} ≥ 1/2`.

---

## 4. Smallness threshold for `η`

The smallness hypothesis of `thm:NS` is `\|h\|_{C^{2,γ_0}} ≤
δ_{\rm sph}(n, γ_0)` where `δ_{\rm sph} = min(δ_1(n, γ_0), δ_3(n))`
from `NearlySphericalClosure.tex` eq. `dsph`.

**Threshold.** Set

\[
\boxed{\;
   \eta_0 \;=\; \eta_0(n, R, \rho_*, \gamma_0)
   \;:=\; \left(\frac{\delta_{\rm sph}(n, \gamma_0)}
                     {C_*(n, R, \rho_*, \gamma_0)}\right)^{\!
              1/((1 - \theta)\,\kappa\mu)}. \;} \tag{4.1}
\]

For every `η ≤ η_0`, the bound (3.3) gives

\[
   \|h\|_{C^{2, \gamma_0}(\partial B_1)} \;\le\; \delta_{\rm sph}(n, \gamma_0).
   \tag{4.2}
\]

The exponent in (4.1) is finite and positive because
`(1 − θ)κμ > 0`:

\[
   (1 - \theta)\,\kappa\,\mu \;\ge\;
   \frac{1 + \gamma - \gamma_0}{4}\cdot
   \frac{\alpha}{2\alpha + n - 1}\cdot
   \frac{1}{2(4n+9)(n-1)} \;>\; 0. \tag{4.3}
\]

This is a *positive* exponent in `η`, not sharp. The blow-up in the
denominator of (4.1) is benign: `δ_{\rm sph}, C_*` are positive
constants depending only on `(n, R, ρ_*, γ_0)`.

---

## 5. First-mode neutralisation (audit C7 / M4)

`thm:NS` requires the *barycenter* of `\widetilde\Omega` to lie at the
origin (eq. `normal`: `x_{\widetilde\Omega} = 0`). Cor 2.2's centre
`x_*` is the inscribed-ball centre supplied by Brandolini's Corollary 9,
not the barycenter. The two centres differ by

\[
   \bigl| x_{E_{\hat t}} - x_* \bigr| \;\le\;
   C(n)\,\|h\|_{L^\infty(\partial B_1)} \;\le\; C(n)\,\varepsilon. \tag{5.1}
\]

**Proof of (5.1).** With `∂E_{\hat t} = \{x_* + (1 + h(\theta))\theta\}`
and `|E_{\hat t}| = ω_n`, direct integration in polar coordinates gives

\[
   x_{E_{\hat t}} - x_* \;=\;
   \frac{1}{|E_{\hat t}|}\int_{\partial B_1}\!\theta\,
   \frac{(1 + h(\theta))^{n+1} - 1}{n+1}\,d\mathcal H^{n-1}(\theta).
\]

Taylor-expand `(1 + h)^{n+1} = 1 + (n+1)h + O(h²)` (valid since
`\|h\|_∞ ≤ 1/2` for `ε` small) and use
`\int_{∂B_1} θ\,dH^{n−1} = 0`:

\[
   x_{E_{\hat t}} - x_* \;=\;
   \omega_n^{-1}\int_{\partial B_1}\!\theta\,h(\theta)\,d\mathcal H^{n-1}
   \;+\; O(\|h\|_\infty^2),
\]

so `|x_{E_{\hat t}} − x_*| ≤ C(n)\,\|h\|_{L^∞}` (the first-mode
projection is bounded by the `L^∞` norm). ∎

**Shift.** Translate `∂E_{\hat t}` by `−x_{E_{\hat t}}` (so the
barycenter ends up at the origin). The new parametrisation
`\tilde h(θ) := h(θ) − ⟨x_{E_{\hat t}} − x_*, θ⟩ + O(ε²)` satisfies

\[
   \|\tilde h\|_{L^\infty} \le 2\,\varepsilon, \qquad
   \|\tilde h\|_{C^{3, \gamma}} \le 2\,\mathcal M, \tag{5.2}
\]

with the factor `2` absorbing the linear correction in `θ`. Re-running
Lemma 3.1 with `\tilde h` produces the same (3.3)–(4.2) up to constants
— concretely a doubling of `C_*` and a halving of `δ_{\rm sph}` in
(4.1). Both are absorbed in `η_0`.

**Volume normalisation.** Plan 2's bounded reduction has already set
`|E_{\hat t}| = ω_n` modulo `O(δ_T)` errors, which feed Corollary
`normabs` of `NearlySphericalClosure.tex` (vol/barycenter absorbed in
the constant). No additional argument is needed.

---

## 6. Final-step chain

Collect §1–§5. Define `η_0` as in (4.1). The implication chain reads:

| Step | Input | Output | Source |
|---|---|---|---|
| (i) Good level | Agent 1 Prop 3.1 | `\hat t ∈ [ρ_*, 1]` with `(D_H + D_I)(\hat t) ≤ η` | `Plan 3/agent1` |
| (ii) Brandolini squeeze + Lemma 2.1' | (i) | `∂E_{\hat t} = \{x_* + (1 + h)θ\}`, `\|h\|_∞ ≤ ε`, `\|h\|_{C^{1,γ}} ≤ C_{1,γ}` | Cor 2.2 of route doc |
| (iii) Interior Schauder for `−Δv = λ²` | (ii) + outer-collar dist. | `\|h\|_{C^{3,γ}} ≤ \mathcal M` | §2.1–§2.2; `SchauderInterpolation.tex` `prop:bootstrap` |
| (iv) Hölder interpolation `θ = θ_{3,2}` | (ii) + (iii) | `\|h\|_{C^{2,γ_0}} ≤ C_*\,η^{(1−θ)κμ}` | Lemma 3.1, eq. (3.3) |
| (v) Smallness threshold | `η ≤ η_0` of (4.1) | `\|h\|_{C^{2,γ_0}} ≤ δ_{\rm sph}(n, γ_0)` | (4.2) |
| (vi) First-mode shift | (v) + §5 | `\tilde h`, `x_{E_{\hat t}} = 0`, `\|\tilde h\|_{C^{2,γ_0}} ≤ δ_{\rm sph}` | §5 + `cor:normabs` |
| (vii) `thm:NS` | (vi) | `Asym(E_{\hat t})² ≤ C\,(E(E_{\hat t}) − E(B_1))` | `NearlySphericalClosure.tex` `thm:NS` |

**Theorem 6.1 (Schauder-interpolation closure at `\hat t`).** Let
`Ω ⊂ B_R`, `−Δu = 1`, and let `\hat t ∈ [ρ_*, 1]` be a good level (per
Agent 1) with `(D_H + D_I)(\hat t) ≤ η`. If
`η ≤ η_0(n, R, ρ_*, γ_0)` with `η_0` defined by (4.1), then the
rescaled-to-unit-volume set `E_{\hat t}` is `C^{2, γ_0}`-nearly
spherical with barycenter-centred parametrisation `\tilde h` satisfying

\[
   \|\tilde h\|_{C^{2, \gamma_0}(\partial B_1)} \;\le\; \delta_{\rm sph}(n, \gamma_0),
\]

and `thm:NS` (with the vol/barycenter absorption of `cor:normabs`)
yields the closing inequality

\[
   E(E_{\hat t}) - E(B_1) \;\ge\;
   \widetilde c_*(n)\,|B_1|^2\,C_1(n)^{-1}\,\mathrm{Asym}(E_{\hat t})^2.
\]

Agent 4 (`Plan 3/agent4-one-level-extraction.md`) then transfers this
inequality from the level `E_{\hat t}` to `Ω` via the cohesion identity,
closing Plan 3.

---

## 7. Audit cross-check

Discharged:

- **G6** (`C^{1,γ}` → small `C^{2,γ_0}`): closed by §2–§4 (interior
  Schauder + Hölder interpolation + threshold (4.1)).
- **C7** (first-mode neutralisation): closed by §5 (routine translation,
  error `O(ε)` absorbed in `η_0`).
- **M4** (Cor 2.2 vs. Agent 3's (G0)): the `\tilde h` produced in §5 is
  first-mode neutralised, `C^{1,γ}` small (in fact `C^{2,γ_0}` small),
  matching (G0) of `agent3-graph-cohesion.md`.

Out of scope: **S1, S2, G1–G5** (geometric Lemma 2.1', connectedness
reduction, rescaling bookkeeping, corrected `κ`; the last is *used*
here in its correct form).

---

## 8. Residual gaps

1. **Sharp rate.** `(1 − θ)κμ` is positive but `≪ 1/2`. Sharp
   `Asym² ≤ Cδ_T` at `Ω` does not require sharp rate on `η`: `thm:NS`
   is rate-preserving and is applied at a single level. Consistent
   with `BRANDOLINI_GRAPH_ENTRY_ROUTE.md` §5 and audit §G5.

2. **Lemma 2.1' (audit S1).** Cor 2.2 is conditional on the corrected
   quantitative annulus-to-graph lemma. Once written, the present note
   plugs in unchanged.

3. **Connectedness reduction (audit G1).** Cor 2.2 is conditional on
   `∂E_{\hat t}` having a single dominant component. Treated elsewhere.

4. **Rescaling bookkeeping (audit G4).** `λ ∈ [c(ρ_*), C(R)]` used to
   assert `\|v\|_{C^{3,α}} ≤ M_v`. Scaling laws should be recorded
   explicitly in a formal write-up.

5. **Choice of `γ`.** Concretely fix `γ = (1 + γ_0)/2`; then
   `θ = (2 + γ_0)/(3 + (1 + γ_0)/2)` is an explicit function of `γ_0`.

6. **Constants.** All `C_*, \mathcal M, C_{\rm sq}, C_{1,γ}, C_{\rm GN}`
   tracked as functions of `(n, R, ρ_*, γ_0)` only. The `M_m` of
   `SchauderInterpolation.tex` are iterated Lieberman-Schauder
   constants, finite at each `m`; `m = 3` (or `5`) is the only value
   used.

---

## 9. One-line summary

For `(D_H + D_I)(\hat t) ≤ η_0(n, R, ρ_*, γ_0)`, the combination

\[
   \text{Cor 2.2}\ \&\ \text{interior Schauder}\ \&\
   \text{Hölder interpolation}\ \&\ \text{barycenter shift}
\]

delivers a barycenter-centred `C^{2, γ_0}` parametrisation `\tilde h` of
`∂E_{\hat t}` (rescaled to unit volume) with
`\|\tilde h\|_{C^{2, γ_0}} ≤ δ_{\rm sph}(n, γ_0)`, which is exactly the
smallness hypothesis (eq. `normal`) of
`Final/NearlySphericalClosure.tex` `thm:NS`. The closing inequality
`Asym² ≤ C\,(E − E(B_1))` follows. The interpolation exponent
`(1 − θ)κμ > 0` is explicit; the smallness threshold `η_0` is given by
(4.1).
