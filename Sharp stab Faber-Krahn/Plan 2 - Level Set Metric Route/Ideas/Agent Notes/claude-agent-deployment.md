# Claude Agent Deployment Brief: Plan 2 Metric Level-Set Route

This file is meant to be copied into separate Claude-agent tasks. The goal is
to audit and complete the no-selection Plan 2 route for sharp quantitative
Saint--Venant/Faber--Krahn stability.

## Executive summary

The proposed Plan 2 route replaces the BDV selection principle by a global
level-set foliation argument.

For the torsion function
\[
-\Delta u=1\quad\hbox{in }\Omega,\qquad u=0\quad\hbox{on }\partial\Omega,
\]
write
\[
E_t=\{u>t\},\qquad m(t)=|E_t|.
\]
Parametrize levels by volume radius
\[
|E_\rho|=\omega_n\rho^n,\qquad E_\rho=\{u>t(\rho)\}.
\]

The exact level-set identity gives
\[
\delta_T(\Omega)
\simeq_n
\int (D_H(t)+D_I(t))\,w(t)\,dt,
\]
where
\[
D_H(t)
=
\left(\int_{\partial^*E_t}\frac1{|\nabla u|}\right)
\left(\int_{\partial^*E_t}|\nabla u|\right)
-P(E_t)^2
\]
is the Holder/Serrin velocity defect, and
\[
D_I(t)=P(E_t)^2-n^2\omega_n^{2/n}|E_t|^{2-2/n}
\]
is the squared isoperimetric defect.

The target metric theorem is:

> In a bounded class \(\Omega\subset B_R\), there is a dimensional constant
> \(C=C(n,R)\) such that
> \[
> \mathcal A(\Omega)^2\le C\,\delta_T(\Omega).
> \]
> The proof should use only the actual torsion level sets, not a BDV selected
> minimizer and not graph entry.

The current route is:

1. Use FvHT-style overlap gluing to choose coherent centers for the level
   family modulo translations.
2. Work in the metric quotient
   \[
   d_{\mathcal X}([A],[C])=\inf_a |A\Delta(C+a)|.
   \]
3. Prove the metric derivative estimate
   \[
   |\dot F_\rho|_{\mathcal X}^2
   \lesssim D_H(t(\rho))+D_I(t(\rho)),
   \qquad F_\rho:=\rho^{-1}E_\rho.
   \]
4. Apply a weighted metric trace at
   \[
   \rho_\delta=1-\kappa\sqrt{\delta_T(\Omega)}
   \]
   and transfer from \(E_{\rho_\delta}\) back to \(\Omega\). The removed layer
   has volume \(O(\sqrt{\delta_T})\), so the squared error is \(O(\delta_T)\).

## Current files to read first

Read these in order:

1. `Plan 2/metric-finite-perimeter-closure.md`
2. `Plan 2/gmt-inputs-for-metric-closure.md`
3. `Plan 2/outer-foliation-entry-proof-attempt.md`
4. `Plan 2/fvht-center-gluing-import.md`
5. `Plan 2/level-set-deficit-identity.md`

Useful background:

- `Plan 2/2501.04656v1.pdf`: Figalli--van Hintum--Tiba PL/BBL stability paper,
  especially the level/truncation center-gluing mechanism.
- `Final/BoundedReduction.tex`
- `Final/KohlerJobinTransfer.tex`
- `Final/SaintVenantAssembly.tex`
- `Final/master.tex`, around the references to FMP/Fusco--Julin.

## Important constraints

Do not solve the task by assuming:

- a BDV selected minimizer;
- global boundary graph parametrization;
- \(C^{1,\alpha}\) or better regularity of \(\partial\Omega\);
- a one-good-level argument with an \(\eta^{-1}\) average loss.

The desired proof must stay intrinsic to the actual finite-perimeter level sets
\(E_\rho\).

It is acceptable to assume a bounded class \(\Omega\subset B_R\), because the
existing Faber--Krahn route already has bounded reduction machinery.

## Agent 1: finite-perimeter level-set identity

### Task

Turn the identity in `level-set-deficit-identity.md` into a fully rigorous
finite-perimeter/coarea theorem.

### Target statement

For every open set \(\Omega\) of finite measure with torsion function
\(u=u_\Omega\), prove
\[
\frac{2}{|\Omega|}(E(\Omega)-E(B))
=
\frac1{|\Omega|}
\int_0^{\|u\|_\infty}
\frac{D_H(t)+D_I(t)}
{n^2\omega_n^{2/n}m(t)^{1-2/n}}\,dt
\]
for a.e. finite-perimeter level \(E_t=\{u>t\}\).

### Required proof components

1. Coarea for \(u\in H^1_0(\Omega)\):
   \[
   -m'(t)=\int_{\partial^*E_t}\frac1{|\nabla u|}\,d\mathcal H^{n-1}.
   \]
2. Weak divergence identity:
   \[
   \int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}=m(t).
   \]
3. Distributional justification of \(I'(s)=u^*(s)\) and
   \(I''(s)=-1/a(u^*(s))\).
4. Endpoint convexity-gap identity.

### Deliverable

A self-contained Markdown note with theorem, proof, and exact references for
coarea/truncation facts. Include any extra hypotheses if unavoidable.

### Failure mode to watch

Do not assume smooth level surfaces. All identities must be stated for a.e.
level via reduced boundaries.

## Agent 2: strong isoperimetry to homothetic velocity defect

### Task

Prove or precisely cite the homothetic velocity defect lemma used in
`metric-finite-perimeter-closure.md`.

### Target statement

Let \(E\subset B_R\) be finite perimeter, \(|E|=|B_\rho|\),
\(\rho\in[\rho_*,1]\). Prove that there exists \(z_E\) such that
\[
\left(
\int_{\partial^*E}
\left|
\frac{(x-z_E)\cdot\nu_E}{\rho}
-
\frac{P(B_\rho)}{P(E)}
\right|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}
\left(P(E)^2-P(B_\rho)^2\right).
\]

### Expected route

Use the strong FMP/Fusco--Julin oscillation-index form of quantitative
isoperimetry. The needed components are:

1. normal oscillation:
   \[
   \left(
   \int_{\partial^*E}
   \left|\nu_E-\frac{x-z_E}{|x-z_E|}\right|
   \right)^2
   \lesssim P(E)-P(B_\rho);
   \]
2. radial trace control:
   \[
   \left(
   \int_{\partial^*E}
   \left|\frac{|x-z_E|}{\rho}-1\right|
   \right)^2
   \lesssim_{R,\rho_*} P(E)-P(B_\rho).
   \]

### Deliverable

A precise proof or citation chain. If the radial trace control is not a known
direct consequence, isolate exactly what additional lemma is needed and prove
it under \(E\subset B_R\).

### Failure mode to watch

Normal oscillation alone does not automatically control radial distance on the
boundary. The radial term must be justified, not handwaved.

## Agent 3: metric first variation modulo translations

### Task

Make the \(L^1/\)translations metric derivative estimate rigorous for the
finite-perimeter torsion level family.

### Target statement

For \(F_\rho=\rho^{-1}E_\rho\) as an element of
\({\mathcal X}=L^1/\)translations, prove for a.e. \(\rho\):
\[
|\dot F_\rho|_{\mathcal X}
\le
C_{n,\rho_*}
\inf_{a\in\mathbb R^n}
\int_{\partial^*E_\rho}
\left|
V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho
\right|\,d\mathcal H^{n-1},
\]
where
\[
V_\rho=\frac{-t_\rho}{|\nabla u|},\qquad
H_{z,\rho}(x)=\frac{(x-z)\cdot\nu_\rho(x)}{\rho}.
\]

### Required proof components

1. Prove the formula first for smooth flows.
2. Pass to finite-perimeter flows by BV/coarea approximation.
3. Justify lower semicontinuity of metric derivatives under \(L^1\) convergence.
4. Explain how quotienting translations removes the \(a\cdot\nu_\rho\) mode.

### Deliverable

A proof note with references to BV evolution/perimeter variation facts.

### Failure mode to watch

Do not introduce a graph parametrization. The proof must use normal velocity
and reduced boundaries.

## Agent 4: weighted metric trace lemma

### Task

Prove the weighted trace step used to pass from integrated action to a specific
radius near \(\rho_\delta=1-\kappa\sqrt\delta\).

### Target statement

Let \(\gamma:[\rho_*,\rho_\delta]\to{\mathcal X}\) be an absolutely continuous
metric curve, and suppose
\[
\int_{\rho_*}^{\rho_\delta}
\left(d_{\mathcal X}(\gamma(\rho),B_1)^2+|\dot\gamma|^2\right)\,d\mu(\rho)
\le C\delta.
\]
Assume the profile-gap interval lower bound:
\[
\mu([a,b])\ge c(b-a)-C\delta.
\]
Prove that there exists
\[
\widehat\rho\in[\rho_\delta-C\delta,\rho_\delta]
\]
such that
\[
d_{\mathcal X}(\gamma(\widehat\rho),B_1)^2\le C\delta.
\]

### Deliverable

A clean metric-Sobolev proof, including treatment of possible microscopic
holes in \(d\mu=-t_\rho d\rho\).

### Failure mode to watch

Do not require pointwise lower bounds on \(-t_\rho\). The profile-gap estimate
only gives interval lower bounds up to \(O(\delta)\).

## Agent 5: bounded reduction and final assembly

### Task

Connect the bounded-class sharp Saint--Venant result from the metric Plan 2
route to the final Faber--Krahn theorem.

### Target chain

1. Bounded reduction gives \(\Omega\subset B_R\), with controlled deficit and
   asymmetry loss.
2. Metric Plan 2 gives
   \[
   \mathcal A(\Omega)^2\le C_{n,R}\delta_T(\Omega).
   \]
3. Kohler--Jobin transfer gives
   \[
   \lambda_1(\Omega)-\lambda_1(B)\ge c_{n,R}\mathcal A(\Omega)^2.
   \]

### Files to read

- `Final/BoundedReduction.tex`
- `Final/KohlerJobinTransfer.tex`
- `Final/SaintVenantAssembly.tex`
- `Plan 1/faber-krahn-transfer.md`

### Deliverable

An assembly note stating the final conditional theorem with every dependency
listed explicitly.

### Failure mode to watch

Track normalization conventions carefully: \(E(\Omega)=-T(\Omega)/2\),
\(\delta_T\), volume normalization, and scale-invariant constants.

## Agent 6: adversarial audit

### Task

Review the whole Plan 2 metric route for hidden selection-principle assumptions
or graph-regularity leakage.

### Specific questions

1. Does any step secretly require \(\partial E_\rho\) to be a graph?
2. Does FvHT center gluing control centers only at \(O(\sqrt\delta)\), and if
   so, does the proof avoid needing better center control?
3. Is the homothetic velocity defect really controlled by \(D_I\), or is there
   a missing radial trace theorem?
4. Is the metric trace valid with only interval lower bounds for \(d\mu\)?
5. Does the boundary-layer transfer from \(E_{\widehat\rho}\) to \(\Omega\)
   preserve the sharp exponent?

### Deliverable

A bug report ordered by severity. For each issue, state whether it is fatal,
repairable with a known theorem, or merely a wording/normalization problem.

## Suggested deployment order

Run Agents 2, 3, and 4 in parallel first. These are the core remaining checks.

Then run Agent 1, because the identity is foundational but less likely to
change the center/metric strategy.

Then run Agent 5 for final assembly.

Run Agent 6 after receiving the others' reports.

## Expected final outcome

If Agents 1--4 succeed, the Plan 2 route gives a genuinely quantitative
replacement for the BDV selection principle in the bounded class:
\[
\mathcal A(\Omega)^2\le C_{n,R}\delta_T(\Omega).
\]
Together with bounded reduction and Kohler--Jobin, this yields the sharp
quantitative Faber--Krahn inequality.

If one of Agents 2--4 fails, the failure should identify the precise missing
theorem. The most likely vulnerable point is Agent 2's radial trace estimate
inside the strong isoperimetric input.
