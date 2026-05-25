# True quantitative closure route

## Status

The manuscript is currently conditional.  The live gap is
`Assumption~\ref{ass:constructive-strong}` in `main.tex`.

To close the proof constructively, we must prove a quantitative Serrin-type
strong form for torsion superlevel sets, with computable constants and without
using the compactness-built Fusco-Julin strong form.

The target is not merely normal control.  The radial trace lemma needs volume
closeness and normal closeness with the **same centre**.

## Target theorem

For fixed `n >= 2`, `R >= 1`, and `0 < rho_* < 1`, prove that there are
computable constants

```tex
C_{\rm Ser}=C_{\rm Ser}(n,R,\rho_*), \qquad
\eta_{\rm Ser}=\eta_{\rm Ser}(n,R,\rho_*)>0
```

such that for a.e. torsion level radius `rho in [rho_*, rho_delta]` satisfying

```tex
D_H(t(rho)) + D_I(t(rho)) <= \eta_{\rm Ser},
```

there is a centre `z_rho` with

```tex
|E_rho \Delta B_rho(z_rho)|^2
+ \int_{\partial^*E_rho}
    \left|\nu_rho(x)-{x-z_rho \over |x-z_rho|}\right|^2
  d\mathcal H^{n-1}(x)
<= C_{\rm Ser}(n,R,\rho_*)
   (D_H(t(rho))+D_I(t(rho))).
```

This theorem must be proved with explicit constants.  No compactness,
contradiction, or appeal to Fusco-Julin strong form is allowed.

## Non-negotiable points

- Use the torsion convention of the manuscript:
  `v = u - t(rho) > 0` in `E_rho`, `v = 0` on `partial E_rho`, and
  `-Delta v = 1`.
- Weighted identities must use the positive weight `v`, not `-v`.
- The estimate must be linear in `D_H + D_I`; a weaker power will not close the
  kinetic estimate.
- The same centre must control both `|E_rho Delta B_rho(z)|` and
  `int |nu-e_z|^2`.
- Constants may depend on `n,R,rho_*`, but not on the particular level or
  domain.

## Phase 1: smooth model theorem

First prove the target for a bounded `C^2` domain `Omega' subset B_R`, with
`|Omega'| = omega_n rho^n`, `rho in [rho_*,1]`, and torsion function

```tex
-\Delta v = 1 \text{ in } Omega', \qquad v=0 \text{ on } \partial Omega',
\qquad v>0.
```

The smooth theorem should assume the same smallness condition:

```tex
D_H(Omega') + D_I(Omega') <= eta.
```

Here

```tex
D_H = \left(\int_{\partial Omega'} {1\over |\nabla v|}\right)
      \left(\int_{\partial Omega'} |\nabla v|\right)
      - P(Omega')^2,

D_I = P(Omega')^2 - P(B_rho)^2.
```

### 1A. A priori good-level bounds

Derive explicit consequences of `D_H + D_I <= eta`:

- upper and lower perimeter bounds `P(Omega') ~ P(B_rho)`;
- `P(Omega') <= C(n,rho_*)`;
- `Omega' subset B_R` and Talenti give `||grad v||_infty <= C(n)R`;
- the flux identity gives `int_{partial Omega'} |grad v| = |Omega'|`;
- the coarea/level convention gives `int_{partial Omega'} 1/|grad v| < infinity`.

This step should not use a lower pointwise bound for `|grad v|`.

### 1B. Convert `D_H` into boundary gradient oscillation

Let `g = |grad v|` on `partial Omega'`, `P=P(Omega')`,
`alpha=int 1/g`, and `beta=int g=|Omega'|`.

Prove a quantitative variance estimate of the form

```tex
\int_{\partial Omega'} |g-\bar g|^2 dH
<= C(n,R,rho_*) D_H,
```

for an explicitly chosen reference value `bar g`.  Natural candidates:

- arithmetic average `beta/P`;
- harmonic/CS reference `P/alpha`;
- Serrin target `rho/n` or a Pohozaev-determined constant.

The verifier must check the exact choice.  The reference has to be compatible
with the Reilly/Serrin identity in Phase 1C.

Expected tool: the identity

```tex
D_H = alpha beta - P^2
```

is a weighted Cauchy-Schwarz defect.  With `g <= C(n)R` and `P` controlled,
it should control the unweighted `L^2` oscillation of `g` around a suitable
average.

### 1C. Weighted Reilly/Serrin estimate

Prove the make-or-break estimate

```tex
\int_{Omega'} v |D^2v + I/n|^2 dx
<= C(n,R,rho_*) D_H.
```

This must be an explicit integral-identity proof.

Acceptable routes:

- weighted Reilly identity with the positive torsion weight `v`;
- Weinberger `P`-function plus a boundary-curvature cancellation;
- Magnanini-Poggesi style integral identities, with all constants traced.

Forbidden route:

- compactness proof that small boundary gradient oscillation implies closeness.

Verifier pressure points:

- Check the sign of every boundary term.
- Check the convention for the outer normal.
- Check that the curvature term is actually removed or controlled.
- Check that the right side is linear in `D_H`, not `D_H^theta`.
- Check that no hidden lower bound on `|grad v|` is used.

### 1D. Extract a centre from Hessian closeness

From

```tex
\int v |D^2v + I/n|^2
```

construct a centre `z` and a quadratic ball profile

```tex
Q_z(x) = (rho^2 - |x-z|^2)/(2n)
```

or an equivalent best-fit profile, and prove quantitative closeness of
`grad v` to `-(x-z)/n` in a boundary collar.

This is where the centre used later must be fixed.

Required output:

```tex
\int_{\partial Omega'} |\nu - e_z|^2 dH
<= C(n,R,rho_*) (D_H + D_I).
```

The proof must be trace-based and quantitative.  It may use the collar supplied
by the positive weight `v`, but must state explicitly how the weight is removed
near the boundary.

### 1E. Same-centre volume control

Using the same `z` from Phase 1D, prove

```tex
|Omega' \Delta B_rho(z)|^2
<= C(n,R,rho_*) (D_H + D_I).
```

Two possible routes:

1. Directly obtain radial graph/height control from the same quadratic profile.
2. Use FMP Fraenkel volume control for some centre `z_FMP`, then prove an
   explicit centre-alignment estimate `|z-z_FMP| <= C(D_H+D_I)^{1/2}`.

The first route is cleaner.  The second route is acceptable only if the
centre-alignment proof is explicit and does not invoke compactness.

## Phase 2: finite-perimeter/a.e. level passage

After the smooth theorem is proved, transfer it to the manuscript's level sets.

Required tasks:

- restrict to a.e. regular levels first, where the level set is smooth enough;
- prove the constants are stable along the regular-level approximation;
- pass to finite-perimeter levels using only the BV/coarea tools already in
  Appendix `app:bv`;
- preserve the same centre in the limiting estimate;
- prove the exceptional set of radii is null in the `rho` parametrisation used
  by the manuscript.

No new nonconstructive compactness constant may enter this passage.

## Phase 3: manuscript integration

Once Phases 1 and 2 are complete:

1. Replace `Assumption~\ref{ass:constructive-strong}` in `main.tex` by a theorem
   with proof or with a self-contained imported proposition.
2. Update `Theorem~\ref{thm:boundedSV}` so it is no longer conditional.
3. Update the dependency certificate: the constructive Serrin theorem becomes
   proved internally or quoted with exact constructive constants.
4. Confirm no live reference to FJ strong form remains in compiled files:

```bash
rg -n -F "FJ2014" "Sharp Faber-Krahn Manuscript/main.tex" \
  "Sharp Faber-Krahn Manuscript/parts/sec_bounded_reduction_body.tex"
rg -n -F "thm:FJ" "Sharp Faber-Krahn Manuscript/main.tex" \
  "Sharp Faber-Krahn Manuscript/parts/sec_bounded_reduction_body.tex"
rg -n -F "C_{\\rm FJ}" "Sharp Faber-Krahn Manuscript/main.tex" \
  "Sharp Faber-Krahn Manuscript/parts/sec_bounded_reduction_body.tex"
```

5. Compile twice:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp main.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp main.tex
```

## Agent execution protocol

Run independent agents on the following tasks.

### Agent A: Reilly identity audit

Goal: prove or refute Phase 1C.

Deliverable:

- exact identity used;
- sign convention;
- boundary terms;
- final inequality with explicit dependencies;
- list of hidden assumptions, especially smoothness, connectedness, and
  lower bounds on `|grad v|`.

### Agent B: `D_H` to oscillation audit

Goal: prove Phase 1B with the correct reference constant.

Deliverable:

- chosen `bar g`;
- exact inequality relating `D_H` to `int |g-bar g|^2`;
- constants in terms of `n,R,rho_*`;
- statement of whether the estimate survives without pointwise lower bounds for
  `g`.

### Agent C: trace and same-centre audit

Goal: prove or refute Phases 1D and 1E.

Deliverable:

- construction of `z`;
- trace inequality from weighted Hessian closeness to boundary normal closeness;
- same-centre volume control;
- explicit treatment of the boundary collar and the weight `v`.

### Agent D: finite-perimeter passage

Goal: prove Phase 2.

Deliverable:

- smooth-level approximation scheme;
- convergence mode for normals and symmetric differences;
- proof that constants are stable;
- exact null-set bookkeeping in the `rho` parametrisation.

## Closure criterion

The proof is truly quantitative only when all of the following are true:

- `Assumption~\ref{ass:constructive-strong}` has been replaced by a proved
  theorem.
- The theorem gives same-centre volume plus normal control.
- Every constant in that theorem is computable from `n,R,rho_*`.
- The proof uses no compactness/contradiction constant.
- The final LaTeX build has no undefined references.
- The dependency certificate no longer lists any unproved nonstandard input.

