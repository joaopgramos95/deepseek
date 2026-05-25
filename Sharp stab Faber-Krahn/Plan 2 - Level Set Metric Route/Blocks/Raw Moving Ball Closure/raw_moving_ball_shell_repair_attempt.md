# Shell/Coarea Repair Attempt for the Raw Moving-Ball Closure

Date: 2026-05-25

Source under repair:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

This note records a rigorous repair pass on the obstruction found in the
audit of the affine shell estimate. The outcome is deliberately conservative:
two defects admit clean repairs, but the current manuscript still needs one
new finite-perimeter local-to-global shell theorem before the closure can be
called manuscript-grade.

## Verdict of This Repair Pass

```text
PARTIAL REPAIR ONLY
```

The following can be fixed cleanly:

1. the non-countable admissibility family;
2. the wrong error measure in the Borel approximation proof of `varcoarea`.

The following is not honestly fixed by the current proof:

1. the compact-exhaustion/no-escape step in Lemma `shell`.

Replacing it by “standard localization” would hide exactly the finite-perimeter
issue the audit found. The missing theorem is now isolated below.

## Repair 1: Countable Admissibility on Compact Pieces

The current admissibility definition is invalid because it registers endpoint
pairs involving the tested radius:

```tex
-w(\rho), \qquad \nabla u(x)\cdot ((x-z)/\rho+a).
```

Those pairs are not a fixed countable family.

A correct countable replacement is to fix once and for all:

```tex
K_m := \{x\in\Omega:\operatorname{dist}(x,\mathbb R^n\setminus\Omega)\ge 1/m\},
```

with empty sets omitted, and a rational parameter set

```tex
c\in\mathbb Q\cap[-1,0],\quad
\lambda\in\mathbb Q\cap[1,1/\rho_*],\quad
z,a\in\mathbb Q^n,\quad r\in\mathbb Q_{>0}.
```

For these parameters define

```tex
b_{\lambda,z,a}(x):=\nabla u(x)\cdot(\lambda(x-z)+a),
```

and localized endpoint pairs

```tex
\alpha_{m,c,\lambda,z,a,r}
:=
{\bf 1}_{K_m}\bigl(\min(c,b_{\lambda,z,a})-r\bigr),

\beta_{m,c,\lambda,z,a,r}
:=
{\bf 1}_{K_m}\bigl(\max(c,b_{\lambda,z,a})+r\bigr).
```

Outside `K_m`, both endpoints are set to `0`, so the slab is empty there.
Each pair is bounded Borel because `u` is `C^1` on `K_m`. The family is now
genuinely countable and independent of the tested radius.

For a real radius `rho`, real centre/translation `(z,a)`, and compact `K_m`,
approximate

```tex
c=-w(\rho),\qquad \lambda=1/\rho,\qquad z,\qquad a
```

by rational parameters. On `K_m`,

```tex
|b_{\lambda,z,a}-b_{\lambda',z',a'}|
\le
C(m,R,\rho_*,z,a)
\bigl(|\lambda-\lambda'|+|z-z'|+|a-a'|\bigr),
```

because `|\nabla u|` is bounded on `K_m`. The maps
`s -> min(c,s)` and `s -> max(c,s)` are `1`-Lipschitz, so the real slab is
contained in a rational outward buffer. This repairs the countability problem
for localized compact pieces.

Important limitation: this only gives shell estimates on fixed compact
pieces `K_m`. It does not by itself prove the global shell estimate.

## Repair 2: Correct Weighted `varcoarea`

The Borel approximation step in the manuscript uses the wrong error measure.
The corrected lemma should be:

```tex
\begin{lemma}[Two-sided variable-thickness coarea differentiation]
Let \alpha\le\beta be bounded Borel functions on \mathbb R^n. Then, for
Lebesgue-a.e. level t such that E_t=\{u>t\} has finite perimeter and
\int_{\partial^*E_t}|\nabla u|^{-1}\,d\mathcal H^{n-1}<\infty,
\[
   \lim_{h\downarrow0}\frac1h
   |\{x:h\alpha(x)<u(x)-t<h\beta(x)\}|
   =
   \int_{\partial^*E_t}
      \frac{\beta-\alpha}{|\nabla u|}\,d\mathcal H^{n-1}.
\]
\end{lemma}
```

For simple pairs this is the BV coarea formula plus Lebesgue differentiation
of

```tex
\tau\mapsto
\int_{\partial^*\{u>\tau\}}
   {\bf 1}_A|\nabla u|^{-1}\,d\mathcal H^{n-1}.
```

For bounded Borel pairs, choose simple pairs sandwiching the slab. The outer
approximation gives

```tex
\int(\sigma'-\sigma)|\nabla u|^{-1}
\le
\int(\beta-\alpha)|\nabla u|^{-1}
+2\eta\int_{\partial^*E_t}|\nabla u|^{-1}\,d\mathcal H^{n-1},
```

not `+ 2 eta P(E_t)`. The last term vanishes as `eta -> 0` because the
weighted boundary measure is finite at the levels under consideration.

This fixes the hidden lower-gradient issue in Lemma `varcoarea`.

## Measure Transfer from Level `t` to Radius `rho`

The corrected `varcoarea` is naturally a statement for Lebesgue-a.e. level
`t`, not automatically for Lebesgue-a.e. radius `rho`.

For the moving-ball proof this is enough on the good-density set

```tex
G_\tau=\{\rho:w(\rho)\ge\tau_0\}.
```

Indeed, if `N` is a null set of bad levels in `t`, then

```tex
|\{\rho\in G_\tau:t(\rho)\in N\}|
\le
\tau_0^{-1}
\int_{\{\rho\in G_\tau:t(\rho)\in N\}}w(\rho)\,d\rho
=0.
```

Thus the corrected countable localized `varcoarea` gives a full-measure set
inside `G_tau`, which is exactly where the proof uses the affine shell
estimate. Bad-density levels are paid by the unconditional Lipschitz bound for
`q`.

## Remaining Missing Theorem: No-Escape / Global Shell

The current proof still fails when it passes from compact pieces to the full
symmetric difference. A rigorous replacement must prove the following theorem
or an equivalent one.

```tex
\begin{theorem}[Global finite-perimeter shell differentiation]
Let \rho\in G_\tau be a good radius satisfying the finite-perimeter,
Sobolev--Sard, and corrected localized coarea conditions above. Let
W(x)=(x-z)/\rho+a and
T_h(x)=x+hW(x). Then
\[
   \limsup_{h\downarrow0}
   \frac{|E_{\rho+h}\Delta T_h(E_\rho)|}{h}
   \le
   \int_{\partial^*E_\rho}
      \left|
      \frac{w(\rho)}{|\nabla u|}
      -W\cdot\nu_\rho
      \right|\,d\mathcal H^{n-1}.
\]
\end{theorem}
```

Equivalently, with `F=w+\nabla u\cdot W`,

```tex
\limsup_{h\downarrow0}
\frac{|E_{\rho+h}\Delta T_h(E_\rho)|}{h}
\le
\int_{\partial^*E_\rho}
\frac{|F|}{|\nabla u|}\,d\mathcal H^{n-1}.
```

The compact-piece proof proves this only on each `K_m`. What remains is a
no-escape estimate:

```tex
\lim_{m\to\infty}\limsup_{h\downarrow0}
\frac{|(E_{\rho+h}\Delta T_h(E_\rho))\setminus K_m|}{h}
\le
\lim_{m\to\infty}
\int_{\partial^*E_\rho\setminus K_m}
   \left|
   \frac{w(\rho)}{|\nabla u|}-W\cdot\nu_\rho
   \right|\,d\mathcal H^{n-1}
=0.
```

This is not a formal consequence of the localized coarea lemma. It is a
genuine finite-perimeter deformation statement.

## Plausible Route to the Missing Theorem

The honest proof route is a De Giorgi blow-up/Vitali covering argument at
`H^{n-1}`-a.e. point of `partial^*E_rho`:

1. At `H^{n-1}`-a.e. `x0 in partial^*E_rho`, use approximate
   differentiability of `u`, the identity
   `nu_rho=-grad u/|grad u|`, and the reduced-boundary half-space blow-up.
2. In balls centered at such points, prove the local asymptotic density
   ```tex
   |E_{\rho+h}\Delta T_h(E_\rho)|
   \sim
   h\left|
   \frac{w(\rho)}{|\nabla u(x0)|}-W(x0)\cdot\nu_\rho(x0)
   \right|
   \omega_{n-1}r^{n-1}
   ```
   after first taking `h/r -> 0` and then `r -> 0`.
3. Use the coarea formula to show the symmetric difference is concentrated in
   an `O(h)` level tube around `partial^*E_rho`; this rules out bulk mass away
   from the reduced boundary.
4. Apply a Vitali covering argument and the Besicovitch differentiation
   theorem for the finite measure
   ```tex
   \left(1+\frac{w(\rho)}{|\nabla u|}+|W|\right)
   \mathcal H^{n-1}\llcorner\partial^*E_\rho.
   ```
5. Sum the local estimates to obtain the global limsup bound.

This route would not use a graph parametrisation, a selection principle, BDV,
or a pointwise lower bound on `|\nabla u|`. It is, however, a real theorem and
should be written as such, not hidden in a one-line compact-exhaustion
sentence.

## Why the Tempting Compact-Containment Shortcut Is Not Acceptable

One might try to say that positive superlevels are compactly contained in
`Omega`, so a single compact set `K compactly contained in Omega` suffices.
That is not available under the stated hypothesis “bounded open `Omega`”.
For rough open sets, `u in H^1_0(Omega)` gives quasi-boundary vanishing, not
uniform topological boundary control. Thus a compact-strip argument would add
an unstated regularity hypothesis on `Omega`.

If the theorem were restricted to sufficiently regular domains where
`{u>t(rho)}` is compactly contained in `Omega` for the relevant levels, then
the localized rational-parameter repair above would likely close the shell
estimate. That is not the stated theorem.

## Recommended Manuscript Patch

Do not leave the current shell proof as-is. The manuscript should be revised
in one of two honest ways.

### Option A: Prove the Global Shell Theorem

Replace the current admissibility/`varcoarea`/compact-exhaustion block by:

1. corrected weighted `varcoarea`;
2. corrected countable localized admissibility on `G_tau`;
3. a full De Giorgi blow-up proof of the global finite-perimeter shell
   differentiation theorem.

Then `qplus`, `positivekinetic`, `endpoint`, and `boundedSV` can remain
structurally unchanged.

### Option B: State a Conditional Closure

If the global shell theorem is not proved in the manuscript, state it as an
explicit hypothesis:

```tex
\textbf{(Shell)}\quad
\limsup_{h\downarrow0}
\frac{|E_{\rho+h}\Delta T_h(E_\rho)|}{h}
\le
\int_{\partial^*E_\rho}
|V_\rho-H_{z,\rho}-a\cdot\nu_\rho|\,d\mathcal H^{n-1}
```

for a.e. `rho in G_tau` and every affine moving-ball field. Then present the
rest of the moving-ball argument as a conditional closure. This is weaker but
mathematically honest.

## Bottom Line

This pass repairs the easy measure-theoretic mistakes but does not honestly
close the finite-perimeter affine shell estimate. The route remains promising:
all downstream bookkeeping survives, and the missing input is now a single
precise global shell differentiation theorem. That theorem is the next
manuscript-grade task.
