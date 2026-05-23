# Agent 2 — Homothetic velocity defect lemma

This note audits the homothetic velocity defect lemma invoked in
`metric-finite-perimeter-closure.md` (§3) and asserted as the radial trace
estimate (1.2) of `gmt-inputs-for-metric-closure.md`. The conclusion is
conditional: the lemma reduces to a precise radial \(L^1\)-trace inequality
that is **not** available in the cited FMP/Fusco–Julin package. The missing
input is isolated below as Conjecture 3.6.

## 1. Precise statement

**Target.** Let \(E\subset B_R\subset\mathbb R^n\) be a set of finite perimeter
with \(|E|=|B_\rho|\), \(\rho\in[\rho_*,1]\). Let \(z_E\) be the Fraenkel
asymmetry center for \(E\) (centre of a ball achieving the Fraenkel infimum;
unique up to a measure-zero set when \(E\) is close to a ball, by
Cicalese–Leonardi 2012). Then there is a constant \(C=C(n,\rho_*,R)\) with
\(C\sim R^{n-1}\) for the boundary–weighted version, such that
\[
\left(\int_{\partial^*E}\left|\frac{(x-z_E)\cdot\nu_E}{\rho}
-\frac{P(B_\rho)}{P(E)}\right|d\mathcal H^{n-1}\right)^2
\le C\bigl(P(E)^2-P(B_\rho)^2\bigr).
\tag{*}
\]

## 2. Cited inputs (hypotheses verified)

(A) **Fuglede / FMP volume Fraenkel.** Fusco–Maggi–Pratelli 2008 Ann. of
Math.; Figalli–Maggi–Pratelli 2010 Invent. Math.: for a finite-perimeter
set with \(|E|=|B_\rho|\),
\[
\inf_{z}\frac{|E\Delta B_\rho(z)|^2}{|B_\rho|^2}\le c_1\bigl(P(E)-P(B_\rho)\bigr).
\tag{A}
\]

(B) **Selection / interior containment.** Cicalese–Leonardi 2012 ARMA: the
asymmetric Fraenkel centre \(z_E\) satisfies \(B(z_E,\rho/2)\subset E\) under
the smallness regime relevant here, and is uniquely defined modulo
\(\mathcal H^{n-1}\)-null sets.

(C) **Fusco–Julin strong oscillation index.** Fusco–Julin 2014 Calc. Var. PDE:
\[
\left(\int_{\partial^*E}\left|\nu_E-\frac{x-z_E}{|x-z_E|}\right|
d\mathcal H^{n-1}\right)^2\le c_2\bigl(P(E)-P(B_\rho)\bigr).
\tag{B}
\]

(D) **Slicing / coarea.** Maggi 2012 (Cambridge), Chs. 13, 17;
Ambrosio–Fusco–Pallara 2000, Thms. 2.39, 3.40.

## 3. Where the proof closes — and where it does not

### 3.1 Algebraic combination conditional on radial trace

Suppose, in addition to (B), the **radial \(L^1\)-trace bound**:
\[
\left(\int_{\partial^*E}\left|\frac{|x-z_E|}{\rho}-1\right|d\mathcal H^{n-1}\right)^2
\le c_3\bigl(P(E)-P(B_\rho)\bigr).
\tag{R}
\]
Then (*) follows. Write
\[
\frac{(x-z_E)\cdot\nu_E}{\rho}-1
=\frac{|x-z_E|}{\rho}\left(\frac{(x-z_E)}{|x-z_E|}\cdot\nu_E\right)-1
=\left(\frac{|x-z_E|}{\rho}-1\right)\left(\frac{(x-z_E)}{|x-z_E|}\cdot\nu_E\right)
+\left(\frac{(x-z_E)}{|x-z_E|}\cdot\nu_E-1\right);
\]
the first term is bounded in \(L^1\) by (R) (cosine factor bounded by 1), the
second by (B) (since \(|u-1|\le|u-v|\) for unit \(u\) and the radial unit \(v\)).
Replacing the constant 1 by \(P(B_\rho)/P(E)=1+O(P(E)-P(B_\rho))\) costs
another factor \(P(E)\) absorbed into \(C\). Squaring and combining: (*).
\(\square\)

So the residual gap is exactly (R).

### 3.2 The divergence-theorem route fails for the unsigned norm

A natural attempt: for the test field \(\Phi(x)=\Psi(|x-z_E|)\,e_r\) with
\(e_r=(x-z_E)/|x-z_E|\), and \(\Psi\) supported near \(r=\rho\),
\[
\int_{\partial^*E}\Psi(|x-z_E|)\,(e_r\cdot\nu_E)\,d\mathcal H^{n-1}
=\int_E\operatorname{div}(\Psi\,e_r)\,dx
=\int_E\left(\Psi'(|x-z_E|)+(n-1)\Psi(|x-z_E|)/|x-z_E|\right)dx.
\]
For \(\Psi(r)=\operatorname{sgn}(r-\rho)\) this controls a *signed* radial
moment:
\[
\left|\int_{\partial^*E}\operatorname{sgn}(|x-z_E|-\rho)\,(e_r\cdot\nu_E)\right|
\le c\sqrt{P(E)-P(B_\rho)}
\]
via (A). The unsigned norm \(\int||x-z_E|/\rho-1|\) is genuinely larger and
not bounded by this route.

### 3.3 The slicing route reduces (R) to an equivalent radial perimeter excess

Via radial slicing through \(z_E\),
\[
\int_{\partial^*E}\Psi(|x-z_E|)\,|e_r\cdot\nu_E|\,d\mathcal H^{n-1}
=\int_{S^{n-1}}\sum_{r\in\partial^*E_\theta}\Psi(r)\,r^{n-1}\,d\theta,
\]
where \(\partial^*E_\theta\) is the 1D reduced boundary of the ray-slice.
Picking \(\Psi(r)=|r-\rho|\) and applying the elementary 1D mismatch lemma

**Lemma 3.5.** For \(A\subset[\alpha,\beta]\) with \(N\) reduced-boundary
points \(r_1\le\dots\le r_N\),
\[
\sum_j|r_j-\rho|\le 2|A\Delta(0,\rho)|_1+(\beta-\alpha)(N-1)^+,
\]
proved by interlacing the points \(r_j\) with \(\rho\) and pairing.

Integrating in \(\theta\) and using (A) on the slicewise asymmetry,
\[
\int_{\partial^*E}|x-z_E|\cdot|e_r\cdot\nu_E|\,d\mathcal H^{n-1}
\le c\bigl(P(E)-P(B_\rho)\bigr)^{1/2}\cdot R^{n-1}
+ R\int_{S^{n-1}}(\#\partial^*E_\theta-1)^+\,d\theta.
\]
By the slicing perimeter formula (Maggi 2012 Thm. 18.11),
\[
\int_{S^{n-1}}\#\partial^*E_\theta\,d\theta
=\int_{\partial^*E}\frac{|e_r\cdot\nu_E|}{|x-z_E|^{n-1}}\,d\mathcal H^{n-1}.
\]
Hence the angular excess term equals
\[
\int_{\partial^*E}\frac{|e_r\cdot\nu_E|}{|x-z_E|^{n-1}}
\,d\mathcal H^{n-1}-n\omega_n.
\]
Bounding this by \(C(P(E)-P(B_\rho))\) is equivalent (up to the bounded
weight \(\rho_*^{-(n-1)}\le|x-z_E|^{-(n-1)}\le 2^{n-1}\rho^{-(n-1)}\) from
(B)+(C)) to the target inequality (R) itself. **The reduction is circular.**

### 3.6 The genuine missing input

**Conjecture 3.6 (radial weighted perimeter excess).** Under the hypotheses
of the theorem,
\[
\int_{\partial^*E}\frac{|e_r\cdot\nu_E|}{|x-z_E|^{n-1}}\,d\mathcal H^{n-1}
- n\omega_n
\le C_{n,\rho_*,R}\bigl(P(E)-P(B_\rho)\bigr).
\tag{C3.6}
\]
Equivalent to (R) up to bounded constants. **Not** a consequence of
(A)+(B)+(C)+\(E\subset B_R\). The natural approach is an \(L^2\)-spherical
trace / Sobolev embedding on \(\partial B_\rho\), passing through the
\(H^{1/2}\)-norm of the boundary perturbation — but this requires turning
the strong oscillation index (B) into a *quadratic* \(L^2\)-bound on
\(\nu_E-e_r\) and using a near-spherical trace identity, which lives outside
the FMP/Fusco–Julin package.

## 4. New vs. cited

| Component                              | Source                          |
|---------------------------------------|---------------------------------|
| (A) volume Fraenkel                   | FMP 2010 Invent.; FMP 2008 AM   |
| (B) normal oscillation                | Fusco–Julin 2014 Calc. Var.     |
| asymmetric centre \(z_E\)             | Cicalese–Leonardi 2012 ARMA     |
| §3.1 algebraic combination            | new (elementary)                |
| §3.2 divergence route fails           | new observation                 |
| §3.3 slicing reduction to (C3.6)      | new (key obstruction)           |
| Lemma 3.5 1D mismatch                 | folklore / Maggi Sec. 18        |
| Conjecture 3.6                        | **open**                        |

## 5. Severity report for Agent 6

**The radial trace estimate (R) is the precise bottleneck of the Plan 2 route.**
It is the failure mode the deployment brief flagged. Status: substantive,
not fatal, repairable in principle by an \(L^2\)-trace argument near the
ball, but **not** by any combination of (A)+(B)+(C)+\(E\subset B_R\).

For Agent 6 / the user, three remediations are plausible:

1. **Quantitative spherical \(H^{1/2}\) trace.** Prove (R) under an
   additional smallness hypothesis using the Fraenkel barycenter and a
   near-spherical normal graph in the *Lipschitz* regularity class supplied
   by Cicalese–Leonardi 2012 (this avoids \(C^{1,\alpha}\) but uses Lipschitz
   parametrization on the bulk of \(\partial^*E\)).
2. **Strong containment input.** If \(B(z_E,\rho(1-\eta))\subset E\subset
   B(z_E,\rho(1+\eta))\) with \(\eta=O(\sqrt{P(E)-P(B_\rho)})\) — i.e. the
   *Hausdorff* near-spherical containment of Fusco–Julin — then (R) follows
   from \(\eta\cdot P(E)\) trivially. The brief's "no graph" constraint
   permits this, since it is a measure-theoretic statement; it is the
   correct workaround for Plan 2.
3. **Replace (R) by a weaker \(L^2\) form.** The application in
   `metric-finite-perimeter-closure.md` (§3) actually integrates against
   the deficit measure. The \(L^2\) form
   \(\int||x-z_E|/\rho-1|^2\le C(P(E)-P(B_\rho))\) suffices and is closer to
   the natural spectral-gap estimate at the ball.

## 6. Conclusion

Conditional on Conjecture 3.6 (or its Hausdorff containment substitute),
the homothetic velocity defect lemma (*) holds with explicit constant. The
unconditional proof is **open**. This is the primary substantive gap of
the Plan 2 route, as anticipated.
