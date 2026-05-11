# Weighted Serrin collar reduction

This note fills in the "Input S" box from
`selected-boundary-layer-theorem.md` and identifies the actual remaining
sharpness obstruction.

The conclusion is:

1. the weighted \(D_H\)-to-Serrin upgrade is available in selected collars, at
   least in the standard oscillation form, by interpolation;
2. the specific Input S used in `selected-boundary-layer-theorem.md` is even
   simpler: it follows from quantitative isoperimetry through \(D_I(t)\);
3. therefore the missing sharp piece is not Serrin stability. It is a boundary
   deficit propagation theorem that avoids the \(1/\eta\) loss in the
   near-boundary slab average.

For clarity this note is volume-normalized: \(|U|=|B_1|=\omega_n\). Constants
depend only on \(n\) and on the selected-minimizer collar constants.

## 1. Selected-collar hypotheses

Assume \(U=\{u>0\}\) is a Plan 1 selected minimizer already in the graph
regime. Thus there are \(t_0>0\), \(q_->0\), \(q_+<\infty\), and \(M<\infty\)
such that, for every regular \(0<t<t_0\),

\[
\Sigma_t=\{u=t\}
\]

is a \(C^{1,\gamma}\) hypersurface with uniformly controlled charts, and

\[
q_-\le |\nabla u|\le q_+
\quad\hbox{on }\Sigma_t,
\qquad
[|\nabla u|]_{C^\gamma(\Sigma_t)}\le M.
\]

These are exactly the estimates supplied by Plan 1 graph entry, the Bernoulli
condition, and Schauder estimates in the fixed collar.

## 2. Weighted variance gives ordinary variance

Let

\[
f_t=|\nabla u|\big|_{\Sigma_t},
\qquad
\bar f_t=\frac1{P(E_t)}\int_{\Sigma_t} f_t.
\]

The level-set identity gives

\[
\int_{\Sigma_t}\frac{(f_t-\bar f_t)^2}{f_t}
=
\frac{m(t)}{P(E_t)^2}D_H(t).
\]

Since \(q_-\le f_t\le q_+\) and \(m(t),P(E_t)\simeq_n1\) in the collar,

\[
\|f_t-\bar f_t\|_{L^2(\Sigma_t)}^2
\le C D_H(t).
\]

Thus \(D_H(t)\) is an ordinary \(L^2\) Serrin defect on selected collars.

## 3. Interpolation to oscillation

Let \(d=n-1\). On a uniformly \(C^{1,\gamma}\) compact hypersurface \(\Sigma\),
if \(g\in C^\gamma(\Sigma)\), then

\[
\|g\|_{L^\infty(\Sigma)}
\le
C
\|g\|_{L^2(\Sigma)}^{\frac{2\gamma}{2\gamma+d}}
[g]_{C^\gamma(\Sigma)}^{\frac{d}{2\gamma+d}}.
\]

Applying this to \(g=f_t-\bar f_t\), and using the uniform \(C^\gamma\) bound,
gives

\[
\|f_t-\bar f_t\|_{L^\infty(\Sigma_t)}
\le
C D_H(t)^{\frac{\gamma}{2\gamma+n-1}}.
\]

This is the precise bridge to Serrin-stability theorems stated in terms of
oscillation of the normal derivative. It is not sharp as a power of \(D_H\), but
it is enough to show that good levels are genuine approximate Serrin domains.

## 4. Input S is already implied by \(D_I\)

The Input S used in `selected-boundary-layer-theorem.md` was

\[
\mathcal A(E_t)^2
\le
C\left(D_H(t)+D_I(t)+|U\setminus E_t|^2\right),
\]

in normalized units. This estimate does not require Serrin stability. The
quantitative isoperimetric inequality gives directly

\[
\mathcal A(E_t)^2
\le C_n D_I(t),
\]

because \(m(t)\simeq_n1\) in the selected collar. Hence Input S holds with
\(D_H\) and the boundary-layer term unused:

\[
\boxed{
\mathcal A(E_t)^2\le C_n D_I(t)
\le C_n\bigl(D_H(t)+D_I(t)+|U\setminus E_t|^2\bigr).
}
\]

So the weighted Serrin upgrade is useful diagnostic information, but it is not
the bottleneck for Fraenkel asymmetry once the level set is already regular and
near the ball.

## 5. Boundary traces of \(D_I\) and \(D_H\)

The selected collar gives genuine boundary traces. Write

\[
q(y)=|\nabla u(y)|,\qquad y\in\partial U.
\]

The normal expansion

\[
\Sigma_t=
\left\{
y-\frac{t}{q(y)}\nu_U(y)+O(t^{1+\gamma})
:y\in\partial U
\right\}
\]

implies

\[
P(E_t)=P(U)+O(t^\gamma),
\qquad
m(t)=|U|-t\int_{\partial U}\frac1q+O(t^{1+\gamma}),
\]

and

\[
\int_{\Sigma_t}|\nabla u|\to\int_{\partial U}q,
\qquad
\int_{\Sigma_t}\frac1{|\nabla u|}\to\int_{\partial U}\frac1q.
\]

Consequently

\[
D_I(t)=D_I(0)+O(t^\gamma),
\qquad
D_H(t)=D_H(0)+O(t^\gamma),
\]

where

\[
D_I(0)=P(U)^2-c_n|U|^{2-2/n},
\]

and

\[
D_H(0)=
\left(\int_{\partial U}\frac1q\right)
\left(\int_{\partial U}q\right)-P(U)^2.
\]

Thus the level-set deficits do pass to the free boundary. What is still missing
is a sharp estimate of these boundary traces in terms of the torsion deficit.

## 6. The tempting boundary-deficit theorem is too strong

The sharp boundary-layer theorem would follow from the following statement, but
the statement is not true on the full nearly spherical class.

**Boundary deficit propagation.** For selected minimizers in the graph regime,

\[
D_I(0)+D_H(0)
\le
C\bigl(E(U)-E(B_1)\bigr).
\]

If it held, choose

\[
t\le c\bigl(E(U)-E(B_1)\bigr)^{1/\gamma}
\]

inside the selected collar. Then

\[
D_I(t)+D_H(t)\le C\bigl(E(U)-E(B_1)\bigr),
\]

and

\[
|U\setminus E_t|^2\le C t^2
=o\bigl(E(U)-E(B_1)\bigr).
\]

Combining Input S with the transfer lemma gives

\[
\mathcal A(U)^2
\le C\bigl(E(U)-E(B_1)\bigr),
\]

which is the sharp Saint-Venant/Faber-Krahn stability estimate for the selected
minimizer.

The obstruction is spectral. For a spherical harmonic perturbation of degree
\(k\ge2\), torsion energy is of size \(k\|g_k\|_2^2\), while \(D_I(0)\) and
\(D_H(0)\) are of size \(k^2\|g_k\|_2^2\). Thus high frequencies violate the
linear estimate.

## 7. Relation to Plan 1

The correct replacement is the selected Bernoulli law. The follow-up Plan 1
note `bernoulli-spectral-closure.md` linearizes the Bernoulli condition and
finds a spectral multiplier \(k-1\) on spherical harmonics. Since the
\(\alpha\)-penalty forcing is only \(O(\sigma)\), all \(k\ge2\) modes are
suppressed when \(\sigma\) is small; volume and barycenter remove \(k=0,1\).

In boundary-deficit language:

- \(D_H(0)\) measures failure of the Bernoulli datum \(q=|\nabla u|\) to be
  constant.
- \(D_I(0)\) measures the perimeter deficit of the selected free boundary.
- These defects are too strong to be bounded by torsion energy for arbitrary
  graphs, but selected minimizers cannot carry the high-frequency modes that
  cause the mismatch.

So the remaining work is a Plan 1 graph-entry plus Bernoulli spectral expansion,
not a stronger Serrin theorem for rough interior levels.
