# Bernoulli expansion proofs: corrected status

This note corrects the overclaims in the previous version of
`bernoulli-expansion-proofs.md`. The Bernoulli spectral idea remains promising,
but the earlier writeup did **not** prove the required Schauder/tame remainder
estimates. In particular, it incorrectly evaluated the interior harmonic first
variation outside \(B_1\).

## 1. What was wrong

The previous proof defined

\[
u_1(r,\theta)=\frac1N\sum_{k\ge0}r^k g_k(\theta)
\]

as the harmonic extension of \(g/N\) in \(B_1\), then evaluated it at
\(r=1+g(\theta)\). For a general \(g\in C^{2,\gamma}\), this series is only an
interior harmonic expansion. It has no controlled extension to \(r>1\). Thus
the claimed estimates for

\[
u_1((1+g)\theta),\qquad \partial_r u_1(1+g,\theta)
\]

are not valid.

Consequently, the claimed quadratic Schauder remainder

\[
\|u_g-u_{B_1}-u_1\|_{C^{2,\gamma}}\lesssim \|g\|_{C^{2,\gamma}}^2
\]

on \(U_g\), and the derived tame estimate

\[
\|R_q(g)\|_{L^2}
\lesssim
\|g\|_{C^{2,\gamma}}\|g\|_{L^2},
\]

were not proved.

## 2. Correct fixed-domain formulation

Let

\[
\Phi_g(r\theta)=(r+\chi(r)g(\theta))\theta,\qquad
\widetilde u_g=u_g\circ\Phi_g.
\]

Then \(\widetilde u_g=0\) on \(\partial B_1\), and

\[
-\operatorname{div}(A_g\nabla\widetilde u_g)=J_g
\quad\hbox{in }B_1,
\qquad
A_g=J_gD\Phi_g^{-1}D\Phi_g^{-T}.
\]

This is the right framework. The first variation of the *shape derivative*
\(u'_g\) still satisfies

\[
\Delta u'=0\quad\hbox{in }B_1,\qquad
u'|_{\partial B_1}=\frac{g}{N}.
\]

But the pullback derivative is not simply \(u'\circ\Phi_g\) evaluated outside
the ball. Boundary-gradient expansions must be derived on the fixed boundary
from the pulled-back equation and the normal transformation formula.

## 3. The useful linearization

The first-order Bernoulli map is still expected to be

\[
q_g
=
\frac1N-\frac1N(\mathcal L g)+\hbox{higher order},
\qquad
\mathcal L g_k=(k-1)g_k.
\]

This part is consistent with standard shape calculus:

- \(u'\) has boundary data \(g/N\);
- the Dirichlet-to-Neumann map on the unit ball sends \(g_k\) to \(k g_k\);
- evaluating the normal derivative on the moved boundary contributes the
  additional \(-g_k\), giving \(k-1\).

The \(\alpha\)-variation bracket also still has the linearization

\[
\Psi_g=1+(I-\Pi_1)g+\hbox{higher order},
\]

where \(\Pi_1\) is the degree-one spherical-harmonic projection.

## 4. Conditional spectral closure

The Bernoulli spectral closure is valid under the following **tame expansion
hypothesis**.

Assume that in the small \(C^{2,\gamma}\) graph class,

\[
q_g=\frac1N-\frac1N\mathcal L g+R_q(g),
\qquad
\|R_q(g)\|_{L^2}\le C\|g\|_{C^{2,\gamma}}\|g\|_{L^2},
\]

and

\[
\Psi_g=1+(I-\Pi_1)g+R_\alpha(g),
\qquad
\|R_\alpha(g)\|_{L^2}\le C\|g\|_{C^1}\|g\|_{L^2}.
\]

Then the selected Bernoulli law

\[
q_g^2=\Lambda+a_\sigma\Psi_g,\qquad |a_\sigma|\le C\sigma,
\]

implies after projecting away constants and first harmonics

\[
\mathcal L g_{\ge2}
=
O(\sigma)g_{\ge2}
+O(\|g\|_{C^{2,\gamma}})\,g.
\]

Since \(\|\mathcal L h\|_{L^2}\ge\|h\|_{L^2}\) on \(k\ge2\), small
\(\sigma\) and small \(\|g\|_{C^{2,\gamma}}\) force \(g_{\ge2}=0\). Volume and
barycenter constraints then force \(g=0\).

This is a correct conditional closure, but it depends on the tame expansion
hypothesis above.

## 5. What remains genuinely open

To make the Bernoulli spectral route publication-ready, one must prove the
tame Bernoulli expansion without evaluating the harmonic first variation
outside \(B_1\). A viable approach is:

1. work entirely on \(B_1\) with the pullback equation;
2. differentiate the coefficient map \(g\mapsto(A_g,J_g,\nu_g)\);
3. prove a second-order fixed-domain remainder estimate for
   \(\widetilde u_g\) in a norm strong enough to control the boundary normal
   derivative;
4. show the boundary-gradient remainder is tame in the mixed form
   \(C^{2,\gamma}\times L^2\), not merely \(C^{2,\gamma}\)-quadratic.

Until that is done, the selection route should still be considered closed by
BDV's nearly spherical second variation, not by the Bernoulli spectral closure.
