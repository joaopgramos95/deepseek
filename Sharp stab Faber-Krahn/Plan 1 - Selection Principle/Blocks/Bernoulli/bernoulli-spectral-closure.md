# Bernoulli spectral closure for selected minimizers

This note attacks the remaining gap more directly than the boundary-layer
deficit route. The conclusion is that the attempted estimate

\[
D_I(0)+D_H(0)\lesssim E(U)-E(B_1)
\]

is the wrong target: it is false for general nearly spherical graphs. The
correct hard mechanism is the selected minimizer's Bernoulli law. Once the
selected minimizer is in the global graph regime, the Euler-Lagrange condition
itself suppresses every non-neutral spherical harmonic mode when the selection
parameter \(\sigma\) is small.

This would give a direct spectral closure of the selected-minimizer
contradiction if the tame Bernoulli remainder estimates stated below were
proved. The follow-up `bernoulli-expansion-proofs.md` corrects an invalid
attempt at those estimates and records the route as conditional.

## 1. Why the boundary-deficit propagation target is too strong

Let

\[
\partial\Omega_\varepsilon
=\{(1+\varepsilon\varphi(\theta))\theta:\theta\in\partial B_1\},
\]

with \(\varphi\) a spherical harmonic of degree \(k\ge2\), normalized by
\(\|\varphi\|_{L^2(\partial B_1)}=1\). The second variation of torsion at the
ball has the \(H^{1/2}\) scale

\[
E(\Omega_\varepsilon)-E(B_1)
\simeq
\varepsilon^2 k.
\]

On the other hand, the perimeter/isoperimetric boundary defect has the \(H^1\)
scale

\[
D_I(0)
\simeq
\varepsilon^2 k^2.
\]

Similarly, the first variation of the boundary Bernoulli datum contains the
multiplier \(k-1\), so the Holder/Serrin defect satisfies

\[
D_H(0)\simeq \varepsilon^2(k-1)^2.
\]

Thus neither \(D_I(0)\) nor \(D_H(0)\) can be bounded linearly by the torsion
energy on the full nearly spherical class. High frequencies violate the bound.
The graph regime alone does not repair this, since small-amplitude high
frequencies can keep \(C^{1,\gamma}\) norms bounded while making the ratio
\(D_I/E\) large.

Therefore the boundary-layer route can close sharply only by using the
selected Euler-Lagrange equation, not by a general trace inequality.

## 2. Linearized torsion data at the ball

Write the selected boundary as

\[
\partial U_g=\{(1+g(\theta))\theta:\theta\in\partial B_1\},
\]

with

\[
\int_{\partial B_1}g=O(\|g\|_{L^2}^2),
\qquad
\int_{\partial B_1}\theta_i g=O(\|g\|_{L^2}^2),
\]

coming from volume and barycenter normalization.

For the actual selected minimizer \(U_*\), the volume is only
\(|B_1|+O(E(U_*)-E(B_1))\). This does not change the argument: first write
\(\partial U_*\) as a graph over \(\partial B_{r_*}\), where
\(|B_{r_*}|=|U_*|\), then dilate by \(r_*^{-1}\). The Bernoulli law is
preserved up to changing the constants \(\Lambda\) and \(a_\sigma\), and
\(|r_*-1|=O(E(U_*)-E(B_1))\) contributes only a quadratic/constant-mode error.

Let

\[
u_g=u_{B_1}+u_1+O(g^2),
\qquad
u_{B_1}(r)=\frac{1-r^2}{2N}.
\]

The first shape derivative satisfies

\[
\Delta u_1=0\quad\hbox{in }B_1,
\qquad
u_1|_{\partial B_1}=\frac{g}{N}.
\]

If

\[
g=\sum_{k\ge0}g_k
\]

is the spherical-harmonic decomposition, then

\[
u_1(r,\theta)=\frac1N\sum_{k\ge0} r^k g_k(\theta).
\]

The outward normal derivative on the perturbed boundary is

\[
\partial_\nu u_g
=
-\frac1N
+\frac1N\sum_{k\ge0}(k-1)g_k
+O(\|g\|_{C^2}^2).
\]

Equivalently, for the positive Bernoulli datum \(q_g=|\nabla u_g|\),

\[
q_g
=
\frac1N
-\frac1N\sum_{k\ge0}(k-1)g_k
+O(\|g\|_{C^2}^2).
\]

Thus the non-neutral linear operator is the Steklov operator shifted by one:

\[
\mathcal L g
:=\sum_{k\ge0}(k-1)g_k.
\]

The kernel consists exactly of the \(k=1\) translation modes, while the
volume constraint removes the \(k=0\) mode.

## 3. Linearization of the selected Bernoulli law

BDV Lemma 4.16 gives, on \(\partial U_g\),

\[
q_g(x)^2
=
\Lambda
+a_\sigma
\left[
|x-x_U|
-
\left(\int_{U_g}\frac{y-x_U}{|y-x_U|}\,dy\right)\cdot x
\right],
\]

where

\[
|a_\sigma|\le C\sigma.
\]

After centering \(x_U=0\), expand the bracket at the ball. On
\(x=(1+g(\theta))\theta\),

\[
|x|=1+g(\theta)+O(g^2),
\]

and

\[
\int_{U_g}\frac{y}{|y|}\,dy
=
\int_{\partial B_1}g(\theta)\theta\,d\theta
+O(\|g\|_{L^2}^2).
\]

The second term is the degree-one projection of \(g\). Therefore the
nonconstant part of the right-hand side is

\[
a_\sigma\,(I-\Pi_1)g+O(\sigma\|g\|_{C^1}^2),
\]

where \(\Pi_1\) is the projection onto first spherical harmonics. Constants are
absorbed into \(\Lambda\).

On the left-hand side,

\[
q_g^2
=
\frac1{N^2}
-\frac{2}{N^2}\mathcal L g
+O(\|g\|_{C^2}^2).
\]

Removing constants and first harmonics gives the projected equation

\[
\boxed{
\mathcal L g_{\ge2}
=
O(\sigma)g_{\ge2}
+O(\|g\|_{C^2}^2).
}
\]

Here \(g_{\ge2}\) denotes the projection onto spherical harmonics of degree
\(k\ge2\).

## 4. Spectral gap closure

On the \(k\ge2\) subspace,

\[
\|\mathcal L h\|_{L^2}\ge \|h\|_{L^2}.
\]

Hence the projected Bernoulli equation yields

\[
\|g_{\ge2}\|_{L^2}
\le
C\sigma\|g_{\ge2}\|_{L^2}
+C\|g\|_{C^2}\|g\|_{L^2}.
\]

If

\[
\sigma\le\sigma_*
\qquad\hbox{and}\qquad
\|g\|_{C^2}\le\delta_*,
\]

with \(C\sigma_*+C\delta_*\le1/2\), then

\[
g_{\ge2}=0.
\]

The volume and barycenter constraints give

\[
g_0=O(\|g\|_{L^2}^2),
\qquad
g_1=O(\|g\|_{L^2}^2).
\]

Thus

\[
\|g\|_{L^2}\le C\|g\|_{L^2}^2.
\]

For \(\|g\|_{L^2}\) small, this implies

\[
g\equiv0.
\]

Thus, conditional on the tame remainder estimates in Section 5, in the
small-graph regime and for \(\sigma\le\sigma_*\), the only selected minimizer
satisfying the Euler-Lagrange equation is the ball.

## 5. Nonlinear estimates needed for a proof

The previous sections become a proof once the following two estimates are
recorded. They are standard consequences of Schauder estimates for the
Dirichlet problem on \(C^{2,\gamma}\) graph domains and Taylor expansion of the
normal map.

### Lemma 5.1: Bernoulli map expansion

For \(\|g\|_{C^{2,\gamma}}\le\delta\), let \(q_g=|\nabla u_g|\) on
\(\partial U_g\), pulled back to \(\partial B_1\). Then

\[
q_g-\frac1N+\frac1N\mathcal L g=R_q(g),
\]

with

\[
\|R_q(g)\|_{L^2(\partial B_1)}
\le
C\|g\|_{C^{2,\gamma}}\|g\|_{L^2(\partial B_1)}.
\]

Sketch: pull \(u_g\) back to \(B_1\) by the radial diffeomorphism
\(r\theta\mapsto r(1+g(\theta))\theta\). The pulled-back equation is a uniformly
elliptic perturbation of \(-\Delta u=1\). Subtract the ball solution and the
harmonic first variation. Schauder estimates give a \(C^{1,\gamma}\), hence
\(L^2(\partial B_1)\), remainder quadratic in the graph size.

### Lemma 5.2: \(\alpha\)-variation bracket expansion

Let

\[
\Psi_g(\theta)
=
|(1+g(\theta))\theta|
-
\left(\int_{U_g}\frac{y}{|y|}\,dy\right)\cdot(1+g(\theta))\theta .
\]

Then, modulo constants,

\[
\Psi_g=(I-\Pi_1)g+R_\alpha(g),
\]

with

\[
\|R_\alpha(g)\|_{L^2(\partial B_1)}
\le
C\|g\|_{C^1}\|g\|_{L^2(\partial B_1)}.
\]

Sketch: expand \(|(1+g)\theta|=1+g\) and

\[
\int_{U_g}\frac{y}{|y|}\,dy
=
\frac1N\int_{\partial B_1}(1+g)^N\theta\,d\theta
=
\int_{\partial B_1}g\theta\,d\theta+O(\|g\|_{L^2}\|g\|_{C^1}).
\]

The linear term \((\int g\theta)\cdot\theta\) is exactly the degree-one
projection, up to the harmless normalization of the \(Y_{1,i}\) basis.

Combining Lemmas 5.1 and 5.2 with the selected Bernoulli law gives the
projected nonlinear equation

\[
\mathcal L g_{\ge2}
=
a_\sigma'(I-\Pi_1)g_{\ge2}
+R(g),
\]

where \(|a_\sigma'|\le C\sigma\) and

\[
\|R(g)\|_{L^2}
\le C(\|g\|_{C^{2,\gamma}}+\sigma\|g\|_{C^1})\|g\|_{L^2}.
\]

This is the precise inequality used in Section 4.

## 6. Consequence for the selection contradiction

Conditionally, the selection principle produces a selected minimizer \(U\) whose asymmetry
stays comparable to the original bad set:

\[
\alpha(U)\ge (1-o(1))\alpha(\Omega_0)>0.
\]

The graph-entry theorem places \(U\) in the small \(C^{2,\gamma}\) graph regime
once \(\alpha(U)\le\alpha_{\rm graph}\). If the tame Bernoulli expansion were
available, the spectral closure above would say that for small enough
\(\sigma\), \(U\) must be the ball. This would contradict \(\alpha(U)>0\).

This is a direct replacement for the boundary-deficit propagation target. It
uses the two facts that are special to selected minimizers:

1. the Bernoulli coefficient is not arbitrary; it is an \(O(\sigma)\)
   perturbation of a constant plus the controlled \(\alpha\)-variation;
2. the linearized Bernoulli map has a spectral gap on all modes except volume
   and translations.

## 7. What remains

The argument above is conditional. The missing estimates are not yet proved:

1. upgrade graph entry to a uniform \(C^{2,\gamma}\) graph. BDV Lemma 4.16
   gives smooth \(q_u\), and Theorem 4.18 plus Schauder bootstrapping supplies
   this once the \(C^{1,\gamma}\) graph is obtained;
2. write Lemmas 5.1 and 5.2 in full detail with a fixed pullback map and
   explicit dependence on the \(C^{2,\gamma}\) radius;
3. track the small volume-normalization error from \(U_*\) to the unit-volume
   dilation.

Until these estimates are proved, the reliable closure remains BDV's nearly
spherical second variation. No external Serrin stability theorem is needed for
the BDV route.
