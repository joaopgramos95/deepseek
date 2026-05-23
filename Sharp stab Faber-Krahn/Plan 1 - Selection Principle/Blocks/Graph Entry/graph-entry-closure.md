# Graph entry and closure of the selected-minimizer route

This note implements the remaining Plan 1 regularity step after the
single-set selection principle. It turns the compactness phrase "for the
selected minimizer close enough to the ball" into an explicit deterministic
pipeline:

\[
\alpha(U)\hbox{ small}
\Longrightarrow
d_H(\partial U,\partial B_1)\hbox{ small}
\Longrightarrow
\hbox{Alt--Caffarelli flatness at a fixed scale}
\Longrightarrow
\partial U\hbox{ is a global graph}
\Longrightarrow
E(U)-E(B_1)\gtrsim \alpha(U).
\]

The constants are not numerical, but every threshold is named and depends only
on the fixed data \((N,R)\) and the BDV free-boundary constants.

## 1. Selected-minimizer input

Let \(U=\{u>0\}\subset B_R\) be a selected minimizer from
`quantitative-selection-principle.md`, with \(\tau\le\tau_{\rm reg}(N,R)\).
After translating by the barycenter, assume the comparison ball is \(B_1\).

The BDV regularity package gives constants

\[
c_d,r_d,L_u,q_-,q_+,L_q>0
\]

depending only on \((N,R)\), such that:

1. two-sided density holds at every free-boundary point and every
   \(r\le r_d\);
2. \(u\) is Lipschitz with constant \(L_u\);
3. \(u\) is nondegenerate:
   \[
   \sup_{B_r(x)}u\ge c_d r
   \qquad(x\in\partial U,\;r\le r_d);
   \]
4. once the free boundary is flat, the Bernoulli coefficient satisfies
   \[
   q_-\le q_u\le q_+,\qquad \operatorname{Lip} q_u\le L_q.
   \]

These are exactly the constants entering BDV Lemmas 4.9, 4.12, 4.16 and
Theorem 4.18.

## 2. From asymmetry to Hausdorff distance

Let

\[
M:=|U\Delta B_1|.
\]

The density estimate implies

\[
d_H(\partial U,\partial B_1)
\le C_H(N,R,c_d,r_d)M^{1/N}.
\]

Since BDV Lemma 4.2 gives

\[
|U\Delta B_1|\le C_\alpha(N)\alpha(U)^{1/2},
\]

we get

\[
\boxed{
d_H(\partial U,\partial B_1)
\le
C_H'(N,R)\alpha(U)^{1/(2N)}.
}
\]

The proof is purely geometric: if a free-boundary point lies distance \(d\)
from \(\partial B_1\), a ball of radius comparable to \(d\) lies on one side of
\(\partial B_1\), while density forces a chunk of \(U\Delta B_1\) of size
\(\gtrsim d^N\). The reverse inclusion is identical, using the density of the
two phases.

## 3. Hausdorff closeness gives flatness

Let \(\bar\mu,\bar\rho,\gamma,C_{\rm AC}\) be the constants in the
Alt--Caffarelli improvement theorem used by BDV, with the above bounds on
\(u\) and \(q_u\). Fix

\[
0<\mu\le \frac{\bar\mu}{16C_0},
\]

where \(C_0\) is the harmless constant converting the geometric slab below into
the \(F(\cdot,1,+\infty)\) normalization. Choose

\[
0<\rho_\mu\le \bar\rho
\]

so small that every cap of \(\partial B_1\) of radius \(6\rho_\mu\) lies in a
\(\mu\rho_\mu\)-slab around its tangent plane:

\[
\partial B_1\cap B_{6\rho_\mu}(\bar x)
\subset
\{x: |(x-\bar x)\cdot \nu_{\bar x}|\le \mu\rho_\mu\}.
\]

Define

\[
h_F:=\frac{\mu\rho_\mu}{16}.
\]

### Proposition 3.1: fixed-scale flatness

If

\[
d_H(\partial U,\partial B_1)\le h_F,
\]

then for every \(\bar x\in\partial B_1\) there is
\(x_0\in\partial U\cap B_{h_F}(\bar x)\) such that, in
\(B_{4\rho_\mu}(x_0)\), the function \(u\) is of Alt--Caffarelli class

\[
F(C_0\mu,1,+\infty)
\]

with respect to the tangent direction \(\nu_{\bar x}\).

#### Proof

The Hausdorff inclusion gives

\[
\partial U\cap B_{5\rho_\mu}(\bar x)
\subset
\{x: |(x-\bar x)\cdot\nu_{\bar x}|
\le \mu\rho_\mu+h_F\}.
\]

Moving the center from \(\bar x\) to \(x_0\) changes the slab height by at most
\(h_F\), hence

\[
\partial U\cap B_{4\rho_\mu}(x_0)
\subset
\{|(x-x_0)\cdot\nu_{\bar x}|\le 2\mu\rho_\mu\}.
\]

The density and nondegeneracy estimates give the two phase alternatives in the
slabs outside this strip: points a fixed multiple of \(\mu\rho_\mu\) inside the
ball phase are positive with the lower linear growth required in the
\(F\)-definition, while points the same distance in the exterior phase vanish.
The Lipschitz bound for \(u\) supplies the upper linear control. These are
precisely the three inequalities in BDV Definition 4.17, after multiplying
\(\mu\) by the universal conversion constant \(C_0\).

## 4. Local flatness gives a global graph

By the choice of \(\mu\), \(C_0\mu\le\bar\mu\). BDV Theorem 4.18 therefore
improves the free boundary in every ball \(B_{\rho_\mu}(x_0)\) above to a
\(C^{1,\gamma}\) graph with norm at most

\[
C_{\rm AC}\mu.
\]

Choose \(\mu\) smaller, if needed, so that

\[
C_{\rm AC}\mu\le \mu_{\rm tub}(N),
\]

where \(\mu_{\rm tub}(N)\) is a fixed tubular-neighborhood slope threshold for
radial projection onto \(\partial B_1\). Then the local graphs cannot fold over
the radial direction. Since the balls \(B_{\rho_\mu}(\bar x)\) cover
\(\partial B_1\), the local parametrizations patch to one global function
\(g:\partial B_1\to\mathbb R\):

\[
\partial U=\{(1+g(\theta))\theta:\theta\in\partial B_1\}.
\]

Moreover

\[
\|g\|_{L^\infty(\partial B_1)}
\le C\,d_H(\partial U,\partial B_1),
\]

and

\[
\|g\|_{C^{1,\gamma}(\partial B_1)}
\le C(N,R)\mu.
\]

Higher \(C^{k,\gamma}\) bounds follow from the explicit smooth selected
Bernoulli law, with BDV Lemma 4.16 supplying the starting uniform coefficient
bounds, and Schauder bootstrapping. These bounds are uniform, not small. Small
\(C^{2,\gamma_0}\) norm is obtained by interpolating the uniform higher bound
with the small \(L^\infty\) bound above.

## 5. Explicit graph-entry threshold

With the constants above fixed, set

\[
\alpha_{\rm graph}(N,R)
:=
\left(\frac{h_F}{C_H'(N,R)}\right)^{2N}.
\]

Then

\[
\boxed{
\alpha(U)\le\alpha_{\rm graph}(N,R)
\quad\Longrightarrow\quad
\partial U\hbox{ is a global }C^{1,\gamma}\hbox{ graph over }\partial B_1.
}
\]

This is the quantitative replacement for the compactness step in BDV.

## 6. Entry into the nearly spherical theorem

BDV's nearly spherical theorem requires small \(C^{2,\gamma_0}\), not merely
small \(C^{1,\gamma}\). Fix \(0<\gamma_0<\gamma\) and an integer \(m\ge3\).
The Schauder bootstrap gives

\[
\|g\|_{C^{m,\gamma}(\partial B_1)}\le M_m(N,R).
\]

Interpolation on \(\partial B_1\) gives

\[
\|g\|_{C^{2,\gamma_0}}
\le
C\|g\|_{L^\infty}^{1-\theta}M_m(N,R)^\theta.
\]

Since \(\|g\|_{L^\infty}\le C d_H(\partial U,\partial B_1)
\le C\alpha(U)^{1/(2N)}\), there is a second threshold
\(\alpha_{\rm sph}(N,R,\gamma_0)\) such that

\[
\alpha(U)\le \alpha_{\rm sph}
\quad\Longrightarrow\quad
\|g\|_{C^{2,\gamma_0}}\le\delta_{\rm sph}(N,\gamma_0).
\]

Set

\[
\alpha_{\rm small}:=\min\{\alpha_{\rm graph},\alpha_{\rm sph}\}.
\]

## 7. Closure by the nearly spherical theorem

Once

\[
\partial U=\{(1+g(\theta))\theta:\theta\in\partial B_1\},
\]

the BDV nearly spherical expansion applies after volume and barycenter
normalization. There is \(c_{\rm sph}(N)>0\) such that, for
\(\alpha(U)\le\alpha_{\rm small}\),

\[
E(U)-E(B_1)
\ge c_{\rm sph}(N)\|g\|_{H^{1/2}(\partial B_1)}^2.
\]

The BDV asymmetry satisfies

\[
\alpha(U)\le C_{\rm sph}(N)\|g\|_{L^2(\partial B_1)}^2
\le C_{\rm sph}(N)\|g\|_{H^{1/2}(\partial B_1)}^2.
\]

Therefore

\[
\boxed{
E(U)-E(B_1)\ge c_*(N)\alpha(U)
}
\]

for every selected minimizer with
\(\tau\le\tau_{\rm reg}\) and \(\alpha(U)\le\alpha_{\rm small}\).

## 8. Final selected-counterexample contradiction

Let \(\Omega_0\subset B_R\), \(|\Omega_0|=|B_1|\), be an alleged bad set with

\[
q:=Q_\alpha(\Omega_0)
=\frac{E(\Omega_0)-E(B_1)}{\alpha(\Omega_0)}
\]

small. Apply the single-set selection map with \(\tau=q^{1/4}\) and obtain the
volume-normalized selected set \(\widetilde\Omega\). The selection principle
gives

\[
Q_\alpha(\widetilde\Omega)\le 2C_{\rm sel}q,
\]

and

\[
\frac12\alpha(\Omega_0)
\le
\alpha(\widetilde\Omega)
\le
\frac32\alpha(\Omega_0).
\]

If \(q\) and \(\alpha(\Omega_0)\) are small enough that
\(\tau\le\tau_{\rm reg}\) and
\(\alpha(\Omega_0)\le 2\alpha_{\rm small}/3\), then
\(\alpha(\widetilde\Omega)\le\alpha_{\rm small}\), so the graph-entry theorem,
the interpolation entry, and the nearly spherical estimate give

\[
Q_\alpha(\widetilde\Omega)\ge c_*(N).
\]

Thus no bad set can have

\[
q<\frac{c_*(N)}{2C_{\rm sel}}.
\]

Equivalently, in the small-asymmetry regime,

\[
E(\Omega)-E(B_1)\ge c\,\alpha(\Omega).
\]

Since BDV Lemma 4.2 gives \(\mathcal A(\Omega)^2\lesssim \alpha(\Omega)\),
this is the sharp quadratic Fraenkel stability estimate.
