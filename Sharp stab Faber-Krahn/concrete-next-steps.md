# Concrete next steps

This note records the most actionable next moves after compiling the current
Faber--Krahn stability notes.

## 1. Prove the finite-perimeter level-set identity

This is the cleanest low-risk theorem to write next.

Target statement: for every open set \(\Omega\) of finite measure, with torsion
function \(u=u_\Omega\), the identity

\[
\frac{2}{|\Omega|}(E(\Omega)-E(B))
=
\frac1{|\Omega|}
\int_0^{\|u\|_\infty}
\frac{D_H(t)+D_I(t)}
{n^2\omega_n^{2/n}m(t)^{1-2/n}}\,dt
\]

holds with \(E_t=\{u>t\}\), \(m(t)=|E_t|\), and \(P(t)=P(E_t)\) for a.e. \(t\).

The proof should be organized as:

1. Use coarea for Sobolev functions to get finite perimeter of \(E_t\) for a.e.
   \(t\) and
   \[
   -m'(t)=\int_{\partial^*E_t}\frac1{|\nabla u|}\,d\mathcal H^{n-1}.
   \]
2. Prove the weak divergence identity
   \[
   \int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}=m(t)
   \]
   by testing \(-\Delta u=1\) with Lipschitz truncations of \((u-t)_+\).
3. Define \(I(s)=\int_{\{u>u^*(s)\}}u\) and justify
   \[
   I'(s)=u^*(s),\qquad I''(s)=-1/a(u^*(s))
   \]
   first where \(m\) is differentiable, then in the distributional sense.
4. Finish by the convexity-gap identity
   \[
   G'(L)-G(L)/L=L^{-1}\int_0^L sG''(s)\,ds.
   \]

This gives a polished standalone theorem, independent of the selection
principle.

## 2. Quantify graph entry for selected minimizers

The most direct continuation of the BDV route is the following theorem.

Let \(U\subset B_R\) be a selected minimizer of the penalized functional, with
the BDV density estimates and Lipschitz Bernoulli coefficient \(q_U\). Then
there exists an explicit threshold \(\varepsilon_0(N,R,\tau)\) such that

\[
\alpha(U)\le \varepsilon_0(N,R,\tau)
\quad\Longrightarrow\quad
\partial U
\text{ is a global }C^{1,\gamma}\text{ graph over }\partial B_1.
\]

The proof should follow this deterministic chain:

1. From density plus BDV Lemma 4.2,
   \[
   d_H(\partial U,\partial B_1)\le C\alpha(U)^{1/(2N)}.
   \]
2. Fix \(\mu<\bar\mu\), where \(\bar\mu\) is the Alt--Caffarelli flatness
   threshold, and choose the corresponding scale \(\rho(\mu)\).
3. Impose
   \[
   C\alpha(U)^{1/(2N)}\le \mu\rho(\mu).
   \]
   Then every ball \(B_{4\rho(\mu)}(x_0)\) centered near \(\partial B_1\) sees a
   sufficiently flat free boundary.
4. Apply Alt--Caffarelli locally and patch the finite cover of \(\partial B_1\)
   into a global graph.

This would turn the compactness phrase "for \(j\) large" into a concrete
smallness condition.

## 3. Use a hybrid route: apply level sets to selected minimizers

The level-set route has a boundary-layer obstruction for arbitrary domains.
The selected minimizers are much better objects: their free boundaries have
nondegeneracy, density estimates, and a Bernoulli condition with controlled
\(q_U\).

This suggests a hybrid theorem:

> For a selected minimizer \(U=\{u>0\}\), the Saint-Venant deficit controls the
> isoperimetric deficit of near-boundary level sets \(\{u>t\}\), uniformly for
> \(0<t<t_0(N,R,\tau)\).

The expected mechanism is:

1. Since \(q_U\) is bounded above and below on \(\partial U\), the coarea factor
   \(a(t)=\int_{\{u=t\}}1/|\nabla u|\) is uniformly controlled for small \(t\).
2. For small \(t\), the level surface \(\{u=t\}\) is a parallel perturbation of
   \(\partial U\), so
   \[
   |U\setminus\{u>t\}|\simeq t\int_{\partial U}\frac1{q_U},
   \qquad
   P(\{u>t\})=P(U)+O(t).
   \]
3. The weighted level-set identity then gives a genuinely near-boundary good
   level, not merely an interior good level.
4. Letting \(t\downarrow0\) should recover a bound on the isoperimetric deficit
   of \(U\) itself.

If this works, it may shorten the route from "selected minimizer" to
"near-ball" and reduce reliance on the full smooth-convergence compactness
argument.

## 4. Boundary-layer asymmetry lemma

A small but useful lemma to prove independently:

If \(E_t=\{u>t\}\), \(s=|E_t|\), \(L=|\Omega|\), and \(\eta=L-s\), then

\[
\mathcal A(\Omega)
\le
C\frac{\eta}{L}
+C\mathcal A(E_t)
\]

after the harmless volume normalization of the optimal ball for \(E_t\).

Proof: take an optimal ball \(B_s\) for \(E_t\), dilate it to a ball \(B_L\)
with volume \(L\), and estimate

\[
|\Omega\Delta B_L|
\le
|\Omega\setminus E_t|
+|E_t\Delta B_s|
+|B_s\Delta B_L|.
\]

This isolates the exact missing ingredient in the pure level-set route:
finding a good level with both \(\eta\) small and \(\mathcal A(E_t)\) controlled.

## 5. Serrin-stability input to look for

The level-set deficit gives a weighted \(L^2\) variance:

\[
\int_{\Sigma_t}\frac{(|\nabla u|-\bar f)^2}{|\nabla u|}
=
\frac{m(t)}{P(t)^2}D_H(t).
\]

Most available Serrin-stability theorems use stronger boundary norms, such as
oscillation or Lipschitz seminorms of \(u_\nu\). The bridge should be:

\[
\|f-\bar f\|_{L^\infty(\Sigma_t)}
\le
C
\|f-\bar f\|_{L^2(\Sigma_t)}^\theta
[f]_{C^\gamma(\Sigma_t)}^{1-\theta},
\]

valid on uniformly \(C^{1,\gamma}\) level surfaces. Selected minimizers are the
right setting for this interpolation because their free-boundary regularity
provides the missing \(C^\gamma\) control.

Relevant Serrin-stability references to check first:

- Brandolini--Nitsch--Salani--Trombetti, *On the stability of the Serrin
  problem*, JDE 2008.
- Ciraolo--Magnanini--Vespri, *Holder stability for Serrin's overdetermined
  problem*, Ann. Mat. Pura Appl. 2016.
- Magnanini--Poggesi, integral-identity approaches to Serrin stability.

The likely outcome is that the existing theorems do not plug in directly, but
their interpolation and integral-identity methods should be adaptable to the
weighted \(L^2\) defect coming from \(D_H\).
