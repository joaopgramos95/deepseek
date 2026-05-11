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

## 2. Import the STFT stability paper's profile-gap method

The new file `s00222-024-01248-2-3.pdf` suggests a sharper one-dimensional
starting point. In that paper, stability is driven by the area between the
rearranged profile \(u^*(s)\) and the optimizer profile \(e^{-s}\).

For torsion, define

\[
v(s):=u_\Omega^*(s),\qquad b(s):=u_B^*(s),
\]

where \(B\) is the ball with \(|B|=|\Omega|=L\). Since

\[
b'(s)=-\frac{1}{n^2\omega_n^{2/n}s^{1-2/n}}
\]

and the level-set inequality gives \(v'(s)\ge b'(s)\), the profile gap

\[
h(s):=b(s)-v(s)
\]

is nonnegative and nonincreasing. Moreover

\[
\int_0^L h(s)\,ds=2(E(\Omega)-E(B)).
\]

Thus

\[
0\le b(s)-v(s)\le \frac{2(E(\Omega)-E(B))}{s}.
\]

This gives an explicit way to choose near-boundary levels: for \(s=L-\eta\),
if \(E(\Omega)-E(B)\ll\eta\), then

\[
t_\eta:=v(L-\eta)
\]

is comparable to the ball's boundary-layer height and

\[
|\Omega\setminus\{u>t_\eta\}|=\eta.
\]

The next lemma to prove is then a near-boundary good-level lemma: among
\(s\in[L-2\eta,L-\eta]\), find one level with controlled \(D_H+D_I\). For
selected minimizers, free-boundary regularity should convert the corresponding
height control into geometric boundary-layer control.

## 3. Quantify graph entry for selected minimizers

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

## 4. Use a hybrid route: apply level sets to selected minimizers

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

## 5. Boundary-layer asymmetry lemma

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

## 6. Superlevel replacement, copied from the STFT strategy

The STFT stability proof first replaces the arbitrary set \(\Lambda\) by the
matched superlevel set

\[
A_\Lambda=\{u_F>u_F^*(|\Lambda|)\},
\]

proves stability of \(A_\Lambda\), and then transfers stability back to
\(\Lambda\) by a transport comparison.

For torsion, the analogous replacement is

\[
\Omega\rightsquigarrow E_t=\{u_\Omega>t\},
\qquad |E_t|=|\Omega|-\eta.
\]

The transfer back to \(\Omega\) is exactly the boundary-layer asymmetry lemma.
The new work is to prove that the chosen \(E_t\) is geometrically good. The
profile-gap lemma chooses \(t\) in the correct near-boundary range; the exact
level-set deficit identity gives averaged control of \(D_H+D_I\); selected
minimizer regularity supplies the missing uniform estimates needed to convert
averages into a useful level.

## 7. Serrin-stability input to look for

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

## 8. Analytic/native-space calculation

The speculative but concrete GGRT-inspired calculation is:

1. Work after BDV selection, so the domain is a smooth near-ball
   \[
   \partial\Omega_\varepsilon
   =
   \{(1+\varepsilon\varphi(\theta))\theta\}.
   \]
2. Replace torsion by the harmonic object
   \[
   h_\varepsilon=u_{\Omega_\varepsilon}+\frac{|x|^2}{2N}.
   \]
   For the ball this is constant, and the first variation is the harmonic
   extension of the boundary graph.
3. For fixed \(s\in(0,|B|)\), compute the second variation of
   \[
   \mathcal K_s(\Omega)
   =
   \int_{\{u_\Omega>u_\Omega^*(s)\}}u_\Omega.
   \]
4. Diagonalize in spherical harmonics. The \(k=0\) mode should vanish because
   of volume normalization, and \(k=1\) because of translation. The question is
   whether the coefficients for \(k\ge2\) control the \(H^{1/2}\)-norm.

In dimension two, also test the holomorphic formulation

\[
F_\Omega(z)=\partial_z u_\Omega(z)+\frac{\bar z}{4},
\]

which is holomorphic in \(\Omega\) and vanishes for centered disks. Pulling this
object back to the disk may give a Bergman/Hardy-space version of the GGRT
Fock-space computation.
