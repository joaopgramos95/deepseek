# Fusco--Julin quantitative route: audit and first rigorous attempt

## Purpose and status

This note audits `FJ_quantitative_ideas.md` against the live manuscripts and
proves the first part of that programme which can be made constructive without
a regularity theorem: an explicit strong-form estimate for balanced
nearly-spherical sets.

It does **not** provide a constructive replacement for Fusco--Julin on arbitrary
finite-perimeter sets or on the general torsion superlevels used in `main.tex`.
That passage still requires a quantitative regularisation/selection theorem or
an additional geometric hypothesis on the level sets.

## 1. Corrections to the exploratory note

There are three corrections which matter before the proposed route can be used.

1. The cited `arXiv:2410.20844` is not a Fusco survey.  It is Jordan Serres,
   *Isoperimetric and geometric inequalities in quantitative form: Stein's
   method approach* (2024).  The accessible Fusco survey containing the
   strong-form discussion is Nicola Fusco, *The quantitative isoperimetric
   inequality and related topics*, Bull. Math. Sci. 5 (2015), 517--607;
   Theorem 5.4 records
   \[
      \beta(E)^2\le \kappa(n)\bigl(P(E)-P(B_r)\bigr).
   \]

2. On \(S^{n-1}\), the eigenvalue of a degree-\(k\) spherical harmonic is
   \(k(k+n-2)\).  Hence the first non-translation mode has
   \[
      \lambda_2=2n,
   \]
   not \(2n+2\).

3. With the Fusco--Julin convention
   \[
      \beta(E)^2
      =\frac12\inf_z\int_{\partial^*E}
         \left|\nu_E-\frac{x-z}{|x-z|}\right|^2\,d\mathcal H^{n-1},
   \]
   the quadratic ratio for balanced degree-two perturbations is
   \[
      \frac{\beta(E)^2}{P(E)-P(B)}
      \longrightarrow \frac{2n}{n+1}.
   \]
   Thus the proposed leading constant
   \((n+2)/(2(n-1))\) is not compatible with this normalization.

The final correction affects applicability.  A nearly-spherical estimate is
useful once a level set is known to be a small \(W^{1,\infty}\) radial graph.
The current constructive manuscript does not prove that property for general
torsion superlevels.  Its live gap is precisely the integrated same-centre
normal estimate in `Assumption~\ref{ass:constructive-strong}` of `main.tex`.
The Reilly investigation in `M1_REILLY_PROGRESS.md` explains why a direct PDE
upgrade currently stalls: it needs control of a large-gradient boundary tail
which is not available on arbitrary level sets.

## 2. Set-up

Let \(S=S^{n-1}\), let \(d\sigma=d\mathcal H^{n-1}|_S\), and let
\(u\in W^{1,\infty}(S)\) satisfy \(1+u>0\).  Define the radial set
\[
   E_u:=\{r\theta:\theta\in S,\ 0\le r<1+u(\theta)\}.
\]
Write
\[
   a:=1+u,\qquad s:=|\nabla_\tau u|,\qquad
   A:=\int_S s^2\,d\sigma,\qquad B:=\int_S u^2\,d\sigma.
\]
Assume the balancing conditions
\[
   |E_u|=|B_1|,\qquad \int_{E_u}x\,dx=0.
\tag{2.1}
\]
Equivalently,
\[
   \int_S(a^n-1)\,d\sigma=0,\qquad
   \int_S\theta a^{n+1}\,d\sigma=0.
\tag{2.2}
\]
The perimeter deficit is \(D(E_u):=P(E_u)-P(B_1)\).

For \(0<\delta<1\), set
\[
  m_p(\delta):=\min_{t\in[1-\delta,1+\delta]}t^p,\qquad
  M_p(\delta):=\max_{t\in[1-\delta,1+\delta]}t^p,
\]
\[
  L_n(\delta):=
  \frac{m_{n-3}(\delta)}
       {1+\sqrt{1+\left(\frac{\delta}{1-\delta}\right)^2}},
  \qquad
  U_n(\delta):=\frac12M_{n-3}(\delta),
\tag{2.3}
\]
\[
  R_n(\delta):=
  \frac{n-1}{2}M_{n-3}(\delta)\bigl(1+(n-1)\delta\bigr),
\tag{2.4}
\]
\[
  C_0(\delta):=\frac{n-1}{2}M_{n-2}(\delta),\qquad
  C_1(\delta):=\frac n2M_{n-1}(\delta),
\]
\[
  \eta_n(\delta):=\delta^2\bigl(C_0(\delta)^2+nC_1(\delta)^2\bigr),
  \qquad
  d_n(\delta):=
  L_n(\delta)-\frac{R_n(\delta)}{2n(1-\eta_n(\delta))}.
\tag{2.5}
\]

## 3. Explicit nearly-spherical strong-form lemma

**Lemma 3.1 (balanced nearly-spherical FJ estimate).**
Let \(n\ge2\).  Suppose \(E_u\) satisfies (2.1) and
\(\|u\|_{W^{1,\infty}(S)}\le\delta<1\).  If
\[
   \eta_n(\delta)<1,\qquad d_n(\delta)>0,
\tag{3.1}
\]
then
\[
   \beta(E_u)^2
   \le \frac{U_n(\delta)}{d_n(\delta)}
      \bigl(P(E_u)-P(B_1)\bigr).
\tag{3.2}
\]
In particular, the fully explicit choice
\[
   \delta\le\delta_*(n):=\frac{1}{100n^3}
\tag{3.3}
\]
gives the conservative bound
\[
   \beta(E_u)^2\le3\bigl(P(E_u)-P(B_1)\bigr).
\tag{3.4}
\]
In fact the same graph centre controls both terms needed downstream:
\[
   |E_u\Delta B_1|^2+
   \int_{\partial^* E_u}\left|\nu_{E_u}-\frac{x}{|x|}\right|^2
      d\mathcal H^{n-1}
   \le(3\omega_n+6)\bigl(P(E_u)-P(B_1)\bigr).
\tag{3.5}
\]
After translation and scaling, for a graph over \(\partial B_\rho(z)\) whose
barycentre is \(z\), (3.5) becomes
\[
   \rho^{-n-1}|E\Delta B_\rho(z)|^2+
   \int_{\partial^* E}\left|\nu_E-\frac{x-z}{|x-z|}\right|^2
      d\mathcal H^{n-1}
   \le(3\omega_n+6)\bigl(P(E)-P(B_\rho)\bigr).
\tag{3.6}
\]

**Proof.**
The area formula for the radial parametrisation gives
\[
   P(E_u)=\int_S a^{n-2}\sqrt{a^2+s^2}\,d\sigma.
\tag{3.7}
\]
Since the radial unit vector at \(a(\theta)\theta\) is \(\theta\), choosing
the centre \(0\) in the definition of \(\beta\) gives
\[
\begin{aligned}
   \beta(E_u)^2
   &\le \int_S a^{n-2}
       \left(\sqrt{a^2+s^2}-a\right)\,d\sigma  \\
   &=\int_S
       \frac{a^{n-3}s^2}
       {\sqrt{1+s^2/a^2}+1}\,d\sigma
   \le U_n(\delta)A .
\end{aligned}
\tag{3.8}
\]
Here the final inequality uses
\(\sqrt{1+t}-1\le t/2\).

For the reverse comparison, split the deficit as
\[
\begin{aligned}
   D(E_u)
   &=\int_S(a^{n-1}-1)\,d\sigma
     +\int_Sa^{n-2}\left(\sqrt{a^2+s^2}-a\right)\,d\sigma \\
   &=:I+G.
\end{aligned}
\tag{3.9}
\]
Since \(s/a\le\delta/(1-\delta)\), the identity
\(\sqrt{1+t}-1=t/(\sqrt{1+t}+1)\) yields
\[
   G\ge L_n(\delta)A.
\tag{3.10}
\]

Use the volume constraint in (2.2) and define
\[
   f(q):=(1+q)^{n-1}-1-\frac{n-1}{n}\bigl((1+q)^n-1\bigr).
\]
Then \(f(0)=f'(0)=0\) and
\[
   f''(q)=-(n-1)(1+q)^{n-3}\bigl(1+(n-1)q\bigr).
\]
Consequently,
\[
   I=\int_S f(u)\,d\sigma\ge-R_n(\delta)B.
\tag{3.11}
\]

It remains to remove the constant and translation modes from \(B\).  Taylor's
formula and (2.2) imply
\[
   \left|\int_Su\,d\sigma\right|\le C_0(\delta)B,\qquad
   \left|\int_S\theta u\,d\sigma\right|\le C_1(\delta)B.
\tag{3.12}
\]
Since \(B\le\delta^2|S|=\delta^2n\omega_n\), the squared \(L^2\) norm of the
degree-zero and degree-one projections of \(u\) is at most
\(\eta_n(\delta)B\).  The remaining spherical harmonics have eigenvalues at
least \(\lambda_2=2n\).  Therefore
\[
   A\ge2n(1-\eta_n(\delta))B.
\tag{3.13}
\]
Combining (3.9)--(3.13) gives
\[
   D(E_u)\ge d_n(\delta)A.
\tag{3.14}
\]
Together with (3.8), this proves (3.2).

For (3.3)--(3.4), substitute \(\delta=1/(100n^3)\) into (2.3)--(2.5).
The elementary estimates
\[
   M_{n-3},M_{n-2},M_{n-1}\le1.004,\quad
   m_{n-3}\ge0.997,\quad
   \eta_n(\delta)<10^{-4}
\]
give \(U_n(\delta)<3/5\) and \(d_n(\delta)>1/5\), hence
\(U_n(\delta)/d_n(\delta)<3\).  Smaller \(\delta\) only improves these
conservative bounds.  Scaling multiplies both \(\beta^2\) and the perimeter
deficit by \(\rho^{n-1}\), proving (3.4).

For the same-centre conclusion, the intermediate integral in (3.8) is exactly
one half of the normal integral about the graph centre.  The bounds
\(U_n(\delta)/d_n(\delta)<3\) and (3.14), applied to that unminimized
integral rather than only to \(\beta\), give
\[
   \int_{\partial^* E_u}\left|\nu_{E_u}-\frac{x}{|x|}\right|^2
      d\mathcal H^{n-1}\le6D(E_u).
\]
Moreover,
\[
   |E_u\Delta B_1|
   =\frac1n\int_S|a^n-1|\,d\sigma
   \le M_{n-1}(\delta)\int_S|u|\,d\sigma,
\]
and Cauchy--Schwarz, (3.13), (3.14), and the estimates used above yield
\[
   |E_u\Delta B_1|^2
   \le\frac{M_{n-1}(\delta)^2\omega_n}
            {2(1-\eta_n(\delta))d_n(\delta)}D(E_u)
   \le3\omega_n D(E_u).
\]
This proves (3.5).  Under the dilation \(E=z+\rho E_u\), the volume term
squared scales as \(\rho^{2n}\), while the normal integral and deficit scale
as \(\rho^{n-1}\); (3.6) follows. \(\square\)

## 4. Quadratic constant and the degree-two test

The lemma deliberately uses the safe constant \(3\).  Its small-graph
quadratic constant is obtained directly from (2.3)--(2.5):
\[
   \lim_{\delta\downarrow0}\frac{U_n(\delta)}{d_n(\delta)}
   =
   \frac{\frac12}
        {\frac12-\frac{n-1}{4n}}
   =\frac{2n}{n+1}.
\tag{4.1}
\]
This value is forced by the degree-two mode.  Let \(Y\) be a nonzero even
spherical harmonic of degree \(2\), and choose a scalar \(c_\varepsilon\)
so that \(u_\varepsilon=\varepsilon Y+c_\varepsilon\) satisfies the volume
condition.  Central symmetry gives the barycentre condition, while
\[
   c_\varepsilon=O(\varepsilon^2),\qquad
   \int_S|\nabla_\tau Y|^2\,d\sigma=2n\int_SY^2\,d\sigma.
\]
The second variations are
\[
   \beta(E_{u_\varepsilon})^2
      =n\varepsilon^2\int_SY^2\,d\sigma+o(\varepsilon^2),
\qquad
   D(E_{u_\varepsilon})
      =\frac{n+1}{2}\varepsilon^2\int_SY^2\,d\sigma
       +o(\varepsilon^2),
\]
where optimizing the centre removes only degree-one modes at this order.
Thus
\[
   \frac{\beta(E_{u_\varepsilon})^2}{D(E_{u_\varepsilon})}
      \longrightarrow\frac{2n}{n+1}.
\tag{4.2}
\]

## 5. What this proves for the manuscript

Lemma 3.1 rigorously validates the restricted-class dividend suggested in
`FJ_quantitative_ideas.md`, after correcting its constant and adding the
necessary balancing condition.  It can be imported wherever one already has:

- a single centre \(z_\rho\) about which a torsion level set is a radial
  \(W^{1,\infty}\) graph;
- exact volume and barycentre balancing about that centre; and
- the quantitative norm bound
  \(\|u_\rho\|_{W^{1,\infty}}\le1/(100n^3)\).

Those hypotheses are not presently available for general good levels of the
bounded Saint--Venant core.  The active alternatives remain:

- use `FK_standard_FuscoJulin.tex`, importing the non-explicit general FJ
  constant;
- prove a genuinely quantitative selection/regularity theorem producing the
  graph hypotheses above with traceable constants; or
- restrict the theorem to a bounded-geometry/convex class where the required
  regularity can be proved independently.

## Sources checked

- N. Fusco and V. Julin, *A strong form of the Quantitative Isoperimetric
  inequality*, arXiv:1111.4866, published in Calc. Var. PDE 50 (2014),
  925--937: <https://arxiv.org/abs/1111.4866>.
- N. Fusco, *The quantitative isoperimetric inequality and related topics*,
  Bull. Math. Sci. 5 (2015), 517--607, especially Theorems 3.1 and 5.4:
  <https://link.springer.com/article/10.1007/s13373-015-0074-x>.
- B. Fuglede, *Stability in the isoperimetric problem for convex or nearly
  spherical domains in \(R^n\)*, Trans. AMS 314 (1989), 619--638:
  <https://doi.org/10.1090/S0002-9947-1989-0942426-3>.
- `arXiv:2410.20844`, checked only to correct its misattribution:
  <https://arxiv.org/abs/2410.20844>.
