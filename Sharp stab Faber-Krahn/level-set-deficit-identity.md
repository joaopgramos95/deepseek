# Level-set deficit identity for the Nicola--Tilli route

This note implements the first concrete step from `plan2.md`: turn the
convexity gap in `faber-krahn-1.pdf` into an exact weighted integral of the two
losses in the level-set proof.

Throughout, let \(u=u_\Omega\) solve

\[
-\Delta u=1 \quad\hbox{in }\Omega,\qquad u=0\quad\hbox{on }\partial\Omega,
\]

and set

\[
E_t=\{u>t\},\qquad m(t)=|E_t|,\qquad
\Sigma_t=\{u=t\},\qquad P(t)=\mathcal H^{n-1}(\Sigma_t).
\]

The formulas below are written for smooth domains and regular levels. The same
identities should extend to the finite-perimeter/coarea setting by the usual
approximation and a.e. level-set interpretation.

## 1. The two pointwise losses

For a regular level \(t\), define

\[
a(t):=-m'(t)=\int_{\Sigma_t}\frac{1}{|\nabla u|}\,d\mathcal H^{n-1}.
\]

By the divergence theorem applied to \(E_t\),

\[
\int_{\Sigma_t}|\nabla u|\,d\mathcal H^{n-1}=m(t).
\]

Let

\[
c_n:=n^2\omega_n^{2/n}.
\]

The total level-set loss in the differential inequality is

\[
D_{\rm lev}(t)
:=
a(t)m(t)-c_n m(t)^{2-2/n}.
\]

It splits as

\[
D_{\rm lev}(t)=D_H(t)+D_I(t),
\]

where

\[
D_H(t)
:=
\left(\int_{\Sigma_t}\frac{1}{|\nabla u|}\right)
\left(\int_{\Sigma_t}|\nabla u|\right)
-P(t)^2
=a(t)m(t)-P(t)^2
\]

is the Holder/Cauchy--Schwarz loss, and

\[
D_I(t)
:=
P(t)^2-c_n m(t)^{2-2/n}
\]

is the squared-perimeter isoperimetric loss of \(E_t\).

Both terms are nonnegative:

\[
D_H(t)\ge 0
\]

by Cauchy--Schwarz, and

\[
D_I(t)\ge 0
\]

by the isoperimetric inequality.

## 2. Convexity variable and exact identity

Let \(L:=|\Omega|\), let \(v(s)=u^*(s)=m^{-1}(s)\), and define

\[
I(s):=\int_{\{u>v(s)\}}u\,dx.
\]

Equivalently, for regular values,

\[
I'(s)=v(s),\qquad I''(s)=v'(s)=\frac{1}{m'(v(s))}=-\frac{1}{a(v(s))}.
\]

The function used in `faber-krahn-1.pdf` is

\[
G(s)
:=
I(s)+
\frac{s^{1+2/n}}{(4+2n)\omega_n^{2/n}}.
\]

Since

\[
\frac{d^2}{ds^2}
\frac{s^{1+2/n}}{(4+2n)\omega_n^{2/n}}
=
\frac{1}{c_n s^{1-2/n}},
\]

we get, with \(s=m(t)\),

\[
G''(s)
=
\frac{1}{c_n s^{1-2/n}}-\frac1{a(t)}
=
\frac{D_{\rm lev}(t)}
{s\,a(t)\,c_n s^{1-2/n}}.
\]

The endpoint convexity gap is

\[
\Gamma(\Omega)
:=
G'(L)-\frac{G(L)}{L}.
\]

Because \(G(0)=0\),

\[
\Gamma(\Omega)
=
\frac1L\int_0^L sG''(s)\,ds.
\]

Changing variables \(s=m(t)\), so that \(ds=-a(t)\,dt\), gives the exact
deficit identity

\[
\boxed{
\Gamma(\Omega)
=
\frac1{|\Omega|}
\int_0^{\|u\|_\infty}
\frac{D_H(t)+D_I(t)}
{n^2\omega_n^{2/n}m(t)^{1-2/n}}\,dt.
}
\]

This is the clean quantitative form of the rigidity statement at the end of
`faber-krahn-1.pdf`.

## 3. Relation to the Saint-Venant deficit

At \(s=L\), one has \(v(L)=0\). Hence

\[
G'(L)
=
\frac{L^{2/n}}{2n\omega_n^{2/n}}.
\]

Also

\[
\frac{G(L)}{L}
=
\frac1L\int_\Omega u\,dx
+
\frac{L^{2/n}}{(4+2n)\omega_n^{2/n}}.
\]

Therefore

\[
\Gamma(\Omega)
=
\frac1L\left(\int_B u_B\,dx-\int_\Omega u_\Omega\,dx\right),
\]

where \(B\) is the ball with \(|B|=|\Omega|\). Since

\[
E(\Omega)=-\frac12\int_\Omega u_\Omega\,dx,
\]

we obtain

\[
\boxed{
\Gamma(\Omega)
=
\frac{2}{|\Omega|}
\big(E(\Omega)-E(B)\big).
}
\]

Thus the endpoint convexity gap is not merely comparable to the torsion
deficit; it is exactly the normalized Saint-Venant deficit.

## 4. Consequences for good levels

The quantitative isoperimetric inequality gives, for a dimensional constant
\(c>0\),

\[
D_I(t)
\ge
c\,m(t)^{2-2/n}\mathcal A(E_t)^2
\]

for a.e. regular level \(t\). Hence

\[
E(\Omega)-E(B)
\gtrsim_n
\int_0^{\|u\|_\infty}
m(t)\mathcal A(E_t)^2\,dt
\]

up to the normalization factor \(|\Omega|\). More precisely, the exact identity
controls the weighted average

\[
\int_0^{\|u\|_\infty}
\frac{D_I(t)}
{m(t)^{1-2/n}}\,dt.
\]

For any measurable level interval \(J\subset(0,\|u\|_\infty)\), define the
weight

\[
d\nu(t)
:=
\frac{dt}{n^2\omega_n^{2/n}m(t)^{1-2/n}}.
\]

If \(\nu(J)>0\), then there exists a regular \(t\in J\) such that

\[
D_H(t)+D_I(t)
\le
\frac{|\Omega|\Gamma(\Omega)}{\nu(J)}.
\]

In particular, on any slab where \(m(t)\) is bounded above and below, the
Saint-Venant deficit produces at least one level with both small isoperimetric
loss and small Holder loss.

## 5. Holder loss as a Serrin-variance defect

Let \(f=|\nabla u|\) on \(\Sigma_t\), and set

\[
\bar f:=\frac1{P(t)}\int_{\Sigma_t}f
=
\frac{m(t)}{P(t)}.
\]

Then the Holder deficit has the exact weighted variance representation

\[
\boxed{
\int_{\Sigma_t}
\frac{(f-\bar f)^2}{f}\,d\mathcal H^{n-1}
=
\frac{m(t)}{P(t)^2}D_H(t).
}
\]

Indeed,

\[
\int_{\Sigma_t}\frac{(f-\bar f)^2}{f}
=
\int_{\Sigma_t}f
-2\bar f P(t)
+\bar f^2\int_{\Sigma_t}\frac1f
=
\frac{m(t)}{P(t)^2}
\left(
m(t)\int_{\Sigma_t}\frac1f-P(t)^2
\right).
\]

Thus small \(D_H(t)\) says that \(|\nabla u|\) is almost constant on
\(\Sigma_t\), in the natural weighted \(L^2(1/f)\) sense.

If, on a good regular level, one also has

\[
0<c_t\le |\nabla u|\le C_t<\infty,
\]

then this becomes an ordinary \(L^2\)-variance estimate:

\[
\int_{\Sigma_t}|f-\bar f|^2\,d\mathcal H^{n-1}
\le
C_t\frac{m(t)}{P(t)^2}D_H(t).
\]

This is the precise bridge from the Nicola--Tilli convexity gap to an
approximate Serrin condition on the interior domain \(E_t\).

## 6. What remains open in this route

The identity proves that small Saint-Venant deficit forces many superlevel sets
to be simultaneously almost isoperimetric and almost overdetermined.

The unsolved propagation problem is to recover \(\mathcal A(\Omega)^2\) from
this information. The deficit identity sees interior levels with positive
height, while Fraenkel asymmetry is a \(t=0\) boundary datum. A sharp proof by
this route needs a boundary-layer theorem of the following form:

\[
\exists t\downarrow0
\quad\hbox{such that}\quad
|\Omega\setminus E_t|
\hbox{ is small and }
D_H(t)+D_I(t)
\hbox{ remains controlled.}
\]

Without such a theorem, the level-set method gives strong information on
interior cores \(E_t\), but not yet a sharp estimate for the original domain
\(\Omega\).
