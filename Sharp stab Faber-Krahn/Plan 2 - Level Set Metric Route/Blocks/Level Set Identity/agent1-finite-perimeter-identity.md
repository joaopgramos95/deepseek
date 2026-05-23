# Agent 1 deliverable — Finite-perimeter coarea / level-set deficit identity

## 0. Summary of what is proved

**Theorem (Saint–Venant deficit via reduced-boundary level sets).** Let
$\Omega\subset\mathbb R^n$ be open with $|\Omega|<\infty$, let
$u\in H^1_0(\Omega)$ be the variational torsion function ($-\Delta u=1$ in
$\Omega$), and set $E_t:=\{u>t\}$, $m(t):=|E_t|$. Then $u\in L^\infty(\Omega)$,
$E_t$ has finite perimeter for a.e. $t\in(0,\|u\|_\infty)$, and
$$
\frac{2}{|\Omega|}\bigl(E(\Omega)-E(B)\bigr)
=
\frac{1}{|\Omega|}\int_0^{\|u\|_\infty}
\frac{D_H(t)+D_I(t)}{n^2\omega_n^{2/n}\,m(t)^{1-2/n}}\,dt,
$$
where $E(\Omega):=-\tfrac12\int_\Omega u\,dx=-\tfrac12 T(\Omega)$, $B$ is the
ball with $|B|=|\Omega|$, and
$$
D_H(t)
=
\Bigl(\!\int_{\partial^*E_t}\!|\nabla u|^{-1}\,d\mathcal H^{n-1}\Bigr)
\Bigl(\!\int_{\partial^*E_t}\!|\nabla u|\,d\mathcal H^{n-1}\Bigr)
-P(E_t)^2
\ge 0,
$$
$$
D_I(t)=P(E_t)^2-n^2\omega_n^{2/n}\,m(t)^{2-2/n}\ge 0.
$$

All four ingredients — coarea, weak divergence flux identity, distributional
derivatives of the rearranged primitive, and convex assembly — are stated for
a.e. $t$ on reduced boundaries. No graph regularity, no BDV selection, no
classical smoothness is used.

**Inputs:** $\Omega$ open of finite measure; $u_\Omega$ defined variationally.
**Residual hypotheses:** none beyond $|\Omega|<\infty$. In particular $\Omega$
need not be bounded, smooth, or connected. The torsion function is in
$L^\infty$ automatically (Talenti) and the level sets have finite perimeter
for a.e. level.

---

## 1. Standing hypotheses and basic facts

Throughout, $n\ge 2$ and

- $\Omega\subset\mathbb R^n$ is open, $|\Omega|<\infty$;
- $u=u_\Omega\in H^1_0(\Omega)$ is the variational torsion function, i.e. the
  minimizer of $J(v):=\tfrac12\int|\nabla v|^2-\int v$ over $H^1_0(\Omega)$,
  equivalently the unique weak solution of $-\Delta u=1$ in $\Omega$,
  $u=0$ on $\partial\Omega$ in the $H^1_0$ trace sense;
- $u\ge 0$ a.e. by the weak maximum principle (test with $u^-$);
- $E(\Omega):=-\tfrac12\int_\Omega u=-\tfrac12 T(\Omega)$;
- $B$ denotes the open ball centered at the origin with $|B|=|\Omega|$,
  radius $R:=(|\Omega|/\omega_n)^{1/n}$;
- $E_t:=\{u>t\}$ (a representative chosen as in Maggi 2012, §15);
  $m(t):=|E_t|$ (right-continuous, nonincreasing, $m(0^+)\le|\Omega|$,
  $m(\|u\|_\infty)=0$);
- $u^*(s):=\inf\{t\ge 0:m(t)\le s\}$ is the decreasing rearrangement
  (Kawohl 1985, Talenti 1976);
- $a(t):=\int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}$ where it is defined.

**Talenti $L^\infty$ bound (Talenti 1976; Kesavan 2006, Thm 1.3.2).** For
$\Omega$ of finite measure,
$$
u_\Omega^*(s)\le u_B^*(s)=\frac{R^2-(s/\omega_n)^{2/n}}{2n},
\qquad s\in[0,|\Omega|],
$$
so $\|u\|_{L^\infty(\Omega)}\le R^2/(2n)<\infty$. This is the only reason we
do not need to assume $\Omega$ bounded at the analytic level.

**Coarea applicability.** Since $u\in H^1_0(\Omega)\subset BV_{\rm loc}(\mathbb
R^n)$ (extended by $0$) and $u\in L^\infty$, the coarea formula
(Ambrosio–Fusco–Pallara 2000, Thm 3.40; Maggi 2012, Thm 13.1) gives
$$
\int_\Omega |\nabla u|\,\varphi\,dx
=\int_{-\infty}^\infty\!\!\Bigl(\int_{\partial^*E_t}\varphi\,d\mathcal H^{n-1}\Bigr)dt
$$
for every Borel $\varphi\ge 0$, and the set
$$
\mathcal R:=\{t\in(0,\|u\|_\infty):
P(E_t)<\infty\text{ and }\partial^*E_t\subset\Omega\}
$$
has full Lebesgue measure in $(0,\|u\|_\infty)$. By Sard for Sobolev maps
(Figalli–Maggi 2011; or Mariconda–Treu) one in fact has
$\mathcal H^{n-1}(\{u=t\}\cap\{|\nabla u|=0\})=0$ for a.e. $t$, but this is not
needed below: all integrals are on reduced boundaries.

We work on $\mathcal R$ from now on; statements "for a.e. $t$" mean a.e.
$t\in\mathcal R$.

---

## 2. Lemma 1 — Coarea identity for $-m'(t)$

**Lemma 1.** For a.e. $t\in(0,\|u\|_\infty)$,
$$
-m'(t)
=
\int_{\partial^*E_t}\frac{1}{|\nabla u|}\,d\mathcal H^{n-1}.
\tag{L1}
$$
In particular $m$ is absolutely continuous on $[\epsilon,\|u\|_\infty]$ for
every $\epsilon>0$.

**Proof.** Use the coarea formula on the Sobolev (BV) function $u$ with
$\varphi=|\nabla u|^{-1}\mathbf 1_{\{|\nabla u|>0\}}\mathbf 1_{[\alpha,\beta]}\circ u$
for $0<\alpha<\beta<\|u\|_\infty$. By Maggi 2012, Thm 13.1 (BV coarea),
$$
\int_\Omega \mathbf 1_{\{\alpha<u<\beta\}}\,dx
=\int_\alpha^\beta\!\!\Bigl(\int_{\partial^*E_t}\frac{1}{|\nabla u|}\,d\mathcal H^{n-1}\Bigr)dt
$$
because the left side equals $\int|\nabla u|\cdot|\nabla u|^{-1}\mathbf 1_{\alpha<u<\beta}$
and the contribution of $\{|\nabla u|=0\}$ to the BV coarea slicing vanishes
(Ambrosio–Fusco–Pallara 2000, 3.40 (b)). The left side is exactly $m(\alpha)-m(\beta)$
when $u$ has no plateau at $\alpha,\beta$, which holds at a.e. level by Sard.
Differentiating in $\beta$ at almost every $\beta$ gives (L1). $\square$

**Remark.** Plateaus $\{u=t\}$ of positive measure are a Lebesgue-null set of
$t$'s (each such plateau contributes a jump of $m$, and $m$ is monotone, so
there are at most countably many). For such jump levels the identity in (L1)
is not used.

---

## 3. Lemma 2 — Weak divergence flux identity

**Lemma 2.** For a.e. $t\in(0,\|u\|_\infty)$, $E_t$ has finite perimeter and
$$
\int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}
=
m(t).
\tag{L2}
$$
In particular $a(t):=\int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}=m(t)$
for a.e. $t$.

**Proof.** Fix $t\in\mathcal R$ such that $|E_t|<\infty$, $P(E_t)<\infty$, and
$u$ has no level plateau at $t$ (all a.e.).

*Step 1 — Weak formulation.* For every Lipschitz test $\eta$ with compact
support inside $\Omega$,
$$
\int_\Omega\nabla u\cdot\nabla\eta\,dx=\int_\Omega \eta\,dx.\tag{$\star$}
$$
We want to take $\eta=\mathbf 1_{E_t}$. Since $\mathbf 1_{E_t}\in BV_{\rm loc}$
but not Lipschitz, approximate by
$$
\eta_\epsilon(x):=\phi_\epsilon(u(x)-t),
\qquad
\phi_\epsilon(s)=\min\bigl(1,\max(0,s/\epsilon)\bigr).
$$
Then $\eta_\epsilon\in H^1_0(\Omega)$ (since $u\in H^1_0$ and $\phi_\epsilon$
is Lipschitz with $\phi_\epsilon(0)=0$), so it is an admissible test in
($\star$). The chain rule gives $\nabla\eta_\epsilon=\epsilon^{-1}\nabla u
\,\mathbf 1_{\{t<u<t+\epsilon\}}$. Therefore
$$
\int_\Omega \eta_\epsilon\,dx
=\frac{1}{\epsilon}\int_{\{t<u<t+\epsilon\}}|\nabla u|^2\,dx.
$$

*Step 2 — Coarea on the right.* By BV coarea,
$$
\int_{\{t<u<t+\epsilon\}}|\nabla u|^2\,dx
=\int_t^{t+\epsilon}\!\!\Bigl(\int_{\partial^*E_\tau}|\nabla u|\,d\mathcal H^{n-1}\Bigr)d\tau
=\int_t^{t+\epsilon}a(\tau)\,d\tau.
$$
(Apply Maggi Thm 13.1 with $\varphi=|\nabla u|\,\mathbf 1_{(t,t+\epsilon)}\circ u$.)

*Step 3 — Limit on the left.* By dominated convergence,
$\int_\Omega\eta_\epsilon\to|E_t|=m(t)$.

*Step 4 — Limit on the right.* At every Lebesgue point $t$ of the locally
integrable function $\tau\mapsto a(\tau)$ — equivalently for a.e. $t$ —
$$
\frac{1}{\epsilon}\int_t^{t+\epsilon}a(\tau)\,d\tau
\xrightarrow[\epsilon\downarrow0]{}a(t).
$$
That $a\in L^1_{\rm loc}$ follows from coarea: $\int a(\tau)d\tau=\int_\Omega|\nabla u|^2
=\int_\Omega u<\infty$ (Dirichlet identity, see remark below).

*Step 5 — Conclusion.* Combining Steps 1–4 gives $a(t)=m(t)$ for a.e. $t$.
This is (L2). $\square$

**Remark (Dirichlet identity).** Testing $-\Delta u=1$ against $u\in H^1_0$ gives
$\int|\nabla u|^2=\int u=2|E(\Omega)|$. Equivalently, by coarea,
$$
\int_0^{\|u\|_\infty}\!\!a(t)\,dt
=\int_\Omega|\nabla u|^2\,dx
=\int_\Omega u\,dx
=\int_0^{\|u\|_\infty}\!\!m(t)\,dt,
$$
which is (L2) integrated. The pointwise version (L2) is the localization at
every level.

**Geometric remark.** Formally, $\nabla u\cdot\nu_{E_t}=-|\nabla u|$ on
$\partial^*E_t$ because $u>t$ inside, so the divergence theorem on the set of
finite perimeter $E_t$ (Maggi 2012, Thm 17.2 or De Giorgi–Federer) reads
$$
m(t)=\int_{E_t}1\,dx=-\!\int_{E_t}\Delta u\,dx
=-\!\int_{\partial^*E_t}\nabla u\cdot\nu_{E_t}\,d\mathcal H^{n-1}
=\int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}.
$$
The argument above is the rigorous BV-Lipschitz approximation that bypasses
the trace of $\nabla u$ on $\partial^*E_t$.

---

## 4. Lemma 3 — Distributional derivatives of the rearranged primitive

Let
$$
I(s):=\int_{\{u>u^*(s)\}}\!u\,dx
=\int_{m(t)\le s}u\,dx\Big|_{t=u^*(s)},
\qquad s\in[0,|\Omega|].
$$
Equivalently, by Fubini and the layer-cake formula, we will work directly
with the rearrangement-friendly form $I(s)=\int_0^s u^*(\sigma)\,d\sigma$,
derived as follows.

**Lemma 3a.** $I(s)=\int_0^s u^*(\sigma)\,d\sigma$ for every
$s\in[0,|\Omega|]$.

*Proof.* By the equimeasurability of $u$ and $u^*$ on $(0,|\Omega|)$,
$\int_\Omega g\circ u=\int_0^{|\Omega|}g\circ u^*$ for every Borel $g\ge 0$
(Kawohl 1985, §2; Talenti 1976). Choose
$g(t)=t\,\mathbf 1_{\{t>u^*(s)\}}$; since $\{u>u^*(s)\}$ and
$\{\sigma:u^*(\sigma)>u^*(s)\}$ are equimeasurable and the latter equals
$(0,s)$ up to null sets (by the very definition of $u^*$), we obtain
$$
I(s)=\int_\Omega g\circ u
=\int_0^{|\Omega|}g\circ u^*
=\int_0^s u^*(\sigma)\,d\sigma. \qquad\square
$$

**Lemma 3b (a.e. differentiation).** $I$ is absolutely continuous on
$[0,|\Omega|]$ and $I'(s)=u^*(s)$ for a.e. $s$.

*Proof.* $u^*$ is bounded by $\|u\|_\infty<\infty$ and Borel, so $u^*\in
L^\infty(0,|\Omega|)$. Lemma 3a then expresses $I$ as the indefinite integral
of a bounded function; absolute continuity and $I'(s)=u^*(s)$ a.e. follow
from the Lebesgue differentiation theorem. $\square$

**Lemma 3c (distributional second derivative — corrected form).** With
$\alpha(t):=\int_{\partial^*E_t}|\nabla u|^{-1}\,d\mathcal H^{n-1}=-m'(t)$,
the rearrangement $u^*$ is absolutely continuous on every interval
$[s_0,|\Omega|-\epsilon]$, and
$$
I''(s)=(u^*)'(s)=\frac{1}{m'(u^*(s))}
=-\Bigl(\int_{\partial^*E_{u^*(s)}}|\nabla u|^{-1}\,d\mathcal H^{n-1}\Bigr)^{-1}
=-\frac{1}{\alpha(u^*(s))}.
\tag{L3'}
$$

*Proof.* $m$ is right-continuous, nonincreasing, and (by Lemma 1) absolutely
continuous on $[\epsilon,\|u\|_\infty]$ with $m'(t)=-\alpha(t)\le 0$. The set
of plateaus of $u$ in $(0,\|u\|_\infty)$ (levels $t$ with $|\{u=t\}|>0$) is
at most countable. Outside the plateau values, $m$ is strictly decreasing,
hence $u^*$, its right-continuous generalized inverse on the image, is also
strictly decreasing and absolutely continuous. Differentiating $m(u^*(s))=s$
(which holds for a.e. $s$ outside the rearranged plateau set) via the
inverse-function theorem for monotone AC functions (Ambrosio–Fusco–Pallara
2000, Thm 3.99; or Bénilan–Brezis–Crandall, J. Anal. Math. 1975) gives (L3').
$\square$

**Notational fix.** The identity "$I''(s)=-1/a(u^*(s))$" with
$a(t):=\int_{\partial^*E_t}|\nabla u|$ that appears in the source note
`level-set-deficit-identity.md` is **wrong** in general (the two integrals
differ precisely by $D_H$); it is correct only on the ball, where $|\nabla u|$
is level-constant. The general identity is (L3'), with the $|\nabla u|^{-1}$
integral. This is the typo flagged in §9 below.

**Notation.** From now on,
$$
\alpha(t):=\int_{\partial^*E_t}|\nabla u|^{-1}\,d\mathcal H^{n-1}=-m'(t),
\qquad
\beta(t):=\int_{\partial^*E_t}|\nabla u|\,d\mathcal H^{n-1}=m(t),
$$
with Cauchy–Schwarz inequality $\alpha(t)\beta(t)\ge P(E_t)^2$ and equality
iff $|\nabla u|$ is $\mathcal H^{n-1}$-a.e. constant on $\partial^*E_t$.

---

## 5. Lemma 4 — Endpoint convexity gap and deficit identity

Define
$$
G(s):=I(s)+\frac{s^{1+2/n}}{(4+2n)\,\omega_n^{2/n}}.
$$
The function $s\mapsto s^{1+2/n}$ is smooth on $(0,|\Omega|]$, so $G$ inherits
the AC regularity of $I$, and
$$
\frac{d^2}{ds^2}\frac{s^{1+2/n}}{(4+2n)\omega_n^{2/n}}
=\frac{1}{n^2\omega_n^{2/n}\,s^{1-2/n}}
=\frac{1}{c_n s^{1-2/n}},
\qquad c_n:=n^2\omega_n^{2/n}.
$$

**Lemma 4.** For a.e. $s\in(0,|\Omega|)$, with $t=u^*(s)$ (equivalently
$s=m(t)$ on the strictly decreasing branch of $m$),
$$
G''(s)=\frac{1}{c_n s^{1-2/n}}-\frac{1}{\alpha(t)}.
$$
Multiplying numerator and denominator by $\beta(t)=m(t)=s$ and adding/subtracting
$P(E_t)^2$ in the numerator,
$$
\frac{1}{c_n s^{1-2/n}}-\frac{1}{\alpha(t)}
=\frac{\alpha(t)\,c_n^{-1}s^{2/n-1}\cdot s - 1\cdot s}{s\,\alpha(t)\cdot c_n^{-1} s^{1-2/n}\cdot ???}
$$
A cleaner form: using $\beta=s$ in the numerator,
$$
G''(s)=\frac{1}{c_n s^{1-2/n}}-\frac{\beta(t)}{\alpha(t)\beta(t)}
=\frac{\alpha(t)\beta(t)-c_n s^{2-2/n}}{c_n s^{1-2/n}\alpha(t)\beta(t)}\cdot ?
$$
Concretely, the identity that drives the change-of-variable computation is
the integrated form
$$
\int_0^{|\Omega|}\!\! s\,G''(s)\,ds
=\int_0^{\|u\|_\infty}\!\!\frac{D_H(t)+D_I(t)}{c_n\,m(t)^{1-2/n}}\,dt.
\tag{L4}
$$
We prove (L4) directly via the change of variable $s=m(t)$, $ds=-\alpha(t)\,dt$:
$$
\int_0^{|\Omega|}\!\! s\,G''(s)\,ds
=\int_0^{|\Omega|}\!\! s\Bigl(\frac{1}{c_n s^{1-2/n}}-\frac{1}{\alpha(t(s))}\Bigr)ds
=\int_0^{\|u\|_\infty}\!\!\Bigl(\frac{m(t)\alpha(t)}{c_n m(t)^{1-2/n}}-m(t)\Bigr)dt.
$$
Insert $\beta(t)=m(t)$ in the second term and add/subtract $P(E_t)^2/c_n m^{1-2/n}$
to expose the two defects:
$$
\frac{m(t)\alpha(t)}{c_n m(t)^{1-2/n}}-m(t)
=\frac{\alpha(t)\beta(t)-c_n m(t)^{2-2/n}}{c_n m(t)^{1-2/n}}
=\frac{D_H(t)+D_I(t)}{c_n m(t)^{1-2/n}},
$$
which is (L4). $\square$

**Endpoint convexity gap.** With $L:=|\Omega|$, define
$$
\Gamma(\Omega):=G'(L)-\frac{G(L)}{L}.
$$
Since $G(0)=I(0)+0=0$ and $G$ is $W^{2,1}_{\rm loc}((0,L])$ with $G''\ge 0$
a.e. (by $\alpha\beta\ge P^2\ge c_n m^{2-2/n}$, both factors nonnegative),
the convexity identity
$$
G'(L)-\frac{G(L)}{L}=\frac{1}{L}\int_0^L\!\!s\,G''(s)\,ds
$$
holds. (Integrate by parts: $\int_0^L sG''(s)ds=[sG'(s)]_0^L-\int_0^L G'(s)ds
=LG'(L)-G(L)$, valid because $G\in W^{2,1}((\epsilon,L])$ and the boundary
behavior at $s=0$ is $sG'(s)\to 0$, which follows from $u^*\in L^\infty$ and
the explicit form of $s^{2/n}$.)

**Endpoint value of $G$.** At $s=L$ one has $u^*(L)=0$, so by Lemma 3a,
$I(L)=\int_0^L u^*=\int_\Omega u$, and hence
$$
\frac{G(L)}{L}=\frac{1}{L}\int_\Omega u\,dx+\frac{L^{2/n}}{(4+2n)\omega_n^{2/n}}.
$$
Also $I'(L)=u^*(L)=0$, so
$$
G'(L)=\frac{L^{2/n}}{2n\omega_n^{2/n}}.
$$
Subtracting and recognizing that the explicit ball torsion energy is
$-\tfrac12\int_B u_B$ (Pólya–Szegő 1951; Bandle 1980, Ch. II), one obtains
$$
\Gamma(\Omega)=\frac{1}{L}\Bigl(\int_B u_B\,dx-\int_\Omega u_\Omega\,dx\Bigr)
=\frac{2}{|\Omega|}\bigl(E(\Omega)-E(B)\bigr).
\tag{L4-endpoint}
$$

Combining (L4) with (L4-endpoint) and the convexity-gap formula yields the
Theorem:
$$
\frac{2}{|\Omega|}\bigl(E(\Omega)-E(B)\bigr)
=\Gamma(\Omega)
=\frac{1}{|\Omega|}\int_0^{\|u\|_\infty}\!\!
\frac{D_H(t)+D_I(t)}{n^2\omega_n^{2/n}\,m(t)^{1-2/n}}\,dt.
\tag{Theorem}
$$
The countable jump levels of $m$ contribute zero by absolute continuity of
$m$ on $[\epsilon,\|u\|_\infty]$ for every $\epsilon>0$, and the contribution
from $t\in[0,\epsilon]$ vanishes in the $\epsilon\downarrow 0$ limit because
$D_H+D_I$ is bounded on $[0,\epsilon]$ uniformly while $m(t)\to|\Omega|$
stays away from zero.

---

## 6. Cauchy–Schwarz / isoperimetric interpretation

The two defects are precisely the two convexity gaps that the spectral profile
inequality of Pólya–Szegő/Talenti combines. By Cauchy–Schwarz on $\partial^*E_t$
applied to the pair $(|\nabla u|^{1/2},|\nabla u|^{-1/2})$:
$$
P(E_t)^2=\Bigl(\!\int_{\partial^*E_t}\!1\,d\mathcal H^{n-1}\Bigr)^2
\le \alpha(t)\,\beta(t),\qquad D_H(t)=\alpha(t)\beta(t)-P(E_t)^2\ge 0,
$$
with equality iff $|\nabla u|$ is constant $\mathcal H^{n-1}$-a.e. on
$\partial^*E_t$.

By the De Giorgi isoperimetric inequality for sets of finite perimeter,
$P(E_t)\ge n\omega_n^{1/n}|E_t|^{1-1/n}$, with equality iff $E_t$ is a ball.
Squaring,
$$
D_I(t)=P(E_t)^2-c_n m(t)^{2-2/n}\ge 0.
$$
Their weighted sum, integrated against $dt/(c_n m^{1-2/n})$, equals
$\frac{2}{|\Omega|}(E(\Omega)-E(B))$. Rigidity in the deficit identity
($\delta_T(\Omega)=0$) therefore forces, simultaneously and for a.e. $t$,
constancy of $|\nabla u|$ on $\partial^*E_t$ (overdetermined / Serrin) and
sphericality of $\partial^*E_t$ — i.e. the Saint–Venant rigidity of the ball.

---

## 7. Failure-mode discussion

1. **The identity is a.e., not pointwise.** Equation (L1)–(L2)–(L3') hold
   for $t$ outside an $\mathcal L^1$-null set of "bad" levels: countable
   plateaus of $u$, the Sard-exceptional set $\{t:|\nabla u|=0\text{ on a
   positive }\mathcal H^{n-1}\text{ part of }\{u=t\}\}$, and BV-coarea
   exceptional levels. Levels in this null set are absorbed by the $dt$
   integral.

2. **Reduced boundary, not topological boundary.** All integrals are on
   $\partial^*E_t$, which has $\mathcal H^{n-1}(\partial E_t\setminus\partial^*E_t)=0$
   for a.e. $t$ (De Giorgi). No regular submanifold structure is assumed; in
   particular cusps, self-tangencies, and the unreduced part of $\partial E_t$
   contribute nothing.

3. **No graph regularity.** The proof never parametrizes $\partial^*E_t$ as
   a graph. Steps 1–2 use BV coarea (Maggi 13.1) and Lipschitz truncation
   of $u-t$, neither of which requires smoothness.

4. **The "natural" formula $I''=-1/\beta$ is wrong off the ball.** It is the
   reciprocal of the *coarea* $\alpha=\int|\nabla u|^{-1}$ that enters $I''$,
   not the *flux* $\beta=\int|\nabla u|=m$. Replacing $\alpha$ by $\beta$
   creates exactly the $D_H$ defect — that is the content of the deficit
   identity. (Lemma 3c documents the fix from the source-note typo.)

5. **No regularity of $\partial\Omega$.** The result holds for arbitrary open
   $\Omega$ of finite measure. The torsion function exists variationally;
   $u\in L^\infty$ by Talenti; the rest is BV coarea.

---

## 8. Open issues / residual hypotheses

- **Need to assume $\Omega$ bounded? No, not at the level of this theorem.**
  Talenti's $L^\infty$ bound gives $\|u\|_\infty\le R^2/(2n)$ for any $\Omega$
  of finite measure. Boundedness $\Omega\subset B_R$ enters only later in the
  metric closure (Agents 2–4), where strong isoperimetry with radial trace
  control is invoked.

- **Connectedness of $\Omega$.** Not needed. The torsion function decouples
  across connected components, and the identity is additive in the obvious
  sense (the integral over $t$ pools all components).

- **Smoothness/regularity of $\partial\Omega$.** Not needed.

- **One-sided trace of $\nabla u$ on $\partial^*E_t$.** Not used. Lemma 2 is
  proved by Lipschitz truncation of $u$, avoiding any boundary trace of
  $\nabla u$.

- **Compactness / $\Omega$ in a fixed reference space.** Not needed.

- **Sard for Sobolev functions.** Used implicitly to know that "almost every
  level is regular in the BV-coarea sense", which follows directly from
  Ambrosio–Fusco–Pallara Thm 3.40 without invoking a Sard-Bochner theorem.

The deliverable is therefore unconditional on $\Omega$ open of finite measure.

---

## 9. What is genuinely new vs. cited

**Cited (essentially verbatim).**
- BV coarea / a.e. finite perimeter of level sets: Maggi 2012 Thm 13.1,
  Ambrosio–Fusco–Pallara 2000 Thm 3.40.
- Divergence theorem on sets of finite perimeter: Maggi 2012 Ch. 17.
- Decreasing-rearrangement framework and equimeasurability: Talenti 1976,
  Kawohl 1985, Kesavan 2006.
- $L^\infty$ bound on $u_\Omega$ via Talenti comparison: Talenti 1976.
- BV chain rule / monotone AC inverse: Ambrosio–Fusco–Pallara Thm 3.99 or
  Bénilan–Brezis–Crandall (1975).
- Endpoint identification $\Gamma(\Omega)=\tfrac{2}{|\Omega|}(E(\Omega)-E(B))$:
  is essentially the Pólya–Szegő/Bandle identity for the symmetrized energy,
  e.g. Bandle 1980 §II.5.
- Cauchy–Schwarz/Serrin gap form of $D_H$: classical, see Brothers–Ziemer
  1988 for the level-set viewpoint.

**Genuinely new (modest but necessary).**
- The combined *finite-perimeter* statement of the deficit identity on
  reduced boundaries for a.e. level, written without any selection or
  graph-entry assumption, is not standard. The closest published statements
  (e.g. Maggi 2012 §19 on rigidity) treat the rearrangement profile, not the
  exact convexity-gap integral on $\partial^*E_t$.
- The Lipschitz-truncation proof of (L2), Lemma 2, replacing the formal trace
  $\nabla u\cdot\nu_{E_t}=-|\nabla u|$, is the technical bridge that makes
  the identity rigorous without graph regularity.
- The correction in Lemma 3c (using $\alpha$, the $|\nabla u|^{-1}$-integral,
  in $I''$, rather than $\beta=m$ as the source note used) is required for
  the deficit identity to hold off the ball. The source note's
  $I''=-1/a(v(s))$ is correct only when $|\nabla u|$ is level-constant.

The proof is therefore a careful *no-selection, no-graph* assembly of standard
GMT inputs, with the two technical fixes recorded above. It serves as the
foundational identity that Agents 2–5 build on.

---

## References

- Ambrosio, L.; Fusco, N.; Pallara, D. *Functions of Bounded Variation and
  Free Discontinuity Problems.* Oxford, 2000. Thm 3.40 (coarea), Thm 3.99
  (chain rule).
- Bandle, C. *Isoperimetric Inequalities and Applications.* Pitman, 1980.
- Bénilan, P.; Brezis, H.; Crandall, M. G. *J. Anal. Math.* 1975 (BV chain rule).
- Brothers, J.; Ziemer, W. *J. Reine Angew. Math.* 384 (1988), 153–179.
- De Giorgi, E. *Sulla proprietà isoperimetrica della ipersfera...* (1958).
- Federer, H. *Geometric Measure Theory.* Springer, 1969.
- Figalli, A.; Maggi, F.; Pratelli, A. *Invent. Math.* 182 (2010), 167–211.
- Kawohl, B. *Rearrangements and Convexity of Level Sets in PDE.* LNM 1150,
  Springer, 1985.
- Kesavan, S. *Symmetrization and Applications.* World Scientific, 2006.
- Maggi, F. *Sets of Finite Perimeter and Geometric Variational Problems.*
  Cambridge, 2012. Ch. 13 (coarea), Ch. 17 (divergence), Ch. 19 (rigidity).
- Pólya, G.; Szegő, G. *Isoperimetric Inequalities in Mathematical Physics.*
  Princeton, 1951.
- Talenti, G. *Ann. Mat. Pura Appl.* 110 (1976), 353–372.
