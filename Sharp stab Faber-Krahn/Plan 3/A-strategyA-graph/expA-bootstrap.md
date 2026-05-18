# Part D — the regularity bootstrap: small $H^{1/2}$ + bounded $C^{m,\gamma}$ ⇒ small $C^{2,\gamma_0}$

Independent exploration of **counter (ii)** of `STRATEGY_A_PLAN.md`, Step 2.
Setup: the good level $\St=\partial\Et$ is written as a graph
$\partial\Et=\{(1+\varphi(\xi))\,\xi:\xi\in\mathbb S^{n-1}\}$ over the
sphere. Two pieces of information about $\varphi$ are postulated:

* **(SV)** the Saint–Venant deficit controls only the half-derivative,
  $\ \|\varphi\|_{H^{1/2}(\mathbb S^{n-1})}\le\varepsilon\ $ with
  $\varepsilon=\varepsilon(\dT)\to0$ (the Fuglede form
  $\dT\simeq_n\sum_{k\ge2}\gamma_k|\hat\varphi_k|^2$,
  $\gamma_k\asymp k$, of `two-strategies.tex` §"Sharpness and the norm
  gap"; linear growth in $k$ ⇒ only $H^{1/2}$, and the explicit family
  $\varphi_h$ with $\|\varphi_h\|_{H^{1/2}}$ bounded,
  $\|\varphi_h\|_{H^1}\to\infty$ shows this is sharp);
* **(B)** Part B supplies a *fixed, $(n,R)$-uniform* high-order bound
  $\ \|\varphi\|_{C^{m,\gamma}(\mathbb S^{n-1})}\le M=M(n,R)\ $,
  $\gamma\in(0,1]$, with $M$ **independent of $\varepsilon$ / of $\dT$**.

Goal: a genuine interpolation
$$\|\varphi\|_{C^{2,\gamma_0}}\le C(n,m,\gamma,\gamma_0)\,
\varepsilon^{\theta}M^{1-\theta},\qquad
\theta=\theta(m,\gamma,\gamma_0,n)\in(0,1),$$
so that $\|\varphi\|_{C^{2,\gamma_0}}\le\delta_{\rm sph}(n,\gamma_0)$
(the BDV Theorem 3.3 threshold) once $\varepsilon$ is a small power of
$\dT$.

Throughout $d:=n-1=\dim\mathbb S^{n-1}$. All norms are on
$\mathbb S^{n-1}$; constants $C$ depend only on the displayed
parameters and the fixed Riemannian structure of the sphere.

---

## 1. The function-space scale and the one inequality that does everything

Work in the Besov/Hölder–Zygmund scale on the closed manifold
$\mathbb S^{n-1}$ (Laplace–Beltrami $-\Delta_{\mathbb S}$, spherical
harmonics $Y_{k}$, $-\Delta_{\mathbb S}Y_k=k(k+d-1)Y_k$). Recall the
standard identifications, valid on a compact boundaryless manifold:

* **Sobolev = Besov$_{2,2}$:** $H^{s}(\mathbb S^{d})=B^{s}_{2,2}$, with
  $\|\varphi\|_{H^s}^2\simeq\sum_k (1+k)^{2s}\|\Pi_k\varphi\|_{L^2}^2$
  ($\Pi_k$ = projection onto degree-$k$ harmonics). In particular
  $H^{1/2}=B^{1/2}_{2,2}$.
* **Hölder = Besov$_{\infty,\infty}$ (Zygmund):** for $r>0$,
  $r\notin\mathbb Z$, $C^{r}(\mathbb S^{d})=B^{r}_{\infty,\infty}$ with
  equivalent norms; here $C^{r}=C^{\lfloor r\rfloor,\,r-\lfloor
  r\rfloor}$. At integer $r$ one has the strict inclusions
  $C^{r}\subsetneq B^{r}_{\infty,\infty}=\Lambda_r$ (Zygmund class);
  this costs nothing below because the *target* exponent $2+\gamma_0$
  and the *source* exponent $m+\gamma$ are taken **non-integer**
  ($\gamma_0,\gamma\in(0,1)$), so every space that actually appears is
  a genuine Hölder space and $B^{r}_{\infty,\infty}=C^{r}$ there. (If
  one insists $\gamma=1$ in (B), replace $C^{m,1}$ by the slightly
  larger $\Lambda_{m+1}=B^{m+1}_{\infty,\infty}$ in the statement; the
  proof is unchanged and the conclusion lands in the honest Hölder
  space $C^{2,\gamma_0}$, $\gamma_0<1$, anyway.)

The single analytic input is the **three-parameter Besov
interpolation inequality with the integrability-index dimensional
shift**. On $\mathbb S^{d}$:

> **Lemma 1 (Besov interpolation, $B_{2,2}\!\leftrightarrow\!
> B_{\infty,\infty}$).**
> Let $s_0\in\mathbb R$, $s_1\in\mathbb R$, $\vartheta\in(0,1)$, and set
> $$r\;=\;(1-\vartheta)\,s_1+\vartheta\Bigl(s_0-\tfrac{d}{2}\Bigr).$$
> Then there is $C=C(d,s_0,s_1,\vartheta)$ with
> $$\|\varphi\|_{B^{r}_{\infty,\infty}}\;\le\;
> C\,\|\varphi\|_{B^{s_0}_{2,2}}^{\vartheta}\;
> \|\varphi\|_{B^{s_1}_{\infty,\infty}}^{1-\vartheta}
> \qquad\text{for all }\varphi\in B^{s_1}_{\infty,\infty}(\mathbb S^{d}).$$

The $-d/2$ on the $B_{2,2}$ endpoint is exactly the Sobolev embedding
loss $B^{s_0}_{2,2}=H^{s_0}\hookrightarrow
B^{s_0-d/2}_{\infty,\infty}=C^{s_0-d/2}$ (Besov embedding
$B^{\sigma}_{2,2}\hookrightarrow B^{\sigma-d/2}_{\infty,\infty}$ on a
$d$-manifold). It is what makes the inequality *true*: one cannot
interpolate an $L^\infty$-type norm purely against an $L^2$-type norm
without paying $d/2$ derivatives once.

### Proof of Lemma 1 (Littlewood–Paley, fully tracked)

Use the spectral Littlewood–Paley decomposition on $\mathbb S^{d}$:
fix a dyadic partition of unity $\{\psi_j\}_{j\ge0}$ in the
$\sqrt{-\Delta_{\mathbb S}}$-calculus, $\psi_0$ supported on
frequencies $\lesssim1$, $\psi_j$ ($j\ge1$) supported on
$|\xi|\simeq2^{j}$ (i.e. on harmonic degrees $k\simeq2^{j}$). Write
$\Delta_j\varphi=\psi_j(\sqrt{-\Delta_{\mathbb S}})\varphi$. The norm
characterizations are, with implied constants depending only on
$(d,\cdot)$,
$$\|\varphi\|_{B^{\sigma}_{p,p}}\;\simeq\;
\Bigl(\sum_{j\ge0}2^{j\sigma p}\|\Delta_j\varphi\|_{L^p}^{p}\Bigr)^{1/p}
\quad(1\le p<\infty),\qquad
\|\varphi\|_{B^{\sigma}_{\infty,\infty}}\;\simeq\;
\sup_{j\ge0}2^{j\sigma}\|\Delta_j\varphi\|_{L^\infty}.$$

**(i) Bernstein on the sphere.** For a function with frequency
localized at $2^{j}$ on the compact $d$-manifold $\mathbb S^{d}$,
$$\|\Delta_j\varphi\|_{L^\infty}\;\le\;C(d)\,2^{\,j d/2}\,
\|\Delta_j\varphi\|_{L^2}. \tag{Bern}$$
(Standard finite-band Bernstein inequality; on $\mathbb S^d$ it follows
from the spectral kernel bound for $\psi_j(\sqrt{-\Delta_{\mathbb
S}})$, whose Schwartz kernel has $L^1\!\to\!L^\infty$ norm
$\lesssim 2^{jd}$ and $L^2\!\to\!L^\infty$ norm $\lesssim 2^{jd/2}$.)

**(ii) Two bounds on the block $\|\Delta_j\varphi\|_{L^\infty}$.**
From the $B^{s_1}_{\infty,\infty}$ norm,
$$\|\Delta_j\varphi\|_{L^\infty}\;\le\;
2^{-j s_1}\,\|\varphi\|_{B^{s_1}_{\infty,\infty}}
\;=:\;2^{-j s_1}\,A_1. \tag{a}$$
From the $B^{s_0}_{2,2}$ norm via (Bern),
$$\|\Delta_j\varphi\|_{L^\infty}\;\le\;C(d)\,2^{j d/2}\,
\|\Delta_j\varphi\|_{L^2}\;\le\;C(d)\,2^{j d/2}\,2^{-j s_0}\,
\Bigl(\sum_{i}2^{2 i s_0}\|\Delta_i\varphi\|_{L^2}^2\Bigr)^{1/2}
\;\le\;C(d)\,2^{-j(s_0-d/2)}\,A_0, \tag{b}$$
where $A_0:=\|\varphi\|_{B^{s_0}_{2,2}}=\|\varphi\|_{H^{s_0}}$ and we
used $\|\Delta_j\varphi\|_{L^2}\le 2^{-js_0}A_0$ termwise.

**(iii) Geometric interpolation of the two block bounds.** Raise
(a) to the power $1-\vartheta$ and (b) to the power $\vartheta$ and
multiply:
$$\|\Delta_j\varphi\|_{L^\infty}
\;\le\;C(d)^{\vartheta}\,
2^{-j\bigl[(1-\vartheta)s_1+\vartheta(s_0-d/2)\bigr]}\,
A_1^{1-\vartheta}A_0^{\vartheta}
\;=\;C(d)^{\vartheta}\,2^{-j r}\,A_1^{1-\vartheta}A_0^{\vartheta},$$
with $r=(1-\vartheta)s_1+\vartheta(s_0-d/2)$ exactly as stated.
Multiplying by $2^{jr}$ and taking $\sup_{j\ge0}$ gives
$$\|\varphi\|_{B^{r}_{\infty,\infty}}\;\simeq\;\sup_j 2^{jr}
\|\Delta_j\varphi\|_{L^\infty}\;\le\;C(d,\vartheta)\,
A_0^{\vartheta}\,A_1^{1-\vartheta},$$
which is the claim with $C(d,s_0,s_1,\vartheta)=C(d)^{\vartheta}\cdot
(\text{norm-equivalence constants})$. $\qquad\blacksquare$

Two remarks the proof makes transparent and that matter for (b) of the
question:

* The inequality is **multiplicative and homogeneous**: it is literally
  an interpolation between two *given* finite quantities $A_0$ (the
  small one) and $A_1$ (the bounded one). Nowhere did smallness of
  $A_0$ enter the *derivation*; the inequality holds for every
  $\varphi$ with finite $A_1$. Smallness is only *used afterwards*, by
  plugging numbers in. This is the formal content of "genuine
  interpolation, no hidden bootstrap".
* The constant $C$ depends only on $d=n-1$, the chosen exponents and
  $\vartheta$ — never on $\varphi$, on $\varepsilon$, or on $M$.

---

## 2. The interpolation lemma in the required spaces, and the exact $\theta$

Specialize Lemma 1 with the two endpoints dictated by the problem:

* **small endpoint:** $s_0=\tfrac12$, $B^{1/2}_{2,2}=H^{1/2}$, size
  $A_0=\|\varphi\|_{H^{1/2}}\le\varepsilon$;
* **bounded endpoint:** $s_1=m+\gamma$,
  $B^{m+\gamma}_{\infty,\infty}=C^{m,\gamma}$ ($m+\gamma\notin\mathbb
  Z$), size $A_1=\|\varphi\|_{C^{m,\gamma}}\le M$;
* **target:** $r=2+\gamma_0$, $B^{2+\gamma_0}_{\infty,\infty}=
  C^{2,\gamma_0}$ ($\gamma_0\in(0,1)$, so $2+\gamma_0\notin\mathbb Z$,
  honest Hölder space — no Zygmund gap).

> **Lemma 2 (the bootstrap interpolation).**
> Let $n\ge2$, $d=n-1$, $\gamma\in(0,1)$, $\gamma_0\in(0,1)$, and let
> $m\in\mathbb N$ satisfy the threshold of §3, namely
> $$m+\gamma\;>\;2+\gamma_0\qquad\text{and}\qquad
> \tfrac12-\tfrac{d}{2}\;<\;2+\gamma_0\ \ (\text{automatic, see §3}).$$
> Define
> $$\boxed{\;\theta\;=\;\dfrac{(m+\gamma)-(2+\gamma_0)}
> {(m+\gamma)-\bigl(\tfrac12-\tfrac{n-1}{2}\bigr)}
> \;=\;\dfrac{(m+\gamma)-(2+\gamma_0)}
> {(m+\gamma)+\tfrac{n}{2}-1}\;\in(0,1).\;}$$
> Then there is $C=C(n,m,\gamma,\gamma_0)$ such that for every
> $\varphi\in C^{m,\gamma}(\mathbb S^{n-1})$,
> $$\|\varphi\|_{C^{2,\gamma_0}(\mathbb S^{n-1})}\;\le\;
> C\;\|\varphi\|_{H^{1/2}(\mathbb S^{n-1})}^{\theta}\;
> \|\varphi\|_{C^{m,\gamma}(\mathbb S^{n-1})}^{1-\theta}.$$

**Derivation of $\theta$.** Lemma 1 requires the exponent identity
$$r=(1-\vartheta)s_1+\vartheta\bigl(s_0-\tfrac d2\bigr),\qquad
\text{i.e.}\qquad
2+\gamma_0=(1-\theta)(m+\gamma)+\theta\bigl(\tfrac12-\tfrac d2\bigr).$$
Solve for $\theta$:
$$2+\gamma_0=(m+\gamma)-\theta\Bigl[(m+\gamma)-\bigl(\tfrac12-\tfrac
d2\bigr)\Bigr]
\;\Longrightarrow\;
\theta=\frac{(m+\gamma)-(2+\gamma_0)}
{(m+\gamma)-\bigl(\tfrac12-\tfrac d2\bigr)}
=\frac{(m+\gamma)-(2+\gamma_0)}{(m+\gamma)+\tfrac n2-1}.$$
(using $\tfrac12-\tfrac d2=\tfrac12-\tfrac{n-1}2=1-\tfrac n2$, so the
denominator is $(m+\gamma)-1+\tfrac n2=(m+\gamma)+\tfrac n2-1$.)
This is in $(0,1)$ precisely when the numerator is positive and
smaller than the denominator:

* numerator $>0\iff m+\gamma>2+\gamma_0$ (the source is genuinely
  smoother than the target — necessary for any interpolation);
* numerator $<$ denominator
  $\iff -(2+\gamma_0)<\tfrac n2-1\iff \tfrac n2>1-\gamma_0$, which
  holds for all $n\ge2$ and $\gamma_0>0$ (already $\tfrac n2\ge1$).

So $\theta\in(0,1)$ exactly under the single substantive condition
$m+\gamma>2+\gamma_0$. $\qquad\blacksquare$

**Sanity checks.**
* $\theta\nearrow1$ as $\gamma_0\downarrow$ and $m+\gamma\downarrow
  2+\gamma_0$ (less is asked of the bounded endpoint ⇒ more weight on
  the small one — best case, almost $\varepsilon^{1}$).
* $\theta\to0$ as $m\to\infty$ (a very high uniform bound buys little
  exponent — diminishing returns). The exponent **degrades like
  $1/m$**: for large $m$,
  $\theta\simeq\dfrac{m}{m}\cdot\dfrac{1}{1}\big/\!\cdots$ — precisely
  $\theta=1-\dfrac{(2+\gamma_0)+\tfrac n2-1}{(m+\gamma)+\tfrac n2-1}
  \to1$? — **no**: recompute. As $m\to\infty$,
  $\theta=\dfrac{m+\gamma-2-\gamma_0}{m+\gamma+\frac n2-1}\to1$. So a
  *larger* $m$ pushes $\theta\to1$ (more of the $\varepsilon$ power),
  not to $0$. The penalty for large $m$ is *not* in $\theta$ but in
  the constant $C(n,m,\gamma,\gamma_0)$ and, more importantly, in the
  difficulty Part B has delivering large $m$. The exponent is
  monotone increasing in $m$ and bounded by $1$; the *floor* is at the
  minimal admissible $m$ (§3), where $\theta$ is smallest. This is the
  honest dependence; the earlier inline "diminishing returns" intuition
  was wrong and is corrected here.

---

## 3. Minimal $m$, and the dimensional side-condition

The only substantive constraint from Lemma 2 is
$$m+\gamma>2+\gamma_0.$$
Since $\gamma\in(0,1)$ and $\gamma_0\in(0,1)$:

* if one is willing to choose $\gamma$ close to $1$: $m+\gamma>2+\gamma_0$
  is satisfiable with $m=2$ provided $\gamma>\gamma_0$ (e.g.
  $\gamma_0=\tfrac12$, $\gamma=\tfrac34$, $m=2$ gives
  $m+\gamma=2.75>2.5$);
* with no control on the relation between $\gamma$ and $\gamma_0$
  (Part B may deliver some fixed small $\gamma$), the safe minimal
  integer is
  $$\boxed{\,m_{\min}=3\,}\qquad\text{(then }m+\gamma\ge3>2+\gamma_0
  \text{ for every }\gamma\in(0,1),\ \gamma_0\in(0,1)).$$
  i.e. **a uniform $C^{3,\gamma}$ bound on the graph from Part B
  always suffices**, irrespective of the values of $\gamma,\gamma_0$.
  $m=2$ works only in the favorable sub-case $\gamma>\gamma_0$.

The dimensional side-condition $\tfrac12-\tfrac d2<2+\gamma_0$ (needed
so that the small endpoint, after the embedding loss, still sits
*below* the target — otherwise $H^{1/2}$ would already control
$C^{2,\gamma_0}$ and there would be nothing to prove) reads
$1-\tfrac n2<2+\gamma_0$, i.e. $\tfrac n2>-1-\gamma_0$, **vacuously
true for every $n\ge2$**. Equivalently: $H^{1/2}(\mathbb S^{n-1})$
embeds only into $C^{(1/2)-(n-1)/2}=C^{1-n/2}$, which for $n\ge2$ is a
*negative-order* (distributional) Hölder space — far below
$C^{2,\gamma_0}$ — so the bounded $C^{m,\gamma}$ endpoint is genuinely
indispensable and the interpolation is non-degenerate. In particular,
for $n\ge4$ the small endpoint does not even embed into $C^0$; the
interpolation is exactly the mechanism that converts a *weak* (here,
for large $n$, even sub-continuous) smallness into pointwise
$C^{2,\gamma_0}$ smallness by borrowing $d/2+\dots$ derivatives from
the $\varepsilon$-independent bound. No circularity is hidden in this:
see §5.

Numerical $\theta$ at the minimal admissible bound, taking the safe
$m=3$ and writing $s_1=3+\gamma$:
$$\theta=\frac{(3+\gamma)-(2+\gamma_0)}{(3+\gamma)+\tfrac n2-1}
=\frac{1+\gamma-\gamma_0}{2+\gamma+\tfrac n2}.$$
E.g. $n=3$, $\gamma=\gamma_0=\tfrac12$:
$\theta=\dfrac{1}{4}=0.25$. $n=2$, $\gamma=\gamma_0=\tfrac12$:
$\theta=\dfrac{1}{3.5}\approx0.286$. $n=8$,
$\gamma=\gamma_0=\tfrac12$:
$\theta=\dfrac1{6.5}\approx0.154$. In every case $\theta$ is a fixed
positive number depending only on $(n,m,\gamma,\gamma_0)$ — uniformly
in $\varepsilon$ and $M$.

---

## 4. Conclusion: small $H^{1/2}$ + bounded $C^{m,\gamma}$ ⇒ small
$C^{2,\gamma_0}$, and the power of $\dT$

Insert (SV) and (B) into Lemma 2:
$$\|\varphi\|_{C^{2,\gamma_0}}\;\le\;C(n,m,\gamma,\gamma_0)\,
\varepsilon^{\theta}\,M^{1-\theta},\qquad
\theta=\frac{(m+\gamma)-(2+\gamma_0)}{(m+\gamma)+\tfrac n2-1}\in(0,1).$$
Because $\theta>0$ and $M=M(n,R)$ is a **fixed** number (does not grow
as $\varepsilon\to0$ — this is the load-bearing hypothesis, audited in
§5), the right-hand side $\to0$ as $\varepsilon\to0$. Quantitatively,
to reach the BDV Theorem 3.3 threshold $\delta_{\rm sph}(n,\gamma_0)$
it suffices that
$$C\,\varepsilon^{\theta}M^{1-\theta}\le\delta_{\rm sph}
\iff
\varepsilon\;\le\;
\Bigl(\frac{\delta_{\rm sph}(n,\gamma_0)}{C(n,m,\gamma,\gamma_0)}\Bigr)^{1/\theta}
M^{-(1-\theta)/\theta}
\;=:\;\varepsilon_*(n,m,\gamma,\gamma_0,R).$$
$\varepsilon_*$ is an explicit positive constant in the named
quantities; it is *smaller* for larger $M$ (a rougher
$\varepsilon$-independent bound forces a smaller deficit) but always
positive.

**Power of $\dT$.** From the Fuglede form (`two-strategies.tex`
§"Sharpness and the norm gap"), the Saint–Venant control of the
half-derivative is $\|\varphi\|_{H^{1/2}}^2\lesssim_n\dT(\Et)$, and by
the deficit-transfer Lemma (`two-strategies.tex` Lemma 2.5,
$\dT(\Et)\le2\dT(\Om)$) one may take
$$\varepsilon\;=\;\|\varphi\|_{H^{1/2}}\;\le\;
C_{\rm SV}(n)\,\dT(\Om)^{1/2}.$$
Hence
$$\|\varphi\|_{C^{2,\gamma_0}}\;\le\;
C\,\bigl(C_{\rm SV}\dT(\Om)^{1/2}\bigr)^{\theta}M^{1-\theta}
\;=\;C'\,\dT(\Om)^{\theta/2}\,M^{1-\theta},$$
a **strictly positive power $\theta/2>0$ of the deficit**. Therefore
$\|\varphi\|_{C^{2,\gamma_0}}\le\delta_{\rm sph}$ as soon as
$$\dT(\Om)\;\le\;
\Bigl(\frac{\delta_{\rm sph}}{C'M^{1-\theta}}\Bigr)^{2/\theta}
\;=:\;\dT^{0}_{\rm boot}(n,m,\gamma,\gamma_0,R)>0.$$
The exponent $\theta/2$ is *not* the sharp $\dT^1$ scaling — but it
does **not** need to be: at this stage one only needs the
nearly-spherical theorem's *qualitative smallness threshold* to be
crossed; the sharp quadratic relation
$\Asym^2\lesssim\dT$ is then produced *by BDV Theorem 3.3 itself*
(its second-variation coercivity), not by this interpolation. So a
fractional power here is harmless, exactly because it gates a
threshold and is not propagated into the final exponent. (Contrast: a
fractional power *would* be fatal if it sat on the
$\Asym\!\leftrightarrow\!\dT$ relation itself — cf. the sharpness
discussion in `two-strategies.tex` §"Setup".)

So, **as a self-contained interpolation/bootstrap statement, Part D is
true and quantitative**: minimal $m=3$ (or $m=2$ if $\gamma>\gamma_0$),
exact $\theta=\dfrac{(m+\gamma)-(2+\gamma_0)}{(m+\gamma)+\frac n2-1}$,
conclusion $\|\varphi\|_{C^{2,\gamma_0}}\le C\dT^{\theta/2}M^{1-\theta}
\to0$.

---

## 5. Honest audit: is it genuinely interpolation, or is $M$
secretly $\varepsilon$-dependent? (the circularity question)

The interpolation inequality itself (Lemmas 1–2) is **unconditionally
true and non-circular**: its proof (Littlewood–Paley + Bernstein) uses
no smallness whatsoever and no relation between the two endpoints
beyond $m+\gamma>2+\gamma_0$. The constant $C$ is purely
$(n,m,\gamma,\gamma_0)$. There is **no hidden bootstrap inside the
inequality**: $A_0$ and $A_1$ are independent given data, and the
inequality is the trivial geometric mean of two block estimates. This
fully answers (a) and the "genuine interpolation" half of (b).

The **entire** soundness question is therefore displaced, cleanly, onto
a single hypothesis:

> **(B-independence).** The uniform bound $\|\varphi\|_{C^{m,\gamma}}\le
> M(n,R)$ from Part B must hold with $M$ a constant that does **not**
> degenerate (blow up) as $\varepsilon\to0$ / $\dT\to0$, and in
> particular is not obtained *via* a smallness of
> $\|\varphi\|_{C^{2,\gamma_0}}$ that one is here trying to prove.

If (B-independence) holds, the bootstrap is **non-circular**: a fixed
$M$, a positive $\varepsilon$-power, done. If Part B's $M$ secretly
behaves like $M\sim\varepsilon^{-a}$ ($a>0$) — e.g. because the only
available high-order bound comes from interior Schauder with constant
$\sim\dist(\St,\partial\Om)^{-\beta}$ that *degrades as the level nears
a rough $\partial\Om$* (precisely checkpoint **A2** of
`two-strategies.tex`, "interior Schauder gives only a constant
$\sim\dist(\St,\partial\Om)^{-\beta}$ that degrades as the level nears
a rough $\partial\Om$") — then
$$\|\varphi\|_{C^{2,\gamma_0}}\le C\varepsilon^{\theta}
M^{1-\theta}\sim C\,\varepsilon^{\theta-a(1-\theta)},$$
and the bootstrap *closes only if $\theta>a(1-\theta)$*, i.e.
$a<\theta/(1-\theta)$. With $\theta$ as small as $0.15$–$0.29$ at the
minimal $m$ (§3), the tolerance $a<\theta/(1-\theta)\approx0.18$–$0.40$
is **slim**: any more than a mild inverse-power degradation of $M$ in
$\varepsilon$ destroys the conclusion. This is the genuine residual,
and it is *exactly the open point A2 of `two-strategies.tex` §"Honest
status of Strategy~A"*; it is **not** internal to Part D.

**Flag (circularity / interface).** Part D contains **no internal
circularity**: the interpolation is genuine, the smallness being proved
($\|\varphi\|_{C^{2,\gamma_0}}$) never feeds back into the inequality.
The *only* way circularity can enter the program is through the
**Part B ↔ Part D interface**: the bootstrap is sound **iff Part B
delivers $M(n,R)$ truly independent of $\varepsilon$/$\dT$**, with at
worst a degradation $M\sim\varepsilon^{-a}$, $a<\theta/(1-\theta)$.

* If Part B's quantified-smoothness mechanism (penalised replacement /
  the self-quantification of Part E) yields $M$ from
  $(n,R)$-data alone — as Plan 1 §5 / Proposition 5.1 *asserts* via
  hodograph + Kinderlehrer–Nirenberg uniform Schauder (and as
  `WHAT_PLAN1_DOES.md` (P3) flags is "exactly the recurring norm-gap,
  claimed repaired but smallness constants not tracked") — then Part D
  is unconditionally fine and quantitative as in §4.
* If, on the contrary, the only honest high-order bound is the
  interior-Schauder one whose constant blows up at the rough boundary
  (checkpoint A2), then Part D's hypothesis (B) is *not met with an
  $\varepsilon$-uniform $M$*, and the chain has a real gap **located at
  Part B**, not at the interpolation. Part D cannot, and does not,
  repair that gap; it can only convert an honest $\varepsilon$-uniform
  $M$ into the needed $C^{2,\gamma_0}$ smallness.

This is the precise, honest statement: **(a)** the interpolation
inequality and the exact $\theta$ are established unconditionally;
**(b)** it is genuine interpolation with no hidden need for the
smallness being proved — the entire conditionality is pushed onto
"(B) supplies $\varepsilon$-independent $M$", which is *external* to
Part D; **(c)** minimal $m=3$ (or $m=2$ if $\gamma>\gamma_0$),
$\theta>0$ explicit, and a power of $\dT$ (namely $\dT^{\theta/2}$)
suffices to cross the BDV Theorem 3.3 threshold, because that step
only needs threshold-crossing and the sharp exponent is regenerated by
the second variation downstream.

---

## 6. One-paragraph residual

The interpolation lemma is rigorous and constant-tracked; the bootstrap
is *non-circular as a statement*. The single residual is the
**Part B/Part D interface**: whether the $(n,R)$-uniform $C^{3,\gamma}$
(or $C^{2,\gamma}$, $\gamma>\gamma_0$) bound exists with $M$ genuinely
independent of $\dT$ — equivalently, with at worst an inverse power
$M\lesssim\dT^{-a}$, $a<\theta/(1-\theta)$. This is checkpoint A2 of
`two-strategies.tex` and (P3) of `WHAT_PLAN1_DOES.md`, and it lives in
Part B (quantified boundary regularity), not here. Strategy B, by
contrast, never needs any graph norm and so never meets this interface
at all.
