# Candidate Proof of the Global Affine Shell Theorem

Date: 2026-05-25

This note tries to close the missing finite-perimeter shell theorem isolated in
`raw_moving_ball_shell_repair_attempt.md`. The proof below is intended as a
manuscript patch candidate, not yet as a replacement silently inserted into
`faber_krahn_raw_moving_ball_closure.tex`.

## Main Claim

Let

```tex
E_\rho=\{u>t(\rho)\},\qquad w(\rho)=-t'(\rho),
```

and let

```tex
T_h(x)=x+hW(x),\qquad W(x)=\frac{x-z}{\rho}+a.
```

At every radius `rho` satisfying the usual finite-perimeter, Sobolev--Sard,
differentiability, and corrected localized coarea conditions below,

```tex
\limsup_{h\downarrow0}
\frac{|E_{\rho+h}\Delta T_h(E_\rho)|}{h}
\le
\int_{\partial^*E_\rho}
\left|
\frac{w(\rho)}{|\nabla u|}
- W\cdot\nu_\rho
\right|\,d\mathcal H^{n-1}.
```

This is exactly Lemma `shell` in the raw manuscript, after using
`nu_rho=-nabla u/|nabla u|`.

## Correct Full-Measure Class

The admissible class should be defined using a fixed countable family.

Let `U_j` be all finite unions of rational balls whose closures are compactly
contained in `Omega`. For rational parameters

```tex
c\in\mathbb Q\cap[-1,0],\quad
\lambda\in\mathbb Q\cap[1,1/\rho_*],\quad
z,a\in\mathbb Q^n,\quad r\in\mathbb Q_{>0},
```

register the Borel endpoint pairs

```tex
\alpha={\bf 1}_{U_j}\bigl(\min(c,\nabla u\cdot(\lambda(x-z)+a))-r\bigr),

\beta={\bf 1}_{U_j}\bigl(\max(c,\nabla u\cdot(\lambda(x-z)+a))+r\bigr).
```

The family is countable and independent of `rho`. By the corrected
two-sided coarea differentiation lemma, each pair fails only at a null set of
levels. Pulling this null set back to radii is legitimate on `G_tau` because
`w>=tau_0` there:

```tex
|\{\rho\in G_\tau:t(\rho)\in N\}|
\le \tau_0^{-1}\int_{\{t(\rho)\in N\}}w(\rho)\,d\rho=0.
```

Thus for a.e. `rho in G_tau`, all registered localized slab differentiations
hold. The bad-density complement is still paid by the Lipschitz bound for `q`,
as in the manuscript.

## Correct Local Coarea Lemma

For bounded Borel `alpha<=beta`,

```tex
\lim_{h\downarrow0}\frac1h
|\{h\alpha<u-t<h\beta\}|
=
\int_{\partial^*E_t}\frac{\beta-\alpha}{|\nabla u|}\,d\mathcal H^{n-1}
```

for a.e. regular level `t`, provided the right side is finite.

The Borel approximation error is

```tex
2\eta\int_{\partial^*E_t}|\nabla u|^{-1}\,d\mathcal H^{n-1},
```

not `2 eta P(E_t)`. This is harmless after `eta downarrow 0`.

## Auxiliary Standard Lemma: BV Transport Tail Estimate

The only standard finite-perimeter input needed beyond coarea is the following
local upper estimate for small Lipschitz deformations.

```tex
\begin{lemma}[Weighted BV transport estimate]
Let E be a bounded set of finite perimeter, W\in C^1_b(\mathbb R^n;\mathbb R^n),
and \Phi_h(x)=x+hW(x) for |h| small. If 0\le\eta\le1 is continuous and
compactly supported, then
\[
   \limsup_{h\to0}
   \frac1{|h|}
   \int \eta(x)\,
      |\mathbf 1_{\Phi_h(E)}(x)-\mathbf 1_E(x)|\,dx
   \le
   \int_{\partial^*E}\eta\,|W\cdot\nu_E|\,d\mathcal H^{n-1}.
\]
\end{lemma}
```

For smooth `E`, this is the usual swept-volume formula: the moving boundary
crosses points with normal speed `W dot nu_E`; the weight can be frozen at
time zero because `eta` and `W` are uniformly continuous and
`\Phi_h=id+O(h)`. For finite-perimeter `E`, take a strict approximation by
smooth sets, use convergence of perimeter measures and normals
(Reshetnyak for continuous one-homogeneous integrands), and then pass to the
limit in `L^1` after applying the smooth estimate. This is an upper estimate,
not the problematic lower-semicontinuity passage from the old metric route.

Equivalently, if `K compactly contained U` and `dist(K,U^c)>0`, then for
small `h`,

```tex
\limsup_{h\to0}
\frac{|(\Phi_h(E)\Delta E)\setminus U|}{|h|}
\le
\int_{\partial^*E\setminus K}|W\cdot\nu_E|\,d\mathcal H^{n-1}.
```

Choose `eta=1` outside `U`, `eta=0` on `K`.

## Proof of the Global Shell Theorem

Fix an admissible good-density radius `rho` and set

```tex
E:=E_\rho,\quad t_0:=t(\rho),\quad w:=w(\rho).
```

Let

```tex
d\mu_\rho
:=
\left(
\frac{w}{|\nabla u|}+|W\cdot\nu_\rho|
+\left|
\frac{w}{|\nabla u|}-W\cdot\nu_\rho
\right|
\right)d\mathcal H^{n-1}\llcorner\partial^*E.
```

This is a finite Radon measure because

```tex
\int_{\partial^*E}\frac{w}{|\nabla u|}\,d\mathcal H^{n-1}=P(B_\rho),
```

and `W` is bounded on `Omega subset B_R` while `P(E)<infty`.

Since `partial^*E subset Omega` for the regular positive levels used in the
level-set identity, inner regularity gives, for every `epsilon>0`, a compact
set

```tex
K\subset \partial^*E\cap\Omega
```

such that

```tex
\mu_\rho(\partial^*E\setminus K)<\epsilon.
```

Choose a rational-balls open set `U compactly contained Omega` with
`K compactly contained U`. The countable admissibility class gives localized
coarea differentiation on `U`.

### Step 1: sharp estimate on the interior set `U`

Because `closure(U) compactly contained Omega`, interior elliptic regularity
gives `u in C^1(closure(U'))` for some open `U'` with
`closure(U) compactly contained U' compactly contained Omega`. For small `h`,
`T_h^{-1}(U) subset U'`, and uniformly for `x in U`,

```tex
u(T_h^{-1}x)
=u(x)-h\nabla u(x)\cdot W(x)+o(h),
```

while

```tex
t(\rho+h)=t_0-hw+o(h).
```

Therefore, if

```tex
x\in (E_{\rho+h}\Delta T_h(E))\cap U,
```

then `u(x)-t_0` lies between

```tex
-hw+o(h)
\quad\text{and}\quad
h\nabla u(x)\cdot W(x)+o(h).
```

Set

```tex
b(x):=\nabla u(x)\cdot W(x),\quad
\alpha_U={\bf 1}_U\min(-w,b),\quad
\beta_U={\bf 1}_U\max(-w,b).
```

After rational approximation of `-w`, `1/rho`, `z`, and `a`, and an outward
rational buffer, the corrected localized coarea lemma gives

```tex
\limsup_{h\downarrow0}
\frac{|(E_{\rho+h}\Delta T_h(E))\cap U|}{h}
\le
\int_{\partial^*E\cap U}
\frac{|w+\nabla u\cdot W|}{|\nabla u|}
\,d\mathcal H^{n-1}.
```

On `partial^*E`,

```tex
\nu_\rho=-\frac{\nabla u}{|\nabla u|},
```

so

```tex
\frac{|w+\nabla u\cdot W|}{|\nabla u|}
=
\left|\frac{w}{|\nabla u|}-W\cdot\nu_\rho\right|.
```

Thus

```tex
\limsup_{h\downarrow0}
\frac{|(E_{\rho+h}\Delta T_h(E))\cap U|}{h}
\le
\int_{\partial^*E\cap U}
\left|\frac{w}{|\nabla u|}-W\cdot\nu_\rho\right|
d\mathcal H^{n-1}.
```

### Step 2: crude tail estimate outside `U`

Use the triangle inequality

```tex
E_{\rho+h}\Delta T_h(E)
\subset
(E_{\rho+h}\Delta E)\cup(E\Delta T_h(E)).
```

For the level-set part, nestedness and localized coarea outside the rational
open set `U` give

```tex
\limsup_{h\downarrow0}
\frac{|(E_{\rho+h}\Delta E)\setminus U|}{h}
\le
w\int_{\partial^*E\setminus U}
\frac1{|\nabla u|}\,d\mathcal H^{n-1}.
```

The reason is that `E_{\rho+h}\setminus E={t(\rho+h)<u\le t_0}` and
`t_0-t(\rho+h)=hw+o(h)`. This uses only the registered set `U`: either apply
the localized coarea lemma to `U^c`, or subtract the `U`-localized formula
from the total formula. Since `K subset U`, the last integral is bounded by
the corresponding integral over `partial^*E\setminus K`.

For the affine deformation part, the BV transport tail estimate gives

```tex
\limsup_{h\downarrow0}
\frac{|(E\Delta T_h(E))\setminus U|}{h}
\le
\int_{\partial^*E\setminus K}
|W\cdot\nu_\rho|\,d\mathcal H^{n-1}.
```

Hence

```tex
\limsup_{h\downarrow0}
\frac{|(E_{\rho+h}\Delta T_h(E))\setminus U|}{h}
\le
\int_{\partial^*E\setminus K}
\left(
\frac{w}{|\nabla u|}+|W\cdot\nu_\rho|
\right)d\mathcal H^{n-1}
\le \epsilon.
```

up to the chosen normalization of `epsilon`.

### Step 3: combine and let the tail vanish

Combining the estimates on `U` and outside `U`,

```tex
\limsup_{h\downarrow0}
\frac{|E_{\rho+h}\Delta T_h(E)|}{h}
\le
\int_{\partial^*E\cap U}
\left|
\frac{w}{|\nabla u|}-W\cdot\nu_\rho
\right|d\mathcal H^{n-1}
\epsilon.
```

Since `K subset U`,

```tex
\int_{\partial^*E\cap U}
\left|
\frac{w}{|\nabla u|}-W\cdot\nu_\rho
\right|
\le
\int_{\partial^*E}
\left|
\frac{w}{|\nabla u|}-W\cdot\nu_\rho
\right|.
```

Letting `epsilon downarrow 0` proves the global affine shell estimate.

## What This Fixes

This proof avoids the invalid compact exhaustion in the raw manuscript. The
compact interior part gives the sharp cancellation. The complement is handled
by a deliberately crude estimate, but its boundary action is arbitrarily
small by inner regularity. No pointwise lower bound on `|\nabla u|` is used.

The only external finite-perimeter input beyond standard coarea is the
weighted BV transport estimate. This is much weaker than the old metric
upper-gradient theorem: it controls only the swept tail of one finite-perimeter
set under a fixed Lipschitz deformation.

## Manuscript Patch Shape

To update `faber_krahn_raw_moving_ball_closure.tex`, replace the current
Section `A coarea differentiation lemma` and Lemma `shell` proof by:

1. the corrected countable admissibility definition using rational localized
   endpoint pairs;
2. the corrected weighted `varcoarea` lemma;
3. the weighted BV transport tail lemma;
4. the global shell proof above.

Then change Theorem `qplus` from `rho in (0,1]` to `rho in (0,1)`.

## Remaining Audit Point

Before treating this as final, the weighted BV transport estimate should be
audited or cited precisely, e.g. from AFP/Maggi via strict approximation of
finite-perimeter sets and the smooth swept-volume formula. This is now a
standard finite-perimeter lemma, not a bespoke level-set deformation theorem.
