# Agent 2: graph entry from small $D_H + D_I$

This note attacks the central Plan 3 question.

> If a near-boundary torsion superlevel set $E_t$ has
> $D_H(t)+D_I(t)\le\eta$ and $|\Omega\setminus E_t|$ lies in the outer collar
> scale, does $\partial E_t$, after translation and scaling, become a graph
> over $\partial B_1$, with norm tending to zero with $\eta$?

The conclusion is an **exact obstruction report**, not a proof. The
combination $D_H+D_I$ delivers three things on a near-boundary level:
quantitative $L^1/\text{translations}$ closeness to a ball, a Fusco--Julin
normal-oscillation index, and a weighted $L^2$ Serrin defect. By itself, on
arbitrary torsion levels, it does **not** yield a Lipschitz graph over
$\partial B_1$. The graph conclusion requires an a priori regularity input
that the level-set identity does not supply: a two-sided density estimate
(equivalently, a lower bound on $|\nabla u|$ on $\Sigma_t$ together with a
Hausdorff smallness statement). Plan 1 supplies these through the BDV
selected minimiser. Plan 2 does not.

Output:

1. the strongest provable substitute (Theorem 2.1) — an
   $L^1/\text{translations}$ FMP / FJ statement plus a weighted $L^2$
   approximate Serrin condition;
2. an explicit list of the missing PDE inputs (§3);
3. a hybrid graph-entry statement using Plan 1 inputs (Theorem 5.1);
4. the recommended Plan 2 substitute that never forms a graph (§4).

This is a **hybrid report**: pure Plan 2 reaches Theorem 2.1; graph entry
requires Plan 1 inputs.

Files used:

- `Plan 2/level-set-deficit-identity.md`
- `Plan 2/global-foliation-trace.md`
- `Plan 2/selected-boundary-layer-theorem.md`
- `Plan 2/weighted-serrin-collar-reduction.md`
- `Plan 2/plan2.md`
- `Plan 2/concrete-next-steps.md`
- `Plan 2/nicola-tilli-stability-import.md`
- `Plan 2/outer-foliation-entry-proof-attempt.md`
- `Final/NearlySphericalClosure.tex`
- `Final/GraphEntry.tex`

Throughout we volume-normalise so $|\Omega|=\omega_n$, $B=B_1$, and write
$\delta:=\delta_T(\Omega)=E(\Omega)-E(B)$, $E_t=\{u>t\}$, $m(t)=|E_t|$,
$\Sigma_t=\{u=t\}$, $r(t)=(m(t)/\omega_n)^{1/n}$.

## 1. What $D_H(t)+D_I(t)\le\eta$ actually buys

The four statements below are **proved unconditionally** in the existing
Plan 2 notes.

### 1.1 $D_I(t)$ part: quantitative isoperimetry on $E_t$

Fusco--Maggi--Pratelli applied to $E_t$ gives
$$
\mathcal A(E_t)^2\ \le\ C_n\,\frac{D_I(t)}{m(t)^{2-2/n}}.
$$
References: `level-set-deficit-identity.md` §5, `selected-boundary-layer-
theorem.md` Cor. 2.2, `weighted-serrin-collar-reduction.md` §4. Under
$D_I(t)\le\eta$ and $m(t)\simeq_n 1$,
$$
\mathcal A(E_t)^2\le C_n\eta.
\tag{1.1}
$$
This is an $L^1$-symmetric-difference statement modulo translations.

The strong form (Fusco--Julin) controls the *normal oscillation index*
$$
\beta(E_t)^2:=\inf_{z\in\mathbb R^n}\!\int_{\partial^*E_t}
\bigl|\nu_{E_t}-\tfrac{x-z}{|x-z|}\bigr|^2 d\mathcal H^{n-1}
\ \le\ C_n\bigl(P(E_t)-P(B_{r(t)})\bigr)\ \le\ C_n m(t)^{1/n-1}D_I(t).
$$
This is the input used in `outer-foliation-entry-proof-attempt.md` §8.

### 1.2 $D_H(t)$ part: weighted Serrin variance

By the identity in `level-set-deficit-identity.md` §6, with
$\bar f_t=m(t)/P(E_t)$,
$$
\int_{\Sigma_t}\frac{(|\nabla u|-\bar f_t)^2}{|\nabla u|}\,d\mathcal H^{n-1}
\ =\ \frac{m(t)}{P(E_t)^2}\,D_H(t).
\tag{1.2}
$$
This is a **weighted** $L^2(1/|\nabla u|)$ smallness of $|\nabla u|-\bar f_t$
along $\Sigma_t$. It is a Serrin defect, but in a weighted norm.

### 1.3 What is *not* automatic from $D_H+D_I$ alone

None of the following follows from $D_H+D_I\le\eta$ without additional
regularity:

- a pointwise lower bound $|\nabla u|\ge c>0$ on $\Sigma_t$ (needed to
  unweight (1.2));
- a pointwise upper bound $|\nabla u|\le C$ on $\Sigma_t$;
- Hausdorff distance $d_H(\partial E_t,z+\partial B_{r(t)})$ small compared
  to $r(t)$;
- two-sided density of $E_t$ at scales comparable to $r(t)$.

The Fraenkel smallness (1.1) is purely $L^1$. It is compatible with thin
filaments or external bubbles that carry $O(1)$ Hausdorff asymmetry while
contributing only $O(\eta)$ to $D_I$ and $D_H$. The conversion of $L^1$ to
Hausdorff in `Final/GraphEntry.tex` Lemma 3.2 (`densH`) uses the BDV
two-sided density (L4.9), which is not implied by $D_H+D_I$.

## 2. Strongest provable substitute (pure Plan 2)

### Theorem 2.1 (pure Plan 2 substitute for graph entry)

Let $E_t$ be a near-boundary torsion superlevel set with
$m(t)\in[\rho_*^n\omega_n,\omega_n]$ for a fixed $\rho_*\in(0,1)$, and
$D_H(t)+D_I(t)\le\eta$. Then there exists $z\in\mathbb R^n$ such that
$$
\frac{|E_t\Delta(z+B_{r(t)})|^2}{m(t)^2}\ \le\ C_n\eta,
\tag{2.1}
$$
$$
\int_{\partial^*E_t}\bigl|\nu_{E_t}-\tfrac{x-z}{|x-z|}\bigr|^2 d\mathcal H^{n-1}
\ \le\ C_n\eta,
\tag{2.2}
$$
$$
\int_{\Sigma_t}\frac{(|\nabla u|-\bar f_t)^2}{|\nabla u|}\,d\mathcal H^{n-1}
\ \le\ C_n\eta.
\tag{2.3}
$$

Proof sketch (assembled from existing Plan 2 lemmas):

- (2.1) is FMP applied to $E_t$;
- (2.2) is Fusco--Julin's strong form, as in
  `outer-foliation-entry-proof-attempt.md` §8;
- (2.3) is the identity (1.2);
- the centre $z$ is the FMP / FJ minimiser. On the outer annulus it varies
  with the level only modulo the FvHT overlap bound
  (`outer-foliation-entry-proof-attempt.md` §3, eq. (3.1)).

This is proved unconditionally. **It is not a graph statement.**

### 2.2 Why Theorem 2.1 falls short of graph entry

A graph statement
$\partial E_t=\{(r(t)+h_t(\theta))\theta+z_t:\theta\in\partial B_1\}$ with
$\|h_t\|_{C^{0,1}}\to 0$ requires three further inputs, none in
(2.1)--(2.3):

- (G1) **Hausdorff smallness:** $d_H(\partial E_t,z_t+\partial B_{r(t)})\to 0$.
  From (2.1) alone one only has $L^1$ smallness. Conversion requires
  two-sided density at $\partial E_t$ (BDV L4.9 in
  `Final/GraphEntry.tex`); not available on arbitrary torsion levels.

- (G2) **Local flatness improvement:** an Alt--Caffarelli-type step is
  needed to produce a $C^{1,\gamma}$ local graph. This requires uniform
  two-sided density and nondegeneracy of $u$ at level $t$; on arbitrary
  $\Omega$ these are unavailable for interior levels with $t>0$.

- (G3) **Lipschitz norm of the graph:** even with (G1)+(G2) one still needs
  $\|h_t\|_{C^{0,1}}\to 0$. The $L^2$ bound from (1.1) only controls
  $\|h_t\|_{L^2}$; the Lipschitz upgrade is interpolation with a
  $C^{0,\gamma}$ a priori bound (`weighted-serrin-collar-reduction.md` §3),
  which depends on a uniform $C^\gamma$ bound for $|\nabla u|$ on
  $\Sigma_t$. This is selected-minimiser input, not level-set input.

In one sentence: (G1), (G2), (G3) are regularity statements about $u$ at
the level $t$, whereas (2.1)--(2.3) are defect statements about $u$ at the
level $t$. The two are not interchangeable.

## 3. Exact obstruction report

The graph-entry theorem fails to be deducible from $D_H+D_I$ through the
following four obstructions.

### 3.1 Obstruction A: rough levels have no a priori density

Plan 1 / BDV's two-sided density (L4.9 in `Final/GraphEntry.tex`) is what
converts $L^1$ smallness to Hausdorff smallness. It is a free-boundary
regularity statement for the selected minimiser's zero set $\{u>0\}$. For
torsion of an arbitrary $\Omega$, no analogous statement is known for
interior level sets $E_t$, $t>0$, when $\partial\Omega$ is rough. Without
this, thin filaments or detached bubbles can carry $O(1)$ Hausdorff
asymmetry while contributing only $O(\eta)$ to $D_I+D_H$. The standard fix
in Plan 1 is the selection principle.

### 3.2 Obstruction B: $D_H$ is a weighted variance, not an $L^\infty$ defect

Identity (1.2) is intrinsically $L^2(1/|\nabla u|)$. Without a positive
lower bound $|\nabla u|\ge c$ on $\Sigma_t$ (equivalently a uniform
Bernoulli coefficient bound, L4.16 of `Final/GraphEntry.tex`), even an
ordinary $L^2(\Sigma_t)$ defect cannot be extracted. Moreover the available
Serrin stability theorems (Brandolini--Nitsch--Salani--Trombetti;
Ciraolo--Magnanini--Vespri; Magnanini--Poggesi) accept $L^2$ or oscillation
norms of $\partial_\nu w-c$ and require **a priori $C^{1,\gamma}$** input
on the boundary. They are conditional graph statements, not graph-entry
statements.

This is the precise sense in which "small $D_H$ is an approximate Serrin
condition, not automatically a graph theorem".

### 3.3 Obstruction C: the Serrin variance does not produce a graph

Even after assuming $|\nabla u|\ge c_t>0$ on $\Sigma_t$, the upgraded
estimate $\|f_t-\bar f_t\|_{L^2(\Sigma_t)}^2\le C D_H(t)$ feeds
Serrin-stability theorems, which output Hausdorff or asymmetry closeness
of $E_t$ to a ball. They do **not** output a Lipschitz graph
parametrisation. The Lipschitz graph is the input, not the output, of
every Serrin-stability theorem currently known. The chain
"level-set defect $\Rightarrow$ Serrin defect $\Rightarrow$ graph"
is not closed: the last arrow does not exist.

### 3.4 Obstruction D: no closure inside Plan 2

The three external regularity packages that would close the chain are:

- (P1) **BDV selection + Alt--Caffarelli flatness improvement.** As in
  `Final/GraphEntry.tex`. Supplies (G1)+(G2)+(G3) simultaneously on
  selected $U=\{u>0\}$, **not** on arbitrary $\Omega$ and **not** on
  positive interior levels.
- (P2) **A direct interior nondegeneracy + density theorem for torsion
  levels.** For $0<t<t_0$, two-sided density of $E_t$ at scale comparable
  to $r(t)$. **Not currently in the literature** for non-selected domains.
  $E_t$ is not almost-minimal in any quantified sense from $D_H+D_I$ alone.
- (P3) **A direct convexity / positive-reach upgrade of $\beta(E_t)\to 0$.**
  Fusco--Julin's $\beta^2\le CD_I$ is an integrated normal-oscillation
  index. It does not imply positive reach of $\partial^*E_t$. A theorem of
  the form "small $\beta$ + topological hypothesis $\Rightarrow$ Lipschitz
  graph" without an additional density / Caccioppoli input is not in the
  literature.

## 4. What pure Plan 2 *can* prove without graph entry

Theorem 2.1 plus FvHT centre gluing on $\rho\in[\rho_*,\rho_\delta]$
(with $\rho_\delta=1-\kappa\sqrt\delta$) plus the weighted-trace lemma of
`outer-foliation-entry-proof-attempt.md` §5 gives the following conditional
statement.

### Theorem 4.1 (conditional sharp Plan 2 closure, no graph entry)

Assume the **velocity-to-metric-derivative lemma** of
`outer-foliation-entry-proof-attempt.md` §7 eq. (7.3). Then
$$
\mathcal A(\Omega)^2\le C_n\delta_T(\Omega).
$$

The (VM) lemma reduces to:

- (VM1) the Cauchy-deficit identity (1.2) (proved);
- (VM2) Fusco--Julin's $\beta(E_\rho)^2\le C_nD_I(t(\rho))$ (proved);
- (VM3) the metric first-variation inequality
  $\big|\tfrac{d}{d\rho}\rho^{-1}(E_\rho-z(\rho))\big|_{L^1/\text{transl}}
   \le C_n\bigl(\int|V-H_z-a\cdot\nu|^2\bigr)^{1/2}$
  (smooth case proved; finite-perimeter case not yet written).

This route **bypasses** graph entry entirely. It uses only the metric
$L^1/\text{translations}$ structure on level sets. Within Plan 2, this is
the natural substitute for graph entry.

## 5. Hybrid graph-entry statement using Plan 1

The strongest graph-entry statement justifiable in the literature is the
following hybrid theorem.

### Theorem 5.1 (hybrid graph entry on a selected boundary collar)

Let $U=\{u>0\}$ be a BDV selected minimiser already in the graph regime of
`Final/GraphEntry.tex` Theorem 5.1: $\partial U$ is a $C^{1,\gamma}$
normal graph over $\partial B_1$ with $\|g_U\|_{C^{1,\gamma}}\le M_1(n,R)$.
Then there exist $t_0(n,R,\gamma)>0$ and $C(n,R,\gamma)$ such that for
every regular $t\in(0,t_0)$,
$$
\partial E_t=\{(r(t)+h_t(\theta))\theta+z_t:\theta\in\partial B_1\},
$$
$$
\|h_t\|_{C^{1,\gamma}(\partial B_1)}\le C,\qquad
\|h_t\|_{L^2(\partial B_1)}^2\le C\bigl(\eta+t^{2\gamma}\bigr),
$$
provided $D_H(t)+D_I(t)\le\eta$ and $\eta+t^{2\gamma}$ is small enough.

Sketch: the parallel-surface expansion
(`selected-boundary-layer-theorem.md` Lemma 3.1) and the Bernoulli bound
$q_-\le|\nabla u|\le q_+$ on $\partial U$ (L4.16) give that $\partial E_t$
is a $C^{1,\gamma}$ parallel perturbation of $\partial U$ for $t<t_0$.
Hence $E_t$ inherits a graph parametrisation from $U$, and the $L^2$
bound on $h_t$ follows from $D_I(t)\le\eta$ via FMP + the near-spherical
comparison $\mathcal A^2\simeq\|h\|_{L^2}^2$
(`Final/NearlySphericalClosure.tex` Lemma 4.2(iii)).

### 5.1 Caveats

- Hybrid: presupposes Plan 1 selection + GraphEntry on $\Omega$ to produce
  $U$.
- Does **not** prove graph entry for $\Omega$; only for $E_t\subset U$,
  $t<t_0$, after Plan 1.
- The relevant smallness scale for $\eta$ is $O(t_0^{2\gamma})$, not
  $\delta_T(\Omega)$. Aligning with Agent 1's outer-collar good-level
  extraction yields essentially
  `selected-boundary-layer-theorem.md` Theorem 4.1.

This is the only graph-entry statement on the table that is justifiable
end-to-end.

## 6. The missing PDE / geometry step, stated precisely

> **Missing theorem.** There exist $\eta_0(n)>0$ and a continuous
> $\omega(\cdot)$ with $\omega(0)=0$ such that for every open $\Omega$ with
> $|\Omega|=\omega_n$ and every regular torsion level $t$ satisfying
> $$
> |\Omega\setminus E_t|\le\eta\le\eta_0,\qquad
> D_H(t)+D_I(t)\le\eta,
> $$
> there are $z\in\mathbb R^n$ and $h:\partial B_1\to\mathbb R$, with
> $r=(m(t)/\omega_n)^{1/n}$, such that
> $\partial E_t=\{(r+h(\theta))\theta+z:\theta\in\partial B_1\}$
> and $\|h\|_{C^{0,1}(\partial B_1)}\le\omega(\eta)$.

This statement is **not in the literature**. Equivalent reformulations of
the gap:

1. From $\beta(E_t)^2\le C_n D_I(t)$, conclude a Lipschitz graph. Requires
   upgrading an integrated normal-oscillation bound to local Lipschitz
   graphability — needs a density input.
2. From the Serrin variance (1.2), conclude the Alt--Caffarelli flat
   regime. Requires lower nondegeneracy of $u$ at level $t$.
3. From $\mathcal A(E_t)^2\le C_n D_I(t)$, pass to Hausdorff closeness.
   Requires BDV-type density on $E_t$.

All three reduce to the same missing ingredient: a uniform density /
nondegeneracy package for torsion levels of arbitrary domains.

## 7. Conclusion

The Plan 3 target — "small $D_H+D_I$ on a near-boundary level forces $E_t$
to be a Lipschitz graph over a ball" — is **not provable as a pure Plan 2
theorem**. The obstruction is the absence of a density / nondegeneracy
package for torsion levels. The level-set identity supplies $L^1$,
normal-oscillation, and weighted-$L^2$ defects, but cannot supply the
regularity needed to convert these defects into a graph.

- **Strongest pure Plan 2 substitute:** Theorem 2.1 — $L^1/\text{transl}$
  FMP bound, FJ oscillation-index bound, weighted Serrin variance bound.
- **Strongest justifiable graph entry (hybrid Plan 1 + Plan 2):**
  Theorem 5.1 — $C^{1,\gamma}$ graph parametrisation of $\partial E_t$
  inherited from the BDV selected-minimiser collar via parallel-surface
  expansion.

**Recommendation for Plan 3.** Within Plan 2 alone, the useful follow-up
is not graph entry but the velocity-to-metric-derivative lemma
(`outer-foliation-entry-proof-attempt.md` §7 eq. (7.3)). It proves sharp
stability without ever forming a graph, using only the FJ oscillation
index and the Cauchy-deficit identity for the normal velocity $V$. That
lemma is the natural Plan 2 substitute for the graph-entry theorem, and
the rest of the foliation route already presupposes it.

If a literal graph statement is required for compatibility with
`Final/NearlySphericalClosure.tex`, the only viable route is the Plan 1
hybrid via `Final/GraphEntry.tex`. There is no shortcut through $D_H+D_I$
smallness alone.
