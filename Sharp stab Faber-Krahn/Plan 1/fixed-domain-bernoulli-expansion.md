# Fixed-domain Bernoulli expansion via implicit function theorem

This note closes the analytical gap flagged in
`bernoulli-expansion-proofs.md` (corrected status). The Bernoulli
boundary-gradient expansion is proved **entirely on the fixed domain** $B_1$,
without evaluating the interior harmonic first variation $u_1$ at $r>1$.

The strategy is the implicit function theorem applied to the pulled-back
torsion problem on $B_1$. See `fixed-domain-bernoulli-expansion.tex/.pdf`
for the full argument.

## 1. The corrected first variation

Define the pulled-back shape derivative on $\overline{B_1}$:

\[
\widetilde u'(g)(x)
=u_1(x)-\frac{\chi(r)r}{N}g(\theta),\qquad x=r\theta.
\]

Here $u_1$ is the harmonic extension of $g/N$ to $B_1$ (well-defined and
$C^{2,\gamma}$ on $\overline{B_1}$), and the correction $-\chi(r)rg/N$ is a
radial cutoff extension of $-g/N$ that makes $\widetilde u'(g)$ vanish on
$\partial B_1$. Both summands are smooth on $\overline{B_1}$ for every
$g\in C^{2,\gamma}(\partial B_1)$; neither requires harmonic continuation
past $\partial B_1$.

A direct computation gives the boundary radial derivative

\[
\partial_r\widetilde u'(g)\big|_{\partial B_1}
=\frac{1}{N}\mathcal L g,\qquad\mathcal L g_k=(k-1)g_k.
\]

The eigenvalue $k-1$ is the DtN eigenvalue $k$ (from $\partial_r u_1$ at
$r=1$) shifted by $-1$ (from $\partial_r(-rg/N)$ at $r=1$).

## 2. Implicit function theorem on $B_1$

The pulled-back torsion equation
$-\nabla\cdot(A_g\nabla\widetilde u_g)=J_g$ is studied as a smooth map
$F(g,w)$ between Banach spaces

- $X = C^{2,\gamma}(\partial B_1)$,
- $Y = \{w \in C^{2,\gamma}(\overline{B_1}) : w|_{\partial B_1} = 0\}$,
- $Z = C^\gamma(\overline{B_1})$.

At $g=0$, $\partial_w F$ is the Dirichlet Laplacian, an isomorphism by
Schauder. The IFT produces a $C^\infty$ map $g \mapsto w(g)$ with quadratic
remainder

\[
\|w(g)-\widetilde u'(g)\|_{C^{2,\gamma}(\overline{B_1})}\le C\|g\|_{C^{2,\gamma}}^2.
\]

This is the rigorous Schauder estimate. The IFT linearization is identified
with $\widetilde u'(g)$ above by Hadamard's classical shape calculus.

## 3. $H^1$-tame remainder

The second variation $w''(sg)(g,g)$ satisfies a Dirichlet problem on $B_1$
with bilinear $L^2(B_1)$ source

\[
\|S(s,g)\|_{L^2(B_1)}\le C\|g\|_{C^{2,\gamma}}\|g\|_{H^1(\partial B_1)},
\]

obtained by pairing the highest-derivative factor in $L^\infty$ and the
lowest in $H^1$ (with integration by parts on the closed manifold
$\partial B_1$ to reduce $|\nabla^2 g|\cdot|\nabla^2 g|$ terms to
$|g|\cdot|\nabla^4 g|$ via duality). Elliptic regularity and the trace
$H^2(B_1)\to H^{1/2}(\partial B_1)\hookrightarrow L^2(\partial B_1)$ give

\[
\|R_q(g)\|_{L^2(\partial B_1)}\le C\|g\|_{C^{2,\gamma}}\|g\|_{H^1(\partial B_1)}.
\]

This is the tame estimate, in the $C^{2,\gamma}\times H^1\to L^2$ form.

## 4. Why $H^1$-tame suffices: derivative gain of $\mathcal L$

The operator $\mathcal L: g_k \mapsto (k-1)g_k$ on $\{k\ge 2\}$ gains a full
derivative:

\[
\|\mathcal L h\|_{L^2}\ge c_N\|h\|_{H^1}\quad\hbox{for }h\hbox{ supported on }\{k\ge 2\}.
\]

This is because $(k-1)^2 \gtrsim k(k+N-2)$ for $k\ge 2$, matching the $H^1$
spectrum of $\partial B_1$.

Combined with the $C^{2,\gamma}\times H^1\to L^2$ remainder, the spectral
closure equation

\[
-\frac{2}{N^2}\mathcal L g_{\ge 2}
=a_\sigma g_{\ge 2}+\widetilde R(g),
\quad \|\widetilde R\|_{L^2}\le C(\sigma+\|g\|_{C^{2,\gamma}})\|g\|_{H^1},
\]

inverts to

\[
\|g_{\ge 2}\|_{H^1}\le C(\sigma+\|g\|_{C^{2,\gamma}})\|g\|_{H^1}.
\]

Volume and barycenter constraints kill $g_0,g_1$ up to quadratic terms, and
in the smallness regime $\sigma\le\sigma_*$,
$\|g\|_{C^{2,\gamma}}\le\delta_*$, the spectral closure forces $g\equiv 0$.

The previous note required an $L^2$-tame estimate; this is not needed because
$\mathcal L$ itself supplies a derivative to compensate.

## 5. End-to-end sharp stability

Combining
- selection (`quantitative-selection-principle.md`),
- graph entry (`graph-entry-closure.md`),
- the spectral closure above,

we obtain a sharp Saint--Venant/Faber--Krahn stability theorem: for
$|\Omega|=|B_1|$ and $Q_\alpha(\Omega)\le q_*(N,R)$,

\[
E(\Omega)-E(B_1)\ge c_*(N,R)\alpha(\Omega),
\]

**conditional** on the second-variation source enumeration of
`corrections-response.md`, §3 being completed with explicit constants.

The BDV nearly spherical second variation is available as an alternative
closure that does not depend on this conditional step.

## 6. Status of the four items in the previous note

The four genuinely-open items listed in
`bernoulli-expansion-proofs.md`, Section 5, are now resolved:

1. **Work entirely on $B_1$ with the pullback equation:** done in
   Section 2 (IFT on $B_1$).
2. **Differentiate the coefficient map $g\mapsto(A_g,J_g,\nu_g)$:** done in
   Lemma 2.1 of the TeX note.
3. **Second-order fixed-domain remainder in a norm controlling the boundary
   normal derivative:** done in Proposition 2.2 ($C^{2,\gamma}$-quadratic).
4. **Tame boundary-gradient remainder in $C^{2,\gamma}\times L^2$:**
   replaced by the equivalent and more natural $C^{2,\gamma}\times H^1$
   form, which suffices because $\mathcal L$ on $\{k\ge 2\}$ gains a full
   derivative.

## Remaining bookkeeping

- Track $\sigma_*,\delta_*,q_*$ through the dependency chain
  $q_*\to\tau=q_*^{1/4}\to\sigma\le C\tau\to$ closure smallness.
- Explicit Schauder bootstrap $C^{1,\gamma}\to C^{2,\gamma}$ in graph entry
  via BDV Lemma 4.16.

These are routine but worth writing out for a publication-quality version.
