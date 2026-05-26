# Making Fusco–Julin Quantitative

The Fusco–Julin strong form of the quantitative isoperimetric inequality states that for every set $E$ of finite perimeter in $\mathbb R^n$ ($n\ge 2$) with $|E|=|B_\rho|$,
$$
   \beta(E)^2 \;:=\; P(E) - (n-1)\sup_{y\in\mathbb R^n}\int_E |x-y|^{-1}\,dx
   \;\le\; C_\beta(n)\bigl(P(E)-P(B_\rho)\bigr).
\tag{FJ}
$$
By the radial Gauss–Green identity this is equivalent to
$$
   \tfrac12\!\inf_{z}\!\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
   \;\le\; C_\beta(n)\,D(E),
   \qquad e_z(x):=(x-z)/|x-z|,
$$
where the infimum is attained at the radial-potential maximiser $z_E$.

The constant $C_\beta(n)$ is not made explicit by the proof in *Calc. Var. PDE* **50** (2014), 925–937. Their argument is by contradiction, uses a penalised-minimiser selection, invokes White's $\varepsilon$-regularity, and concludes with Fuglede 1989 — only the last step is constructive. The Fusco 2024 survey (arXiv:2410.20844) records this explicitly.

This note inventories realistic routes to extracting an explicit (or at least constructive) dimensional constant. Each section names the step in FJ's proof it attacks and the existing techniques most likely to feed in.

## 0. Where the non-explicitness comes from

FJ's argument has four constructive ingredients and three non-constructive ones. The non-constructive places are:

(N1) Compactness of the sequence $F_k$ of penalised minimisers ($L^1$-precompactness of bounded-perimeter sets in a fixed ball).
(N2) White's $\varepsilon$-regularity theorem extracting a $C^{1,\alpha}$ graph representation for almost-quasi-minimisers near a smooth limit.
(N3) The implicit choice of penalisation parameter $\Lambda_k$ that makes the contradiction argument fire.

Each of these has known quantitative refinements available in the literature. The strategies below correspond to making each constructive in turn.

## 1. Quantitative $\varepsilon$-regularity (Tamanini / De Philippis–Maggi)

White's theorem gives no explicit threshold or modulus. Tamanini's earlier work and the De Philippis–Maggi refinements of perimeter $\varepsilon$-regularity (e.g. *Comm. Pure Appl. Math.* **70** (2017)) make the threshold quantitative for *almost-minimisers* of perimeter with explicit deviation. The constant in the $C^{1,\alpha}$ bound is then a polynomial in the excess. Feeding this into FJ's penalised minimisers replaces the non-explicit "for $k$ large enough, $F_k$ is $C^{1,\alpha}$" by an explicit threshold.

**Status:** the quantitative excess-decay estimates are in Tamanini's lecture notes (Quaderni Univ. Lecce, 1984) and the modern Maggi text (Ch. 26). The bookkeeping has not been carried out for the FJ contradiction sequence specifically.

**What is gained.** An explicit threshold $\eta(n)>0$ such that whenever $D(E)\le\eta(n)$ and $E$ is an $\omega$-minimiser of perimeter with small $\omega$, $E$ is $C^{1,1/2}$-close to a ball. Combined with Fuglede's explicit nearly-spherical bound, this gives an explicit $C_\beta(n)$ *in the small-asymmetry regime*. The large-asymmetry regime (where $D(E)$ is order one) is handled separately by triviality + the explicit FMP 2008 Fraenkel-asymmetry constant.

## 2. Direct selection principle without contradiction

Cicalese–Leonardi 2012 (*ARMA* **206**, 617–643) replaced the FMP mass-transport argument by a *direct* selection principle in $n=2$: starting from $E$, construct a competitor $F$ via a penalised minimisation problem with explicit Lagrange multiplier, then upgrade $F$ by regularity and apply Fuglede. The argument is by direct construction, not contradiction; all constants are traceable.

In dimension $n\ge 3$ the Cicalese–Leonardi route was extended by Acerbi–Fusco–Morini 2013 (*Comm. Math. Phys.* **322**) for the Fraenkel form. The oscillation-form (i.e. strong-form FJ) version has not been written down explicitly but the same scheme should apply: penalise the deviation of $\beta(E)^2$ from $0$ instead of the Fraenkel asymmetry, and follow through.

**What is gained.** A direct constructive proof of (FJ) with constants traceable to: a Lagrange multiplier from the penalised functional + Tamanini-type excess decay + Fuglede's $W^{1,2}$ Sobolev constant on the sphere. Each is dimensional and computable.

**Likely bottleneck.** The Lagrange multiplier choice. Cicalese–Leonardi pick $\Lambda$ implicitly via a continuity argument; making this explicit requires either a fixed-point estimate or a continuation method.

## 3. Mass-transport route via Figalli–Maggi–Pratelli

Figalli–Maggi–Pratelli 2010 (*Invent. Math.* **182**, 167–211) gave an optimal-transport proof of the Fraenkel form with explicit constants. The transport map $T\colon B_\rho \to E$ (Brenier) satisfies $\det DT = |E|/|B_\rho|$ and the boundary normal information is encoded in $DT$ on $\partial B_\rho$. Specifically, the L² oscillation $\int |\nu_E - e_z|^2$ pulled back to $\partial B_\rho$ is, up to lower-order terms, the $L^2$ norm of the *tangential* derivative of $T-\mathrm{id}$.

**Idea.** Combine the Figalli–Maggi–Pratelli L¹ control of $T-\mathrm{id}$ with a boundary trace inequality to get L² control of the tangential derivative of $T-\mathrm{id}$ on $\partial B_\rho$, translating into the FJ L² normal oscillation.

**Likely obstacle.** Brenier maps need not be smooth up to the boundary for general finite-perimeter $E$. The Caffarelli regularity theory gives $C^{2,\alpha}$ regularity only under convexity hypotheses. So this route would either restrict to convex $E$ or use a regularisation (which reintroduces a non-explicit step).

**What is gained on the convex / John class.** A fully explicit dimensional constant $C_\beta(n)$ on convex sets via Caffarelli regularity + FMP transport. This may already be enough for the FK application: torsion superlevel sets of the bounded core are not generally convex, but they are quasi-convex on good levels (uniform interior ball condition modulo deficit-sized defect).

## 4. Restricted-class explicit version (immediate dividend)

On the class of *Lipschitz nearly-spherical sets* $\partial E = \{(1+\varphi(\theta))\theta : \theta\in S^{n-1}\}$ with $\|\varphi\|_{W^{1,\infty}}\le\delta_0$ small, Fuglede 1989 already gives an explicit bound: there is $C_F(n)>0$ depending only on $n$ such that
$$
   \beta(E)^2 \;\le\; C_F(n)\bigl(P(E)-P(B_\rho)\bigr),
   \qquad C_F(n) \;=\; \frac{n+2}{2(n-1)} + O(\delta_0).
$$
(The sharp constant $C_F(n) = (n+2)/(2(n-1))$ comes from the spherical-harmonic spectral gap on modes $\ell\ge 2$, with the $\ell=2$ mode saturating.) **Explicit.**

**Action item.** A genuinely useful immediate output is to write a clean restricted-class quantitative FJ statement:
$$
   \beta(E)^2 \le C_F(n)\bigl(P(E)-P(B_\rho)\bigr)
   \qquad \text{whenever $\partial E$ is a $W^{1,\infty}$ graph over $\partial B_\rho$ with norm $\le\delta_0(n)$}.
$$
This is verifiable by hand from Fuglede's proof + one Taylor expansion. The threshold $\delta_0(n)$ and the constant $C_F(n)$ are both explicit. For the FK paper, this is the regime on good levels far from the bad set, and could be exploited directly.

## 5. Spectral / mode-by-mode upgrade

Fuglede's bound on nearly-spherical sets is essentially a spectral gap statement on $L^2(S^{n-1})$: after removing the constant ($\ell=0$, volume) and dipole ($\ell=1$, barycentre) modes, the smallest eigenvalue of the relevant operator on the remaining modes gives the constant. **The spectral gap is explicit**: $\lambda_2 = 2n+2$ for the Laplacian on $S^{n-1}$, and the spectral gap of the Fuglede operator is computable directly.

This is just a reformulation of (4) but it points to a generalisation: for non-spherical reference sets (e.g. ellipsoids, Wulff shapes), spectral-gap estimates give explicit constants in the corresponding nearly-spherical regime. Less directly useful for FK, but a clean way to think about (FJ) in the small-asymmetry case.

## 6. Iterated regularisation tower

Acerbi–Fusco–Morini use one round of penalised regularisation. Brasco–De Philippis–Velichkov in their Faber–Krahn paper (*Duke Math. J.* **164**, 1777–1831) use a similar two-step scheme. **Idea.** Iterate: at each step, the penalised minimiser is closer to a ball; quantify the per-step gain explicitly. The resulting constant is a geometric series of explicit dimensional constants.

**Likely difficulty.** Each iteration step requires a partial $C^{1,\alpha}$ regularity bound (Step 1 above). The per-step gain factor in the symmetric difference is dimensional and can be computed (typically $1/2$ or similar in the L¹ scale). The challenge is propagating from L¹ control to L² normal control across iterations, which would require either a uniform interior-ball condition or the Fuglede regime.

## 7. n = 2 plane case

In the plane, Bianchini–Croce–Henrot (arXiv:1101.0169) and Cicalese–Leonardi 2012 give explicit Fraenkel constants. Indyk and others have explicit constants for the planar oscillation form in the convex case. **A fully explicit planar FJ constant is plausibly within reach** and would be a clean stress-test of the program. The FK constant $c_{FK}(2, R, \rho_*)$ would then be fully explicit on planar domains.

## 8. Direct sharp Fuglede + truncation reduction

A possibly cleaner global scheme:

1. **Bounded reduction.** Given $E$ with $D(E)\le \eta_0$ small, replace $E$ by a bounded representative $E'$ with $E'\subset B_R$ and $D(E')\le 2D(E)$ at the cost of an explicit dimensional constant (this is in the manuscript already via the Plan 1 bounded reduction).
2. **John / quasi-convexity reduction.** Show that small $D(E')$ forces $E'$ to be quasi-convex (e.g. uniform interior ball condition with deficit-sized defect). Quantitative versions of such reductions are in the literature for the Fraenkel form (e.g. Cinti–Fusco–Ottuso).
3. **Fuglede on the quasi-convex class.** On the quasi-convex class with explicit modulus, the boundary is a Lipschitz graph over $\partial B_\rho$ with explicit norm; Fuglede applies directly with explicit constant.

The advantage of this scheme over (1)+(4) is that it avoids the implicit selection-principle multiplier entirely. The disadvantage is that step 2 is itself a non-trivial quantitative regularity statement; it may end up being a re-statement of FJ.

## 9. Quantitative Fuglede beyond the Lipschitz threshold

Fuglede's nearly-spherical bound is proved by direct Taylor expansion. The threshold $\delta_0(n)$ is needed only for the higher-order terms; the leading-order $W^{1,2}$ Sobolev bound is unconditional. One can ask: is there an extension of Fuglede's bound to general $C^{1,\alpha}$ graphs with explicit dependence on $\alpha$ and the $C^{1,\alpha}$ norm? Pieces of this are in the literature (Cinti–Pratelli, Magnanini–Poggesi). A clean quantitative version would extend the regime where the "explicit Fuglede + reduction" scheme of §8 applies.

## Recommended priority for the FK paper

For the present quantitative Faber–Krahn project, the cleanest dividend is **§4 + §1**:

- **§4** gives an immediate explicit constant $C_\beta(n) = (n+2)/(2(n-1)) + o(1)$ on $W^{1,\infty}$-nearly-spherical sets with small norm.
- **§1** (quantitative $\varepsilon$-regularity) gives the threshold $\eta(n,R,\rho_*)$ under which torsion superlevel sets are $W^{1,\infty}$-nearly spherical with norm $\le \delta_0(n)$.

Combined, these would convert the "FJ used as black box with non-explicit constant" import in the manuscript into a "FJ used in explicit form on good levels, FMP fallback on the bad set". The dependency certificate would then list **no** non-explicit constants. This is the smallest patch that delivers full explicitness.

The wider question — fully explicit (FJ) on all finite-perimeter sets — is open and corresponds to making Cicalese–Leonardi / Acerbi–Fusco–Morini selection principles fully quantitative in $n\ge 3$.

## Pointers

- Fusco–Julin, *Calc. Var. PDE* **50** (2014), arXiv:1111.4866 — the original strong-form bound.
- Fusco survey, arXiv:2410.20844 — confirms non-explicitness and surveys the explicit-constant methods.
- Fuglede, *Trans. AMS* **314** (1989) — explicit nearly-spherical bound.
- Cicalese–Leonardi, *ARMA* **206** (2012) — selection principle for the Fraenkel form, $n=2$ explicit.
- Acerbi–Fusco–Morini, *Comm. Math. Phys.* **322** (2013) — second-variation reproof in $n\ge 3$.
- Figalli–Maggi–Pratelli, *Invent. Math.* **182** (2010) — mass-transport explicit constants for the Fraenkel form.
- Tamanini, Quaderni Univ. Lecce (1984); Maggi, *Sets of Finite Perimeter*, Ch. 26 — quantitative $\varepsilon$-regularity for perimeter almost-minimisers.
- De Philippis–Maggi, *Comm. Pure Appl. Math.* **70** (2017) — modern quantitative $\varepsilon$-regularity.
- Cinti–Fusco–Ottuso — quantitative reductions for the Fraenkel form.
- Magnanini–Poggesi — weighted-Hessian / Serrin-type quantitative stability.
- Brasco–De Philippis 2017 survey — overview of quantitative isoperimetric methods.
