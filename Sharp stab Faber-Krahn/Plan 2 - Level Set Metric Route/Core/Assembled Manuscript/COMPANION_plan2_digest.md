# Plan 2 in plain English

*A companion to the second proof. Reading time ≈ 30 minutes. The aim is to convey what the proof is doing and why, not to replicate any estimate.*

---

## 0. What is the problem?

The **Faber–Krahn inequality** says: among all open sets in $\mathbb{R}^n$ of a given volume, the ball minimises the first Dirichlet eigenvalue of the Laplacian:
$$
\lambda_1(\Omega) \;\ge\; \lambda_1(B^*),
$$
where $B^*$ is the ball of the same volume as $\Omega$. The classical proof (Faber 1923, Krahn 1925) uses symmetrisation.

We care about **how rigid this is**. If $\Omega$ is only "a little" non-ball — quantified by Fraenkel asymmetry
$$
\mathcal{A}(\Omega) \;=\; \inf_{x \in \mathbb{R}^n} \frac{|\Omega \triangle B^*(x)|}{|\Omega|},
$$
the symmetric difference between $\Omega$ and its best-matching ball — then $\lambda_1$ should be only a little above $\lambda_1(B^*)$. The **sharp quantitative Faber–Krahn inequality** says exactly that:
$$
\delta_{FK}(\Omega) \;\ge\; c(n)\,\mathcal{A}(\Omega)^2,
$$
where $\delta_{FK}(\Omega) = (|\Omega|/\omega_n)^{2/n}(\lambda_1(\Omega) - \lambda_1(B^*))$ is the normalised eigenvalue gap. The exponent $2$ is sharp (an ellipsoid with one axis stretched by $\varepsilon$ gives $\mathcal{A} \sim \varepsilon$ and $\delta_{FK} \sim \varepsilon^2$, so you can't ask for any smaller exponent on the right). Proving this was the conjecture closed by Brasco–De Philippis–Velichkov in 2015. Plan 1 of this manuscript polishes their argument; Plan 2 gives a *different* proof.

### Two simplifications before we start

**Trade $\lambda_1$ for the torsion function.** It is much easier to work with the **torsion function** $u_\Omega$, the unique solution of
$$
-\Delta u = 1 \text{ in } \Omega, \qquad u = 0 \text{ on } \partial \Omega.
$$
The **torsional rigidity** is $T(\Omega) = \int_\Omega u$. There is a Saint–Venant inequality $T(\Omega) \le T(B^*)$ (same direction as Faber–Krahn after sign) and a corresponding deficit $\delta_T(\Omega)$.

The two stability problems are **not independent**. Kohler–Jobin (1978) proved
$$
T(\Omega)\,\lambda_1(\Omega)^{(n+2)/2} \;\ge\; T(B^*)\,\lambda_1(B^*)^{(n+2)/2},
$$
and a small computation turns this into:
$$
\boxed{\text{sharp $\delta_T$-stability} \;\Longrightarrow\; \text{sharp $\delta_{FK}$-stability,}}
$$
with an explicit dimensional constant. **So our entire job reduces to proving** $\delta_T(\Omega) \ge c(n) \, \mathcal{A}(\Omega)^2$. That is the target. Plan 1 and Plan 2 both produce this same input.

**Reduce to bounded $\Omega$.** A separate lemma (already in the BDV paper, Lemma 5.3) shows that for the purposes of stability you may assume $\Omega \subset B_R$ for some explicit $R = R(n)$. The constants in the proof are allowed to depend on $R$; bounded reduction at the end removes that dependence. This is just bookkeeping — Plans 1 and 2 use the same bookkeeping.

So: **the problem is** $\delta_T(\Omega) \ge c(n, R)\,\mathcal{A}(\Omega)^2$ **for bounded $\Omega$**.

---

## 1. The big idea of Plan 2

Plan 1 (BDV) is a **selection** argument: find one near-extremal $\Omega$, prove it is smooth enough to be a graph over the unit sphere, then quote the *nearly spherical theorem* of Fuglede that says a near-ball that's actually a graph satisfies the inequality directly.

Plan 2 is a **foliation** argument. Instead of looking at $\Omega$ as a single shape, slice $u_\Omega$ into its superlevel sets
$$
E_\rho \;:=\; \{u_\Omega > t(\rho)\}, \qquad |E_\rho| = \omega_n \rho^n.
$$
As $\rho$ runs from $0$ (top of $u$) to $1$ (whole $\Omega$), the sets $E_\rho$ swell from a point up to $\Omega$. Each is a finite-perimeter set. By Talenti's classical theorem, the rearrangement of $u_\Omega$ matches the rearrangement of the torsion function of $B^*$, so the *volumes* behave correctly; the question is how the *shapes* behave.

The strategy:

> **Watch every level set, control it using Fusco–Julin isoperimetric stability, integrate against a clever weight, and read off control of $\mathcal{A}(\Omega)$ at the end.**

Six things have to happen in sequence:

1. **The Saint–Venant deficit must be expressible as a $\rho$-integral** over the foliation. (level-set deficit identity)
2. **The foliation must be a well-defined path in some metric space of shapes**, so that we can talk about its "speed" and its "distance from the unit ball". (metric framework)
3. **Each level set must have a centre** with respect to which we can quantify how non-ball it is. (Fusco–Julin centres)
4. **A geometric estimate (the radial trace lemma) must convert "distance from ball" to defects the level set already controls.** (oriented $L^1$ radial trace)
5. **Integrating along the foliation must produce a single special radius $\widehat\rho$ where the rescaled level set $F_{\widehat\rho}$ is genuinely close to the unit ball.** (weighted metric trace)
6. **That control on $F_{\widehat\rho}$ must transfer back to $\Omega$ itself**, with the boundary layer $\Omega \setminus E_{\widehat\rho}$ behaving tamely. (boundary-layer transfer)

Each is a separate idea, each is necessary, and none is conditional. Let me explain them.

---

## 2. Step 1 — The level-set deficit identity

This is the **foundation**. The claim is that there is a non-negative weight $w(\rho)$ on $(0,1)$ and two non-negative defects $D_H(t)$, $D_I(t)$ such that:
$$
\delta_T(\Omega) \;\simeq\; \int_{0}^{1} \bigl(D_H(t(\rho)) + D_I(t(\rho))\bigr)\, w(\rho)\, d\rho.
$$
The deficit, an a-priori opaque single number, is **exactly** the integral of two pointwise non-negative defects along the foliation. That is the key move: a single global inequality has become an integrated identity.

### What do $D_H$ and $D_I$ measure?

Both come from rewriting Saint–Venant's proof one level at a time. Define
$$
\alpha(t) = \int_{\partial^* E_t} \frac{1}{|\nabla u|}\, d\mathcal{H}^{n-1},
\qquad
\beta(t) = \int_{\partial^* E_t} |\nabla u|\, d\mathcal{H}^{n-1}.
$$
Both are integrals over the boundary of the superlevel set, with reciprocal and direct $|\nabla u|$ weights respectively. By Cauchy–Schwarz, $\alpha(t)\beta(t) \ge P(E_t)^2$, with equality iff $|\nabla u|$ is constant on $\partial^* E_t$.

- $\boxed{D_H(t) = \alpha(t)\beta(t) - P(E_t)^2 \;\ge\; 0}$ — measures **oscillation of $|\nabla u|$ on the level set**. Zero when $|\nabla u|$ is constant along $\partial^* E_t$. ($H$ for "Hessian-like" / horizontal.)
- $\boxed{D_I(t) = P(E_t)^2 - c_n |E_t|^{2-2/n} \;\ge\; 0}$ — the **squared isoperimetric deficit** of the level set. Zero when $E_t$ is a ball. ($I$ for "Isoperimetric".)

So the identity says: the Saint–Venant deficit is the integral over levels of (gradient oscillation on the level) + (how far the level is from a ball), weighted by something explicit.

### Why this is true

Talenti's rearrangement comparison from 1976 is a single inequality $T(\Omega) \le T(B^*)$. Inside Talenti's proof there are **two** Cauchy–Schwarz-like steps — one giving an inequality on level perimeters (the isoperimetric one) and one on gradient integrals (the Cauchy–Schwarz one). Each contributes a non-negative defect at every level. Plan 2's first move is to refuse to throw these defects away. Saint–Venant becomes an *equality* in which the two defects sum, integrated against an explicit weight, to give $\delta_T$.

This is in the spirit of Nicola–Tilli's recent work on the short-time Fourier Faber–Krahn problem, where the same "level-set integral identity" idea appeared in a different setting. Plan 2 imports it into the Dirichlet Saint–Venant world.

### Why it matters

Once you have an identity like this, **two non-negative summands on the right that sum to something small** means that **both summands are integrally small**:
- $\int D_H(t(\rho)) w(\rho)\, d\rho$ is small.
- $\int D_I(t(\rho)) w(\rho)\, d\rho$ is small.

The first will be used to control the *speed* of the foliation in the metric space of shapes (Step 2/4). The second will be used to control how *ball-shaped* each level is (Step 3).

---

## 3. Step 2 — The metric framework

We want to think of the family $\{E_\rho\}_{\rho \in [0,1]}$ as a **path** in a space of shapes. Then "speed" and "distance from a target" make sense, and standard metric-space arc-length tools apply.

### The space $\mathcal{X}$

Define $\mathcal{X}$ to be the space of finite-perimeter sets in $\mathbb{R}^n$ *modulo translations*, with distance
$$
d_{\mathcal{X}}([A], [B]) \;=\; \inf_{v \in \mathbb{R}^n} |A \triangle (B+v)|.
$$
Two sets are at distance zero iff they're translates of one another. The completion of this metric is essentially a Polish space ("nice" enough that AGS-style metric arc-length theory works).

### The path

Now consider the **rescaled** foliation
$$
F_\rho \;:=\; \rho^{-1} E_\rho.
$$
Why rescale? Because $|E_\rho| = \omega_n \rho^n$, so $|F_\rho| = \omega_n = |B_1|$ for every $\rho$. All the $F_\rho$ live on the **same volume scale**, so it's meaningful to compare their distance to the unit ball $B_1$.

Plan 2 proves two things about this path:

- **It is absolutely continuous.** $\rho \mapsto [F_\rho]$ has finite metric derivative $|\dot F_\rho|_{\mathcal{X}}$ a.e., in the Ambrosio–Gigli–Savaré sense.
- **The metric speed is bounded by something geometric.** Roughly, $|\dot F_\rho|_{\mathcal{X}}$ is controlled by the $L^1$ norm of the normal velocity $V_\rho = -t'(\rho)/|\nabla u|$ on $\partial^* E_\rho$, after the rescaling.

This step is *almost smooth-flow geometry*. If $\Omega$ were smooth and $u_\Omega$ were Morse, the level sets would move with normal velocity $V_\rho$ and a one-line classical first-variation argument would give the bound. The work is to make this rigorous when **$\Omega$ is only of finite perimeter** — no smoothness, no Lipschitz assumption on the boundary. That involves mollifying $u_\Omega$, applying the smooth identity to the mollified levels, and passing to the limit using Reshetnyak lower-semicontinuity. The technical care is non-trivial but the **idea** is just: the foliation is a Lipschitz path, and the right notion of "Lipschitz" is the AGS metric derivative.

---

## 4. Step 3 — Fusco–Julin centres and the oriented radial trace

This is the heart of Plan 2. We need to convert isoperimetric defect into something that talks about $F_\rho$'s distance from the unit ball.

### The Fusco–Julin inequality

The classical Fuglede–Fusco–Maggi–Pratelli inequality (2008) says: for any set $E$ with the volume of a ball,
$$
\mathcal{A}(E)^2 \;\le\; C(n)\, \mathcal{D}(E),
$$
where $\mathcal{D}(E) = (P(E) - P(B^*))/P(B^*)$ is the (linear) isoperimetric deficit. The exponent 2 is sharp.

Fusco–Julin (2014) strengthened this to a *two-term* inequality:
$$
\mathcal{A}(E)^2 \;+\; \beta(E)^2 \;\le\; C(n)\, \mathcal{D}(E),
$$
where $\beta(E)$ is a **normal-oscillation index**:
$$
\beta(E)^2 \;=\; \inf_{z \in \mathbb{R}^n}\, \fint_{\partial^* E} \Bigl|\nu_E(x) - \frac{x-z}{|x-z|}\Bigr|^2\, d\mathcal{H}^{n-1}.
$$
For the optimal centre $z = z(E)$, $\beta(E)$ measures how much the outer normal $\nu_E$ differs from the radial direction pointing away from $z$ — i.e., how much $\partial^* E$ fails to be a sphere around $z$.

Both terms — symmetric difference *and* normal oscillation — are controlled by the (single) isoperimetric deficit. **This is what makes a foliation argument possible**: at every level, Fusco–Julin gives us two pieces of geometric information, and we need both.

### The Fusco–Julin centres

For each $\rho$ where $D_I(t(\rho))$ is small enough (we'll call these **good levels**), pick a centre $z_\rho$ that almost realises the FJ infimum. We need this choice to depend on $\rho$ in a **measurable** way; this is a standard Federer-style Borel selection. The canonical concrete choice is the **bulk centroid** of $E_\rho$ — it's automatically Borel in $\rho$ and (with a small Wave 3 argument) it sits well inside $E_\rho$, which is exactly the analytic input we need below.

So now we have, for a.e. good $\rho$, a centre $z_\rho \in \mathbb{R}^n$, plus controls:
- (asymmetry) $|E_\rho \triangle B_\rho(z_\rho)| \le \rho^n \cdot O(\sqrt{D_I(t(\rho))})$,
- (oscillation) $\int_{\partial^* E_\rho} |\nu_\rho - (x - z_\rho)/|x - z_\rho||^2\, d\mathcal{H}^{n-1} \le O(D_I(t(\rho)))$.

(Constants are dimensional / depend on the confining radius $R$ and the foliation parameter $\rho_*$; they don't depend on $\delta_T$.)

### The oriented $L^1$ radial trace lemma

This is the most delicate step and the **load-bearing original lemma** of Plan 2. It says:

$$
\boxed{
\int_{\partial^* E_\rho} \Bigl|\frac{|x - z_\rho|}{\rho} - 1\Bigr|\, d\mathcal{H}^{n-1}
\;\le\; C\Bigl(\underbrace{|E_\rho \triangle B_\rho(z_\rho)|}_{\text{symmetric diff}} \;+\; \underbrace{\int_{\partial^* E_\rho} \bigl|\nu_\rho - \tfrac{x-z_\rho}{|x-z_\rho|}\bigr|^2\, d\mathcal{H}^{n-1}}_{\text{normal oscillation}} \Bigr).
}
$$

In words: the **average distance of $\partial^* E_\rho$ from the sphere of radius $\rho$ around $z_\rho$** is controlled by the FJ defects.

#### The intuition

Imagine $\partial^* E_\rho$ as a closed surface near the sphere of radius $\rho$ centered at $z_\rho$. The integrand $||x-z_\rho|/\rho - 1|$ measures, at each point of $\partial^* E_\rho$, how far that point's distance to $z_\rho$ deviates from $\rho$. The left side is the total "radial deviation" of the surface.

We control it by **applying the divergence theorem to the radial vector field**
$$
X(x) \;=\; \Bigl|\frac{|x - z_\rho|}{\rho} - 1\Bigr| \cdot \frac{x - z_\rho}{|x - z_\rho|}.
$$
Outside the sphere $|x-z_\rho|=\rho$ this points outward radially; inside, inward radially. The divergence theorem then says:
$$
\int_{\partial^* E_\rho} X \cdot \nu_\rho \, d\mathcal{H}^{n-1} \;=\; \int_{E_\rho} \mathrm{div}\, X.
$$
The right side, after some bookkeeping, expands into a *signed* version of $|E_\rho \triangle B_\rho(z_\rho)|$ plus error. The left side bounds the radial trace **only if you replace $X \cdot \nu_\rho$ by $|X|$**, which costs an oscillation term $|\nu_\rho - (x-z_\rho)/|x-z_\rho||$. Squaring gives the second term on the right of the lemma. Putting both together yields the inequality.

#### Why this is delicate

1. The vector field $X$ has a **singularity at $z_\rho$** (the factor $(x-z_\rho)/|x-z_\rho|$). You can't apply the divergence theorem naively — you must truncate $X$ near $z_\rho$, apply the theorem to a smooth truncation, and pass to the limit. This is the *truncation argument*, which the preliminaries (Step 0) made rigorous as a separate lemma valid for finite-perimeter sets.
2. For the truncation to be free, we need $z_\rho$ to be **interior** to $E_\rho$ (and to the comparison ball), at a uniform positive distance. This is exactly why we chose the bulk centroid: a Wave 3 argument shows $B(z_\rho, \rho_*/4) \subset E_\rho$ on good levels. Then the symmetric-difference region $E_\rho \triangle B_\rho(z_\rho)$ stays away from $z_\rho$, and the truncation limit is *trivial* (not just convergent).
3. The lemma is *linear* in the radial deviation (left side) and combines a linear term and a *squared* oscillation term on the right. This linear-vs-squared mismatch is what makes the final rate sharp instead of degraded.

#### Why this is the load-bearing step

Earlier attempts at Plan 2 tried to use $L^2$ radial traces (square the left side too) and *ray-slicing* arguments (decompose the boundary by rays from $z_\rho$). Both failed. The Wave 2 audits flagged the $L^2$ version as inconsistent with the FJ scaling, and ray-slicing doesn't work for finite-perimeter sets. **The $L^1$ oriented trace via the divergence theorem with truncation is what saves Plan 2**. The audit (Agent 16) explicitly verifies that the named vector field $X$, the truncation argument, and the finite-perimeter divergence theorem are all present and used.

---

## 5. Step 4 — The weighted metric trace

We now have, for each good level:
- a centre $z_\rho$,
- a radial trace estimate (Step 3),
- the level-set identity for $\delta_T$ (Step 1),
- the metric derivative bound for the path $F_\rho$ (Step 2).

We want to put them together to find **one specific $\widehat\rho$ near 1** such that $F_{\widehat\rho}$ is close to the unit ball $B_1$ in $\mathcal{X}$.

### The integrated action inequality

The first half of Step 4 chains the estimates above. The radial trace, after rescaling, turns the FJ pair (asymmetry + oscillation) into a single bound on $d_{\mathcal{X}}([F_\rho], [B_1])^2$ at each good level. Combining with the metric derivative bound $|\dot F_\rho|_{\mathcal{X}}$ (Step 2, controlled by $D_H$ via the normal-velocity formula), and integrating against the natural weight $\mu(d\rho) = -t'(\rho)\, d\rho$, we get
$$
\int_{[\rho_*, 1]} \Bigl( d_{\mathcal{X}}([F_\rho], [B_1])^2 + |\dot F_\rho|_{\mathcal{X}}^2 \Bigr)\, \mu(d\rho)
\;\le\; C(n, R, \rho_*)\, \delta_T(\Omega).
$$
**This is the metric-space avatar of the level-set deficit identity.** The integrated "action" of the path $F_\rho$ (distance to target + speed squared, weighted) is controlled by the deficit.

### Good levels vs. bad levels

A subtle point: Fusco–Julin only gives information on levels where $D_I$ is *small*. On "bad" levels (where $D_I$ is above some fixed threshold), we have no centre, no radial trace, nothing. **Markov's inequality saves the day**: the bad-level set has weighted measure at most $\delta_T / \text{threshold}$, so it's a tiny piece of $[\rho_*, 1]$ when $\delta_T$ is small.

A separate good/bad decomposition is needed for the levels where the **profile slope** $-t'(\rho)$ is small. There the weight $\mu$ is too small for the integrated bound to be useful. Talenti's classical *bad-set Lebesgue estimate* gives that this bad-$\mu$ region also has Lebesgue measure $O(\delta_T)$, and a uniform Lipschitz bound on the path absorbs it without rate loss.

After both decompositions, the integrated action holds on the *whole* interval $[\rho_*, 1]$, with the bad-set contributions absorbed.

### The abstract metric trace argument

We have: an absolutely continuous path $\rho \mapsto [F_\rho]$ in the metric space $\mathcal{X}$, an integrated bound on the path's distance to the target $B_1$ plus its speed squared, and we want to extract **one good radius** $\widehat\rho$ where the path *is* near $B_1$.

This is a classical arc-length argument. Heuristically: if the action integral $\int (d^2 + |\dot F|^2)\,d\mu \le \varepsilon$ over a window of weighted length $L^*$, then by averaging there is some $\widehat\rho$ in the window where $d([F_{\widehat\rho}], [B_1])^2 \le \varepsilon / L^*$ (Markov in $d^2$) and the "kinetic transport" within the window is bounded by $L^* \cdot$(speed term).

The critical choice — and this is exactly what the Plan 2 audit (B1) caught and the repair fixed — is the **window scale**:
$$
\widehat\rho \in [\rho_\delta - c_0\sqrt{\delta_T}, \rho_\delta], \qquad \rho_\delta = 1 - \kappa\sqrt{\delta_T}.
$$
The window has length $c_0 \sqrt{\delta_T}$, not a fixed $O(1)$ length. With this scale the boundary layer $\Omega \setminus E_{\widehat\rho}$ will be $O(\sqrt{\delta_T})$ in measure (Step 5). The original draft had an $O(1)$ window, which would have *broken* Step 5; the repair fixed it.

The output:
$$
\boxed{
d_{\mathcal{X}}([F_{\widehat\rho}], [B_1])^2 \;\le\; C_*(n, R, \rho_*)\, \delta_T(\Omega).
}
$$

In words: there is a level $\widehat\rho$ very close to the top of the foliation, at which the rescaled superlevel set is within distance $\sqrt{\delta_T}$ of a unit ball in the shape metric.

---

## 6. Step 5 — Boundary-layer transfer and assembly

We have $F_{\widehat\rho}$ close to $B_1$ in $\mathcal{X}$. We want $\Omega$ close to its ball $B^*$ in $\mathcal{X}$. There is a gap: $E_{\widehat\rho}$ is a *superlevel set* of $\Omega$, not $\Omega$ itself.

### The boundary layer

Since $\widehat\rho \in [\rho_\delta - c_0\sqrt{\delta_T}, \rho_\delta]$ and $|E_\rho| = \omega_n \rho^n$, the boundary layer is
$$
|\Omega \setminus E_{\widehat\rho}| \;=\; \omega_n(1 - \widehat\rho^n) \;\le\; C\sqrt{\delta_T(\Omega)}.
$$
This **is** a rate loss — we're saying "$E_{\widehat\rho}$ differs from $\Omega$ by $O(\sqrt{\delta_T})$" — but it's harmless if we handle it correctly.

### The squaring trick

We have:
- $\mathcal{A}(E_{\widehat\rho}) \le O(\sqrt{\delta_T})$ (after unscaling from $F_{\widehat\rho}$ to $E_{\widehat\rho}$).
- $\mathcal{A}(\Omega) \le \mathcal{A}(E_{\widehat\rho}) + 2|\Omega \setminus E_{\widehat\rho}|/|\Omega| \le \mathcal{A}(E_{\widehat\rho}) + C\sqrt{\delta_T}$ (triangle inequality for asymmetry).

So $\mathcal{A}(\Omega) \le O(\sqrt{\delta_T})$. **Squaring** gives $\mathcal{A}(\Omega)^2 \le O(\delta_T)$ — the sharp exponent. Concretely: $(a + b)^2 \le 2a^2 + 2b^2$ doubles a constant but does *not* degrade the exponent.

This is the famous "**square at the end, not in the middle**" principle. Earlier drafts of Plan 2 (the centroid / $\Pi$-route, now an auxiliary remark) squared too early and ended up with $\sqrt{\delta_T}$ on the right of the final inequality — the wrong rate. The repaired Plan 2 squares **after** the transfer to $\Omega$ and so preserves exponent 2.

### Bounded reduction and Kohler–Jobin

At this point we have
$$
\mathcal{A}(\Omega)^2 \;\le\; C(n, R)\, \delta_T(\Omega) \qquad \text{for $\Omega \subset B_R$.}
$$
**Bounded reduction** (the BDV Lemma 5.3, imported from Plan 1's Final/BoundedReduction block) removes the $R$ dependence; **Kohler–Jobin** (from Step 0) transfers $\delta_T$-stability to $\delta_{FK}$-stability. The two reductions are common to both Plans, so Plan 2's final theorem
$$
\delta_{FK}(\Omega) \;\ge\; c_{FK}(n)\, \mathcal{A}(\Omega)^2
$$
is stated in the **same normalisation and with the same dimensional constant** as Plan 1's.

---

## 7. A one-page summary

Read this when you forget what just happened.

```
                       δ_T(Ω)
                          │
                          │  Step 1: level-set deficit identity
                          ▼
        ∫ [ D_H(t(ρ)) + D_I(t(ρ)) ] w(ρ) dρ
            ↑gradient          ↑isoperimetric
           oscillation         defect
                          │
                          │ Step 2: rescale E_ρ → F_ρ; metric framework
                          │ controls |Ḟ_ρ|_X by D_H.
                          ▼
       ∫ |Ḟ_ρ|_X^2 dμ  ≤ (D_H term) ≤ δ_T
                          │
                          │ Step 3: Fusco-Julin centre z_ρ
                          │ + ORIENTED RADIAL TRACE lemma
                          │ converts D_I into d_X(F_ρ, B_1)^2
                          ▼
   ∫ [ d_X(F_ρ, B_1)^2 + |Ḟ_ρ|_X^2 ] dμ  ≤  C · δ_T
                          │
                          │ Step 4: weighted metric trace
                          │ on window [ρ_δ - c_0√δ_T, ρ_δ]
                          ▼
         ∃ ρ̂:  d_X(F_ρ̂, B_1)^2  ≤  C_* · δ_T
                          │
                          │ Step 5: |Ω \ E_ρ̂| = O(√δ_T)
                          │ transfer + squaring trick
                          ▼
                A(Ω)^2  ≤  C(n,R) · δ_T(Ω)
                          │
                          │ Bounded reduction (removes R)
                          │ Kohler-Jobin (δ_T → δ_FK)
                          ▼
                δ_FK(Ω)  ≥  c_FK(n) · A(Ω)^2
```

---

## 8. How Plan 2 differs from Plan 1

| Aspect | Plan 1 (BDV) | Plan 2 (level-set/metric) |
|---|---|---|
| Object | One near-extremal $\Omega$ found by selection | The whole foliation $\{E_\rho\}$ of $u_\Omega$ |
| Regularity used | C^{2,γ} graph over the sphere | Finite perimeter only |
| Isoperimetric input | Fuglede's nearly-spherical theorem | Fusco–Julin two-term sharp inequality |
| Closing step | Contradiction at the selected minimiser | Arc-length trace argument in $\mathcal{X}$ |
| Common final step | Bounded reduction + Kohler–Jobin | Same |

**Why bother including Plan 2?**
1. **Structurally different.** It doesn't smooth $\Omega$; it doesn't pick out one near-ball; it doesn't graph anything over a sphere. It treats $\Omega$ as a foliation and watches every level.
2. **Direct use of FJ.** Plan 1 uses isoperimetric stability only indirectly, through regularity. Plan 2 plugs FJ into every level set; the role of quantitative isoperimetry is laid bare.
3. **Finite-perimeter native.** The whole proof works for finite-perimeter $\Omega$ with no graph assumption. The metric framework and the radial trace lemma are designed for finite perimeter from the start.
4. **A new lemma.** The oriented $L^1$-radial trace lemma (Step 3) is, to our knowledge, new in this Saint–Venant / Faber–Krahn context. It is the conceptual core of the proof.

---

## 9. What is *not* used in Plan 2

The manuscript also contains an **auxiliary** section on the **centroid kinematic identity** and the **space-time $\Pi$-identity**. These are diagnostic computations:
- The bulk centroid $\bar z_\rho$ as a function of $\rho$ has a kinematic formula (Lipschitz in $\rho$, derivative computable from $|\nabla u|$ on the level set).
- A space-time identity decomposes the signed "$\Pi$-moment" $\int |x - \bar z_\rho| - \rho$ on $\partial^* E_\rho$ across $\rho$.

These are **not** load-bearing for the repaired Plan 2. The original first attempt at Plan 2 tried to close the chain through pointwise $\Pi$-control instead of the oriented radial trace lemma, and it required an *integrated* $\Pi$-control estimate that we could not prove. The repaired chain (Steps 1–5 above) bypasses the $\Pi$-route entirely. The auxiliary section is kept in the manuscript as a record of the route and a place to upgrade if a future integrated $\Pi$-bound is proved, but **nothing in Plan 2 currently depends on it**. The auditor (Agent 16) verified this explicitly.

---

## 10. Where to look in the manuscript

| If you want to read about… | Look at |
|---|---|
| Step 0 (Kohler–Jobin bridge, Talenti, FJ, GMT toolbox) | `01_preliminaries_draft.tex` |
| Step 1 (level-set identity) | `plan2_levelset_identity.tex` |
| Step 2 (metric framework, first variation) | `plan2_metric_framework.tex` |
| Step 3 (FJ centres, oriented radial trace) | `plan2_fj_center_radial_trace.tex` |
| Step 4 (weighted metric trace) | `plan2_weighted_metric_trace.tex` |
| Step 5 (boundary layer, assembly) | `plan2_boundary_layer_assembly.tex` |
| Auxiliary centroid/$\Pi$-route (not load-bearing) | `plan2_aux_centroid_note.tex` |
| What the audit found and how it was repaired | `audit_plan2.md`, `audit_plan2_repair_report.md` |
| What's the final verdict | `final_adversarial_audit.md`, `audit_final_repair_report.md` |

The compiled manuscript is `Manuscript/main.pdf` (119 pages).

---

## 11. The two-sentence version

Plan 2 expresses the Saint–Venant deficit as an integral over the superlevel-set foliation of the torsion function, controls each level using Fusco–Julin centres and an oriented $L^1$ radial trace lemma, and extracts a single near-ball level via a weighted metric-space arc-length argument; transferring back to $\Omega$ and squaring at the end (not in the middle) gives the sharp $\mathcal{A}(\Omega)^2 \le C\,\delta_T(\Omega)$. Kohler–Jobin then turns this into the sharp quantitative Faber–Krahn inequality with the same dimensional constant Plan 1 produces.
