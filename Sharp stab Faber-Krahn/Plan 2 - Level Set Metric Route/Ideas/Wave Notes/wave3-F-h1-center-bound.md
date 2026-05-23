# Wave 3 Agent F: H¹-in-ρ Fraenkel-center bound

**Author.** Wave 3 Agent F, Plan 2 audit (ETH Zürich).
**Date.** 2026-05-13.
**Status.** Proves (F) **unconditionally** (no graph, no selection, no use of the radial-trace input (R) or the quadratic Fusco–Julin (B²)). The proof uses the **centroid** as the center field, Agent 1's coarea identity, gmt-inputs (3.2) (Cauchy-deficit on $V_\rho$, $D_H$-only), FMP, and Fusco–Julin's L¹ oscillation bound (B). Integration against $(-t')\,d\rho$ is absorbed by Agent B's Corollary 3.2.

## 1. Precise statement

Fix $n \ge 2$, $R \ge 2$, $\rho_* \in (0,1)$, and $\kappa > 0$. Let $\Omega \subset B_R \subset \mathbb R^n$ be open with $|\Omega| = \omega_n$ and $\delta := \delta_T(\Omega) \le \delta_0(n, \rho_*, R)$ small. Let $u$ be the variational torsion function of $\Omega$, $t : [\rho_*, 1] \to (0, \|u\|_\infty)$ the volume-radius parametrization with $|\{u > t(\rho)\}| = \omega_n \rho^n$, $E_\rho := \{u > t(\rho)\}$, and $V_\rho(x) := -t'(\rho)/|\nabla u(x)|$ on $\partial^* E_\rho \cap \{|\nabla u| > 0\}$. Set $\rho_\delta := 1 - \kappa\sqrt{\delta}$.

**Theorem F (H¹-in-ρ center bound).** Define the **centroid field**
$$
\bar z_\rho := \frac{1}{|E_\rho|}\int_{E_\rho} x\, dx \in \mathbb R^n, \qquad \rho \in [\rho_*, 1].
$$
Then $\rho \mapsto \bar z_\rho$ is Lipschitz on $[\rho_*, 1]$ (so AC; the distributional derivative coincides with the classical derivative a.e.), and
$$
\boxed{\int_{\rho_*}^{\rho_\delta} |\bar z_\rho'|^2\, (-t'(\rho))\, d\rho \;\le\; C(n, R, \rho_*)\,\delta_T(\Omega).} \tag{F}
$$
The constant $C$ is polynomial in $1/\rho_*$, $R$, and $n$, and depends only on the constants of FMP (Figalli–Maggi–Pratelli 2010), Fusco–Julin (B) (Fusco–Julin 2014), gmt-inputs (3.2), Agent 1, and Agent B (Corollary 3.2). It does not depend on $\kappa$ or on $\delta$.

**Compatibility with the Fraenkel centre.** By Cicalese–Leonardi 2012 (Prop. 2.3) and Acerbi–Fusco–Morini 2013 (Lem. 2.6), in the smallness regime
$$
|\bar z_\rho - z^{\mathrm{Fr}}_\rho| \le C(n, \rho_*)\, \mathcal A(E_\rho) \le C'(n, \rho_*, R)\sqrt{\delta_T(\Omega)},
$$
so $\bar z_\rho$ is interchangeable with the CL Fraenkel centre $z^{\mathrm{Fr}}_\rho$ at cost $O(\sqrt{\delta_T})$, absorbed downstream into the constants of Wave 3 Agent G's route-δ assembly exactly as in Wave 2 Agent C §C1.

## 2. Setup and measurability

**2.1 Smallness regime.** By Wave 2 Agent A Lemma 2.2, $\mathcal A(E_\rho) \le C(n,\rho_*)\sqrt{\delta_T} \le \varepsilon_0$ for all $\rho \in [\rho_*, 1]$, $\varepsilon_0$ the CL 2012 smallness threshold, provided $\delta_0(n, \rho_*, R)$ is chosen small. Hence the CL containment
$$
B(z^{\mathrm{Fr}}_\rho, \rho/2) \subset E_\rho \subset B(z^{\mathrm{Fr}}_\rho, 2\rho) \tag{CL}
$$
holds for a.e. $\rho \in [\rho_*, 1]$. Since $|\bar z_\rho - z^{\mathrm{Fr}}_\rho| \le C\sqrt{\delta_T} \le \rho/4$ for $\delta$ small, the centred containment $B(\bar z_\rho, \rho/4) \subset E_\rho \subset B(\bar z_\rho, 3\rho)$ holds too; in particular $|x - \bar z_\rho| \le 3\rho \le 3$ on $\partial^* E_\rho$.

**2.2 Borel measurability and Lipschitz-in-$\rho$ regularity of $\bar z_\rho$.**

*Borel.* $\rho \mapsto E_\rho$ is monotone nested (since $t$ is decreasing). Hence $\rho \mapsto \int_{E_\rho} x_i\, dx$ is Borel (in fact continuous: dominated convergence applied to monotone $\chi_{E_\rho}$), and $|E_\rho| = \omega_n\rho^n$ is smooth; so $\bar z_\rho$ is Borel.

*Lipschitz.* By Agent B Lemma 2.1 (= (A0)), for $\rho_* \le \rho \le \rho' \le 1$,
$$
|E_\rho \,\Delta\, E_{\rho'}| \;\le\; |E_{\rho'}| - |E_\rho| \;=\; \omega_n((\rho')^n - \rho^n) \;\le\; n\omega_n\,|\rho - \rho'|,
$$
(monotone nesting; no homothety argument needed for the $L^1$ piece). Since $E_\rho, E_{\rho'} \subset B_R$,
$$
\biggl|\int_{E_\rho} x_i \,dx - \int_{E_{\rho'}} x_i\, dx\biggr| \le R\, |E_\rho \,\Delta\, E_{\rho'}| \le R n\omega_n\, |\rho - \rho'|.
$$
Combined with $|E_\rho| \ge \omega_n\rho_*^n$,
$$
|\bar z_\rho - \bar z_{\rho'}| \le L_{\mathrm{cent}}(n, R, \rho_*)\,|\rho - \rho'|, \qquad L_{\mathrm{cent}} := \frac{2nR}{\rho_*^n}.
$$
In particular $\bar z_\rho$ is AC and differentiable a.e.

## 3. The centroid derivative identity

**Lemma 3.1 (centroid kinematic formula).** For a.e. $\rho \in [\rho_*, 1]$,
$$
\bar z_\rho' \;=\; \frac{1}{|E_\rho|}\int_{\partial^* E_\rho} (x - \bar z_\rho)\, V_\rho \, d\mathcal H^{n-1}. \tag{3.2}
$$

**Proof.** By the coarea identity for the level family of $u$ (Agent 1 §3, also `agent3-metric-first-variation.md` (0.1); valid here because $\rho \mapsto E_\rho$ is the level family of a Sobolev function $u \in W^{2,p}_{\mathrm{loc}}$, $p > n$, with $|\nabla u| > 0$ a.e. on $\partial^* E_\rho$ by Sobolev–Sard — Figalli–Maggi 2011 App. A; see Wave 2 Agent C §C2):
$$
\frac{d}{d\rho}\int_{E_\rho} f\, dx \;=\; \int_{\partial^* E_\rho} f \,V_\rho\, d\mathcal H^{n-1} \tag{3.1}
$$
for any Lipschitz $f: B_R \to \mathbb R$ and a.e. $\rho$. Take $f(x) = x_i$ and use $|E_\rho| = \omega_n\rho^n$, $\frac{d}{d\rho}|E_\rho| = P(B_\rho) = \int_{\partial^* E_\rho} V_\rho\, d\mathcal H^{n-1}$ (the last by (3.1) with $f \equiv 1$). Then
$$
\bar z_\rho' = \frac{d}{d\rho}\left(\frac{1}{|E_\rho|}\int_{E_\rho} x\, dx\right) = \frac{1}{|E_\rho|}\int_{\partial^* E_\rho} x V_\rho\, dH - \frac{P(B_\rho)}{|E_\rho|^2}\int_{E_\rho} x\, dx
$$
$$
= \frac{1}{|E_\rho|}\left(\int_{\partial^* E_\rho} x V_\rho\, dH - \bar z_\rho \int_{\partial^* E_\rho} V_\rho\, dH\right) = \frac{1}{|E_\rho|}\int_{\partial^* E_\rho}(x - \bar z_\rho) V_\rho\, dH.
$$
$\square$

**Remark.** Identity (3.2) is the **first vector moment** of the velocity field $V_\rho$ relative to the centroid. Crucially, it has **no comparison to the homothety $H_{z,\rho}$**. This is the structural reason the proof avoids (1.2)/(R).

## 4. The key pointwise estimate

**Lemma 4.1.** For a.e. $\rho \in [\rho_*, 1]$ in the smallness regime,
$$
|\bar z_\rho'|^2 \;\le\; C_*(n, \rho_*, R)\,\bigl(D_H(t(\rho)) + D_I(t(\rho))\bigr), \tag{4.1}
$$
with $C_*$ depending only on $n, \rho_*, R$ and on the constants of FMP and FJ.

**Proof.** Set $\bar V_\rho := P(B_\rho)/P(E_\rho)$. Note $0 < \bar V_\rho \le 1$ in smallness ($P(E_\rho) \ge P(B_\rho)$ by isoperimetry).  Decompose $V_\rho = \bar V_\rho + (V_\rho - \bar V_\rho)$ in (3.2):
$$
|E_\rho|\, \bar z_\rho' \;=\; \underbrace{\bar V_\rho \int_{\partial^* E_\rho}(x - \bar z_\rho)\, d\mathcal H^{n-1}}_{(\mathrm I)} \;+\; \underbrace{\int_{\partial^* E_\rho}(x - \bar z_\rho)\,(V_\rho - \bar V_\rho)\, d\mathcal H^{n-1}}_{(\mathrm{II})}. \tag{4.2}
$$

### 4.A Bound on (II): unconditional, $D_H$-only

By CL containment §2.1, $|x - \bar z_\rho| \le 3\rho \le 3$ on $\partial^* E_\rho$. Hence
$$
|(\mathrm{II})| \;\le\; 3 \int_{\partial^* E_\rho} |V_\rho - \bar V_\rho| \, d\mathcal H^{n-1}.
$$
By gmt-inputs **(3.2)** — the **unconditional** Cauchy-deficit bound for $V_\rho$, derived from the exact identity gmt-inputs (3.1) and Cauchy–Schwarz, both purely algebraic consequences of Agent 1:
$$
\left(\int_{\partial^* E_\rho}|V_\rho - \bar V_\rho|\, d\mathcal H^{n-1}\right)^2 \;\le\; C_{n, \rho_*}\, D_H(t(\rho)). \tag{4.3}
$$
Therefore
$$
|(\mathrm{II})|^2 \;\le\; 9\, C_{n, \rho_*}\, D_H(t(\rho)) \;=:\; C_1\, D_H(t(\rho)). \tag{4.3'}
$$

### 4.B Bound on (I): unconditional, FMP + FJ + divergence theorem

We claim, for each direction $e_i$,
$$
\biggl|\int_{\partial^* E_\rho} (x - \bar z_\rho)_i\, d\mathcal H^{n-1}\biggr| \;\le\; C_2(n, \rho_*)\,\sqrt{\delta_\rho}, \qquad \delta_\rho := P(E_\rho) - P(B_\rho), \tag{4.4}
$$
**unconditionally**, where $C_2$ depends on the constants of FMP and FJ.

*Proof of (4.4).* Write $x - \bar z_\rho = |x - \bar z_\rho|\, e_r(x)$ with $e_r(x) := (x - \bar z_\rho)/|x - \bar z_\rho|$, well-defined since $\bar z_\rho \in B(\bar z_\rho, \rho/4) \subset E_\rho$ (so $\bar z_\rho \notin \partial^* E_\rho$). Decompose
$$
(x - \bar z_\rho)_i = |x - \bar z_\rho|(e_r)_i = |x - \bar z_\rho|(\nu_E)_i + |x - \bar z_\rho|\bigl((e_r)_i - (\nu_E)_i\bigr). \tag{4.5}
$$

*First integral in (4.5).* Apply the divergence theorem to the **Lipschitz** vector field $V^{(i)}(x) := |x - \bar z_\rho|\, e_i$ ($|\nabla V^{(i)}|_\infty \le 1$): $\partial_j V^{(i)}_j = (e_r)_i$ (computed in the distributional/a.e. sense; the function $|x - \bar z_\rho|$ is Lipschitz hence W^{1,\infty}, with classical gradient $e_r$ a.e.). The divergence theorem for finite-perimeter sets (Maggi 2012 Thm. 15.9) gives
$$
\int_{\partial^* E_\rho}|x - \bar z_\rho|(\nu_E)_i\, d\mathcal H^{n-1} \;=\; \int_{E_\rho} (e_r(x))_i\, dx. \tag{4.6}
$$
On the comparison ball $B_\rho(\bar z_\rho)$, $\int (e_r)_i\, dx = 0$ by spherical symmetry. Hence
$$
\biggl|\int_{E_\rho}(e_r)_i\, dx\biggr| = \biggl|\int_{E_\rho}(e_r)_i - \int_{B_\rho(\bar z_\rho)}(e_r)_i\biggr| \;\le\; |E_\rho \,\Delta\, B_\rho(\bar z_\rho)|. \tag{4.7}
$$
By **FMP** (Figalli–Maggi–Pratelli 2010 Thm. 1.1), $|E_\rho \,\Delta\, B_\rho(z^{\mathrm{Fr}}_\rho)|^2 \le c_1 |B_\rho|^2\,\delta_\rho$, i.e. $|E_\rho \,\Delta\, B_\rho(z^{\mathrm{Fr}}_\rho)| \le C(n, \rho_*)\sqrt{\delta_\rho}$. By Acerbi–Fusco–Morini 2013 Lem. 2.6 / CL 2012 Prop. 2.3, in the smallness regime $|\bar z_\rho - z^{\mathrm{Fr}}_\rho| \le C\sqrt{\delta_\rho}$; combined with $|B_\rho(a) \,\Delta\, B_\rho(b)| \le C(n)\rho^{n-1}|a - b|$,
$$
|E_\rho \,\Delta\, B_\rho(\bar z_\rho)| \;\le\; |E_\rho \,\Delta\, B_\rho(z^{\mathrm{Fr}}_\rho)| + |B_\rho(z^{\mathrm{Fr}}_\rho) \,\Delta\, B_\rho(\bar z_\rho)| \;\le\; C(n, \rho_*)\sqrt{\delta_\rho}. \tag{4.8}
$$
Substituting (4.8) into (4.7) and (4.6),
$$
\biggl|\int_{\partial^* E_\rho}|x - \bar z_\rho|(\nu_E)_i\, dH\biggr| \;\le\; C(n, \rho_*)\sqrt{\delta_\rho}. \tag{4.9}
$$

*Second integral in (4.5).* Using $|x - \bar z_\rho| \le 3$ and the L¹ form of **Fusco–Julin** (B) (Fusco–Julin 2014 Thm. 1.1):
$$
\int_{\partial^* E_\rho}|\nu_E - e_r|\, d\mathcal H^{n-1} \;\le\; C_{\mathrm{FJ}}(n, \rho_*)\sqrt{\delta_\rho}. \tag{FJ}
$$
(Strictly, FJ (B) is stated for the FJ centre, but the centroid is within $O(\sqrt{\delta_\rho})$ — see (4.8); the change-of-centre error in FJ is $|\bar z_\rho - z^{\mathrm{FJ}}|\cdot\int 1/|x - z|\, dH \le C\sqrt{\delta_\rho}\cdot 4\rho_*^{-1}\cdot P(E_\rho) \le C\sqrt{\delta_\rho}$, absorbed.) Thus
$$
\biggl|\int_{\partial^* E_\rho}|x - \bar z_\rho|\bigl((e_r)_i - (\nu_E)_i\bigr)\, dH\biggr| \;\le\; 3\, C_{\mathrm{FJ}}\sqrt{\delta_\rho}. \tag{4.10}
$$

Combining (4.5), (4.9), (4.10) gives (4.4) with $C_2 := C(n, \rho_*) + 3 C_{\mathrm{FJ}}$. $\square$

### 4.C Combining (4.3') and (4.4)

From (4.2), (4.3'), and (4.4) (and $\bar V_\rho \le 1$),
$$
|E_\rho|^2\, |\bar z_\rho'|^2 \;\le\; 2|(\mathrm I)|^2 + 2|(\mathrm{II})|^2 \;\le\; 2 C_2^2\, \delta_\rho + 2 C_1\, D_H(t(\rho)). \tag{4.11}
$$
Use the **algebraic** lower bound
$$
D_I(t(\rho)) \;=\; P(E_\rho)^2 - P(B_\rho)^2 \;=\; \delta_\rho\,(P(E_\rho) + P(B_\rho)) \;\ge\; \delta_\rho\, P(B_\rho) \;\ge\; n\omega_n\rho_*^{n-1}\, \delta_\rho, \tag{4.12}
$$
so $\delta_\rho \le (n\omega_n\rho_*^{n-1})^{-1}\, D_I(t(\rho))$. Combined with $|E_\rho|^2 \ge \omega_n^2\rho_*^{2n}$, (4.11) becomes
$$
|\bar z_\rho'|^2 \;\le\; \frac{2 C_1}{\omega_n^2\rho_*^{2n}}\,D_H \;+\; \frac{2 C_2^2}{\omega_n^2\rho_*^{2n}\cdot n\omega_n\rho_*^{n-1}}\,D_I \;\le\; C_*(n, \rho_*, R)\bigl(D_H + D_I\bigr),
$$
which is (4.1). $\square$

## 5. Closing the integral

**Proof of Theorem F.** By Lemma 4.1, Agent B Lemma 3.1 ($D_H + D_I = P(B_\rho)^2 |\psi(\rho)|/(-t'(\rho))$ with $\psi := -t_B' - (-t')$), and Agent B Corollary 3.2 ($\int_{\rho_*}^1 |\psi(\rho)|\, d\rho \le K_1(n, \rho_*)\,\delta$, $K_1 = 2/(\omega_n\rho_*^n)$):
$$
\int_{\rho_*}^{\rho_\delta}|\bar z_\rho'|^2\,(-t')\, d\rho \;\le\; C_*\int_{\rho_*}^{\rho_\delta}(D_H + D_I)(-t')\, d\rho \;=\; C_*\int_{\rho_*}^{\rho_\delta} P(B_\rho)^2\,|\psi(\rho)|\, d\rho
$$
$$
\;\le\; C_*\, (n\omega_n)^2\int_{\rho_*}^{1}|\psi|\, d\rho \;\le\; C_*\,(n\omega_n)^2\, K_1\, \delta_T(\Omega) \;=:\; C(n, R, \rho_*)\, \delta_T(\Omega),
$$
since $P(B_\rho) = n\omega_n\rho^{n-1} \le n\omega_n$ on $[\rho_*, 1]$. $\square$

## 6. Conditionality analysis

**Claim: Theorem F is unconditional.** It uses *none* of (R), (B²), (1.1), (1.2), or any per-ρ form thereof.

Inputs used:

| Input | Source | Status |
|---|---|---|
| Agent 1 exact deficit identity | `agent1-finite-perimeter-identity.md` Thm. §0 | **Unconditional** |
| Coarea (3.1) for level family of $u$ | Agent 1, Maggi 2012 Thm. 13.1 | **Unconditional** |
| Sobolev–Sard | Figalli–Maggi 2011 App. A; Wave 2 Agent C §C2 | **Unconditional** |
| Agent B Lemma 3.1 ($D_H + D_I = P_\rho^2|\psi|/(-t')$) | `wave2-B-kinetic-bound.md` §3 | **Unconditional** (algebraic) |
| Agent B Corollary 3.2 ($\int|\psi|\,d\rho \le K_1\delta$) | `wave2-B-kinetic-bound.md` §3 | **Unconditional** (Talenti / Agent 1) |
| gmt-inputs **(3.2)** ($(\int|V_\rho - \bar V_\rho|)^2 \le C D_H$) | `gmt-inputs-for-metric-closure.md` §3 | **Unconditional** |
| FMP volume bound $|E\Delta B_\rho(z)|^2 \le c\,\rho^{n+1}\,\delta_\rho$ | Figalli–Maggi–Pratelli 2010 | **Unconditional** |
| FJ L¹ oscillation $(\int|\nu_E - e_r|)^2 \le C\,\delta_\rho$ | Fusco–Julin 2014 | **Unconditional** |
| CL containment $B(z, \rho/2) \subset E \subset B(z, 2\rho)$ | Cicalese–Leonardi 2012 | **Unconditional** in smallness |
| Centroid–Fraenkel-centre proximity $|\bar z - z^{\mathrm{Fr}}| \le C\sqrt{\delta_\rho}$ | Cicalese–Leonardi 2012 Prop. 2.3, Acerbi–Fusco–Morini 2013 Lem. 2.6 | **Unconditional** |

**Inputs *not* used.** Explicitly:

- gmt-inputs **(1.1)** (strong isoperimetric oscillation) — this is the no-graph (B²) equivalent;
- gmt-inputs **(1.2)** (the radial L¹ trace = (R));
- gmt-inputs **(2.4)** ($(\int|\bar V_\rho - H_{z,\rho}|)^2 \le C D_I$), which is the squared-perimeter version of (1.1);
- Agent 3 **(7.1)** ($|\dot\gamma|^2 \le C(D_H + D_I)$ per $\rho$), which uses (2.4);
- the entire Agent 2 §3 chain ($D_I$-controlled bound on the homothetic velocity defect);
- Wave 2 Agent A's quadratic Fusco–Julin oscillation (B²).

**The structural reason** (F) avoids (R)/(B²) is that the centroid's kinematic formula (3.2) contains **no homothety term**. The temptation in writing (F) "via the Fraenkel functional first-order condition" (Strategy 1 of the brief) would have led to $\bar z_\rho' = \mathrm{Hess}^{-1}\cdot\partial_\rho\nabla_z F_\rho$, and the right-hand side $\partial_\rho\nabla_z F_\rho$ is the integral of $V_\rho - H_{z, \rho}$ over a sphere — i.e. it *does* invoke the homothety, and the bound then goes through (2.4) → (R). The centroid choice eliminates the homothety because it is defined directly by a bulk integral, not by a Fraenkel minimization principle that requires comparison to balls.

This is the bypass Agent E §5 step (5) called for: the H¹-in-$\rho$ control of the centre comes from the *integrated $D_H+D_I$ action* (which is unconditional from Agent 1) plus the *bulk first-moment closeness to a ball* (FMP+FJ — both unconditional), not from a per-ρ application of (R).

## 7. Constants track

We track $C(n, R, \rho_*)$ explicitly.

| Step | Constant | Origin |
|---|---|---|
| (4.3) | $C_1 = 9 C_{\mathrm{gmt}}$, $C_{\mathrm{gmt}} \le 1/(n\omega_n\rho_*^{n-1})$ | gmt-inputs (3.2): $(\int|V - \bar V|)^2 \le (A_\rho/P_\rho^2)\cdot P_\rho \cdot \int(V-\bar V)^2/V$ |
| (4.4) | $C_2 \le C(n,\rho_*) + 3 C_{\mathrm{FJ}}(n, \rho_*)$ | FMP + FJ |
| $\bar V_\rho \le 1$ | smallness | $P(E_\rho) \ge P(B_\rho)$ |
| (4.12) | $\sqrt{\delta_\rho} \le (n\omega_n\rho_*^{n-1})^{-1/2}\sqrt{D_I}$ | algebra |
| $1/|E_\rho|^2 \le 1/(\omega_n\rho_*^n)^2$ | dimensional | volume |
| $C_*$ in (4.1) | $C_* \le C(n) \cdot \max(C_1, C_2^2)\cdot \rho_*^{-(3n-1)}$ | combine |
| $K_1$ in Agent B Cor. 3.2 | $K_1 = 2/(\omega_n\rho_*^n)$ | Talenti / Agent 1 |
| Final $C$ in (F) | $C(n, R, \rho_*) \le C_*\cdot (n\omega_n)^2\cdot K_1$, polynomial in $1/\rho_*$ and $R$ | combine |

All constants are polynomial in $1/\rho_*, R, n$ and **independent of $\kappa$ and $\delta$**.

## 8. Open issues

**8.1 No residual gap on (F) itself.** The proof is complete and unconditional within the smallness regime $\delta \le \delta_0(n, \rho_*, R)$. Outside smallness, $\mathcal A(\Omega) \ge c(n) > 0$ implies $\delta_T(\Omega) \ge c'(n) > 0$ (FMP); (F) is then trivial with $C$ enlarged by $1/c'$.

**8.2 Centre choice for downstream use (Wave 3 Agent G).** The centroid $\bar z_\rho$ differs from the FvHT block centre / Fraenkel centre by $O(\sqrt{\delta_T})$. Wave 3 Agent G should use $\bar z_\rho$ throughout, or absorb the $O(\sqrt{\delta_T})$ correction into constants exactly as Wave 2 Agent C §C1 does.

**8.3 Reconciliation with FvHT-style overlap.** The centroid is the continuous analog of the FvHT block-centre. On the Agent-B good set, by Cauchy–Schwarz on intervals, the increment $|\bar z_{\rho''} - \bar z_{\rho'}|$ recovers (and quantitatively strengthens) the FvHT overlap bound.

**8.4 What is *not* claimed.** Theorem F does **not** close (B²) or (R). It supplies one specific input — the H¹-in-$\rho$ control of the centre drift — that Agent E §4 (Wave 3 problem statement, step 5) identified as the missing piece in route δ. Closing Plan 2 at rate $\delta_T$ via route δ requires also (i) the space-time $\Pi$ identity, (ii) the Nicola–Tilli profile-gap conversion, (iii) the moving-centroid correction — all Wave 3 Agent G's task.

**8.5 Stronger H² question (open).** Whether $\bar z_\rho$ satisfies an H²-in-$\rho$ bound is open and likely requires (B²). Not needed for Plan 2's closure under route δ.

**8.6 Sharpness of (4.1).** The pointwise bound (4.1) is sharp in scaling: for a small translation $\bar z_\rho = \bar z_{\rho_0} + (\rho - \rho_0)\eta$ of a ball, $V_\rho - \bar V_\rho$ has a dipole structure of size $\sim |\eta|$, giving $D_H \sim |\eta|^2 \sim |\bar z_\rho'|^2$. Linear scaling in $D_H$ cannot be improved.

**8.7 Plan-2-brief compatibility.** The proof uses only finite-perimeter / coarea (no graph), the centroid (a bulk integral, not a Fraenkel selection), CL containment (measure-theoretic), FMP, FJ, Agent 1, Agent B, gmt-inputs (3.2). **No graph parametrisation of $\partial^* E_\rho$, no BDV/Plan 1 selection, no free-boundary regularity.** Inside Plan 2's brief.

## 9. References

- Acerbi, E.; Fusco, N.; Morini, M., *Minimality via second variation for a nonlocal isoperimetric problem*, Comm. Math. Phys. **322** (2013), 515–557. (Lem. 2.6: centroid–Fraenkel-centre proximity.)
- **Agent 1** = `agent1-finite-perimeter-identity.md`. (Coarea identity, exact deficit, $V_\rho$ definition.)
- **Agent 3** = `agent3-metric-first-variation.md`. (Sobolev–Sard, kinematic formula context; *(7.1) and (T) are not used in this note*.)
- **Agent B** = `wave2-B-kinetic-bound.md`. (Lemma 3.1, Corollary 3.2, Lemma 4.1.)
- **Agent C** = `wave2-C-cleanup.md`. (C1, C2.)
- **Agent E** = `wave2-E-bypass-search.md`. (Route δ Wave 3 problem statement, §4 step 5.)
- Cicalese, M.; Leonardi, G. P., *A selection principle for the sharp quantitative isoperimetric inequality*, ARMA **206** (2012), 617–643.
- Figalli, A.; Maggi, F., *On the shape of liquid drops...*, ARMA **201** (2011), 143–207.
- Figalli, A.; Maggi, F.; Pratelli, A., *A mass transportation approach...*, Invent. Math. **182** (2010), 167–211.
- Fusco, N.; Julin, V., *A strong form of the quantitative isoperimetric inequality*, Calc. Var. PDE **50** (2014), 925–937.
- **gmt-inputs** = `gmt-inputs-for-metric-closure.md`. ((3.1)–(3.2): Cauchy-deficit identity. *(2.4) is not used in this note*.)
- Maggi, F., *Sets of Finite Perimeter...*, Cambridge, 2012.
- Talenti, G., Ann. Mat. Pura Appl. **110** (1976), 353–372.
- **Wave 2 Agent A** = `wave2-A-radial-l2-trace.md`. (Lemma 2.2: smallness regime.)

## 10. Verdict

**Theorem F is proved unconditionally** by the centroid kinematic identity (3.2) + (4.3) [gmt-inputs (3.2), $D_H$-only, unconditional] + (4.4) [FMP + FJ + divergence theorem, unconditional] + Agent B Corollary 3.2 [Agent 1, unconditional].

**No graph, no selection, no (R), no (B²).** The proof bypasses the Wave 2 Agent D-flagged conditionality (Agent 3 (7.1) → gmt-inputs (2.4) → (R)/(1.1)) by:
1. choosing the centroid as the centre field, whose derivative is a direct bulk-coarea computation with no homothety;
2. handling the boundary first moment $\int(x - \bar z_\rho)\,dH$ by FMP + divergence theorem, not by a radial trace.

(F) thereby supplies, **unconditionally**, the H¹-in-$\rho$ centre-coherence input that Wave 3 Agent G's route-δ assembly requires.
