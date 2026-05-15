# From `D_H + D_I` to Brandolini's hypothesis: rigorous pipeline

**Purpose.** Make rigorous §1 of
`Plan 3/BRANDOLINI_GRAPH_ENTRY_ROUTE.md`. Given a regular level `t̂` in
the fixed outer annulus `ρ ∈ [ρ_*, 1]` with `(D_H + D_I)(t̂) ≤ η`,
derive, after rescaling `E_{t̂}` to unit volume,
\[
\delta := \bigl\| |Dv| - 1 \bigr\|_{L^\infty(\partial E_{\hat t}^{\rm sc})}
\le C(n, R, \rho_*) \, \eta^{\kappa},
\qquad
\kappa = \min\Bigl(\tfrac{1}{2}, \tfrac{\alpha}{2\alpha + n - 1}\Bigr).
\]
This closes audit issues **G2, G3, G4, M1** of
`Plan 3/AUDIT_BRANDOLINI_ROUTE.md`.

Throughout `Ω ⊂ ℝⁿ` is a `C^{2,α}` bounded open set, `Ω ⊂ B_R(0)`. The
torsion function `u ∈ C^{2,α}(\overline\Omega) ∩ C^{3,α}_{\rm loc}(\Omega)`
satisfies (Plan 2 sign convention)
\[
-\Delta u = 1 \quad \text{in } \Omega,
\qquad u = 0 \quad \text{on } \partial\Omega.
\]
For `t > 0` write `E_t = \{u > t\}`, `\Sigma_t = \{u = t\}`,
`m(t) = |E_t|`, `P(t) = \mathcal H^{n-1}(\Sigma_t)`. The deficits
`D_H, D_I, D_{\rm lev}` are as in `Plan 2/level-set-deficit-identity.md`
§1.

## 0. The fixed outer collar

Fix once and for all `ρ_* ∈ (0, 1)`. The fixed outer annulus is
\[
A_* := \{ t > 0 \; : \; \rho_t \in [\rho_*, 1] \},
\qquad
\rho_t := \bigl( m(t)/\omega_n \bigr)^{1/n}.
\]
Here `ρ_t` is the radius of the ball of volume `m(t)`. We assume the
bounded-reduction regime: there exists `c_0(n, R, \rho_*) > 0` such
that for every `t \in A_*`,
\begin{equation}
\label{eq:dist-bound}
\operatorname{dist}(\Sigma_t, \partial \Omega) \ge c_0(n, R, \rho_*).
\end{equation}
This is the (R) hypothesis of the route document. By interior Schauder
applied to `-\Delta u = 1` on the open set `\{u > t/2\}` (which contains
a `c_0/2`-neighbourhood of `\Sigma_t`),
\begin{equation}
\label{eq:schauder}
\| u \|_{C^{3,\alpha}(\overline{\{u \ge t/2\}})}
\le C_S(n, R, \rho_*).
\end{equation}

## 1. Choosing `t̂` regular and good (audit G3)

**Lemma 1 (Sard + good level).** Let `G_\eta \subset A_*` denote the
set of levels with `D_H(t) + D_I(t) \le \eta`. If
`\mathcal L^1(G_\eta) > 0`, then there exists `\hat t \in G_\eta` with
`|\nabla u(x)| > 0` for all `x \in \Sigma_{\hat t}`, i.e.
`\Sigma_{\hat t}` is a regular level. In particular, by the implicit
function theorem applied to `u \in C^{3,\alpha}_{\rm loc}`,
`\Sigma_{\hat t}` is a `C^{3,\alpha}` hypersurface.

*Proof.* By Sard's theorem (applied to `u \in C^n(\Omega)`, automatic
from `C^{3,\alpha}` for `n \ge 2`), the set of critical values
`u(\{|\nabla u| = 0\})` has Lebesgue measure zero. The set
`G_\eta \subset A_* \subset (0, \|u\|_\infty)` has positive measure;
removing a measure-zero set leaves positive measure. Pick `\hat t` in
the intersection. `\Sigma_{\hat t}` is then a regular level set and
`C^{3,\alpha}` by the implicit function theorem and \eqref{eq:schauder}.
∎

**Input from Agent 1.** `Plan 3/agent1-outer-collar-good-level.md`
Proposition 3.1 supplies, given the Saint–Venant deficit `δ_T(Ω)`, a
level interval inside `A_*` of measure `\ge c(n, \rho_*) \cdot |A_*|` on
which `D_H(t) + D_I(t) \le C(n, \rho_*) \, \delta_T / |A_*|`. With
`\eta := C(n, \rho_*) \, \delta_T / |A_*|`, this guarantees
`\mathcal L^1(G_\eta) > 0` and Lemma 1 applies.

**Lower gradient bound on `\Sigma_{\hat t}`.** Since `\hat t \in A_*`
and `\Sigma_{\hat t}` is regular and `C^{3,\alpha}`, and since
\eqref{eq:dist-bound}-\eqref{eq:schauder} hold, `|\nabla u|` extends
continuously to `\Sigma_{\hat t}` and is strictly positive. We do **not**
assert a quantitative lower bound `\gtrsim 1` at this stage; the bound
\begin{equation}
\label{eq:grad-lower}
|\nabla u(x)| \ge c_1(n, R, \rho_*) > 0
\quad \text{for all } x \in \Sigma_{\hat t}
\end{equation}
will be obtained **a posteriori** from §3 once `δ` is small. For now
it suffices that `\Sigma_{\hat t}` is a `C^{3,\alpha}` compact embedded
hypersurface with `\|u\|_{C^{3,\alpha}} \le C_S(n, R, \rho_*)`.

## 2. The rescaling chain (audit G4, M1)

Let `\lambda := \rho_{\hat t} = (m(\hat t) / \omega_n)^{1/n}`. Fix any
`x_0 \in E_{\hat t}` (e.g. the barycenter of `E_{\hat t}`; the choice
will become important in §M4 of the audit). Define
\[
\widetilde E := \lambda^{-1} \bigl( E_{\hat t} - x_0 \bigr),
\qquad
|\widetilde E| = \lambda^{-n} m(\hat t) = \omega_n.
\]
So `\widetilde E` has the volume of the unit ball. Now define
\begin{equation}
\label{eq:v-def}
v(y) := - \frac{n}{\lambda^2} \bigl( u(x_0 + \lambda y) - \hat t \bigr)
\quad \text{for } y \in \widetilde E.
\end{equation}
Then `v \in C^{3,\alpha}(\overline{\widetilde E})` with
\[
\Delta v(y)
= - \frac{n}{\lambda^2} \cdot \lambda^2 \cdot \Delta u(x_0 + \lambda y)
= - n \cdot (-1) = n,
\]
and `v = 0` on `\partial \widetilde E`. So `v` solves Brandolini's
problem on `\widetilde E`. Moreover
\begin{equation}
\label{eq:grad-rescale}
D v(y) = - \frac{n}{\lambda^2} \cdot \lambda \cdot \nabla u(x_0 + \lambda y)
= - \frac{n}{\lambda} \nabla u(x_0 + \lambda y),
\qquad
|D v(y)| = \frac{n}{\lambda} \, |\nabla u(x_0 + \lambda y)|.
\end{equation}

(Audit M1, audit C4: the route document's "$|Dv| = n \lambda^3 |\nabla u|$"
is wrong; the correct rescaled gradient is `(n/\lambda) |\nabla u|`.
The sign-flip enters via `c = -n/\lambda^2` so that `\Delta v = n`,
not `\Delta v = -n`.)

**Surface and volume rescaling.** For any
`f : \Sigma_{\hat t} \to \mathbb R`,
\[
\int_{\partial \widetilde E} f(x_0 + \lambda y) \, d\mathcal H^{n-1}(y)
= \lambda^{-(n-1)} \int_{\Sigma_{\hat t}} f \, d\mathcal H^{n-1}.
\]
In particular `P(\partial \widetilde E) = \lambda^{-(n-1)} P(\hat t)`.

**Volume preservation, not unit volume.** `\widetilde E` has volume
`\omega_n`, the volume of the unit ball; this is Brandolini's
normalization (so the target object is `B_1`). Henceforth all hatted
quantities (`\widetilde E`, `v`, `\partial \widetilde E`) live in this
normalization.

**Bound on `\lambda`.** For `\hat t \in A_*`,
\begin{equation}
\label{eq:lambda-range}
\rho_* \le \lambda \le 1.
\end{equation}

## 3. Mean of `|∇u|` is close to 1 (audit §1.1 redone)

By the divergence theorem on `E_{\hat t}` with `-\Delta u = 1` and
outward normal `-\nabla u / |\nabla u|`,
\begin{equation}
\label{eq:mass}
m(\hat t) = \int_{E_{\hat t}} (- \Delta u) \, dx
= \int_{\Sigma_{\hat t}} |\nabla u| \, d\mathcal H^{n-1}.
\end{equation}
Define
\[
\bar f := \frac{1}{P(\hat t)} \int_{\Sigma_{\hat t}} |\nabla u| \, d\mathcal H^{n-1}
= \frac{m(\hat t)}{P(\hat t)}.
\]
Now use `D_I(\hat t) \le \eta`. Recall `c_n = n^2 \omega_n^{2/n}` and
\[
D_I(\hat t) = P(\hat t)^2 - c_n \, m(\hat t)^{2 - 2/n} \ge 0.
\]
Hence
\[
P(\hat t)^2
= c_n m(\hat t)^{2 - 2/n} (1 + D_I/(c_n m^{2-2/n})),
\qquad
P(\hat t)
= \sqrt{c_n} \, m(\hat t)^{1 - 1/n} \sqrt{1 + \theta},
\]
with `\theta := D_I(\hat t)/(c_n m(\hat t)^{2 - 2/n}) \in [0, \eta / (c_n m^{2-2/n})]`.
For `\hat t \in A_*`, `m(\hat t) \in [\omega_n \rho_*^n, \omega_n]`, so
\[
0 \le \theta \le \frac{\eta}{c_n (\omega_n \rho_*^n)^{2 - 2/n}}
= C_2(n, \rho_*) \, \eta.
\]
For `\eta \le \eta_1(n, \rho_*) := 1/(2 C_2)`, `\theta \le 1/2` and
`\sqrt{1 + \theta} = 1 + \theta_1` with `0 \le \theta_1 \le \theta` (so
`\theta_1 \le C_2 \eta`). Hence
\begin{equation}
\label{eq:perimeter-expand}
P(\hat t) = \sqrt{c_n} \, m(\hat t)^{1 - 1/n} \cdot (1 + r_P),
\qquad |r_P| \le C_3(n, \rho_*) \, \eta.
\end{equation}
(The dependence on `D_I` is **linear**, not square-root — the audit's
parenthetical guess `(1 + O(\sqrt{\eta}))` is suboptimal but does not
break the chain since we keep the worse exponent `1/2` separately.)

Combining \eqref{eq:mass} and \eqref{eq:perimeter-expand},
\[
\bar f
= \frac{m(\hat t)}{P(\hat t)}
= \frac{m(\hat t)^{1/n}}{\sqrt{c_n} (1 + r_P)}
= \frac{\omega_n^{1/n} \lambda}{n \omega_n^{1/n}} (1 + r_P)^{-1}
= \frac{\lambda}{n} (1 + r_P)^{-1}.
\]
Here we used `m(\hat t)^{1/n} = \omega_n^{1/n} \lambda` and
`\sqrt{c_n} = n \omega_n^{1/n}`.

By \eqref{eq:grad-rescale}, the mean of `|Dv|` on `\partial \widetilde E`
is
\[
\overline{|Dv|}
:= \frac{1}{P(\partial \widetilde E)}
\int_{\partial \widetilde E} |Dv| \, d\mathcal H^{n-1}
= \frac{n}{\lambda} \cdot \bar f
= \frac{n}{\lambda} \cdot \frac{\lambda}{n} (1 + r_P)^{-1}
= (1 + r_P)^{-1}.
\]
Therefore
\begin{equation}
\label{eq:mean-grad}
\bigl| \overline{|Dv|} - 1 \bigr|
\le \frac{|r_P|}{1 - |r_P|} \le 2 C_3(n, \rho_*) \, \eta
\quad \text{for } \eta \le \eta_1.
\end{equation}

## 4. `L^2` variance from `D_H` (audit §1.2 redone)

`Plan 2/level-set-deficit-identity.md` §6, boxed identity (line 379):
\begin{equation}
\label{eq:dh-identity}
\int_{\Sigma_t} \frac{(|\nabla u| - \bar f_t)^2}{|\nabla u|} \, d\mathcal H^{n-1}
= \frac{m(t)}{P(t)^2} \, D_H(t),
\qquad \bar f_t = \frac{m(t)}{P(t)}.
\end{equation}
At `t = \hat t`. We multiply by `\bar f_{\hat t}` to remove the weight
in two steps.

**Step 4.1 (weighted-to-unweighted on `\Sigma_{\hat t}`).** Suppose we
have established (we do so a posteriori in §6, then close a bootstrap)
\begin{equation}
\label{eq:bootstrap-hypothesis}
|\nabla u(x)| \ge \tfrac{1}{2} \bar f_{\hat t}
\quad \text{for all } x \in \Sigma_{\hat t}.
\end{equation}
Then `1/|\nabla u| \le 2/\bar f_{\hat t}`, so
\eqref{eq:dh-identity} multiplied by `\bar f_{\hat t}/2` gives
\[
\int_{\Sigma_{\hat t}} (|\nabla u| - \bar f_{\hat t})^2 \, d\mathcal H^{n-1}
\cdot \frac{1}{\| |\nabla u| \|_{L^\infty(\Sigma_{\hat t})}}
\le
\int_{\Sigma_{\hat t}}
\frac{(|\nabla u| - \bar f_{\hat t})^2}{|\nabla u|} \, d\mathcal H^{n-1}
= \frac{m(\hat t)}{P(\hat t)^2} D_H(\hat t),
\]
and `\| |\nabla u| \|_{L^\infty(\Sigma_{\hat t})} \le C_S(n, R, \rho_*)`
by \eqref{eq:schauder}. Hence
\begin{equation}
\label{eq:unweighted-variance}
\int_{\Sigma_{\hat t}} (|\nabla u| - \bar f_{\hat t})^2 \, d\mathcal H^{n-1}
\le \frac{C_S \, m(\hat t)}{P(\hat t)^2} D_H(\hat t)
\le C_4(n, R, \rho_*) \, D_H(\hat t).
\end{equation}
(`m(\hat t)/P(\hat t)^2` is bounded by \eqref{eq:perimeter-expand} and
\eqref{eq:lambda-range}.)

**Step 4.2 (rescaling to `\widetilde E`).** Using
`|Dv(y)| - \overline{|Dv|} = (n/\lambda) (|\nabla u(x_0 + \lambda y)| - \bar f_{\hat t})`
and the surface change of variable,
\[
\int_{\partial \widetilde E} (|Dv| - \overline{|Dv|})^2 \, d\mathcal H^{n-1}
= \frac{n^2}{\lambda^2} \cdot \lambda^{-(n-1)}
\int_{\Sigma_{\hat t}} (|\nabla u| - \bar f_{\hat t})^2 \, d\mathcal H^{n-1}.
\]
With \eqref{eq:unweighted-variance} and \eqref{eq:lambda-range}, the
prefactor is bounded by `C(n, \rho_*)`, so
\begin{equation}
\label{eq:variance-rescaled}
\int_{\partial \widetilde E} (|Dv| - \overline{|Dv|})^2 \, d\mathcal H^{n-1}
\le C_5(n, R, \rho_*) \, D_H(\hat t).
\end{equation}
Combining with \eqref{eq:mean-grad},
\begin{equation}
\label{eq:variance-from-1}
\int_{\partial \widetilde E} (|Dv| - 1)^2 \, d\mathcal H^{n-1}
\le 2 \int (|Dv| - \overline{|Dv|})^2 + 2 P(\partial \widetilde E) \bigl(\overline{|Dv|} - 1\bigr)^2
\le C_6(n, R, \rho_*) \bigl( D_H(\hat t) + \eta^2 \bigr).
\end{equation}

The bootstrap \eqref{eq:bootstrap-hypothesis} is justified at the end
of §6.

## 5. `L^2`–`C^\alpha` interpolation on a surface (audit G2)

We need the following standard interpolation; we give a proof to track
constants.

**Lemma 2 (interpolation).** Let `\Sigma \subset \mathbb R^n` be a
compact `C^{1}` embedded hypersurface with `(n-1)`-dimensional volume
`\mathcal H^{n-1}(\Sigma) \le V_0`. Let `f \in C^\alpha(\Sigma)`
(intrinsic Hölder seminorm) with `[f]_{C^\alpha(\Sigma)} \le M` and
`\|f\|_{L^2(\Sigma)} \le A`. Assume the surface satisfies a uniform
local volume-doubling bound:
\[
\mathcal H^{n-1}(\Sigma \cap B_r(x)) \ge c_V r^{n-1}
\quad \text{for all } x \in \Sigma, \; 0 < r \le r_0,
\]
with constants `c_V, r_0 > 0`. Then
\begin{equation}
\label{eq:interp}
\|f\|_{L^\infty(\Sigma)} \le C_7(n, c_V, r_0)
\, A^{2\alpha/(2\alpha + n - 1)}
\, M^{(n-1)/(2\alpha + n - 1)}.
\end{equation}

*Proof.* Let `x_0 \in \Sigma` with `|f(x_0)| = \|f\|_{L^\infty}`. For
`0 < r \le r_0`, every `y \in \Sigma \cap B_r(x_0)` satisfies
`|f(y) - f(x_0)| \le M |y - x_0|^\alpha \le M r^\alpha`. Hence
`|f(y)| \ge \|f\|_{L^\infty} - M r^\alpha` for such `y`. If
`r^\alpha \le \|f\|_{L^\infty}/(2M)`, then `|f(y)| \ge \|f\|_{L^\infty}/2`
on `\Sigma \cap B_r(x_0)`, so
\[
A^2
\ge \int_{\Sigma \cap B_r(x_0)} f^2 \, d\mathcal H^{n-1}
\ge \frac{\|f\|_{L^\infty}^2}{4} \cdot c_V r^{n-1}.
\]
Choosing `r := (\|f\|_{L^\infty}/(2M))^{1/\alpha}` (and assuming the
chosen `r \le r_0`, which holds whenever `\|f\|_{L^\infty}/(2M) \le r_0^\alpha`),
\[
A^2 \ge \frac{c_V}{4} \cdot \|f\|_{L^\infty}^2 \cdot
\left( \frac{\|f\|_{L^\infty}}{2M} \right)^{(n-1)/\alpha}.
\]
Solving for `\|f\|_{L^\infty}`,
\[
\|f\|_{L^\infty}^{2 + (n-1)/\alpha}
\le \frac{4 \cdot 2^{(n-1)/\alpha}}{c_V} \, A^2 \, M^{(n-1)/\alpha}
= C(n, c_V, \alpha) \, A^2 \, M^{(n-1)/\alpha},
\]
i.e. (multiplying exponents by `\alpha/(2\alpha + n - 1)`)
\[
\|f\|_{L^\infty}
\le C \, A^{2\alpha/(2\alpha + n - 1)}
\, M^{(n-1)/(2\alpha + n - 1)}.
\]
If instead `r > r_0`, i.e. `\|f\|_{L^\infty} > 2 M r_0^\alpha`, the rough
bound `\|f\|_{L^\infty} \le M (\operatorname{diam} \Sigma)^\alpha + A V_0^{-1/2}`
absorbs into \eqref{eq:interp} after raising to the appropriate power.
∎

(Audit G2 closed: the exponent on `A` is `2\alpha/(2\alpha + n - 1)`,
not `\alpha/(n - 1 + \alpha)`.)

**Geometric input for `\partial \widetilde E`.** By \eqref{eq:schauder}
and \eqref{eq:lambda-range}, `\partial \widetilde E` is a compact
`C^{3,\alpha}` embedded hypersurface with intrinsic curvature bound
`\|II\|_{L^\infty(\partial \widetilde E)} \le C(n, R, \rho_*)` and
diameter `\le 2R/\rho_* \le C(n, R, \rho_*)`. Standard differential
geometry: such a surface admits uniform local volume-doubling with
constants `c_V, r_0` depending only on `(n, R, \rho_*)`. (Take `r_0`
smaller than the reach of `\partial \widetilde E`, which is bounded
below by the inverse curvature bound.)

**`C^\alpha` bound on `|Dv|`.** Set `f := |Dv| - 1` on
`\partial \widetilde E`. From \eqref{eq:schauder} and the rescaling,
`v \in C^{3,\alpha}(\overline{\widetilde E})` with norm bounded by
`C(n, R, \rho_*)` (the prefactors `n/\lambda^2`, `n/\lambda` are
uniformly bounded by \eqref{eq:lambda-range}). Hence
`|Dv| \in C^{2,\alpha}` (one derivative loss because of the absolute
value: where `|Dv| \ne 0` it is `C^{2,\alpha}`; on `\partial \widetilde E`,
once we know `|Dv|` is bounded below away from zero by the bootstrap of
§6, the absolute value is irrelevant). Composing with the embedding of
`\partial \widetilde E` (a `C^{3,\alpha}` hypersurface) gives
\begin{equation}
\label{eq:M-bound}
[\, |Dv| - 1 \,]_{C^\alpha(\partial \widetilde E)}
\le \| |Dv| \|_{C^\alpha(\partial \widetilde E)}
\le C_8(n, R, \rho_*) =: M_0.
\end{equation}

## 6. Putting it together

Apply Lemma 2 to `f = |Dv| - 1` on `\Sigma = \partial \widetilde E`,
with `M = M_0` from \eqref{eq:M-bound} and
\[
A^2
:= \int_{\partial \widetilde E} (|Dv| - 1)^2 \, d\mathcal H^{n-1}
\le C_6 \bigl( D_H(\hat t) + \eta^2 \bigr) \le C_6 (\eta + \eta^2) \le 2 C_6 \eta
\]
(for `\eta \le 1`, using `D_H \le \eta`). The exponent in
\eqref{eq:interp} on `A` is `2\alpha/(2\alpha + n - 1)`; so on `A^2` it
is `\alpha/(2\alpha + n - 1)`. Therefore
\begin{equation}
\label{eq:Linfty-DH}
\bigl\| |Dv| - 1 \bigr\|_{L^\infty(\partial \widetilde E)}
\le C_7 \, (2 C_6 \eta)^{\alpha/(2\alpha + n - 1)} M_0^{(n-1)/(2\alpha + n - 1)}
\le C_9(n, R, \rho_*) \, \eta^{\alpha/(2\alpha + n - 1)}.
\end{equation}

**The clean final statement.**
\begin{equation}
\label{eq:Linfty-clean}
\boxed{
\delta := \bigl\| |Dv| - 1 \bigr\|_{L^\infty(\partial \widetilde E)}
\le C_{10}(n, R, \rho_*) \, \eta^\kappa,
\qquad
\kappa = \min\!\Bigl(\tfrac{1}{2}, \, \tfrac{\alpha}{2\alpha + n - 1}\Bigr).
}
\end{equation}

For `n \ge 2` and `\alpha \in (0, 1]`,
`\alpha/(2\alpha + n - 1) \le 1/(n + 1) \le 1/3 < 1/2`, so the
interpolation exponent is always the smaller one and
\[
\kappa = \frac{\alpha}{2\alpha + n - 1}.
\]

**Discharging the bootstrap \eqref{eq:bootstrap-hypothesis}.** By
\eqref{eq:Linfty-clean}, `\bigl| |Dv| - 1 \bigr| \le \delta` on
`\partial \widetilde E`, so `|Dv| \ge 1 - \delta` there. By
\eqref{eq:grad-rescale}, `|\nabla u| = (\lambda/n) |Dv| \ge (\lambda/n)(1 - \delta)`
on `\Sigma_{\hat t}`. And `\bar f_{\hat t} = (\lambda/n)(1 + r_P)^{-1} \le 2\lambda/n`
for `|r_P| \le 1/2`. So
\[
|\nabla u| \ge (\lambda/n)(1 - \delta) \ge \tfrac{1}{2} \bar f_{\hat t}
\]
holds for `\delta \le 1/4` and `|r_P| \le 1/2`. By
\eqref{eq:Linfty-clean}, `\delta \le 1/4` for
`\eta \le \eta_2(n, R, \rho_*)`. So the bootstrap closes for `\eta`
below a threshold depending only on `(n, R, \rho_*)`. Below that
threshold, the lower bound \eqref{eq:grad-lower} holds with
`c_1 = (\lambda/n)(3/4) \ge 3 \rho_*/(4n)`. ∎

## 7. Statement (Brandolini's hypothesis procured)

**Proposition 7.1.** Let `Ω ⊂ B_R` be a `C^{2,\alpha}` bounded open
set, `u` the torsion function (`-\Delta u = 1`, `u|_{\partial \Omega} = 0`).
Fix `\rho_* \in (0, 1)`. There exist `\eta_0 = \eta_0(n, R, \rho_*) > 0`
and `C = C(n, R, \rho_*)` such that the following holds. If
`\hat t \in A_*` is a regular level with
`D_H(\hat t) + D_I(\hat t) \le \eta \le \eta_0`,
then the rescaling `v` defined by \eqref{eq:v-def} satisfies
`\Delta v = n` in `\widetilde E`, `v = 0` on `\partial \widetilde E`,
`|\widetilde E| = \omega_n`, `\widetilde E \in C^{2,\alpha}`, and
\[
\bigl\| |Dv| - 1 \bigr\|_{L^\infty(\partial \widetilde E)}
\le C \, \eta^\kappa,
\qquad
\kappa = \frac{\alpha}{2\alpha + n - 1}.
\]

This is precisely Brandolini's hypothesis. Modulo the connectedness
reduction (audit G1) and the diameter bound on `\widetilde E`
(audit M2), Brandolini Theorem 2 applies and yields
\[
R_{\rm out}(\widetilde E) - R_{\rm in}(\widetilde E) \le C'' \eta^{\kappa \mu},
\qquad
|1 - R_{\rm in}|, \, |1 - R_{\rm out}| \le C'' \eta^{\kappa \mu},
\]
with `\mu = \mu(n) = 1/(2(4n + 9)(n-1))` from p. 1581–2 of
`brandolini.pdf`.

## 8. Constants summary

| Constant | Depends on | Source |
|---|---|---|
| `c_0` | `n, R, \rho_*` | dist bound \eqref{eq:dist-bound} |
| `C_S` | `n, R, \rho_*` | interior Schauder \eqref{eq:schauder} |
| `C_2, C_3` | `n, \rho_*` | perimeter expansion \eqref{eq:perimeter-expand} |
| `C_4, C_5, C_6` | `n, R, \rho_*` | variance bound \eqref{eq:variance-rescaled}-\eqref{eq:variance-from-1} |
| `c_V, r_0` | `n, R, \rho_*` | local doubling on `\partial \widetilde E` |
| `M_0 = C_8` | `n, R, \rho_*` | `C^\alpha` bound on `|Dv|` |
| `C_7` | `n, c_V, r_0`, hence `n, R, \rho_*` | interpolation Lemma 2 |
| `C_9, C_{10}` | `n, R, \rho_*` | final assembly |
| `\kappa` | `n, \alpha` | `\alpha/(2\alpha + n - 1)` |
| `\mu` | `n` | Brandolini, `1/(2(4n+9)(n-1))` |
| `\eta_0, \eta_1, \eta_2` | `n, R, \rho_*` | smallness thresholds |

All constants are independent of `\Omega` other than through
`(n, R, \rho_*)`.

## 9. Residual gaps (not closed here)

- **(G1, audit).** Connectedness of `E_{\hat t}` (equivalently
  `\widetilde E`). Required by Brandolini Theorem 2. Not closed
  here; addressed separately via a `D_I`-tentacle-exclusion argument.
- **(G5/G6, audit).** The output of Brandolini is annular squeeze, not
  `C^{2, \gamma_0}` smallness required by `NearlySphericalClosure`.
  An additional Schauder interpolation step (`C^{1,\gamma}` smallness +
  `C^{3,\alpha}` boundedness → small `C^{2,\gamma_0}`) is needed
  downstream; not addressed here.
- **(S1, audit).** Lemma 2.1 (annulus + connectedness ⇒ graph) needs a
  quantitative threshold compared against the `C^{1,\gamma}` norm of
  `\partial \widetilde E`. Independent of this note.
- **(M4, audit).** Cor 2.2's center `x_*` is the inscribed-ball
  center, not the barycenter. First-mode neutralization (translation
  to barycenter, of size `O(\eta^{\kappa\mu})`) is needed to feed
  Agent 3's (G0); not in scope here.
