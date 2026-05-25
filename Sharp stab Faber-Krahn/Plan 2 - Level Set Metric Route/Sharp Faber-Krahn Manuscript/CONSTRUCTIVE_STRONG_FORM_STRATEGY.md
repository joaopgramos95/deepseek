# Constructive strong-form input via quantitative Serrin (Reilly/Weinberger)

**Purpose.** Replace the one non-constructive ingredient of the sharp Faber–Krahn
manuscript — the Fusco–Julin strong form, whose constant `κ(n)` is obtained by
contradiction (Fusco survey, Thm 5.4, pp. 38–41) — by a *truly quantitative*
theorem with a computable constant, valid for the torsion superlevel sets we
actually use. We do **not** reprove general-set Fusco–Julin (that is where the
compactness lives); we get the shape control natively, via integral identities
for the torsion function. This is the overdetermined-problem (Serrin/Alexandrov)
circle, which is constructive.

---

## Execution status (2026-05-25)

The manuscript has been patched in `main.tex` as a conditional constructive
version:

- The old Fusco-Julin strong-form theorem is no longer a live dependency in the
  compiled manuscript.  It is replaced by `Assumption~\ref{ass:constructive-strong}`.
- The required input is stronger than the first draft of this strategy said: it
  must give **same-centre volume plus normal control** for one centre `z_rho`,
  namely `|E_rho Delta B_rho(z_rho)|^2 + int_{partial*E_rho}|nu-e_z|^2 <=
  C(D_H+D_I)`.  Normal control alone is not enough for the radial-trace lemma.
- The sign convention is corrected: for `v=u-t(rho)` on `E_rho`, one has
  `v>0`; weighted Reilly identities must use the positive torsion weight `v`,
  not `(-v)`.
- The bounded-reduction seed now uses only the ordinary constructive Fraenkel
  quantitative isoperimetric inequality (Fusco-Maggi-Pratelli), not the strong
  Fusco-Julin input.
- The route is **not closed** until the constructive Serrin input is proved with
  computable constants and with the same-centre conclusion above.  Claude should
  treat the current manuscript as conditional and audit exactly this remaining
  assumption.

---

## 0. Success criterion (what we must produce)

A theorem of the following shape, with **explicitly computable** `C`, is the
minimum needed by the manuscript:

> **(Constructive same-centre shape control.)** There are computable
> `C = C(n,R,rho_*) > 0` and `eta_0 = eta_0(n,R,rho_*) > 0` such that for a.e.
> good level `rho` with `D_H(t(rho)) + D_I(t(rho)) <= eta_0`, there is one centre
> `z = z_rho` satisfying the **same-centre** estimate
> `|E_rho Delta B_rho(z)|^2
>  + int_{partial* E_rho} |nu_rho - e_z|^2 dH^{n-1}
>    <= C (D_H(t(rho)) + D_I(t(rho)))`,
> where `e_z = (x-z)/|x-z|`, and no step uses compactness or contradiction.

The volume term is not cosmetic: `lem:oriented-radial-trace` consumes volume
closeness and normal closeness about the **same centre**.  A normal-only Serrin
output, plus a separate FMP Fraenkel centre, does not by itself identify the
centres strongly enough.

This is exactly the input the radial-trace lemma (`lem:oriented-radial-trace`)
turns into the homothetic-trace bound `\int|H_{z,\rho} - \bar V_\rho| \le
C(D_H+D_I)^{1/2}`, i.e. the content of the same-centre package
`inp:samecenter`. Note we may control the oscillation by `D_H` (or
`D_H+D_I`); both sit in the budget `\int(D_H+D_I)\,d\mu \le C\delta_T`, so either
suffices. **Linearity in the defect is essential** (a sub-linear power breaks the
kinetic estimate, as the Fraenkel-only route shows).

---

## 1. The linchpin: each superlevel set carries its own torsion function

On a regular level set `v := u - t(\rho)` solves
`-\Delta v = 1` in `E_\rho`, `v = 0` on `\partial E_\rho`, `v > 0` inside; so
**`v` is the torsion function of `E_\rho`**, and `|\nabla v| = |\nabla u|` on
`\partial E_\rho`. Hence:

- "`\partial E_\rho` is close to a sphere" = quantitative Serrin/Alexandrov for `E_\rho`;
- the smallness parameter is the **oscillation of `|\nabla v|` on `\partial E_\rho`**,
  which is the Cauchy–Schwarz defect `D_H(t(\rho))`
  (recall `D_H = (\int 1/|\nabla u|)(\int |\nabla u|) - P(E_\rho)^2`, the weighted
  variance of `|\nabla u|` on `\partial^* E_\rho`).

So the strong form, restricted to our sets, is a *stability statement for the
overdetermined torsion problem* — and that has explicit-constant proofs.

---

## 2. Primary method: Reilly identity + Weinberger P-function

Weinberger's proof of Serrin's theorem (rigidity) and its quantitative
refinements (Brandolini–Nitsch–Salani–Trombetti 2008; Magnanini–Poggesi 2019–20)
are integral-identity arguments — **no compactness, computable constants**.

### 2.1 The deviation functional

For `v` the torsion function of a (smooth) domain `\Omega'` (here `\Omega' = E_\rho`),
`-\Delta v = 1`, set the **Hessian deviation**
```
   Dev(Ω') := ∫_{Ω'} | D²v + (1/n) I |² dx  ≥ 0,
```
which is `0` iff `D²v ≡ -(1/n)I`, i.e. `v = (R'^2 - |x-z|²)/(2n)` and `Ω'` is a
ball `B_{R'}(z)`. (Identity used: `|D²v+\tfrac1n I|² = |D²v|² + \tfrac2n\Delta v +
\tfrac1n = |D²v|² - \tfrac1n` since `\Delta v=-1`.) `Dev` is the bulk distance to
"being a ball."

### 2.2 The Reilly / P-function identity (concretely)

The Weinberger `P`-function `P := |\nabla v|² + \tfrac2n v` satisfies
`\Delta P = 2(|D²v|² - \tfrac1n) = 2\,|D²v+\tfrac1n I|²`, so integrating,
```
   2 Dev(Ω') = ∫_{Ω'} ΔP dx = ∫_{∂Ω'} ∂_ν P dH^{n-1}.        (★)
```
On `∂Ω'` (where `v=0`, hence `\nabla v = -|\nabla v|\nu`), a direct computation
using `v_{νν} = -1 + H_∂ |\nabla v|` (from `\Delta v = v_{νν}+H_∂ v_ν = -1`,
`H_∂ =` sum of principal curvatures) gives
```
   ∂_ν P = 2(1 - 1/n)|\nabla v| - 2 H_∂ |\nabla v|².            (★★)
```
So `(★)` reads `Dev(Ω') = (1-\tfrac1n)\int_{∂Ω'}|\nabla v| - \int_{∂Ω'} H_∂|\nabla v|²`.
For the ball `|\nabla v|≡c`, `H_∂≡(n-1)/R'`, both sides vanish.

**The crux (curvature term).** `(★★)` contains the mean curvature `H_∂`, which we
do not control directly. This is exactly the technical knot Magnanini–Poggesi
resolve. Two known devices, both explicit:
- **Weighted identity.** Run Reilly with the positive weight `v >= 0` (vanishing on
  `∂Ω'`), which kills the boundary curvature term and yields
  `int_{Omega'} v |D^2v+(1/n)I|^2 <= C\, (\text{oscillation of } |\nabla v| \text{ on } ∂Ω')`
  (Magnanini–Poggesi, Indiana 2020). The weight is harmless: `v \asymp` the
  boundary-layer height, recoverable on a collar.
- **Heintze–Karcher / Newtonian-potential comparison.** Subtract the harmonic
  function with the same boundary trace of `|\nabla v|` to remove `H_∂`.

The target after this step:
```
   L1  (Reilly bound).   Dev_w(E_rho) := int_{E_rho} v |D^2v+(1/n)I|^2 dx
                          <= C(n) * Osc_{partial E_rho}(|grad v|),
   where Osc is an explicit L²-oscillation of |∇v| on ∂E_ρ, and
   Osc_{∂E_ρ}(|∇v|) ≤ C(n,ρ_*,R) · D_H(t(ρ)).               (to be pinned down)
```
The identification `Osc ≍ D_H` is plausible because both are the variance of
`|\nabla v|=|\nabla u|` on the level surface; matching the exact constant (and the
weight `v`) is computation, not compactness.

### 2.3 From bulk deviation to normal oscillation

`Dev_w(E_ρ)` small forces `v` to be `H²`-close (weighted) to the ball profile,
hence `\nabla v` close in `H¹` to the radial field, hence on the level surface the
normal `\nu = -\nabla v/|\nabla v|` is `L²`-close to radial:
```
   L2  (trace step).  ∫_{∂*E_ρ} |ν_ρ - e_z|² dH^{n-1}
                      ≤ C(n,R,ρ_*) · Dev_w(E_ρ),
   with z the centre of the best-fitting ball profile (the point where
   D²v ≈ -(1/n)I), via a coarea/trace argument on good levels.
```
Chaining `L1 + L2` gives the success criterion (with `D_H`, hence
`\le D_H + D_I`). The constant is the product of explicit constants.

**Why this beats de-compactifying GMT.** `(★)` is an *identity* ⇒ the dependence
on the defect is **linear**, with an explicit constant; and it is a **bulk**
statement in `D²v`, so it never needs a pointwise lower bound `|\nabla u| \ge c`
on the level set — it sidesteps the gradient non-degeneracy wall that the
moving-ball route was built to avoid.

---

## 3. The make-or-break first computation

Before anything else, settle **L1** in clean form:

> **Lemma (to prove first).** Let `Ω' ⊂ R^n` be bounded with `C²` boundary,
> `v` its torsion function. Then with `H_∂` the boundary mean curvature and
> `\bar c := P(B_{Ω'})/P(Ω')`-type reference value fixed by Pohozaev,
> ```
> ∫_{Ω'} v\,|D²v + (1/n) I|² dx
>    ≤ C(n) ∫_{∂Ω'} (|∇v| - \bar c)²  dH^{n-1},
> ```
> with `C(n)` explicit, using only Reilly's identity, the Pohozaev identity
> `((n-2)/2)∫|∇v|² + (1/2)∫_{∂}((x-z)·ν)|∇v|² = (\text{vol terms})`, and
> Cauchy–Schwarz. No compactness.

Then identify `∫_{∂E_ρ}(|∇v|-\bar c)² dH` with `D_H(t(ρ))` up to a factor
controlled by the a priori bounds `|\nabla u| \le K_n R` (Talenti) and the
good-level perimeter bounds. If this lemma holds with a **linear** constant, the
whole program closes modulo the (routine) trace step L2 and bookkeeping.

**Pohozaev's role.** It pins the correct reference value `\bar c` (the "Serrin
constant" `|\nabla v|` would have on the ball of the same torsion) explicitly, so
the oscillation `(|\nabla v| - \bar c)` is measured against a computable target —
this is what makes the constant explicit rather than implicit.

---

## 4. Architecture integration

- **Volume closeness** from the ordinary Fraenkel inequality is constructive, but
  it may be centred at a different point from the Serrin/Reilly centre.
- **Shape/normal closeness** comes from L1+L2 (constructive, `D_H`-driven),
  replacing the Fusco-Julin call inside the same-centre package.
- **Same-centre requirement.** The constructive theorem must either produce
  `|E_rho Delta B_rho(z)|^2` for the Reilly centre, or prove a separate explicit
  centre-alignment lemma strong enough to transfer the FMP volume centre to the
  Reilly centre before applying the radial trace lemma.  The later
  `lem:center-transfer` only transfers from the same-centre package to the
  minimising centre; it does not repair a missing same-centre input.
- **Net effect.** `c_{FK}(n)` becomes a product of: the De Giorgi/truncation
  constants (explicit), the Kohler–Jobin constants (explicit), the FMP Fraenkel
  constant (explicit), and the new Reilly/Pohozaev constant `C(n,R,\rho_*)`
  (explicit). **No `κ(n)` from contradiction remains.**

---

## 5. Risks and mitigations

| Risk | Where | Mitigation |
|---|---|---|
| Curvature term `∫_∂ H_∂\|∇v\|²` in (★★) | L1 | weighted `v` Reilly / Newtonian-potential subtraction (Magnanini–Poggesi); both explicit |
| Rate degradation (bulk → shape) | L2 | (★) is an identity ⇒ linear; keep the weighted form so the trace stays `L²`; verify the power survives |
| Uniformity of `C` in `rho` | L1,L2 | restrict to good levels `G_sc`; use Talenti `||grad u||_infty <= K_n R` and perimeter bounds from `D_H+D_I <= eta_Ser`; the positive weight `v` collar must be uniform on the outer collar `[rho_c,1]` |
| a.e.-level regularity of `∂E_ρ` | both | regular values (analytic `u`) give `C^\infty` level sets a.e.; integral identities are stable under the coarea null-set passage already used |
| Matching `Osc(|∇v|) ≍ D_H` exactly | L1 | both are the variance of `|\nabla u|`; compute the constant via Cauchy–Schwarz, using `\bar V_\rho` as the reference |
| Connectedness of `E_ρ` | L1 | Serrin identities are additive over components; small deficit forces one dominant component (volume bound) and charges the rest to the budget |

The **only** genuine mathematical crux is L1 (the curvature handling and the
linear constant); everything downstream is bookkeeping. L1 is a known technique
applied to a new domain (`E_ρ` instead of `∂Ω`), so the risk is "constant
chasing," not "new idea needed."

---

## 6. Alternative methods (fallbacks / cross-checks)

- **Plan B — constructive ε-regularity.** De-compactify Cicalese–Leonardi/FJ:
  build the penalized almost-minimizer `F` (direct method, explicit), then use a
  *quantitative* De Giorgi/Allard excess-decay (explicit `ε_0`, decay rate) to
  get `C^{1,α}`-closeness to a sphere, then Fuglede. Riskier: needs
  excess-to-deficit smallness made explicit, and the almost-minimizer regularity
  constants are heavier; but it is a pure GMT route independent of the PDE, useful
  as a cross-check.
- **Plan C — mass transport for the normal.** Extend the Figalli–Maggi–Pratelli
  transport proof (which gives the Fraenkel form constructively) to also control
  the normal direction via the trace of `DT`. Speculative; flag as exploratory.
- **Plan D — accept non-sharp constructive exponent.** If L1 stalls, ship the
  fully-constructive non-sharp theorem `\delta_T \gtrsim \mathcal A^{2n/(n-1)}`
  (FMP-only) as a self-contained alternative, keeping the sharp theorem with the
  `κ(n)` caveat. Guaranteed fallback.

---

## 7. References

- H. Weinberger, *Remark on the preceding paper of Serrin*, ARMA 43 (1971). (P-function rigidity.)
- R. Reilly, *Applications of the Hessian operator in a Riemannian manifold*, Indiana Univ. Math. J. 26 (1977). (Reilly's identity.)
- S. Pohozaev / F. Rellich identities (standard).
- L. Brandolini, C. Nitsch, P. Salani, C. Trombetti, *On the stability of the Serrin problem*, J. Differential Equations 245 (2008). **[in repo: `Plan 3 .../References/brandolini.pdf`]**
- R. Magnanini, G. Poggesi, *On the stability for Alexandrov's Soap Bubble theorem*, J. Anal. Math. 139 (2019); *Serrin's problem and Alexandrov's Soap Bubble Theorem: stability via integral identities*, Indiana Univ. Math. J. 69 (2020). (Quantitative Serrin via Reilly, explicit constants.)
- B. Fuglede, *Stability in the isoperimetric problem for convex or nearly spherical domains*, TAMS 314 (1989). (Explicit nearly-spherical inequality — final polish.)
- Fusco survey, *The quantitative isoperimetric inequality and related topics* (Thm 5.4 = the strong form we are replacing; §3.1 Fuglede; §4, §5.1 the constructive Fraenkel proofs).

## 8. Repo assets to reuse

- `Plan 3 - Graph and Planar Routes/Blocks/Route B Weinberger/` — existing Weinberger-route material.
- `Plan 3 .../References/brandolini.pdf` — Serrin-stability paper.
- `Plan 5 - Inset Regularity and Geometric Flow/Ideas/Serrin Discussion/` — prior Serrin scoping.
- `Sharp Faber-Krahn Manuscript/` — `lem:oriented-radial-trace` (consumes the output), `lem:center-transfer` (centre reconciliation), `prop:levelset` (budget), `lem:velocity` (the `D_H` weighted-variance identity to match `Osc`).

---

## 9. Milestones

1. **M1 (settle L1).** Prove the make-or-break lemma of §3 for a `C²` domain with
   an explicit linear constant; identify `Osc(|∇v|) ≍ D_H`. *Self-contained;
   verify in isolation, then by adversarial agent pass.*
2. **M2 (trace step L2).** Bulk deviation → `\int|\nu-e_z|²` on `\partial E_ρ`,
   uniform on good levels.
3. **M3 (assemble).** State the constructive shape-control theorem (success
   criterion of §0); slot it in place of the Fusco–Julin call; reconcile centres.
4. **M4 (constant audit).** Trace `c_{FK}(n)` end-to-end; confirm no
   contradiction-derived constant survives.
5. **M5 (manuscript).** Replace the strong-form input; update the dependency
   certificate to "fully constructive"; re-verify and recompile.

**Start at M1** — it is the single point of failure and is a contained
computation.
