# Final Countdown — Pressure-Point Verification Report

**Source of truth:** `Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex`
(1297 lines; compiles).
**Mode:** hostile, manuscript-grade, line-by-line. Report only — no source edits.
**Date:** 2026-05-25.

---

## Consolidated verdict: **PASS**

Every one of the six pressure points survives line-by-line scrutiny. No blocking
issue invalidates the affine shell estimate, Theorem `qplus`, the positive
kinetic estimate, or the final sharp square rate. No patch is required for any
audited item (the MINOR items from the prior audit are already in the file:
the `2η∫1/|∇u|` error measure, the rational countable registration, the
`B_{R+1}` shell cutoff, the ball–ball lower bound proof, the explicit
center-transfer triangle inequality).

**Certification status: certified closed** — for the moving-ball machinery that
this file is responsible for. The two ingredients the file explicitly *imports*
rather than proves (see "Scope / standing dependencies") are out of scope for
these six pressure points and are individually accounted for.

---

## Pressure-point summary

| # | Pressure point | TeX | Verdict |
|---|----------------|-----|---------|
| 1 | Variable-thickness coarea (`varcoarea`)        | L622–689   | PASS |
| 2 | Shell-admissible radii                          | L691–744   | PASS |
| 3 | Local BV deformation tail (`BV-tail`)           | L746–796   | PASS |
| 4 | Affine shell estimate (`shell`)                 | L800–945   | PASS |
| 5 | One-sided first variation (`qplus`)             | L947–995   | PASS |
| 5 | Positive kinetic bound (`positivekinetic`)      | L1093–1146 | PASS |

---

## Phase 1 — Variable-thickness coarea (`varcoarea`)

**Verdict: PASS. Blocking: none. Major: none.**

1. Constant-slab identity is the BV coarea formula applied to
   `1_{A_j}·1_{|∇u|>0}/|∇u|` (write `1 = |∇u|^{-1}·|∇u|` on the slab and
   integrate); legitimate after the null critical set is discarded. ✓
2. Critical-set discard valid: `−Δu=1` makes `u` real-analytic in the interior
   of each component; an open set has ≤ countably many components; on each, the
   real-analytic `∇u` cannot vanish on a positive-measure set without vanishing
   identically (excluded by `−Δu=1`). So `|{∇u=0}|=0`. ✓
3. Negative `p,q` and straddling intervals: `[s+hp_j, s+hq_j] ⊂ [s+h·min p,
   s+h·max q] → {s}`; one- and two-sided shrinking intervals converge at a
   Lebesgue point of `τ ↦ ∫_{∂*{u>τ}} 1_{A_j}/|∇u|`, which is `L¹(0,M)` because
   its integral over `τ` is `≤ |A_j| < ∞`. ✓
4. Simple-function step uses Borel partitions: coarea holds for any nonnegative
   Borel integrand, and `A_j` are Borel cells. ✓
5. **Bounded-Borel approximation uses the correct error measure.** Outer
   sandwich yields the error `2η ∫_{∂*{u>s}} 1/|∇u| dH^{n-1}`, i.e. `dH/|∇u|`,
   never `P` alone. ✓ (this is the B2 fix, now correct).
6. One fixed exceptional null set per `(α,β)`: bounded `α,β` quantised to dyadic
   mesh `2^{-m}` give finitely many cells (boundedness) ⇒ finite union of
   Lebesgue-point null sets per `m`; countable union over `m` is null and
   depends only on `(α,β)`. ✓
7. No pointwise lower bound on `|∇u|`: only integrability of `1/|∇u|` on the
   reduced boundary at the used levels (the stated finiteness hypothesis) and
   measure-zero discard of `{∇u=0}`. ✓

**Patch suggestions:** none.

---

## Phase 2 — Shell-admissible radii

**Verdict: PASS. Blocking: none. Major: none.**

1. `𝒰` (finite unions of rational balls with closure `⋐Ω`) is countable and
   cofinal for compacts. ✓
2. Registered pairs are bounded Borel: `∇u` is continuous on `U⋐Ω`, so
   `∇u·(λ(x−z)+a)` is continuous and bounded on the bounded set `U`; `1_U`
   makes it bounded Borel on `ℝⁿ`. ✓
3. Parameters `c,p,q,λ,r∈ℚ`, `z,a∈ℚⁿ`, `U∈𝒰`: countable, independent of `ρ`. ✓
4. Real `(z,a,ρ)` reached: `λ≈1/ρ∈[1,ρ_*^{-1}]` (since `ρ∈[ρ_*,1]`), `c≈−w∈
   [−1/n,0]⊂[−1,0]`; the buffer `r↓0` absorbs rational→real and the `o(h)`
   Taylor error. ✓
5. **Pullback through the monotone AC map `t` is rigorous.** For a null `N`, the
   change-of-variables/area formula for AC monotone `t` gives `∫ 1_N(t(ρ))|t'|dρ
   = |N ∩ range(t)| ≤ |N| = 0`; on `G_τ`, `w=|t'|≥τ_0`, so `|{ρ∈G_τ: t(ρ)∈N}| ≤
   τ_0^{-1}∫ 1_N(t)w\,dρ = 0`. Flat parts of `t` carry `w<τ_0`, hence lie in
   `B_τ` (excluded), and contribute `|t'|=0` to the area formula anyway. ✓
6. Critical-boundary condition for a.e. level: `∫_0^M H^{n-1}(∂*{u>s}∩{∇u=0})ds
   = ∫_{{∇u=0}}|∇u| = 0`. Finite-perimeter and flux conditions hold a.e. by BV
   coarea and the FP level-set package. ✓

**Patch suggestions:** none. (See standing dependency note on
`∂*E_ρ ⊂ Ω` for positive levels, which is supplied by the companion FP package,
not re-derived here.)

---

## Phase 3 — Local BV deformation tail (`BV-tail`)

**Verdict: PASS. Blocking: none. Major: none.**

1. `T_h=id+hW` is a `C¹` diffeomorphism on the fixed ball for `‖hDW‖<1`. ✓
2. `x=T_h y`: Jacobian `det(I+hDW)=1+o(1)`; integrand becomes
   `|1_E(y)−1_E(T_h y)|`. ✓
3. `u_ε=1_E*φ_ε → 1_E` in `L¹_loc`; both composed terms converge at fixed `h`
   (bounded Jacobian), so the mollified integral → the indicator integral. ✓
4. FTC bound `|u_ε(T_h y)−u_ε(y)| ≤ |h|∫_0^1 |∇u_ε(y+θhW)||W| dθ`. ✓
5. `y ↦ y+θhW(y)` uniformly bi-Lipschitz over `θ∈[0,1]` for small `h`. ✓
6. After change of variables `x=y+θhW(y)` and Fubini in `θ`, the weights `ψ_h`
   are continuous, compactly supported, uniformly bounded, and `ψ_h → η|W|`
   uniformly (since `Φ_θ^{-1}→id` uniformly in `θ`). ✓
7. `∫ψ_h|∇u_ε| → ∫ψ_h d|D1_E|` by strict `BV_loc` convergence of mollifications
   + Reshetnyak continuity for the continuous compactly supported weight. ✓
8. Reshetnyak used in the correct direction, only for continuous weights, and
   only to obtain an **upper** bound (no lower-semicontinuity passage). ✓
9. Limit order `ε→0` (fixed `h`) then `limsup_{h→0}` is respected; the `o_h(1)`
   factor is `ε`-independent. ✓
10. Output `∫_{∂*E} η|W| dH^{n-1}` with constants independent of any exhaustion;
    strong enough for the shell tail. ✓

**Patch suggestions:** none.

---

## Phase 4 — Affine shell estimate (`shell`)

**Verdict: PASS. Blocking: none. Major: none.** This is the crux; all 13 sub-checks pass.

1. `K` from inner regularity of the finite measure
   `(w/|∇u|+|W|+|w/|∇u|−W·ν|)H^{n-1}⌞∂*E` (each term integrable at admissible
   `ρ`). ✓
2. `K⊂U⋐Ω` by cofinality of `𝒰`. ✓
3–4. `u∈C¹` on `Ū`; `T_h^{-1}(x)=x−hW(x)+O(h²)` and
   `u(T_h^{-1}x)=u(x)−h∇u·W+o(h)`, both uniform on `U` (affine `T_h`, uniformly
   continuous `∇u`). ✓
5. Threshold signs correct: `x∈E_{ρ+h} ⟺ u>t(ρ)−hw+o(h)`;
   `x∈T_h(E) ⟺ u>t(ρ)+h∇u·W+o(h)`. ✓
6. **Two-sided slab and registered inclusion.** The local symmetric difference
   sits in `{h·min(−w,∇u·W)+o(h) < u−s < h·max(−w,∇u·W)+o(h)}` (thickness
   `h|w+∇u·W|`). With `|c+w| + sup_U|∇u·(λ(x−z_0)+a_0)−∇u·W| ≤ δ` and `r>2δ`,
   the registered slab `[min(c,g_0)−r, max(c,g_0)+r]` contains it for small `h`
   (the buffer beats both `δ` and the `o(h)/h=o(1)` error). The earlier false
   one-sided containment is gone — this is the genuinely two-sided version. ✓
7. `varcoarea` on the registered pair gives `∫_{∂*E∩U}(|c−g_0|+2r)/|∇u|`; as
   `δ,r↓0`, `→ ∫_{∂*E∩U}|w+∇u·W|/|∇u|` by dominated convergence. ✓
8. Local coarea limit is exactly `∫_{∂*E∩U}|F|/|∇u|`, `F=w+∇u·W`. ✓
9. Level-set tail: exact `|E_{ρ+h}\E|=ω_n((ρ+h)^n−ρ^n)=h·P(B_ρ)+o(h)
   =h·w∫_{∂*E}1/|∇u|+o(h)` (flux identity), minus the localized
   `w∫_{∂*E∩U}1/|∇u|`, gives `≤ w∫_{∂*E\K}1/|∇u|`. ✓
10. Affine tail: `(E Δ T_h E)\U ⊂ \overline{B_{R+1}}\U ⊂ {η=1}` (since
    `T_h(E)⊂B_{R+1}`), with `η=0` near `K`; `BV-tail` gives `≤ ∫_{∂*E\K}|W|`. ✓
11. Both tails `≤ ε` by the inner-regularity choice of `K`; sum `≤ 2ε`. ✓
12. Set decomposition `(E_{ρ+h}ΔT_h E) ⊂ [∩U] ∪ [(E_{ρ+h}ΔE)\U] ∪
    [(EΔT_h E)\U]`; subadditive limsup then `ε↓0`. ✓
13. Identification: `ν_ρ=−∇u/|∇u|`, `W·ν_ρ=H_{z,ρ}+a·ν_ρ`, so
    `F/|∇u| = V_ρ − W·ν_ρ = V_ρ − H_{z,ρ} − a·ν_ρ`. Sign correct. ✓

**Patch suggestions:** none.

---

## Phase 5 — Downstream propagation (`qplus`, `positivekinetic`)

**Verdict: PASS. Blocking: none. Major: none.**

1. Minimiser of `z↦|E_ρΔB_ρ(z)|` exists (continuous; `→2|E_ρ|` for `|z|>R+ρ`). ✓
2. `T_h(B_ρ(z_ρ))=B_{ρ+h}(z_ρ+ha)` exactly (the shell map is built with the
   ball centre `z=z_ρ`). ✓
3. `|T_h(E_ρ)ΔT_h(B_ρ(z_ρ))|=(1+h/ρ)^n q(ρ)`. ✓
4. At differentiability points `D^+q=q'`. ✓
5. RHS of `qplus` is nonnegative, so it bounds `q'_+=max(q',0)`. ✓
6. `dρ ≤ τ_0^{-1} dμ` only on `G_τ` (`w≥τ_0`). ✓
7. Bad sets paid by measure: `|J∩B_τ|≤Cδ_T` (badtau); `|J∩G_τ∩G_I^c| ≤
   τ_0^{-1}μ(G_I^c) ≤ (C/η_I)∫D_I dμ ≤ Cδ_T` (budget); `q'_+≤2nω_n` (qLip);
   so `∫_𝓑(q'_+)² ≤ Cδ_T`. ✓
8. No rescaled-metric estimate is reintroduced; the bound is `(q'_+)² ≤
   C(D_H+D_I)` on `G` via `q²≤CD_I` (FJ), velocity (`∫|V−V̄|≤D_H^{1/2}`) and
   center-transfer (`∫|H−V̄|≤CD_I^{1/2}`), then the budget. ✓

The endpoint trace (`endpoint`) and `boundedSV` then close the square rate via
Cauchy–Schwarz on `∫_J(q'_+)²` plus the mean-value pick of `ρ_0∈J` and the
superlevel→domain asymmetry transfer; consistent, no new pressure point.

**Patch suggestions:** none.

---

## Minor findings

- **None requiring a patch.** All MINOR items from the prior audit are already
  applied in the current file.

## Passed checks (summary)

- The coarea machinery is two-sided, uses `dH/|∇u|` as the error measure, and
  never assumes `|∇u|≥c>0`.
- The countable rational registration genuinely makes the a.e. statement
  uniform over the radius, and the AC-pullback through `t` is correct including
  flat parts.
- The shell estimate's interior/tail split is sound: interior by localized
  registered coarea, level-set tail by exact volume minus localized shell,
  affine tail by `BV-tail` with the correct cutoff; signs all correct.
- The kinetic estimate pays good levels by the budget and bad levels by measure
  using only the nestedness Lipschitz bound for `q`.

---

## Scope / standing dependencies (not pressure points; individually accounted)

This audit certifies the **moving-ball machinery** (the six pressure points).
The file explicitly imports, rather than re-derives, two things:

1. **Exact level-set deficit identity + FP superlevel package**
   (`eq:imported-levelset-identity`, and the a.e.-level facts: finite perimeter,
   `∂*E_ρ⊂Ω` for `t>0`, flux identity `∫_{∂*{u>t}}|∇u|=m(t)`). These are proved
   in the companion `Blocks/Level Set Identity/LevelSetIdentity.tex` (separately
   audited PASS). For this file they are a named import, by design.
2. **Published theorems**, cited in the needed form: Fusco–Julin `[FJ2014]`
   (used in its exact same-centre form), BV coarea / finite-perimeter
   Gauss–Green / strict-`BV` convergence / Reshetnyak continuity `[AFP2000,
   Maggi2012]`.

Modulo these explicit imports, the route is internally complete and the square
rate `𝓐(Ω)² ≤ C δ_T(Ω)` follows.

---

## Certification status

```
certified closed
```

— for the audited moving-ball pressure points, with the level-set identity and
the cited published theorems as the explicit, named external inputs.
