# Agent 6 — Hybrid Route with Selected Collar

Plan 3 deployment, sub-task 6.

*Note: file assembled from the agent's full returned text (Write inside
the sub-agent was denied; content was relayed via the final message).*

## Output classification

**Pure Plan 2** for the deficit-identity step;
**Hybrid (Plan 2 + Plan 1)** for the regularity / closure step.

The hybrid route can be assembled rigorously **only as a conditional
theorem**, and only at the cost of replacing the actual torsion function
`u_Ω` by the torsion function `u_Ũ` of the BDV-selected minimiser `Ũ`.
Without that replacement, the interface step does not exist as a proved
statement. With the replacement, the route does not save any work that
Plan 1 is not already doing — it merely re-routes the closing step
through the level-set identity. It does **not** reduce sharpness loss
compared to pure Plan 1.

## Files used

1. `Plan 2/level-set-deficit-identity.md` — exact identity
   `δ_T(Ω) = ∫ (D_H + D_I) / (c_N m^{1-2/N}) dt`, profile-gap estimate,
   Lemmas 8.1–8.4.
2. `Plan 2/selected-boundary-layer-theorem.md` — Prop 1.1 (boundary-slab
   good level), Lemma 2.1 (asymmetry transfer), Lemma 3.1 (selected
   parallel surfaces), Theorem 4.1 (conditional closure).
3. `Plan 2/weighted-serrin-collar-reduction.md` — Input S is implied by
   quantitative isoperimetry on a selected collar; the true obstruction
   is boundary-deficit propagation; spectral counterexample on degree-`k≥2`
   harmonics.
4. `Plan 2/plan2.md` — §§5–7, §§11–12.
5. `Plan 2/concrete-next-steps.md` — §0 target theorem, §4 hybrid route.
6. `Final/SelectionPrinciple.tex` — Theorem 3.1 (single-set selection):
   produces `Ũ`, `|Ũ| = ω_N`, `α(Ũ) ≃ α(Ω)`, `Q_α(Ũ) ≤ C q`,
   BDV regularity package, rescaled Bernoulli law on `∂Ũ`.
7. `Final/GraphEntry.tex` — Theorem 5.1.
8. `Final/NearlySphericalClosure.tex` — Theorem 2.1.
9. `Final/BoundedReduction.tex`.
10. `Final/master.tex` — pipeline `S → G → I → N`.

## 1. The hybrid candidate, stated as a chain

**Input.** Bounded open `Ω ⊂ B_R`, `|Ω| = ω_N`, small `δ_T(Ω)`, `A(Ω)`.

1. **(S, Plan 1).** `SelectionPrinciple` ⇒ `Ũ`, `|Ũ| = ω_N`,
   `α(Ũ) ≃ α(Ω)`, `Q_α(Ũ) ≤ C q`, BDV regularity, rescaled Bernoulli.
2. **(P2, Plan 2).** Level-set identity
   `2 δ_T(Ũ) = ∫ (D_H + D_I) / (c_N m^{1-2/N}) dt` for `u_Ũ`.
3. **(BL, Plan 2 on selected `Ũ`).** Prop 1.1: for `0 < η < |Ũ|/4`,
   `δ_T(Ũ) ≤ c R² η`, ∃ regular `t_η` with `η ≤ |Ũ ∖ E_{t_η}| ≤ 2η`,
   `D_H(t_η) + D_I(t_η) ≤ C_n L^{2-4/N} δ_T(Ũ) / η`.
4. **(PS, Plan 1 regularity → parallel surfaces).** Lemma 3.1: for
   `0 < t < t_0`, `{ u_Ũ = t } = { y - (t/q(y)) ν_Ũ(y) + O(t^{1+γ}) : y ∈ ∂Ũ }`,
   `q = |∇u_Ũ| ∈ [q_-, q_+]`.
5. **(G, Plan 1).** `GraphEntry`.
6. **(N, Plan 1).** `NearlySphericalClosure`.
7. **(BR, Plan 1).** `BoundedReduction`.

## 2. The interface step (Plan 2 → Plan 1 inside the selected world)

The interface is between **Steps 3 and 4**.

**Interface Hypothesis IH.** `Ũ = { u_Ũ > 0 }`, with `u_Ũ` the torsion
function of `Ũ` (**not** of `Ω`). Assume the BDV regularity package:

- (IH1) `∂Ũ ∈ C^{1,γ}`, `‖∂Ũ‖_{C^{1,γ}} ≤ M(N, R)` after `GraphEntry`;
- (IH2) `0 < q_- ≤ |∇u_Ũ(y)| ≤ q_+` on `∂Ũ`,
  `[|∇u_Ũ|]_{C^γ(∂Ũ)} ≤ M`;
- (IH3) inward normal exponential map of `∂Ũ` is a `C^{1,γ}`
  diffeomorphism on a collar of depth `t_0(N, R)`.

**Interface Lemma I (proved, conditional on IH).** For `0 < t < t_0`,
`{ u_Ũ = t }` is the parallel surface:
\[ P(E_t) = P(\tilde U) + O(t^\gamma), \qquad
   |\tilde U \setminus E_t| = t \int_{\partial \tilde U} q^{-1} + O(t^{1+\gamma}), \]
\[ D_I(t) = D_I(0) + O(t^\gamma), \qquad
   D_H(t) = D_H(0) + O(t^\gamma), \]
with `D_I(0) := P(Ũ)² - c_N |Ũ|^{2-2/N}`,
`D_H(0) := (∫_{∂Ũ} q^{-1})(∫_{∂Ũ} q) - P(Ũ)²`.
This is `weighted-serrin-collar-reduction.md` §5.

### What IH gives, and what it does not

1. IH says **torsion levels of `Ũ`** are smooth parallel perturbations
   of `∂Ũ`. It says **nothing** about torsion levels of `Ω`.
   `u_Ω ≠ u_Ũ`.
2. IH gives no quantitative bound on `D_I(0) + D_H(0)` in terms of
   `δ_T(Ũ)`. The needed statement is
   \[ D_I(0) + D_H(0) \le C (E(\tilde U) - E(B_1)). \tag{$*$} \]
   This is **false in the nearly-spherical class**: on a degree-`k ≥ 2`
   spherical-harmonic perturbation `δ_T ∼ k ‖g_k‖_{L²}²`, while
   `D_I(0), D_H(0) ∼ k² ‖g_k‖_{L²}²`.
3. Without (*), the only quantitative passage gives Corollary 2.2:
   `A(Ũ)² ≤ C δ_rel^{1/2}` — the **wrong exponent**.

## 3. The hybrid theorem (rigorous version)

**Theorem (hybrid route, rigorous core).** Fix `N ≥ 2`, `R ≥ 2`.
There exist `α_hyb, q_hyb, C_hyb > 0` such that, for `Ω ⊂ B_R`,
`|Ω| = ω_N`, `α(Ω) ≤ α_hyb`, `Q_α(Ω) ≤ q_hyb`, the set
`Ũ = SelectionPrinciple(Ω)` satisfies:

(a) `|Ũ| = ω_N`, `α(Ũ) ≃ α(Ω)`, `Q_α(Ũ) ≤ C q`;

(b) (IH1)–(IH3) with constants depending only on `(N, R)`;

(c) for every regular `0 < t < t_0`, `{ u_Ũ = t }` is a `C^{1,γ}`
   parallel surface of `∂Ũ`, and `t ↦ D_I(t), D_H(t), P(E_t), |Ũ ∖ E_t|`
   extend continuously to `t = 0+` with Lemma 3.1 expansions;

(d) `A(Ω)² ≤ C δ_T(Ω)` holds **iff** the pure Plan-1 chain
   (`GraphEntry → SchauderInterpolation → NearlySphericalClosure`)
   closes, **independently** of the level-set identity.

(a)–(c) is genuinely new (parallel-surface picture on selected collar
with controlled traces). (d) is the honest verdict: at the sharp `A²`
exponent Plan 2 contributes no separate closing step.

### Where Plan 2 *does* add value
(i) Diagnostic identity with continuous boundary values.
(ii) Approximate-Serrin diagnosis:
    `∫_{Σ_t} (|∇u| - f̄)² / |∇u| = (m / P²) D_H`. Under IH2 this is
    ordinary `L²` oscillation, but no current Serrin theorem upgrades
    it to sharp `A² ≤ C δ_T` (would need (*), which fails).
(iii) Boundary-layer transfer Lemma 2.1 — just the symmetric-difference
    inequality.

## 4. Honest verdict

1. **Plan 1 selection is unavoidable.** Interface Lemma I needs the BDV
   regularity package, available only on `Ũ`.
2. **Once `Ũ` is selected, Plan 1 already closes the proof** via
   `S → G → SchauderInterpolation → N`. The level-set identity is never
   invoked.
3. **The level-set identity does not bypass the spectral obstruction.**
   (*) is false at degree-`k ≥ 2`; `NearlySphericalClosure` works
   because the `H^{1/2}` norm scales like `k`, matching `δ_T`.
4. **The interface "comparison between actual torsion levels and the
   selected minimiser's collar" reduces to `E_t = E_t`** because the
   torsion function used throughout is `u_Ũ`, not `u_Ω`. The hybrid
   silently substitutes `u_Ω → u_Ũ` — exactly the failure mode the brief
   warns about, and intrinsic to applying Lemma 3.1.
5. **A real Plan 2 → Plan 1 transfer from `u_Ω`-levels to `u_Ũ`-levels
   is itself a missing theorem.** It would require `d_H(∂Ω, ∂Ũ) → 0`
   (only after `GraphEntry`) plus a quantitative PDE comparison
   principle compatible with the sharp exponent. Not established
   anywhere in the listed files.

## 5. Hidden regularity assumptions

| Step  | Hidden assumption | Paid for by |
|-------|-------------------|-------------|
| BL    | `Ũ` has finite perimeter, regular levels a.e. | BDV Lemma 4.6 in `SelectionPrinciple.tex` |
| PS    | `∂Ũ ∈ C^{1,γ}` near every boundary point | BDV Lem 4.16 + Thm 4.18 via `GraphEntry` (NOT free for `Ω`) |
| PS    | `q = |∇u_Ũ| ∈ [q_-, q_+]` and `C^γ` on `∂Ũ` | BDV Lemma 4.16 (Bernoulli) |
| PS    | Normal exp. map is `C^{1,γ}` diffeomorphism on collar of depth `t_0` | `C^{1,γ}` + positive reach; needs `α(Ũ) ≤ α_graph` |
| Close | (*) boundary-deficit propagation, or equivalent `H^{1/2}` lower bound | NOT supplied by Plan 2; supplied directly by `NearlySphericalClosure` via BDV Theorem 3.3 |

None of these is discharged by an "A0"-type perimeter-free metric
Lipschitz argument; the route does **not** reuse that invalid argument.

## 6. Bottom line

The hybrid route can be **stated** as the Theorem in §3 with Interface
Lemma I as the explicit comparison step. It is **proved** modulo the
BDV regularity package on `Ũ` (established in
`Final/SelectionPrinciple.tex` + `Final/GraphEntry.tex`).

But the hybrid theorem is **strictly weaker than pure Plan 1**:
produces no new sharp inequality; does not avoid `GraphEntry` (the most
non-trivial Plan 1 step); its closing step is either (a) Plan 1's
`NearlySphericalClosure` (Plan 2 decorative) or (b) the conditional
Theorem 4.1 of `selected-boundary-layer-theorem.md`, which only delivers
non-sharp `A² ≤ C δ_T^{1/2}` and depends on an "Input S" that reduces
to quantitative isoperimetry.

The correct reading is **deliverable option 2**: this deliberate hybrid
does **not** genuinely simplify the proof. Remaining utility is
**diagnostic**: it identifies `D_I(0), D_H(0)` as the natural
boundary-trace quantities that fail to be controlled by torsion deficit
at sharp rate, and pinpoints degree-`k ≥ 2` harmonics as the spectral
obstruction.
