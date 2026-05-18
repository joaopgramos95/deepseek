# n=2 graph route, regularity-free — OBSTRUCTED

(Summary of an agent result that was returned inline only — Write was
sandbox-blocked at the time, so this file reconstructs the verdict
faithfully, with the skeptical correction applied. Reconstruction, not
the original verbatim deliverable.)

## Question
In `n=2`, exploiting the 2D structure (`u_p=-(x²+y²)/4`, `h=u-u_p`
harmonic, `φ=h_x-ih_y` holomorphic, `R=2∫|φ'|²` = holomorphic Dirichlet
energy): does near-Serrin `L²` on a level curve give a small-norm graph
over a circle, with constant depending only on `θ` and absolute —
**without** any `∂Ω`-regularity (no Part-A premise)?

## Verdict: OBSTRUCTED for every graph norm strictly above `L^∞`
- **Regularity-free, only `L^∞`/inner–outer-radius closes**: near-Serrin
  `≤θ` ⇒ concentric discs with `r_e-r_i ≤ Cθ^{1/2}` (`C` absolute; a
  harmless `log` in the literal `L^∞` form). Interior Hessian rigidity
  also has an absolute Cauchy constant `(2π)^{-1/2}`.
- **Explicit analytic counterexample** to any stronger norm: a localized
  bump family `Σ_{a,λ}` (`a=θ^{1/2}/\log(1/λ)^{1/2}`, width `λ→0`,
  Serrin defect `≡θ` fixed) with `‖g‖_{C¹}, ‖g‖_{H¹}, κ_{max} → ∞`.
  So near-Serrin does **not** yield a small `C¹`/`H¹`/curvature graph
  regularity-free; the conformal-modulus / `∂Ω`-type constant re-enters
  at the interior→curve passage for any norm `> L^∞`.

## The over-reach that was caught (do not trust it)
The agent further claimed "`n=2` closes anyway via the 2D Fuglede
spectral inequality" (`Asym²≍‖g‖²_{H^0} ≤ ‖g‖²_{H^{1/2}}≍δ_T`). This is
**unsound**: the Fuglede nearly-spherical second-variation expansion
`δ_T≍Σγ_k|ĝ_k|²` requires `‖g‖_{C¹}`/`W^{1,∞}` small — exactly what the
counterexample disproves. "Analytic curve" (qualitative) ≠ `C¹`-small
(quantitative). The closure is circular and was rejected.

## Net
`n=2` does **not** close via the graph route regularity-free. The robust
fact reconfirmed is dimension-independent: the torsional/Serrin defect
controls only `H^{1/2}` of the graph (`γ_k≍k`), never `C¹/H¹` — no "2D
miracle". `n=2` (and `n=3`) remain genuinely open in this program.
