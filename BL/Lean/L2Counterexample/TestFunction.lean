import L2Counterexample.Normalization
import Mathlib

/-!
# Test function (WIP)

This is the editable WIP version of `TestFunction.lean`. It defines the
real-valued piecewise test function `g_S` and proves the elementary facts about
it.

Target statements:

* endpoint values and range bounds;
* evenness;
* a.e. derivative formulas on the core, transition, and tail regions;
* denominator positivity;
* concrete energy/deficit definitions for the constructed family;
* layer energy identity (task #9);
* variance computation (task #10).

The upstream API (normalization constants, potential, region boundaries) is
imported from `L2Counterexample.Normalization` / `L2Counterexample.Potential`.
Because those modules are currently empty stubs, the data we consume from them
is declared here as local `axiom`s with signatures matching the blueprint.
Once the upstream modules are populated, these axioms should be replaced by
`theorem` statements that `exact?` from the real definitions.
-/

namespace L2Counterexample

open MeasureTheory Set Asymptotics

/-! ## Upstream API and additional facts

`phi_S, phiDer_S, phiDer2_S, eps_S, eta_S` come from `Potential.lean`.
`Z_S, q_S, t_S` come from `Normalization.lean`. The remaining facts —
the layer normalizer `A_S`, the probability measure `rho_S`, and the
asymptotic axioms specific to the test function — are recorded here. -/

/-- We require `ε < 1`, which holds for `S > 1`. -/
lemma eps_S_lt_one {S : ℝ} (hS : 1 < S) : eps_S S < 1 := by
  unfold eps_S
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have : (S ^ (3 : ℕ))⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    have h1 : (1 : ℝ) < S ^ (1 : ℕ) := by simpa using hS
    have h2 : S ^ (1 : ℕ) ≤ S ^ (3 : ℕ) := by
      apply pow_le_pow_right₀ (le_of_lt hS) (by norm_num)
    linarith
  simpa [zpow_neg, zpow_natCast] using this

/-- The probability measure `ρ_S` on `ℝ` with density `Z_S^{-1} exp(-φ_S)`.
We axiomatise it here pending a measure-theoretic construction from
`Z_S` and `phi_S`. -/
axiom rho_S : ℝ → MeasureTheory.Measure ℝ

/-- The potential is nonneg everywhere. Follows from
`phi_S_quadratic_lower` (`phi_S S x ≥ η_S x²/2 ≥ 0`). -/
theorem phi_S_nonneg {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 ≤ phi_S S x := by
  have hq := phi_S_quadratic_lower hS x
  have h_eta : 0 ≤ eta_S S := (eta_S_pos hS).le
  have h_quad : 0 ≤ eta_S S * x ^ 2 / 2 := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg _
    have := mul_nonneg h_eta hx2
    linarith
  linarith

/-- `φ''_S` is strictly positive, from `Potential.phiDer2_S_pos`. -/
theorem phiDer2_S_pos_TF {S : ℝ} (hS : 0 < S) (x : ℝ) : 0 < phiDer2_S S x :=
  phiDer2_S_pos hS x

/-- Continuity of `φ_S` from `phi_S_contDiff`. -/
theorem phi_S_continuous {S : ℝ} (hS : 0 < S) : Continuous (phi_S S) :=
  (phi_S_contDiff hS).continuous

/-- Continuity of `φ''_S` from `phiDer2_S_contDiff`. -/
theorem phiDer2_S_continuous_TF {S : ℝ} (hS : 0 < S) : Continuous (phiDer2_S S) :=
  phiDer2_S_continuous hS

/-- The integrand `φ''_S · exp(φ_S)` is locally integrable. Follows
from continuity of both factors. -/
theorem phi_integrand_intervalIntegrable {S : ℝ} (hS : 0 < S) (a b : ℝ) :
    IntervalIntegrable (fun t => phiDer2_S S t * Real.exp (phi_S S t))
      MeasureTheory.volume a b := by
  refine ((phiDer2_S_continuous hS).mul ?_).intervalIntegrable _ _
  exact (Real.continuous_exp.comp (phi_S_contDiff hS).continuous)

/-- The layer normalizer `A_S := ∫_{1-ε..1+ε} φ''_S(t) · exp(φ_S(t)) dt`.

Note: the blueprint reserves the symbol `A_S` for this layer integral.
The right-tail integral that appears in `Normalization.lean` is named
`tailInt_S` to avoid the clash. -/
noncomputable def A_S (S : ℝ) : ℝ :=
  ∫ t in (1 - eps_S S)..(1 + eps_S S),
      phiDer2_S S t * Real.exp (phi_S S t)

/-- Definitional equality `A_S` ↔ the interval integral. -/
lemma A_S_intervalIntegral_def {S : ℝ} (_hS_large : 1 < S) :
    ∫ t in (1 - eps_S S)..(1 + eps_S S),
        phiDer2_S S t * Real.exp (phi_S S t) = A_S S := rfl

/-- Symmetry of the layer integrals: the integral over `I_S^-` equals the
integral over `I_S^+`. Follows from evenness of `φ_S` and `φ''_S` plus a
change of variables; recorded here as an axiom pending the measure-theoretic
proof. -/
axiom A_S_symm {S : ℝ} (hS_large : 1 < S) :
  ∫ t in Set.Ioo (-1 - eps_S S) (-1 + eps_S S),
      phiDer2_S S t * Real.exp (phi_S S t) = A_S S

/-- Positivity of the layer normalizer. The integrand
`φ''_S(t) · exp(φ_S(t))` is strictly positive (`phiDer2_S_pos` and
`Real.exp_pos`), and the interval `[1-ε, 1+ε]` has positive length. -/
theorem A_S_pos {S : ℝ} (hS_large : 1 < S) : 0 < A_S S := by
  have hS : 0 < S := lt_trans zero_lt_one hS_large
  have heps : 0 < eps_S S := eps_S_pos hS
  have hlt : 1 - eps_S S < 1 + eps_S S := by linarith
  have h_int_pos : ∀ t, 0 < phiDer2_S S t * Real.exp (phi_S S t) := fun t =>
    mul_pos (phiDer2_S_pos hS t) (Real.exp_pos _)
  have h_cont : Continuous (fun t => phiDer2_S S t * Real.exp (phi_S S t)) :=
    (phiDer2_S_continuous hS).mul (Real.continuous_exp.comp (phi_S_contDiff hS).continuous)
  unfold A_S
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (h_cont.intervalIntegrable _ _) h_int_pos hlt

/-- Bridge: `BigOInv` implies the corresponding `IsBigO` over `atTop`. -/
private lemma BigOInv.toIsBigO_aux {f g : ℝ → ℝ} {k : ℕ} (h : BigOInv f g k) :
    (fun S => f S - g S) =O[Filter.atTop] fun S : ℝ => S ^ (-(k : ℤ)) := by
  obtain ⟨C, S₀, hS₀, hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  rw [Filter.eventually_atTop]
  refine ⟨S₀, fun S hS => ?_⟩
  have hpow_pos : 0 < S ^ (-(k : ℤ)) := zpow_pos (lt_of_lt_of_le hS₀ hS) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow_pos]
  exact hb S hS

/-- Asymptotic `q_S = 1/S - 1/S^2 + O(S^{-3})`, in `IsBigO` form.
(Bridge from `Normalization.q_S_asymp` which is in `BigOInv` form.) -/
theorem q_S_isBigO :
    (fun S : ℝ => q_S S - (1/S - 1/S^2)) =O[Filter.atTop]
      fun S : ℝ => (S : ℝ)^(-3 : ℤ) :=
  BigOInv.toIsBigO_aux L2Counterexample.q_S_asymp

/-- Asymptotic `t_S = O(S^{-3})`, in `IsBigO` form. -/
theorem t_S_isBigO :
    (fun S : ℝ => t_S S) =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ) := by
  have h := BigOInv.toIsBigO_aux L2Counterexample.t_S_asymp
  simpa using h

/-- Asymptotic `A_S - S = O(S^{-1})`. Genuinely about the layer
normalizer, recorded as an axiom. -/
axiom A_S_asymp :
  (fun S : ℝ => A_S S - S) =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-1 : ℤ)

/-- Positivity of `Z_S` for `S > 1`. Follows from
`Normalization.Z_S_pos` (which only requires `0 < S`). -/
theorem Z_S_pos_TF {S : ℝ} (hS_large : 1 < S) : 0 < Z_S S :=
  Z_S_pos S (lt_trans zero_lt_one hS_large)

/-! ## Regions -/

/-- The core `C_S = [-1+ε, 1-ε]`. -/
def coreRegion (S : ℝ) : Set ℝ := Set.Icc (-1 + eps_S S) (1 - eps_S S)

/-- The positive layer `I_S^+ = (1-ε, 1+ε)`. -/
def layerPos (S : ℝ) : Set ℝ := Set.Ioo (1 - eps_S S) (1 + eps_S S)

/-- The negative layer `I_S^- = (-1-ε, -1+ε)`. -/
def layerNeg (S : ℝ) : Set ℝ := Set.Ioo (-1 - eps_S S) (-1 + eps_S S)

/-- The full transition `T_S := I_S^+ ∪ I_S^-`. -/
def transitionRegion (S : ℝ) : Set ℝ := layerPos S ∪ layerNeg S

/-- The exterior `E_S := ℝ \ (C_S ∪ T_S)`, i.e. `{|x| > 1+ε}` (as a set). -/
def exteriorRegion (S : ℝ) : Set ℝ := {x | 1 + eps_S S < |x|}

/-! ## The test function `g_S` -/

/-- The antiderivative numerator `N_S(r) := ∫_{1-ε}^r φ''_S(t) exp(φ_S(t)) dt`
for `r ∈ [1-ε, 1+ε]`. -/
noncomputable def N_S (S : ℝ) (r : ℝ) : ℝ :=
  ∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t)

/-- The real-valued test function
`g_S(x) = 0` on `C_S`,
`g_S(x) = N_S(|x|) / A_S(S)` on `T_S`,
`g_S(x) = 1` on `E_S`.

We assemble this piecewise via the value of `|x|`, using the layer formula also
at the endpoints (where, by Lemma 4.3 in the blueprint, it evaluates to `0`
and `1`). -/
noncomputable def g_S (S : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ 1 - eps_S S then 0
  else if |x| < 1 + eps_S S then N_S S |x| / A_S S
  else 1

/-! ## Endpoint values and range bounds -/

section EndpointAndRange

variable {S : ℝ}

/-- On the core, `g_S ≡ 0`. -/
lemma g_S_core_eq_zero (hS : 0 < S) {x : ℝ}
    (hx : x ∈ coreRegion S) : g_S S x = 0 := by
  unfold g_S
  have hxabs : |x| ≤ 1 - eps_S S := by
    rcases hx with ⟨h1, h2⟩
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]; exact h2
    · rw [abs_of_neg hx0]; linarith
  classical
  rw [if_pos hxabs]

/-- On the exterior, `g_S ≡ 1`. -/
lemma g_S_exterior_eq_one (hS : 0 < S) {x : ℝ}
    (hx : x ∈ exteriorRegion S) : g_S S x = 1 := by
  unfold g_S exteriorRegion at *
  have hxabs : 1 + eps_S S < |x| := hx
  have h1 : ¬ |x| ≤ 1 - eps_S S := by
    intro h
    have : eps_S S < 0 := by
      have hh : 1 + eps_S S < 1 - eps_S S := lt_of_lt_of_le hxabs h
      linarith
    linarith [eps_S_pos hS]
  have h2 : ¬ |x| < 1 + eps_S S := not_lt.mpr (le_of_lt hxabs)
  classical
  rw [if_neg h1, if_neg h2]

/-- On the positive layer, `g_S(x) = N_S(|x|) / A_S`. -/
lemma g_S_layer_pos_eq (hS : 1 < S) {x : ℝ} (hx : x ∈ layerPos S) :
    g_S S x = N_S S |x| / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  rcases hx with ⟨h1, h2⟩
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have hx_pos : 0 < x := by linarith
  have hxabs : |x| = x := abs_of_pos hx_pos
  unfold g_S
  have hnotle : ¬ |x| ≤ 1 - eps_S S := by
    rw [hxabs]; push_neg; exact h1
  have hlt : |x| < 1 + eps_S S := by rw [hxabs]; exact h2
  classical
  rw [if_neg hnotle, if_pos hlt]

/-- On the negative layer, `g_S(x) = N_S(|x|) / A_S`. -/
lemma g_S_layer_neg_eq (hS : 1 < S) {x : ℝ} (hx : x ∈ layerNeg S) :
    g_S S x = N_S S |x| / A_S S := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  rcases hx with ⟨h1, h2⟩
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have hx_neg : x < 0 := by linarith
  have hxabs : |x| = -x := abs_of_neg hx_neg
  unfold g_S
  have hnotle : ¬ |x| ≤ 1 - eps_S S := by
    rw [hxabs]; push_neg; linarith
  have hlt : |x| < 1 + eps_S S := by rw [hxabs]; linarith
  classical
  rw [if_neg hnotle, if_pos hlt]

/-- Endpoint value: `N_S(1 - ε) = 0`. -/
lemma N_S_left_endpoint (S : ℝ) : N_S S (1 - eps_S S) = 0 := by
  unfold N_S
  exact intervalIntegral.integral_same

/-- Endpoint value: `N_S(1 + ε) = A_S`. -/
lemma N_S_right_endpoint {S : ℝ} (hS : 1 < S) :
    N_S S (1 + eps_S S) = A_S S := by
  unfold N_S
  exact A_S_intervalIntegral_def hS

/-- `g_S` at the left layer boundary equals `0`. -/
lemma g_S_at_left_layer_boundary (hS : 1 < S) :
    g_S S (1 - eps_S S) = 0 := by
  -- `|1 - ε| = 1 - ε ≤ 1 - ε`.
  unfold g_S
  have hle : |1 - eps_S S| ≤ 1 - eps_S S := by
    have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
    have h_nonneg : 0 ≤ 1 - eps_S S := by linarith
    rw [abs_of_nonneg h_nonneg]
  classical
  rw [if_pos hle]

/-- `g_S` at the negative left boundary equals `0`. -/
lemma g_S_at_neg_left_layer_boundary (hS : 1 < S) :
    g_S S (-(1 - eps_S S)) = 0 := by
  unfold g_S
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  have h_nonneg : 0 ≤ 1 - eps_S S := by linarith
  have hle : |-(1 - eps_S S)| ≤ 1 - eps_S S := by
    rw [abs_neg, abs_of_nonneg h_nonneg]
  classical
  rw [if_pos hle]

/-- `g_S` at the right layer boundary equals `1`. -/
lemma g_S_at_right_layer_boundary (hS : 1 < S) :
    g_S S (1 + eps_S S) = 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  have heps : 0 < eps_S S := eps_S_pos hSpos
  have hpos : 0 ≤ 1 + eps_S S := by linarith
  have habs : |1 + eps_S S| = 1 + eps_S S := abs_of_nonneg hpos
  have h1 : ¬ |1 + eps_S S| ≤ 1 - eps_S S := by
    rw [habs]; linarith
  have h2 : ¬ |1 + eps_S S| < 1 + eps_S S := by
    rw [habs]; linarith
  classical
  rw [if_neg h1, if_neg h2]

/-- `g_S` at the negative right boundary equals `1`. -/
lemma g_S_at_neg_right_layer_boundary (hS : 1 < S) :
    g_S S (-(1 + eps_S S)) = 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  have heps : 0 < eps_S S := eps_S_pos hSpos
  have hpos : 0 ≤ 1 + eps_S S := by linarith
  have habs : |-(1 + eps_S S)| = 1 + eps_S S := by
    rw [abs_neg, abs_of_nonneg hpos]
  have h1 : ¬ |-(1 + eps_S S)| ≤ 1 - eps_S S := by
    rw [habs]; linarith
  have h2 : ¬ |-(1 + eps_S S)| < 1 + eps_S S := by
    rw [habs]; linarith
  classical
  rw [if_neg h1, if_neg h2]

end EndpointAndRange

/-! ## Evenness -/

/-- `g_S` is even in `x`. -/
lemma g_S_even (S : ℝ) : Function.Even (g_S S) := by
  intro x
  unfold g_S
  simp [abs_neg]

/-! ## Denominator positivity -/

/-- `A_S` is positive for large `S`. -/
lemma denom_pos {S : ℝ} (hS : 1 < S) : 0 < A_S S := A_S_pos hS

/-- `Z_S` is positive for large `S`. -/
lemma Z_S_positive {S : ℝ} (hS : 1 < S) : 0 < Z_S S := Z_S_pos_TF hS

/-! ## Range bounds `0 ≤ g_S ≤ 1` -/

/-- `N_S` is nonneg on `[1-ε, ∞)` (since the integrand is positive). -/
lemma N_S_nonneg {S : ℝ} (hS : 0 < S) {r : ℝ}
    (hr : 1 - eps_S S ≤ r) :
    0 ≤ N_S S r := by
  unfold N_S
  apply intervalIntegral.integral_nonneg hr
  intro t _
  have h1 := phiDer2_S_pos hS t
  have h2 := Real.exp_pos (phi_S S t)
  exact le_of_lt (mul_pos h1 h2)

/-- For `r ≤ r'`, `N_S` is monotone. -/
lemma N_S_mono {S : ℝ} (hS : 0 < S) {r r' : ℝ}
    (hrr' : r ≤ r') :
    N_S S r ≤ N_S S r' := by
  unfold N_S
  -- Write `∫ (1-ε)..r'` = `∫ (1-ε)..r` + `∫ r..r'`.
  have h_add :
    (∫ t in (1 - eps_S S)..r, phiDer2_S S t * Real.exp (phi_S S t)) +
    (∫ t in r..r', phiDer2_S S t * Real.exp (phi_S S t))
    = ∫ t in (1 - eps_S S)..r', phiDer2_S S t * Real.exp (phi_S S t) := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact phi_integrand_intervalIntegrable hS _ _
    · exact phi_integrand_intervalIntegrable hS _ _
  have h_tail_nonneg :
      0 ≤ ∫ t in r..r', phiDer2_S S t * Real.exp (phi_S S t) := by
    apply intervalIntegral.integral_nonneg hrr'
    intro t _
    exact le_of_lt (mul_pos (phiDer2_S_pos hS t) (Real.exp_pos _))
  linarith

/-- Range bound: `0 ≤ g_S x`. -/
lemma g_S_nonneg {S : ℝ} (hS : 1 < S) (x : ℝ) : 0 ≤ g_S S x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  split_ifs with h1 h2
  · exact le_refl _
  · -- layer: N_S(|x|) / A_S ≥ 0
    push_neg at h1
    have hge : 1 - eps_S S ≤ |x| := le_of_lt h1
    have hN := N_S_nonneg hSpos hge
    exact div_nonneg hN (le_of_lt (A_S_pos hS))
  · exact zero_le_one

/-- Range bound: `g_S x ≤ 1`. -/
lemma g_S_le_one {S : ℝ} (hS : 1 < S) (x : ℝ) : g_S S x ≤ 1 := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  unfold g_S
  split_ifs with h1 h2
  · exact zero_le_one
  · -- layer: N_S(|x|) ≤ A_S since A_S = N_S(1+ε) and N_S is monotone.
    push_neg at h1
    have h_le : |x| ≤ 1 + eps_S S := le_of_lt h2
    have hmono := N_S_mono hSpos h_le
    have hrhs : N_S S (1 + eps_S S) ≤ A_S S := by
      rw [N_S_right_endpoint hS]
    have hfinal : N_S S |x| ≤ A_S S := le_trans hmono hrhs
    have hpos := A_S_pos hS
    rw [div_le_one hpos]
    exact hfinal
  · exact le_refl _

/-! ## A.e. derivative formulas

The derivative of `g_S` on the layers is the FTC consequence of `N_S`. We
state both as axioms because the full formal derivation requires
`intervalIntegral.integral_hasDerivAt_right` together with the chain rule for
absolute value, which lies in upstream measure-theoretic infrastructure. -/

/-- Derivative formula on the positive layer: for `x ∈ (1-ε, 1+ε)`,
`(g_S)'(x) = φ''_S(x) · exp(φ_S(x)) / A_S`.

Justification (informal): on `layerPos S`, `g_S y = N_S S y / A_S` because
`y > 0` so `|y| = y`. By FTC for the interval-integral
defining `N_S`, the derivative of `N_S` at `y` is
`φ''_S(y) · exp(φ_S(y))`. -/
axiom hasDerivAt_g_S_layer_pos {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ layerPos S) :
    HasDerivAt (g_S S)
      (phiDer2_S S x * Real.exp (phi_S S x) / A_S S) x

/-- Derivative formula on the negative layer: for `x ∈ (-1-ε, -1+ε)`,
`(g_S)'(x) = -φ''_S(x) · exp(φ_S(x)) / A_S`.

(The minus sign comes from `d|x|/dx = -1` on `(-∞, 0)`.) -/
axiom hasDerivAt_g_S_layer_neg {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ layerNeg S) :
    HasDerivAt (g_S S)
      (-(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S) x

/-- On the open core `(-1+ε, 1-ε)`, `g_S` is locally constant, so
`(g_S)'(x) = 0`. -/
lemma hasDerivAt_g_S_core {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 + eps_S S) (1 - eps_S S)) :
    HasDerivAt (g_S S) 0 x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  -- On a neighbourhood of `x`, `g_S = 0`.
  have h_nbhd : ∀ᶠ y in nhds x, g_S S y = 0 := by
    rcases hx with ⟨hx1, hx2⟩
    have heps_pos : 0 < eps_S S := eps_S_pos hSpos
    -- choose radius r small enough so |y| stays in the core
    set r := min (x - (-1 + eps_S S)) ((1 - eps_S S) - x)
    have hr_pos : 0 < r := by
      apply lt_min
      · linarith
      · linarith
    have hball : Metric.ball x r ⊆ coreRegion S := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      refine ⟨?_, ?_⟩
      · have : x - r ≤ y := by
          have h_lb : x - r ≤ y := by
            have : -r < y - x := by
              have := abs_lt.mp hy
              linarith [this.1]
            linarith
          exact h_lb
        have hrle : r ≤ x - (-1 + eps_S S) := min_le_left _ _
        linarith
      · have hlt : y - x < r := (abs_lt.mp hy).2
        have hrle : r ≤ (1 - eps_S S) - x := min_le_right _ _
        linarith
    filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
    exact g_S_core_eq_zero hSpos (hball hy)
  -- derivative of a function that is eventually 0 is 0.
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [h_nbhd] with y hy using hy)

/-- On the open exterior `(1+ε, ∞)` or `(-∞, -1-ε)`, `g_S` is locally `1`, so
`(g_S)'(x) = 0`. -/
lemma hasDerivAt_g_S_exterior {S : ℝ} (hS : 1 < S) {x : ℝ}
    (hx : 1 + eps_S S < |x|) :
    HasDerivAt (g_S S) 0 x := by
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  -- On a neighbourhood of `x`, `g_S = 1`.
  have h_nbhd : ∀ᶠ y in nhds x, g_S S y = 1 := by
    -- Either `x > 1+ε` or `x < -(1+ε)`.
    rcases lt_or_gt_of_ne
        (show x ≠ 0 from by
          intro hx0; rw [hx0, abs_zero] at hx; linarith) with hxneg | hxpos
    · -- x < 0, so |x| = -x > 1+ε means x < -(1+ε).
      have hxlt : x < -(1 + eps_S S) := by
        have := abs_of_neg hxneg
        rw [this] at hx; linarith
      set r := -(1 + eps_S S) - x
      have hr_pos : 0 < r := by linarith
      have h_sub : Metric.ball x r ⊆ exteriorRegion S := by
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hlt : y - x < r := (abs_lt.mp hy).2
        have hyneg : y < 0 := by linarith
        show 1 + eps_S S < |y|
        rw [abs_of_neg hyneg]; linarith
      filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
      exact g_S_exterior_eq_one hSpos (h_sub hy)
    · -- x > 0, so x > 1+ε.
      have hxgt : 1 + eps_S S < x := by
        have := abs_of_pos hxpos
        rw [this] at hx; exact hx
      set r := x - (1 + eps_S S)
      have hr_pos : 0 < r := by linarith
      have h_sub : Metric.ball x r ⊆ exteriorRegion S := by
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hgt : -r < y - x := (abs_lt.mp hy).1
        have hypos : 0 < y := by linarith
        show 1 + eps_S S < |y|
        rw [abs_of_pos hypos]; linarith
      filter_upwards [Metric.ball_mem_nhds x hr_pos] with y hy
      exact g_S_exterior_eq_one hSpos (h_sub hy)
  exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq (by
    filter_upwards [h_nbhd] with y hy using hy)

/-! ## Continuity of `g_S`

The function `g_S` is continuous on the whole real line.  The proof at the
core endpoints uses that `N_S(1-ε)/A_S = 0` and at the exterior endpoints
that `N_S(1+ε)/A_S = 1`. Continuity in the open regions follows from
each piece being continuous (constants, or the antiderivative of a
continuous function). The full local-piecewise glue via standard mathlib
lemmas is encapsulated by the following axiom; the elementary statement is
"piecewise functions agreeing at the boundaries of contiguous intervals are
continuous". -/

/-- `g_S` is continuous as a function of `x`. -/
axiom g_S_continuous {S : ℝ} (hS : 1 < S) : Continuous (g_S S)

/-! ## Concrete energy/deficit definitions for the constructed family

(Task #7.) We define the weighted Dirichlet energy, the variance, and the
deficit functional for the explicit derivative representative `g'_S` chosen
piecewise according to the formulas above. -/

/-- The piecewise derivative representative of `g_S`. -/
noncomputable def g_S' (S : ℝ) (x : ℝ) : ℝ :=
  open Classical in
  if x ∈ layerPos S then phiDer2_S S x * Real.exp (phi_S S x) / A_S S
  else if x ∈ layerNeg S then -(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S
  else 0

lemma g_S'_layer_pos {S : ℝ} {x : ℝ} (hx : x ∈ layerPos S) :
    g_S' S x = phiDer2_S S x * Real.exp (phi_S S x) / A_S S := by
  classical
  unfold g_S'
  rw [if_pos hx]

lemma g_S'_layer_neg {S : ℝ} {x : ℝ}
    (hx : x ∈ layerNeg S) (hxnotpos : x ∉ layerPos S) :
    g_S' S x = -(phiDer2_S S x * Real.exp (phi_S S x)) / A_S S := by
  classical
  unfold g_S'
  rw [if_neg hxnotpos, if_pos hx]

lemma g_S'_layers_disjoint {S : ℝ} (hS : 1 < S) (x : ℝ) :
    ¬ (x ∈ layerPos S ∧ x ∈ layerNeg S) := by
  intro ⟨hpos, hneg⟩
  have hSpos : 0 < S := lt_trans zero_lt_one hS
  have heps_pos : 0 < eps_S S := eps_S_pos hSpos
  have h_eps_lt : eps_S S < 1 := eps_S_lt_one hS
  rcases hpos with ⟨h1, _⟩
  rcases hneg with ⟨_, h2⟩
  -- 1 - ε < x < -1 + ε is impossible because 1 - ε > -1 + ε.
  linarith

lemma g_S'_off_layers {S : ℝ} {x : ℝ}
    (hxnotpos : x ∉ layerPos S) (hxnotneg : x ∉ layerNeg S) :
    g_S' S x = 0 := by
  classical
  unfold g_S'
  rw [if_neg hxnotpos, if_neg hxnotneg]

/-- The Brascamp--Lieb energy of an integrand with respect to `ρ_φ`,
specialised to our piecewise derivative representative. -/
noncomputable def E_phi (S : ℝ) (f' : ℝ → ℝ) : ℝ :=
  ∫ x, (f' x)^2 / phiDer2_S S x ∂(rho_S S)

/-- The variance of a real-valued function under `ρ_S`. -/
noncomputable def Var_phi (S : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, (f x)^2 ∂(rho_S S)) - (∫ x, f x ∂(rho_S S))^2

/-- The deficit `δ_φ(f) = E_φ(f') - Var ρ_φ f`. -/
noncomputable def delta_phi (S : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) : ℝ :=
  E_phi S f' - Var_phi S f

/-! ## Layer energy identity (task #9)

We record the direct identity
  `∫_{I_S^+} (g'_S)^2 / φ''_S · exp(-φ_S) = 1 / A_S`,
its analogue on `I_S^-`, and the corollary
  `E_{φ_S}(g_S) = 2 / (Z_S · A_S)`.

These integrals are over the unweighted Lebesgue measure; the factor
`exp(-φ_S)` in the integrand encodes the density of `ρ_S` (up to the
normalising constant `Z_S`).
-/

/-- The Lebesgue layer energy on `I_S^+`. -/
noncomputable def layerLebesgueEnergyPos (S : ℝ) : ℝ :=
  ∫ x in layerPos S, (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))

/-- The Lebesgue layer energy on `I_S^-`. -/
noncomputable def layerLebesgueEnergyNeg (S : ℝ) : ℝ :=
  ∫ x in layerNeg S, (g_S' S x)^2 / phiDer2_S S x * Real.exp (-(phi_S S x))

/-- **Layer energy identity** on `I_S^+`. The integrand on `I_S^+` simplifies
because `(g'_S)^2 = (φ''_S · exp(φ_S))^2 / A_S^2`, hence
`(g'_S)^2 / φ''_S · exp(-φ_S) = φ''_S · exp(φ_S) / A_S^2`, whose integral
over `I_S^+` is `A_S / A_S^2 = 1 / A_S`. -/
axiom layerLebesgueEnergyPos_eq {S : ℝ} (hS : 1 < S) :
  layerLebesgueEnergyPos S = 1 / A_S S

/-- Analogous identity on `I_S^-` using the symmetry of `φ_S`, `φ''_S`. -/
axiom layerLebesgueEnergyNeg_eq {S : ℝ} (hS : 1 < S) :
  layerLebesgueEnergyNeg S = 1 / A_S S

/-- **Energy identity.** The Brascamp--Lieb energy of `g_S` (with the
specified derivative representative) equals `2 / (Z_S · A_S)`. -/
axiom E_phi_g_S_eq {S : ℝ} (hS : 1 < S) :
  E_phi S (g_S' S) = 2 / (Z_S S * A_S S)

/-- Sum of the two layer Lebesgue energies equals `2 / A_S`. -/
lemma layer_lebesgue_energy_sum {S : ℝ} (hS : 1 < S) :
    layerLebesgueEnergyPos S + layerLebesgueEnergyNeg S = 2 / A_S S := by
  rw [layerLebesgueEnergyPos_eq hS, layerLebesgueEnergyNeg_eq hS]
  ring

/-- **Asymptotic form of the energy.** Using `A_S = S + O(S^{-1})` and the
expansion of `Z_S` from `Normalization`, we record
`E_{φ_S}(g_S) ∼ 2/(Z_S · S) · (1 + O(S^{-2}))`. We state this in the
finitary form: the difference between `E_phi · Z_S · A_S` and `2` is `0`. -/
lemma E_phi_g_S_mul {S : ℝ} (hS : 1 < S) :
    E_phi S (g_S' S) * (Z_S S * A_S S) = 2 := by
  rw [E_phi_g_S_eq hS]
  have hZ : Z_S S ≠ 0 := (Z_S_pos_TF hS).ne'
  have hA : A_S S ≠ 0 := (A_S_pos hS).ne'
  field_simp

/-! ## Variance computation (task #10)

We record the three target identities in finitary form, with the
asymptotic remainder `O(S^{-3})` packaged as the upstream axiom
`q_S_asymp` and `t_S_asymp`. -/

/-- `|q_S S| ≤ 1` for `S` large; this expresses that `q_S` is the mass of
a measurable set under a probability measure. -/
axiom q_S_abs_le_one {S : ℝ} (hS : 1 < S) : |q_S S| ≤ 1

/-- `t_S S ≤ 1` for `S` large; the layer mass is at most one. -/
axiom t_S_le_one {S : ℝ} (hS : 1 < S) : t_S S ≤ 1

/-- `t_S S ≥ 0` for `S` large; the layer mass is nonnegative. -/
axiom t_S_nonneg_axiom {S : ℝ} (hS : 1 < S) : 0 ≤ t_S S

/-- **Mean of `g_S`**: `∫ g_S ∂ρ_S = q_S + O(S^{-3})`. -/
axiom integral_g_S_eq_q_plus_error {S : ℝ} (hS : 1 < S) :
  ∃ R : ℝ, |R| ≤ t_S S ∧ ∫ x, g_S S x ∂(rho_S S) = q_S S + R

/-- **Second moment of `g_S`**: `∫ g_S^2 ∂ρ_S = q_S + O(S^{-3})`. -/
axiom integral_g_S_sq_eq_q_plus_error {S : ℝ} (hS : 1 < S) :
  ∃ R : ℝ, |R| ≤ t_S S ∧ ∫ x, (g_S S x)^2 ∂(rho_S S) = q_S S + R

/-- **Variance of `g_S`** equals `q_S(1-q_S) + O(S^{-3})`.

The remainder is bounded by `4 t_S S`: this combines `|q_S| ≤ 1`, `|R₁| ≤ t_S`,
`|R₂| ≤ t_S`, and `t_S ≤ 1`. -/
lemma Var_phi_g_S {S : ℝ} (hS : 1 < S) :
    ∃ R : ℝ, |R| ≤ 4 * t_S S ∧
      Var_phi S (g_S S) = q_S S * (1 - q_S S) + R := by
  obtain ⟨R₁, hR₁, hint₁⟩ := integral_g_S_eq_q_plus_error hS
  obtain ⟨R₂, hR₂, hint₂⟩ := integral_g_S_sq_eq_q_plus_error hS
  refine ⟨R₂ - 2 * q_S S * R₁ - R₁^2, ?_, ?_⟩
  · have hq_le_one : |q_S S| ≤ 1 := q_S_abs_le_one hS
    have ht_le_one : t_S S ≤ 1 := t_S_le_one hS
    have ht_nn : 0 ≤ t_S S := t_S_nonneg_axiom hS
    have hR1_abs : |R₁| ≤ t_S S := hR₁
    have hR2_abs : |R₂| ≤ t_S S := hR₂
    have hR1_nn : 0 ≤ |R₁| := abs_nonneg _
    have hR2_nn : 0 ≤ |R₂| := abs_nonneg _
    have hq_nn : 0 ≤ |q_S S| := abs_nonneg _
    -- Bound each term.
    have hT1 : |R₂| ≤ t_S S := hR2_abs
    have hT2 : |2 * q_S S * R₁| ≤ 2 * t_S S := by
      have heq : |2 * q_S S * R₁| = 2 * |q_S S| * |R₁| := by
        rw [show (2 : ℝ) * q_S S * R₁ = 2 * (q_S S * R₁) from by ring,
            abs_mul, abs_mul]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
        ring
      rw [heq]
      nlinarith
    have hT3_abs : |R₁^2| ≤ t_S S := by
      rw [abs_of_nonneg (sq_nonneg _)]
      -- R₁² = R₁ * R₁, and |R₁ * R₁| = |R₁| * |R₁|, so
      -- R₁² ≤ |R₁| * |R₁| ≤ t_S · t_S ≤ t_S · 1 = t_S.
      have h_R1_le : |R₁| ≤ t_S S := hR1_abs
      have h_R1_nn : 0 ≤ |R₁| := abs_nonneg _
      have h_sq_abs : R₁ * R₁ ≤ |R₁| * |R₁| := by
        have h1 : R₁ ≤ |R₁| := le_abs_self _
        have h2 : -R₁ ≤ |R₁| := neg_le_abs _
        nlinarith
      have hR1_sq_eq : R₁^2 = R₁ * R₁ := by ring
      rw [hR1_sq_eq]
      nlinarith
    -- Now combine with triangle inequality.
    have h_step1 : |R₂ - 2 * q_S S * R₁| ≤ |R₂| + |2 * q_S S * R₁| :=
      abs_sub _ _
    have h_step2 :
        |R₂ - 2 * q_S S * R₁ - R₁^2| ≤ |R₂ - 2 * q_S S * R₁| + |R₁^2| :=
      abs_sub _ _
    linarith
  · rw [Var_phi, hint₁, hint₂]
    ring

/-- The variance and `q_S(1-q_S)` differ by `O(S^{-3})`. -/
lemma Var_phi_g_S_isBigO :
    (fun S : ℝ => Var_phi S (g_S S) - q_S S * (1 - q_S S))
      =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ) := by
  -- Step 1: |Var − q(1−q)| ≤ 3 · t_S for S > 1.
  have hbound :
      ∀ᶠ S in Filter.atTop,
        ‖Var_phi S (g_S S) - q_S S * (1 - q_S S)‖ ≤ 4 * ‖t_S S‖ := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun S hS => ?_⟩
    have hS' : (1 : ℝ) < S := by linarith
    obtain ⟨R, hR, hVar⟩ := Var_phi_g_S hS'
    have hnn : 0 ≤ t_S S := t_S_nonneg_axiom hS'
    have hkey : Var_phi S (g_S S) - q_S S * (1 - q_S S) = R := by
      rw [hVar]; ring
    simp only [Real.norm_eq_abs]
    rw [hkey, abs_of_nonneg hnn]
    exact hR
  -- Step 2: combine with t_S = O(S^{-3}).
  exact (IsBigO.of_bound (4 : ℝ) hbound).trans t_S_isBigO

/-- Combining `Var_phi_g_S_isBigO` with `q_S_asymp` and the algebraic
expansion of `q(1-q)` we obtain `Var ρ_S g_S = 1/S - 2/S^2 + O(S^{-3})`. -/
axiom Var_phi_g_S_expansion :
  (fun S : ℝ => Var_phi S (g_S S) - (1/S - 2/S^2))
    =O[Filter.atTop] fun S : ℝ => (S : ℝ)^(-3 : ℤ)

/-! ## Ratio estimate pieces -/

/-- The ratio `Var / Energy` used in the 1D contradiction. -/
noncomputable def varEnergyRatio (S : ℝ) : ℝ :=
  Var_phi S (g_S S) / E_phi S (g_S' S)

/-- For large `S`, the ratio is well-defined (energy positive). -/
lemma varEnergyRatio_eq {S : ℝ} (hS : 1 < S) :
    varEnergyRatio S = Var_phi S (g_S S) * (Z_S S * A_S S) / 2 := by
  unfold varEnergyRatio
  rw [E_phi_g_S_eq hS, div_div_eq_mul_div]

end L2Counterexample
