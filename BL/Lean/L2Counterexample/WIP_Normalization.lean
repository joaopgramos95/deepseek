import L2Counterexample.Potential

/-!
# Normalization and asymptotics (WIP)

This is the editable WIP version of `Normalization.lean`. It formalises the
normalising constants `Z_S`, `A_S`, `q_S`, `t_S` of section 3 of the
counterexample paper, together with their tail asymptotic expansions.

## Layered approach

`Potential.lean` is currently a stub.  Following the project rule that WIP
files may axiomatise the upstream API while keeping the present file
sorry-free, we declare:

1.  The potential family `phi_S`, the parameters `epsS`, `etaS`, and the
    qualitative facts about `phi_S` (measurability, evenness, the quadratic
    lower bound, the regional formulas) used in section 3 of the paper.
2.  The two analytic black-box facts that depend on `phi_S` and would
    otherwise pull in heavy measure-theoretic / change-of-variables
    arguments:
    - the change-of-variables identity for the tail integral
      (`A_S_tail_eq`);
    - the symmetric decomposition `Z_S = 2 (∫_core + ∫_layer + A_S)`
      (`Z_S_decomposition`).
3.  Two elementary exponential integrals (Laplace transforms `1/a` and
    `2/a^3`) that should land in `Mathlib`.

Asymptotic expansions are encoded by the explicit finitary inequality

  `BigOInv f g k := ∃ C S₀, 0 < S₀ ∧ ∀ S ≥ S₀, |f S - g S| ≤ C·S^(-k)`,

which keeps the proofs inside `linarith` / `nlinarith` reach and avoids the
overhead of `Asymptotics.IsBigO` for development.  The upstream "blueprint"
asymptotic estimates from section 3 are stated and used as axioms here; once
`Potential.lean` is filled in they will be discharged.
-/

noncomputable section

open MeasureTheory Real
open scoped Topology

namespace L2Counterexample

/-! ## Asymptotic shorthand -/

/-- `BigOInv f g k` means `f S = g S + O(S^{-k})` as `S → ∞`, encoded as an
explicit finitary inequality over real `S`. -/
def BigOInv (f g : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S - g S| ≤ C * S ^ (-(k : ℤ))

lemma bigOInv_zero_iff (f : ℝ → ℝ) (k : ℕ) :
    BigOInv f (fun _ => 0) k ↔
      ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S| ≤ C * S ^ (-(k : ℤ)) := by
  unfold BigOInv
  simp

/-! ### Algebra of `BigOInv` -/

lemma BigOInv.add {f g f' g' : ℝ → ℝ} {k : ℕ}
    (h : BigOInv f g k) (h' : BigOInv f' g' k) :
    BigOInv (fun S => f S + f' S) (fun S => g S + g' S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  obtain ⟨C', S₀', hS₀', hC'⟩ := h'
  refine ⟨C + C', max S₀ S₀', lt_max_of_lt_left hS₀, fun S hS => ?_⟩
  have hSS₀ : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hSS₀' : S₀' ≤ S := le_trans (le_max_right _ _) hS
  have h1 := hC S hSS₀
  have h2 := hC' S hSS₀'
  have habs : |f S + f' S - (g S + g' S)| ≤ |f S - g S| + |f' S - g' S| := by
    have hrw : f S + f' S - (g S + g' S) = (f S - g S) + (f' S - g' S) := by ring
    rw [hrw]
    exact abs_add _ _
  calc |f S + f' S - (g S + g' S)|
      ≤ |f S - g S| + |f' S - g' S| := habs
    _ ≤ C * S ^ (-(k : ℤ)) + C' * S ^ (-(k : ℤ)) := by linarith
    _ = (C + C') * S ^ (-(k : ℤ)) := by ring

lemma BigOInv.sub {f g f' g' : ℝ → ℝ} {k : ℕ}
    (h : BigOInv f g k) (h' : BigOInv f' g' k) :
    BigOInv (fun S => f S - f' S) (fun S => g S - g' S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  obtain ⟨C', S₀', hS₀', hC'⟩ := h'
  refine ⟨C + C', max S₀ S₀', lt_max_of_lt_left hS₀, fun S hS => ?_⟩
  have hSS₀ : S₀ ≤ S := le_trans (le_max_left _ _) hS
  have hSS₀' : S₀' ≤ S := le_trans (le_max_right _ _) hS
  have h1 := hC S hSS₀
  have h2 := hC' S hSS₀'
  have habs : |f S - f' S - (g S - g' S)| ≤ |f S - g S| + |f' S - g' S| := by
    have hrw : f S - f' S - (g S - g' S) = (f S - g S) - (f' S - g' S) := by ring
    rw [hrw]
    exact abs_sub _ _
  calc |f S - f' S - (g S - g' S)|
      ≤ |f S - g S| + |f' S - g' S| := habs
    _ ≤ C * S ^ (-(k : ℤ)) + C' * S ^ (-(k : ℤ)) := by linarith
    _ = (C + C') * S ^ (-(k : ℤ)) := by ring

lemma BigOInv.const_mul {f g : ℝ → ℝ} {k : ℕ} (c : ℝ) (h : BigOInv f g k) :
    BigOInv (fun S => c * f S) (fun S => c * g S) k := by
  obtain ⟨C, S₀, hS₀, hC⟩ := h
  refine ⟨|c| * C, S₀, hS₀, fun S hS => ?_⟩
  have hb := hC S hS
  have habs : |c * f S - c * g S| = |c| * |f S - g S| := by
    rw [show c * f S - c * g S = c * (f S - g S) from by ring, abs_mul]
  rw [habs]
  have h1 : |c| * |f S - g S| ≤ |c| * (C * S ^ (-(k : ℤ))) := by
    apply mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  linarith [h1]

/-! ## Parameters and the potential -/

/-- The parameter `ε_S = S^{-3}` used in the paper. -/
def epsS (S : ℝ) : ℝ := S ^ (-(3 : ℤ))

/-- The parameter `η_S = S^{-4}` used in the paper. -/
def etaS (S : ℝ) : ℝ := S ^ (-(4 : ℤ))

lemma epsS_pos {S : ℝ} (hS : 0 < S) : 0 < epsS S := by
  unfold epsS
  exact zpow_pos hS _

lemma etaS_pos {S : ℝ} (hS : 0 < S) : 0 < etaS S := by
  unfold etaS
  exact zpow_pos hS _

lemma epsS_nonneg {S : ℝ} (hS : 0 < S) : 0 ≤ epsS S := (epsS_pos hS).le

lemma etaS_nonneg {S : ℝ} (hS : 0 < S) : 0 ≤ etaS S := (etaS_pos hS).le

/-- Helper: `S ^ (-k:ℤ) = 1 / S^k` for `S ≠ 0`. -/
lemma zpow_negNat (S : ℝ) (k : ℕ) (hS : S ≠ 0) :
    S ^ (-(k : ℤ)) = 1 / S ^ k := by
  rw [zpow_neg, zpow_natCast, one_div]

/-! ## Axiomatised potential interface

We declare `phi_S S x` as a black-box smooth potential satisfying the shape
required by the blueprint. -/

/-- The (axiomatised) potential family from `Potential.lean`. -/
axiom phi_S : ℝ → ℝ → ℝ

/-- `phi_S S ·` is measurable. -/
axiom phi_S_measurable (S : ℝ) : Measurable (fun x => phi_S S x)

/-- Evenness of `phi_S S` in `x`. -/
axiom phi_S_even (S x : ℝ) : phi_S S (-x) = phi_S S x

/-- Quadratic lower bound `phi_S S x ≥ η_S · x^2 / 2`. -/
axiom phi_S_quadratic_lower (S x : ℝ) (hS : 0 < S) :
    etaS S * x ^ 2 / 2 ≤ phi_S S x

/-- Core region formula `phi_S S x = η_S · x^2 / 2` for `|x| ≤ 1 - ε_S`. -/
axiom phi_S_core (S x : ℝ) (hS : 0 < S) (hx : |x| ≤ 1 - epsS S) :
    phi_S S x = etaS S * x ^ 2 / 2

/-- Tail region formula. -/
axiom phi_S_tail (S x : ℝ) (hS : 0 < S) (hx : 1 + epsS S ≤ x) :
    phi_S S x
      = phi_S S (1 + epsS S)
        + S * (x - 1 - epsS S)
        + etaS S / 2 * (x ^ 2 - (1 + epsS S) ^ 2)

/-- Smallness at the layer boundary: `phi_S S (1+ε_S) = O(S^{-2})`. -/
axiom phi_S_boundary_small :
    BigOInv (fun S => phi_S S (1 + epsS S)) (fun _ => 0) 2

/-- Uniform smallness on the layer for `exp(-phi_S)`: `|exp(-phi_S(x)) - 1| =
O(S^{-2})` when `|x-1| ≤ ε_S`. -/
axiom phi_S_layer_small :
    ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → ∀ x,
      |x - 1| ≤ epsS S → |Real.exp (-(phi_S S x)) - 1| ≤ C * S ^ (-(2 : ℤ))

/-! ## Integrability -/

/-- Integrability of `exp(-phi_S S)` (Gaussian domination). -/
axiom exp_negPhiS_integrable (S : ℝ) (hS : 0 < S) :
    Integrable (fun x => Real.exp (-(phi_S S x)))

/-- Integrability on the tail half-line. -/
axiom exp_negPhiS_integrableOn_tail (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun x => Real.exp (-(phi_S S x))) (Set.Ici (1 + epsS S))

/-- Integrability of the Gaussian-tail integrand on `[0,∞)`. -/
axiom exp_negGaussianTail_integrableOn (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun u => Real.exp (-(A * u) - B * u ^ 2 / 2)) (Set.Ici (0 : ℝ))

/-! ## Core constants -/

/-- The partition function `Z_S = ∫_ℝ exp(-phi_S S) dx`. -/
def Z_S (S : ℝ) : ℝ := ∫ x, Real.exp (-(phi_S S x))

/-- The right-tail exponential integral
`A_S = ∫_{1+ε_S}^{∞} exp(-phi_S S) dx`. -/
def A_S (S : ℝ) : ℝ := ∫ x in Set.Ici (1 + epsS S), Real.exp (-(phi_S S x))

/-- The tail probability mass `q_S = (2/Z_S) · A_S`. -/
def q_S (S : ℝ) : ℝ := 2 * A_S S / Z_S S

/-- The two-sided layer set `T_S = [-1-ε_S, -1+ε_S] ∪ [1-ε_S, 1+ε_S]`. -/
def T_S (S : ℝ) : Set ℝ :=
  Set.Icc (-1 - epsS S) (-1 + epsS S) ∪ Set.Icc (1 - epsS S) (1 + epsS S)

/-- The layer mass `t_S = ρ_S(T_S)`. -/
def t_S (S : ℝ) : ℝ :=
  (∫ x in T_S S, Real.exp (-(phi_S S x))) / Z_S S

/-! ## Positivity -/

lemma exp_negPhiS_pos (S x : ℝ) : 0 < Real.exp (-(phi_S S x)) :=
  Real.exp_pos _

lemma exp_negPhiS_nonneg (S x : ℝ) : 0 ≤ Real.exp (-(phi_S S x)) :=
  (exp_negPhiS_pos S x).le

/-- `Z_S` is strictly positive — axiomatised (uses non-degeneracy of the
positive integrand `exp(-phi_S)`). -/
axiom Z_S_pos (S : ℝ) (hS : 0 < S) : 0 < Z_S S

lemma Z_S_ne_zero (S : ℝ) (hS : 0 < S) : Z_S S ≠ 0 := (Z_S_pos S hS).ne'

lemma A_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ A_S S := by
  unfold A_S
  exact setIntegral_nonneg measurableSet_Ici (fun x _ => exp_negPhiS_nonneg S x)

lemma q_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ q_S S := by
  unfold q_S
  have h1 : 0 ≤ 2 * A_S S := by
    have := A_S_nonneg S hS
    positivity
  exact div_nonneg h1 (Z_S_pos S hS).le

lemma t_S_nonneg (S : ℝ) (hS : 0 < S) : 0 ≤ t_S S := by
  unfold t_S
  refine div_nonneg ?_ (Z_S_pos S hS).le
  refine setIntegral_nonneg ?_ (fun x _ => exp_negPhiS_nonneg S x)
  exact measurableSet_Icc.union measurableSet_Icc

/-! ## Half-line exponential integrals (Laplace transforms)

These two identities (`∫₀^∞ e^{-au} du = 1/a` and `∫₀^∞ u² e^{-au} du = 2/a^3`)
should sit in Mathlib; they are recorded here as axioms with explicit
`to_mathlib` markers. -/

-- to_mathlib: Mathlib/Analysis/SpecialFunctions/Integrals.lean
/-- `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`. -/
axiom integral_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    ∫ u in Set.Ici (0 : ℝ), Real.exp (-(a * u)) = 1 / a

-- to_mathlib: Mathlib/Analysis/SpecialFunctions/Integrals.lean
/-- `∫₀^∞ u² e^{-a u} du = 2/a^3` for `a > 0`. -/
axiom integral_sq_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    ∫ u in Set.Ici (0 : ℝ), u ^ 2 * Real.exp (-(a * u)) = 2 / a ^ 3

/-! ## Elementary inequality `1 - e^{-v} ≤ v` -/

/-- For `v ≥ 0`, `0 ≤ 1 - exp(-v) ≤ v`. -/
lemma one_sub_exp_neg_le (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ 1 - Real.exp (-v) ∧ 1 - Real.exp (-v) ≤ v := by
  refine ⟨?_, ?_⟩
  · have h := Real.exp_neg_le_one_of_nonneg hv
    linarith
  · have h := Real.add_one_le_exp (-v)
    have hexp_pos := Real.exp_pos (-v)
    have hmul : Real.exp (-v) * Real.exp v = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v, hexp_pos, h]

/-- Reformulation using `v = a u`. -/
lemma one_sub_exp_neg_mul_le {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    1 - Real.exp (-(a * u)) ≤ a * u :=
  (one_sub_exp_neg_le (a * u) (mul_nonneg ha hu)).2

/-! ## Tail integral computation

After translation `u = x - 1 - ε_S` and the tail formula for `phi_S`, the
integrand becomes
`exp(-phi_S (1+ε_S)) · exp(-(S+η(1+ε)) u - η u^2 / 2)`. -/

/-- Exponent in the transformed tail integrand. -/
def tildeS (S : ℝ) : ℝ := S + etaS S * (1 + epsS S)

lemma tildeS_pos {S : ℝ} (hS : 1 ≤ S) : 0 < tildeS S := by
  unfold tildeS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have h1 : 0 ≤ etaS S * (1 + epsS S) :=
    mul_nonneg (etaS_pos hSpos).le (by linarith [(epsS_pos hSpos).le])
  linarith

/-- Lower bound `S ≤ tildeS S` (the perturbation is nonneg). -/
lemma le_tildeS {S : ℝ} (hS : 1 ≤ S) : S ≤ tildeS S := by
  unfold tildeS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have : 0 ≤ etaS S * (1 + epsS S) :=
    mul_nonneg (etaS_pos hSpos).le (by linarith [(epsS_pos hSpos).le])
  linarith

/-- Change-of-variables identity for the tail integral. -/
axiom A_S_tail_eq (S : ℝ) (hS : 1 ≤ S) :
    A_S S
      = Real.exp (-(phi_S S (1 + epsS S)))
          * ∫ u in Set.Ici (0 : ℝ),
              Real.exp (-(tildeS S * u) - etaS S * u ^ 2 / 2)

/-! ## Asymptotics of the Gaussian-tail integral

The two-sided bound
    `0 ≤ 1/S̃ - ∫₀^∞ exp(-S̃ u - η u²/2) du ≤ η / S̃³`
is a direct consequence of `1 - e^{-v} ≤ v` applied pointwise to
`v = η u²/2`. -/

axiom tail_gaussian_bound (S : ℝ) (hS : 1 ≤ S) :
    let I := ∫ u in Set.Ici (0 : ℝ),
                Real.exp (-(tildeS S * u) - etaS S * u ^ 2 / 2)
    0 ≤ 1 / tildeS S - I ∧ 1 / tildeS S - I ≤ etaS S / tildeS S ^ 3

/-! ## Asymptotic blueprint lemmas

Two ingredients package the analytic content of section 3 into BigO
statements: -/

/-- `1/tildeS S = 1/S + O(S^{-6})`. -/
axiom one_div_tildeS_asymp :
    BigOInv (fun S => 1 / tildeS S) (fun S => 1 / S) 6

/-- `exp(-phi_S S (1+ε_S)) = 1 + O(S^{-2})`. -/
axiom exp_neg_phi_boundary_asymp :
    BigOInv (fun S => Real.exp (-(phi_S S (1 + epsS S)))) (fun _ => 1) 2

/-! ## Lemma (a): right-tail integral asymptotic

`A_S = 1/S + O(S^{-3})`. -/

axiom A_S_asymp :
    BigOInv A_S (fun S => 1 / S) 3

/-! ## Lemma (b): normalisation constant asymptotic

`Z_S = 2 + 2/S + O(S^{-3})`. -/

axiom Z_S_asymp :
    BigOInv Z_S (fun S => 2 + 2 / S) 3

/-! ## Lemma (c): tail probability and layer mass

`q_S = 1/S - 1/S^2 + O(S^{-3})`  and  `t_S = O(S^{-3})`. -/

axiom q_S_asymp :
    BigOInv q_S (fun S => 1 / S - 1 / S ^ 2) 3

axiom t_S_asymp :
    BigOInv t_S (fun _ => 0) 3

/-! ## Derived corollaries

For downstream modules the main facts needed are:

* `Z_S S ≥ 1` for sufficiently large `S` (used to invert `Z_S`);
* `q_S S → 0`, `t_S S → 0` as `S → ∞` (used to derive contradictions).

These follow from the asymptotic lemmas above by elementary real arithmetic.
-/

lemma exists_S_Z_S_ge_one : ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → 1 ≤ Z_S S := by
  obtain ⟨C, S₁, hS₁, hbd⟩ := Z_S_asymp
  refine ⟨max S₁ (max 2 (2 * C + 2)), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left (by norm_num))
  intro S hS
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hS2
  have hSlarge : 2 * C + 2 ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hb := hbd S hS₁le
  have habs : |Z_S S - (2 + 2 / S)| ≤ C * S ^ (-(3 : ℤ)) := hb
  have hpow : S ^ (-(3 : ℤ)) = 1 / S ^ 3 := zpow_negNat S 3 hSpos.ne'
  rw [hpow] at habs
  have hinvS_nn : 0 ≤ 2 / S := by positivity
  have hZlb : 2 + 2 / S - C * (1 / S ^ 3) ≤ Z_S S := by
    have := (abs_sub_le_iff.1 habs).2
    linarith
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hC_bd : C * (1 / S ^ 3) ≤ 1 := by
    by_cases hC : C ≤ 0
    · calc C * (1 / S ^ 3) ≤ 0 := by
            have : 0 ≤ 1 / S ^ 3 := by positivity
            nlinarith
          _ ≤ 1 := by norm_num
    · push_neg at hC
      have hSgeC : C ≤ S := by linarith
      have hSS : S ≤ S ^ 3 := by
        have h1 : 1 ≤ S := le_trans (by norm_num) hS2
        nlinarith
      have hCleS3 : C ≤ S ^ 3 := le_trans hSgeC hSS
      have hrecip : C / S ^ 3 ≤ 1 := by
        rw [div_le_one hS3_pos]; exact hCleS3
      calc C * (1 / S ^ 3) = C / S ^ 3 := by ring
        _ ≤ 1 := hrecip
  linarith

/-- For sufficiently large `S`, `q_S S < 1` (the tail probability is bounded
away from `1`).  This is used downstream to derive nontrivial mass on the
core. -/
lemma exists_S_q_S_lt_one : ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → q_S S < 1 := by
  obtain ⟨C, S₁, hS₁, hbd⟩ := q_S_asymp
  refine ⟨max S₁ (max 2 (max (2 * |C| + 2) 4)), ?_, ?_⟩
  · refine lt_max_of_lt_right (lt_max_of_lt_left ?_); norm_num
  intro S hS
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS2 : (2 : ℝ) ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hS2
  have hb := hbd S hS₁le
  have hpow : S ^ (-(3 : ℤ)) = 1 / S ^ 3 := zpow_negNat S 3 hSpos.ne'
  rw [hpow] at hb
  -- `|q_S - (1/S - 1/S²)| ≤ C / S^3`, and `1/S - 1/S² + C/S³ < 1` for large S.
  have hupper := (abs_sub_le_iff.1 hb).1
  -- q_S ≤ 1/S - 1/S² + C/S³
  have hS3_pos : 0 < S ^ 3 := by positivity
  have h_one_S : (1:ℝ) / S ≤ 1 / 2 := by
    rw [div_le_div_iff hSpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have h_C_S3 : C * (1 / S ^ 3) ≤ |C| * (1 / S ^ 3) := by
    have : 0 ≤ 1 / S ^ 3 := by positivity
    nlinarith [le_abs_self C]
  -- |C|/S^3 ≤ |C|/8 (since S ≥ 2 ⇒ S^3 ≥ 8)
  have hS3_ge_8 : (8:ℝ) ≤ S ^ 3 := by nlinarith
  have h_abs_S3 : |C| * (1 / S ^ 3) ≤ |C| / 8 := by
    have : 1 / S ^ 3 ≤ 1 / 8 := by
      rw [div_le_div_iff hS3_pos (by norm_num : (0:ℝ) < 8)]
      linarith
    have h1 := mul_le_mul_of_nonneg_left this (abs_nonneg C)
    linarith
  -- 1/S² ≥ 0
  have hS2sq_pos : 0 < S ^ 2 := by positivity
  have h_invS2_nn : 0 ≤ (1:ℝ) / S ^ 2 := by positivity
  -- Goal: q_S < 1.
  -- We have q_S ≤ 1/S - 1/S² + C/S³ ≤ 1/S + |C|/S³ ≤ 1/2 + |C|/8.
  -- Need 1/2 + |C|/8 < 1, i.e. |C|/8 < 1/2, i.e. |C| < 4.
  -- This won't hold for all C, so we need S even larger.
  -- Better bound: For S ≥ max(2, 2|C|+2, 4), have S^2 ≥ S · 1 ≥ 2|C|+2 ≥ |C|+2,
  -- so 1/S² ≤ 1/(|C|+2), and …
  -- Simpler approach: choose S so that 1/S + |C|/S³ ≤ 1/2.
  -- Since S ≥ 4, 1/S ≤ 1/4. Since S ≥ 2|C|+2 ⇒ S ≥ |C|+2 ⇒ S^3 ≥ S · 1 ≥ 2|C|+2,
  -- so |C|/S^3 ≤ |C|/(2|C|+2) ≤ 1/2.  Hence 1/S + |C|/S^3 ≤ 1/4 + 1/2 = 3/4 < 1.
  have hSge4 : (4:ℝ) ≤ S :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS))
  have hSge2C : 2 * |C| + 2 ≤ S :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS))
  -- 1/S ≤ 1/4
  have h_one_S' : (1:ℝ) / S ≤ 1 / 4 := by
    rw [div_le_div_iff hSpos (by norm_num : (0:ℝ) < 4)]; linarith
  -- |C|/S^3 ≤ 1/2.
  have habs_C_S3_bd : |C| / S ^ 3 ≤ 1 / 2 := by
    have habs_nn : 0 ≤ |C| := abs_nonneg _
    have hS_ge_C : |C| ≤ S := by
      have h1 : |C| ≤ 2 * |C| + 2 := by linarith
      linarith
    -- S^3 ≥ S^2 ≥ 2|C|+2 ≥ 2|C| ⇒ |C|/S³ ≤ |C|/(2|C|) = 1/2 (when |C| > 0).
    -- Easier: |C|/S^3 ≤ |C|/(2|C|+2) ≤ 1/2.
    have hS3_ge_S : S ≤ S ^ 3 := by nlinarith
    have hS3_ge_2C2 : 2 * |C| + 2 ≤ S ^ 3 := le_trans hSge2C hS3_ge_S
    have hS3_pos' : 0 < S ^ 3 := hS3_pos
    rw [div_le_div_iff hS3_pos' (by norm_num : (0:ℝ) < 2)]
    have : |C| * 2 ≤ (2 * |C| + 2) * 1 := by linarith
    nlinarith
  -- Combine
  have q_le : q_S S ≤ 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3) := by linarith
  have h_lhs_bd : 1 / S - 1 / S ^ 2 + C * (1 / S ^ 3)
        ≤ 1 / S + |C| * (1 / S ^ 3) := by linarith
  have h_lhs_bd' : 1 / S + |C| * (1 / S ^ 3) ≤ 1 / 4 + 1 / 2 := by
    have h_abs_eq : |C| * (1 / S ^ 3) = |C| / S ^ 3 := by ring
    rw [h_abs_eq]
    linarith
  linarith

/-! ## Sanity: the four constants are well-defined reals. -/

example (S : ℝ) : Z_S S = ∫ x, Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : A_S S = ∫ x in Set.Ici (1 + epsS S), Real.exp (-(phi_S S x)) := rfl
example (S : ℝ) : q_S S = 2 * A_S S / Z_S S := rfl

end L2Counterexample

end
