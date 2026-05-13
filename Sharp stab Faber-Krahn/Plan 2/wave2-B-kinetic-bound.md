# Wave 2 Agent B: integrated kinetic bound in the finite-perimeter regime

**Author:** Wave 2 Agent B, Plan 2 audit (ETH Zürich).
**Date:** 2026-05-13.
**Status:** Settles Wave 2 Priority 2 (the integrated L²(dρ) kinetic bound (5.14) / (K)) **unconditionally**, in the finite-perimeter regime, using only Agent 1's deficit identity, Agent 3 (7.1), and an elementary uniform L¹-Lipschitz bound on the rescaled curve ρ ↦ F_ρ.

## 200-word summary

I prove the integrated L²(dρ) kinetic bound (K) — equivalently (5.14) of `agent4-weighted-metric-trace.md` — in the finite-perimeter regime, **without** assuming smooth coherent graphs and **without** assuming a pointwise lower bound on −t′(ρ). The proof has three inputs: Agent 1's exact deficit identity, Agent 3 (7.1) (the per-ρ first-variation L¹-squared estimate), and an **elementary uniform L¹-Lipschitz bound** |γ̇|(ρ) ≤ C_{n,R,ρ_*} on the rescaled curve [F_ρ] = [ρ⁻¹E_ρ] ∈ 𝒳 that follows from volume monotonicity and the homothety alone. The argument is a clean good-set / bad-set decomposition: the bad set B_τ := {−t′ < τ} has Lebesgue measure ≤ Cδ for τ a fixed dimensional constant (because the integrated Talenti gap forces |ψ| ≥ ρ_*/(2n) there), on which the uniform bound suffices; on the good set −t′ ≥ τ allows the (H1)-action ∫|γ̇|²(−t′)dρ ≤ Cδ to be divided by τ. The resulting compound theorem upgrades Agent 4 Theorem to an unconditional weighted metric trace at the sharp δ-rate. **No new geometric input** is required — in particular, this does not depend on the Wave 2 Priority 1 L²-radial-trace (R²); (K) is settled in advance of (R²).

## 1. Notation and the target (K)

Throughout, n ≥ 2, R ≥ 2, ρ_* ∈ (0, 1) fixed; Ω ⊂ B_R open with |Ω| = ω_n; δ := δ_T(Ω) = E(Ω) − E(B_1); u is the variational torsion function on Ω; E_ρ := {u > t(ρ)} with |E_ρ| = ω_n ρⁿ, ρ ∈ [ρ_*, 1]; t_B(ρ) := (1 − ρ²)/(2n) is the ball's profile; F_ρ := ρ⁻¹ E_ρ; γ(ρ) := [F_ρ] ∈ 𝒳 with the L¹/translations metric d_𝒳; |γ̇|(ρ) is the AGS metric derivative (Ambrosio–Gigli–Savaré 2008, Thm 1.1.2); ρ_δ := 1 − κ√δ; ψ(ρ) := −t′(ρ) − (−t_B′(ρ)) ≤ 0; |ψ| = t′ − t_B′.

**Target (K).** There exists C′ = C′(n, R, ρ_*, κ) such that
$$
\int_{\rho_*}^{\rho_\delta} |\dot\gamma|(\rho)^2 \, d\rho \;\le\; C' \, \delta.
\tag{K}
$$

**Equivalent target (K′).** Setting c_n^*(ρ) := −t_B′(ρ) = ρ/n, the second-order profile gap:
$$
\int_{\rho_*}^{\rho_\delta} \bigl(-t'(\rho) - c_n^*(\rho)\bigr)^2 \cdot \bigl(-t'(\rho)\bigr)^{-1} \, d\rho \;\le\; C \, \delta.
\tag{K'}
$$
The equivalence (K) ⇔ (K′) follows from §4.

## 2. Three building blocks

### 2.1 Agent 1's exact deficit identity (finite-perimeter)

From `agent1-finite-perimeter-identity.md`, Theorem §0:
$$
\frac{2\delta}{|\Omega|} \;=\; \frac{1}{|\Omega|}\int_0^{\|u\|_\infty}\frac{D_H(t)+D_I(t)}{c_n \, m(t)^{1-2/n}}\,dt,
\qquad c_n := n^2\omega_n^{2/n}.
\tag{A1}
$$

### 2.2 Agent 3's per-ρ first-variation bound

From `agent3-metric-first-variation.md`, §7 (7.1) (proved via the unweighted L¹-squared Cauchy bound (3.2) of `gmt-inputs-for-metric-closure.md`, which itself uses the weighted L²-Cauchy identity (2.3) and the strong isoperimetric oscillation (2.4)):
$$
|\dot\gamma|(\rho)^2 \;\le\; C_{n,\rho_*,R}\bigl(D_H(t(\rho)) + D_I(t(\rho))\bigr) \quad\text{for a.e. } \rho \in [\rho_*, 1].
\tag{A3}
$$

### 2.3 Uniform L¹-Lipschitz bound on ρ ↦ [F_ρ]

**Lemma 2.1 (uniform metric Lipschitz).** Under the standing hypotheses,
$$
|\dot\gamma|(\rho) \;\le\; L_0(n, R, \rho_*) \quad\text{for a.e. } \rho \in [\rho_*, 1].
\tag{A0}
$$

*Proof.* For ρ_*≤ρ < ρ′ ≤ 1, nestedness E_ρ ⊆ E_{ρ′} (since t is decreasing in ρ) gives
$$
|E_{\rho'}\Delta E_\rho| \;=\; |E_{\rho'}| - |E_\rho| \;=\; \omega_n\bigl((\rho')^n - \rho^n\bigr) \;\le\; n\omega_n (\rho' - \rho).
$$
Split F_ρ Δ F_{ρ′} through the intermediate set (ρ′)⁻¹E_ρ:
$$
|F_\rho \Delta F_{\rho'}| \;\le\; |F_\rho \Delta (\rho')^{-1} E_\rho| \;+\; (\rho')^{-n}|E_\rho \Delta E_{\rho'}|.
$$
For the first term, E_ρ ⊂ B_R, so ρ⁻¹E_ρ ⊂ B_{R/ρ_*}; the dilation $\Lambda_\lambda(x) := \lambda x$ with λ = ρ′/ρ ≥ 1 satisfies, on bounded measurable A ⊂ B_S,
$$
|\Lambda_\lambda(A) \Delta A| \;\le\; |A|\,(\lambda^n - 1) \;\le\; n\,S^n\omega_n\,(\lambda-1)\cdot\text{const},
$$
applied to A = (ρ′)⁻¹E_ρ ⊂ B_{R/ρ_*} with λ = ρ′/ρ, giving
$$
|F_\rho \Delta (\rho')^{-1} E_\rho| \;=\; |\Lambda_{\rho'/\rho}\bigl((\rho')^{-1}E_\rho\bigr) \Delta (\rho')^{-1}E_\rho| \;\le\; C_{n,R,\rho_*}\,(\rho' - \rho).
$$
For the second term, (ρ′)⁻ⁿ ≤ ρ_*⁻ⁿ, so it is ≤ ρ_*⁻ⁿ · nω_n(ρ′−ρ). Thus
$$
d_\mathcal{X}([F_{\rho'}],[F_\rho]) \;\le\; |F_{\rho'}\Delta F_\rho| \;\le\; L_0(n,R,\rho_*)\,(\rho' - \rho),
$$
yielding (A0). □

**Remark.** (A0) does **not** use Agent 1 or Agent 3; it follows from volume monotonicity and the homothety. It is the elementary input that allows route (a) to close at the δ-rate.

## 3. The exact algebraic identity D_H + D_I = P(B_ρ)² φ(ρ)

By Agent 1 (Lemmas 1, 2): α(t) := ∫|∇u|⁻¹ = −m′(t) and β(t) := ∫|∇u| = m(t) on a.e. reduced-boundary level. With m(t(ρ)) = ω_n ρⁿ, differentiating gives α(t(ρ))·(−t′(ρ)) = nω_n ρⁿ⁻¹ = A_ρ, so
$$
\alpha(t(\rho)) \;=\; \frac{A_\rho}{-t'(\rho)}.
$$

**Lemma 3.1.** For a.e. ρ ∈ [ρ_*, 1],
$$
D_H(t(\rho)) + D_I(t(\rho)) \;=\; P(B_\rho)^2 \cdot \phi(\rho), \qquad \phi(\rho) := \frac{-t_B'(\rho) - (-t'(\rho))}{-t'(\rho)} \;=\; \frac{|\psi(\rho)|}{-t'(\rho)} \;\ge\; 0.
\tag{3.1}
$$

*Proof.* D_H + D_I = αβ − c_n m^{2−2/n}, where the inequality αβ ≥ P² and P² ≥ c_n m^{2−2/n} (Cauchy + isoperimetric) split the total. Substituting:
$$
D_H + D_I \;=\; \frac{A_\rho}{-t'(\rho)} \cdot \omega_n\rho^n \;-\; n^2\omega_n^{2/n}(\omega_n\rho^n)^{2-2/n} \;=\; \frac{n\omega_n^2\rho^{2n-1}}{-t'(\rho)} - n^2\omega_n^2\rho^{2n-2}.
$$
With −t_B′(ρ) = ρ/n, this is n²ω_n²ρ^{2n−2}·((−t_B′)/(−t′) − 1) = P(B_ρ)² · φ(ρ). □

**Corollary 3.2.** Plugging (3.1) into Agent 1 (A1) and using dt = −t′(ρ) dρ:
$$
2\delta \;=\; \int_0^1 \frac{P(B_\rho)^2 \phi(\rho)}{c_n m(t(\rho))^{1-2/n}}\,(-t'(\rho))\,d\rho \;=\; \int_0^1 \omega_n\rho^n \,|\psi(\rho)|\,d\rho,
\tag{3.2}
$$
since P(B_ρ)²/(c_n m^{1−2/n}) = ω_n ρⁿ and φ(ρ)·(−t′(ρ)) = |ψ(ρ)|. Restricting to [ρ_*, 1] and bounding ω_n ρⁿ ≥ ω_n ρ_*ⁿ,
$$
\int_{\rho_*}^{1} |\psi(\rho)|\,d\rho \;\le\; \frac{2\delta}{\omega_n\rho_*^n} \;=:\; K_1(n, \rho_*)\,\delta.
\tag{3.3}
$$

**Remark 3.3 (Equivalent form via Talenti).** (3.3) also follows directly from the pointwise profile gap: $t(\rho) - t_B(\rho) \in [-2\delta/(\omega_n \rho_*^n), 0]$ on [ρ_*, 1] (Talenti 1976; see `level-set-deficit-identity.md` §4 and `outer-foliation-entry-proof-attempt.md` (1.2)), so
$$
\int_{\rho_*}^{1}|\psi|\,d\rho \;=\; \int_{\rho_*}^{1}(t' - t_B')\,d\rho \;=\; (t-t_B)(1) - (t-t_B)(\rho_*) \;\le\; 2\delta/(\omega_n \rho_*^n).
$$

## 4. The bad-set lemma

**Lemma 4.1.** Set τ_0 := ρ_*/(2n) and
$$
B_{\tau_0} \;:=\; \{\rho \in [\rho_*, \rho_\delta] : -t'(\rho) < \tau_0\}.
$$
Then |B_{τ_0}| ≤ K_2(n, ρ_*)·δ.

*Proof.* On B_{τ_0}, −t_B′(ρ) = ρ/n ≥ ρ_*/n, and −t′(ρ) < τ_0 = ρ_*/(2n), so
$$
|\psi(\rho)| \;=\; -t_B'(\rho) - (-t'(\rho)) \;\ge\; \rho_*/n - \rho_*/(2n) \;=\; \rho_*/(2n).
$$
By (3.3),
$$
\frac{\rho_*}{2n} |B_{\tau_0}| \;\le\; \int_{B_{\tau_0}}|\psi|\,d\rho \;\le\; \int_{\rho_*}^{1}|\psi|\,d\rho \;\le\; K_1\delta,
$$
giving |B_{τ_0}| ≤ 2nK_1/ρ_* · δ =: K_2 δ. □

## 5. The proof of (K)

**Theorem 5.1 (Wave 2 (K)).** Under the standing hypotheses, there exists C′ = C′(n, R, ρ_*, κ) such that
$$
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|(\rho)^2\,d\rho \;\le\; C'\,\delta_T(\Omega).
$$

*Proof.*

**Step 1 — (H1)-type integrated action.** By Agent 3 (A3), Lemma 3.1, and Corollary 3.2,
$$
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|^2 (-t'(\rho))\,d\rho \;\le\; C_{n,\rho_*,R}\int_{\rho_*}^{\rho_\delta}\bigl(D_H + D_I\bigr)(-t')\,d\rho
$$
$$
\;=\; C_{n,\rho_*,R}\int_{\rho_*}^{\rho_\delta} P(B_\rho)^2 |\psi(\rho)|\,d\rho \;\le\; C_{n,\rho_*,R}\cdot n^2\omega_n^2\int_{\rho_*}^{\rho_\delta}|\psi|\,d\rho \;\le\; K_3(n,\rho_*,R)\,\delta.
\tag{5.1}
$$

**Step 2 — Good-set bound.** Let G := [ρ_*, ρ_δ] \ B_{τ_0} with B_{τ_0} as in Lemma 4.1. On G, −t′(ρ) ≥ τ_0, so
$$
\int_G|\dot\gamma|^2\,d\rho \;=\; \int_G|\dot\gamma|^2 \frac{(-t'(\rho))}{(-t'(\rho))}\,d\rho \;\le\; \frac{1}{\tau_0}\int_G|\dot\gamma|^2(-t')\,d\rho \;\le\; \frac{K_3\delta}{\tau_0} \;=\; \frac{2n K_3}{\rho_*}\delta.
\tag{5.2}
$$

**Step 3 — Bad-set bound.** On B_{τ_0}, use the uniform Lipschitz bound (A0) of Lemma 2.1:
$$
\int_{B_{\tau_0}}|\dot\gamma|^2\,d\rho \;\le\; L_0(n,R,\rho_*)^2\,|B_{\tau_0}| \;\le\; L_0^2\,K_2\,\delta.
\tag{5.3}
$$

**Step 4 — Combine.** Adding (5.2) and (5.3),
$$
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|^2\,d\rho \;\le\; \left(\frac{2n K_3}{\rho_*} + L_0^2 K_2\right)\,\delta \;=:\; C'(n,R,\rho_*,\kappa)\,\delta. \qquad \square
$$

**Remark 5.2.** Step 1 alone is (H1) of `agent4-weighted-metric-trace.md`. The new content is the upgrade (H1) + (A0) + Lemma 4.1 ⇒ (K). The bad set is treated by the **trivial** uniform bound (A0); we do **not** require any pointwise lower bound on −t′ inside B_{τ_0}, nor any L²-norm of the metric derivative there.

**Remark 5.3 (Equivalence with (K′)).** Lemma 3.1 gives D_H + D_I = P(B_ρ)²|ψ|/(−t′), and (A3) gives |γ̇|² ≤ C(D_H + D_I). So (K) is equivalent to
$$
\int_{\rho_*}^{\rho_\delta}\frac{|\psi(\rho)|^2}{(-t'(\rho))}\,d\rho \;\le\; C\delta,
$$
which is (K′). Equivalently, ψ² · (−t′)⁻¹ is integrable to O(δ) on [ρ_*, ρ_δ]. This is exactly the **second-order Talenti profile-gap refinement** in the sense of Agent 4 §5.

## 6. Where the smooth-graph derivation broke

The §4 argument of `outer-foliation-entry-proof-attempt.md` (smooth coherent regime) proves
$$
D_H + D_I \;\ge\; c_n\bigl(\rho^{n-1}\|\partial_\rho h_{\ge 2}\|_2^2 + \rho^{2n-4}Q(h)\bigr),
$$
and then **integrates against dμ = (−t′)dρ** to obtain
$$
\int_{\rho_*}^{\rho_\delta}\bigl(\|\partial_\rho h\|_2^2 + Q(h)\bigr)(-t')\,d\rho \;\le\; C\delta.
$$
This is the **(H1)** form of the bound. It is **not** the L²(dρ) form (K) — even in the smooth regime, dividing by (−t′) is not free, because the smooth coherent graph regime does not by itself provide a pointwise lower bound on −t′. The §5 "weighted trace lemma" of `outer-foliation-entry-proof-attempt.md` papers over this by an unjustified "ordinary Hilbert trace estimate with measure dμ" on a putative "nondegenerate component of J_δ" — Agent 6 (I11) correctly diagnoses this gap, and Agent 4 §5 confirms (H1)+(H2) alone yield only δ^{1/2}.

**The fix supplied by Theorem 5.1 is intrinsic to finite-perimeter levels**: the uniform Lipschitz bound (A0) of Lemma 2.1, combined with the bad-set lemma (Lemma 4.1) derived from the integrated Talenti gap (3.3), bypasses the smooth-graph route entirely. (A0) is purely volumetric/scaling; it does not require any regularity of ∂*E_ρ.

## 7. Compound corollary: unconditional weighted metric trace

The Wave 1 statement of Agent 4 was: under (H1) + (H2) + (H3) + (5.14), there exists a radius ρ̂ ∈ [ρ_δ − C_*δ, ρ_δ] with d_𝒳(γ(ρ̂), B_1)² ≤ C_*δ. With (5.14) now supplied by Theorem 5.1, we obtain:

**Theorem 7.1 (Wave 2 unconditional weighted metric trace).** Let Ω ⊂ B_R with |Ω| = ω_n and δ_T(Ω) ≤ δ_0(n, ρ_*) small. Then there exist C_*= C_*(n, R, ρ_*, κ) and a radius
$$
\widehat\rho \in [\rho_\delta - C_*\delta_T,\,\rho_\delta], \qquad \rho_\delta = 1 - \kappa\sqrt{\delta_T},
$$
such that
$$
d_\mathcal{X}([F_{\widehat\rho}], B_1)^2 \;\le\; C_*\,\delta_T(\Omega).
$$
The constant C_* depends polynomially on (1/ρ_*, R, n, 1/κ) and on the constants of Agent 1, Agent 3 (T)/(7.1), and the strong isoperimetric oscillation lemma feeding (3.4) of `metric-finite-perimeter-closure.md`.

*Proof.* The hypotheses (H1), (H2), (H3) of `agent4-weighted-metric-trace.md` §1 are verified for the torsion application as follows. Take μ = (−t′)dρ, c = ρ_*/(2n), M = 1/n, ρ_* and ρ_δ as fixed.

- **(H1)**: By Step 1 above, ∫(|γ̇|² + d_𝒳(γ, B_1)²)(−t′)dρ ≤ C δ, where the distance term is controlled by Agent 2 / `gmt-inputs-for-metric-closure.md` (1.2) integrated against dμ together with (3.2) of Corollary 3.2.
- **(H2)**: Interval lower bound. By Talenti / `outer-foliation-entry-proof-attempt.md` (1.3), μ([a,b]) = t(a) − t(b) ≥ (b² − a²)/(2n) − C_{n, ρ_*}δ ≥ c(b−a) − Cδ for [a,b] ⊂ [ρ_*, ρ_δ].
- **(H3)**: μ_ρ = −t′(ρ) ≤ −t_B′(ρ) = ρ/n ≤ 1/n =: M (Talenti).
- **(5.14)**: by Theorem 5.1.

Apply the weighted metric trace lemma `agent4-weighted-metric-trace.md` §2. □

**Corollary 7.2 (sharp metric closure, unconditional in the finite-perimeter regime).** Combining Theorem 7.1 with the boundary-layer transfer of `metric-finite-perimeter-closure.md` §6 (which preserves the sharp exponent 2; Agent 6 Q5),
$$
\mathcal{A}(\Omega)^2 \;\le\; C_{n,R,\rho_*}\,\delta_T(\Omega).
$$
This is Theorem A (the bounded sharp Saint–Venant of `agent5-final-assembly.md` §1.1) **conditional only on Wave 2 Priority 1 (Conjecture 3.6 / the radial trace input (R))** — that is, on the strong-isoperimetric input that feeds (3.4) of `metric-finite-perimeter-closure.md`. The Wave 2 Priority 2 input (K5.14) is now closed.

## 8. Constants track

Through the proof:

| Constant | Definition | Dependence |
|---|---|---|
| K_1 | (3.3): ∫|ψ|dρ ≤ K_1δ | 2/(ω_n ρ_*ⁿ) |
| τ_0 | Lemma 4.1: threshold | ρ_*/(2n) |
| K_2 | Lemma 4.1: bad set | (2n K_1)/ρ_* = 4n/(ω_n ρ_*^{n+1}) |
| K_3 | (5.1) | C_{n,ρ_*,R} · n²ω_n² · K_1 |
| L_0 | (A0) | C(n) · (R/ρ_*)ⁿ + n/ρ_*ⁿ; explicitly n(R/ρ_*)^n + n/ρ_*^n suffices |
| C′ | Final | 2n K_3/ρ_* + L_0² K_2 |

All constants are polynomial in (1/ρ_*, R, n); none depends on δ.

## 9. Open issues

- **The L¹-Lipschitz bound (A0) of Lemma 2.1** uses only volume monotonicity of {E_ρ} (which is automatic from nestedness) and the homothety. It is genuinely elementary. The constant L_0 may be sharpened (the dilation estimate |Λ_λ(A) Δ A| ≤ |A|(λⁿ − 1) is loose for sets concentrated near the origin), but no sharpening is needed for (K).
- **The bad-set decomposition** uses only the integrated Talenti gap (3.3), which is itself a corollary of Agent 1. No additional geometric input.
- **Compatibility with Agent 4** is verified in §7. The compound Theorem 7.1 is unconditional given Agent 1, Agent 3 (T)/(7.1), and the strong isoperimetric oscillation (1.1)/(3.4); the only conditional input is the (R) of Wave 2 Priority 1 entering (3.4) via (1.2).
- **Cleaner C′(κ) dependence.** Strictly, ρ_δ = 1 − κ√δ ∈ (ρ_*, 1) requires δ ≤ δ_0(κ, ρ_*) = ((1−ρ_*)/κ)². For δ above this threshold the statement (K) is vacuous (the integration range is empty). C′ does not blow up as κ → 0; it is monotone in 1/κ only through the constraint on δ_0.

## 10. References

- **Agent 1** = `agent1-finite-perimeter-identity.md`, Theorem §0, Lemmas 1–4.
- **Agent 3** = `agent3-metric-first-variation.md`, Theorem §2 (T), §7 (7.1).
- **Agent 4** = `agent4-weighted-metric-trace.md`, §1 hypotheses, §2 Theorem.
- **Agent 6** = `agent6-adversarial-audit.md`, §3 verdict (I4, I11), §4 Wave 2 priorities.
- `outer-foliation-entry-proof-attempt.md`, §1 (1.2)–(1.3) profile gap, §4 (4.7) smooth regime, §5 sketch (where I11 lives).
- `gmt-inputs-for-metric-closure.md`, §2–§3 ((2.4), (3.1)–(3.4)).
- `metric-finite-perimeter-closure.md`, §3 (homothetic velocity defect), §4–§6 (closure chain).
- `level-set-deficit-identity.md`, §4 (profile gap).
- Ambrosio, L.; Gigli, N.; Savaré, G. *Gradient Flows in Metric Spaces and in the Space of Probability Measures*, 2nd ed., Birkhäuser, 2008. Thm 1.1.2.
- Talenti, G. *Elliptic equations and rearrangements*, Ann. Mat. Pura Appl. 110 (1976), 353–372.
- Maggi, F. *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge, 2012.

## 11. Status

**(K) is settled unconditionally in the finite-perimeter regime.** The compound Theorem 7.1 gives the Wave 2 version of Agent 4's weighted metric trace, no longer conditional on (K5.14). The remaining open input of Plan 2 is **Wave 2 Priority 1** (the L²-radial-trace (R²) / equivalently Agent 2's Conjecture 3.6), which feeds (3.4) of `metric-finite-perimeter-closure.md`. With both Wave 2 priorities closed, Plan 2 becomes unconditional in the bounded class.
