# Agent 6 — Adversarial audit of Plan 2 metric route

## Verdict summary (≈200 words)

Plan 2 is structurally sound but **two genuine gaps remain**, and a third issue (smuggled Lipschitz parametrization in Agent 2's remediation (a)) shows the conjectured remediations are not all "no-graph". Agent 2 has correctly isolated the **radial L¹-trace (R) / Conjecture 3.6** as the genuine bottleneck. Of the three remediations: (a) breaks the brief's "no graph" rule by importing a Lipschitz parametrization; (b) misquotes the Fusco–Julin rate (the published Hausdorff containment is η = O((P−P(B_ρ))^{1/(2(n−1))}), **not** O(√(P−P(B_ρ))) as claimed); (c) — the L² form — is the only honest path, but Agent 4's bookkeeping then forces a second-order profile-gap that is not in the repo. Agent 4's diagnosis is correct: (H1)+(H2) yields only δ^{1/2}, and the auxiliary kinetic bound (5.14) is genuinely required and is **not** in fact proved anywhere (only sketched). Agents 1 and 3 are clean. The boundary-layer transfer is correct up to an explicit factor 2. Compared to Plan 1 (Route A), which is unconditional, Plan 2 is **strictly weaker as of now**; its scientific value, if closed, is the no-selection, no-nearly-spherical claim, which extends to rougher classes but produces no new theorem in the FK setting.

---

# Detailed bug report

## 1. Severity table

| # | Location | Issue | Severity | Repairability |
|---|----------|-------|----------|--------------|
| **I1** | `agent2-homothetic-velocity-defect.md` §3.6 (Conjecture 3.6) | Radial L¹-trace estimate (R) is the genuine missing input; (1.2) of `gmt-inputs-for-metric-closure.md` *asserts* (R) but the proof there is a one-line hand-wave that doesn't close. | **Substantive, not fatal.** | Needs a real theorem; see issue I2 / I3. |
| **I2** | `agent2-homothetic-velocity-defect.md` §5, remediation (a) | "Lipschitz parametrisation supplied by Cicalese–Leonardi 2012" violates the brief's "no graph parametrization" rule. | **Methodological**: this remediation, if used, makes Plan 2 collapse into a Plan 1-style argument. | Replace by (c) or (b), but each has its own issue. |
| **I3** | `agent2-homothetic-velocity-defect.md` §5, remediation (b) | Claim "Fusco–Julin Hausdorff containment with η = O(√(P−P(B_ρ)))" appears not to be in the cited literature explicitly. The Esposito–Fusco–Trombetti / Fusco–Julin results give η at a worse rate (typically η = O((P−P(B_ρ))^{α}) with α < 1/2). | **Substantive.** If the brief's "no-better-than-√δ" stance is enforced, this *is* the right rate, but it is not in the published literature in this form. | Either find a sharper version (possibly in newer Acharya–Bressan-style stability papers) or accept that (b) does not close (R) at the rate Plan 2 needs. |
| **I4** | `agent4-weighted-metric-trace.md` §1 (K5.14) and §9 | Bound (5.14), the integrated L²(dρ) kinetic bound, is asserted to follow "for free" from the Cauchy–deficit identity, but the actual derivation is **not in the repo**. The hand-off is to `outer-foliation-entry-proof-attempt.md` §4–8, which proves it only in the smooth coherent graph regime. | **Substantive, repairable in principle.** | Either prove M − c = O(δ) (a second-order profile-gap refinement, not obviously true for finite-perimeter levels), or supply the integrated L² Cauchy–deficit bookkeeping rigorously. |
| **I5** | `agent3-metric-first-variation.md` §0, §3.1 | The center field z_ρ is "piecewise constant on a finite block decomposition, Borel measurable". This means at block-boundary points of ρ, the curve ρ ↦ [F_ρ] in 𝒳 is *continuous* (the jump is by a translation, which is killed by the quotient) — but the **pointwise** velocity V_ρ − H_{z_ρ,ρ} − a·ν_ρ inherits the discontinuity. The infimum-over-a regularises this, but the proof should explicitly check that the L¹(ρ)-integrability of the right-hand side of (T) is unaffected by the finitely many jump points. Currently glossed. | **Wording/normalization.** | Add one paragraph: at a jump point, V_ρ is unchanged, H_{z,ρ} changes by a hyperplane affine function, which is exactly the a·ν_ρ mode; the infimum then sees nothing of the jump. |
| **I6** | `agent3-metric-first-variation.md` §3, eqs. (3.1)–(3.6) | The smooth proof uses a *smooth* foliation X(ρ,x) of ∂E_ρ. This is OK on smooth domains, but the BV approximation in §4 requires that the *normal velocities* V_ρ^k of the smoothed levels converge to V_ρ on ∂*E_ρ. The proof relies on coarea (4.6) for the L¹-norm of V_ρ^k, but for the **integrand inside the infimum** (V_ρ^k − H_{z,ρ} − a·ν_ρ^k), one needs Reshetnyak continuity for *vector-valued perimeter measures*, which is invoked but where the *upper* semicontinuity (not just lower) is needed to pass from the smooth bound (3.8) to the BV limit. AGS Thm 1.1.2 gives this via the m_k ⇀ m route in §4.4, which is correct, but only assuming **uniform L¹(ρ)-boundedness** of m_k — which itself depends on Agent 2's defect lemma applied to u_k. Since C3.6 is conditional, the BV passage is not formally complete. | **Conditional on I1.** | Once I1 is settled, the BV passage closes. |
| **I7** | `metric-finite-perimeter-closure.md` §6, line 270 | The bound $\|\Omega\setminus E_{\widehat\rho}\|=\omega_n(1-\widehat\rho^n)\le C_n\sqrt\delta$ uses $\widehat\rho\ge\rho_\delta-C\delta=1-\kappa\sqrt\delta-C\delta$. For small δ this is correct. Note that |Ω \ E_{ρ̂}| = ω_n − ω_n ρ̂^n is **only** valid when |E_ρ̂| = ω_n ρ̂^n is exact, which is by construction (volume parametrization). Fine. | **Clean.** | — |
| **I8** | `metric-finite-perimeter-closure.md` §6, A(Ω) ≤ A(E_{ρ̂}) + C_n√δ | The asymmetries are computed with *different* reference balls (B_1 vs B_{ρ̂}). The estimate uses Lemma 8.3 of `level-set-deficit-identity.md`, which is correct in the regime |Ω \ E_t| ≪ L, with an explicit factor 2η/L = O(√δ). Squaring: A(Ω)² ≤ 2A(E_{ρ̂})² + O(δ). | **Clean.** Sharp exponent 2 preserved. | — |
| **I9** | `agent5-final-assembly.md` §1.1, Theorem A and §3 (constants table) | The constants table tracks R-dependence correctly. There is one quiet issue: C_{n,ρ_*,R} ~ R^{n−1} for the homothetic velocity defect lemma; after applying at R = R_*(n) = max(d(n),2), the Plan 2 constant feeds into BoundedReduction.tex Lemma 4.2. Lemma 4.2's reciprocal 1/c̃_SV(n) is then ~ R_*(n)^{n−1}, which is acceptable but should be flagged. | **Bookkeeping.** | — |
| **I10** | Across all notes | **No agent verifies that on ∂*E_ρ, the integral identity (L2) "∫|∇u| = m(t)" needs that {|∇u|=0} has H^{n−1}-zero on ∂*E_ρ for a.e. ρ.** Agent 1 §1 explicitly states this is *not* needed (because the formal trace is bypassed by Lipschitz truncation), but Agent 3's V_ρ = −t'(ρ)/|∇u| **does** require |∇u| > 0 H^{n−1}-a.e. on ∂*E_ρ for V_ρ to be defined as a function. Agent 3 §0 states this implicitly. For *Sobolev* (not C¹) u, this requires a Sard-for-Sobolev theorem. Such theorems exist (Figalli–Maggi 2011; De Philippis–Marini–Mukoseeva 2021), but neither is cited in Agent 3. | **Wording/citation.** | Cite Figalli–Maggi 2011 Thm A.1 or equivalent. |
| **I11** | `outer-foliation-entry-proof-attempt.md` §4 vs `agent4-weighted-metric-trace.md` §9 | Agent 4 says "see `outer-foliation-entry-proof-attempt.md` §4 for the bookkeeping" supplying K5.14. But that §4 is explicitly **in the smooth coherent graph regime** with ‖h‖_{C¹} small. It does *not* supply K5.14 for the finite-perimeter family. The hand-off is broken. | **Substantive.** Together with I4 this is the second genuine open item. | Same fix as I4. |
| **I12** | `gmt-inputs-for-metric-closure.md` §1, eq. (1.2) | The "radial trace estimate" (1.2) is **asserted, not proved**. The half-line proof on lines 51–55 ("the oscillation index controls the boundary-normal defect, while the Fraenkel part controls the volume of the radial mismatch...") is a hand-wave; Agent 2 §3.6 correctly identifies that this is exactly the missing Conjecture 3.6. | **Documentation.** Note that the *source note* `gmt-inputs-for-metric-closure.md` was written under the misimpression that (1.2) follows from (1.1). Agent 2 corrects this. | — |

---

## 2. Q-by-Q treatment

### Q1. Hidden graph regularity?

**Agent 1:** clean. The "Lipschitz" in Lemma 2 refers to the *test function* φ_ε ∘ (u−t), not a parametrization of ∂*E_t. ✓

**Agent 3 §3 (smooth case):** explicitly assumes a smooth flow, with the boundary parametrized by a smooth motion X(ρ,x). This is for the purpose of deriving (3.1)–(3.7) cleanly, and the §4 BV-approximation step is invoked to remove it. The approximation step §4.3 uses Reshetnyak lower semicontinuity, which is standard. **One subtle point** (I6): the upper bound on |Ḟ_ρ| from the smooth case uses the *full* integrand |V−H−a·ν|, and Reshetnyak gives only lower semicontinuity. The passage closes via AGS Thm 1.1.2 + Dunford–Pettis (m_k ⇀ m), which is correct but requires uniform L¹(ρ) bounds on m_k, themselves depending on Agent 2 / Conjecture 3.6 applied to u_k. Conditional on I1.

**Agent 2 §5 remediation (a):** This **does** smuggle a Lipschitz graph (I2). Cicalese–Leonardi 2012 ARMA does not by itself supply a Lipschitz parametrization of ∂*E; that is Fusco–Julin 2014 (which Cicalese–Leonardi calls in). Either way, remediation (a) explicitly violates the brief.

**Agent 4:** clean — no graph entry.

**Verdict on Q1:** No agent's main proof requires a graph, but **Agent 2's remediation (a) does**, which means Plan 2 cannot close via (a) without violating the brief. Only (b) or (c) are "no-graph" remediations; both have their own issues (I3, I4).

### Q2. FvHT center gluing rate.

**Reading:** `fvht-center-gluing-import.md` §4 gives |z_j − z_{j+1}| ≤ C(ε_j + ε_{j+1}), where ε_j = Φ_j(z_j) is the block integrated L¹ closeness. The natural rate is ε_j ≲ ∫ inf_z |E_ρ Δ (z+B_ρ)| dρ ≲ √(∫ D_I) ≲ √δ (Cauchy–Schwarz on the block).

So FvHT controls centers at **O(√δ)**, no better. This is consistent with the deployment brief's expected scale, and §5 of `fvht-center-gluing-import.md` explicitly flags this.

**Downstream uses of z_ρ:**
- Agent 3 §0–§5 uses z_ρ only as an L^∞ measurable field (|z_ρ| ≤ R + R'); no rate needed.
- Agent 2 / `metric-finite-perimeter-closure.md` §3.4: uses z_ρ in (3.4) ∫|H_{z_ρ,ρ} − V̄_ρ| ≲ √(D_I(t(ρ))). This requires z_ρ to be the **Fraenkel asymmetry center** of E_ρ, not the FvHT block center.

**Issue:** The two centers — FvHT block center (which jumps in ρ) and Fraenkel center per ρ — are not the same. Agent 3 cites FvHT (z_ρ piecewise constant), but Agent 2's Lemma 3.2 needs the Fraenkel center. The reconciliation is that **on overlapping blocks**, the FvHT center is close to the Fraenkel center (Cicalese–Leonardi uniqueness). This is implicit; it should be made explicit. **Minor.**

**Verdict on Q2:** FvHT controls at O(√δ), and no downstream use needs better. The proof avoids overcommitting. ✓ With a minor wording fix on the FvHT-vs-Fraenkel center identification.

### Q3. Is the homothetic velocity defect controlled by D_I? (Conjecture 3.6.)

**Confirmation of Agent 2's diagnosis:** correct. The algebraic chain in §3.1 cleanly reduces (*) to the radial L¹-trace (R), and §3.3 shows that the slicing route from (R) leads back to the equivalent (C3.6). Agent 2's circularity argument is sound: (R) ⇔ (C3.6) modulo the bounded weights in [ρ_*^{n−1}, (2ρ)^{n−1}].

**Look-up of remediations:**

**(a) Cicalese–Leonardi 2012 ARMA "Lipschitz parametrization":** This paper (M. Cicalese & G. P. Leonardi, *A selection principle for the sharp quantitative isoperimetric inequality*, ARMA 2012) supplies a selection principle and the asymmetric Fraenkel centering, with B(z_E, ρ/2) ⊂ E in the smallness regime. But it does **not** by itself give a Lipschitz graph; the regularity comes from elliptic regularity of the selected minimizer (Tamanini), which is what BDV / Plan 1 uses. The "Lipschitz parametrization" claim in remediation (a) is therefore either (i) using Cicalese–Leonardi to *select* and then applying further regularity — which is Plan 1 in disguise — or (ii) referring to Fusco–Julin 2014, which gives C^{1,α} but only after a selection-type step that constructs an "almost-minimizer" of a penalized functional. **Verdict: remediation (a) is a back-door Plan 1.** Reject.

**(b) Fusco–Julin Hausdorff containment with η = O(√(P − P(B_ρ))):**
- Fusco & Julin, *A strong form of the quantitative isoperimetric inequality*, Calc. Var. PDE 50 (2014), 925–937, proves
  $$ \inf_z \frac{|E \Delta B_\rho(z)|^2}{|B_\rho|^2} + \mathcal{O}(E)^2 \le C(P(E) - P(B_\rho)), $$
  where 𝒪(E) is the Fraenkel oscillation index. This is the "strong form" (B) of Agent 2.
- The **published** Hausdorff containment in the strong form is **not** at the √(P−P(B_ρ)) rate. The classical Fuglede-type containment under nearly-spherical regime gives diameter control via the Lipschitz norm, but this requires C¹ smallness, not just (B). The published "strong quantitative isoperimetric" containment results (Cicalese–Leonardi 2012 Thm 1.1; Acerbi–Fusco–Morini *Comm. Math. Phys.* 2013) give **L^∞ closeness η = O(P(E) − P(B_ρ))^α** with α < 1/2 in general, sharpening to 1/2 only after a selection-and-regularity step.
- **Verdict:** Remediation (b), as stated, **misquotes the literature**. The actual published rate is worse than √(P−P(B_ρ)); the sharp rate comes only via a selection-and-Schauder argument, which is back to Plan 1.

**(c) L² form ∫||x−z_E|/ρ − 1|² ≤ C(P(E)−P(B_ρ)):** This is actually the natural Fuglede-type quadratic estimate. It is known **in the nearly-spherical class** where ∂E is a C^{1,α} graph over ∂B_ρ with small norm — see Fuglede 1989, Fusco *Bull. Math. Sci.* 2015 §3. But in that regime the boundary IS a graph, so we're back to Plan 1 territory. **Without** the graph assumption, (c) is open. **Verdict:** Remediation (c) is the cleanest no-graph path but is itself a substantive open theorem; it is **not** in the cited FMP/Fusco–Julin package.

**Net verdict on Q3:** Agent 2's diagnosis (Conjecture 3.6 is the bottleneck) is correct. All three proposed remediations have issues; only (c) is genuinely no-graph, and it remains open. Plan 2's closure **does** require a new theorem of the form "L²-radial-trace on ∂*E for finite-perimeter near-balls", and that theorem is not in the literature in the strength Plan 2 needs.

### Q4. Metric trace with only interval lower bounds.

Agent 4's diagnosis is correct. (H1)+(H2) alone give only δ^{1/2}, because the bad-set lemma (Lemma 3.1) controls |B_*| only to O((M−c)L^* + δ), and the kinetic-transport step (Step 2) costs O(|B_*|‖γ̇‖_∞²), which is O(δ^{1/2}) when M − c = O(δ^{1/2}).

**Adversarial check:** Could one avoid (5.14) some other way?

1. Pointwise lower bound on dμ/dρ: ruled out by the deployment brief.
2. Doubling on μ: the interval bound (H2) gives μ([ρ_δ − c√δ, ρ_δ]) ≥ c·√δ − Cδ, which is not doubling.
3. A weighted Markov argument: would yield d_𝒳(γ(ρ̂), B_1)² ≤ Cδ/μ(I_δ) on some I_δ ⊂ [ρ_δ − c√δ, ρ_δ]; with μ(I_δ) = O(√δ) this gives d² ≤ C√δ, not Cδ. So **Markov-in-μ alone gives only δ^{1/2}**. Confirms Agent 4.
4. Poincaré / Hardy on the metric curve: would need (H1) to control ∫ d_𝒳² dρ (not dμ), which is (5.14) again.

**Verdict on Q4:** Agent 4 is **correct that (H1)+(H2) are insufficient** at the δ-rate. The auxiliary kinetic bound (5.14) is needed. Whether (5.14) holds is the second open point (I4, I11). Agent 4 asserts it follows from the Cauchy–deficit identity via the bookkeeping in `outer-foliation-entry-proof-attempt.md` §4, but **that section is in the smooth coherent regime only**. The finite-perimeter version of (5.14) is not proved anywhere in the repo. This is a real gap.

### Q5. Boundary-layer transfer preserves exponent 2.

Reading `metric-finite-perimeter-closure.md` §6 and `level-set-deficit-identity.md` Lemma 8.3:

- |Ω \ E_{ρ̂}| = ω_n(1 − ρ̂^n) ≤ C_n √δ. ✓
- A(Ω) ≤ A(E_{ρ̂}) + C_n √δ by Lemma 8.3. ✓ (with 2η/L = 2·C√δ/ω_n ≤ C√δ.)
- Squaring: A(Ω)² ≤ 2 A(E_{ρ̂})² + 2C²·δ ≤ 2Cδ + 2C²δ = O(δ). ✓
- **The constant is doubled** by the (a+b)² ≤ 2a²+2b² step, but the **exponent 2 is preserved**. ✓

There is one bookkeeping subtlety: A(E_{ρ̂}) is normalized against |B_{ρ̂}|, not |B_1|. Lemma 8.3 correctly accounts for this via the additive 2η/L correction. ✓

**Verdict on Q5:** The boundary-layer transfer is clean; the constant chain in §6 gives the sharp exponent 2 with explicit constants. No hidden δ^{1/2} loss.

### Q6 (own). Is D_H ≥ 0 by Cauchy–Schwarz robust under multiple components / topology?

Agent 1 Lemma 1 gives α(t) = ∫_{∂*E_t} |∇u|^{−1} = −m'(t). Lemma 2 gives β(t) = ∫_{∂*E_t} |∇u| = m(t). Cauchy–Schwarz on the measure space (∂*E_t, dℋ^{n−1}) applied to the pair (|∇u|^{1/2}, |∇u|^{−1/2}) gives:
$$P(E_t)^2 = \Bigl(\int_{\partial^* E_t} 1\, d\mathcal H^{n-1}\Bigr)^2 \le \alpha(t)\beta(t),$$
i.e. D_H(t) ≥ 0, regardless of whether ∂*E_t has one or many components, regardless of topology. The reduced boundary need not be connected; Cauchy–Schwarz on L²(∂*E_t) doesn't care.

The only subtle point: Lemma 2 requires that {|∇u| = 0} ∩ ∂*E_t has H^{n−1}-zero, so that the integrand |∇u| is well-defined a.e. This is implicit in Agent 1's "for a.e. t" statement and supported by Sard-for-Sobolev (Figalli–Maggi 2011), though Agent 1 §1 says explicitly this isn't needed because the Lipschitz-truncation proof bypasses the formal trace. Still, the *Cauchy–Schwarz statement* applies on the reduced boundary as a measure-theoretic identity.

**Verdict on Q6:** D_H ≥ 0 is robust under multiple components and arbitrary topology. ✓

### Q7 (own). Does the proof require u ∈ C¹?

V_ρ = −t'(ρ)/|∇u| requires |∇u| > 0 H^{n−1}-a.e. on ∂*E_ρ. For variational torsion u ∈ H^1_0 ∩ W^{2,p}_{loc}, this is provided by **Sard for Sobolev maps** (Figalli–Maggi 2011 Appendix; De Philippis–Marini–Mukoseeva 2021): for a.e. level t, ℋ^{n−1}(∂*E_t ∩ {|∇u| = 0}) = 0. Agent 1 §1 mentions this. Agent 3 §0 implicitly uses it but does not cite a Sard theorem.

**Issue I10:** Agent 3 should cite Figalli–Maggi 2011 Thm A.1 (or equivalent) for the Sobolev Sard. This is a documentation issue, not a substantive gap.

**Other dependence on C¹:** Agent 3 §3 uses smooth flows X(ρ,x), but only as an intermediate step; the BV passage in §4 removes the C¹ requirement. **The final theorem (T) holds for u ∈ H^1_0 ∩ W^{2,p}_{loc}.** ✓

**Verdict on Q7:** No agent's proof requires more than W^{2,p}_{loc} regularity (in fact, Agent 1's proof requires only u ∈ H^1_0 ∩ L^∞). Sard-for-Sobolev gives Agent 3's V_ρ. ✓ (I10 is documentation only.)

### Q8 (own). Plan 1 vs Plan 2: scientific value.

**Plan 1 status:** Route A (single-set selection + graph entry + uniform Schauder + interpolation + BDV nearly-spherical + Kohler–Jobin) is **reported unconditional** in `Plan 1/PLAN1_AGENT_REPORT.md` (5th pass). Route B (Bernoulli spectral) is conditional. So **Plan 1 closes the sharp FK inequality unconditionally** as of the current state of the repo.

**Plan 2's value if closed:**
- **Strictly weaker as a result:** the conclusion (D) is identical to Plan 1's. So as a *theorem*, Plan 2 adds nothing.
- **Strictly stronger / structurally novel as a *proof*:**
  1. No selection principle. Plan 1's Route A constructs a penalized minimizer; Plan 2 stays intrinsic.
  2. No graph entry. Plan 1 uses graph parametrization of the selected minimizer; Plan 2 uses reduced-boundary GMT throughout.
  3. No BDV nearly-spherical theorem. Plan 1 ends with BDV Thm 3.3; Plan 2 ends with a metric Sobolev trace.
  4. **Extends to rougher classes.** Plan 1's selection requires Λ-minimizers of a penalized functional, which need at least Tamanini regularity. Plan 2 works for arbitrary finite-perimeter level sets, so it potentially extends to:
     - General quasi-linear PDE with rougher gradient regularity.
     - The Robin / Steklov / fractional torsion contexts.
     - The discrete / nonlocal versions.
- **Strictly stronger in *style*:** Plan 2's intermediate output (A) — bounded sharp Saint–Venant via metric level-set route — is a *new* analytical statement, not equivalent to Plan 1's.

**Net scientific value of closing Plan 2 (Conjecture 3.6 + K5.14):**
1. A new proof technique for sharp quantitative isoperimetric-type inequalities, applicable beyond torsion.
2. Closure of the radial L¹-trace estimate (R), which is a *fundamental* missing input in the FMP/Fusco–Julin package and would be a publishable theorem in its own right.
3. A genuine alternative to BDV's nearly-spherical theorem.

**Is it worth the effort?** Yes — but the main payoff is **not** "a new proof of sharp FK"; it is **the radial L¹-trace theorem** (Conjecture 3.6), which has independent interest in GMT.

---

## 3. Final verdict

**Plan 2 status:** (b) — needs serious surgery, **NOT** "close to closure modulo Conjecture 3.6".

The two genuine open items are:
- **Conjecture 3.6 / (R) (I1):** Agent 2's three remediations are not all viable: (a) violates the brief, (b) misquotes the literature, (c) is open. No remediation in the repo actually closes (R).
- **K5.14 / second-order profile-gap (I4, I11):** Agent 4 says this follows "for free", but the actual derivation is **only in the smooth coherent graph regime** (`outer-foliation-entry-proof-attempt.md` §4). The finite-perimeter version is not in the repo.

**Hidden structural problems Agent 5's assembly missed:**
- **I2** (remediation (a) smuggles a graph): Agent 5 explicitly recommends remediation (b) as "measure-theoretic and respects the brief's 'no graph' constraint", but does not flag that (a) violates the brief.
- **I3** (Fusco–Julin Hausdorff rate misquoted): Agent 5 lists (b) as a remediation without checking the rate.
- **I11** (K5.14 derivation is only in smooth case): Agent 5 lists this as "open / repairable" but does not flag that the supposed `outer-foliation-entry-proof-attempt.md` §4 reference is in the smooth coherent graph regime, **not** the finite-perimeter regime needed.

These are not fatal in the sense that they don't preclude eventual closure, but they mean the gap between "Plan 2 conditional on two items" and "Plan 2 unconditional" is larger than Agent 5's assembly suggests.

---

## 4. Wave 2 priorities (ordered)

1. **(Highest)** Prove an L²-radial-trace inequality
$$\int_{\partial^* E} \Bigl|\frac{|x-z_E|}{\rho}-1\Bigr|^2 d\mathcal H^{n-1} \le C(P(E) - P(B_\rho))$$
for finite-perimeter E ⊂ B_R near a ball, with no graph parametrization. This is **Agent 2 remediation (c)**, restated, and is the only no-graph path. The Cauchy–Schwarz step then upgrades it to the L¹ form (R). **De-risks I1, I2, I3 simultaneously.** Likely route: spherical-coordinate disintegration of perimeter (Maggi Ch. 18) + Hardy inequality on rays + the strong oscillation index (B). Best target paper: extend Fusco *Bull. Math. Sci.* 2015 Section 3 Fuglede-Lemma to the no-graph setting.

2. **(Second)** Make the K5.14 hand-off rigorous in the finite-perimeter regime. Concretely: prove that the integrated Cauchy–deficit identity
$$\int_{\rho_*}^{\rho_\delta} \int_{\partial^* E_\rho} \frac{(V_\rho - \bar V_\rho)^2}{V_\rho} \, d\mathcal H^{n-1} \, d\rho \le C\delta$$
together with (5.14) follow from Agent 1's exact identity, without assuming the smooth graph regime. **De-risks I4, I11.** Likely route: combine Agent 1's Lemma 2 with the Reshetnyak-LSC passage of Agent 3 §4.

3. **(Third)** Tighten Agent 2's center-identification: state explicitly that on each overlap block, the FvHT block-center z_j and the Fraenkel asymmetry center of E_ρ for ρ ∈ I_j ∩ I_{j+1} differ by O(√δ_T), and the deviation is absorbed into the constants. **De-risks I5.**

4. **(Fourth, documentation only)** Cite Figalli–Maggi 2011 Appendix or De Philippis–Marini–Mukoseeva 2021 in Agent 3 §0 for the Sobolev Sard providing |∇u| > 0 H^{n−1}-a.e. on ∂*E_ρ. **Closes I10.**

5. **(Lowest)** Re-audit `gmt-inputs-for-metric-closure.md` (1.2) — rewrite the half-line "proof" as an explicit reference to whichever theorem (R) is eventually proved from. **Closes I12.**

Closing 1 and 2 makes Plan 2 unconditional. Closing 3–5 are cleanup. The remaining items in the original Agent 5 open-issues table (FvHT center gluing, bounded reduction, KJ transfer, boundary-layer transfer) are clean and do not need attention.
