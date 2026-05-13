# Wave 2 Agent E: Bypass routes for (B²) — codebase search

## ~250-word summary and ranking

Plan 2's last open theorem is (B²): a quadratic L² Fusco–Julin oscillation bound ∫_{∂*E}|ν_E−e_r|² dH^{n−1} ≤ C(P(E)−P(B_ρ)) for finite-perimeter near-balls, with no graph parametrization and no selection. After Wave 2 Agents A and B, *all* other inputs (the integrated kinetic bound (K), the weighted metric trace, the boundary-layer transfer, the FvHT center gluing, the level-set deficit identity, the elliptic regularity feeding Agent 3) are settled unconditionally. Wave 2 Agent A's central identity ∫|ν−e_r|² = 2(P−P_ρ) + 2Π reduces (B²) to controlling the radial volume moment Π = (n−1)∫_E |x−z_E|^{−1}dx − P(B_ρ), which equals O(δ) **iff** the volume L¹-radial moment M₁ is O(δ), and this is not in FMP.

I have read the eleven listed files and assessed routes α–ζ. **Ranking by viability**:

1. **(δ) Integrated/good-set (B²)** — *the only route I judge tractable in a Wave 3 timeframe*. Already half-proven by Agent A §4 (bad-ray quadratic absorption) and Agent B (bad-set has Lebesgue measure ≤ Cδ). Recommended.
2. **(γ) Weighted (B²) via |∇u|** — only partially aligned with what Plan 2 actually needs; promising but loses sharp rate at one step.
3. **(α) Torsion-level local C^{1,α}** — *interpretation-dependent*; if "no graph" is read strictly, this violates it; if read as "no global graph", it is the same gambit as Agent 2 remediation (a) up to relabeling.
4. **(β), (ε), (ζ)** — not viable from the codebase.

**Honest verdict**: route (δ) plausibly closes Plan 2 at the sharp rate without proving (B²) pointwise. If (δ) also fails on closer inspection, Plan 2 is **genuinely stuck** at the FMP rate δ^{1/2}, and the scientific case for finishing it (rather than declaring Plan 1 the canonical proof) weakens substantially.

---

## 1. Status restatement of (B²) and why it's the remaining gap

After Wave 2 Agents A (`wave2-A-radial-l2-trace.md`) and B (`wave2-B-kinetic-bound.md`), Plan 2 has the following structure.

**(K)** The integrated kinetic bound ∫_{ρ_*}^{ρ_δ}|γ̇|²dρ ≤ Cδ is settled unconditionally (Agent B Theorem 5.1) by combining Agent 1's exact deficit identity, Agent 3 (T), an elementary L¹-Lipschitz bound (A0), and a bad-set/good-set decomposition. The bad set {−t′(ρ) < ρ_*/(2n)} has Lebesgue measure ≤ K₂δ.

**(R²)** The L²-radial trace T₂(E) ≤ C(P−P_ρ) feeds Conjecture 3.6 → homothetic velocity defect (*) → (3.4) of `metric-finite-perimeter-closure.md`. Agent A reduced (R²) to its slicing-weighted part (R2-rad, settled at rate δ) plus the residual Π = O(δ) piece. By the divergence-theorem identity (Agent A §5.3'),
$$\int_{\partial^*E}|\nu_E-e_r|^2\,d\mathcal H^{n-1} = 2(P(E)-P(B_\rho)) + 2\Pi(E,z_E),$$
where Π(E,z_E) := (n−1)∫_{B_ρ(z_E)\E}|x−z_E|^{−1}dx − (n−1)∫_{E\B_ρ(z_E)}|x−z_E|^{−1}dx ≥ 0. So **(B²) ⇔ Π = O(δ) ⇔ M₁ = O(δ)** (volume L¹-radial moment).

FMP gives only M₁ = O(√δ). The L¹ Fusco–Julin oscillation (B) squared gives ∫|ν−e_r|² ≤ C·∫|ν−e_r| ≤ C√δ, *not* Cδ. The sharp form (B²) is the missing theorem.

(B²) is known in the **nearly-spherical (graph) class** (Fuglede 1989) and via **selection** (Cicalese–Leonardi 2012 + Schauder), but in the no-graph no-selection setting it is open.

## 2. Codebase digest

- **`wave2-A-radial-l2-trace.md`** — establishes the exact decomposition (R²) = (R²-rad) + (P−P_ρ) + Π, proves (R²-rad) at rate δ via bad-ray quadratic absorption (good ingredient for route δ), and identifies (B²) ⇔ Π=O(δ) ⇔ M₁=O(δ) as the genuine gap. The §9 sketches three escape routes (α Hausdorff, β Hardy/Wirtinger, γ H^{1/2} via graph) and **rejects all three**.

- **`wave2-B-kinetic-bound.md`** — proves (K) by a *bad-set* decomposition: the bad set {−t′<τ₀} has Lebesgue measure ≤ K₂δ, exploited via the **trivial uniform L¹-Lipschitz bound (A0)** of γ. This is **the architectural template** for route (δ): "what fails pointwise can succeed in integrated form via a bad-set Lebesgue-measure bound."

- **`agent6-adversarial-audit.md`** §3, §4 — confirms (B²)/(R) is the only open item and rejects all three Agent 2 remediations: (a) is back-door selection, (b) misquotes FJ Hausdorff rate, (c) is open.

- **`agent2-homothetic-velocity-defect.md`** §5 — three rejected remediations; the slicing reduction to (C3.6) is **circular** in the L¹ form (this is *the* reason Agent A introduced the L² form).

- **`analytic-native-route.md`** — proposes h = u + |x|²/(2N) (harmonic) and 2D holomorphic F_Ω = ∂_z u + z̄/4. *Entire computation in §§7–10 assumes "after BDV selection" / "nearly spherical graph regime"*. The H^{1/2} weights come from k|φ_k|² on a graph perturbation. **This route is graph-entry-conditional**; it computes the second variation only in the smooth coherent regime, identical in scope to BDV/Fuglede.

- **`nicola-tilli-stability-import.md`** §6, §9, §10 — the GGRT/STFT transfer-back step requires *regular superlevel geometry*, which Nicola–Tilli get from Fock analyticity. The "torsion replacement" §5 states explicitly: "for arbitrary domains, no comparable regularity is available" — hybrid via Plan 1 only. **No no-graph (B²) is in Nicola–Tilli.**

- **`concrete-next-steps.md`** §0 — explicit hybrid via BDV selection. The Lemma 3.1 boundary-trace expansion assumes C^{1,γ} free boundary, density estimates, nondegeneracy: this is **exactly Plan 1**.

- **`selected-boundary-layer-theorem.md`** — §3 ("Selected-minimizer boundary trace") *requires* "U is a Plan 1 selected minimizer in the graph regime". The proof of Lemma 3.1 uses Bernoulli boundary regularity q = |∇u| ∈ C^γ on ∂U, which is post-selection regularity. **Cannot be re-used in pure Plan 2.**

- **`global-foliation-trace.md`** — §1's "coherent foliation gauge" §1 explicitly assumes ∂E_ρ can be written as z(ρ) + (ρ+h(ρ,θ))θ. The proof of (F)/(T) is **inside that gauge**. §6 "What must replace the selection principle" identifies the **outer foliation entry lemma** as the genuinely missing input — this is again (B²)-equivalent at the integrated level. §7 reduces to the velocity-to-metric-derivative lemma (7.3), which Agent A and Wave 2 Agent B together have *almost* closed except for (B²).

- **`level-set-deficit-identity.md`** §6–§8 — the good-level lemma 8.2 only gives D_H + D_I ≤ Cδ/η on a slab. The 1/η loss is what the slab-averaging route was *introduced to* circumvent; Agent 4 and the foliation route replace 1/η by an integrated bound. Slab averaging by itself **does not** give a quadratic (B²) at any single level.

- **`outer-foliation-entry-proof-attempt.md`** §4 — derives D_H + D_I ≥ c(ρ^{n−1}‖∂_ρ h_{≥2}‖² + ρ^{2n−4}Q(h)) **only inside the smooth coherent graph regime with ‖h‖_{C¹} small**. Agent 6 (I11) and Agent A confirm this: cannot be transplanted to finite-perimeter without graph entry.

- **`Plan 1/quantitative-selection-principle.md`** + **`Plan 1/graph-entry-closure.md`** — by design, supply the regularity that Plan 2 forbids. Their partial results (density, nondegeneracy, Hausdorff containment via BDV Lemma 4.2) all *require selection*. Not usable in pure Plan 2.

- **`fvht-center-gluing-import.md`** §3–4 — FvHT's quadratic mechanism is for PL/BBL, with a **convex** core. For torsion levels there is no convex core; the FvHT *gluing* idea has been imported (FvHT block centers) but its **quadratic stability** depends on convexity and does *not* transfer.

## 3. Route-by-route analysis

### Route α (torsion-level elliptic regularity / local C^{1,α})

**Idea.** −Δu=1 ⇒ u ∈ W^{2,p}_{loc} for all p. By Sobolev Sard (Figalli–Maggi 2011 App. A; cited in `agent6-adversarial-audit.md` I10 and `agent1-finite-perimeter-identity.md` line 84), {|∇u|=0} ∩ ∂*E_t has H^{n−1}-measure zero for a.e. t. **Wherever |∇u|>0**, the implicit function theorem makes {u=t} a *local* C^{1,α} graph.

**Supporting fragment.** `agent1-finite-perimeter-identity.md` lines 84–87 cites Sard for Sobolev. `agent6-adversarial-audit.md` §I10 confirms it. `agent3-metric-first-variation.md` §0 uses |∇u|>0 a.e.

**Additional input.** A *local* (B²) statement: on every connected piece of ∂*E_t where |∇u| ≥ ε, the part of ∫|ν−e_r|² localized to that piece is ≤ C(P_local − P_ball,local). Then integrate over a partition.

**Open vs tractable.** *Tractable as a local statement* (it's Fuglede-style with C^{1,α} graph control + uniform |∇u| lower bound from elliptic Schauder), *but only after the "selection" step that decides what counts as the "near-spherical" piece*. Concretely: the |∇u|≥ε set may be only a small fraction of ∂*E_t; on its complement (|∇u| small), the level surface degenerates and the local-Fuglede bound has constant blowing up like ε^{−k}.

**The honest issue.** Plan 2's brief says **no graph parametrization**. The strict reading rules α out: a *local* C^{1,α} graph at a point where |∇u|>0 *is* a graph parametrization (in a neighborhood). The Plan 2 vs Plan 1 distinction is precisely this — Plan 1 uses *exactly* this local C^{1,α} graph (via Alt–Caffarelli / Bernoulli regularity on selected minimizers, equivalent to elliptic Schauder on u in a fixed collar). So **route α is essentially Plan 1 in disguise**, and Agent 2 remediation (a) is the same idea.

If the brief is read more leniently — "no a-priori imposed graph; local graphs from elliptic regularity of u are OK" — then route α reduces (B²) to (i) showing |∇u|≥ε on H^{n−1}-most of ∂*E_t, which is the **gradient nondegeneracy** that Plan 1 needs the BDV selection for, and (ii) a Fuglede-type bound on the C^{1,α} piece with explicit ε-dependent constants. **Step (i) is the entire content of selection.** So α succeeds only at the cost of importing selection, contrary to the brief.

**Verdict.** Not a genuine bypass. Either equivalent to Plan 1 (strict reading) or requires a no-selection gradient-nondegeneracy theorem that is itself open.

### Route β (Cauchy-deficit D_H controls L² normal oscillation directly)

**Idea.** D_H(t(ρ)) = (∫|∇u|^{−1})(∫|∇u|) − P(E_ρ)² is the L² variance of |∇u| around its mean on ∂*E_ρ. Since |∇u| = −t′(ρ)/V (Agent B Lemma 3.1), and in the near-spherical regime V≈1 + radial graph derivative + tangential O(|ν − e_r|), perhaps ∫|ν−e_r|² · w dH^{n−1} ≤ C·D_H/(something) for some weight w.

**Supporting fragment.** `gmt-inputs-for-metric-closure.md` (2.4)+(3.2) gives ∫|H_{z,ρ}−V̄|² ≤ CD_I and ∫(V−V̄)²/V = (A_ρ/P²)D_H. Combining: ∫|V−H_{z,ρ}|² ≤ C(D_H+D_I).

**Additional input.** This *would* give (B²) only if |H_{z,ρ} − e_r·ν_E| controls |ν_E − e_r|. But H_{z,ρ}(x) = ((x−z)/ρ)·ν_E = (|x−z|/ρ)(e_r·ν_E), and as Agent 2 §3.1 shows, |H_{z,ρ}−1| ≤ ||x−z|/ρ − 1| + |e_r·ν_E − 1|, *not the other direction*. The kinetic bound controls (V−V̄), which is the **scalar** velocity variance, not the **vector** ν−e_r. The tangential part of ν−e_r is **invisible** to V_ρ (a scalar field).

**Open vs tractable.** Not viable: D_H is a Cauchy–Schwarz gap of a *scalar* function (|∇u|) on a hypersurface, while (B²) measures the *vector* angle between ν_E and e_r. There is no extraction direction; D_H gives only the radial component of the normal-velocity mismatch.

**Verdict.** Not viable.

### Route γ (weighted (B²) via |∇u| or u)

**Idea.** Replace ∫|ν−e_r|² by ∫|ν−e_r|²·w dH^{n−1} with a natural PDE weight. The divergence-theorem identity uses div(e_r) = (n−1)/|x−z_E|, giving exact identities for **(1−e_r·ν_E)** integrated against radial weights.

**Supporting fragment.** Agent A §5.3 gives exactly such an identity for the constant weight: ∫(1−e_r·ν_E) = (P−P_ρ) + Π. With the natural torsion weight |∇u|: by the test field Φ = (1−e_r·ν_E)|∇u|^?, and using Δu = −1 inside E, one *can* derive an exact identity. Specifically: applying the divergence theorem to F(x) = u(x)·e_r,
$$\int_{\partial^*E} u\,(e_r\cdot\nu_E)\,d\mathcal H^{n-1} = \int_E \nabla u\cdot e_r\,dx + (n-1)\int_E \frac{u}{|x-z_E|}\,dx,$$
since u = 0 on ∂Ω = ∂*E if E = Ω. But for **level sets** E_t = {u>t}, u ≡ t on ∂*E_t, giving
$$t\int_{\partial^*E_t} e_r\cdot\nu_E\,d\mathcal H^{n-1} = \int_{E_t} (\nabla u\cdot e_r + (n-1)u/|x-z_E|)\,dx.$$
This is an **exact identity**, but it has the radial weight 1 (constant), so it gives back Agent A §5.3 modulo a factor t.

**A more substantive weighted form.** Use F(x) = |x−z_E|·e_r = x−z_E. Then div F = n, so
$$\int_{\partial^*E} (x-z_E)\cdot\nu_E\,d\mathcal H^{n-1} = n|E| = n\omega_n\rho^n.$$
This is just the volume identity (used everywhere); not (B²) information.

**Use F(x) = |x−z_E|^{1−n}·e_r (the harmonic radial field outside z_E).** Then div F = 0 on ℝⁿ\{z_E}, so for E ⊃ B(z_E, ε),
$$\int_{\partial^*E} \frac{e_r\cdot\nu_E}{|x-z_E|^{n-1}}\,d\mathcal H^{n-1} = \int_{\partial B(z_E,\varepsilon)} \frac{1}{\varepsilon^{n-1}}\,d\mathcal H^{n-1} = n\omega_n.$$
This is the slicing identity (S₀ in Agent A §3), which integrates to P(E) − ∫(1−|e_r·ν_E|)·|x−z_E|^{−(n−1)} = n·ω_n + (multiplicity terms). This is exactly Agent 2's circular (C3.6).

**Additional input.** None of these weighted identities introduces new information beyond what Agent A already isolated: (1−e_r·ν_E) integrated against natural weights either gives the constant-weight version (modulo factors) or the circular slicing identity.

**Open vs tractable.** Weighted (B²) with w = |∇u|: I do not see a divergence-form identity giving ∫|ν−e_r|²·|∇u| ≤ C·(P−P_ρ) directly. One could try a Pohozaev-style multiplier (x−z_E)·∇u against −Δu=1, giving
$$\int_E \nabla u\cdot e_r |x-z_E|\,dx + \int_E |x-z_E|\,dx = \int_{\partial^*E_t} ((x-z_E)\cdot\nu_E)|\nabla u|^2/2\cdot\,d\mathcal H^{n-1}/(...) - \text{boundary terms},$$
but the resulting identity controls the integral of |∇u|²·(e_r·ν_E)·|x−z_E|, which is not (B²).

**Verdict.** Partially promising as a research direction but **no fragment in the codebase actually produces a weighted (B²) at sharp rate δ**. Open. Plausibly easier than (B²) itself, but not yet a Wave-3-ready problem.

### Route δ (integrated (B²), not pointwise) — **RECOMMENDED**

**Idea.** Plan 2 ultimately uses (B²) **inside an integral against (−t′)dρ** to derive (3.4) of `metric-finite-perimeter-closure.md`. So instead of proving (B²) at each ρ ∈ [ρ_*, ρ_δ], prove only:
$$\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu_{E_\rho}-e_r|^2\,d\mathcal H^{n-1}\,(-t'(\rho))\,d\rho \le C\delta_T(\Omega). \tag{B²-int}$$

**Supporting fragment.** Three pieces:

(i) **Agent A §5.3'**: ∫_{∂*E_ρ}|ν−e_r|² = 2(P(E_ρ) − P(B_ρ)) + 2Π(E_ρ, z_{E_ρ}). Integrating against (−t′)dρ on [ρ_*, ρ_δ] and using `wave2-B-kinetic-bound.md` Corollary 3.2 = (3.2),
$$\int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))\,(-t'(\rho))\,d\rho \le 2\delta_T \cdot \tfrac{1}{2}\cdot(\text{absorbable const}),$$
because P(E_ρ)−P(B_ρ) is exactly (P/P_ρ−1)·P_ρ and the full integrated identity for D_I gives ∫D_I·(−t′)dρ ≤ Cδ. **The "2(P−P_ρ)" piece integrates to O(δ) for free.**

(ii) The remaining task is ∫_{ρ_*}^{ρ_δ} Π(E_ρ, z_{E_ρ})·(−t′)dρ ≤ Cδ. This is the **integrated radial volume moment**:
$$\Pi(E_\rho, z_\rho) \asymp \rho^{-2}\cdot M_1(E_\rho,z_\rho) = \rho^{-2}\int_{E_\rho\Delta B_\rho(z_\rho)}||x-z_\rho|-\rho|\,dx.$$
(Agent A §5 Taylor analysis.) Integrating in ρ against (−t′)dρ ≤ M dρ (Talenti, Agent B (H3)),
$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\rho \le \tfrac{1}{\rho_*^2}\int_{\rho_*}^{\rho_\delta}\int_{E_\rho\Delta B_\rho(z_\rho)}||x-z_\rho|-\rho|\,dx\,d\rho.$$

(iii) **Agent B-style good-set / bad-set decomposition for Π itself.** This is the crucial new mechanism that the codebase suggests but has not yet executed for Π.

**Good set G:** ρ where Π(E_ρ, z_ρ) ≤ τ·(P(E_ρ)−P(B_ρ))/(weight) for some threshold τ. On G, integration against (−t′)dρ gives O(δ).

**Bad set B':** ρ where Π is large. By Cicalese–Leonardi containment (CL): E_ρ ⊂ B(z_ρ, 2ρ) \ B(z_ρ, ρ/2), so Π ≤ C·|E_ρ Δ B_ρ(z_ρ)|/ρ_*. Hence |B'| · τ · (typical δ-scale) ≤ ∫_{B'}Π·(−t′)dρ ≤ ∫_{B'}(P−P_ρ)dρ + ∫_{B'}|EΔB_ρ|/ρ_* dρ.

The second term involves the volume Fraenkel integrated in ρ. By FMP applied levelwise, |E_ρ Δ B_ρ|² ≤ c₁ω_n²(P(E_ρ)−P(B_ρ)), so |E_ρ Δ B_ρ| ≤ C√(δ_ρ) where δ_ρ := P(E_ρ)−P(B_ρ). Integrating
$$\int_{\rho_*}^{\rho_\delta}|E_\rho\Delta B_\rho(z_\rho)|\,d\rho \le C\int_{\rho_*}^{\rho_\delta}\sqrt{\delta_\rho}\,d\rho \le C\sqrt{\rho_\delta-\rho_*}\cdot\sqrt{\int_{\rho_*}^{\rho_\delta}\delta_\rho\,d\rho} \le C\sqrt\delta.$$
This is the **square-root loss** of Agent A §4.11.

**Where Agent B's mechanism saves us:** On the bad set B' for Π, we use the *trivial uniform bound* Π ≤ C·|E_ρ Δ B_ρ|/ρ_*. By Agent B (3.3), the integrated Talenti |ψ| bound, **and** by Agent A (4.9) the integrated multiplicity excess ∫k(θ)dθ ≤ C(P−P_ρ) pointwise, perhaps the bad set for Π has small Lebesgue measure **at the integrated level**. Specifically: the bad set for Π is contained in {ρ : |E_ρ Δ B_ρ(z_ρ)| > τ·δ}. By FMP, |E_ρΔB_ρ|² ≤ Cδ_ρ, so on the bad set δ_ρ ≥ τ²δ²/C. But ∫δ_ρ(−t′)dρ ≤ Cδ; therefore |bad set| · τ²δ² ≤ Cδ, i.e. |bad set| ≤ C/(τ²δ). This is **growing** as δ→0, not shrinking. So this naïve bad-set argument **fails**.

**The right mechanism for (δ) is more subtle.** What Agent B exploits is that the bad set for −t′ has measure ≤ Cδ because |ψ| ≥ τ₀ there and ∫|ψ|dρ ≤ Cδ. For Π, the analog would be: prove an **integrated** identity ∫Π·(−t′)dρ ≤ Cδ directly, not via pointwise FMP.

**The candidate integrated identity:** apply the divergence theorem in the *space-time* domain ⋃_{ρ}(∂*E_ρ × {ρ}) ⊂ Ω × [ρ_*, ρ_δ], using as test field F(x, ρ) = (x − z_ρ)·|x−z_ρ|^{−(n−1)} (a radial harmonic field with moving center). This is the **co-area-in-ρ** version of the Pohozaev/Schiffer multiplier. The result is, schematically,
$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\rho = \int_{\rho_*}^{\rho_\delta}\int_{E_\rho\setminus B_\rho(z_\rho)\cup B_\rho(z_\rho)\setminus E_\rho}\frac{1}{|x-z_\rho|}\,dx\,d\rho,$$
and the inner double integral has a 2-form structure on Ω × ℝ. By Fubini / co-area, this becomes
$$\int_\Omega\int_{\{ρ : u_\Omega(x) > t(\rho)\}\Delta\{ρ : x \in B_\rho(z_\rho)\}}\frac{1}{|x-z_\rho|}\,d\rho\,dx.$$
For each fixed x, the symmetric difference in ρ has length |ρ(x) − ρ_ball(x)| where ρ(x) is the level radius assigned to x (i.e., u_Ω^*−¹(u(x))) and ρ_ball(x) is the corresponding radius for the comparison ball. The difference (ρ(x)−ρ_ball(x)) is exactly the **horizontal profile gap** in the Nicola–Tilli dictionary, and by the profile-gap estimate `level-set-deficit-identity.md` §4 (Lemma 8.1),
$$|t(\rho) - t_B(\rho)| \le C\delta \quad\text{on}\quad [\rho_*, 1].$$
Translating via −t_B′ ≃ ρ/n: |ρ(x) − ρ_ball(x)| ≤ C·δ. Hence
$$\int_{\rho_*}^{\rho_\delta}\Pi\,d\rho \le \int_\Omega \frac{C\delta}{|x-z(x)|}\,dx \le \frac{C\delta}{\rho_*}\cdot|\Omega| = C\delta.$$

**This is exactly the integrated (B²-int) at rate δ.** It does not give pointwise (B²) but it gives the integrated version, which is all Plan 2's downstream chain needs.

**Additional input required.** Three things to verify carefully:

1. The space-time divergence identity for Π integrated against dρ, including handling the moving center z_ρ (FvHT block-center field of `fvht-center-gluing-import.md`, with the Agent 6/C1 reconciliation to the Fraenkel center).
2. The horizontal profile-gap interpretation (Nicola–Tilli b(s) − v(s) ≤ 2δ/s, `nicola-tilli-stability-import.md` §2) into the ρ-coordinate, giving |ρ(x) − ρ_ball(x)| ≤ Cδ pointwise in x for x in the slab where ρ ∈ [ρ_*, ρ_δ].
3. **Verification that Plan 2's downstream chain actually uses only (B²-int), not pointwise (B²).** Inspection of `gmt-inputs-for-metric-closure.md` §3 and `metric-finite-perimeter-closure.md` §3 shows: yes, the application is integrated. The pointwise (R²) is needed only at the metric-trace endpoint, where Wave 2 Agent B already replaces pointwise control by the bad-set mechanism plus integrated action.

**Open vs tractable.** **Tractable.** All three ingredients exist (one in Agent A, one in `level-set-deficit-identity.md`, one already in Agent B's bad-set mechanism). The remaining work is technical: writing the space-time divergence identity rigorously for finite-perimeter levels and reconciling the centers.

**Verdict. Recommended.** This is the only route I judge realistic for Wave 3.

### Route ε (Brasco–De Philippis 2017 spectral inequalities)

**Idea.** The cited survey `BraDeP2017` (in `Final/master.tex` line 718–721) is L. Brasco & G. De Philippis, *Spectral inequalities in quantitative form*, in *Shape Optimization and Spectral Theory*, De Gruyter 2017. From its scope (a survey) it consolidates **existing** quantitative spectral results — i.e., the FMP, FJ, BDV, CL machinery. The codebase does not cite a *new* (B²) theorem from Brasco–De Philippis; the BDV reference is for the **selection-principle proof** of sharp Saint–Venant, not for (B²).

**Supporting fragment.** None: the only Plan-2-relevant Brasco/De Philippis references in the codebase point to the selection-principle path.

**Verdict.** Not a bypass. The survey may contain a useful exposition of (B²) in the graph regime (which everyone has) but there is no evidence in the codebase of a no-graph (B²) due to Brasco–De Philippis.

### Route ζ (Allen–Kriventsov–Neumayer 2023+)

**Idea.** AKN's *Sharp quantitative Faber–Krahn inequalities via the Alt–Caffarelli–Friedman monotonicity formula* (cited in `Final/master.tex` line 763 as preprint). The ACF monotonicity formula gives a sharp comparison between the harmonic measure / first eigenfunction on two complementary regions and the corresponding Bessel functions; it is the central tool for two-phase free boundary problems (Alt–Caffarelli–Friedman 1984).

**Supporting fragment.** The codebase cites AKN only in `Final/master.tex` as a parallel approach. **There is no Plan-2-side import** of AKN. AKN's mechanism uses a **selection step** (constructing extremals where the ACF monotonicity is nearly saturated), so it falls under the same "back-door selection" objection as Cicalese–Leonardi.

**Verdict.** Not a bypass. AKN does prove sharp Faber–Krahn but through a (different) selection mechanism, not a no-selection no-graph (B²).

## 4. Recommendation: Wave 3 problem statement

The recommendation is **route δ**: integrated (B²) via space-time divergence identity for Π + Nicola–Tilli profile gap + bad-set bookkeeping à la Agent B.

### Wave 3 Problem (sharp formulation)

**Hypotheses.** Let n ≥ 2, R ≥ 2, ρ_* ∈ (0,1). Let Ω ⊂ B_R with |Ω| = ω_n and δ := δ_T(Ω) ≤ δ_0(n, ρ_*, R) small. Let u be the variational torsion function of Ω, E_ρ := {u > t(ρ)} the volume-radius parametrized level sets, and z_ρ a Fraenkel-asymmetry center for E_ρ (existing modulo H^{n−1}-null sets by Cicalese–Leonardi 2012 in the smallness regime).

**Target (B²-int).** There exists C = C(n, R, ρ_*) such that
$$\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu_{E_\rho}(x)-e_{r,z_\rho}(x)|^2\,d\mathcal H^{n-1}(x)\,(-t'(\rho))\,d\rho \le C\delta_T(\Omega),$$
where ρ_δ := 1 − κ√δ as in Wave 2.

**Equivalent target (Π-int).** Equivalently (by Agent A §5.3'),
$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho, z_\rho)\,(-t'(\rho))\,d\rho \le C\delta_T(\Omega),$$
where Π(E,z) = (n−1)∫_{B_ρ(z)\E}|x−z|^{−1}dx − (n−1)∫_{E\B_ρ(z)}|x−z|^{−1}dx ≥ 0.

**Proof strategy (sketch).**

1. **(Space-time identity.)** Write the inner ρ-integral of Π using the indicator difference 1_{B_ρ(z_ρ)} − 1_{E_ρ}, weighted by (n−1)/|x−z_ρ|. Fubini gives an integral over Ω of a 1D length in ρ.
2. **(Profile-gap conversion.)** For each fixed x ∈ Ω, the ρ-set on which x lies in B_ρ(z_ρ) Δ E_ρ has Lebesgue length ≤ |ρ_{ball}(x) − ρ_E(x)|, where ρ_{ball}(x) is determined by x ∈ ∂B_ρ(z_ρ) (i.e., ρ = |x − z_ρ|, with z_ρ measurable in ρ) and ρ_E(x) is determined by x ∈ ∂*E_{ρ_E(x)} (i.e., ρ_E(x) is the volume radius of the level of u_Ω passing through x).
3. **(Talenti / Nicola–Tilli profile.)** By Nicola–Tilli's profile gap (`nicola-tilli-stability-import.md` §2, `level-set-deficit-identity.md` Lemma 8.1, Agent B Remark 3.3),
$$|t(\rho) - t_B(\rho)| \le \frac{2\delta_T}{|\Omega|\rho_*^n} \le C\delta_T,\qquad \rho\in[\rho_*, 1],$$
giving |ρ_{ball}(x) − ρ_E(x)| ≤ C·δ_T uniformly. **However**, this uses only the Talenti rearrangement and doesn't account for the moving center z_ρ; the proof of step 2 must handle z_ρ ≠ 0 carefully via FvHT center coherence.
4. **(Center coherence.)** By `fvht-center-gluing-import.md` §3–4 and `wave2-C-cleanup.md` §C1, on each block I_j the centers are coherent at rate √δ. Globally over [ρ_*, ρ_δ], the total center drift is ≤ N·√δ ≤ C√δ (finite cover). Inserting into step 2 introduces an additional contribution ≤ C·√δ·∫_Ω|x−z|^{−1}dx ≤ C√δ. **This is a √δ loss, not δ.**
5. **(Square-integrability fix.)** To recover the sharp δ rate, use the Cauchy–Schwarz form on the center drift:
$$\int_{\rho_*}^{\rho_\delta}|z'(\rho)|^2\,d\rho \le \int_{\rho_*}^{\rho_\delta}\inf_z\frac{|E_\rho\Delta(z+B_\rho)|^2}{(\text{gauge})}\,d\rho \le C\int_{\rho_*}^{\rho_\delta}D_I\,d\rho \le C\delta$$
(this is the H¹-in-ρ version of the FvHT block-center bound — *needs verification, possibly the genuinely hard step*). Combining with the profile-gap step 3 in L²(ρ) rather than L^∞(ρ) closes (Π-int) at sharp rate δ.

**Concrete Wave 3 question.** Prove the H¹-in-ρ Fraenkel-center bound:
$$\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2(-t'(\rho))\,d\rho \le C(n,R,\rho_*)\delta_T(\Omega),$$
for some choice of measurable center field ρ ↦ z_ρ ∈ ℝⁿ.

This is the **only** missing input in route (δ). If it holds, (B²-int) and hence Plan 2 close at sharp rate δ.

**Tractability assessment.** The L²-Lipschitz bound (A0) of Agent B Lemma 2.1 is *trivial* (volume monotonicity); the H¹-bound on the center field z_ρ is stronger but morally equivalent to "the optimal ball z_ρ + B_ρ moves slowly in ρ if the level sets E_ρ are integrally close to balls". This is the analog at the **center** level of what FvHT proved at the **set** level for log-concave functions. There is reason to expect this is provable using the same Agent-B bad-set / good-set mechanism: on the good set the center is C^1 (by implicit function theorem on the Fraenkel functional), and on the bad set the trivial L^∞ bound |z_ρ| ≤ R + 2 (from CL containment) combined with the bad-set having Lebesgue measure ≤ Cδ gives integrated H¹ control at rate δ.

## 5. Honest assessment

Route (δ) is the only one I see as tractable. Routes α, β, γ, ε, ζ either reduce to a known open problem, fall back into Plan 1 territory, or are inconsistent with Plan 2's "no graph, no selection" brief.

If route (δ) — specifically the H¹-in-ρ center bound — turns out to be itself a hard open problem, then **Plan 2 is genuinely stuck at the FMP rate δ^{1/2}**. In that case, the scientific case for completing Plan 2 (rather than declaring Plan 1's Route A the canonical proof) is materially weakened: Plan 2's distinctive virtue (no selection, no graph, extensibility to rougher classes) has not produced a new theorem, only a new structure for a known theorem with a worse rate.

There is one final caveat. The brief asks for **no selection / no graph**. Strictly, Cicalese–Leonardi containment (CL) — used pervasively by Agents A, B, and 2 — already imports a *measure-theoretic* selection (the Fraenkel center as a unique ARMA-uniqueness statement). Plan 2 has implicitly accepted CL as "not selection in the relevant sense" (Wave 2 Agent A §2 Lemma 2.1 line 67 explicitly: "we use only the measure-theoretic part of their result … we do *not* use the selection-and-regularity machinery that follows"). Under that interpretation, route δ stays inside the brief, and route α (strict reading) does not. Under a *strictest* reading where any selection is forbidden, both routes fall, and the only remaining technique is **direct PDE multipliers** (route γ), which the codebase has *not* succeeded in pushing to the sharp rate.

**Bottom line.** Recommended action for Wave 3: attack the H¹-in-ρ Fraenkel-center bound, and use it together with the space-time Π identity and the Talenti/Nicola–Tilli profile gap to close (B²-int). Skepticism is warranted but the architecture is more promising than any of α, β, γ, ε, ζ in isolation.
