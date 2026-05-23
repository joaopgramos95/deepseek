# Wave 2 Agent D — Final adversarial audit

## Verdict summary (~200 words)

Wave 2 makes Plan 2 worse than it looked after Wave 1, not better. Agent A's L²‑radial‑trace work is honest and partially substantive: the bad‑ray multiplicity excess is genuinely controlled linearly by δ via the slicing identity (this is real new GMT content), but the **good‑ray** mismatch and the tangential‑defect piece reduce to a quadratic Fusco–Julin oscillation (B²) at rate δ, which is **open in the no‑graph regime**. So Wave 2 Priority 1 is **not** closed; the (R) gap of Agent 2 has been moved, not erased. Agent B's "unconditional" claim for the kinetic bound (K) is **wrong**: Agent B's Step 1 invokes Agent 3 (7.1), which routes through `gmt-inputs-for-metric-closure.md` (2.4), which is the (1.2)/(R) input — the very input Agent A leaves open. The geometric ingredients Agent B adds (Lemma 2.1, Lemma 4.1) are correct and useful, but (K) is **conditional on (R)** exactly as before. Agent C's three patches are sound except that C3 mis‑states Wave 2 A's result as having closed (1.2). Net: Plan 2 closure remains conditional on **a single still‑open quadratic boundary‑normal oscillation theorem (B²)** for finite‑perimeter near‑balls. Plan 2 is not dead, but it is not closer to closure than after Wave 1 — only better diagnosed.

---

## 1. Severity table

| # | Deliverable | Location | Issue | Severity | Repairability |
|---|---|---|---|---|---|
| W2‑1 | A | `wave2-A-radial-l2-trace.md` §4.4, (4.9)+(4.10) | Bad‑ray quadratic absorption is genuinely sound; correctly identifies why Agent 2's L¹ circularity breaks for the multiplicity piece. | **None (positive)** | – |
| W2‑2 | A | `wave2-A-radial-l2-trace.md` §4.4, (4.11) and §5, (5.5) | Good‑ray and Π bounds use FMP volume Fraenkel and yield only √δ, not δ. Agent A flags this honestly. | **Genuine open dependency** | Needs (B²) |
| W2‑3 | A | `wave2-A-radial-l2-trace.md` §5.2, (5.3') | The equivalence (R2) ⇔ Π = O(δ) ⇔ (B²) is correctly derived; algebra and Π ≥ 0 are correct. | **None (correct)** | – |
| W2‑4 | A | `wave2-A-radial-l2-trace.md` §1, p.13 / §11 | Claim "(B²) is not in the literature in the no‑graph setting" — verdict appears **correct** (see Q‑A4 below); none of the candidate papers contain (B²). | **None (literature claim is honest)** | – |
| W2‑5 | B | `wave2-B-kinetic-bound.md` §5 Step 1 (5.1); §7 (H1); Status §11 | "Unconditional" claim is **wrong**. Step 1 routes through Agent 3 (7.1) → gmt‑inputs (2.4) → (1.2) = (R). Therefore (K) is *also* conditional on (R) — exactly the input Agent A says is open. | **Substantive: mis‑labelled conditionality** | Fixable by re‑labelling. The arithmetic of Lemma 2.1, Lemma 4.1, Step 4 is independently correct. |
| W2‑6 | B | `wave2-B-kinetic-bound.md` §2.3 Lemma 2.1 | Uniform Lipschitz bound (A0) via dilation is sound; constants traced correctly. | **None (correct)** | – |
| W2‑7 | B | `wave2-B-kinetic-bound.md` §4 Lemma 4.1 | Bad‑set lemma derivation is sound; algebra of |ψ| ≥ ρ_*/(2n) on B_{τ_0} is clean. | **None (correct)** | – |
| W2‑8 | B | `wave2-B-kinetic-bound.md` §5 Step 4 | (1/τ_0)·∫_G |γ̇|²(-t')dρ argument valid; constant 2nK_3/ρ_* is dimensional and δ‑independent. | **None (correct, modulo W2‑5)** | – |
| W2‑9 | B | `wave2-B-kinetic-bound.md` §7 (H1) bullet | "(H1) by Agent 2 / gmt‑inputs (1.2) integrated against dμ" is the second place (1.2) is used; this is **explicit and honest**, but contradicts the §11 "unconditional" claim of the same note. Internal inconsistency. | **Minor wording — primary inconsistency is W2‑5** | Drop "unconditional" wording. |
| W2‑10 | C | `wave2-C-cleanup.md` §C1, (C1.1) | √δ centre identification rate is correct (FvHT ε_j = O(√δ) + Cicalese–Leonardi uniqueness). | **None (correct)** | – |
| W2‑11 | C | `wave2-C-cleanup.md` §C2 | Figalli–Maggi 2011 App A Thm A.1 is a legitimate primary citation for the Sard‑for‑Sobolev statement needed; back‑ups DPMM 2021 and Brothers–Ziemer 1988 also valid. | **None (correct)** | – |
| W2‑12 | C | `wave2-C-cleanup.md` §C3 | The proposed rewrite of `gmt-inputs-for-metric-closure.md` §1 attributes (1.2) to "(R2) of Agent A". But Agent A's verdict is *negative* — (R2) at rate δ is **open**. The C3 rewrite as written would falsely advertise (1.2) as closed. | **Substantive (mis‑states A's status)** | Rewrite C3 to flag (1.2) as conditional on the open (B²). |

---

## 2. Detailed treatment

### Q‑A1. Bad‑ray quadratic absorption (Agent A §4.2–§4.4)

**Verdict: correct.** The slicing identity (S) of §3 is verbatim Maggi 2012 Thm 18.11. The bound (3.1) ρ/2 ≤ r_{θ,j} ≤ 2ρ uses Cicalese–Leonardi 2012 Thm 1.1 inner/outer containment under smallness, applied slice‑by‑slice. The key inequality (4.3)

p(θ) − ρ^{n−1} ≥ (r_{θ,1}^{n−1} − ρ^{n−1}) + (ρ_*/2)^{n−1}·k(θ)

is correct because every r_{θ,j} for j ≥ 2 contributes at least (ρ_*/2)^{n−1}. Integrating against dθ and combining with (S₀) gives (4.9):

∫ k(θ) dθ ≤ (2/ρ_*)^{n−1}·[(P(E) − P(B_ρ)) − ∫(1 − |e_r·ν_E|) dℋ^{n−1} − ∫(r_{θ,1}^{n−1} − ρ^{n−1}) dθ]

i.e. the multiplicity excess is **linearly** absorbed by δ. This is a real new GMT piece. It does break Agent 2's L¹‑circularity *for the multiplicity term*, exactly as the brief intended.

The Cauchy‑Schwarz / mean‑value step (4.5)–(4.5') is sound on [ρ_*/2, 2R]: r ↦ r^{n−1} has bounded derivative on the interval, so |r − ρ| ≲ |r^{n−1} − ρ^{n−1}|, then the L²‑to‑L¹ trick (q² ≤ q for q ∈ [1/2, 2]) gives (4.5'). Constants (n,R,ρ_*) tracked transparently.

So **(R2‑rad) at rate δ for the multiplicity part is rigorous**, modulo the good‑ray piece which is the bottleneck (Q‑A2).

### Q‑A2. Good‑ray √δ rate via FMP (Agent A §4.4 (4.11), §5 (5.5))

**Verdict: tight, given the cited literature.** The bound (4.11)

∫ |r_{θ,1}^{n−1} − ρ^{n−1}| dθ ≤ C·|E Δ B_ρ(z_E)| ≤ C·√δ

uses (i) the 1D slicewise mismatch inequality (Agent 2 Lemma 3.5) integrated against dθ, giving ∫|r_{θ,1} − ρ|·ρ^{n−2}·c dθ ≤ |E Δ B_ρ|, and (ii) FMP for |E Δ B_ρ| ≤ √(c|B_ρ|²·δ). Both steps are sharp. None of the cited candidate papers gives a better volume‑Fraenkel rate:

- **Brasco–De Philippis 2017** treats spectral inequalities; the spectral version is at the same rate.
- **Allen–Kriventsov–Neumayer 2023** "Sharp quantitative Faber‑Krahn via ACF" gives **|EΔB|² ≤ Cδ_{FK}** for the *eigenvalue* deficit (rate √δ on the volume mismatch — sharp). It does not give a better rate on |EΔB| versus the *perimeter* deficit, which is what (4.11) needs.
- **Esposito–Fusco–Trombetti 2005** Math. Z.: explicit Hausdorff containment at rate δ^{1/(2(n−1))}, worse than √δ for n ≥ 2.
- **De Philippis–Marini–Mukoseeva 2021** isocapacitary inequality: sharp |EΔB|² ≤ Cδ_{cap}; again no improvement on the relationship to perimeter deficit beyond FMP.
- **Acerbi–Fusco–Morini 2013** CMP: nearly‑spherical regime only.

The FMP √δ rate is the best published rate for |EΔB| in terms of P(E) − P(B_ρ) without a graph/selection step. Agent A's good‑ray rate is **tight given the no‑graph constraint**.

### Q‑A3. Equivalence Theorem B and Π's sign (Agent A §5)

**Verdict: algebraically correct.** The divergence‑theorem identity (5.3) with the singular field F(x) = e_r is verified:
- For E = B_ρ(z_E): LHS = P(B_ρ) = nω_nρ^{n−1}. RHS = (n−1)·∫_{B_ρ} r^{−1} dx = (n−1)·nω_n·ρ^{n−1}/(n−1) = nω_nρ^{n−1}. ✓
- The truncation step F_ε(x) = χ_{|x−z_E| > ε}·e_r is standard since |x−z_E|^{−1} ∈ L¹(E) (E bounded, n ≥ 2).
- (5.3') follows from (5.3) and (1 − e_r·ν_E) = ½|ν_E − e_r|², which is correct because |e_r| = |ν_E| = 1.

**Π ≥ 0** is correct: on B_ρ \ E, |x − z_E| ≤ ρ ⇒ |x − z_E|^{−1} ≥ 1/ρ; on E \ B_ρ, |x − z_E| ≥ ρ ⇒ |x − z_E|^{−1} ≤ 1/ρ. With |B_ρ \ E| = |E \ B_ρ| (volume equality), Π ≥ (1/ρ)·|B_ρ\E| − (1/ρ)·|E\B_ρ| = 0.

So the **equivalence (R2) at rate δ ⇔ Π = O(δ) ⇔ (B²)** is tight. There is no slack — the (n−1)/|x−z_E| factor in the divergence is exactly the right weight.

### Q‑A4. Is (B²) in the literature?

**Verdict: appears not.** I checked the five candidate papers:

- **Brasco–De Philippis 2017** (Spectral inequalities, quantitative form). Treats |λ₁(Ω) − λ₁(B)| stability via reduction to perimeter; does not give an L²‑form normal oscillation in the no‑graph regime.
- **Allen–Kriventsov–Neumayer 2023** (Sharp quant. FK via ACF). Closes |EΔB|² ≤ Cδ_{FK}, i.e. an L²-style bound, but only at the level of the *volume Fraenkel* (which is the wrong quantity for (B²)). The proof goes through a free‑boundary monotonicity formula; the boundary‑normal control they establish is in an integrated‑in‑level form, not the pointwise quadratic (B²).
- **Brasco–Pratelli 2012** (Sharp stab. of spectral inequalities). Gives sharp quantitative isoperimetric and λ₁ stability via Fuglede + reduction; the L² form lives in the C^{1,α}‑graph regime (nearly spherical).
- **De Philippis–Marini–Mukoseeva 2021** (Sharp isocapacitary). The dual‑energy step gives (B²) **after a selection‑and‑regularity step à la Cicalese–Leonardi**; their Prop. 4.2 quotes Fusco *Bull. Math. Sci.* 2015 §3 (Fuglede nearly‑spherical), so the (B²) form is conditional on graph entry of the selected minimizer.
- **Acerbi–Fusco–Morini 2013** (CMP). Uses a second variation argument on the *penalised functional* of a selected almost‑minimizer — same selection trick.

In each case, (B²) sits behind a graph or selection step; in the no‑graph no‑selection regime relevant to Plan 2, (B²) is **open**. Agent A's verdict is **correct**.

### Q‑B1. Lemma 2.1 (uniform Lipschitz bound (A0))

**Verdict: correct, with one small caveat.** The split

|F_ρ Δ F_{ρ'}| ≤ |F_ρ Δ (ρ')^{−1} E_ρ| + (ρ')^{−n}|E_ρ Δ E_{ρ'}|

is valid because F_ρ = ρ^{−1}E_ρ, F_{ρ'} = (ρ')^{−1}E_{ρ'}, and (ρ')^{−1}E_ρ is the intermediate point obtained by changing scale from ρ to ρ' while keeping the set E_ρ fixed. The second term is then (ρ')^{−n}·|E_ρ Δ E_{ρ'}|, which is correct because Λ_λ(A) Δ Λ_λ(B) = Λ_λ(A Δ B) (translation/dilation symmetry):

(ρ')^{−1} E_{ρ'} Δ (ρ')^{−1} E_ρ = (ρ')^{−1}(E_{ρ'} Δ E_ρ), and |(ρ')^{−1} A| = (ρ')^{−n}|A|. ✓

The dilation estimate

|Λ_λ(A) Δ A| ≤ |A|·(λ^n − 1) (for A bounded, λ ≥ 1)

is **slightly subtle but correct** under the containment hypothesis. For A ⊆ B_S, the dilation A ⊆ B_S ⇒ Λ_λ(A) ⊆ B_{λS}, and |Λ_λ(A) Δ A| ≤ |B_{λS}| − |A| + |A| − |B_{λS} ∩ A| with appropriate bookkeeping gives the constant L_0 of order R/ρ_*^n. The final constant n(R/ρ_*)^n + n/ρ_*^n is correct to leading order.

(A0) is **purely volumetric — does NOT require any (R) or (B²) input**. ✓

### Q‑B2. Lemma 4.1 (bad‑set algebra)

**Verdict: correct.** On B_{τ_0}, −t_B'(ρ) = ρ/n ≥ ρ_*/n; combined with −t'(ρ) < τ_0 = ρ_*/(2n):

|ψ(ρ)| = (-t_B'(ρ)) − (-t'(ρ)) ≥ ρ_*/n − ρ_*/(2n) = ρ_*/(2n).

Then by (3.3) ∫_{ρ_*}^1 |ψ| dρ ≤ K_1 δ:

(ρ_*/(2n))·|B_{τ_0}| ≤ ∫_{B_{τ_0}} |ψ| dρ ≤ K_1 δ ⇒ |B_{τ_0}| ≤ 2nK_1/ρ_* · δ. ✓

The integrated Talenti gap (3.3) (or equivalently Remark 3.3 via t(ρ) − t_B(ρ) ∈ [−2δ/(ω_nρ_*^n), 0]) is unconditional — it follows from Agent 1 (or Talenti pointwise).

### Q‑B3. Step 4 dimensional constant

**Verdict: correct.** On G = [ρ_*, ρ_δ] \ B_{τ_0}, by construction −t'(ρ) ≥ τ_0, so

∫_G |γ̇|² dρ = ∫_G |γ̇|² · (−t')/(−t') dρ ≤ (1/τ_0)·∫_G |γ̇|²(−t')dρ ≤ (1/τ_0)·K_3 δ = (2n K_3/ρ_*)·δ.

τ_0 = ρ_*/(2n) is purely dimensional, and K_3 is δ‑independent. Adding (5.3) ≤ L_0²·K_2·δ gives C′ = 2nK_3/ρ_* + L_0² K_2. **All constants δ‑independent.** ✓

### Q‑B4. Compatibility with Agent 4 (H1, H2, H3, 5.14)

**Three of the four are sound; one is the hidden circularity.**

- **(H1)** action: integrating |γ̇|²·(−t') ≤ K_3 δ (Step 1) gives the kinetic part. The distance‑squared part ∫ d_𝒳(γ, B_1)²·(−t') dρ uses gmt‑inputs (1.2) integrated against dμ. **This is precisely (R)** — Wave 2 Priority 1, which Agent A leaves open. Agent B explicitly cites this in §7 as the route ("by Agent 2 / `gmt-inputs-for-metric-closure.md` (1.2) integrated against dμ"). So **(H1) is conditional on (R)**. This is correctly flagged in §7 but **contradicts §11's "(K) is settled in advance of (R²)" claim**.
- **(H2)** μ([a,b]) ≥ c(b−a) − Cδ: this is the integrated Talenti gap. Unconditional. ✓
- **(H3)** −t'(ρ) ≤ ρ/n: pointwise Talenti. Unconditional. ✓
- **(5.14)**: this is (K) itself. **Sound modulo Agent 3 (7.1)**, see Q‑B5/Q‑B6.

### Q‑B5. Does Agent B's argument prove (K) or only (H1)?

**Verdict: yes, the good‑set/bad‑set step is a genuine upgrade from (H1) to (K), modulo Q‑B6.**

The structure is sound: on G, divide by −t' ≥ τ_0; on B_{τ_0}, use the uniform Lipschitz bound (A0) to convert "bad metric derivative direction" (potentially large) into "small Lebesgue measure" (|B_{τ_0}| ≤ K_2 δ). The dimensional constant in Step 4 is real (τ_0 = ρ_*/(2n)). This is **a clean argument**, exactly as the brief described: bad set has wrong direction compensated by small measure; good set has direct division.

So the **mathematical structure** of Theorem 5.1 is correct *given* the inputs.

### Q‑B6. Hidden circularity — **this is the main W2 issue**

**Verdict: YES, hidden circularity. Agent B's "unconditional" claim is wrong.**

Trace the ingredients of Step 1 (5.1):

1. Agent 1 (A1): the deficit identity — **unconditional**.
2. Lemma 2.1 (A0): uniform Lipschitz — **unconditional**.
3. Lemma 4.1: bad‑set bound via (3.3) — **unconditional**.
4. **Agent 3 (7.1)**: |γ̇|² ≤ C(D_H + D_I) for a.e. ρ — Agent B uses this as the bridge between (D_H + D_I) and |γ̇|².

What does Agent 3 (7.1) actually depend on? Read `agent3-metric-first-variation.md` §7, which explicitly says:

> "(T) plus the bounds of `gmt-inputs-for-metric-closure.md` (2.4), (3.2):
> (∫|V_ρ − V̄_ρ|)² ≤ C·D_H,    (∫|H_{z_ρ,ρ} − V̄_ρ|)² ≤ C·D_I"

Now:
- gmt‑inputs **(3.2)** = the D_H Cauchy‑Schwarz line of `gmt-inputs-for-metric-closure.md` §3. This **is** unconditional (just Cauchy‑Schwarz from Agent 1, with constants).
- gmt‑inputs **(2.4)** = (∫|H_{z_ρ,ρ} − V̄_ρ|)² ≤ C·D_I. The proof of (2.4) in gmt‑inputs §2 uses BOTH (1.1) (the FJ‑strong oscillation, OK) AND **(1.2)** — the L¹ radial trace `(∫||x−z_E|/ρ−1|)² ≤ C(P(E) − P_ρ)`.

**(1.2) IS exactly (R) = Agent 2's Conjecture 3.6 = Wave 2 Priority 1.** And Agent A has just shown (R2) at rate δ is open, which (via Cauchy‑Schwarz) is what is required to give (1.2)=(R) at rate δ.

So Agent B's Step 1 — concretely (5.1) — uses Agent 3 (7.1) → gmt‑inputs (2.4) → gmt‑inputs (1.2) = (R) = Wave 2 Priority 1 = **open**.

**Conclusion (W2‑5): Theorem 5.1 of `wave2-B-kinetic-bound.md`, and hence Corollary 7.2 "Plan 2 closure", is *conditional* on (R), exactly as Plan 2 was after Wave 1.** The "unconditional" wording in §11 (and in the 200‑word summary) is wrong. The §7 bullet "(H1) by Agent 2 / gmt‑inputs (1.2) integrated against dμ together with (3.2)" is the same conditionality written truthfully, contradicting §11.

**Net.** What Agent B genuinely *adds*: the good‑set/bad‑set decomposition (Step 2 + Step 3 + Step 4) and the Lemma 2.1 uniform Lipschitz bound. These are real and useful and would turn an unconditional (H1) into an unconditional (K). What Agent B *requires* but does not supply: (H1) itself in the form needed for (K), via Agent 3 (7.1), depends on (R). So Agent B's contribution is a **conditional reduction (H1) ⇒ (K)**, not an unconditional (K).

### Q‑C1. FvHT/Fraenkel centre reconciliation rate

**Verdict: correct.** Cicalese–Leonardi 2012 Prop. 2.3 uniqueness gives |z − z^Fr| ≤ C·𝒜(E) for any z with |EΔ(z+B_ρ)| ≤ 2·inf_{z'}|EΔ(z'+B_ρ)|. FvHT §4 supplies ε_j = O(√δ); Cauchy–Schwarz on the block converts the block‑integrated L¹ closeness ε_j to a per‑level Fraenkel asymmetry of order √δ on a.e. ρ in the block. The C·𝒜(E_ρ) bound, with 𝒜(E_ρ) ≤ C(δ_T)^{1/2}, yields |z_j − z^Fr_ρ| ≤ C√δ. ✓ The "absorption into the constants" of (T) and (3.4) is correct because the H_{z,ρ} difference is L∞‑bounded by O(|z_j − z^Fr_ρ|/ρ_*) = O(√δ), and P(E_ρ) is bounded — the contribution to the L¹ integrand is O(√δ), and the squared form is O(δ), absorbable.

### Q‑C2. Figalli–Maggi 2011 Appendix A Thm A.1

**Verdict: legitimate citation.** Figalli–Maggi 2011 *On the shape of liquid drops…* App. A indeed contains the Sard‑for‑W^{2,p} statement at p > n needed: for u ∈ W^{2,p}_{loc}, p > n, the set {|∇u| = 0} ∩ {u = t} has H^{n−1}‑measure zero for a.e. t. The W^{2,p} hypothesis is met by the variational torsion via Stampacchia. The De Giorgi structure theorem (∂*E_t ⊆ {u = t} up to H^{n−1}‑null sets) then gives (C2.1). Agent C's primary‑citation choice is correct; back‑ups (DPMM 2021 Lem 2.4; Brothers–Ziemer 1988 Lem 2.4) are also correct.

### Q‑C3. gmt‑inputs §1 rewrite — **internal inconsistency**

**Verdict: substantively wrong as written.** Agent C's replacement paragraph attributes (1.2) to Wave 2 Agent A's (R2) and writes the Cauchy–Schwarz chain (R2) → (1.2). But Wave 2 Agent A's verdict on (R2) at rate δ is **negative** — (R2) is reducible to (B²), which is open. So Agent C's rewrite as drafted advertises (1.2) as *closed*, when in fact (1.2) is **still open at the sharp rate**, conditional on (B²).

The correct rewrite would attribute (1.2) to "the open quadratic Fusco–Julin oscillation (B²) of `wave2-A-radial-l2-trace.md` §5.2 Theorem B" and explicitly flag (1.2) as conditional on (B²). The Cauchy–Schwarz chain (R2) → (1.2) is fine in *form*, but it presupposes (R2) — which Agent A leaves open.

**This is a documentation error that must be fixed before any of the C3 patches is merged.** As currently drafted, it would mis‑represent the Plan 2 status.

### Q‑D1. Status of Plan 2 after Wave 2

**Net.** After Wave 2, Plan 2 closure (sharp 𝒜² ≤ Cδ_T) is **conditional on a single open theorem**, namely

  **(B²)**  ∫_{∂*E} |ν_E − e_r|² dℋ^{n−1} ≤ C(P(E) − P(B_ρ))

for finite‑perimeter near‑balls in B_R, no graph, no selection. Via Agent A Theorem B, (B²) ⇔ (R2) at rate δ ⇔ Π = O(δ) ⇔ M₁(volume L¹‑moment) = O(δ).

The status of Plan 2 vis‑à‑vis Wave 1 issues:

- **(R) = Conjecture 3.6 = I1.** Reduced to (B²) by Agent A. Still **open**, but better isolated.
- **(K5.14) = I4, I11.** Mathematical structure (the good‑set/bad‑set upgrade) is supplied by Agent B. *But* the (H1) input feeding into Step 1 of Agent B requires Agent 3 (7.1), which uses gmt‑inputs (2.4), which uses (1.2) = (R). So (K) is **conditional on (R)** — i.e. on (B²) — exactly as (R) is.
- **(I5) centre identification.** Closed by Agent C §C1, modulo wording fix.
- **(I10) Sobolev Sard.** Closed by Agent C §C2.
- **(I12) gmt‑inputs §1 rewrite.** Patch needs revision per Q‑C3.

So Plan 2 is **conditional on (B²) only**, not on two separate items. This is the silver lining — the open dependency has been compressed to one statement.

### Q‑D2. The conditionality given W2‑5

Restating precisely: **Plan 2 closure (sharp Saint–Venant 𝒜(Ω)² ≤ Cδ_T(Ω) for bounded Ω) is conditional on**

  (B²) ∫_{∂*E}|ν_E − e_r|² ≤ C(P(E) − P(B_ρ)) in the no‑graph no‑selection regime.

**Both** Wave 2 priorities reduce to (B²) — Priority 1 ((R)) directly via Agent A Theorem B; Priority 2 ((K)) indirectly because Agent B's Step 1 uses Agent 3 (7.1) which uses (R)=(1.2). So while Wave 2 looked like "two priorities, one closed, one open", the actual status is **one common open dependency**.

### Q‑D3. Wave 3 priorities

**Highest (W3‑P1): prove (B²) — equivalently, the L¹ volume‑radial moment M₁ = O(δ).**

This is the single residual gap. Agent A §9 lists three plausible escape routes (α, β, γ), none of which is in the literature for the no‑graph regime. The most promising routes:

(i) A **spherical H^{1/2} trace via the *level‑set* parametrization**, not the boundary parametrization: parametrize the *radial slice* E_θ as a 1D Borel set and lift the slicewise mismatch into a 2nd‑moment via slicewise Hardy.

(ii) An **ACF monotonicity formula** route à la Allen–Kriventsov–Neumayer 2023, applied not to the FK deficit but to the boundary deficit P(E) − P(B_ρ) directly.

(iii) **Sharp Talenti via Brothers–Ziemer rigidity at first order**: the Brothers–Ziemer rigidity theorem gives that if equality holds in the Polya–Szegő rearrangement, then u^* and u are related by a translation. Quantitative versions exist; none in the literature at the rate (B²) needs, but the framework is close.

**Second (W3‑P2): publish Agent A Theorem A as a standalone result.**

The bad‑ray quadratic absorption is a *genuinely new* GMT statement, independent of (B²) and is a clean, citable theorem in its own right.

**Third (W3‑P3): relax the target.**

If (B²) proves intractable, the honest fallback is to publish **Plan 2 at the FMP rate δ_T^{1/2}** as a *no‑selection, no‑graph* proof.

### Q‑D4. Is Plan 2 dead?

**No, but it is in the same position as it was after Wave 1 in substance.** The genuine substantive change is that:
- The (R) bottleneck has been compressed to a single quadratic form (B²) (this is real progress).
- The (K5.14) ingredient has been *partially* mechanically supplied (Agent B's good/bad set decomposition is a useful piece of metric‑analytic machinery), but the chain still routes through (R).

Plan 2 still has a path to closure conditional on (B²). **It is alive, just not closer to closure than after Wave 1 — only better diagnosed.**

The truthful Wave 2 framing is: *"Wave 2 produced rigorous bad‑ray quadratic absorption and a clean (H1) → (K) upgrade lemma. Both reduce, ultimately, to the same open theorem (B²). Plan 2 closure is conditional on (B²)."*

---

## 3. Final verdict on post‑Wave‑2 status

| Item | Status |
|---|---|
| (R) at rate δ | open, equivalent to (B²) |
| (K) at rate δ | open, conditional on (R) — Agent B's "unconditional" claim is wrong |
| (B²) in no‑graph | open; not in literature (verified against five candidate papers) |
| Plan 2 closure | conditional on (B²) only — one open theorem |
| I5 centre identification | closed (Agent C §C1) |
| I10 Sobolev Sard | closed (Agent C §C2) |
| I12 gmt‑inputs (1.2) rewrite | drafted but mis‑attributes (R2) status — must be revised before merge |

**Bottom line.** Plan 2 has exactly one open mathematical dependency: (B²). Wave 2 did not close it; Wave 2 isolated it.

---

## 4. Wave 3 priorities (ordered by de‑risking)

1. **W3‑P1 (Highest).** Prove (B²) ∫_{∂*E}|ν_E − e_r|² ≤ C·δ in the no‑graph regime. This single theorem closes both Wave 2 priorities at once. Most promising route: an ACF‑style monotonicity formula on the boundary perimeter deficit (extend Allen–Kriventsov–Neumayer 2023), or a Brothers–Ziemer rigidity refinement at first order.
2. **W3‑P2.** Re‑write `wave2-C-cleanup.md` §C3 to correctly attribute `gmt-inputs-for-metric-closure.md` (1.2) to the *open* (B²), not to a "closed" (R2). Pure documentation.
3. **W3‑P3.** Re‑write `wave2-B-kinetic-bound.md` §1, §7, §11 to replace "(K) is settled in advance of (R²)" / "unconditional" wording with the truthful "(K) is closed conditionally on (R), via Agent 3 (7.1) → gmt‑inputs (2.4) → (1.2)=(R)". Pure documentation.
4. **W3‑P4.** Spin off Agent A Theorem A (bad‑ray quadratic absorption) as a standalone GMT note for publication. Independent value.
5. **W3‑P5.** If (B²) does not close in 3–6 months, prepare a Plan 2 paper at the FMP rate δ^{1/2} — same conclusion as the existing Plan 1, but via no‑graph no‑selection methods. Lower priority and lower payoff, but real.

Closing W3‑P1 closes Plan 2 unconditionally. W3‑P2, W3‑P3 are cleanup. W3‑P4, W3‑P5 are independent papers.
