# Structural audit — Plan 1 (sharp quantitative Faber–Krahn via a single-set selection map)

Scope: argument/structural soundness only. Sources audited: `WHAT_PLAN1_DOES.md`,
`quantitative-selection-principle.md`, `plan1.md`, `route-A-summary.md`,
`route-A-summary.tex`, `corrections-needed.md`, `PLAN1_AGENT_REPORT.md`, and
Brasco–De Philippis–Velichkov `1306.0392v1.pdf` (Lemmas 4.2, 4.5, 4.6, 4.7,
4.9, 4.11, 4.12, 4.13, 4.16, Theorem 4.18, Theorem 3.3, Proposition 4.4).

The headline conclusion: Plan 1's central claim about question A is **largely
correct and is the genuine technical content of the programme** — the
quotient-preservation half of BDV's selection really is sequence-free and
Plan 1 reproduces it faithfully. But the programme contains one **showstopper**
structural gap (the global graph patching, F2) and one **serious** circularity
in the bootstrap (B / F3), plus several serious unproved bridges. Net: Plan 1
is *not* "a complete proof modulo uncomputed constants"; it has genuine
structural gaps, concentrated exactly where BDV's compactness did real work.

---

## A. Does Theorem 2.2 genuinely remove BDV's contradiction?

**Verdict: the quotient/asymmetry-preservation estimate is genuinely
sequence-free and correctly reproduced. But the contradiction BDV remove with
compactness was never in that estimate — it was in the *global graph
representation*, and Plan 1 has not removed it there (see F2). So "A" is
half-true: the part Plan 1 isolates is fine; the part it claims to have also
discharged is not.**

Detailed finding (this is the audit's core, so I give the BDV cross-check):

In BDV the asymmetry preservation is **Lemma 4.7(i)**: `|α(Ω_j) − ε_j| ≤ 3σε_j`,
together with `||Ω_j| − |B_1|| ≤ C_5 σ⁴ε_j`, and the energy bound is
**Lemma 4.7(iii)**: `0 ≤ F_η̂(Ω_j) − F_η̂(B_1) ≤ σ⁴ε_j`. Reading BDV's proof
(p.15–16, eq. (4.17)): both are derived **purely from the one-line minimality
comparison** `G_η̂,j(Ω_j) ≤ G_η̂,j(Ω̃_j) ≤ F_η̂(B_1) + (1+σ⁴)ε_j`, squaring
`√(ε_j²+σ²(α(Ω_j)−ε_j)²) ≤ ε_j(1+σ⁴)`. **No limit, no compactness, no
contradiction enters here.** The index `j` is a passive label; BDV never pass
to `j→∞` to obtain (i) or (iii). Plan 1's Lemma 1–3 and Proposition 4 of
`quantitative-selection-principle.md` reproduce exactly this computation with
`τ` in place of `σ`. The algebra (`τ²(α(U_*)−ε)² ≤ 2εδ+δ²`, Lemma 1, lines
241–249) is correct. Lemma 2's volume bound uses BDV Lemma 4.5/(4.9) correctly.

Therefore Plan 1's claim that the **asymmetry-preservation + deficit-ratio
bound holds for a single set without a limiting argument is TRUE**, and
`C_sel(n,R)` is a genuine estimate (it is `2` times the Lipschitz/volume
constants `C_2(R), C_4(N,R)` of BDV Lemma 4.2(ii)/4.5, plus the
`O(δ)`-dilation loss), **not** a placeholder hiding removed compactness. The
collapse-to-ball worry is excluded *by the same computation*: `α(U_*) ≥
(1−ρ)ε > 0` is a quantitative inequality, not a limit statement. This part of
the programme is sound and is a correct, faithful single-set recasting.

**However**, the audit's question A presupposes that this estimate is "BDV's
contradiction." It is not. Re-reading BDV's *Proof of Proposition 4.4*
(p.26, §4.4) and *Proof of Theorem 4.3* (p.13): BDV's genuine
compactness/contradiction is used in **two distinct places that are NOT the
ratio estimate**:

1. **Lemma 4.13** (Kuratowski convergence `∂Ω_j → ∂B_1`, p.20–21), invoked in
   the Prop. 4.4 proof to assert: "for `j` large there exists a point
   `x_0 ∈ ∂Ω_j ∩ B_{µρ(µ)}(x̄)`" *for every* `x̄ ∈ ∂B_1`. This is what turns
   per-scale Alt–Caffarelli flatness into a **global** graph. It is purely
   qualitative ("for `j` large depending on `µ`").
2. The `C^{2,γ}`-regularity needed for Theorem 3.3 ("for `j∈ℕ` large enough
   each `U_j` is a nearly spherical set of class `C^{2,γ}`", p.13).

Plan 1's true burden is to make (1) and (2) quantitative. Its own
`quantitative-selection-principle.md` §5 admits this ("Thus the selection
route has been reduced to two concrete missing quantitative regularity
statements", lines 684–686). So the honest status of A is: **the part Plan 1
calls "the contradiction" was already sequence-free in BDV and Plan 1
correctly keeps it so; the part that genuinely *was* a compactness argument is
relocated into the graph-entry lemmas, where it is not in fact discharged
(F2).** The narrative in `route-A-summary.md` §10 ("The single contradiction
step that was removed: BDV's sequential selection + compactness limit") is
therefore **structurally mislabelled**: the selection ratio was never the
contradiction; the compactness sat in Lemma 4.13.

---

## B. The `C^{1,γ} → small C^{2,γ_0}` bootstrap: is it non-circular?

**Verdict: there is a genuine circularity / unproved-uniformity gap in
Proposition 5.1 (`prop:bootstrap`, route-A-summary.tex:413–434). The
*interpolation half* of the argument is logically valid; the *uniform Schauder
half* it is interpolated against is asserted, not established, and its
constant `M_m(N,R)` is exactly the object whose uniformity is in question.**

The logic Plan 1 wants is the standard one and is, abstractly, sound:
`‖g‖_{C^{2,γ_0}} ≤ C ‖g‖_{L^∞}^{1−θ} ‖g‖_{C^{m,γ}}^θ` with `‖g‖_{L^∞}` small
(from Hausdorff closeness, Lemma `lem:interp`, lines 436–470) and
`‖g‖_{C^{m,γ}} ≤ M_m(N,R)` *fixed*. If `M_m` is a genuine `(N,R)`-uniform
constant, the conclusion `‖g‖_{C^{2,γ_0}} ≤ δ_sph` follows and there is **no**
circularity (BDV Theorem 3.3 needs only a *fixed* threshold `δ_1(N,γ)`, since
the `C^{2,γ}` norm enters its proof solely through the modulus
`ω(‖φ‖_{C^{2,γ}})`, p.8, eq.(3.4) — confirmed against the source: the
required smallness is `ω(δ_1) ≤ 1/(16N²)`, a fixed number, **not**
smallness relative to the deficit). So question B's "is δ_sph required to be
arbitrarily small relative to the deficit?" — answer: **no**, and that part of
the architecture is correct. P4 in `WHAT_PLAN1_DOES.md` slightly overstates
the difficulty here: the `H^{1/2}`-vs-`C^{2,γ}` gap is real but the closure
only needs a fixed `C^{2,γ}` threshold, which interpolation *can* in principle
deliver.

The circularity is one level down, in **Proposition 5.1's proof itself**
(lines 423–433). It claims `‖g‖_{C^{m,γ}} ≤ M_m(N,R)` "by hodograph +
Kinderlehrer–Nirenberg/Lieberman Schauder, iterated." Two structural defects:

- (B-i) **The Schauder iteration is run on the graph whose smallness is being
  proved.** The hodograph/oblique-derivative Schauder estimate produces
  `‖g‖_{C^{m,γ}} ≤ M_m` only if the oblique boundary operator is uniformly
  elliptic/oblique *with constants independent of `g`*, which requires an
  a-priori `C^{1,γ}` (in fact `C^{2}`) bound on `g` that is **small enough for
  the hodograph map to be a non-degenerate diffeomorphism on a fixed collar**.
  Graph entry supplies `‖g‖_{C^{1,γ}} ≤ Cµ` with `µ = µ(N,R)` fixed-small —
  this *is* available pre-bootstrap, so the diffeomorphism is non-degenerate
  and (B-i) is, on inspection, **not fatal**: the first-order smallness needed
  to start hodograph comes from the flatness theorem, not from the conclusion.
  This should be stated explicitly in the proof; currently it is implicit and
  reads circularly. Severity: **minor-to-serious (presentation; the constant
  chain must record that `M_m` depends on `µ(N,R)` only).**

- (B-ii) **The genuine gap: the right-hand side / Bernoulli data is asserted
  smooth with uniform bounds.** Proposition 5.1's proof says "the selected
  Bernoulli law has an explicit smooth right-hand side on the fixed collar"
  and cites BDV Lemma 4.16. BDV Lemma 4.16 gives `q_u ∈ C^{1,γ}` with uniform
  bounds **for the BDV sequential minimizers**; Plan 1 needs this for the
  *single selected `U_*`* with the penalisation prefactor
  `τ²(α(U_*)−ε)/√(ε²+τ²(α(U_*)−ε)²)`. `quantitative-selection-principle.md`
  §4 (lines 488–504) argues this prefactor is `≤ τ` hence `q_{u_*}` has
  uniform `C^k`. That argument is **correct for the boundedness of the
  prefactor** but does **not establish uniform `C^k` smoothness of `Ψ_{U_*}`
  itself**, which is a nonlocal functional of `U_*` (it contains
  `∫_{U_*} (z−x_{U_*})/|z−x_{U_*}| dz` and `|x−x_{U_*}|`); its `C^k` norm on
  `∂U_*` depends on the regularity of `∂U_*` — i.e. on `g` — so the
  higher-order bootstrap *does* feed back on itself beyond first order. BDV
  break this loop with Lemma 4.16 + Theorem 4.18 *along the sequence* and
  Ascoli (p.26: "by the Ascoli–Arzelà Theorem ... `g_j → 0` in `C^{k−1}`").
  Plan 1 must reproduce that iterated bootstrap with `g`-independent
  constants and does not; it asserts the endpoint. **Severity: serious.** It
  is not a mere uncomputed constant: the *existence* of a `g`-independent
  `M_m` is the claim, and it is unproved.

So B's net: the macro-architecture (interpolate fixed high norm against small
`L^∞`; closure needs only a fixed threshold) is **non-circular and correct**.
The micro-step that supplies the fixed high norm (Prop. 5.1) is **asserted,
not proved**, and contains a real (not bookkeeping) feedback at orders `≥2`
via the nonlocal Bernoulli bracket.

---

## C. Volume normalisation (P2)

**Finding (serious, but well-localised).** `route-A-summary.tex` Lemma
`lem:rescale` (lines 274–303) now *does* write a transformed Bernoulli law
(unlike the older `corrections-needed.md` §2 state), with scaling
`Λ̃ = r_*^{−2}Λ`, `ã_σ = r_*^{−1}a_σ`, `|r_*−1| ≤ Cδ_T`. The scaling
exponents are individually plausible. Two structural points:

- (C-i) The derivation is delegated ("Detailed computation in
  `corrections-response.tex`, §1"); the parenthetical bracket-scaling tally
  ("one `r_*` from `|·|`, `r_*^N` from the centroid ... the volume Jacobian
  factor cancels the `r_*^N`") is an *assertion of cancellation* presented
  inside a proof. For an audit-ready document the cancellation must be shown,
  not narrated. **Severity: serious (the EL/Bernoulli law downstream — Lemma
  `prop:flatness`, BDV 4.16 — is applied to `Ω̃`, so an unverified prefactor
  scaling propagates).** This is exactly the P2 item; it is *improved* over
  `corrections-needed.md` but not closed.

- (C-ii) Logical-order subtlety: the Bernoulli law is the **Euler–Lagrange
  equation of the penalised functional for `U_*`**, derived in BDV via
  Lemma 4.14/4.15 (interior minimality `Ω_j` minimal w.r.t. `W₀^{1,2}(N_δ(Ω_j))`
  perturbations, p.21–22). After dilation `Ω̃ = r_*^{-1}U_*` is **no longer a
  critical point of the same functional** — it is the image of one under a
  fixed map. Plan 1 treats the dilated law as if `Ω̃` still solved an EL
  problem on the fixed collar (used in `prop:bootstrap`). The law is an
  identity that *transports* correctly (that is fine), but the *minimality*
  used to run Alt–Caffarelli/Schauder must also be transported; Lemma
  `lem:rescale` transports the equation but not the variational inequality
  (4.19). Downstream lemmas (`prop:flatness`, `prop:bootstrap`) silently
  require the quasi-minimality, not just the pointwise EL identity. **Severity:
  serious** — the regularity machinery's hypothesis (quasi-minimality, BDV
  Remark 4.8) is not shown to survive normalisation; only the EL identity is.

---

## D. Constant-chain integrity

**Finding: no hidden dependence on `δ_T` or on the conclusion in the *named*
ledger, with one exception flagged below.** The `route-A-summary.md` ledger
constants (`τ_ex, τ_reg, C_sel, q_sel, C_H', h_F, α_graph, M_m, c_sph,
δ_sph, C_BDV, c_*, q_*`) are each, on inspection, functions of `(N,R)` and of
BDV's own `(N,R)`-constants. The composition `q_* = c_*/(2C_sel)` does not
circularly reference `q_*` or `δ_T`. `c_far,SV` (Lemma `lem:far`, lines
623–658) correctly uses BDV's *suboptimal* (non-sharp) Saint–Venant
`E−E(B_1) ≥ C_8^{-1}𝒜⁴` — a previously established result — so the far regime
does **not** smuggle the sharp-stability compactness back in. That is sound.

Exception: **`M_m(N,R)` is in the ledger as `(N,R)`-uniform but is exactly the
unproved object of F3/B-ii.** Listing it as a named constant *presupposes* the
uniformity that is the open problem. This is the one place the ledger's
"every constant depends only on `(N,R)`" is **claimed, not established**.
Severity: serious (it is the B-ii gap, surfacing in the ledger).

Also: `δ_sph(N,γ_0)` in `lem:interp` is BDV Theorem 3.3's threshold and is
genuinely fixed (confirmed against source, §B above) — no circularity there.

---

## E. Net assessment — severity-tagged structural gaps

| # | Finding | Location | Severity |
|---|---------|----------|----------|
| F1 | **Mislabelled "removed contradiction."** BDV's selection ratio (Lemma 4.7(i),(iii)) is already sequence-free; the genuine compactness is Lemma 4.13 (Kuratowski → global graph) + qualitative `C^{2,γ}`. Plan 1's headline ("removed the contradiction of the selection") is structurally inaccurate; the contradiction was relocated, not removed, into graph entry. | `route-A-summary.md` §2,§10; `WHAT_PLAN1_DOES.md` lines 18–43 vs BDV p.15–16, p.20–21 | serious (correctness of the central narrative; the math of Thm 2.2 itself is sound) |
| F2 | **Global graph patching is not made quantitative — the real removed-compactness gap.** `prop:globalgraph` (route-A-summary.tex:361–383) assumes `prop:flatness` "holds at every `x̄∈∂B_1`" and patches "via uniqueness." BDV obtain "a point `x_0∈∂Ω_j` near every `x̄`" *only from Lemma 4.13's Kuratowski convergence* (qualitative, "for `j` large"). `prop:flatness` (lines 340–360) derives the per-`x̄` boundary point from the *Hausdorff* bound `d_H ≤ h_F` — but that Hausdorff bound (`lem:alphaH`) itself rests on BDV Lemma 4.9 density estimates whose constants BDV prove **for the sequential minimizers**; Plan 1 invokes 4.9 as a black box for the single `U_*` without re-deriving uniformity, and the "patch via uniqueness" of overlapping Alt–Caffarelli graphs into one global `g` is asserted with no quantitative non-folding/cover argument beyond a one-line `µ_tub` slope remark. This is precisely the step BDV did by compactness, and it is **not discharged**. | route-A-summary.tex:340–404; `quantitative-selection-principle.md` Lemmas 6–7 (lines 566–657, themselves flagged "first remaining constant-tracking task", "the most important remaining theorem") | **showstopper** |
| F3 | **Uniform Schauder constant `M_m(N,R)` asserted, not proved; nonlocal Bernoulli bracket creates real higher-order feedback.** | route-A-summary.tex:413–434 (`prop:bootstrap`); `quantitative-selection-principle.md` §4 lines 488–504 | serious |
| F4 | **Volume-normalisation transports the EL identity but not the quasi-minimality** that the regularity machinery (Alt–Caffarelli, Schauder) actually consumes; bracket-scaling cancellation narrated, not shown. | route-A-summary.tex:274–303 (`lem:rescale`) | serious |
| F5 | **Black-box uniformity over the single selected set.** BDV Lemmas 4.9/4.11/4.12/4.16 are quoted "with constants depending only on `(N,R)`" but BDV state/prove them for the *sequence* `{u_j}` with the `j`-uniform structure coming from `ε_j→0`. For one `U_*` with fixed `τ=q^{1/4}`, the constants are plausibly uniform (the proofs are per-set given `σ≤σ_i`), but Plan 1 *asserts* this transfer rather than checking that none of BDV's 4.9–4.16 proofs use a sequential/`ε_j→0` ingredient. (Spot-check: BDV 4.9–4.12 proofs are per-set given `σ≤σ_i`; BDV 4.13 *is* sequential — consistent with F2 being the locus.) | `route-A-summary.md` "black box" list; `quantitative-selection-principle.md` §4 | minor-to-serious (likely OK for 4.9–4.12,4.16; the sequential one, 4.13, is the F2 gap) |
| F6 | Route B (Bernoulli spectral closure) remains conditional (bilinear source not enumerated, smallness constants `σ_*,δ_*,q_*` untracked) — already self-reported; not load-bearing for Route A. | `PLAN1_AGENT_REPORT.md` 4th/5th pass; `corrections-needed.md` §4,§6 | serious-but-acknowledged (off the unconditional route) |

### Most serious structural gap

**F2 (showstopper): the local-flatness-to-global-graph patching.** This is the
*actual* location of the compactness Plan 1 claims to have removed. BDV cover
`∂B_1` and locate a free-boundary point near every `x̄` using Lemma 4.13's
Kuratowski convergence, which is genuinely a compactness/limit statement.
Plan 1's replacement chain (α → Hausdorff → per-`x̄` flatness → global patch)
ends in two lemmas that `quantitative-selection-principle.md` itself labels as
the open problems ("the first remaining constant-tracking task"; "the most
important remaining theorem"). `route-A-summary.tex` *upgrades these to
proved-looking propositions* (`prop:flatness`, `prop:globalgraph`) whose
"proofs" are slab-inclusion sketches plus "patch via uniqueness," with the
global cover/non-folding argument asserted in one clause. The single-set
selection (Thm 2.2) is genuinely sound (question A), but the programme's
end-to-end claim fails here: **the compactness was not removed, it was pushed
into an unproved graph-patching lemma.**

### Verdict

Plan 1 is **not** a complete quantitative proof modulo named-but-uncomputed
constants. Thm 2.2 (the conceptual core) is correct and genuinely sequence-
free — the audit confirms BDV's ratio estimate was never the contradiction, so
recasting it single-set is legitimate and well-executed. But there is a
**showstopper structural gap (F2)** at the global graph patching — the true
home of BDV's compactness — and a **serious circularity/unproved-uniformity
gap (F3/B)** in the Schauder constant, plus serious issues in normalisation
(F4) and black-box transfer (F5). These are structural, not cosmetic: they
concern whether named objects (`M_m`, the global `g`, the post-normalisation
quasi-minimality) *exist with the claimed uniformity*, not merely their
numerical size.
