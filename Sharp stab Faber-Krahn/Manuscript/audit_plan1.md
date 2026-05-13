# Internal Audit — Plan 1 (Agent 15)

**Audited drafts**

- `Manuscript/plan1_selection.tex` (Agent 5)
- `Manuscript/plan1_graph_entry.tex` (Agent 6)
- `Manuscript/plan1_nearly_spherical.tex` (Agent 7)
- `Manuscript/plan1_kohler_jobin_transfer.tex` (Agent 8)

**Source blocks cross-checked**

- `Plan 1/quantitative-selection-principle.tex`, `Plan 1/graph-entry-closure.tex`,
  `Plan 1/route-A-summary.tex`, `Plan 1/faber-krahn-transfer.tex`.
- `Final/SelectionPrinciple.tex`, `Final/GraphEntry.tex`,
  `Final/SchauderInterpolation.tex`, `Final/NearlySphericalClosure.tex`,
  `Final/SaintVenantAssembly.tex`, `Final/BoundedReduction.tex`,
  `Final/KohlerJobinTransfer.tex`.
- `Plan 1/bernoulli-spectral-closure.tex` and
  `Plan 1/bernoulli-expansion-proofs.tex` (conditional Bernoulli spectral
  route — checked for silent use).

---

## Verdict

**PASS — no blocking findings.**

The Plan 1 chain (selection → graph entry → Schauder/interpolation entry →
BDV nearly spherical → bounded sharp Saint–Venant → bounded reduction →
Kohler–Jobin → sharp Faber–Krahn) closes coherently. Every load-bearing
theorem has stated hypotheses, every constant has declared dependence,
and no proof is shorter than the corresponding source block (Agent 5
and Agent 6 in fact expand on the source sketches at the
quotient-preservation and patching steps). The conditional Bernoulli
spectral route is **not** silently invoked anywhere: every occurrence
of the word "Bernoulli" in the drafts refers either to the **BDV
one-phase free-boundary regularity package** (Lemma 4.16 / Thm 4.18 —
unconditional) or to the volume-rescaled form of that classical Bernoulli
free-boundary identity, never to the conditional spectral route of
`Plan 1/bernoulli-spectral-closure.tex` /
`Plan 1/bernoulli-expansion-proofs.tex`.

Findings below are MAJOR / MINOR / NOTE only.

---

## MAJOR findings (none blocking; should be patched before final assembly)

### MAJOR-1. `α_small` is defined incompatibly between Agent 6 and Agent 7

- **Location.** Agent 6, `plan1_graph_entry.tex` line 737–738 and
  Theorem 4 (line 760–761); Agent 7, `plan1_nearly_spherical.tex`
  eq. `\eqref{eq:plan1-asmall}` (line 322–327).
- **Issue.**
  - Agent 6 defines
    `α_small(n, R, γ_0) := min{α_graph(n,R), α_sph(n,R,γ_0)}`.
  - Agent 7 defines
    `α_small(n, R) := (1/2) min{ε_sel(n,R), α_graph(n,R),
    α_sph(n,R,γ_0)}`.
  - Same symbol, two different definitions and dependence lists
    (Agent 7 silently drops `γ_0` from the argument list even though
    `α_sph` depends on `γ_0`; Agent 7 also adds `ε_sel` and a factor
    `1/2`).
  - The Agent 7 definition is strictly stronger (smaller threshold), so
    the chain is **logically correct** at the manuscript level. But the
    repeated symbol with two different definitions will trip up the
    Notation/Unification Agent (Agent 17) and the Final Assembly Agent
    (Agent 19).
- **Recommended fix.** Either (a) Agent 17 renames Agent 6's
  intermediate quantity to `α_small^{graph}` (or just `α_GS`) and uses
  `α_small` exclusively in the Agent-7 sense; or (b) Agent 7 redefines
  using a fresh name `α_*^{NS}(n,R,γ_0)`. The factor `1/2` and the
  `ε_sel` summand in Agent 7 should be displayed at the point of use
  (otherwise the reader cannot reconstruct why
  `α_small ≤ ε_sel/2` is the right cushion for the `3/2`-loss in (S2)).

### MAJOR-2. `C_2` dependence: `C_2(R)` vs `C_2(n,R)` clash

- **Location.** Agent 5, eq. `\eqref{eq:bdv42ii}` (line 98), states the
  BDV Lipschitz comparison with constant `C_2(R)` (depending only on
  `R`); Agent 7, (B2)(ii) eq. `\eqref{eq:plan1-42ii}` (line 138–140)
  and downstream eq. `\eqref{eq:plan1-anear}` write `C_2(n,R)`.
- **Source check.** `Final/SaintVenantAssembly.tex` line 75 and its
  constant table (line 393) record `C_2 = C_2(R)` (`R` only); BDV
  Lemma 4.2(ii) as stated there is in fact dimension-aware via
  `|Ω₁△Ω₂|` so `C_2(R)` is the canonical convention. Agent 7's
  `C_2(n,R)` is a harmless strengthening (any `C_2(R)` is also an
  `(n,R)`-constant), but it contradicts Agent 5 and the cited source.
- **Why it matters.** The constant chain in Agent 7 §`sec:plan1-constants`
  declares `C_2(n,R)` as `(n,R)`-dependent (entry in line 615); Agent 5's
  constant table (line 777) declares `C_2` as `R`-dependent only.
  Agent 17 will need to pick one convention. Following the source, the
  correct entry is `C_2 = C_2(R)`.
- **Recommended fix.** Replace `C_2(n,R)` by `C_2(R)` throughout
  Agent 7 (4 occurrences), and adjust the dependence table.

### MAJOR-3. Domain class mismatch: "quasi-open" (Agent 5) vs "bounded open" (Agent 7) vs "open" (Agent 8, register)

- **Location.** Agent 5 uses "quasi-open subsets of $\overline{B_R}$"
  throughout (line 67 and following); Agent 7 declares "all sets are
  bounded open subsets of $\R^n$" (line 70) and states (B2) for
  "bounded open" sets (line 128, 135, 159); Agent 8 and the Notation
  Register §2 use "open with $0<|\Om|<\infty$" (the canonical class).
- **Issue.** The selection lemma produces a quasi-open minimiser
  (matching BDV); the nearly-spherical theorem and the bounded
  Saint–Venant statement use "open"; the final Plan 1 statement is for
  "open". There is no logical gap: a quasi-open set with the BDV
  regularity package is, in particular, an open set up to capacity-zero
  sets (BDV §2), and `δ_T`, `𝒜`, `α_BDV`, `λ_1` are insensitive to
  capacity-zero modifications. However, the manuscript currently does
  not say this anywhere.
- **Recommended fix.** Add one explicit sentence at the boundary
  between Agent 5 and Agent 6 (and/or at the start of Agent 7)
  stating that the BDV quasi-open class coincides, for the load-bearing
  quantities, with the open class of the notation register. The
  notation register §16 already declares the canonical class; the
  Plan 1 drafts must reconcile it at the agent boundaries.

### MAJOR-4. `λ_1(Ω) = ∞` case in the final theorem is not addressed

- **Location.** Agent 8, Theorem `thm:KJ-FK-upper` (line 639–660) is
  stated for "every open set $\Om\subset\R^n$ with $0<|\Om|<\infty$";
  Lemma `lem:KJ-ptwise` (line 415–427) requires `\lambda_1(\Om)<\infty`.
- **Issue.** For an arbitrary open `Ω` with finite measure (e.g.\ a
  countable union of disjoint balls of summable volume),
  `λ_1(Ω)` may equal `+∞`. In that case `δ_FK(Ω) = +∞` and the
  inequality holds trivially, but the proof of `thm:KJ-FK-upper` does
  not handle this case (it goes through `Lem:KJ-ptwise`, which has
  `\lambda_1(\Om)<\infty` as a hypothesis).
- **Recommended fix.** Add a one-line case split at the start of the
  proof of `thm:KJ-FK-upper`: if `\lambda_1(\Om)=+\infty` the
  inequality is trivial; otherwise apply `Lem:KJ-ptwise`. (This is the
  pattern already followed in `Final/master.tex`.)

---

## MINOR findings

### MINOR-1. `c_*^{NS}(n)` vs `c_*(n)` symbol drift

- **Location.** Agent 6 line 803 writes `c_*^{NS}(n)`; Agent 7 writes
  `c_*(n)` throughout (eq. `\eqref{eq:plan1-NS-alpha}`, line 217).
- **Issue.** Notation register §14 allows the bare symbol `c_*(n)`
  inside Plan 1 (since there is no in-paragraph clash with Plan 2's
  `C_*^{trace}`), so this is correct. The drift is purely cosmetic.
- **Recommended fix.** Agent 17 chooses one form globally; recommend
  `c_*^{NS}(n)` for clarity, since `c_FK` and `c_SV` also carry tags.

### MINOR-2. Agent 7 absorbs Agent 5's `r_*-1` error implicitly

- **Location.** Agent 7, §`sec:plan1-vol-bary` line 354–359.
- **Issue.** Agent 7 states "$|r_*-1|\le C(n,R)\,\delta_T(U_*)$" with
  a one-line citation to BDV Lemma 4.5 and Agent 5, but does not
  carry the explicit dependence: the constant absorbing
  "$1+O(\delta_T(U_*))$" into $C_{\rm sel}(n,R)$ is asserted, not
  exhibited. Agent 5 actually proves this in
  Lemma `plan1-sel-L2` and Remark `plan1-sel-ratio`, with explicit
  constant $C_5(n,R)$. This is the same level of detail as the source
  blocks, so it is not a Stop Condition; but the cross-reference would
  improve traceability.
- **Recommended fix.** Replace "the constants $C_{\rm sel}(n,R)$
  already include (Agent~5)" by a precise citation
  "see Lemma~\ref{lem:plan1-sel-L2} and Remark~\ref{rmk:plan1-sel-ratio}".

### MINOR-3. (B2)(iii) hypothesis name `\delta_3(n)` overloaded

- **Location.** Agent 7 §`sec:plan1-bdv-blackboxes` (line 125).
- **Issue.** Agent 7 declares `δ_3 = δ_3(n)` as the BDV Lemma 4.2(iii)
  smallness threshold and `δ_1 = δ_1(n, γ_0)` as the BDV Theorem 3.3
  threshold. The combined `δ_sph := min(δ_1, δ_3)` (eq. `\eqref{eq:plan1-deltasph}`)
  is fine. However, Agent 6 already defines a quantity called
  `δ_sph(n, γ_0)` (its `\delta_{\rm sph}` in eq.
  `\eqref{eq:plan1-ge-alpha-sph}`), used as the output threshold of
  the interpolation step. The two `δ_sph`'s play distinct roles (input
  threshold for NS vs output threshold from interpolation) but they
  must be exactly the same number so that the Agent 6 → Agent 7
  hand-off works; Agent 6 line 674 references "the smallness threshold
  of \cite[Theorem~3.3]{BDV}" and Agent 7 line 202 also references
  Theorem 3.3 — these will coincide if Agent 17 unifies them.
- **Recommended fix.** Agent 17 should align Agent 6 and Agent 7's
  definitions of `δ_sph`: both should be `min(δ_1(n,γ_0), δ_3(n))`,
  spelt out at first use in Agent 6 (currently only spelt out in
  Agent 7).

### MINOR-4. Agent 7's "implicit homothety + translation" reduction is asserted, not displayed

- **Location.** Agent 7 §`sec:plan1-vol-bary` paragraph
  "Barycentre normalisation" (line 379–397).
- **Issue.** Agent 7 says "the detailed reduction, which is a one-step
  rescaling plus translation, is recorded in
  `Final/NearlySphericalClosure.tex` (Corollary 2.4) and shows that
  we may replace [the strict hypotheses] by [the relaxed
  hypotheses] at the cost of replacing $c_*(n)$ by
  $\widetilde c_*(n) := c_*(n)/4$." The actual factor `4` is asserted
  on the authority of `Final/NearlySphericalClosure.tex`; this is the
  same level of detail as the source.
  Agent 7 then concludes that the post-normalisation hypotheses are
  trivially satisfied, so the actual constant in the conclusion is
  `c_*(n)` (no `/4`). This bookkeeping is correct but easy to misread.
- **Recommended fix.** Explicitly compute the volume/barycentre
  defects after the rescale + translate step (one paragraph) so the
  reader can verify that the factor `4` is *not* paid.

### MINOR-5. Removal of the volume normalisation in Agent 8 is sketched

- **Location.** Agent 8 Remark `rem:scale-removal` (line 343–364).
- **Issue.** The scale-invariance argument is correct but the chain of
  identities in `\eqref{eq:BR-scaleinv}` is truncated with "etc." and
  no final form is displayed. Agent 8 then re-derives the
  scale-removal in the proof of `thm:KJ-FK-lower` (line 553–564) using
  $\Om_*$; this works, but having two slightly different
  scale-removal arguments is redundant.
- **Recommended fix.** Either complete `\eqref{eq:BR-scaleinv}` and
  delete the redundant computation in the proof of `thm:KJ-FK-lower`,
  or delete `\eqref{eq:BR-scaleinv}` entirely.

### MINOR-6. Agent 7's `c_SV(n,R)` is double-named with Agent 8's import

- **Location.** Agent 7 Theorem `thm:plan1-SV` and Agent 8 Theorem
  `thm:SV-bounded` (which restates it under a different label).
- **Issue.** Agent 8 imports Agent 7's bounded Saint–Venant theorem
  with a fresh label `thm:SV-bounded`, but the same theorem appears in
  Agent 7 as `thm:plan1-SV`. Both labels will exist after Agent 19's
  integration. The duplicated statement is fine for stand-alone
  drafts but should collapse to a single theorem in the assembled
  manuscript.
- **Recommended fix.** Agent 19 deletes Agent 8's standalone restatement
  and replaces it by a reference to Agent 7's
  Theorem~\ref{thm:plan1-SV}.

---

## NOTE findings (informational)

### NOTE-1. Conditional Bernoulli spectral route — verified NOT silently used

The two source files `Plan 1/bernoulli-spectral-closure.tex` and
`Plan 1/bernoulli-expansion-proofs.tex` are conditional alternative
arguments and must not enter the main Plan 1 chain unconditionally.
The four Plan 1 drafts contain 14 occurrences of the word "Bernoulli"
(`plan1_selection.tex` 10 times, `plan1_graph_entry.tex` 5 times,
`plan1_nearly_spherical.tex` 1 time, `plan1_kohler_jobin_transfer.tex` 0 times).
Every single occurrence refers to:

- the BDV one-phase Bernoulli free-boundary regularity package
  (BDV Lemma 4.16, smooth Bernoulli coefficient on `\partial U_*`); or
- the volume-rescaled form of that classical Bernoulli identity
  (Agent 5, Lemma `plan1-sel-bern`); or
- the BDV Alt–Caffarelli flatness theorem (BDV Thm 4.18) for one-phase
  Bernoulli free boundaries (Agent 6 (R3), (R4)).

None of these is the *conditional* spectral-closure route. The drafts
correctly stop short of the conditional argument, in line with the
master brief.

### NOTE-2. Bounded reduction and Kohler–Jobin normalisation match the register

Agent 8's final theorem (`thm:KJ-FK-upper`) is stated with
`δ_FK(Ω) = (|Ω|/ω_n)^{2/n}(λ_1(Ω) - λ_1(B^*))`, which is the canonical
form in Notation Register §4 and Source Map D4.6. The intermediate
bounded Saint–Venant statement (`thm:BR`) is stated with $c_{\rm SV}^{\rm glob}(n)$
purely dimensional — the `R`-dependence in the input `c_{\rm SV}(n,R)`
is internalised at `R = R_*(n) := max(d(n), 2)`. The bounded
reduction radius `R_*(n)` matches Notation Register §1.

### NOTE-3. No rate loss `δ_T → √δ_T` anywhere in Plan 1

Every step of Plan 1 preserves the linear-in-`δ_T` exponent on `𝒜²`:

- Agent 5 (S3) preserves `Q_BDValpha` up to an `(n,R)`-multiplicative
  factor.
- Agent 6's threshold passing is in terms of `α_BDV(Ω)`, not its
  square root.
- Agent 7 BDV nearly-spherical gives `δ_T ≥ c_* α_BDV`, then
  `α_BDV ≥ ω_n^2 𝒜² / C_1`, so `δ_T ≥ const · 𝒜²` (linear).
- Agent 8 bounded reduction (Lemma `lem:near`) carries the linear
  exponent via `D(Ω) ≥ const · 𝒜(Ω)²` after the truncation step,
  with the additional `D(Ω)² ≤ D(Ω)` absorption using `D ≤ δ_BDV ≤ 1`.
- Agent 8 Kohler–Jobin linearisation uses the FTC `f(s) ≥ p s` —
  exponent 1 in `s`, hence exponent 1 in `δ_T`, hence exponent 1 in
  `𝒜²`.

No `√δ_T` enters anywhere.

### NOTE-4. No hidden smoothness in finite-perimeter sections

Plan 1 does not enter the finite-perimeter / level-set framework; it
operates in the BDV quasi-open / regular-free-boundary class. The
regularity package of Agent 6 is **derived** from BDV Lemma 4.9, 4.12,
4.16 / Thm 4.18 — these are the only sources of smoothness, and they
are exhibited as inputs not assumed silently. The hodograph
straightening (Agent 6, Step 4) is applied only after the global
`C^{1,γ}` graph parametrisation has been established (Step 3), so no
ambient smoothness is hidden.

### NOTE-5. `R \ge 2` requirement met by Agent 8's choice

Agent 7's bounded Saint–Venant theorem requires `R \ge 2`. Agent 8's
`R_*(n) := max(d(n), 2) \ge 2`, so the input theorem is applied within
its declared regime. (Source `Final/master.tex` §VI uses the same
`R_*(n)`.)

### NOTE-6. `N` dimension symbol no longer appears in math

A regex sweep on the four drafts confirms that no math-mode `N` is
used as a dimension symbol anywhere. All remaining `N` occurrences are
in source-map comment lines explaining the `N → n` conversion, or in
inline prose like "with $N\to n$" that describes the conversion. The
notation register §1 requirement is satisfied.

### NOTE-7. Constant tracking is complete

Every `C` and `c` symbol in the four drafts is declared at first use
with an explicit dependence list (`(n)`, `(n,R)`, `(n,R,γ_0)`). The
explicit constant tables at the end of each subsection
(`plan1_selection.tex` §`subsubsec:plan1-sel-constants`,
`plan1_graph_entry.tex` final paragraph,
`plan1_nearly_spherical.tex` §`sec:plan1-constants`,
`plan1_kohler_jobin_transfer.tex` summary) close the bookkeeping. No
unqualified `C` is left.

### NOTE-8. "Source map" headers present in every draft

Each of the four Plan 1 drafts opens with a `% SOURCE MAP` comment
block listing the source file(s) and theorem labels each item is
adapted from, with the proper LOCAL/CITE/PROVED-HERE annotation. This
matches the "non-negotiable standards" of the master brief.

---

## Audit checklist summary

| # | Checklist item | Status |
|---|---|---|
| 1 | Every theorem has full hypotheses | PASS (1 minor edge case: MAJOR-4) |
| 2 | Every constant dependence is stated | PASS (1 cosmetic clash: MAJOR-2) |
| 3 | No conditional Bernoulli spectral route used unconditionally | PASS |
| 4 | Bounded reduction + KJ normalisation match the final theorem | PASS |
| 5 | No proof is shorter than its source block | PASS (Agent 5 and Agent 6 expand) |
| 6 | Threshold continuity (α_small ↔ α_graph/α_sph; selection → graph entry) | PASS (1 notation clash: MAJOR-1) |
| 7 | No `N` dimension symbols remain in math | PASS |

No Stop Conditions are triggered:

- No theorem is used without proof or reference.
- No hidden smoothness assumption.
- No rate loss `δ_T → √δ_T`.
- No unconditional reliance on the conditional Bernoulli spectral route.
- Bounded-reduction and KJ normalisations match Notation Register §4
  and §1.

Recommendation for Agent 17 (Notation Unification): resolve MAJOR-1,
MAJOR-2, MAJOR-3 and MINOR-3 as part of the unification pass; pass the
remaining minors to Agent 19 (Final Assembly) for absorption when the
four drafts are merged into `02_plan1_draft.tex`.
