# Notation and Normalization Unification Report

**Agent 17 deliverable.** Date: 2026-05-13. Scope: all thirteen section
drafts under `Manuscript/`. Patch policy: conservative — only changes
required by the canonical Notation Register
(`Manuscript/00_notation_register.md`) or to resolve the MAJOR
findings of `Manuscript/audit_plan1.md` /
`Manuscript/audit_plan2.md` (the latter via the
`audit_plan2_repair_report.md` already incorporated upstream). No proof
is rewritten. Each edited draft has a top-of-file
`% UNIFIED 2026-05-13` comment.

The macro preamble has been collected into a single file
`Manuscript/macros.tex` (canonical macros only, taken verbatim from
the register §15) so that Agent 19's `main.tex` can `\input` it.

---

## 1. Inventory of conflicts found

### 1.1 Dimension symbol

| Conflict | Files affected | Canonical choice | Action |
|---|---|---|---|
| `N` vs `n` for ambient dimension | Plan 1 drafts inherited `N` from `Final/`. | `n` (register §1). | Verified all Plan 1 drafts already replaced math-mode `N` by `n` (audit NOTE-6); only narrative comments retain `N` in the form "$N\to n$". No additional math edits needed. |

### 1.2 Ball notation

No conflict. All drafts use `B_r(z)`, `B_1`, `B^*` (`\Bstar`) per
register §2. The bounded-reduction radius `R_*(n)` (register §1) is
consistently used in Plan 1 Agent 8 and Plan 2 Agent 13.

### 1.3 Torsion energy sign convention

Canonical: `E(Ω) = −T(Ω)/2`, `E(Ω) ≤ 0`, `δ_T(Ω) = E(Ω) − E(B^*) ≥ 0`
(register §3). All thirteen drafts already use this convention
(preliminaries_torsion.tex Agent 3 enforced it at the source). The
remark in `plan2_boundary_layer_assembly.tex` near line 562
explicitly tracks `δ_SV = 2 δ_T` so that the Kohler-Jobin two-case
branch absorbs the factor 2 — this is correct and consistent.

### 1.4 Saint–Venant deficit notation

Canonical `δ_T = E(Ω) − E(B^*)` (register §3, macro `\deltaT`). No
draft uses `δ_SV` for the canonical quantity. The symbol `δ_SV` appears
only as `δ_SV := T(B^*) − T(Ω) = 2 δ_T` inside the Kohler-Jobin
two-case proof in `plan2_boundary_layer_assembly.tex`; this is the only
permitted local appearance and is correct as documented in the proof.

### 1.5 Faber–Krahn deficit notation

Canonical `δ_FK(Ω) = (|Ω|/ω_n)^{2/n} (λ_1(Ω) − λ_1(B^*))` (register §4,
macro `\deltaFK`). One discrepancy fixed:

- `Manuscript/plan2_boundary_layer_assembly.tex`, Theorem
  `thm:plan2-FK` (≈ line 578): formula was written
  `(|Ω|/|B_1|)^{2/n}(λ_1(Ω)−λ_1(B^*))`. Rewritten as
  `δ_FK(Ω) = (|Ω|/ω_n)^{2/n}(λ_1(Ω)−λ_1(B^*))` to match the
  Plan 1 Agent 8 final theorem `thm:KJ-FK-lower` verbatim.

### 1.6 Fraenkel asymmetry notation

Canonical: `\Fr := \mathcal{A}` (register §5, macro `\Fr`). Some drafts
wrote `\mathcal{A}` directly; converted to `\Fr` for uniformity in
these files:

- `Manuscript/preliminaries_quant_isoperimetry.tex` (15 occurrences).
- `Manuscript/plan2_levelset_identity.tex` (7 occurrences).
- `Manuscript/plan2_fj_center_radial_trace.tex` (2 occurrences).

(The macro expands to `\mathcal{A}`, so the change is purely cosmetic;
it removes the surface inconsistency flagged in the audit.)

### 1.7 Plan 1 BDV smooth asymmetry symbol

Canonical: `\BDValpha := \alpha_{\mathrm{BDV}}` (register §5). All four
Plan 1 drafts use this. The minor cosmetic drift `c_*^{NS}(n)` vs
`c_*(n)` (audit MINOR-1) is not load-bearing: the register §14 allows
the bare `c_*(n)` in Plan-1-only paragraphs, so no edit is needed here.

### 1.8 Foliation radii (§12)

Canonical: `\rstar`, `\rhodelta`, `\rhad` (= ρ̂). All Plan 2 drafts use
these. The post-repair window
`ρ̂ ∈ [ρ_δ − c_0 √δ_T, ρ_δ]` (Agent 12, Agent 13) matches register §12
after the audit B1 repair (already done in
`audit_plan2_repair_report.md`); no further edit.

### 1.9 Metric quotient §11

Canonical: `\X`, `\dX`, `\Frho`, `\Erho`. All Plan 2 drafts use these.
No conflict.

### 1.10 Constants (§14)

Canonical: every `C`, `c` appears with declared dependence. All
remaining issues from the audits:

- **MAJOR-1 (audit_plan1)**, `α_small` clash between Agent 6 and
  Agent 7. Fixed by renaming Agent 6's intermediate threshold to
  `α_small^{graph}(n,R,γ_0)`, leaving `α_small(n,R)` reserved for
  Agent 7's stronger Saint-Venant-closure threshold.
  - File: `Manuscript/plan1_graph_entry.tex`, lines ≈ 737–738 and
    ≈ 760–761 (post-renaming `α_{\rm small}^{\rm graph}` in two
    places).
- **MAJOR-2 (audit_plan1)**, `C_2(n,R)` vs `C_2(R)`. Fixed by
  globally replacing `C_2(n,R)` → `C_2(R)` in
  `Manuscript/plan1_nearly_spherical.tex` (5 in-text occurrences +
  constants-table entry on line 627 corrected to `R`-only dependence).
- **MAJOR-3 (audit_plan1)**, quasi-open / open / bounded-open
  domain-class drift. Fixed by inserting a domain-class
  reconciliation parenthetical at the start of
  `Manuscript/plan1_nearly_spherical.tex` §
  `sec:plan1-nearly-spherical` (post-standing-hypotheses paragraph),
  stating that the BDV quasi-open class of Agent 5 and the canonical
  open class of register §2 coincide for `δ_T, Fr, α_BDV, λ_1`.
- **MAJOR-4 (audit_plan1)**, `λ_1(Ω) = ∞` edge case. Fixed by
  prepending a one-line case split to the proof of
  `thm:KJ-FK-upper` in `Manuscript/plan1_kohler_jobin_transfer.tex`:
  if `λ_1(Ω) = +∞` then `δ_FK(Ω) = +∞` and the inequality is
  trivial; otherwise `λ_1(Ω) < ∞` and `Lem:KJ-ptwise` applies.

The Plan 2 BLOCKING and MAJOR findings (audit_plan2 B1, M1, M2) were
already resolved upstream in `audit_plan2_repair_report.md`; Agent 17
reconfirms that the resulting drafts (`plan2_weighted_metric_trace.tex`,
`plan2_boundary_layer_assembly.tex`) use `κ = κ(n,R,ρ_*)` canonical
and `C_*(n,R,ρ_*)` without residual `κ`-dependence.

### 1.11 Macros

No draft defines its own `\newcommand` or `\DeclareMathOperator`. All
drafts use the macros of register §15 directly. The macro preamble has
been written verbatim to `Manuscript/macros.tex` for Agent 19's use.

---

## 2. Per-file edit count

| File | Edits | Type |
|---|---:|---|
| `plan1_graph_entry.tex` | 3 | Header + α_small^graph rename ×2 |
| `plan1_kohler_jobin_transfer.tex` | 2 | Header + λ_1=∞ case split |
| `plan1_nearly_spherical.tex` | 8 | Header + C_2 rename ×6 + constants-table dep + domain-class paragraph |
| `plan1_selection.tex` | 1 | Header only (already conformant) |
| `plan2_aux_centroid_note.tex` | 1 | Header only (already conformant) |
| `plan2_boundary_layer_assembly.tex` | 2 | Header + ω_n/B_1 unification in final theorem |
| `plan2_fj_center_radial_trace.tex` | 3 | Header + \Fr unification ×2 |
| `plan2_levelset_identity.tex` | 8 | Header + \Fr unification ×7 |
| `plan2_metric_framework.tex` | 1 | Header only (already conformant) |
| `plan2_weighted_metric_trace.tex` | 1 | Header only (post-repair already conformant) |
| `preliminaries_gmt.tex` | 1 | Header only (already conformant) |
| `preliminaries_quant_isoperimetry.tex` | 16 | Header + \Fr unification ×15 |
| `preliminaries_torsion.tex` | 1 | Header only (already conformant) |

New file:
- `Manuscript/macros.tex` (canonical TeX preamble, ~25 lines).

---

## 3. Register entries that required Agent 17 extension

The register §15 macro list is reproduced verbatim in `macros.tex`. No
new macros were introduced. Two notation choices were borderline
under-specified in the register; Agent 17 records the chosen extension
here:

1. **`α_small` (Plan 1)**. The register §14 mentions thresholds in
   general but does not give a specific entry for Plan 1's
   `α_small`. The audit MAJOR-1 flags a clash between Agent 6 and
   Agent 7. Agent 17's canonical extension: `α_small(n,R)` is the
   Agent 7 threshold (the stronger one, used in the bounded
   Saint–Venant chain); Agent 6's intermediate threshold is renamed
   `α_small^{graph}(n,R,γ_0)`. Both definitions remain explicit in
   their own subsections.
2. **Form of the final Faber–Krahn statement**. Register §4 fixes
   `δ_FK` but does not commit to "upper" vs "lower" form for the
   stated theorem. Agent 17 keeps both: Plan 1's
   Theorem `thm:KJ-FK-lower` and Plan 2's `thm:plan2-FK` are the
   canonical lower-form statements
   `δ_FK(Ω) ≥ c_FK(n) Fr(Ω)^2`; Plan 1's `thm:KJ-FK-upper` is the
   equivalent upper-form rephrasing
   `Fr(Ω)^2 ≤ (1/c_FK(n)) δ_FK(Ω) = C_FK(n) δ_FK(Ω)`. The
   inverse-constant relation `C_FK = 1/c_FK` is stated in Plan 1
   Agent 8.

No other register entry required an Agent-17-side extension.

---

## 4. Confirmation: identical final theorems

Plan 1's canonical lower-form final theorem
(`Manuscript/plan1_kohler_jobin_transfer.tex`,
Theorem `thm:KJ-FK-lower`, ≈ line 526):

> Let `n ≥ 2`. There is a dimensional constant `c_FK(n) > 0` such
> that for every open `Ω ⊂ ℝⁿ` with `0 < |Ω| < ∞`,
> `δ_FK(Ω) = (|Ω|/ω_n)^{2/n}(λ_1(Ω) − λ_1(B^*)) ≥ c_FK(n) Fr(Ω)^2`,
> with `c_FK(n) := min{c_1(n), c_2(n)}` as in (eq:cFKdef).

Plan 2's final theorem (`Manuscript/plan2_boundary_layer_assembly.tex`,
Theorem `thm:plan2-FK`, ≈ line 573, post-unification):

> Let `n ≥ 2`. There exists a constant `c_FK(n) > 0`, depending only
> on `n`, given by the explicit formula (eq:plan2-cFKdef), such that
> for every open `Ω ⊂ ℝⁿ` with `0 < |Ω| < ∞`,
> `δ_FK(Ω) = (|Ω|/ω_n)^{2/n}(λ_1(Ω) − λ_1(B^*)) ≥ c_FK(n) Fr(Ω)^2`.
> The exponent `2` is sharp.

Both statements use:

- the same domain class ("open `Ω ⊂ ℝⁿ` with `0 < |Ω| < ∞`");
- the same canonical normalisation
  `δ_FK = (|Ω|/ω_n)^{2/n}(λ_1(Ω) − λ_1(B^*))`;
- the same constant name `c_FK(n)`;
- the same lower-form inequality `δ_FK ≥ c_FK Fr^2`.

The numerical value of `c_FK(n)` is in general different between the
two proofs, because each chain constructs its own
`c_SV^{glob}(n)` and feeds it into the same Kohler-Jobin transfer; both
explicit formulae (Plan 1 (eq:cFKdef), Plan 2 (eq:plan2-cFKdef))
expand to `min{4 n L_n c_SV^{glob}(n) / ω_n, L_n (2^{2/(n+2)}-1)/4}`
with the route-specific `c_SV^{glob}(n)`. Plan 1 Remark
`rem:plan2-match` and Plan 2 Remark `rem:plan2-vs-plan1-normalisation`
each explicitly record this match.

Plan 1 also provides the upper-form theorem `thm:KJ-FK-upper`
`Fr(Ω)^2 ≤ C_FK(n) δ_FK(Ω)` with `C_FK(n) = 1/c_FK(n)`, which is what
the master brief asks the manuscript to "culminate" in. Plan 2's
final theorem is the equivalent lower form; the master brief
indifferently calls either of these "the sharp quantitative
Faber-Krahn inequality".

**Conclusion.** The two final theorems are stated in identical notation
and identical normalisation; they differ only in the explicit numerical
constant `c_FK(n)`, which is allowed since each proof route gives an
independent (and explicit) constant.

---

## 5. Items deferred to Agent 19 (Final Assembly)

The following audit items are cosmetic / structural and are out of
scope for Agent 17's notation pass; Agent 19 should fold them into the
single assembled file:

- audit_plan1 **MINOR-1** (cosmetic drift `c_*^{NS}(n)` vs `c_*(n)`).
- audit_plan1 **MINOR-2** (cross-reference precision in the
  vol/barycentre normalisation paragraph).
- audit_plan1 **MINOR-3** (`δ_sph` definition collision between
  Agent 6 and Agent 7).
- audit_plan1 **MINOR-4** (vol/barycentre defects bookkeeping).
- audit_plan1 **MINOR-5** (redundant scale-removal in Agent 8).
- audit_plan1 **MINOR-6** (duplicate `thm:SV-bounded` vs
  `thm:plan1-SV` label after merging).
- audit_plan2 **m1, m2, m3, m4** (constant tightening, duplicate
  superlevel transfer lemma, `C_4` explicit form, `rmk:FJ-equiv`
  annotation).

These do not affect notation correctness; they affect proof bookkeeping
clarity and theorem-label cleanup, both of which are Agent 19's domain.

---

## 6. Stop conditions

None of the stop conditions of `MANUSCRIPT_ASSEMBLY_AGENTS.md` are
triggered:

- No theorem is used without proof or reference.
- No hidden smoothness assumption in a finite-perimeter section.
- No rate loss `δ_T → √δ_T` anywhere in the chain.
- No unconditional reliance on the conditional Bernoulli spectral
  route (audit_plan1 NOTE-1).
- No unconditional reliance on the centroid Π-route (audit_plan2 N1).
- The two final theorems are now stated in identical normalisation.

End of report.
