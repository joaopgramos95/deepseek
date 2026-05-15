# Audit of `BRANDOLINI_GRAPH_ENTRY_ROUTE.md`

Cross-checked against:

- `Plan 3/brandolini.pdf` (Brandolini–Nitsch–Salani–Trombetti, JDE 245
  (2008), 1566–1583), Theorem 2 and surrounding Lemmas 8, 10,
  Corollary 9.
- `Plan 2/level-set-deficit-identity.md` (definitions of `D_H`, `D_I`,
  the weighted variance identity §6).
- `Plan 3/agent1-outer-collar-good-level.md` (Prop. 3.1).
- `Plan 3/agent2-graph-entry.md` (statement of what is missing).
- `Plan 3/agent3-graph-cohesion.md` (Thm 5.1, hypothesis (G0)).
- `Plan 3/agent4-one-level-extraction.md` (extraction theorem).
- `Plan 3/agent5-serrin-survey.md` (Serrin survey).
- `Plan 3/agent7-obstruction-report.md` (obstruction report).
- `Final/NearlySphericalClosure.tex` (Theorem `thm:NS`).

The pagination convention below refers to the route document.

---

## Showstoppers

### S1. Lemma 2.1 (§2.1) is FALSE as stated and the proof sketch does not work

The lemma claims: `S` connected, closed, `C^{1,γ}`, contained in an
annulus of width `ε`, with `S = ∂E`, `B_{R_in} ⊂ E ⊂ B_{R_out}`, implies
`S` is a radial graph over `∂B_1`.

**Counterexample in 2D.** Take the annulus `1−ε ≤ |x| ≤ 1`. Build a
closed curve which mostly traces the circle of radius `1`, but at one
angle dips inward to radius `1 − ε/2`, makes a small angular excursion
backward, and rejoins. Concretely, in polar coordinates parametrize a
closed C^∞ curve `t → (r(t), θ(t))` such that for `t ∈ [0,1]` the curve
loops around the origin (θ wraps once) but on a small interval
`t ∈ [t_1, t_2]`, the angular component `θ(t)` is not monotone — it
goes forward, retraces a small amount, and goes forward again, while
`r(t)` dips inside `[1−ε/2, 1]`. The resulting curve:

- is connected (homeomorphic to a circle),
- is C^∞,
- lies in the annulus,
- bounds an open `E` with `B_{1−ε} ⊂ E ⊂ B_1`,
- but is **not** a radial graph: rays through the fold cross 3 times.

The proof sketch's key sentence

> "If [the ray] crossed more than once, there would be two values
> r_1 < r_2 ..."

rules out 2 crossings, but a ray must cross an odd number of times, so
the real exclusion is 3, 5, 7, .... The argument "the radial
parametrisation flips orientation at any tangent-to-radial point" is
not an exclusion: tangent-to-radial points are exactly the fold turning
points, which **do** occur in the counterexample.

**What's actually true.** To rule out folds in a thin annulus one
needs a quantitative C^{1,γ} bound that is small *compared to the
annulus width*. Specifically: a fold of radial depth `h` inside a
curve of C^{1,γ}-seminorm `M` has angular extent at least
`c(M, γ) h^{1/γ}`. To exclude such a fold in an annulus of width `ε`
one needs `ε^{1/γ} M < c` — i.e., `ε ≤ ε_0(M, γ, n)`, with `ε_0` going
to zero as `M` grows.

**Consequence.** Lemma 2.1 must be re-stated as

> **Lemma 2.1′ (quantitative).** Fix `M, γ`. There exists
> `ε_0 = ε_0(M, γ, n) > 0` such that, if additionally
> `‖S‖_{C^{1,γ}} ≤ M` (in a translation/rotation-invariant intrinsic
> sense) and `ε ≤ ε_0`, then `S` is a radial graph.

Whether the route as a whole survives depends on whether the
C^{1,γ}-norm bound on `∂E_t̂` (after rescaling) is small enough at the
**same δ-scale** where Brandolini's `R_out − R_in ≤ Cδ^μ` is small.
The route document never even mentions this threshold.

For Brandolini's `Cδ^μ` to be small relative to `ε_0(M, γ, n)`, the
constants must be compared: `M` (the C^{1,γ}-norm of `∂E_t̂` after
rescaling) depends on `(n, R, ρ_*)` (Schauder), and is therefore not a
function of `δ`. So for **δ small enough**, `Cδ^μ ≤ ε_0(M, γ, n)`, and
the qualitative lemma can be salvaged.

**Verdict.** The route is recoverable, but Lemma 2.1's proof sketch
must be rewritten with an explicit quantitative version, and §8's claim
that "the only step requiring new mathematics is Lemma 2.1" is correct
only in the sense that this is the substantive piece that needs care.
It is **not** elementary in the way the document suggests.

---

### S2. The route silently uses Brandolini's Lemma 8 in addition to Theorem 2

Brandolini's proof of Theorem 2 is **not** "Theorem 2 = Theorem 1 +
C^{2,α} regularity". The actual proof of Theorem 2 uses

- **Lemma 8** of `brandolini.pdf` (p. 1579): under the C^{2,α} +
  `||Du|−1| ≤ δ` hypothesis, **`Ω_ε = {u < −ε}` is connected for
  `ε < ε_0(n, α, K, ρ_0)`**, with `K, ρ_0` the C^{2,α} parametrization
  constants of `∂Ω` (Remark 7).

- **Lemma 10** (p. 1580): a perimeter-side bound on tentacles.

- **Corollary 9**: combines Theorem 1 with Lemma 8 + Schauder estimates.

The route document writes "C = C(n, diam Ω, [∂Ω]_{C^{2,α}})", but
Brandolini actually states `C = C(n, d, α)` with `d = diam Ω` and "the
regularity of Ω", which in Remark 7 is unpacked into a *pair* `(K, ρ_0)`
controlling the local C^{2,α} parametrization. The single seminorm
`[∂Ω]_{C^{2,α}}` is not a complete description of the dependence — one
also needs a local **scale** `ρ_0` over which charts exist. In
rescaled coordinates (after unit-volume rescaling) the chart radius
`ρ_0` changes; this dependence must be tracked.

The route's §4 (R) discussion claims uniform C^{2,α} after rescaling is
"not an obstruction in the fixed-collar regime". This is partially
correct, but it overlooks the `ρ_0` (chart radius) part of the
regularity dependence, which scales as the volume rescaling factor.
Since on the fixed annulus `[ρ_*, 1]` the rescaling factor is bounded
above and below, `ρ_0` and `K` are both bounded — but the document
should say so explicitly.

---

## Serious

### G1. Connectedness of `∂E_{t̂}` is NOT a clean side condition (§4 (C))

Brandolini Theorem 2 requires `Ω` **connected**. The document
acknowledges this and proposes (§4 (C)) to apply Theorem 1 (which
allows multiple balls) and argue "only one component carries
non-negligible volume".

Two issues:

1. **The reduction is genuinely non-trivial.** "Multi-component
   Brandolini outputs a finite union of balls (Theorem 1, eqs (5)–(7))"
   — but Theorem 1 of `brandolini.pdf` requires the **two-sided** bound
   `||Du|−1| ≤ δ` in `L^∞(∂Ω)` and the additional `L^1` hypothesis
   `‖|Du|−1‖_{L^1(∂Ω)} ≤ δ|∂Ω|`. The latter follows from the L^∞
   bound by integration, but it is *not* a free statement — and the
   conclusion of Theorem 1 is in terms of asymmetry, not graph entry.

2. **The "tentacles" example (Figs 1–2 of brandolini.pdf) is the
   sharp obstruction.** The unit ball with an arbitrarily long thin
   tentacle has small `‖|Du|−1‖_{L^∞}` on `∂Ω`, is connected, has
   small `D_I` (the tentacle contributes O(thin radius)^{n−1} to
   perimeter, negligible), and has small `D_H` (similar). Brandolini's
   Theorem 2 still works for this `Ω` because the tentacle is part of
   the connected `Ω`, but the constant `C` blows up with `diam Ω`. The
   route's §4 (R) claim "uniform C^{2,α} after rescaling" implicitly
   assumes `diam Ω` is bounded after rescaling to unit volume; a long
   thin tentacle violates that. **This must be ruled out by a separate
   diameter bound** — typically from a bounded-reduction argument
   (`Final/BoundedReduction.tex`), but the document does not cite it.

3. **`D_I` only rules out comparable-volume extra components.** The
   route's verification of the "two balls of total volume |B_1|" gives
   `D_I = n²ω_n²(2^{2/n}−1) > 0` — correct. But a configuration with
   one big component (volume `ω_n(1−ε)`) plus tiny tentacles of total
   volume `ε ω_n` has `D_I` of order `ε^{(n−1)/n}` or similar (small),
   so small `D_I` does NOT rule out tentacles.

   The document's wording "only one component carries non-negligible
   volume" is honest about this, but does not finish the argument: even
   after isolating the main component, the **C^{2,α} regularity
   hypothesis of Brandolini applies to the whole `∂Ω`, including the
   tentacle**, with constants depending on the tentacle's geometry.

**Bottom line.** (C) is not "clean". It requires (i) bounded
diameter, (ii) ruling out non-negligible extra components, and
(iii) ensuring the C^{2,α} regularity holds **uniformly on the whole
boundary** — including any small extras. (iii) is the tightest.

### G2. The L²→L^∞ interpolation exponent in §1.3 is wrong

The document claims

\[ \kappa = \frac{\alpha}{2(n-1+\alpha)}. \]

The standard interpolation on an `(n−1)`-dimensional surface, with
`‖f‖_{L²}² ≤ A²` and `[f]_{C^α} ≤ M`, gives

\[ \|f\|_{L^\infty} \le C\, A^{2\alpha/(2\alpha + n-1)}\,
   M^{(n-1)/(2\alpha + n-1)}. \]

So with `A² ≤ C D_H`, the correct exponent is

\[ \boxed{\kappa = \frac{\alpha}{2\alpha + n-1}}, \]

not `α/(2(n−1+α)) = α/(2α + 2(n−1))`. The document has a spurious
factor of 2 in front of `(n−1)`. The exponent is still positive and
< 1/2 (for α ≤ 1, n ≥ 2), so qualitatively the chain still runs, but
the explicit constant in to-do item §7.3 is wrong.

### G3. The §1.3 C^α bound on `|∇u|` on `Σ_t` is asserted, not derived

The document writes

\[ [|\nabla u|]_{C^\alpha(\Sigma_t)} \le C \|u\|_{C^{2,\alpha}(\Sigma_t)}. \]

What is `‖u‖_{C^{2,α}(Σ_t)}`? This requires `Σ_t` itself to be at
least `C^{0,1}` to define a Hölder seminorm in an intrinsic way, and
`C^{2,α}` to bound `[|∇u|]_{C^α}` by `[D²u]_{L^∞} \cdot \mathrm{diam}` or
by `[D²u]_{C^α} \cdot \mathrm{diam}^α`. In any case, the regularity of
`Σ_t` is a *consequence* of `|∇u| > 0` at `Σ_t` (implicit function
theorem) plus interior `C^{2,α}` regularity of `u`. Since `−Δu = 1`
with smooth right-hand side, interior Schauder gives `u ∈ C^{3,α}_{loc}`
on `Ω`, so `D²u` is `C^α_{loc}`, hence `[|∇u|]_{C^α}` is finite on any
compact subset bounded away from critical points.

The required input is therefore:

- (i) `t̂` is a *regular* level (`|∇u| > 0` on `Σ_t̂`), so that `Σ_t̂` is
  a `C^{2,α}` hypersurface; and
- (ii) `Σ_t̂` is bounded away from `∂Ω` in the dilated geometry so
  that the Schauder constant is uniform.

(i) holds for a.e. `t` by Sard, but the document never invokes Sard or
discusses choosing `t̂` to be regular. Agent 1's good-level extraction
yields a positive-measure set of good `t`, but the document doesn't
clarify that *regularity* is also extracted (in fact a.e. `t` is
regular by Sard, so this is a free side condition).

(ii) is exactly the (R) hypothesis of §4 and is correctly identified
there, but should be referenced at §1.3.

### G4. The rescaling to unit volume is hand-waved; the constants are not tracked

The document moves between original `Ω`, `E_t`, and `E_t̂` rescaled to
unit volume without explicit scaling laws. Brandolini's hypothesis is
`||Dv|−1| ≤ δ` and `Δv = n`. With Plan 2 convention `−Δu = 1`, going
to a unit-volume copy of `E_t̂` requires:

- spatial rescaling `x → x/λ`, `λ = (|E_t̂|/ω_n)^{1/n}`;
- defining `v(x) = c · (u(λx) − t̂)`, choosing `c` so that `Δv = n`.

The chain of substitutions gives `c = −n λ²` (since `Δu = −1`, so
`Δ(u(λ·)) = −λ²`, and we want `Δv = n`). Then
`|Dv(x)| = c · λ · |∇u(λx)| = n λ³ |∇u(λx)|`.

On `∂E_t̂` (in `λ`-rescaled coordinates), the mean of `|∇u|` is
`m(t̂)/P(E_t̂) = ρ_t̂/n` where `ρ_t̂ = (m/ω_n)^{1/n}`. So
`mean |Dv| = n λ³ · ρ_t̂/n = λ³ ρ_t̂`. With `λ = ρ_t̂ ω_n^{1/n}/ω_n^{1/n}
= ρ_t̂/(something)` — the computation gets messy and the document
never does it.

After unit-volume rescaling, `λ → 1`, `ρ_t̂ → 1`, and the mean of
`|Dv|` is 1. The variance is rescaled by `λ^{2(n−1)+1} = λ^{2n−1}` (for
L² on (n−1)-surface). These are all bounded above/below by absolute
constants since `λ ∈ [c, C]` with constants depending on `ρ_*`.

**This is fine in principle**, but the document's three-line treatment
of rescaling — "After rescaling to unit volume on ∂B_1, the mean is
1 + O(√D_I)" — invites confusion. Constants should be displayed
explicitly, especially because Brandolini's constant `C` already
depends on `diam Ω̃` after rescaling.

### G5. §5 confuses `α(Ω̃)` with `α(Ω̃)²`

The document writes (§5):

> `α(E_t̂)² ≤ C δ_T(E_t̂)` follows from Cor 2.2 + closure.

But `Final/NearlySphericalClosure.tex` Theorem `thm:NS` (eq.
`NSalpha`) gives `E(Ω̃) − E(B_1) ≥ c_*(N) α(Ω̃)` — **linear** in α,
not α². The Fraenkel-asymmetry consequence (eq. `NSfraenkel`) is
`≥ c_*(N) |B_1|² C_1(N)^{-1} \mathcal A(Ω̃)²` — α² in `Asym`, not in
`α`.

So the correct chain is:

\[ \alpha(E_{\hat t}) \le C \delta_T(E_{\hat t})
   \quad\text{(linear from `thm:NS`)},
   \qquad
   \mathcal A(E_{\hat t})^2 \le C \alpha(E_{\hat t}) \le C \delta_T(E_{\hat t}).
\]

The document's "α²" is wrong on the LHS; it should be `Asym²` (Fraenkel
asymmetry squared). This is a notation slip — the document conflates
smooth asymmetry `α` and Fraenkel asymmetry `A` — but it matters
because the final inequality is stated in terms of Fraenkel asymmetry.

### G6. `thm:NS` requires `‖g‖_{C^{2,γ_0}}` small; the route only delivers `‖g‖_{C^{1,γ}}` small

`NearlySphericalClosure.tex` Theorem `thm:NS` hypothesis (eq.
`normal`):

\[ \|g\|_{C^{2,\gamma_0}(\partial B_1)} \le \delta_{\rm sph}(N, \gamma_0). \]

The Brandolini route's Cor 2.2 outputs `‖h‖_{C^{1,γ}}` bounded by
`C(n, R, ρ_*)` — **not small**, and only `C^{1,γ}`, not `C^{2,γ_0}`.

The route document acknowledges this implicitly by listing the
"C^{2,γ_0} regularity gap" in `Plan 3/agent4-one-level-extraction.md`
§"Regularity gap (flagged, not closed here)". The Brandolini route
**does not** close this gap. The interior Schauder bound gives
`u ∈ C^{3,α}_{loc}`, so `∂E_t̂` is `C^{3,α}` (one more derivative than
`u`). After rescaling, the rescaled boundary is `C^{3,α}` with norm
bounded by `C(n, R, ρ_*) · λ^{stuff}`. So **a posteriori** one can
upgrade to `C^{2,γ_0}` for any `γ_0 < α`, with a bound that does not go
to zero as `δ → 0`.

For `‖g‖_{C^{2,γ_0}}` to be *small* (as required by `δ_{sph}`), one
needs either (a) interpolation between an `L^∞` smallness of `g` and a
fixed `C^{2,γ_0}` bound; or (b) a separate small-deformation theorem.

The document's §5 implicitly assumes (a), but never executes it. This
is the same issue that has plagued Plan 1/Plan 2 throughout: the
qualitative-graph-entry → quantitative-closure step requires a
Schauder interpolation that costs a fractional power of `δ_T`, and the
"sharp" `Asym² ≤ Cδ_T` is recovered only if the loss balances. The
document's claim "qualitative graph entry suffices" is correct **only
modulo this interpolation argument, which it does not perform**.

In particular, the `Final/SchauderInterpolation.tex` (or its
counterpart) is the load-bearing block here, and the document should
cite it explicitly.

---

## Minor

### M1. PDE sign convention

The document writes `Δu = 1` in §1.1, but Plan 2 convention is
`−Δu = 1`. This is consistent with Brandolini's `Δu = n` only if the
document's `u` is `−n` times the Plan 2 `u`. The integration-by-parts
identity `|E_t| = ∫_{∂*E_t} |∇u| dH^{n−1}` is unaffected (modulus
signs), but a careful write-up must reconcile signs throughout.

### M2. The doc misstates Brandolini's `C` dependence

The doc writes `C = C(n, diam Ω, [∂Ω]_{C^{2,α}})`. Brandolini's
statement is `C = C(n, d, α)` where `d = diam Ω` "and the regularity
of Ω" (p. 1568). Remark 7 (p. 1579) clarifies that this means the
pair `(K, ρ_0)` from the local-chart definition of `C^{2,α}`. The
document's notation `[∂Ω]_{C^{2,α}}` is non-standard and conflates the
chart norm with a global seminorm.

### M3. Lemma 2.1 statement: `B_{R_in}(x_*) ⊂ E ⊂ B_{R_out}(x_*)` is a hypothesis, not a free Brandolini output

Brandolini Theorem 2 outputs `R_out − R_in ≤ Cδ^μ` and
`|1 − R_in|, |1 − R_out| ≤ Cδ^μ`. The statement does NOT explicitly
guarantee an `x_*` such that `B_{R_in}(x_*) ⊂ Ω ⊂ B_{R_out}(x_*)`. It
does (by Corollary 9 + Lemma 10, p. 1580) produce two concentric balls
`B_R ⊂ Ω` and `Ω ⊂ B_{\bar R}` (with `\bar R = R_out` in the
notation). So both balls have the **same** center, which is the center
of the inscribed ball `B_R`.

This is what Lemma 2.1 needs (concentric annulus) and the proof of
Brandolini Theorem 2 does deliver it. But the doc should cite the
correct source (Cor 9 + Lemma 10) rather than just "Theorem 2".

### M4. The doc's §3 table entry for Agent 4 is misleading

Agent 4 takes as input (A2)+(A3). (A2) is "outer-collar graph entry on
ρ ∈ [ρ_*,1] with `‖h(ρ)‖_{C^{1,γ_*}}/ρ ≤ ε_0`". The Brandolini route
delivers graph entry **at a single level `t̂`**, not on the whole
collar `[ρ_*, 1]`. Agent 3 then extends from one level to the whole
collar (Thm 5.1).

So the correct logical chain is:

Brandolini + Lemma 2.1 → graph entry at one level (Cor 2.2)
→ Agent 3 (cohesion) → graph entry on `[ρ_*, 1]`
→ Agent 4 (extraction).

The route document's table conflates "graph entry at one level" with
the input to Agent 4. The document is correct that the chain runs,
but the dependence on Agent 3 is essential and the (G0) condition of
Agent 3 (`C^{1,γ}` graph + small `L^∞` + first-mode-neutralised)
matches Cor 2.2's output **only after first-mode neutralisation**.
First-mode neutralisation is a choice of barycenter, easy to perform,
but the document does not mention it.

### M5. Agent 5's verdict is misstated

The doc's §6 says Agent 5 "asked for a Serrin-stability theorem
outputting graph entry. None exists directly." But Agent 5's row 2
explicitly evaluated Brandolini–Nitsch–Salani–Trombetti and rejected
it because it (mis)read the hypotheses as requiring **convex** `D`.
Brandolini Theorem 2 does **not** require convexity — only `C^{2,α}`
and connectedness. So Agent 5 misread the paper.

The route document is right that Agent 5 missed the Brandolini route,
but for the wrong reason: it was a misreading, not a structural
"single-theorem packaging" issue.

### M6. Agent 7's verdict requires explicit comparison

The doc's §6 says "(G2) and the Brandolini route are alternative
bottlenecks." Agent 7 lists (G2) (the ρ-Fubini profile-gap conversion
with moving centroid) as the cheapest missing input. The Brandolini
route bypasses (G2) entirely and replaces it with hypothesis (R)
(uniform `C^{2,α}` regularity). Which is cheaper depends on whether
one already has Plan 2's Wave 3 G machinery (in which case (G2) is one
lemma away) vs. the Brandolini machinery (in which case Lemma 2.1' + a
connectedness reduction are needed). The doc's "both should be
pursued" is reasonable, but the comparison is not really fair: (G2) is
known to be one identity-manipulation away, whereas Lemma 2.1' needs
nontrivial geometric work (see S1).

---

## Cosmetic

- **C1.** §1.1: "After rescaling to unit volume on `∂B_1`, the mean
  is `1 + O(√D_I)`" — the constant in `O(√D_I)` depends on `n` and on
  the rescaling factor. Spell out.
- **C2.** §1.2: the identity in `Plan 2/level-set-deficit-identity.md`
  §6 is stated on `Σ_t`, not `∂*E_t`. For regular `t` these agree;
  the doc's "∂*E_t" notation is acceptable but inconsistent with the
  source.
- **C3.** §1.2 cites the source as `Plan 2/level-set-deficit-identity.md`
  §6 — verified, the identity is correct (boxed identity on line 379 of
  that file).
- **C4.** §2 "Apply Theorem 2 to E_t̂ rescaled to unit volume" — but
  Theorem 2's hypothesis is `Δu = n` and `||Du|−1| ≤ δ`. The
  rescaling that turns Plan 2's `−Δu = 1` into `Δv = n` is sign-flip +
  scaling; spelled out, the rescaled gradient is `n λ³ |∇u|` where
  `λ` is the spatial rescaling factor. This should be made explicit
  to avoid hidden constants.
- **C5.** §2.1, lemma statement: "`h: ∂B_1 → ℝ`" — should be
  `h ∈ C^{1,γ}(∂B_1)` to match the conclusion. Trivial.
- **C6.** Brandolini's explicit exponent is
  `μ = 1/(2(4n+9)(n−1))` (p. 1581-2 of `brandolini.pdf`, end of proof
  of Theorem 2). The doc writes `μ = μ(n) > 0` only; explicit value
  is available and should be quoted if the route is to be self-
  contained.
- **C7.** "First-mode-neutralised" (used in Agent 3's (G0)) is
  not mentioned in Cor 2.2. The radial-graph center `x_*` from
  Brandolini is the inscribed-ball center, **not** the barycenter.
  These differ by `O(δ^μ)` and a barycenter shift is required to feed
  (G0). Trivial but should be noted.
- **C8.** §4 (M): "Volume preservation in interpolation. ...Standard,
  but constants need to be tracked." Nothing is actually lurking here
  beyond what (G2)–(G4) flagged above. Title is misleading: this isn't
  about volume *preservation* but about the L²–C^α interpolation
  constants.

---

## Verdict

**The route is plausibly sound but is not "modulo write-up".**

Brandolini's Theorem 2 is correctly identified as the key external
input, and the high-level architecture (annular squeeze + graph
extraction → Agent 3 cohesion → Agent 4 extraction → NS-closure) is
correct. However:

- **Lemma 2.1, the only piece of "new mathematics" claimed, has a
  false proof sketch and is in fact a non-trivial quantitative
  geometric statement (S1).** A correct version requires comparing
  the annulus width `Cδ^μ` against an `ε_0(M, γ, n)` threshold coming
  from the C^{1,γ} regularity of `∂E_t̂` after rescaling. The
  comparison can be done — interior Schauder bounds `M` by
  `C(n, R, ρ_*)`, and for `δ` small enough one wins — but this is
  geometric work, not a "fold of size h forces R_out − R_in ≥ h"
  one-liner.

- **The connectedness reduction (G1) is genuinely non-trivial.** The
  tentacle example shows `D_I` alone does not suffice to rule out
  problematic geometries. The reduction relies on bounded-diameter
  hypotheses imported from elsewhere (BoundedReduction.tex), and
  on Brandolini Theorem 1 for multi-component squeeze, neither of
  which is cited in the route document.

- **The L²→L^∞ interpolation exponent is wrong (G2)**, the sign
  convention is sloppy (M1), the rescaling is hand-waved (G4), and
  the final-step Schauder interpolation to upgrade `C^{1,γ}` to
  small `C^{2,γ_0}` (required by `thm:NS`) is not addressed (G6).

In sum: the chain is **structurally plausible**, but the document
substantially under-estimates the work required to discharge Lemma 2.1
and hypothesis (C). The route is not "modulo write-up". To make it
genuinely sound, three pieces of mathematical work need to be done:

1. A quantitative Lemma 2.1' (annulus + bounded C^{1,γ} + small-enough
   ε ⇒ radial graph), with explicit `ε_0(M, γ, n)`.
2. A connectedness reduction (C-clean) that uses bounded diameter
   (from BoundedReduction) + Brandolini Theorem 1 multi-ball output +
   `D_I` smallness, ruling out *non-negligible* extra components, and
   handling small tentacles via perimeter control.
3. The C^{1,γ} → C^{2,γ_0} interpolation step closing the gap to
   `thm:NS`.

These are doable but not "write-up". They are **two to three lemmas
worth of new work**, comparable in difficulty (and conceptually
adjacent to) Plan 2's (G2). The doc's claim in §8 that "the only
step requiring new mathematics is Lemma 2.1 plus the one-component
reduction" is correct in spirit but understates both.
