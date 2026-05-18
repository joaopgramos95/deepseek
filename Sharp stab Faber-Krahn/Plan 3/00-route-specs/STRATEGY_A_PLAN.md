# Strategy A — the natural plan (user's formulation)

Authoritative record of the plan the user laid out (2026-05-15) for the
graph route. Faithful to the user's own words; this anchors the
independent exploration agents. Setup: `−Δu=1` in `Ω`, `u=0` on
`∂Ω`; `δ_T` Saint–Venant deficit; `Asym` Fraenkel asymmetry; goal
`Asym(Ω)² ≤ C(n) δ_T(Ω)`. "Local result" = sharp stability for domains
whose boundary is a graph over a sphere.

Caveat the user states up front: it is not known whether Plan 1 truly
works; this plan is the one the user considers most natural, possibly
sharing machinery with Plan 1.

## Step 1 — quantified boundary regularity by penalised replacement

Use BDV-style machinery (replace the set by an extremal of a penalised
functional) **as a regularisation device only**: produce a competitor
whose boundary is smooth with *explicit, quantified* bounds on the
derivatives of the parametrising functions. Ideally: `∂` of the
competitor is `C^k` with named constants. The competitor must keep the
deficit `O(δ_T)` and asymmetry comparable.

## Step 2 — a good level `O(δ_T)` inside, and the smallness problem

Find a good level `O(δ_T)` inside (the level-set extraction). From the
sketches this level can likely be made a *smooth graph*. Problem: the
graph's norm need not be small. Two ways to counter this:

- **(i) Monotonicity.** Show that *any* graph domain satisfies the
  sharp stability estimate, by some kind of monotonicity — not
  requiring the graph norm to be small. (Untried; the user considers it
  a viable route.)
- **(ii) Regularity bootstrap.** If only the `H^{1/2}` norm of the
  graph is small, use the quantitative smoothness from Step 1 to
  *propagate* the smallness to a higher norm (the norm BDV-type
  nearly-spherical closure actually needs).

## The self-quantification + propagation idea (the user's favoured one)

This is the variant the user finds most natural and most clearly
Serrin-connected:

- Assume the boundary is smooth. This is *legitimate*: by passing to
  the inside of the domain one can always assume it, while keeping the
  deficit `O(δ_T)`.
- Use the **condition itself** to quantify the smoothness. By the
  near-Serrin `L²` smallness of `|∇u|−`const together with
  Chebyshev/Markov, most of `|∇u|` is close to a constant in `L¹`.
  There should therefore be a way to show that the *overwhelming part*
  of the boundary has controlled norm — not merely that the set is
  close to a ball, but that the smoothness of the boundary is
  controlled in *most places*.
- Then, by going again `O(δ_T)` inside in terms of level sets (to
  `{u>t}`, `t≥Cδ_T`, `C` large), the smoothness *propagates to the
  whole boundary* by **interior elliptic regularity (Poisson-kernel
  smoothing)** — NOT dispersion: solving the elliptic equation averages
  a boundary irregularity away once one steps a definite distance
  inside. **Premise (essential):** the domain is already smooth with
  controlled geometry in the Part A sense; then global up-to-boundary
  Schauder is `δ_T`-uniform (no interior-distance blow-up), so a small
  bad set on a level is smoothed out on a slightly deeper level, and
  pointwise `|∇u|≈c` + controlled geometry bootstraps higher
  derivatives. The real crux is therefore whether Part A/B delivers
  that `δ_T`-uniform smooth boundary, not the smoothing itself.
- Outcome: going into the domain makes it a graph, and bootstrapping
  makes the graph small in (say) `C³` norm.

## Step 3 — transfer

By construction the new set's deficit is `O(δ_T)`, and the new set
differs from the original by at most `O(δ_T)`. The local result (sharp
stability for graph domains) then closes everything.

## Why Plan 3 at all, if Plan 1 exists

The user's honest answer: unknown, but possibly there is a clean way.
The point of the self-quantification idea is precisely that it makes
Plan 3 — and the Serrin connection — *evident*: the near-Serrin
condition is used to quantify the boundary regularity from within,
rather than importing it from a selection principle.

## The independent investigations (one per part)

- **Part B (Step 1).** Does penalised-selection-as-regulariser deliver
  a competitor with quantified smooth boundary (explicit derivative
  bounds) at `O(δ_T)` deficit cost and comparable asymmetry?
- **Part C (counter (i)).** Can the sharp estimate be proved for *any*
  graph domain (bounded norm, not small) via monotonicity?
- **Part D (counter (ii)).** Given quantified boundary smoothness,
  propagate `H^{1/2}`-smallness of the graph to small higher norm.
- **Part E (self-quantify + propagate).** Near-Serrin `L²` + Markov ⇒
  overwhelming part of the boundary has controlled norm; going
  `O(δ_T)` inside propagates it to the whole boundary
  (dispersive-style); bootstrap to small `C³`.

Each is explored independently and meticulously; honest negative
results (precise obstruction) are as valuable as a proof.
