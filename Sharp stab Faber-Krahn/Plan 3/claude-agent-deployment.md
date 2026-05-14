# Claude Agent Deployment Brief: Plan 3 Outer-Collar Graph Entry Route

This brief is for deploying parallel Claude agents on the new hybrid route.
The goal is not to salvage the old bad-set metric-transport argument. The goal
is to use the level-set defects `D_H` and `D_I` to enter a perturbative graph
regime on an outer collar, and then finish by a Plan 1-type perturbative
argument.

The route is:

1. Use the exact level-set identity to show that on many near-boundary levels,
   both `D_H` and `D_I` are small.
2. Prove an outer-collar graph-entry theorem: if a near-boundary level has
   small `D_H + D_I`, then that level set is a regular graph over a ball, after
   translation and scaling.
3. Show that on a collar of such graph levels, the family moves coherently.
4. Extract one level in the collar with perturbative deficit `O(delta_T)`.
5. Transfer from that level back to `Omega` with only the standard
   `O(sqrt(delta_T))` collar loss, which squares correctly.

This is intentionally closer in spirit to Plan 1, but the input data should
come from the actual torsion levels and the Plan 2 level-set identity.

## Executive summary

Let `u = u_Omega` solve

\[
-\Delta u = 1 \quad \text{in } \Omega, \qquad u=0 \quad \text{on } \partial\Omega,
\]

and define

\[
E_t := \{u>t\}, \qquad m(t):=|E_t|.
\]

For regular levels set

\[
D_H(t)
=
\left(\int_{\partial^*E_t}\frac{1}{|\nabla u|}\right)
\left(\int_{\partial^*E_t}|\nabla u|\right)
-P(E_t)^2,
\]

\[
D_I(t)
=
P(E_t)^2 - n^2 \omega_n^{2/n} m(t)^{2-2/n}.
\]

The exact level-set identity gives

\[
\delta_T(\Omega)
\simeq_n
\int
\frac{D_H(t)+D_I(t)}{m(t)^{1-2/n}}\,dt.
\]

Interpretation:

- `D_I(t)` says `E_t` is almost isoperimetric.
- `D_H(t)` says `|grad u|` is almost constant on `partial E_t`, i.e. `E_t` is
  an approximate Serrin domain.

The missing theorem is not another bad-set kinetic estimate. The missing
theorem is:

> **Outer-collar graph entry.**
> If a near-boundary level `E_t` has both small isoperimetric defect and small
> Serrin defect, then `E_t` is a quantitatively controlled graph over a ball.

Once that theorem is available, the rest should look like coherent foliation /
perturbative trace, rather than metric transport on rough levels.

## Files to read first

Read these in order:

1. `Plan 2/level-set-deficit-identity.md`
2. `Plan 2/global-foliation-trace.md`
3. `Plan 2/selected-boundary-layer-theorem.md`
4. `Plan 2/weighted-serrin-collar-reduction.md`
5. `Plan 2/plan2.md`
6. `Plan 2/concrete-next-steps.md`

Useful supporting files:

7. `Plan 2/nicola-tilli-stability-import.md`
8. `Plan 2/wave2-E-bypass-search.md`
9. `Final/NearlySphericalClosure.tex`
10. `Final/GraphEntry.tex`

## What this route is allowed to use

Allowed:

- bounded reduction to `Omega subset B_R`;
- the exact level-set identity and profile-gap estimates;
- quantitative isoperimetry / FMP / Fusco--Julin;
- Serrin-stability inputs, if they are explicitly compatible with the norms
  delivered by `D_H`;
- a graph-regime perturbative argument once graph entry is proved.

Not allowed as a black box:

- "A0"-type perimeter-free metric Lipschitz bounds for rough levels;
- claiming that all levels are graphs without a theorem;
- smuggling in BDV selected minimizers unless the task is explicitly to build a
  hybrid selected-collar theorem;
- replacing the actual torsion levels by an auxiliary minimizer unless this is
  stated as a deliberate hybrid route.

## Main theorem target

The route should aim to prove the following bounded-class statement:

> There exists `C(n,R)` such that for every open `Omega subset B_R` with
> `|Omega| = omega_n`,
> \[
> \mathcal A(\Omega)^2 \le C(n,R)\,\delta_T(\Omega).
> \]

The intended mechanism is:

1. find a near-boundary collar of levels where many `E_t` have small
   `D_H + D_I`;
2. on that collar, prove graph entry and coherent motion;
3. extract one good perturbative level;
4. transfer back to `Omega`.

## Agent 1: Outer-Collar Good-Level Extraction

### Task

Turn the level-set identity into a clean theorem that produces many
near-boundary levels with simultaneously small `D_H` and `D_I`.

### Target statement

Fix a boundary collar in volume or radius variables, for example

\[
|\,\Omega \setminus E_t\,| \in [c_1 \sqrt{\delta_T}, c_2 \sqrt{\delta_T}]
\]

or the equivalent `rho`-collar near `rho_delta = 1 - kappa sqrt(delta_T)`.
Prove that outside a set of levels of measure `O(delta_T / eta)`, one has

\[
D_H(t) + D_I(t) \le \eta
\]

for any fixed small threshold `eta`.

### Deliverable

A self-contained note giving the exact good-level measure bound on an outer
collar, with the weight and change-of-variables done correctly.

### Failure mode to watch

Do not average over a slab in a way that introduces an `eta^{-1}` loss large
enough to kill the sharp rate after transfer. The point is to find a large good
set in a collar, not just one averaged good level far inside.

## Agent 2: Graph Entry from Small `D_H + D_I`

### Task

Attack the central missing theorem:

small near-boundary `D_H + D_I` implies graph entry over a ball.

### Target statement

Find the strongest theorem you can justify of the form:

> If `E_t` is a near-boundary torsion superlevel set with
> \[
> D_H(t) + D_I(t) \le \eta
> \]
> and `|Omega \setminus E_t|` lies in the outer collar scale, then after
> translation and scaling `partial E_t` is a `C^{1,alpha}` or at least
> Lipschitz graph over `partial B_1`, with norm tending to zero as
> `eta -> 0`.

If the full statement is too strong, isolate the strongest provable substitute:

- star-shapedness;
- positive reach on an outer collar;
- Reifenberg-flat graph entry;
- convexity after quantitative smallness;
- a graph theorem only for a subset of the collar.

### Deliverable

Either:

1. a proof with precise hypotheses and references, or
2. an exact obstruction report identifying which regularity theorem is missing.

### Failure mode to watch

Small `D_H` is an approximate Serrin condition, not automatically a graph
theorem. You must identify the missing PDE/geometry step explicitly.

## Agent 3: Parallel-Surface / Level-Set Cohesion in the Graph Regime

### Task

Assuming one is in a graph regime on an outer collar, prove that the nearby
interior levels remain graphs over balls and move coherently with the level
parameter.

### Target statement

Work in a setting like:

\[
\partial E_t = z(t) + (r(t) + h(t,\theta))\theta
\]

with `h` small in a graph norm for one level or a short collar. Prove a theorem
showing that for nearby levels:

1. the level sets remain graphs over spheres or balls;
2. the centers and graph functions vary continuously / quantitatively in `t`;
3. the level family admits a foliation gauge compatible with
   `global-foliation-trace.md`.

### Deliverable

A note stating and proving a “graph levels stay graph” theorem on an outer
collar, with exact norm propagation.

### Failure mode to watch

“Boundary is a graph, therefore all interior levels are graphs” is not true
without collar control. You only need a quantitative outer collar, not the full
interior.

## Agent 4: One-Level Perturbative Extraction

### Task

Assume the outer-collar graph-entry theorem and the cohesion theorem. Show that
one can extract at least one level in the collar whose perturbative deficit is
already `O(delta_T)`.

### Target statement

Inside the graph collar, prove there exists `t_hat` such that:

\[
\widetilde\delta(E_{t_{\hat{}}}) \le C \delta_T(\Omega),
\]

where `widetilde delta` is the perturbative quantity needed by the
nearly-spherical closure theorem or equivalent graph perturbative result.

This may be:

- the graph `H^1` norm squared;
- the non-neutral quadratic form `Q(h)`;
- the perturbative Saint--Venant deficit for the level;
- another equivalent smallness parameter.

### Deliverable

A rigorous extraction theorem from average-on-collar bounds to one perturbative
level in the collar.

### Failure mode to watch

Do not simply re-run Markov on too small a window if that reintroduces the old
`sqrt(delta_T)` problem. Use the graph-cohesion information if needed.

## Agent 5: Serrin-Stability Survey with Exact Norm Matching

### Task

Survey which Serrin-stability theorems are actually compatible with the norm
coming from `D_H`.

### Questions to answer

1. Does small `D_H(t)` give an `L^2`, `L^\infty`, or Hölder control on
   `|grad u|` along `partial E_t` after interpolation?
2. Which Serrin-stability theorems accept exactly that boundary norm?
3. What additional a priori geometry do they require?
4. Can they output graph entry or only Hausdorff / asymmetry closeness?

### Deliverable

A theorem table:

- reference;
- hypotheses;
- output;
- whether it is usable for torsion interior levels.

### Failure mode to watch

Do not report general Serrin references without checking norm compatibility.
The issue is not existence of stability theorems; it is whether `D_H` feeds the
right one.

## Agent 6: Hybrid Route with Selected Collar

### Task

Test a deliberate hybrid version: use Plan 2 only to produce a good
near-boundary level or collar, then switch to Plan 1 selected-collar machinery.

### Target statement

Determine whether the following route can be made rigorous:

1. Plan 2 gives one or many near-boundary approximate Serrin / almost
   isoperimetric levels.
2. Those levels can be compared to a selected minimizer collar or directly
   upgraded to the same regularity class.
3. Plan 1 graph closure then finishes sharply.

### Deliverable

Either:

1. a clean hybrid theorem statement with exact interface assumptions, or
2. a proof that this does not genuinely simplify anything.

### Failure mode to watch

Do not silently assume the selected minimizer is the same as the actual torsion
level. The interface has to be explicit.

## Agent 7: Obstruction Report

### Task

If the full graph-entry theorem seems out of reach, identify the exact weakest
statement that would still make the hybrid route work.

### Examples

- outer-collar Reifenberg flatness;
- star-shapedness plus quantitative normal oscillation;
- one good graph level plus short-cohesion to the boundary;
- a selected-collar comparison theorem.

### Deliverable

A short note:

1. what is enough;
2. what is currently missing;
3. which existing file is closest to supplying it.

## Common standards for all agents

Every agent should:

- state exactly which file(s) they used;
- separate proved statements from heuristic ones;
- isolate every hidden regularity assumption;
- avoid reusing the invalid “A0” metric Lipschitz argument;
- say explicitly whether the output is pure Plan 2 or a hybrid with Plan 1.

## What success looks like

This deployment succeeds if it produces either:

1. a viable outer-collar graph-entry theorem strong enough to replace the old
   bad-set metric transport route; or
2. a rigorous hybrid theorem that says Plan 2 provides the correct perturbative
   entry data and Plan 1 closes from there.

The key question is no longer “can we estimate the bad set by measure?”.
The key question is:

> Can `D_H + D_I` force actual geometric entry into a coherent graph collar
> near the boundary?

That is the theorem Plan 3 should attack.
