# Agent 5: Serrin-Stability Survey with Exact Norm Matching

## 0. Scope and files used

The task is to decide which Serrin-stability theorem, if any, accepts as input
exactly the boundary norm that the level-set Hadamard / Heintze--Karcher defect
`D_H(t)` delivers on a torsion superlevel set `partial E_t`, and outputs the
graph-entry information that Plan 3 needs.

Files read inside the repository:

1. `Plan 2/level-set-deficit-identity.md` (definition of `D_H`, `D_I`, exact
   identity, weighted variance representation; Sections 1, 2, 4, 6, 8).
2. `Plan 2/nicola-tilli-stability-import.md` (Section 10: what selected
   regularity adds; weighted-`L^2`-to-`L^infty` upgrade discussion).
3. `Plan 2/selected-boundary-layer-theorem.md` (Section 3 trace lemma,
   Section 4 "Input S", Section 5 implementation).
4. `Plan 2/weighted-serrin-collar-reduction.md` (Sections 2--4, 6: the explicit
   bridge from `D_H` to ordinary `L^2`/oscillation, and the observation that
   Input S is implied by `D_I` alone).
5. `Plan 2/plan2.md` (Sections 4, 6, 10, 14: prior survey-level discussion and
   Obstacle 5 on variance vs. oscillation).
6. `Plan 2/concrete-next-steps.tex` (Section "Serrin-Stability Input to Look
   For": list of canonical Serrin-stability papers to evaluate).

External literature was referenced by name only (WebSearch / WebFetch were
denied in this run). The corresponding theorem statements are taken from
their standard published forms; nothing below is asserted that is not already
public, and every row of the theorem table flags what is "proved by the
cited authors" vs. "what the Plan 2 notes have proved compatible with `D_H`".

## 1. What kind of boundary norm does `D_H(t)` produce?

This is the crux. Without an explicit answer, no Serrin-stability theorem can
be matched.

### 1.1 Native form (proved, unconditional)

On a regular level `Sigma_t = {u=t}`, write `f = |grad u|` and
`bar f = m(t)/P(t)`. The identity proved in
`level-set-deficit-identity.md`, Section 6, is exactly

  integral_{Sigma_t} (f - bar f)^2 / f  dH^{n-1}
    = (m(t) / P(t)^2) * D_H(t).                                          (1)

This is a **weighted `L^2` variance** of the normal derivative with the
intrinsic weight `1/f = 1/|grad u|`. It is the only norm that `D_H`
produces without additional structure: the identity is sharp, and
`1/|grad u|` is the natural coarea weight.

### 1.2 Ordinary `L^2` (conditional on two-sided gradient bounds)

If on the level one has

  0 < q_- <= |grad u| <= q_+ < infinity                                  (2)

with universal constants, then (1) implies

  || f - bar f ||_{L^2(Sigma_t)}^2  <=  C * (m(t)/P(t)^2) * D_H(t).       (3)

The two-sided bound (2) is **not** an unconditional output of
`D_H(t) + D_I(t)` small. It is supplied externally:

- in the Plan 2 / Plan 1 hybrid, by selected-minimizer nondegeneracy and
  Lipschitz bounds for `u` on the collar (cf. `selected-boundary-layer-
  theorem.md`, Section 3);
- in the pure Plan 2 setting, it is not available. This is an explicit
  open gap.

This is the precise content of Obstacle 5 in `plan2.md`: "Holder deficit
gives variance, not oscillation".

### 1.3 `L^infty` / Holder oscillation (conditional on `C^gamma` trace)

The interpolation step in `weighted-serrin-collar-reduction.md`, Section 3,
gives, on a uniformly `C^{1,gamma}` hypersurface and assuming a uniform
Holder bound `[f]_{C^gamma(Sigma_t)} <= M`,

  || f - bar f ||_{L^infty(Sigma_t)}
    <=  C * ||f - bar f||_{L^2}^{2 gamma / (2 gamma + n - 1)}
          * [f]_{C^gamma}^{(n - 1) / (2 gamma + n - 1)}.                 (4)

Combined with (3) this gives

  || f - bar f ||_{L^infty(Sigma_t)}
    <=  C * D_H(t)^{gamma / (2 gamma + n - 1)}.                          (5)

The exponent in (5) is **subsharp** in `D_H` and depends on `gamma` and
`n`. Crucially, (4) requires the `C^gamma` Holder seminorm of `|grad u|`
along the level surface to be controlled. Inside the actual torsion
superlevel sets of an arbitrary `Omega`, this is not implied by `D_H` and
`D_I`. It is again the selected-minimizer regularity that supplies it.

### 1.4 Summary table for the norm question

| Norm on `partial E_t`                | What `D_H(t)` gives                                | Hidden hypothesis                                       | Status in Plan 2 |
|--------------------------------------|----------------------------------------------------|---------------------------------------------------------|------------------|
| Weighted `L^2` (`1/|grad u|`)        | Exact identity (1)                                 | none                                                    | proved           |
| Ordinary `L^2`                       | `D_H` modulo two-sided gradient bound              | `q_- <= |grad u| <= q_+`                                | proved in selected collar; unknown for rough levels |
| `L^infty` oscillation                | `D_H^{gamma/(2 gamma + n - 1)}` via interpolation  | uniform `C^gamma` trace of `|grad u|` on `Sigma_t`       | conditional      |
| Lipschitz / `C^{1,alpha}` of `|grad u|` | Not directly                                    | requires Schauder on the collar                          | unavailable      |

Question 1 from the brief is therefore answered as follows: `D_H(t)`
natively gives a **weighted `L^2` variance**, not `L^infty` or Holder.
Upgrades to ordinary `L^2` or `L^infty` require external gradient bounds
and external `C^gamma` regularity of the gradient on the level. These are
exactly what the hybrid route imports from Plan 1; the pure Plan 2 route
does not provide them.

## 2. Theorem table

Notation: `D` is the candidate Serrin domain; `w` solves `-Delta w = 1`,
`w = 0` on `partial D`; `c` is the candidate Serrin constant; "graph
entry" means the conclusion places `partial D` as a small `C^{1,alpha}`
graph over `partial B_1`, after translation and scaling, strong enough to
feed a nearly-spherical second variation. "Hausdorff" / "asymmetry"
outputs are weaker.

| # | Reference                                              | Boundary input norm of `\partial_\nu w - c` | A priori geometric/regularity hypotheses | Output | Usable for the actual torsion superlevel set `E_t`? |
|---|--------------------------------------------------------|---------------------------------------------|------------------------------------------|--------|------------------------------------------------------|
| 1 | Aftalion--Busca--Reichel, *Approximate radial symmetry...*, Adv. Diff. Eq. 1999 | `L^infty`                                | `C^{2,alpha}` boundary; uniform interior/exterior ball | Hausdorff closeness to a sphere; **logarithmic** rate | No. `D_H` does not give `L^infty`; torsion levels of an arbitrary `Omega` are not `C^{2,alpha}`. Hybrid-only, and the rate is non-sharp. |
| 2 | Brandolini--Nitsch--Salani--Trombetti, *On the stability of the Serrin problem*, JDE 2008 | `L^infty` (oscillation) | Convex `D`; `C^2` boundary               | `L^infty` graph closeness to a ball, polynomial rate (`alpha = 1/(n+1)`) | No. Convexity is not produced by small `D_H + D_I` on a rough torsion level. Asking Plan 1 to produce convexity for the hybrid is circular. |
| 3 | Ciraolo--Magnanini--Vespri, *Holder stability for Serrin's overdetermined problem*, Ann. Mat. Pura Appl. 2016 | `L^infty`                              | Uniform interior sphere; `C^{1,Dini}` boundary | `C^0` Hausdorff distance to a sphere; Holder rate | No, in pure Plan 2. Uniform interior sphere is not produced by `D_H + D_I`; the `L^infty` norm is not the native `D_H` norm. Output is Hausdorff, **not graph entry**. |
| 4 | Magnanini--Poggesi, *On the stability for Alexandrov's soap-bubble theorem*, J. Anal. Math. 2020; also Trans. AMS 2019 (torsion case) | `L^2(partial D)` with Cauchy--Schwarz integral identity | `C^2` boundary; uniform interior touching ball of radius `r_i`; diameter bound | `L^2`/`L^1` deviation of two Aleksandrov radii (`r_e - r_i`); Holder rate; **NOT graph entry** | Closest match in **norm** to `D_H`, but the geometry (uniform interior ball, `C^2`) is not produced by `D_H + D_I`. Output is radius-spread, strictly weaker than `C^{1,alpha}` graph entry. Hybrid-only. |
| 5 | Magnanini--Poggesi, *Serrin's problem and Alexandrov's soap-bubble theorem: enhanced stability via integral identities*, Indiana Univ. Math. J. 2020 | Improved `L^2(partial D)` with logarithmic enhancement | `C^2`; uniform interior ball | Sharp Holder exponent for `L^1` deviation of distance function; asymmetry-type, not graph | Same status as #4. Norm match is good but the geometry must be supplied externally. |
| 6 | Magnanini--Poggesi, recent works on quantitative symmetry (post-2021) | `L^2` or weighted `L^2`                  | `C^2`; quantitative non-degeneracy of `|grad w|`         | Asymmetry / Hausdorff                                | Same family. Norm compatible with (3); but graph entry is not the output. |
| 7 | Krummel--Maggi-type follow-up Heintze--Karcher stability | Quantitative Heintze--Karcher **interior** defect, no boundary norm | Constant mean curvature surface; Heintze--Karcher slack | Hausdorff / `L^1` closeness to a union of spheres | Indirectly relevant: their Heintze--Karcher slack is exactly `D_H` in disguise, but they require constant mean curvature. Torsion levels do **not** have constant mean curvature; no feedback. |
| 8 | Ciraolo--Vezzoni, *A sharp quantitative Alexandrov inequality*, CPAM 2018 | Sup-norm of mean curvature deviation                 | `C^2` hypersurface; uniform two-sided ball condition     | Hausdorff closeness to a sphere; **sharp linear rate** | Norm mismatch: requires `||H - bar H||_infty`, which `D_H` does not produce. Hybrid: works inside Plan 1's `C^{2,alpha}` collar, but does not need Plan 2 input. |
| 9 | Fuglede 1989; Cicalese--Leonardi quantitative isoperimetric | Not Serrin; *isoperimetric* deficit       | Nearly-spherical class (`C^1` small graph)               | Graph `H^1` quadratic form / asymmetry-square        | This is Plan 1's nearly-spherical closure: a graph is already required *as input*. Plan 2's `D_I` only gives asymmetry, not graph entry. |
| 10| Nicola--Tilli style, Gomez--Guerra--Ramos--Tilli, Inventiones 2024 | Profile gap `h(s) = b(s) - v(s)`         | None on `Omega`, but uses STFT analyticity globally      | Profile control, then set comparison via Fock-space transport | The set-comparison step uses analyticity of `F`; torsion has no analogue. Plan 2 imports the **profile lemma** (proved), not the set-comparison step. |

Two further entries that the brief lists but that are not standalone
Serrin-stability theorems:

- *Pohozaev / Weinberger integral identities* (the foundation of all of the
  above): they underlie Magnanini--Poggesi. They produce `L^2`-on-boundary
  estimates directly, hence are the natural target for (3). But they
  assume `C^2` boundary, so the same geometric obstruction applies.
- *Reichel's moving-plane symmetry results*: qualitative only, not
  quantitative; cannot give graph entry from `D_H`-smallness.

## 3. Per-question summary

**(1) Norm.** `D_H(t)` natively gives the **weighted `L^2`** variance (1).
It is upgraded to ordinary `L^2` only with a two-sided bound (2) on
`|grad u|`, which is not implied by `D_H + D_I`. It is upgraded to
`L^infty` / Holder only with an additional `C^gamma` trace bound on
`|grad u|` along `partial E_t`; the rate is then **non-sharp** in `D_H`
(eq. (5)). For arbitrary torsion levels of an arbitrary `Omega`, neither
upgrade is available unconditionally.

**(2) Which theorems accept exactly that boundary norm.** Only the
**Magnanini--Poggesi family** (rows 4--6 of the table) is stated natively
in `L^2(partial D)` of `partial_\nu w - c`. This is the unique norm match.
Aftalion--Busca--Reichel, Brandolini--Nitsch--Salani--Trombetti, and
Ciraolo--Magnanini--Vespri all require `L^infty` of the gradient
deviation, which is a **downgrade** from `D_H` and forces the lossy
interpolation (5).

**(3) Additional a priori geometry.** Every existing Serrin-stability
theorem in the literature assumes at least one of: `C^2` / `C^{1,alpha}`
boundary; uniform interior sphere; uniform two-sided ball condition;
convexity; `|grad w|` bounded away from `0` on `partial D`. None of these
is delivered by `D_H + D_I` for an interior torsion superlevel set. They
are all *outputs* of a graph-entry theorem, not inputs to one. This is
the circularity that the deployment brief warns about.

**(4) Output type.** Across the entire Serrin-stability literature, the
**output is Hausdorff or `L^1`/`L^2` radius-spread**, not `C^{1,alpha}`
graph closeness over a ball. The strongest forms (Brandolini--Nitsch--
Salani--Trombetti under convexity; Ciraolo--Vezzoni for CMC) give
Hausdorff closeness with various rates; none of them, as published,
delivers a `C^{1,alpha}` graph parametrization of `partial E_t` over
`partial B_1`, which is what Plan 3's graph regime requires. Graph entry
is obtained in the literature only by combining Serrin-stability output
with an *additional* Allard / De Giorgi epsilon-regularity step, which
itself requires a perimeter / mean-curvature smallness hypothesis that
Plan 2 does not provide.

## 4. Cross-check against `weighted-serrin-collar-reduction.md`

The note `weighted-serrin-collar-reduction.md`, Section 4, observes a fact
that is crucial for this survey and worth repeating: in the
selected-collar regime where (2) and a `C^gamma` trace bound hold, the
specific "Input S" needed downstream

  A(E_t)^2  <=  C ( D_H(t) + D_I(t) + |U \ E_t|^2 )                       (6)

is **already implied by `D_I(t)` alone** through the quantitative
isoperimetric inequality (Fusco--Maggi--Pratelli). In that regime, `D_H`
is **diagnostic**, not load-bearing for asymmetry. This is independent
confirmation that no Serrin-stability theorem is actually doing work in
the Plan 2 closure: `D_I` already closes Input S via isoperimetry, and
the weighted-`L^2` Serrin information from `D_H` is informational only.

The corollary, inverted for the present survey, is that there is no point
hunting for a Serrin-stability theorem that accepts `D_H` in its native
norm. The asymmetry bottleneck does not live at the level of the Serrin
defect. It lives at the **boundary-deficit-propagation** step (Section 6
of the same note), which is a spectral question on `partial U`, not a
Serrin question on a single level.

This is the key qualitative finding.

## 5. Failure mode that this survey rules out

The pure Plan 2 hope is:

> "Small `D_H` gives `|grad u|` almost constant on `partial E_t`, hence by
> Serrin-stability `E_t` is a near-ball, hence by transfer `Omega` is a
> near-ball."

Each link in this chain fails for a different reason, and the table makes
this explicit:

1. `D_H` small gives only **weighted `L^2`** variance (Section 1.1).
2. No published Serrin-stability theorem accepts weighted `L^2` natively.
3. The closest match (Magnanini--Poggesi, ordinary `L^2`) requires `C^2`
   boundary and a uniform interior ball, neither delivered by
   `D_H + D_I`.
4. Even if (3) is granted, the output is Hausdorff / radius-spread, not
   graph entry.
5. The hybrid upgrade through (3)--(5) requires Plan 1's selected
   regularity, at which point Plan 1's nearly-spherical closure already
   finishes the argument and `D_H` is no longer load-bearing.

This is exactly the failure mode the brief flagged: "the issue is not
existence of stability theorems; it is whether `D_H` feeds the right
one".

## 6. Heuristic vs. proved separation

**Proved statements (Plan 2 internal):**

- The exact identity (1) for `D_H(t)` as a weighted `L^2` variance
  (`level-set-deficit-identity.md`, Section 6).
- Under (2), the ordinary-`L^2` estimate (3)
  (`weighted-serrin-collar-reduction.md`, Section 2).
- Under `C^{1,gamma}` collar and uniform `C^gamma` trace of `|grad u|`,
  the `L^infty` estimate (5)
  (`weighted-serrin-collar-reduction.md`, Section 3).
- Input S (6) follows from `D_I` and quantitative isoperimetry, with
  `D_H` unused (`weighted-serrin-collar-reduction.md`, Section 4).

**Proved statements (external literature, cited by name):**

- Each Serrin-stability theorem in rows 1--8 of the table is proved by
  the cited authors in its native form. The proofs have not been
  independently reverified in this run, since web access was denied.

**Heuristic / not proved:**

- That any of the existing Serrin-stability theorems can be modified to
  accept weighted-`L^2` input with the same a priori geometry. This is
  conjectured in `plan2.md`, Section 11 (Lemma 4), but not proved in any
  file in the repository.
- That a generic torsion superlevel set has uniform interior sphere /
  `C^2` boundary / two-sided gradient bound. None of these is implied
  by smallness of `D_H + D_I` alone.

## 7. Hidden regularity assumptions, isolated

Every Serrin-stability theorem in the table secretly assumes at least one
of:

(R1) `C^2` boundary of `partial E_t`. Not produced by `D_H + D_I`.
(R2) Uniform interior ball at every point of `partial E_t`. Not produced.
(R3) Two-sided bound `0 < q_- <= |grad u| <= q_+` on `partial E_t`. Not
     produced --- and indeed it *cannot* be produced from a single-level
     defect: `|grad u|` can be small or large at individual points of
     `partial E_t` consistently with `D_H + D_I` small.
(R4) `C^gamma` Holder trace of `|grad u|` on `partial E_t`. Not produced.
(R5) Convexity of `E_t`. Not produced.

In contrast, Plan 1's selected-minimizer machinery produces (R1)--(R4)
on a free-boundary collar. So every "applicable" row of the table is
applicable only in the hybrid setting where Plan 1 has already done the
regularity work; in that setting Plan 1's own nearly-spherical closure
is also available, and is strictly stronger than running a
Serrin-stability theorem on `E_t`.

This is the source of the verdict below.

## 8. Pure Plan 2 vs. hybrid status

Every row of the table with a non-trivial "Usable?" status is **hybrid**:
it requires Plan 1's selected-minimizer regularity. There is no Serrin-
stability theorem in the literature, and none in the Plan 2 notes, that
works in the **pure Plan 2** setting (arbitrary `Omega`, no selection).

The reason is structural, not a matter of finding the right paper. Serrin
stability theorems are stability *of equality cases* in a problem with
prescribed regularity. A torsion superlevel set `E_t` of an arbitrary
`Omega` does not have prescribed regularity until something external
(selection, perimeter regularity from `D_I` smallness with a uniform
density bound, etc.) supplies it.

## 9. Verdict

**No Serrin-stability theorem in the existing literature is compatible
with the native norm produced by `D_H(t)` and outputs graph entry.**

More precisely:

(V1) `D_H(t)` natively produces a **weighted `L^2`** variance of
     `|grad u|` on `partial E_t` (eq. (1)). It does not give `L^infty`,
     Holder, or Lipschitz control without external regularity.

(V2) The **only** norm-compatible family is **Magnanini--Poggesi** in
     ordinary `L^2`. Their theorem accepts the upgraded form (3), but:
     (a) the upgrade from weighted `L^2` to ordinary `L^2` requires the
         two-sided bound (2), which is not produced by `D_H + D_I`;
     (b) their theorem requires `C^2` boundary and a uniform interior
         ball; these are external geometric inputs;
     (c) their **output is radius-spread / asymmetry**, *not*
         `C^{1,alpha}` graph entry. Even when applicable, it does not
         deliver Plan 3's graph regime.

(V3) The other natural candidates --- Aftalion--Busca--Reichel,
     Brandolini--Nitsch--Salani--Trombetti, Ciraolo--Magnanini--Vespri,
     Ciraolo--Vezzoni --- all require `L^infty` of the gradient
     deviation as input. Reaching `L^infty` from `D_H` requires
     interpolation (5), which costs a non-sharp power and a `C^gamma`
     trace assumption that Plan 2 does not provide.

(V4) Even after a fully successful Serrin-stability step, the output is
     Hausdorff / asymmetry, **not** graph entry. To convert that output
     into a `C^{1,alpha}` graph one needs an Allard-type epsilon-
     regularity theorem with a perimeter / mean-curvature smallness
     hypothesis, which Plan 2 again does not supply for `partial E_t`.

(V5) Independently of all the above, `weighted-serrin-collar-reduction.md`,
     Section 4, shows that in the only regime where (2)--(R4) hold (the
     selected collar), the Plan 2 Input S is already closed by the
     **quantitative isoperimetric inequality** applied to `D_I`. The
     weighted-`L^2` Serrin information from `D_H` is then strictly
     redundant. The true bottleneck for sharp Faber--Krahn stability
     moves to the **boundary deficit propagation** step
     `D_I(0) + D_H(0) <= C * delta_T(U)`, which is a **spectral**
     question on `partial U`, not a Serrin-stability question on
     `partial E_t`.

**Practical recommendation for Plan 3.**

- Do *not* spend effort hunting for a Serrin-stability theorem to feed
  graph entry in Agent 2. The native norm of `D_H` does not match any
  existing graph-output theorem, and the mismatch is structural, not
  bibliographic.
- Treat `D_H` as **diagnostic** (it certifies "this level is an
  approximate Serrin domain") rather than **load-bearing** for graph
  entry.
- Reroute Agent 2's missing graph-entry theorem through perimeter /
  Allard / Reifenberg regularity using `D_I` (quantitative isoperimetry)
  and the volume control from the outer-collar good-level extraction
  (Agent 1). This bypasses Serrin stability entirely and is more likely
  to deliver `C^{1,alpha}` graph entry on the outer collar.
- If a Serrin step is still desired downstream of graph entry, for
  instance to refine constants, use the Magnanini--Poggesi `L^2`
  framework, since it is the unique norm match with `D_H`. But by that
  point Plan 1's nearly-spherical closure is also available and is
  strictly stronger.

The verdict, in one line: **`D_H` does not feed a graph-entry Serrin-
stability theorem; route Plan 3 through `D_I` + perimeter regularity for
graph entry, and treat `D_H` as confirmatory information only.**

This output is a **hybrid finding**: the analysis takes Plan 2 inputs
(`D_H`, `D_I`, the level-set identity) but concludes that the missing
graph-entry step must come from quantitative isoperimetry / perimeter
regularity (Plan 1-flavored or De Giorgi-flavored), not from Serrin
stability.
