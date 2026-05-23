# Step 4 — perturbative finish: exact Proposition, sharp-linear proof, interface verdict

**Scope.** This note discharges **Step 4** of `PLAN3_INTENDED_ROUTE.md` (v3):
the standalone statement "sharp Faber–Krahn (Saint–Venant) stability for a
domain whose boundary is a small graph over a sphere", applied to the
graph subdomain `Ω̃ = E_{t̂}`. Per the spec it must **not** use the
foliation / `(F)` / `∂_ρ`, must **not** route through Brandolini as input,
and must **not** invoke `∂Ω`-of-the-original regularity nor the struck
`SchauderInterpolation` `C^{1,γ}→C^{2,γ₀}` bootstrap. It is a self-contained
nearly-spherical statement about the already-graph domain.

Conventions (from `Plan 2/level-set-deficit-identity.md`, §3): for an open
`Ω⊂ℝⁿ` with `|Ω|=ω_n`, `u_Ω` solves `−Δu_Ω=1`, `u_Ω=0` on `∂Ω`,
`T(Ω)=∫u_Ω`, `E(Ω)=−½T(Ω)`. The **Saint–Venant deficit** is
`δ_T(Ω)=E(Ω)−E(B₁)≥0` (here `B₁` is the unit ball, `|B₁|=ω_n`); by
`level-set-deficit-identity.md` §3 this equals `½ω_n·Γ(Ω)`, the normalized
endpoint convexity gap. `Asym(Ω)=inf_{x₀}|Ω△B₁(x₀)|/|B₁|` is the Fraenkel
asymmetry. `α(Ω)=∫_{Ω△B₁(x_Ω)}||x−x_Ω|−1|dx` is the smooth (weighted)
asymmetry of `NearlySphericalClosure.tex`. Spherical harmonics on `Sⁿ⁻¹`:
`−Δ_{Sⁿ⁻¹}y_{k,i}=k(k+n−2)y_{k,i}`; mode `0` ↔ volume, modes `1,i` ↔
translation/barycenter.

---

## 1. The exact Proposition, with the exact norm `X` and citation

There are **two** distinct nearly-spherical theorems in play, with
**different controlling norms**, and conflating them is the central trap.

### 1a. The perimeter (isoperimetric) prototype — `X = W^{1,∞}`, controls `H¹`

> **Theorem A (Fuglede 1989; Fusco survey Thm 3.1).** There is `ε(n)>0`
> such that if `E={tx(1+u(x)) : x∈Sⁿ⁻¹, 0≤t<1}` with `u:Sⁿ⁻¹→(−1,1)`
> measurable, `|E|=|B|`, barycenter of `E` at the origin, and
> `‖u‖_{W^{1,∞}(Sⁿ⁻¹)} ≤ ε`, then
> `P(E)−P(B) ≥ ¼‖∇_τ u‖²_{L²(Sⁿ⁻¹)} ≥ (1/8ω_n)|E△B|²`.

Citation: B. Fuglede, *Stability in the isoperimetric problem for convex or
nearly spherical domains in ℝⁿ*, Trans. AMS **314** (1989), 619–638
(`@Fuglede1989` in `Manuscript/references.bib`); restated verbatim as
**Theorem 3.1** in N. Fusco, *The quantitative isoperimetric inequality and
related topics*, Bull. Math. Sci. **5** (2015), `doi:10.1007/s13373-015-0074-x`,
§3.1. The norm there is **exactly** `‖u‖_{W^{1,∞}(Sⁿ⁻¹)} ≤ ε(n)`; Fusco's
own prose: "nearly spherical sets, that are sets close to a ball in `C¹`
sense" (and the proof uses only the Lipschitz/`W^{1,∞}` smallness). This is
the *isoperimetric/perimeter* functional; it controls the **`H¹`** seminorm
`‖∇_τ u‖_{L²}` (Sobolev/`H¹` of `∂E`). **This is not the Step-4 functional.**

### 1b. The Saint–Venant / torsional analogue — controls only `H^{1/2}`

The route's deficit is `δ_T = E(Ω)−E(B₁)` (torsion energy), **not** the
perimeter. The correct nearly-spherical statement is the torsional Fuglede-type
result of Brasco–De Philippis–Velichkov:

> **Proposition (Step 4) — Theorem B (BDV 2015, Thm 3.3 = Fusco survey
> Thm 6.14; recorded as `NearlySphericalClosure.tex` Lemma `lem:BDV33`).**
> Fix `0<γ≤1`. There exist `δ₁=δ₁(n,γ)>0` and a dimensional constant such
> that if `D⊂ℝⁿ` is a nearly spherical set,
> `∂D={(1+φ(ξ))ξ : ξ∈Sⁿ⁻¹}`, with
> `|D|=ω_n`, barycenter `x_D=0`, and
> `‖φ‖_{X} ≤ δ₁`, then
> `E(D)−E(B₁) ≥ (1/32 n²)·‖φ‖²_{H^{1/2}(Sⁿ⁻¹)}`.
> Chaining the trace–Poincaré comparison `‖φ‖²_{L²}≤‖φ‖²_{H^{1/2}}`,
> BDV Lemma 4.2(iii) `α(D)≤C₃(n)‖φ‖²_{L²}`, and BDV Lemma 4.2(i)
> `C₁(n)α(D)≥|B₁|²Asym(D)²` (all in `NearlySphericalClosure.tex`,
> Thm `thm:NS`) yields the **sharp linear** conclusion
> `Asym(D)² ≤ c(n)·δ_T(D)`, with `c(n)=32 n² C₃(n) C₁(n)/|B₁|²`.

Citation: L. Brasco, G. De Philippis, B. Velichkov, *Faber–Krahn
inequalities in sharp quantitative form*, Duke Math. J. **164** (2015),
1777–1831 (`@BDV2013`/`@BDV` in the corpus), **Theorem 3.3**; restated as
**Theorem 6.14** in the Fusco survey §6.2; packaged with the asymmetry
chain as **Theorem `thm:NS`** of `Final/NearlySphericalClosure.tex`.

**The norm `X`.** *As literally stated and proved in BDV / `thm:NS` /
`SaintVenantAssembly.tex` Thm `thm:NS`, the norm is*
> **`X = C^{2,γ}(Sⁿ⁻¹)`**, `‖φ‖_{C^{2,γ}}≤δ₁(n,γ)`, `0<γ≤1`.

This is *strictly stronger* than the `W^{1,∞}` of Theorem A, and is **the
struck `C^{2,γ₀}` smallness** that the spec forbids reaching via
`SchauderInterpolation`. **Whether `X` can honestly be weakened to
`W^{1,∞}` (or `C¹`, `C^{1,α}`, `H¹`) is the substance of §2–§3 and is
answered there: the spectral core is `H^{1/2}`-coercive, but the
*remainder* in the published torsional proof genuinely needs more than
`W^{1,∞}` because of how BDV linearize (a volume-preserving Hadamard
flow). The honest verdict is a GAP — see §3.**

**Why `H^{1/2}` and not `H¹` (sharpness of the controlled norm).** The
torsional deficit controls only the weaker `H^{1/2}` norm of `φ`, never
`H¹`. Fusco survey §6.2 gives the explicit obstruction: there are
nearly-spherical `Ω_h` with `‖u_h‖_{H^{1/2}}` bounded but
`‖u_h‖_{H¹}=‖∇_τ u_h‖_{L²}→∞` (long thin oscillations: perimeter blows up
but `λ₁`/torsion stay bounded). So Theorem A's `H¹`-control has **no**
torsional analogue; Step 4 must use Theorem B's `H^{1/2}` lower bound. This
is *sufficient* for sharp-linear `Asym²≲δ_T` because the asymmetry chain
only needs `‖φ‖_{L²}≤‖φ‖_{H^{1/2}}` (BDV Lemma 4.2(iii)).

---

## 2. Proof of sharp-linearity (spectral / Fuglede second-variation)

The sharp linear power — `Asym²≲δ_T`, equivalently `Asym≲δ_T^{1/2}`, with
**no** fractional loss — comes entirely from the coercivity of the second
variation on the subspace with modes `0` and `1` removed. We give the
computation in the clean (perimeter, Theorem A) form first because it
exhibits the mechanism transparently and verbatim (Fusco survey §3.1,
Steps 1–3), then state the modification for the torsional functional.

### 2a. The Fuglede expansion and the role of modes 0, 1

Write the boundary as the radial graph `φ(x)=x(1+u(x))`, extend `u`
0-homogeneously. The area formula gives (Fusco (3.3))
`Hⁿ⁻¹(∂E)=∫_{Sⁿ⁻¹}√((1+u)^{2(n−1)}+(1+u)^{2(n−2)}|∇_τu|²) dHⁿ⁻¹`,
and the volume map has Jacobian `(1+u(x))ⁿ`. Hence the two scalar
constraints are **exactly**

- `|E|=|B|`  ⇔  `∫_{Sⁿ⁻¹}((1+u)ⁿ−1)dHⁿ⁻¹=0`  ⇔
  `∫(nu+Σ_{h≥2}\binom{n}{h}uʰ)dHⁿ⁻¹=0`  (Fusco (3.7));
- barycenter `0`  ⇔  `(1/(n|B|))∫x(1+u)^{n+1}dHⁿ⁻¹=0`  (Fusco (3.5)).

Taylor-expanding the square root (`√(1+t)≥1+t/2−t²/7`) and using only
`‖u‖_{W^{1,∞}}≤ε`,

`P(E)−P(B) ≥ (½−Cε)∫|∇_τu|² − (\frac{n−1}{2}+Cε)∫u²`   (Fusco (3.8)).

Expand `u=Σ_{k≥0}Σ_i a_{k,i}y_{k,i}` in (normalized) spherical harmonics,
`−Δ_{Sⁿ⁻¹}y_{k,i}=k(k+n−2)y_{k,i}`:
`‖u‖²_{L²}=Σa_{k,i}²`, `‖∇_τu‖²_{L²}=Σ_{k≥1}k(k+n−2)Σ_i a_{k,i}²`.

**Removing mode 0 (volume).** From the volume identity (3.7),
`a₀=(1/√(nω_n))∫u dHⁿ⁻¹ = −(1/(n√(nω_n)))∫Σ_{h≥2}\binom{n}{h}uʰ`, so
`|a₀|≤C‖u‖²_{L²}≤Cε‖u‖_{L²}` — the **zeroth (volume) mode is quadratically
small**, hence negligible at second order.

**Removing mode 1 (translation).** From the barycenter identity and
`∫x_i dHⁿ⁻¹=0`, `|a_{1,i}|=(1/√ω_n)|∫u x_i dHⁿ⁻¹|≤Cε‖u‖_{L²}` — the
**first (translation) modes are quadratically small**.

**The spectral gap closes it sharply.** With modes `0,1` removed, the
remaining spectrum satisfies `k(k+n−2)≥2n` for all `k≥2` (the first
*nontrivial* Laplace–Beltrami eigenvalue after the killed modes). Hence
`‖u‖²_{L²} ≤ (1+Cε)Σ_{k≥2}Σ_i a_{k,i}² ≤ \frac{1}{2n(1−Cε)}‖∇_τu‖²_{L²}`.
Substituting into (3.8) and taking `ε=ε(n)` small,

`P(E)−P(B) ≥ ¼‖∇_τu‖²_{L²} ≥ \frac{n}{3}‖u‖²_{L²} ≥ \frac{1}{8ω_n}|E△B|²`.

The exponent on `|E△B|` (equivalently on `Asym`) is **exactly 2** because
the bound is *quadratic* in `u` with a *strictly positive* coefficient,
produced by a finite spectral gap (`2n>0`) — no compactness, no
contradiction, no loss of power. The gap is positive **only** because modes
`0,1` (eigenvalues `0` and `n`, the latter `<2n`) were excised by the volume
and barycenter normalizations; without that excision the quadratic form is
not coercive (indefinite) and no linear estimate holds.

### 2b. Torsional functional (the Step-4 functional)

For `E(D)=−½∫u_D` the same scheme applies but the quadratic form is the
*Saint–Venant/Steklov* second variation, not the perimeter one. BDV
(`1306.0392v1`, proof of Thm 3.3; `NearlySphericalClosure.tex` Lemma
`lem:BDV33`) compute
`∂²E(B₁)[φ,φ] = 2(\frac1n∫_{B₁}|∇H(φ)|² − ∫_{Sⁿ⁻¹}φ²)`, where `H(φ)` is the
harmonic extension. On the subspace `M₀` with **mode 0 (volume) and modes
1,i (barycenter) removed** they show (BDV (3.10))
`∂²E(B₁)[ξ,ξ] ≥ (1/4n²)‖ξ‖²_{H^{1/2}(Sⁿ⁻¹)}` for `ξ∈M₀`.
The positive constant is the **Steklov spectral gap**:
`min{∫|∇H(ξ)|²/∫ξ² : ξ∈M₀}=2` in every dimension `n≥2`, the second
nonzero Steklov eigenvalue of `B₁` (eigenspace = degree-2 spherical
harmonics; killed eigenvalues are `σ₀=0` for the volume mode and `σ₁=1<2`
for the translation modes). For `φ` only constrained to `M_δ` (the
normalization holds up to a `δ‖φ‖_{H^{1/2}}` defect) BDV's two-step
projection (their Step 2) recovers `∂²E(B₁)[φ,φ]≥(1/8n²)‖φ‖²_{H^{1/2}}`.
Combined with the remainder estimate (Lemma 3.4 / Dambrine), they obtain
`E(D)−E(B₁) ≥ (1/32n²)‖φ‖²_{H^{1/2}}` (Theorem B). The asymmetry chain of
`thm:NS` then gives `Asym(D)² ≤ c(n)·δ_T(D)`, sharp linear.

**Sharpness is intrinsic, not an artifact.** `NearlySphericalClosure.tex`
Remark `rem:ellipsoid`: for ellipsoids `E_ε` with semi-axes `1+εe_i`,
`Σe_i=0`, one has `Asym(E_ε)=c₁ε+O(ε²)` while
`E(E_ε)−E(B₁)=c₂ε²+O(ε³)`; so `Asym²` and `δ_T` are *both* `Θ(ε²)` and no
inequality `δ_T≥c·Asym^{2−θ}` (`θ>0`) can hold even within the
nearly-spherical class. Power **2** is optimal; the linear estimate is the
best possible.

**Verdict on sharp-linearity: YES** — `Asym²≲δ_T` with the sharp exponent
2, established by the `H^{1/2}` Steklov-gap coercivity after removing the
volume mode (`σ₀=0`) and the translation modes (`σ₁=1`), and shown sharp by
the ellipsoidal family. (This holds *given* the `X`-smallness hypothesis;
the contested point is purely *which* `X`, treated in §3.)

---

## 3. Interface check (critical): does Step 2's `L^∞`-gradient output meet `X`?

### 3a. What Step 2 delivers

Per `PLAN3_INTENDED_ROUTE.md` Step 2 + "single genuine crux": from
`D_H(t̂)≤θ` one upgrades to
`‖ |∇u|−c ‖_{L^∞(Σ_{t̂})}` small, where `Σ_{t̂}={u=t̂}` is, for a.e. `t̂`,
a smooth (Sard-regular, interior real-analytic) closed hypersurface
*in the interior of `Ω`* (interior analyticity of `u`; never `∂Ω`). So the
honest Step-2 output is, with modulus `m(θ)→0` as `θ→0`:

> (S2)  `Σ_{t̂}` is a closed `C^ω` hypersurface, interior to `Ω`, with
> `‖ |∇u|−c ‖_{L^∞(Σ_{t̂})} ≤ m(θ)` and `c≍` the ball value;
> additionally `|∇u|` bounded above and below on `Σ_{t̂}` (nondegeneracy
> earned from `D_H`).

### 3b. The level-set ↔ graph translation (implicit-function/Serrin relation)

`Ω̃=E_{t̂}={u>t̂}`, `∂Ω̃=Σ_{t̂}`. Center at the barycenter, scale to
`|Ω̃|=ω_n`. Write `∂Ω̃` as a radial graph `r=1+φ(ξ)`, `ξ∈Sⁿ⁻¹`. The
*existence* and `C^ω` *regularity* of `φ` is free from (S2): `Σ_{t̂}` is a
smooth closed hypersurface `C¹`-close to a sphere (the `L^∞`-Serrin input
makes it a genuine star-shaped graph, the route's Step 3 mechanism), so by
the implicit function theorem applied to the analytic map
`(r,ξ)↦u(rξ)−t̂` (with `∂_r u=∇u·ξ≠0` near `Σ_{t̂}` by nondegeneracy),
`φ∈C^ω(Sⁿ⁻¹)` and `‖φ‖_{C¹(Sⁿ⁻¹)}` is small.

The **norm transfer is governed by the Serrin/Pohozaev relation between
`|∇u|` on `Σ_{t̂}` and the geometry of the graph.** Differentiating
`u((1+φ(ξ))ξ)=t̂` tangentially:
`∇u·∂_τ[(1+φ)ξ]=0`, i.e. the tangential derivative of `φ` is controlled by
the *deviation of `∇u` from normal/constant*. Quantitatively, on a
`C¹`-graph close to `Sⁿ⁻¹`,

  `|∇u| = (∂_ν u) (1 + O(|∇_τφ|²))`  and the curvature/Newtonian-potential
  identity for `−Δu=1` on a near-ball gives, to first order,
  `|∇u|(ξ) − c = L[φ](ξ) + (quadratic in φ)`,

where `L` is, to leading order, the **Dirichlet-to-Neumann / shape
derivative of the torsion overdetermined map** — an order **+1**
(first-order, elliptic) operator in `φ` (the linearized Serrin map; same
operator whose spectrum is the Steklov gap of §2b). Hence, *at the
linearized level*,

> `‖ |∇u|−c ‖_{L^∞(Σ_{t̂})}` small  controls `φ` **one derivative
> weaker** than `L^∞`: it gives an `L^∞`-type bound on a *first-order
> elliptic operator of* `φ`, i.e. control of `φ` in (at best) a space
> like `C^{1,α}` *only after an elliptic gain*, and **without** the
> elliptic gain only `H^{1/2}`-type / `W^{1−ε}` control.

This is the precise sense of the survey's `H^{1/2}`-vs-`H¹` remark turned
into the graph norm: the *torsional* overdetermined datum `|∇u|−c` is a
**first-order** functional of `φ`, so its smallness is naturally an
`H^{1/2}`(of `φ`)-scale statement, **not** a `C^{2,γ}`(of `φ`) statement.

### 3c. Does (S2) meet `X` directly, by clean interior interpolation, or is there a GAP?

Three honest possibilities, adjudicated:

**(i) DIRECT? No.** `X=C^{2,γ}(Sⁿ⁻¹)` (the literal Theorem B / `thm:NS`
hypothesis) is a **second-order** norm on `φ`. Step 2 delivers an
`L^∞`-smallness of `|∇u|−c`, which by §3b is a *first-order* functional of
`φ`. An `L^∞` bound on a first-order quantity cannot, with no further
input, produce smallness of a *second-order* norm of `φ` (two-derivative
gap). So (S2) does **not** meet the literal `X=C^{2,γ}` hypothesis
directly.

**(ii) Clean interior interpolation to `X`? No — and this is exactly the
struck route.** One *could* close the two-derivative gap by an interior
Schauder/hodograph bootstrap of `u` near `Σ_{t̂}` (Kinderlehrer–Nirenberg
straightening + Lieberman oblique Schauder, then Gagliardo–Nirenberg
interpolation `‖φ‖_{C^{2,γ₀}}≤C‖φ‖_{L^∞}^{1−θ}‖φ‖_{C^{5,γ}}^{θ}`) — this
is **precisely the `SchauderInterpolation` block** and is **explicitly
struck** by `PLAN3_INTENDED_ROUTE.md` ("Explicitly struck", first bullet:
the `C^{2,γ₀}` regularization detour). Note: on an *inner analytic* level
set `Σ_{t̂}` such a bootstrap is actually *legitimate* (it is interior
regularity of the analytic `u`, not `∂Ω`-regularity, so it does **not**
violate the "no `∂Ω` regularity" constraint); but it **does** violate the
spec's explicit prohibition on the Schauder-to-`C^{2,γ₀}` machinery and on
"upgrading to a strong norm". Within the rules as written, this path is
**unavailable**. There is no *one-line* interior interpolation from a
first-order `L^∞` datum to a second-order norm; closing it inherently
requires the (struck) elliptic bootstrap.

**(iii) GAP — the honest verdict.**

> **VERDICT: GENUINE NORM GAP.** Step 2's output (an `L^∞`-smallness of the
> *first-order* overdetermined datum `|∇u|−c` on the smooth inner level
> `Σ_{t̂}`) does **not** meet, directly or by any *spec-permitted* clean
> interpolation, the hypothesis `X=C^{2,γ}(Sⁿ⁻¹)` under which the only
> sharp-linear torsional nearly-spherical theorem currently available
> (BDV Thm 3.3 = Fusco Thm 6.14 = `NearlySphericalClosure.tex` `thm:NS`)
> is proved. The gap is **two derivatives** of `φ` at the literal level,
> and at least **one derivative** even against the weakest *correct*
> torsional theorem (see "which side must give").

**Precise statement of the gap.**
Let `g(ξ):=|∇u((1+φ(ξ))ξ)|−c`. Step 2 controls `‖g‖_{L^∞(Sⁿ⁻¹)}=O(m(θ))`.
By §3b, `g = L[φ] + Q[φ]` with `L` a first-order elliptic
(Dirichlet-to-Neumann–type, Steklov) operator and `Q` quadratic. Therefore
Step 2 yields, *at most* and *only after the elliptic regularity of `L`*,
`‖φ‖_{C^{1,α}(Sⁿ⁻¹)} = O(m(θ))` for some `α=α(n)∈(0,1)` — and *without*
invoking that elliptic gain (i.e. using only the raw `L^∞` of `g`), one
gets merely a `W^{1,∞}`/`C¹`-type or `H^{1/2}`-type control of `φ`. In
**no** case does Step 2 produce `‖φ‖_{C^{2,γ}}→0`. Hence the hypothesis
`‖φ‖_{C^{2,γ}}≤δ₁` of the cited theorem is **not met**.

**Which side must give.** Two options; the second is the principled one.

1. *Strengthen Step 2 (NOT spec-permitted).* Run the interior
   Kinderlehrer–Nirenberg/Lieberman bootstrap on the analytic inner level
   `Σ_{t̂}` to upgrade `φ` to small `C^{2,γ}`. Legitimate as *interior*
   regularity (no `∂Ω` used) but **explicitly struck** by the spec; record
   as the honest "if the prohibition were lifted, this is the one-block
   fix" — it is the `SchauderInterpolation` block applied to an inner level
   rather than to `∂Ω`.

2. *Weaken the nearly-spherical theorem to a `W^{1,∞}` (Lipschitz)
   torsional statement (the correct target; partially open).* The
   `C^{2,γ}` in BDV Thm 3.3 enters **only** through Lemma 3.4
   (Dambrine's remainder), and Dambrine/BDV obtain that remainder via a
   *volume-preserving Hadamard flow* `Φ_t` with
   `‖Φ_t−Id‖_{C^{2,γ}}≤ω̂(‖φ‖_{C^{2,γ}})`. The second `t`-derivative of
   `e(t)=E(Φ_t(B₁))` (BDV (A.10)) contains
   `∇²u_t[∇u_t]·X` — **two derivatives of `u_t` up to the moving
   boundary**, hence two derivatives of `φ`. *This `C^{2,γ}` cost is an
   artifact of BDV's Hadamard-flow linearization, not of the underlying
   torsional second variation.* By contrast, Fuglede's **perimeter**
   Theorem A reaches the analogous sharp estimate with only `W^{1,∞}`
   smallness, by expanding the energy *directly* (area formula + Taylor),
   never differentiating a flow. The principled resolution is therefore:
   **prove the torsional second-variation expansion à la Fuglede
   (direct, flow-free), establishing**

   > **(Target B′, currently NOT in the corpus).** ∃ `ε(n)>0`: if `D` is
   > nearly spherical, `|D|=ω_n`, barycenter `0`,
   > `‖φ‖_{W^{1,∞}(Sⁿ⁻¹)}≤ε`, then
   > `E(D)−E(B₁) ≥ c(n)‖φ‖²_{H^{1/2}(Sⁿ⁻¹)}` (hence
   > `Asym(D)²≲δ_T(D)`, sharp linear).

   `B′` has the **same `H^{1/2}` spectral core (the Steklov gap = 2, §2b)
   — that part is already flow-free in BDV (3.9)–(3.10)** — and would
   require only a flow-free `W^{1,∞}` (or `C^{1,α}`) bound on the
   *nonlinear remainder* `E(D)−E(B₁)−½∂²E(B₁)[φ,φ]`. This is plausible (it
   is the torsional mirror of Fusco survey §3.1 Steps 1–2, replacing the
   perimeter area-formula expansion by the Hadamard/Newtonian-potential
   expansion of `∫u_D`) **but is not proved in the available corpus**:
   `NearlySphericalClosure.tex` only records the `C^{2,γ}` BDV form, and
   no flow-free torsional remainder estimate exists in the read sources.
   With `B′` in hand, §3b's
   `‖φ‖_{W^{1,∞}}=O(m(θ))` (the raw, no-elliptic-gain reading of Step 2,
   *provided* Step 2 additionally delivers a `C¹`/`W^{1,∞}` and not merely
   `H^{1/2}` graph bound — see Residual gap below) would meet `X=W^{1,∞}`
   and the route would close regularity-free.

**Residual gap even against `B′`.** Step 2's deliverable is an `L^∞`-bound
on `g=|∇u|−c`, a *first-order* functional of `φ` (§3b). Without an elliptic
gain this controls `φ` only at the `H^{1/2}`/`W^{1−ε,∞}` scale, **one
derivative short of the `W^{1,∞}` that even `B′` needs.** So *two* things
must be supplied for a fully regularity-free close:
  (a) the flow-free torsional `W^{1,∞}` theorem `B′` (replacing the struck
      `C^{2,γ}` BDV form); **and**
  (b) a Step-2 strengthening from `L^∞(|∇u|−c)` to a genuine `C¹`/`W^{1,∞}`
      *graph* bound on `φ` — which, by the first-order nature of the
      Serrin map, again needs an elliptic gain (interior Schauder on the
      analytic level), i.e. (b) is itself the struck machinery in
      lightweight form.
Equivalently: the *one* genuine crux flagged by the spec (Step 2's
`L²→L^∞` harmonic upgrade) is **not sufficient** to feed Step 4; a *second*
elliptic upgrade (`L^∞`-overdetermined-datum → `W^{1,∞}`/`C¹` graph norm)
is also required, and that second upgrade is exactly the kind of
elliptic-regularity step the spec strikes.

---

## 4. Summary verdict

- **Exact norm `X` of the only available sharp-linear torsional theorem:**
  `X = C^{2,γ}(Sⁿ⁻¹)`, `‖φ‖_{C^{2,γ}}≤δ₁(n,γ)`, `0<γ≤1` (BDV 2015
  Thm 3.3 = Fusco survey Thm 6.14 = `NearlySphericalClosure.tex`
  `thm:NS`). The torsional deficit controls only `‖φ‖_{H^{1/2}}` (sharp;
  Fusco §6.2 counterexample `Ω_h`), which is nonetheless enough for the
  sharp-linear `Asym²≲δ_T` via the BDV Lemma 4.2 asymmetry chain.
- **Sharp-linear:** YES (exponent 2 optimal; ellipsoidal sharpness,
  `NearlySphericalClosure.tex` `rem:ellipsoid`), driven by the Steklov
  spectral gap `=2` after excising the volume mode (`σ₀=0`) and the
  translation modes (`σ₁=1`).
- **Weakest *correct* norm (the right target):** the *isoperimetric*
  prototype (Theorem A, Fuglede 1989) is sharp-linear at `W^{1,∞}`; the
  *torsional* analogue `B′` at `W^{1,∞}` is the correct Step-4 target but
  **is not established in the corpus** (only the `C^{2,γ}` BDV form is).
- **Interface verdict vs Step 2's `L^∞`-gradient output: GAP** (genuine,
  precisely stated in §3c). Step 2's `L^∞`-smallness of the *first-order*
  overdetermined datum `|∇u|−c` does not meet `X=C^{2,γ}` directly, and
  no *spec-permitted* clean interior interpolation closes the
  two-derivative gap (the only closure is the explicitly struck
  Schauder/hodograph bootstrap, even though on an inner analytic level it
  would not violate the separate "no `∂Ω` regularity" rule). Closing
  Step 4 regularity-free requires **both** a flow-free `W^{1,∞}`
  torsional theorem `B′` (to remove the struck `C^{2,γ}`) **and** a
  second elliptic upgrade of Step 2 from `L^∞(|∇u|−c)` to a `C¹`/`W^{1,∞}`
  graph bound — the latter being a further elliptic-regularity step beyond
  the single crux the spec isolates.
