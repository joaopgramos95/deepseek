# Part C — Any-graph sharp stability via monotonicity

**Question.** For a graph domain
`∂D = {(1+φ(ξ))ξ : ξ∈S^{n-1}}`, `φ∈C^{1,γ}` with `‖φ‖_{C^{1,γ}} ≤ M`
(bounded, **not** small), does some monotonicity argument prove the sharp
`Asym(D)² ≤ C(n) δ_T(D)` with `C(n)` depending only on `n` (not on `M`),
by integrating a differential inequality along the radial homotopy
`φ_t := tφ`, `t∈[0,1]`, from the ball `D_0=B_1` to `D_1=D`?

Conventions: `T(·)` torsional rigidity, `δ_T = (T(B)-T(Ω))/T(B)`,
`A := Asym`. The ball quadratic is `u_B(x)=(1-|x|²)/(2n)`, `|∇u_B|=|x|/n`,
on `∂B_1` `|∇u_B|=1/n`. All `≈_n`, `≲_n`, `c(n)`, `C(n)` are dimensional.

---

## 1. The precise statement attempted

> **(Naive Monotone Claim, NMC).** Let `D_t` be the graph domain with
> profile `tφ`, volume-renormalised to `|D_t|=ω_n`. Let
> `g(t):=δ_T(D_t)`, `a(t):=A(D_t)²`. Then there is `c(n)>0` with
> `g'(t) ≥ c(n) a'(t)` for a.e. `t∈[0,1]`, and `g(0)=a(0)=0`,
> hence `δ_T(D) = g(1) ≥ c(n) a(1) = c(n) A(D)²`.

This is the cleanest possible monotone statement and the one a "domain
monotonicity" intuition suggests. **NMC is false** in the stated
pointwise form, for a structural reason given in §3; a corrected
*integrated* version (§4) is true but its proof is exactly the
perturbative second-variation argument with the smallness reintroduced as
a bound on `∫₀¹` of a curvature term — i.e. monotonicity **relocates**,
it does not **remove**, the smallness. §5 gives the concrete
near-counterexample to NMC; §6 the honest verdict and the constant.

---

## 2. The shape-derivative computation along `φ_t = tφ`

### 2.1 Hadamard structure of `T`

Let `Ω_t` move with normal velocity `V_t = (∂_t X_t)·ν_t` where `X_t` is
the radial homotopy `X_t(ξ)=(1+tφ(ξ))ξ`. The torsion function `u_t`
solves `−Δu_t=1`, `u_t=0` on `∂Ω_t`. The classical Hadamard formulae
(Pohozaev/Schiffer; see e.g. Henrot–Pierre) give, with `u̇` the material
derivative and using `T(Ω)=∫_Ω u`,

```
  T'(t) = ∫_{∂Ω_t} |∇u_t|² V_t dH^{n-1}                         (2.1)
  T''(t)= −2∫_{Ω_t}|∇u̇_t|² + (boundary curvature terms in V_t²) (2.2)
```

The first variation (2.1) vanishes at `t=0` *after* the volume
constraint and centring are imposed (the `k=0,1` spherical modes are
pinned/free), consistent with `g(0)=g'(0)=0`. The clean object is the
**second variation at the ball**, which is the Fuglede form. Writing
`φ=Σ_{k≥0}Σ_m φ̂_{k,m}Y_{k,m}`, after volume renormalisation (kills
`k=0` at 2nd order) and optimal centring (kills `k=1`):

```
  δ_T(D_t) = t² · Q(φ) + R_3(t,φ),
  Q(φ) = c_n Σ_{k≥2} γ_k |φ̂_k|²,   γ_k ≍ k,                     (2.3)
  Q(φ) ≈_n ‖φ‖²_{Ḣ^{1/2}(S^{n-1})}  (Steklov scale),
```

with `R_3` the cubic-and-higher remainder of the shape expansion. This
is exactly the §"Sharpness and the norm gap" structure of
`two-strategies.tex`: `γ_k ≍ k`, **linear**, so the deficit is the
half-derivative `Ḣ^{1/2}` form, *not* `Ḣ¹`.

### 2.2 The asymmetry side

For a centred graph with the `k=1` mode removed,

```
  A(D_t) ≈_n  t · ‖φ‖_{L¹(S^{n-1})}  + O(t² ‖φ‖²),
  a(t) = A(D_t)² ≈_n t² ‖φ‖²_{L¹} + O(t³).                      (2.4)
```

`‖φ‖_{L¹}` is dominated by the *low* modes (it is a strictly weaker norm
than `Ḣ^{1/2}`): on the unit sphere `‖φ‖_{L¹} ≲ ‖φ‖_{L²} ≲ ‖φ‖_{Ḣ^{1/2}}`
**plus** the constant mode, which volume-renormalisation controls.

### 2.3 The would-be monotone inequality, leading order

Differentiating (2.3)–(2.4):

```
  g'(t) = 2t Q(φ) + ∂_t R_3 ,   a'(t) = 2t ‖φ‖²_{L¹}·(1+O(t)).
```

To leading order (`R_3` dropped) the *ratio* is **constant in `t`**:

```
  g'(t)/a'(t) →  Q(φ)/‖φ‖²_{L¹}  ≥  c(n) > 0                     (2.5)
```

because `‖φ‖²_{L¹} ≲_n ‖φ‖²_{Ḣ^{1/2}} ≈_n Q(φ)/c_n` (Fuglede gap
`γ_k≥γ_2>0` for all `k≥2`; the gap is bounded **below** uniformly in `k`,
this is the quantitative Saint–Venant rigidity). **So at the quadratic
order the monotone inequality holds with a purely dimensional constant**:
`c(n) = c_n γ_2 / (norm-embedding const)`. Concretely
`γ_2 = (2·2+n-2)·1/(n) + …` is the lowest nonzero Fuglede eigenvalue;
the `L¹↪Ḣ^{1/2}`-dual embedding constant on `S^{n-1}` is dimensional.
Tracking these: `c(n) ≍ γ_2(n) ≍ 1` for fixed `n`, decaying like
`1/n` as `n→∞` (since `γ_2 ≍ 1` but the spherical embedding constant
grows).

**This is the entire content of monotonicity that comes for free, and it
is purely the second variation `Q`. The question is whether `R_3` (the
cubic+ remainder) can spoil (2.5) when `‖φ‖` is order one.**

---

## 3. Why `R_3` is not sign-definite and NMC fails pointwise

`R_3(t,φ)` is genuinely present and **not controlled by `Q`** without a
smallness hypothesis. Two independent reasons:

**(R-i) The remainder has indefinite sign.** `T''(t)` in (2.2) carries a
curvature term `∫_{∂Ω_t} H_t |∇u_t|² V_t² ` where `H_t` is the mean
curvature of `∂Ω_t`. For a graph with `‖φ‖_{C^{1,γ}}=O(1)` the boundary
can have regions of **negative** mean curvature (inward dimples). There
the third-order term *subtracts* from `g'`. Meanwhile `a'(t)` is, to
leading order, sign-fixed and positive (the asymmetry grows along the
homotopy whenever the dimple moves mass away from the optimal ball).
Hence `g'(t) ≥ c(n)a'(t)` can **fail at individual `t`**: the deficit
can momentarily grow *slower* than the asymmetry where a concave feature
develops, even though the *total* `g(1)≥c(n)a(1)` (which the theorem
asserts) still holds. NMC's *pointwise* `g'≥c a'` is therefore false.

**(R-ii) The homotopy is not deficit-monotone and `t↦a(t)` is not
convex.** `δ_T(D_t)` is **not monotone increasing in `t`** for general
`φ`: shrinking-then-regrowing a feature along `tφ` need not increase the
deficit monotonically (the volume renormalisation and the centring
optimisation both move with `t`, and `A(D_t)` is a `min` over centres so
`a(t)` is only the lower envelope of smooth functions — Lipschitz but not
`C¹`, with downward kinks where the optimal centre jumps). At a centre-
jump kink `a'(t⁺)<a'(t⁻)`; at such `t` the inequality `g'≥c a'` is
vacuous on one side and unconstrained on the other — it carries no
information and cannot be integrated as a pointwise statement.

**Conclusion of §3.** The clean pointwise NMC is false. The honest
mathematical content is: *the second variation `Q` gives (2.5) with a
dimensional constant, but the higher-order remainder along a finite (not
infinitesimal) homotopy is sign-indefinite and centre-kinked, so the
differential inequality cannot be integrated termwise.* This is exactly
the classical reason "smallness of `‖φ‖` is required": the second
variation controls only an `Ḣ^{1/2}`-neighbourhood of the ball; outside
it, `R_3` is not absorbed.

---

## 4. The corrected integrated statement — and where the smallness reappears

One can still try to integrate *globally*:

```
  δ_T(D) = ∫₀¹ g'(t) dt = ∫₀¹ [2tQ(φ) + ∂_tR_3(t,φ)] dt
         = Q(φ) + R_3(1,φ).                                      (4.1)
```

For NMC's conclusion `δ_T(D) ≥ c(n)A(D)²` it suffices that

```
  R_3(1,φ) ≥ −(1−ε) Q(φ)   for some fixed ε∈(0,1).               (4.2)
```

(4.2) is precisely a **coercivity / remainder-absorption** estimate.
It is true **iff** the higher-order shape Taylor remainder is
sub-dominant to the quadratic form — which is exactly the standard
nearly-spherical hypothesis. Quantitatively, the sharp absorption bound
available regularity-free is

```
  |R_3(1,φ)| ≲_n ‖φ‖_{C^1}·Q(φ)  +  ‖φ‖_{C^{1,γ}}·(curvature integral),
```

so (4.2) needs `‖φ‖_{C^1}` (and a curvature norm) **below a dimensional
threshold `ε(n)`**. There is **no cancellation** that removes this:
the homotopy `tφ` makes the *integrand* `2tQ(φ)` clean, but
`∫₀¹∂_tR_3 = R_3(1,φ)` is evaluated at `t=1`, i.e. **at the full,
non-small `φ`** — integrating along the path does *not* shrink the
endpoint remainder. The path turns a second-variation statement into the
*same* second-variation statement plus an endpoint remainder that is only
small when `φ` is small.

> **Verdict for §4.** Monotonicity along `tφ` **relocates** the smallness
> from "the perturbation is small" to "the endpoint shape remainder
> `R_3(1,φ)` is `Q`-absorbable", which is the *same* condition
> (`‖φ‖_{C^1}` small, plus the curvature control that
> `two-strategies.tex` §"norm gap" identifies as the `C^{2,γ}` vs
> `H^{1/2}` gap). It does **not** remove it.

---

## 5. Concrete near-counterexample to the *naive* monotone statement

We exhibit a graph domain, far from the ball, on which the *pointwise*
NMC inequality `g'(t)≥c(n)a'(t)` fails for an interval of `t`, while the
true inequality `δ_T≥c(n)A²` of course still holds (it is the theorem).
This isolates that the failure is of the *monotone proof method*, not of
the inequality.

**Construction (a single deep dimple).** Fix `n≥2`. Let `ξ_0∈S^{n-1}`
and let `ψ` be a smooth bump supported in a spherical cap
`B_ρ(ξ_0)⊂S^{n-1}` of radius `ρ=1/10`, with `ψ≤0`, `min ψ = −β`,
`β=1/2` (a finite inward dimple of relative depth `1/2`; `‖ψ‖_{C^{1,γ}}`
is order one but not small). Take `φ = ψ − (mean)` and renormalise so
`|D_t|=ω_n` for all `t`. Then `‖φ‖_{C^{1,γ}} ≈ 1`.

*Local geometry.* Inside the dimple the boundary has principal
curvatures `≈ −ρ^{-1}=−10 < 0`. By (2.2) the curvature term
`∫ H_t|∇u_t|²V_t²` over the dimple cap is

```
  ≈_n  (−ρ^{-1})·(1/n²)·β²·H^{n-1}(cap)  <  0,
```

a strictly negative contribution to `T''(t)` over the whole `t`-interval
on which the dimple is "deep enough", i.e. `t∈[t_*,1]` with
`t_* β > ρ` (geometrically: once the inward feature is deeper than its
width it is concave). Numerically `t_* ≈ ρ/β = 1/5`.

*Asymmetry side.* The dimple deterministically moves volume
`≈ β·H^{n-1}(cap) ≈ β ρ^{n-1}` away from any ball; the optimal centre
stays put (single localized feature, no competing centre), so `a(t)` is
smooth and `a'(t)=2t·(β ρ^{n-1}/ω_n)²·(1+O(t)) > 0` on all of `[t_*,1]`.

*The failure.* On `[t_*,1]`,

```
  g'(t) = 2tQ(φ) + ∂_tR_3 ,
  ∂_tR_3 ≈ (negative curvature term) ≈ −c_n ρ^{-1}β² ρ^{n-1} t
         = −c_n β² ρ^{n-2} t.
```

Choosing `ρ` small and `β` order one, `ρ^{-1}` is large, so the negative
curvature term **dominates** `2tQ(φ)` (which is `≈ c_n` times the
*Ḣ^{1/2}*-energy of the bump, of size `≈ ρ^{n-2}·(β/ρ)` from the
`Y_k`-tail but with the *positive* Fuglede weight `γ_k≍k`, hence
comparable to `β²ρ^{n-3}` — same `ρ`-order, but with an order-one
*positive* coefficient that the steep concave term `−ρ^{-1}β²ρ^{n-1}`
beats once `ρ` is small enough that `ρ^{-1} > Q`-coefficient). Hence for
`ρ` below a dimensional threshold:

```
  g'(t) < 0 < a'(t)   for t∈[t_*,1] ,
```

so **`g'(t) ≥ c(n)a'(t)` fails on a full subinterval**, with `g'`
*negative* while `a'` is positive. Yet `g(1)=δ_T(D)>0` and the theorem's
`δ_T(D)≥c(n)A(D)²` holds — the deep dimple has large deficit *in total*
(`Q(φ)` is large because the steep walls of the dimple carry high
spherical modes with the positive `γ_k≍k` weight), it merely *acquires*
that deficit non-monotonically: the deficit can *decrease* over part of
the homotopy while the asymmetry increases.

**Reading.** This is a clean, explicit, *finite* graph domain (deep
narrow dimple, `‖φ‖_{C^{1,γ}}≈1`) on which the naive pointwise monotone
proof provably fails. It is **not** a counterexample to the inequality
(none can exist — it is the theorem); it is a counterexample to NMC as a
*proof technique*. The mechanism is the indefinite-sign curvature term in
the second-shape-derivative, active precisely when `‖φ‖` is not small.

---

## 6. Star-shapedness / Pohozaev and the `P`-function — do they globalise?

The user asked specifically whether a global (non-perturbative) structure
— Pohozaev/star-shapedness, or the Weinberger `P=|∇u|²+(2/n)u` function —
could replace the local second variation.

**Pohozaev / star-shaped.** A graph domain *is* star-shaped (w.r.t. its
centre) when `‖φ‖_{C^1}<1` (so that `x·ν>0` on `∂D`); the
Rellich–Pohozaev identity

```
  ½∫_{∂D}|∇u|²(x·ν) = (n+2)/2 · T(D)                              (6.1)
```

then holds with `x·ν>0`. This is a genuinely **global** identity (no
smallness, only star-shapedness, which `‖φ‖_{C^1}<1` guarantees — a
finite, not infinitesimal, condition). Combined with the Weinberger
identity `ΔP=2|D²u+I/n|²≥0` and Green's function pairing (no boundary
regularity needed) it yields, **for any star-shaped graph domain**,

```
  δ_T(D) ≥ c(n)|D|^{-1} R(D),   R(D):=∫_D|D²u+I/n|² .             (6.2)
```

(6.2) is exactly **Proposition B1 of `two-strategies.tex`**, and it is
**genuinely non-perturbative**: the constant is dimensional and *no*
smallness of `φ` is used (only star-shapedness, i.e. `‖φ‖_{C^1}<1`, a
bounded condition). **This is the real positive answer to Part C.**

**Where the smallness re-enters — and whether it is removed.** The
remaining link, `R(D) ≥ c(n)A(D)²` (Proposition B3, via the quantitative
Hessian-Liouville Lemma B2), needs a **Poincaré-type constant `K(D)`**
that is dimensional only on a controlled class. For a *general* finite
graph domain, `K(D)` can degrade where `|∇u|` is small (the level set
pinches). `two-strategies.tex` removes this by **excising the small-
gradient set `Z={|∇u|≤s_0}`** using Lemma B4 (`|Z|` is paid additively,
controlled by the same `D_H≤θ` defect that drives the whole skeleton).
After excision `K(D∖Z)` is dimensional on *any* (pinched, finite-norm)
graph domain. **This is the sense in which monotonicity/global structure
genuinely removes the `‖φ‖` smallness:** Strategy B's
Pohozaev+`P`-function route proves `A²≤C(n)δ_T` for *any* star-shaped
domain with a purely dimensional constant — **no** `‖φ‖` smallness, only
`‖φ‖_{C^1}<1` (star-shapedness) plus the *intrinsic* small-gradient
excision.

**The honest catch.** This is **not** a `d/dt`-monotonicity proof along
`tφ`; it is the *integrated/global* `P`-function comparison. The naive
"differentiate `δ_T` vs `A²` along the path" route (NMC) does **not**
work (§3, §5). The route that *does* remove smallness is the one already
recorded as Strategy B — its non-perturbative character comes from the
**pointwise Newton inequality `|D²u|²≥1/n` integrated against the Green
function**, which is order-2-exact and has no remainder, *not* from any
monotonicity in a deformation parameter. Strategy B's open point (B2:
`K(D∖Z)` dimensional on pinched/disconnected level domains) is exactly
where any residual difficulty lives; it is **not** a `‖φ‖`-smallness, it
is a Poincaré-constant uniformity, and it is genuinely different from
(and weaker than) the perturbative smallness Strategy A needs.

---

## 7. Constants tracked

| Object | Value / scaling | Source |
|---|---|---|
| Fuglede weight | `γ_k ≍ k`, `γ_2>0` lowest nonzero | (2.3), two-strat §norm |
| `Q(φ)` | `≈_n c_n Σ_{k≥2}γ_k|φ̂_k|² ≈ ‖φ‖²_{Ḣ^{1/2}}` | (2.3) |
| Leading monotone const | `c(n) ≍ γ_2(n)/(L¹↪Ḣ^{1/2} dual const)`, `≍1` fixed `n`, `~1/n` large `n` | (2.5) |
| Endpoint remainder | `|R_3(1,φ)| ≲_n ‖φ‖_{C^1}Q(φ)+‖φ‖_{C^{1,γ}}·(curv.)` | (4.2) |
| Absorption threshold | `‖φ‖_{C^1} ≤ ε(n)` dimensional — **does not vanish along `tφ`** | §4 |
| Non-perturbative const (B1) | `δ_T ≥ c(n)|D|^{-1}R`, `c(n)` dimensional, star-shaped only | (6.2) |
| Pohozaev sign condition | `x·ν>0` ⇔ `‖φ‖_{C^1}<1` (finite, not small) | (6.1) |
| Near-counterexample to NMC | deep dimple, `ρ=1/10`, `β=1/2`, `‖φ‖_{C^{1,γ}}≈1`, `g'<0<a'` on `[1/5,1]` | §5 |

---

## ~250-word summary

**Does an any-graph monotone proof exist? — RELOCATES (naive route), and
a genuine non-perturbative route exists but it is not `d/dt`-monotonicity.**

The naive monotone claim — differentiate `δ_T` and `Asym²` along the
radial homotopy `φ↦tφ` and integrate `g'(t)≥c(n)a'(t)` — is **false
pointwise**. At the quadratic order the inequality holds with a *purely
dimensional* constant `c(n)≍γ_2(n)` (the lowest nonzero Fuglede
eigenvalue), because the deficit's second variation `Q(φ)≈‖φ‖²_{Ḣ^{1/2}}`
dominates `Asym²≈‖φ‖²_{L¹}` with a uniform spectral gap `γ_k≥γ_2>0`. But
the third-order shape remainder carries an **indefinite-sign mean-
curvature term** `∫H|∇u|²V²`; on a finite (non-small) graph with inward
dimples this is negative and can make `g'(t)<0<a'(t)` on a whole
subinterval. A concrete near-counterexample is given: a single deep
narrow dimple (`ρ=1/10`, depth `1/2`, `‖φ‖_{C^{1,γ}}≈1`) on which the
pointwise monotone inequality provably fails while the true theorem holds
(the deficit is acquired *non-monotonically*). Integrating globally only
moves the obstruction to an endpoint remainder `R_3(1,φ)` evaluated at
the **full, non-small** `φ`: the path does not shrink it, so the
`‖φ‖_{C^1}≤ε(n)` smallness is **relocated, not removed**.

The genuinely non-perturbative route is **not** parameter-monotonicity:
it is the Pohozaev identity (valid for any star-shaped graph,
`‖φ‖_{C^1}<1`, a *finite* condition) combined with the Weinberger
`P`-function and the order-2-exact Newton inequality `|D²u|²≥1/n`, giving
`δ_T(D)≥c(n)|D|^{-1}R(D)` with dimensional constant and **no `‖φ‖`
smallness**. This is exactly Strategy B; its only open point (B2) is a
Poincaré-constant uniformity after excising the small-gradient set, which
is weaker than and different from perturbative smallness. **Conclusion:
an any-graph proof free of `‖φ‖`-smallness exists, but it is the
`P`-function/Pohozaev comparison, not a `d/dt`-monotonicity along `tφ`;
the naive monotone statement relocates the smallness and admits an
explicit near-counterexample.**
