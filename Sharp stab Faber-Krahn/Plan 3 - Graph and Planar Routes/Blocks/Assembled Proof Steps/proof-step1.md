# Plan 3 — Step 1, fully rigorous

**Chebyshev extraction of a good near‑boundary level.**

This note discharges Step 1 of `PLAN3_INTENDED_ROUTE.md` (v3) with full
rigour. It is self‑contained modulo the exact level‑set deficit identity,
which is **not** struck (it is Plan 2 material) and which we cite, in its
finite‑perimeter / no‑regularity form, from

- `Plan 2/level-set-deficit-identity.md` (§1 definitions, §2 boxed identity,
  §3 boxed deficit identification, §6 boxed variance, §8 Lemma 8.2 weight),
- `Plan 2/agent1-finite-perimeter-identity.md` (the unconditional
  finite‑perimeter statement of that identity, Theorem in §0 and §5).

Nothing from the struck list is used: no (BReg)/boundary regularity, no
selection principle, no `Cδ_T`‑collar / `D_H≲1/C` / `1≪C≪δ_T^{-1/2}`
window, no `√δ_T`‑collar, no `D_I`/Fuglede, no foliation/`(F)`/`∂_ρ`/
cohesion. Only `D_H`, a single static level, plain Markov.

---

## 0. Standing setup, normalization, and hypotheses on `Ω`

Fix the dimension `n ≥ 2`. Throughout, constants written `C_n`, `c_n`
depend **only on `n`** and may change from line to line.

**(H) Hypothesis on `Ω`.** `Ω ⊂ ℝⁿ` is open with `|Ω| < ∞`. We do
**not** assume `Ω` bounded, connected, or that `∂Ω` has any regularity.
After the scaling normalization below we additionally take
`|Ω| = ω_n` (so the volume‑radius is `R := (|Ω|/ω_n)^{1/n} = 1`); this
is the normalization fixed in the task setup and it is the *only* use of
"scaling".

Let `u = u_Ω ∈ H¹₀(Ω)` be the **variational** torsion function: the
minimizer of `J(v) = ½∫|∇v|² − ∫v` over `H¹₀(Ω)`; equivalently the
unique weak solution of `−Δu = 1` in `Ω`, `u = 0` on `∂Ω` in the
`H¹₀`‑trace sense. By the weak maximum principle `u ≥ 0` a.e. Set

```
E_t := {u > t},   m(t) := |E_t|,   P(t) := P(E_t) (perimeter),
‖u‖_∞ =: M_∞.
```

Because `Ω` is merely open of finite measure, the *geometric* boundary
`∂Ω` and the *level surfaces* `{u=t}` are handled in the
finite‑perimeter sense. All surface integrals below are over the
**reduced boundary** `∂*E_t`, and `P(t) = ℋⁿ⁻¹(∂*E_t)`. This is exactly
the setting in which the identity of §1 was proved unconditionally
(`agent1-finite-perimeter-identity.md`, §0, §7.5, §8). The phrase
"`Σ_t` smooth" is **only** invoked in conclusion (iii), where it is
earned for a.e. `t` from *interior* analyticity of `u` plus Sard — never
from regularity of `∂Ω`.

**Talenti `L^∞` bound** (Talenti 1976; Kesavan 2006, Thm 1.3.2;
restated in `agent1`, §1). For `Ω` of finite measure,

```
u*_Ω(s) ≤ u*_B(s) = ( R² − (s/ω_n)^{2/n} ) / (2n),   s ∈ [0,|Ω|],
```

so with the normalization `R = 1`,

```
M_∞ = ‖u‖_{L^∞(Ω)} ≤ 1/(2n) < ∞.                                  (T)
```

This finiteness is the only place where "no boundedness assumption on
`Ω`" is cashed in; it requires nothing of `∂Ω`.

**Deficit normalization.** Set, as in Plan 2 §8 and `agent1` §0,

```
δ_T(Ω) := E(Ω) − E(B),    E(Ω) := −½∫_Ω u = −½ T(Ω),
```

with `B` the ball of volume `|Ω|`. Under `x ↦ λx` one has
`u_{λΩ}(x)=λ²u_Ω(x/λ)`, hence `E(λΩ)−E(B_{λΩ}) = λ^{n+2}(E(Ω)−E(B))`,
whereas the scale‑invariant Saint–Venant deficit divides by
`|Ω|^{(n+2)/n}`. With `|Ω| = ω_n` fixed these differ by the *fixed*
dimensional factor `ω_n^{(n+2)/n}`, absorbed into `C_n`. So under (H)
with `|Ω|=ω_n`, "`δ_T(Ω)`" below is interchangeably the unnormalized or
the scale‑invariant deficit, the conversion factor being a dimensional
constant. Everything downstream (Steps 2–5) is stated in this same
normalization.

---

## 1. The exact identity and its weight (cited, not re‑proved)

Define, for a.e. regular level `t` (in the reduced‑boundary / BV‑coarea
sense of `agent1` §1, i.e. `t` in the full‑measure set
`ℛ := {t∈(0,M_∞): P(E_t)<∞, ∂*E_t⊂Ω}` minus the at‑most‑countable
plateau levels of `u`):

```
α(t) := ∫_{∂*E_t} |∇u|⁻¹ dℋⁿ⁻¹ = −m'(t),                          (α)
β(t) := ∫_{∂*E_t} |∇u|   dℋⁿ⁻¹ =  m(t),                           (β)
```

— equation (α) is `agent1` Lemma 1 (BV‑coarea); equation (β) is
`agent1` Lemma 2 (Lipschitz‑truncation divergence identity, no trace of
`∇u` used). The two **defects** are

```
D_H(t) := α(t)β(t) − P(t)²  ≥ 0      (Cauchy–Schwarz on ∂*E_t),
D_I(t) := P(t)² − n²ω_n^{2/n} m(t)^{2−2/n}  ≥ 0   (isoperimetry),
```

both nonnegative for a.e. `t` (`agent1` §6; Plan 2 §1).

**The weight.** From Plan 2 §8 (Lemma 8.2) and `agent1` §5, define the
nonnegative measure on `(0,M_∞)`

```
              dt
dν(t) := ─────────────────────.                                  (W)
         n² ω_n^{2/n} m(t)^{1−2/n}
```

**Exact identity (cited).** `agent1-finite-perimeter-identity.md`, §0
Theorem and §5 (Theorem), proved unconditionally for `Ω` open with
`|Ω|<∞` (no regularity of `∂Ω`, `u` variational, integrals on reduced
boundaries):

```
∫₀^{M_∞} ( D_H(t) + D_I(t) ) dν(t)
   = 2 ( E(Ω) − E(B) )
   = 2 δ_T(Ω).                                                    (I)
```

Equivalently, in the boxed form of Plan 2 §2 / §3,
`Γ(Ω) = |Ω|⁻¹∫ (D_H+D_I)/(n²ω_n^{2/n}m^{1−2/n}) dt = (2/|Ω|)(E(Ω)−E(B))`.

Since `D_I ≥ 0`, dropping it only loses a nonnegative quantity, giving
the one‑sided bound we will actually use:

```
∫₀^{M_∞} D_H(t) dν(t) ≤ 2 δ_T(Ω).                                 (I_H)
```

> **Honesty checkpoint — what is the "`D_H`‑integrand".** The route's
> phrase "`(D_H‑integrand)(t)`" is, unambiguously, the density of the
> measure `D_H(t) dν(t)` with respect to `dt`, namely
> ```
>            D_H(t)
> g(t) :=  ─────────────────────.                                  (G)
>          n² ω_n^{2/n} m(t)^{1−2/n}
> ```
> So `∫₀^{M_∞} g(t) dt ≤ 2 δ_T(Ω)` is (I_H) written with Lebesgue `dt`.
> The route's Chebyshev display
> `|{t: (D_H‑integrand)(t) > θ}| ≤ (C_n/θ) δ_T(Ω)` is Markov **for `g`**,
> not for `D_H(t)` itself. We will keep `g` and `D_H` rigorously
> distinct and reconcile units in §3 (Remark 3.3): on the near‑boundary
> window the weight is two‑sidedly `O(1)`, so `g(t̂) ≤ θ` and
> `D_H(t̂) ≤ C_n θ` are equivalent up to a dimensional constant. We
> deliver the conclusion in **both** forms so Step 2 can take whichever
> normalization of `D_H` it consumes.

---

## 2. Level variable vs. layer measure; the near‑boundary window

The route asks for a level `t̂` that "lurks within `O_θ(δ_T)` of the
boundary". The rigorous quantity that Step 5 (Lemma 8.3) actually
consumes is the **layer (collar) measure**

```
μ(t) := |{0 < u ≤ t}| = |Ω ∖ E_t| = |Ω| − m(t).                   (μ)
```

(`dist(Σ_{t̂},∂Ω)` is heuristic and is **not** used as a rigorous
quantity anywhere below.) `μ` is the relevant object because
`|Ω∖E_{t̂}| = μ(t̂)` is precisely the quantity fed to Lemma 8.3 / Step 5.

**Properties of `μ`.** From the standard structure of the distribution
function of `u ∈ H¹₀(Ω) ∩ L^∞` (Kawohl 1985; `agent1` §1, Lemma 1):

- `μ(0⁺) = |Ω| − m(0⁺) = 0`. Indeed `m(0⁺) = |{u>0}|`. Since
  `u = u_Ω > 0` a.e. on `Ω` for the torsion function on each connected
  component (strong maximum principle on the open set `Ω`; on
  disconnected `Ω` apply it componentwise — the torsion function is
  positive on every component of positive measure and `|{u=0}∩Ω| = 0`),
  we have `m(0⁺) = |Ω|`, hence `μ(0⁺) = 0`.
- `μ` is nondecreasing on `[0,M_∞]`, `μ(M_∞) = |Ω|`.
- `μ` is **absolutely continuous on `[ε, M_∞]` for every `ε>0`**, with
  `μ'(t) = −m'(t) = α(t) ≥ 0` for a.e. `t` (`agent1` Lemma 1: `m` is AC
  on `[ε,M_∞]`).

> **Honesty checkpoint — the `μ↔t` bookkeeping.** Two distinct
> monotone reparametrizations are in play, and conflating them is the
> classic trap. We will **not** change variables `t ↦ μ`. Instead we run
> two independent one‑dimensional Markov inequalities **in the same `t`
> variable**: one against Lebesgue `dt` for the defect (giving a bad‑`t`
> set of small *length*), one against `dt` for `μ'` for the layer
> (controlling how far `μ` has grown). Their compatibility is then a
> clean nonemptiness argument (Lemma 2.2 + Proposition 3.1), not a
> change of variables. This sidesteps the genuine gap that a naive
> "Markov in the layer variable" would create (the weight `dν` and the
> layer density `μ'=α` are *different* densities and need not be
> comparable globally — only on the near‑boundary window, where we
> prove two‑sided control, §2 and §3).

### Lemma 2.1 (the weight `dν` is two‑sidedly `O(1)` near the boundary)

Fix the absolute **near‑boundary window**

```
   J₀ := { t ∈ (0, M_∞) : m(t) ≥ |Ω|/2 }.                         (J0)
```

Equivalently `J₀ = {t : μ(t) ≤ |Ω|/2}`. Since `μ` is nondecreasing and
`μ(0⁺)=0`, `J₀` is an interval `(0, t*]` (or `(0,t*)`), `t* := sup J₀ >
0`. For every `t ∈ J₀`,

```
|Ω|/2 ≤ m(t) ≤ |Ω|,
```

hence, with `|Ω| = ω_n`,

```
ω_n /2 ≤ m(t) ≤ ω_n,
```

and therefore the Lebesgue density of `dν` obeys, for all `t ∈ J₀`,

```
   1                 dν           1
─────────  ·  c_n⁻ ≤ ──(t) ≤ ───────── · c_n⁺,
                     dt
```

precisely

```
       1                          dν             1
────────────────────────  ≤   ──(t)  ≤  ────────────────────────,
n²ω_n^{2/n} · ω_n^{1−2/n}      dt        n²ω_n^{2/n} · (ω_n/2)^{1−2/n}
```

i.e. there are dimensional constants `0 < c_W^- ≤ c_W^+ < ∞`,

```
c_W^-  ≤  dν/dt (t)  ≤  c_W^+      for all t ∈ J₀,                 (2.1)
c_W^- := 1 / ( n²ω_n^{2/n} · ω_n^{1−2/n} ) = 1/(n²ω_n),
c_W^+ := 1 / ( n²ω_n^{2/n} · (ω_n/2)^{1−2/n} ) = 2^{1−2/n}/(n²ω_n).
```

In particular `c_W^+/c_W^- = 2^{1−2/n} ≤ 2`, a dimensional constant,
**uniformly in `δ_T`** (no smallness of `δ_T` was used: only `m(t) ≍
|Ω|` on `J₀`, which is the *definition* of `J₀`). ∎

*Proof.* `m(t)^{1−2/n}` is increasing in `m(t)` for `n ≥ 2`
(`1−2/n ≥ 0`); insert `ω_n/2 ≤ m(t) ≤ ω_n` into (W). The map
`m ↦ m^{1−2/n}` is monotone, so the extreme values of the weight on
`J₀` are attained at `m = ω_n` and `m = ω_n/2`. (For `n = 2`,
`1−2/n = 0` and `dν/dt ≡ 1/(4ω_2)` exactly; (2.1) holds with
`c_W^- = c_W^+`.) ∎

> **Why `J₀` and not a `δ_T`‑collar.** `J₀` is an **absolute** window
> defined by the volume fraction `m ≥ |Ω|/2`; its `t`‑length `t*` is a
> geometric quantity of `Ω`, *not* tied to `δ_T`. This is the
> structurally correct replacement for the struck `Cδ_T`/`√δ_T`
> collars. We never need a lower bound on `t*` in absolute terms: the
> argument lives entirely on the *layer* side via `μ`, see §3.

### Lemma 2.2 (defect mass on the near‑boundary window)

Restricting (I_H) to `J₀` and using `D_H ≥ 0`, `D_I ≥ 0`,

```
∫_{J₀} D_H(t) dν(t)  ≤  ∫₀^{M_∞} D_H(t) dν(t)  ≤  2 δ_T(Ω).
```

Convert to Lebesgue measure with the **lower** bound in (2.1)
(`dν ≥ c_W^- dt` on `J₀`, so `g(t)dt = D_H dν ≥ ` … no — we need the
density `g`): with `g` from (G),

```
g(t) = D_H(t) · (dν/dt)(t),       t ∈ J₀,
```

and `∫_{J₀} g(t) dt = ∫_{J₀} D_H(t) dν(t) ≤ 2 δ_T(Ω)`. Hence the
**`D_H`‑integrand has small `dt`‑mass on the whole near‑boundary
window**:

```
∫_{J₀} g(t) dt  ≤  2 δ_T(Ω).                                      (2.2)
```

*(This is exact: `g(t)dt` and `D_H(t)dν(t)` are the same measure by
definition (G); no inequality is incurred in (2.2). The two‑sided (2.1)
is used in §3 only to translate between `g ≤ θ` and `D_H ≤ θ'`.)* ∎

---

## 3. The two Markov inequalities and the nonemptiness of their good set

Fix once and for all a **small absolute constant** `θ ∈ (0,1)` (a fixed
number; **not** `δ_T`‑small, **not** `1/C`‑small).

### 3.1 Markov for the defect (controls a *bad‑length*)

Define the **bad‑defect set**

```
Bad_θ := { t ∈ J₀ : g(t) > θ }.
```

By Markov’s inequality applied to the nonnegative `g` against Lebesgue
`dt` on `J₀`, using (2.2),

```
|Bad_θ| = ∫_{Bad_θ} dt ≤ (1/θ) ∫_{J₀} g(t) dt ≤ (2/θ) δ_T(Ω).
```

So

```
|Bad_θ|  ≤  (C_n^{(1)}/θ) · δ_T(Ω),     C_n^{(1)} := 2.            (3.1)
```

This is exactly the route’s Chebyshev display, with `C_n` made explicit
and **dimension‑free** (`C_n^{(1)}=2`; no `n`‑dependence at this step).

### 3.2 Markov for the layer (controls how far `μ` has grown)

We now produce a **lower bound on the `t`‑length of a sub‑window with
small layer measure**, *without* changing variables.

Pick a **layer budget** `λ > 0` (to be set `λ = (C_n/θ) δ_T(Ω)` in
Prop. 3.1). Define the **small‑layer window**

```
W_λ := { t ∈ (0, M_∞) : μ(t) ≤ λ }.
```

Since `μ` is nondecreasing with `μ(0⁺)=0`, `W_λ` is an interval
`(0, τ_λ]` (or `(0, τ_λ)`), with

```
τ_λ := sup { t : μ(t) ≤ λ } > 0      whenever λ > 0.              (3.2)
```

(That `τ_λ > 0` for every `λ>0`: `μ(0⁺)=0` and `μ` is right‑continuous
nondecreasing, so `{μ ≤ λ}` contains a right neighbourhood of `0`.)

**Claim 3.2 (length of the small‑layer window vs. budget).** For
`0 < λ < |Ω|/2` one has `W_λ ⊂ J₀` (because `μ ≤ λ < |Ω|/2 ⇒ m ≥
|Ω|/2`), and the Lebesgue length of `W_λ` is bounded **below** by

```
|W_λ|  ≥  λ / sup_{(0,τ_λ]} μ'   — not used; instead use the integral form:
```

we use the exact identity (μ AC on `[ε,M_∞]`, `μ(0⁺)=0`)

```
λ ≥ μ(τ_λ⁻) = ∫₀^{τ_λ} μ'(t) dt = ∫₀^{τ_λ} α(t) dt,              (3.3)
```

with equality `μ(τ_λ) = λ` unless `μ` jumps at `τ_λ` (a single level,
measure‑zero in `t`). Equation (3.3) is the **only** place the layer
budget enters; it does *not* require comparing `α` with the weight
`dν/dt` globally. ∎

> **Honesty checkpoint — is there a genuine gap here?** A naive route
> would try to lower‑bound `|W_λ|` by `λ / ‖α‖_{L^∞(J₀)}`, which fails
> if `α` is unbounded (it can be: `α=∫|∇u|⁻¹` blows up where `|∇u|→0`,
> e.g. at interior critical points). **We do not need such a bound.**
> The nonemptiness argument in Prop. 3.1 below is purely
> **measure‑subtractive**: it compares the *length* of `Bad_θ` (bounded
> by (3.1)) with the *length* of `W_λ`, and the latter is bounded below
> by an honest, unconditional estimate (Lemma 3.0) that uses only
> `μ(0⁺)=0` and the Talenti height bound — never an `L^∞` bound on `α`.
> There is **no residual gap** in the `μ↔t` bookkeeping; the trap is
> avoided by *not* attempting the change of variables and by using the
> integral identity (3.3) instead of a pointwise density comparison.

### Lemma 3.0 (unconditional lower bound on the small‑layer window length)

For every `λ ∈ (0, |Ω|/2)`,

```
|W_λ| = τ_λ  ≥  λ / a*,        where  a* := |Ω| / M_∞.            (3.4)
```

Equivalently `τ_λ ≥ (M_∞/|Ω|) · λ`. With the normalization `|Ω|=ω_n`
and Talenti (T) (`M_∞ ≤ 1/(2n)`),

```
τ_λ  ≥  λ / a*  =  (M_∞/ω_n) λ  ≥  (something)·λ,
```

and more usefully, **`a* ≤ |Ω|·(2n)` is bounded above** by a dimensional
constant: `a* = |Ω|/M_∞`. We need a *lower* bound on `τ_λ`, i.e. an
*upper* bound on `a*`. By Talenti, `M_∞ ≤ R²/(2n) = 1/(2n)`, which
bounds `M_∞` *above*, hence bounds `a*=|Ω|/M_∞` *below* — the **wrong
direction**. The correct, unconditional inequality is the averaged one:

```
∫₀^{M_∞} α(t) dt = ∫₀^{M_∞}(−m'(t)) dt = m(0⁺) − m(M_∞) = |Ω|.    (3.5)
```

(Total variation of `m`; `agent1` Lemma 1 / Dirichlet identity remark.)
Thus `α ∈ L¹(0,M_∞)` with `∫α = |Ω|`. By (3.3), `μ(τ_λ) =
∫₀^{τ_λ}α ≤ ∫₀^{M_∞}α = |Ω|`, consistent, but to get a *lower bound on
`τ_λ` from an upper bound on `λ`* we use the following sharp,
**unconditional** form.

*Correct statement and proof of Lemma 3.0.* Define the nondecreasing AC
function `Φ(t) := μ(t) = ∫₀^{t} α`. We bound `τ_λ` below using only that
`α ∈ L¹` with the *Talenti pointwise profile bound* converted to an
**upper bound on the increasing rearrangement of the layer**. Concretely,
by the Hardy–Littlewood / layer‑cake estimate and the Talenti comparison
`u*_Ω ≤ u*_B`, the layer at height `t` is **at most** the ball’s layer at
the same height:

```
μ_Ω(t) = |{0<u_Ω≤t}| = |Ω| − m_Ω(t),
m_Ω(t) = |{u_Ω>t}|.
```

Talenti gives `u*_Ω(s) ≤ u*_B(s)` for all `s∈[0,|Ω|]`, equivalently for
the distribution functions `m_Ω(t) ≤ m_B(t)` for all `t ≥ 0` (a
decreasing rearrangement dominated pointwise has a larger super‑level
measure). Hence

```
μ_Ω(t) = |Ω| − m_Ω(t)  ≥  |Ω| − m_B(t) = μ_B(t),                  (3.6)
```

**the domain’s layer dominates the ball’s layer at every height.** This
is the *wrong* direction for an upper bound on `μ_Ω`. Therefore Talenti
does **not** yield an unconditional *upper* bound on `μ_Ω(t)` (hence not
an unconditional lower bound on `τ_λ` of the clean form (3.4)).

> **Honesty checkpoint — this is a real subtlety, stated plainly.** An
> unconditional pointwise *upper* bound `μ_Ω(t) ≤ C·(geom)·t` is **false
> in general** for an arbitrary finite‑measure open set: a domain with a
> very thin long tentacle has `|∇u|` tiny near the tip, so the layer
> `{0<u≤t}` can have measure `≫ t` for small `t` (the level surfaces are
> almost parallel to the tentacle and sweep large volume per unit `t`).
> So one **cannot** lower‑bound `|W_λ|` by a clean `λ/(geom)` for *all*
> open `Ω`. The route’s phrase "a good level is found inside any
> near‑boundary window of length `> (C_n/θ)δ_T`" is therefore **not**
> literally an absolute statement about `t`‑length; the correct
> rigorous mechanism is the **layer‑measure budget**, which is exactly
> what Step 5 consumes and which we now make airtight **without** any
> such pointwise layer bound.

### 3.3 The correct nonemptiness argument — entirely on the layer side

The fix is to run **both** Markov inequalities as inequalities about the
**measure `dμ = α dt`**, not about Lebesgue `dt`. This is legitimate and
uses no comparison between `α` and the weight.

**Step A — defect mass against the layer measure.** On `J₀`, by (2.1),
`dν/dt ≥ c_W^-`, i.e. `dt ≤ (1/c_W^-) dν`. We want the `D_H` defect
controlled in the layer measure `dμ = α\,dt`. Use instead the *exact*
weight: for `t ∈ J₀`,

```
D_H(t) α(t) dt  ≤  ( α(t) / (dν/dt)(t) ) · D_H(t) dν(t)
              ≤  ( ‖α‖ ... )  — again an α bound; avoid.
```

This again needs an `α` bound and is **not** the route. We abandon any
weighting of `D_H` by `α`.

**Step A′ — the genuinely correct argument (length subtraction on
`J₀`).** Recall:

- (3.1): `|Bad_θ| ≤ (2/θ) δ_T(Ω)` (a Lebesgue‑length bound on the bad
  set, *unconditional*, dimension‑free).
- We must exhibit a level `t̂ ∈ J₀ ∖ Bad_θ` whose **layer measure**
  `μ(t̂)` is `≤ (C_n/θ) δ_T(Ω)`.

Set the layer budget `λ := (4/θ) δ_T(Ω)` and the small‑layer window
`W_λ = {μ ≤ λ} = (0,τ_λ]` (or `(0,τ_λ)`). We show **`W_λ ∖ Bad_θ ≠ ∅`**,
and any `t̂` in it satisfies (i)–(ii). The mechanism:

```
On W_λ, every level has layer ≤ λ (by definition of W_λ).         (★1)
The portion of W_λ that is "bad" has small Lebesgue length: 
        |W_λ ∩ Bad_θ| ≤ |Bad_θ| ≤ (2/θ)δ_T.                       (★2)
```

To conclude `W_λ ⊄ Bad_θ` we need the Lebesgue length of `W_λ` to
strictly exceed `(2/θ)δ_T`. This is where (3.3) is used **as a lower
bound via the *layer budget itself*** — not via an `α`‑bound:

```
μ(τ_λ⁻) = ∫₀^{τ_λ} α(t) dt = λ = (4/θ)δ_T(Ω).                     (★3)
```

By the layer **co‑area / Chebyshev split on the layer measure**:
partition `(0,τ_λ)` into the bad part `Bad_θ∩(0,τ_λ)` and its
complement `Good := (0,τ_λ)∖Bad_θ`. Then

```
λ = ∫_{(0,τ_λ)} α dt = ∫_{Bad_θ∩(0,τ_λ)} α dt + ∫_{Good} α dt.    (★4)
```

If `Good = ∅`, i.e. `(0,τ_λ) ⊂ Bad_θ`, then **all** of the layer mass
`λ` is carried by `Bad_θ`:

```
λ = ∫_{Bad_θ∩(0,τ_λ)} α dt.                                       (★5)
```

We now bound the right side of (★5) from above using the **defect
bound**, turning the contradiction. On `Bad_θ`, `g(t) > θ`, i.e.
`D_H(t)·(dν/dt)(t) > θ`, hence by (2.1) (`dν/dt ≤ c_W^+` on `J₀ ⊇ W_λ`):

```
D_H(t) > θ / (dν/dt)(t) ≥ θ / c_W^+        on Bad_θ ∩ J₀.         (★6)
```

This lower‑bounds `D_H` on the bad set but still does not bound
`∫_{Bad}α`. **The clean contradiction instead uses the defect *mass*
budget (2.2) against the *length* of `Bad_θ`, which we already have, and
the layer budget against the *length* of `(0,τ_λ)`.** Combine:

- From (3.1): `|Bad_θ| ≤ (2/θ)δ_T`.
- Choose `λ` so that the **layer can not be exhausted by a set of
  Lebesgue length `≤ (2/θ)δ_T`** *unless* `α` is large there — but a set
  where `α` is large is exactly a set of large layer mass, which is
  capped by `λ`. Formally: suppose `(0,τ_λ) ⊂ Bad_θ`. Then
  `τ_λ = |(0,τ_λ)| ≤ |Bad_θ| ≤ (2/θ)δ_T`. Also, by (★3),
  `∫_{(0,τ_λ)} α = λ = (4/θ)δ_T`. There is **no contradiction yet**
  (a short interval can carry large `α`‑mass). 

> **Honesty checkpoint — the length‑subtraction argument as stated
> does NOT close, and here is exactly why.** A set of small Lebesgue
> *length* can still carry an arbitrarily large *layer mass* `∫α`,
> because `α` is unbounded in general. Hence comparing `|Bad_θ|`
> (length) with `|W_λ|` (length) is **insufficient**: `W_λ` could be a
> very short interval entirely inside `Bad_θ`. The naive "good set =
> small‑layer window minus bad‑length set is nonempty" argument has a
> **genuine gap** precisely at the point where one wants `|W_λ| >
> |Bad_θ|`, because `|W_λ|` has **no unconditional lower bound** for an
> arbitrary open set (thin‑tentacle counterexample, §3.2). I will not
> paper over this. The correct argument must compare **like with
> like**: defect mass *in the layer measure* vs. total layer budget. I
> give that argument now; it closes, and it is the one the route
> actually needs.

### 3.4 The argument that closes — Markov for the defect *in the layer measure* `dμ = α dt`

The decisive observation: re‑weight the exact identity by `α`. Define on
`(0,M_∞)` the **layer‑defect density**

```
h(t) := D_H(t) / P(t)² · m(t)        — motivated by §6 variance; see below.
```

We use the **§6 boxed variance identity** of `level-set-deficit-identity.md`:

```
∫_{∂*E_t} (f − f̄)²/f dℋⁿ⁻¹ = ( m(t)/P(t)² ) · D_H(t),   f := |∇u|,
                                                f̄ := m(t)/P(t).      (V)
```

This is exact and unconditional on reduced boundaries (Plan 2 §6;
`agent1` §6). It is **not used** in the present Step 1 conclusion; we
record it only to flag that the natural normalization Step 2 will
consume is the *variance per unit perimeter*, i.e. `D_H(t)·m(t)/P(t)²`,
not `D_H(t)` raw. We return to this in Remark 3.6 (unit reconciliation).

For the nonemptiness we use a **direct Markov inequality on the measure
`D_H(t) dν(t)`**, comparing it to the **layer measure `dμ(t)=α(t)dt`**
*only through the exact identity (I_H)*, never through a pointwise
`α`‑weight bound. The clean statement:

#### Proposition 3.1 (good near‑boundary level — correct form)

Let `θ ∈ (0,1)`. There exist a dimensional constant `C_n` and a level
`t̂ ∈ (0, M_∞)` such that

- **(i)** `g(t̂) ≤ θ`, equivalently (Remark 3.6)
  `D_H(t̂) ≤ C_n θ` and the §6 variance
  `∫_{∂*E_{t̂}}(f−f̄)²/f ≤ C_n θ · m(t̂)/P(t̂)²`;
- **(ii)** `μ(t̂) = |Ω ∖ E_{t̂}| ≤ (C_n/θ) · δ_T(Ω)`;

provided the **near‑boundary mass condition** holds:

```
δ_T(Ω)  ≤  c_n · ε₀ · |Ω|,                                        (NB)
```

for a fixed small dimensional `c_n` and **any** chosen absolute
`ε₀∈(0,1/4)` fixing the layer fraction (e.g. `ε₀ = 1/8`); without (NB)
the conclusion is vacuous (the layer bound exceeds `|Ω|`) and Step 1 is
not needed because `δ_T(Ω) ≳ |Ω|` already makes `Asym(Ω)² ≲ δ_T(Ω)`
trivial (`Asym ≤ 2`). We track `(NB)` as an isolated, dimensionally
explicit hypothesis (it is *not* `δ_T`-small in a quantitative sense —
`ε₀` is a fixed absolute constant — it merely says the regime is the
nontrivial one).

*Proof of Proposition 3.1.* The argument is a **single Markov inequality
in the volume variable `s = m(t)`**, which is the change of variable that
*is* unconditional (it linearizes the layer), as opposed to the layer
density `α dt`.

**Volume‑variable form of the identity.** This is the *native* form of
the convexity gap and is taken **verbatim** from `agent1` Lemma 4
(`agent1-finite-perimeter-identity.md`, eqns (L4) and the displayed
algebra `s·G''(s) = (D_H+D_I)/(c_n s^{1−2/n})`), together with the
endpoint identification `Γ(Ω) = (1/|Ω|)∫₀^{|Ω|} s G''(s) ds =
(2/|Ω|)(E(Ω)−E(B))` (`agent1` Lemma 4 endpoint, Plan 2 §3 box). It does
**not** require any reconciliation with the `dν` measure of §1 — the
gap `∫ s G''(s) ds` is intrinsically a Lebesgue `ds` integral over the
**volume variable** `s∈[0,|Ω|]`, where `v(s):=u*(s)=m⁻¹(s)` is the
decreasing rearrangement and `s=m(t)` for `t=v(s)`. The plateau levels
of `u` are `ds`‑null and `m` is AC off them (`agent1` Lemma 3a–3c), so:

```
2 δ_T(Ω) = ∫₀^{|Ω|} s · G''(s) ds = ∫₀^{|Ω|}  (D_H+D_I)/(c_n s^{1−2/n})  ds.
```

Dropping `D_I ≥ 0` (which only decreases the integrand, pointwise a.e.):

```
∫₀^{|Ω|}  Φ_H(s) ds  ≤  2 δ_T(Ω),     Φ_H(s) := D_H(v(s))/(c_n s^{1−2/n}),
                                                                  (I_s')
```

with `c_n = n²ω_n^{2/n}`. This is exact and unconditional on `Ω` open
of finite measure (same provenance as (I); no regularity of `∂Ω`).

**Near‑boundary volume slab.** The layer measure is **linear in the
volume variable**:

```
μ(t) = |Ω| − m(t) = |Ω| − s     ⇔     s = |Ω| − μ(t).
```

So "`μ(t̂) ≤ λ`" is **exactly** "`s ≥ |Ω| − λ`", a clean slab in `s`
with **Lebesgue length `λ` in the `s` variable, unconditionally**
(no `α`-bound, no tentacle issue: the volume variable trivializes the
layer). Define the volume slab

```
S_λ := [ |Ω| − λ , |Ω| ),     |S_λ|_{ds} = λ.                     (S)
```

For `t = v(s)` with `s ∈ S_λ` we have `m(t) = s ≥ |Ω|−λ`, hence for
`λ ≤ |Ω|/2`, `m(t) ≥ |Ω|/2`, i.e. `t ∈ J₀` and (2.1) applies:
`dν/dt ∈ [c_W^-,c_W^+]`. Moreover on `S_λ` the volume weight is
two‑sided: for `s∈S_λ`, `(|Ω|/2)^{1−2/n} ≤ s^{1−2/n} ≤ |Ω|^{1−2/n}`,
so with `|Ω|=ω_n`,

```
c_n s^{1−2/n} ∈ [ c_n (ω_n/2)^{1−2/n},  c_n ω_n^{1−2/n} ] =: [κ⁻,κ⁺],
0 < κ⁻ ≤ κ⁺ < ∞   dimensional, ratio κ⁺/κ⁻ = 2^{1−2/n} ≤ 2.       (3.7)
```

**Markov in the volume slab.** By (I_s′) and `Φ_H ≥ 0`,

```
∫_{S_λ} Φ_H(s) ds ≤ ∫₀^{|Ω|} Φ_H(s) ds ≤ 2 δ_T(Ω).
```

By Markov in the **`s` variable** (Lebesgue `ds`, slab length `λ`):

```
| { s ∈ S_λ : Φ_H(s) > θ' } |_{ds}  ≤  (1/θ') ∫_{S_λ}Φ_H ds
                                    ≤  (2/θ') δ_T(Ω).             (3.8)
```

Choose the slab length

```
λ := (4/θ') δ_T(Ω).                                              (3.9)
```

Then the bad‑slab `{s∈S_λ: Φ_H(s)>θ'}` has `ds`‑length `≤ (2/θ')δ_T =
λ/2 < λ = |S_λ|_{ds}`. Hence

```
G_λ := { s ∈ S_λ : Φ_H(s) ≤ θ' }      has   |G_λ|_{ds} ≥ λ/2 > 0,
```

so **`G_λ ≠ ∅`**: there is `ŝ ∈ S_λ` with `Φ_H(ŝ) ≤ θ'`. Set
`t̂ := v(ŝ)`.

**Verification of (ii).** `ŝ ∈ S_λ ⇒ ŝ ≥ |Ω|−λ ⇒
μ(t̂) = |Ω| − m(t̂) = |Ω| − ŝ ≤ λ = (4/θ') δ_T(Ω)`. Setting
`θ' := θ` gives

```
|Ω ∖ E_{t̂}| = μ(t̂) ≤ (4/θ) δ_T(Ω).                              (3.10)
```

For this to be a nontrivial bound we need `λ = (4/θ)δ_T ≤ |Ω|/2`, i.e.

```
δ_T(Ω) ≤ (θ/8) |Ω|,                                              (NB-θ)
```

which is implied by (NB) with `c_n·ε₀ := θ/8` (and is automatic in the
regime where Step 1 is needed: if `δ_T ≥ (θ/8)|Ω|` then since
`Asym(Ω) ≤ 2` always, `Asym(Ω)² ≤ 4 ≤ (32/θ)·δ_T/|Ω|·... ` — in the
normalization `|Ω|=ω_n`, `Asym² ≤ 4 ≤ (32/(θω_n))δ_T = C_n δ_T`, so the
target inequality holds trivially and Step 1 is not invoked).

**Verification of (i).** `Φ_H(ŝ) ≤ θ` means
`D_H(v(ŝ))/(c_n ŝ^{1−2/n}) ≤ θ`, i.e. by (3.7)

```
D_H(t̂)  ≤  θ · c_n ŝ^{1−2/n}  ≤  θ · κ⁺  =: C_n^{(2)} θ,
C_n^{(2)} := κ⁺ = n²ω_n^{2/n} · ω_n^{1−2/n} = n² ω_n.             (3.11)
```

For the route’s integrand normalization `g(t)=D_H(t)·(dν/dt)(t)`, use
(2.1) on `J₀ ∋ t̂`:

```
g(t̂) = D_H(t̂)·(dν/dt)(t̂) ≤ C_n^{(2)} θ · c_W^+
      = (n²ω_n)·(2^{1−2/n}/(n²ω_n))·θ = 2^{1−2/n} θ ≤ 2θ.
```

Hence, after relabelling the absolute constant `θ ← θ/2` (still a fixed
small absolute constant), one obtains the route’s exact display
`g(t̂) ≤ θ`. Equivalently `D_H(t̂) ≤ C_n θ` with `C_n = n²ω_n`. ∎

> **Why the volume variable is the right one — and the earlier
> length‑subtraction gap is now genuinely closed.** The change of
> variable `s=m(t)` is unconditional (`agent1` Lemmas 3a–3c: `m` is AC
> off countably many plateaus, the rearrangement framework needs no
> regularity of `∂Ω`). Crucially, **the layer measure is *linear* in
> `s`**: `μ = |Ω|−s`. So "small layer" is the slab `S_λ` of *exact*
> `ds`‑length `λ`, with **no dependence on `α` and no tentacle
> pathology**. The defect mass (I_s′) is also an integral against `ds`.
> Both objects now live in the *same* variable with the *same* reference
> measure `ds`, so Markov‑length subtraction is legitimate and the good
> set has `ds`‑measure `≥ λ/2 > 0`. This is the airtight version of the
> route’s "a good level is found inside any near‑boundary window of
> length `>(C_n/θ)δ_T`": the correct window is in the **volume
> variable**, where its length *is* the layer budget by the identity
> `μ=|Ω|−s`. The `t`‑phrasing in the route was heuristic; the volume
> (equivalently layer‑measure) phrasing is the rigorous one, and it is
> exactly the quantity Step 5 / Lemma 8.3 consumes (`|Ω∖E_{t̂}|`).

### 3.5 Intersection with Sard‑regular values (conclusion (iii))

The good set in the volume variable,
`G_λ = {s∈S_λ: Φ_H(s) ≤ θ}`, has `|G_λ|_{ds} ≥ λ/2 > 0`. Pull it back
to the level variable through `t = v(s)`. Off the at‑most‑countable
plateau levels of `u`, `v = m⁻¹` is a strictly decreasing absolutely
continuous bijection between full‑measure subsets of `S_λ` and a
`t`‑interval (`agent1` Lemma 3c). Hence the pull‑back
`Ĝ := v(G_λ) ⊂ (0,M_∞)` has **positive Lebesgue `t`‑measure** (a
strictly monotone AC map sends positive‑measure sets to
positive‑measure sets: `|v(A)| = ∫_A |v'| = ∫_A 1/α > 0` whenever
`|A|>0`, since `α<∞` a.e.).

Now intersect with the **Sard‑regular levels**. The torsion function `u`
is **real‑analytic in the interior of `Ω`** (interior elliptic
regularity for `−Δu=1`: `u ∈ C^∞`, indeed analytic, on the open set
`Ω`; this is *interior* analyticity and uses **nothing** about `∂Ω`).
By the Morse–Sard theorem for `C^∞`/analytic functions
(Sard 1942; for the analytic case the critical‑value set is even
locally finite away from `∂Ω`), the set of **critical values**

```
N := { t ∈ (0,M_∞) : ∃ x∈Ω, u(x)=t, ∇u(x)=0 }
```

has Lebesgue measure zero (`|N| = 0`). For every **regular value**
`t ∉ N`, `Σ_t = {u=t}∩Ω` is a (possibly empty) smooth — in fact
real‑analytic — embedded hypersurface, with `|∇u|>0` on `Σ_t`. (This is
the *inner* level statement; it never touches `∂Ω`. Cf.
`PLAN3_INTENDED_ROUTE.md` §Step 2 and the user’s red‑pen note (a) in
`MY_UNDERSTANDING.md`: interior level sets are smooth for free.)

Since `|Ĝ| > 0` and `|N| = 0`,

```
Ĝ ∖ N   has positive Lebesgue measure, in particular Ĝ ∖ N ≠ ∅.
```

Pick **any** `t̂ ∈ Ĝ ∖ N`. Then:

- `t̂ ∈ Ĝ` ⇒ `Φ_H(m(t̂)) ≤ θ` ⇒ **(i)** holds: `D_H(t̂) ≤ C_n θ` and
  (relabelling `θ`) `g(t̂) ≤ θ`; the §6 variance bound (V) follows by
  substituting (i) into (V):
  `∫_{∂*E_{t̂}}(f−f̄)²/f = (m(t̂)/P(t̂)²)D_H(t̂) ≤ C_n θ·m(t̂)/P(t̂)²`.
- `t̂ ∈ Ĝ ⊂ v(S_λ)` ⇒ `m(t̂) ∈ S_λ` ⇒ **(ii)** holds:
  `|Ω∖E_{t̂}| = |Ω|−m(t̂) ≤ λ = (C_n/θ)δ_T(Ω)`.
- `t̂ ∉ N` ⇒ **(iii)** holds: `t̂` is a regular value, so `Σ_{t̂}` is a
  smooth (real‑analytic) embedded hypersurface with `|∇u|>0` on it —
  exactly what Step 2 requires.

This completes the proof of the Lemma. ∎

### Remark 3.6 (unit reconciliation — which `D_H` normalization)

Three normalizations appear; they are mutually equivalent on `J₀` up to
dimensional constants, so the Lemma can be quoted in whichever form the
consumer needs:

| object | value at `t̂` | relation |
|---|---|---|
| route integrand `g(t)` | `≤ θ` | `g = D_H·(dν/dt)`, `dν/dt∈[c_W^-,c_W^+]` on `J₀` |
| raw defect `D_H(t)` | `≤ n²ω_n·θ` | `D_H = g/(dν/dt) ≤ g/c_W^-` |
| §6 weighted variance `∫(f−f̄)²/f` | `≤ n²ω_n·θ·m(t̂)/P(t̂)²` | exact identity (V) |

The conversion factors `c_W^±`, `κ^±` are **dimensional, two‑sided, and
`δ_T`‑uniform on the near‑boundary window `J₀`** (Lemma 2.1, (3.7)).
**Step 2 consumes the §6 variance form** (integrated `L²` closeness of
`|∇u|` to the constant `f̄=m/P`); the table shows it is `≤ C_n θ ·
m(t̂)/P(t̂)²`. Since on `J₀` additionally `m(t̂) ≍ |Ω|` and (once Step 2’s
own a‑priori `0<c≤|∇u|≤C` on `Σ_{t̂}` is in force, see Plan 2 §6 last
display) `P(t̂) ≍ |Ω|^{1−1/n}`, this is the genuine `L²`‑variance bound
`∫_{Σ_{t̂}}||∇u|−f̄|² ≤ C_n θ` that the harmonic‑interior upgrade
(the route’s single crux) takes as input. (Step 1 does **not** assert
the lower bound `|∇u|≥c`; that is Step 2’s business. Step 1 only
delivers (i)–(iii) as stated.)

---

## 4. The Lemma, stated precisely

> **Lemma (Plan 3, Step 1 — Chebyshev extraction of a good
> near‑boundary level).** Let `n≥2`. Assume **(H)**: `Ω⊂ℝⁿ` open,
> `|Ω|<∞`, normalized so `|Ω|=ω_n`; `u=u_Ω∈H¹₀(Ω)` the variational
> torsion function. (No regularity, boundedness, or connectedness of
> `∂Ω` is assumed.) Let `δ_T(Ω):=E(Ω)−E(B)` with `B` the unit‑volume
> ball, and assume the nontrivial regime **(NB‑θ)**: `δ_T(Ω) ≤ (θ/8)ω_n`
> (outside this regime the target `Asym(Ω)²≤C_nδ_T(Ω)` is trivial since
> `Asym≤2`, so Step 1 is not invoked).
>
> Then there is a dimensional constant `C_n` (explicitly `C_n = n²ω_n`
> for the raw‑defect form; `C_n=4` for the layer bound; `C_n=2` for the
> bad‑set length) such that for **every** fixed absolute constant
> `θ∈(0,1)` there exists a level `t̂∈(0,‖u‖_∞)` with
>
> 1. **(i)** the `D_H`‑integrand is small:
>    `g(t̂) := D_H(t̂)/(n²ω_n^{2/n}m(t̂)^{1−2/n}) ≤ θ`;
>    equivalently the raw defect `D_H(t̂) ≤ n²ω_n·θ`, equivalently the
>    §6 weighted Serrin variance
>    `∫_{∂*E_{t̂}}(|∇u|−\bar f)²/|∇u|\,dℋⁿ⁻¹ ≤ n²ω_n·θ·m(t̂)/P(t̂)²`,
>    with `\bar f=m(t̂)/P(t̂)`;
> 2. **(ii)** the discarded layer is `O_θ(δ_T)` in **measure**:
>    `|Ω∖E_{t̂}| = |{0<u≤t̂}| ≤ (4/θ)·δ_T(Ω)`;
> 3. **(iii)** `t̂` is a regular value of `u`, so `Σ_{t̂}={u=t̂}∩Ω` is a
>    smooth (real‑analytic) embedded hypersurface with `|∇u|>0` on it.
>
> All constants depend on `n` only. The number `θ` is a fixed small
> absolute constant (not `δ_T`‑small, not `1/C`‑small).

The three proof obligations of the brief are discharged as: **(1)**
Lemma 2.1 + Lemma 2.2 + (I_H) (weight two‑sided `O(1)` on `J₀`,
`∫_{J₀} g ≤ 2δ_T`); **(2)** Proposition 3.1 via the **volume‑variable**
Markov (`s=m(t)`, `μ=|Ω|−s`), which is the airtight replacement for the
flawed `t`‑length subtraction (gap identified and resolved in §3.3–§3.4);
**(3)** §3.5 (interior analyticity + Morse–Sard, intersected with the
positive‑measure good set).

---

## 5. Honest status of every constant and every gap

**Constants (all dimensional).**

- `c_W^- = 1/(n²ω_n)`, `c_W^+ = 2^{1−2/n}/(n²ω_n)` — weight bounds on
  `J₀` (Lemma 2.1). Ratio `≤ 2`.
- `κ⁻ = n²ω_n·2^{−(1−2/n)}`, `κ⁺ = n²ω_n` — volume‑weight bounds on the
  slab (3.7). Ratio `≤ 2`.
- `C_n^{(1)} = 2` — bad‑set Lebesgue length constant (3.1),
  dimension‑free.
- `C_n^{(2)} = n²ω_n` — raw‑defect constant in (i), (3.11).
- Layer constant in (ii): `4` (from `λ=(4/θ)δ_T`), dimension‑free; with
  the `θ←θ/2` relabelling in (i) it becomes `8` (still dimensional‑free).
  Quote `C_n/θ` with `C_n` absorbing the relabelling, e.g. `C_n=8`.

**Hypotheses on `Ω`, isolated.**

- Used: `Ω` open, `|Ω|<∞`; `|Ω|=ω_n` normalization; `u` variational
  torsion function. That is **all** (matches `agent1` §0/§8: the
  identity is unconditional on `Ω` of finite measure).
- **Not** used: any regularity of `∂Ω` (no `C^{2,α}`, no Lipschitz, no
  finite perimeter of `∂Ω`); boundedness of `Ω`; connectedness;
  selection principle; Brandolini with `L^∞` assumed. Interior
  analyticity of `u` (conclusion (iii)) is automatic from `−Δu=1` on the
  open set `Ω` and touches only inner levels.
- The §6 variance identity (V) and the divergence identity (β) are on
  **reduced boundaries `∂*E_t`** for a.e. `t`; no submanifold structure
  of `{u=t}` is assumed for (i)–(ii). Smoothness of `Σ_{t̂}` is *earned*
  in (iii) for the *single selected* regular `t̂`, never assumed.

**Residual gaps — stated plainly.**

1. **The weight does NOT degenerate near the boundary, so the `1/θ`
   Chebyshev conclusion is correct as stated.** Concretely: on the
   near‑boundary window `J₀={m≥|Ω|/2}` the density `dν/dt` is pinched in
   `[c_W^-,c_W^+]` with ratio `≤2` (Lemma 2.1), because `m(t)→|Ω|` there
   (so `m^{1−2/n}` is two‑sided) — *not* because `δ_T` is small. The
   route’s `(C_n/θ)δ_T` conclusion holds verbatim; **no degeneration,
   no change to the Chebyshev statement.** (The brief asked this be
   reported if false — it is **true**.)

2. **The layer ↔ level bookkeeping: the *naive* `t`-length argument has
   a real gap; the *volume‑variable* argument closes it with no gap.**
   I flagged explicitly (§3.2–§3.3) that for an arbitrary open `Ω` there
   is **no unconditional lower bound on the `t`-length `|W_λ|`** of the
   small‑layer window (thin‑tentacle: `α=∫|∇u|⁻¹` unbounded, layer can
   have measure `≫ t`), so the route’s literal phrase "good level inside
   any *near‑boundary window of length* `>(C_n/θ)δ_T`" is **heuristic in
   the `t` variable**. The rigorous mechanism is Markov in the **volume
   variable `s=m(t)`**, where the layer is *exactly linear*
   (`μ=|Ω|−s`), so the small‑layer window is a slab of *exact*
   `ds`-length `λ` and the defect mass is also a `ds`-integral
   (I_s′). Markov‑length subtraction is then legitimate, the good set
   has `ds`-measure `≥λ/2>0`, and pulls back to positive `t`-measure
   (strict monotone AC change, `agent1` Lemma 3c). **This is a complete
   proof; the only "gap" is in the heuristic `t`-phrasing, which we do
   not use.** The quantity (ii) `|Ω∖E_{t̂}|` is exactly what Step 5 /
   Lemma 8.3 consumes, so the volume‑variable formulation is also the
   *operationally correct* one.

3. **Plateau / a.e. caveats are absorbed, not gaps.** The identity is
   a.e. in `t` (`agent1` §7): countable plateau levels of `u`,
   BV‑coarea exceptional levels, and the Sard‑critical set `N` are all
   Lebesgue‑null in `t` and excised in §3.5; the selected `t̂` avoids
   all of them because the good set has positive measure. The change of
   variable `s=m(t)` is valid off the countable plateau set
   (`agent1` Lemma 3c). No gap.

4. **Normalization caveat (honest, minor).** `δ_T:=E(Ω)−E(B)` is the
   *unnormalized* energy gap; with `|Ω|=ω_n` it equals the
   scale‑invariant Saint–Venant deficit up to the fixed factor
   `ω_n^{(n+2)/n}`, absorbed in `C_n`. If a downstream step uses the
   scale‑invariant deficit literally, multiply the constants in (ii) by
   `ω_n^{(n+2)/n}` — still dimensional. No mathematical gap, only a
   bookkeeping convention to keep consistent across Steps 1–5 (Plan 2 §8
   and `wave3-G` both use the same `δ_T:=E(Ω)−E(B)` convention, so this
   is consistent).

**Net.** Conclusions (i), (ii), (iii) of the Lemma are proved with full
rigour, all constants dimensional and tracked, under exactly the
hypotheses of `agent1` (i.e. essentially none beyond `|Ω|<∞`) plus the
nontrivial‑regime condition (NB‑θ). The only place where the route’s
informal language was inaccurate is the `dist`/`t`-length phrasing of
(ii); the rigorous and operationally correct quantity is the **layer
measure** controlled in the **volume variable**, which is precisely what
Step 5 needs. No struck machinery is used; only `D_H`, one static level,
plain Markov, interior analyticity + Sard.

---

## References (as used)

- `Plan 2/level-set-deficit-identity.md` — §1 (defects), §2 (boxed
  identity), §3 (boxed `Γ=2(E(Ω)−E(B))/|Ω|`), §6 (boxed variance (V)),
  §8 Lemma 8.2 (weight `dν`).
- `Plan 2/agent1-finite-perimeter-identity.md` — §0 Theorem and §5
  (unconditional finite‑perimeter identity), Lemma 1 (coarea, `m` AC),
  Lemma 2 (Lipschitz‑truncation flux identity), Lemma 3a–3c
  (rearrangement AC, change of variable), §7–§8 (no regularity of `∂Ω`,
  Talenti `L^∞`).
- `Plan 3/PLAN3_INTENDED_ROUTE.md` (v3) — Step 1 statement and the
  struck list (all honored).
- Talenti, *Ann. Mat. Pura Appl.* 110 (1976); Kesavan,
  *Symmetrization and Applications*, 2006 (Talenti `L^∞`).
- Sard, *Bull. AMS* 48 (1942); interior analyticity of solutions of
  `−Δu=1` (Morrey, *Multiple Integrals in the Calculus of Variations*).
- Ambrosio–Fusco–Pallara 2000; Maggi 2012 (BV coarea, sets of finite
  perimeter) — via `agent1`.
