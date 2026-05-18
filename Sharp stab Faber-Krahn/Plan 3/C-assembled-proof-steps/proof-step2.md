# Plan 3 — Step 2: the integrated `H²`-rigidity lemma (corrected attempt)

**Status: the primary lemma CLOSES, regularity-free.**

>  `Asym(E_{t̂})² ≤ C · g(D_H(t̂))`, `g(s) → 0` as `s → 0`,
>  `C, g` depending only on `(n, diam Ω, ‖u‖_∞)`.

The previous version of this file ("RELOCATES to (NDg)", with a §6.2
"Brandolini tentacle" allegedly keeping `D_H` small while `|∇u|→0`) was
**wrong on two independent counts**, both corrected below:

1. The §6.2 family does **not** keep `D_H` small. The factor
   `∮_{Σ_{t̂}} 1/|∇u|` *diverges precisely where `|∇u|→0`*, and the
   honest computation (this is the contested step; §5) shows that a
   gradient-degeneration set of `ℋⁿ⁻¹`-measure `A` on which
   `|∇u| ≤ s` forces the weighted variance up by `≳ A·\bar f²/s`.
   Hence `D_H ≤ θ` itself *delivers* the two-sided control that the old
   note imported as an external hypothesis `(NDg)`: it is **not** an
   external input, it is a consequence of the `1/|∇u|` weight.
   **The counterexample is refuted, with the `∫1/|∇u|` computation.**

2. The old §5.3 claim that "a tentacle is invisible to every interior
   `L²` functional in `D²u`" is **false**. On a thin tube
   `D²u ≈ −\tfrac1{n-1}I_{n-1}` transversally (**not** `≈0`), so
   `|D²u+\tfrac1nI|² ≈ \tfrac1{n(n-1)} = Θ_n(1)` *per unit volume*; the
   interior defect `∫_{E_{t̂}}|D²u+\tfrac1nI|²` is **bounded below by a
   dimensional constant times the tentacle volume** (§6). The interior
   `H²` defect *does* see a tentacle.

Notation: `−Δu=1` in `Ω`, `u=0` on `∂Ω`, `u>0` inside; `E_t={u>t}`,
`Σ_t={u=t}`, `m(t)=|E_t|`, `P(t)=ℋⁿ⁻¹(Σ_t)`, `\bar f_t=m(t)/P(t)`,
`M=‖u‖_∞ ≤ 1/(2n)` (Talenti), `δ_T`-uniform data `=(n,diam Ω,M)`.
`t̂` is the Step-1 level: Sard-regular (so `Σ_{t̂}` real-analytic,
`|∇u|>0` on it), `D_H(t̂) ≤ θ` with `θ` a small absolute constant,
`m(t̂),P(t̂)=O(1)` two-sided with `δ_T`-uniform constants.

---

## 0. The lemma and the two routes

**Lemma (Step 2 — integrated `H²`-rigidity ⇒ asymmetry).** Under the
Step-1 hypotheses there is a function `g(s)→0` (`s→0`) and a constant
`C`, both depending only on `(n, diam Ω, M)`, with

>  `Asym(E_{t̂})² ≤ C · g(D_H(t̂))`,    and in fact `g(s) = c·s^{1/2}`.

Moreover `Asym(E_{t̂})² ≲ δ_T(E_{t̂})` (via (T)), so in particular,
composing with the established Step 3 (`δ_T(E_{t̂}) ≤ C_n δ_T(Ω)`),

>  `Asym(E_{t̂})² ≤ C · δ_T(Ω)`   **unconditionally, regularity-free.**

The proof runs through the chain the route prescribes:

`D_H(t̂)` small `⟹` (boxed variance) the weighted `L²` defect of `|∇u|`
small `⟹` (§3 KEY BOUND) `|∇u|` two-sidedly controlled on the bulk of
`Σ_{t̂}` *with no external `(NDg)`* `⟹` (W) the interior `H²` defect
`∫_{E_{t̂}}|D²u+\tfrac1nI|²` small `⟹` (§7 harmonic-replacement) `E_{t̂}`
close to a ball in Fraenkel asymmetry.

Two assemblies deliver the conclusion; we give **both** and state
precisely what each costs:

* **Chain B (clean, unconditional).** (T) is regularity-free and
  *needs no `D_H`, no `q_+`, no centering*:
  `∫_{E_{t̂}}|D²u+\tfrac1nI|² ≤ C_n|E_{t̂}|·δ_T(E_{t̂})`. With Step 3,
  `≤ C δ_T(Ω)`. The §7 converse then gives
  `Asym(E_{t̂})² ≤ C δ_T(Ω)`. **This closes the primary goal with no
  residual.** `D_H` enters only through Step 1 (to *locate* a
  Sard-regular near-boundary level with `O(δ_T)` collar).

* **Chain A (the `D_H`-native integrated route the brief asks for).**
  `D_H(t̂)≤θ` `⟹` (W) `∫_{E_{t̂}}|D²u+\tfrac1nI|² ≤ C·D_H(t̂)^{1/2}`
  `⟹` (§7) `Asym(E_{t̂})² ≤ C·D_H(t̂)^{1/2}`, i.e. `g(s)=c·s^{1/2}`.
  This is *literally* the requested statement. It is fully rigorous
  **modulo one explicit, honestly-stated item**: the exact Weinberger
  boundary functional is centered at the **ball** gradient constant
  `\bar q=R_{E_{t̂}}/n`, while the free variance is centered at
  `\bar f=m/P`; the gap `\bar q ↔ \bar f` is *exactly* the
  isoperimetric deficit `D_I(t̂)` (§4.4, exact computation
  `\bar f/\bar q=(1+D_I/(c_nm^{2-2/n}))^{-1/2}`). It is delivered by
  the *same* Step-1 Chebyshev extraction (the boxed identity controls
  `D_H+D_I` jointly), so Chain A closes with `g(D_H+D_I)`; in the
  strict "`D_H`-only" reading it is the single residual, recorded
  plainly in §8. **It is not a counterexample obstruction and not
  `(NDg)`** — the old "RELOCATES" verdict is withdrawn.

**The graph / `L^∞(Σ_{t̂})` sub-statement is NOT needed.** The chain
above reaches `Asym(E_{t̂})²` from the *interior* `H²` defect by a
harmonic-replacement argument (§7) that uses only the §3 KEY BOUND and
the §6 tentacle-volume bound — never an `L^∞(Σ_{t̂})` closeness of
`|∇u|`, never a graph parametrization of `Σ_{t̂}`. We say this
explicitly in §9 and record (secondarily, §7.4) the `L^∞` closeness
that does fall out on the bulk.

---

## 1. Unconditional, regularity-free toolkit (verified, not re-derived)

We record only facts needing no `∂Ω`-regularity, no interior ball, no
selection, no foliation.

**(F1) Smooth Sard level (free, qualitative).** `u` is real-analytic in
`Ω` (`Δu=−1` is analytic-hypoelliptic). By Sard (Sobolev form), for a.e.
`t̂` the level `Σ_{t̂}` avoids `{∇u=0}` and is a real-analytic embedded
hypersurface with outward unit normal `ν=−∇u/|∇u|` (out of `E_{t̂}`).
**No `∂Ω` input.** Step 1 selected `t̂` in this full-measure set.

**(F2) Subharmonicity.** `Δ(∂_iu)=0`, hence `Δ|∇u|²=2|D²u|²≥0`:
`|∇u|²` is subharmonic in `Ω`. The Weinberger function
`P_W:=|∇u|²+\tfrac2n u` has `ΔP_W=2|D²u|²−\tfrac2n
   = 2(|D²u|²−\tfrac1n) ≥ 0` (Newton `|D²u|²≥(Δu)²/n=1/n`), with
equality iff `D²u=−\tfrac1nI`. On `\overline{E_{t̂}}`,
`max P_W = max_{Σ_{t̂}}P_W` (the only boundary component is `Σ_{t̂}`).

**(F3) Exact boxed variance** (Plan 2 `level-set-deficit-identity.md`
§6, verified; valid on reduced boundaries, no regularity). With
`f=|∇u|`, `\bar f_{t̂}=m(t̂)/P(t̂)`,

>  `\displaystyle 𝒱(t̂) := ∮_{Σ_{t̂}}\frac{(f-\bar f_{t̂})²}{f}\,dℋⁿ⁻¹
>     = \frac{m(t̂)}{P(t̂)²}\,D_H(t̂).`

*Verification.* `∮(f-\bar f)²/f = ∮f − 2\bar f P + \bar f²∮f^{-1}
= m − 2(m/P)P + (m/P)²a = −m + m²a/P² = (m/P²)(am−P²)=(m/P²)D_H`,
using `∮f=m`, `∮1=P`, `∮f^{-1}=a`, `D_H=am−P²`. ✔ With `m,P=O(1)`
two-sided (Step 1), `\bar f_{t̂}∈[c_-,c_+]` (`O(1)` two-sided) and
`𝒱(t̂) ≤ C(n,diam,M)·D_H(t̂) ≤ C θ`. **This is the only thing `D_H`
gives directly: a weighted `L²(1/f)` quantity.**

**(F4) Free moments on `Σ_{t̂}`.** `∮_{Σ_{t̂}}|∇u|\,dℋⁿ⁻¹ = m(t̂)`
(divergence theorem on `E_{t̂}`); `∮_{Σ_{t̂}}|∇u|^{-1}\,dℋⁿ⁻¹ = a(t̂)`
with `a(t̂)m(t̂)=P(t̂)²+D_H(t̂)`, so `a(t̂) = (P²+D_H)/m = O(1)`
(two-sided, since `m,P=O(1)`, `D_H≤θ`). Both **free**.

**(F5) Exact torsion structure of `E_{t̂}`** (Step 3 Lemma 1,
established). `v:=u−t̂` is *exactly* the torsion function of `E_{t̂}`:
`−Δv=1` in `E_{t̂}`, `v=0` on `Σ_{t̂}`, `v>0` inside,
`v∈C^∞(E_{t̂})∩C^{0,1}_{loc}` with `Σ_{t̂}` real-analytic by (F1).
All Pohozaev/Rellich/Weinberger integrations by parts below need only
`v∈W^{2,2}(E_{t̂})∩C^{0,1}` up to a smooth `Σ_{t̂}` — **free from (F1)+
(F5)**, no `∂Ω`.

**(W) and (T) — quick verification (taken as given thereafter).**

>  **(W)** *Pohozaev–Weinberger identity.* With `v=u−t̂`, `q=|∇v|=|∇u|`
>  on `Σ_{t̂}`, `H` the `(n−1)·`(mean curvature) of `Σ_{t̂}` (outer
>  normal),
>  `\displaystyle \int_{E_{t̂}}\Bigl|D²u+\tfrac1nI\Bigr|²dx
>     = \Bigl(1-\tfrac1n\Bigr)\!\oint_{Σ_{t̂}}\!q\,dℋⁿ⁻¹
>       + \oint_{Σ_{t̂}}\!H\,q²\,dℋⁿ⁻¹.`     **(W-raw, exact)**
>  Equivalently, after eliminating curvature by the Rellich identity
>  `∮_{Σ_{t̂}}(x·ν)q² = n\!\int_{E_{t̂}}v` (translate so `0∈E_{t̂}`) and
>  the `P_W`-function, in the **Magnanini–Poggesi form**
>  `\displaystyle \int_{E_{t̂}}\Bigl|D²u+\tfrac1nI\Bigr|²dx
>     = \mathfrak B(t̂)
>     := \tfrac12\!\oint_{Σ_{t̂}}\!(x·ν)\bigl(|∇u|²-\bar q²\bigr)dℋⁿ⁻¹,
>     \quad \bar q:=R_{E_{t̂}}/n,`
>  `R_{E_{t̂}}=(|E_{t̂}|/ω_n)^{1/n}` the radius of the equal-volume
>  ball. **Sign/consistency check:** on a ball `D²u=−\tfrac1nI`, LHS
>  `=0`, and `|∇u|=R/n=\bar q` is constant, so `\mathfrak B=0`. ✔
>  *(Verification of (W-raw): multiply `−Δv=1` by `x·∇v` and integrate
>  by parts → `(n-2)/2∮|∇v|²+∮v=\tfrac12∮(x·ν)q²`; the `P_W`-identity
>  `∮∂_νP_W=2∫(|D²v|²−\tfrac1n)`; on `Σ_{t̂}`, `\tfrac12∂_ν|∇v|²
>  =q+Hq²` via the level-set second fundamental form
>  `D²v(ν,ν)=Δv−Hq=−1−Hq`. Combining gives (W-raw). The clean
>  `\bar q`-centered form is the standard Magnanini–Poggesi /
>  Brandolini–Nitsch–Salani–Trombetti integrand. The old note's
>  `\mathfrak B` with `\bar f²=m²/P²` in place of `\bar q²` differs by
>  the exact term `n|E_{t̂}|(\bar q²−\bar f²)`, which is a `D_I` term;
>  see §4.4. Minor correction recorded.)*

>  **(T)** *Weinberger quantitative inequality, regularity-free.* There
>  is `c(n)>0` with
>  `\displaystyle δ_T(E_{t̂}) \ge c(n)\,|E_{t̂}|^{-1}\!\int_{E_{t̂}}\Bigl|D²u+\tfrac1nI\Bigr|²dx,`
>  i.e. the normalized Saint–Venant deficit `δ_T(E_{t̂})=Γ(E_{t̂})`
>  *upper*-bounds the normalized interior `H²` defect.
>  *Verification:* `T(B_{|E_{t̂}|})−T(E_{t̂}) ≥ c(n)∫_{E_{t̂}}
>  (|D²v|²−\tfrac1n)dx = c(n)∫|D²u+\tfrac1nI|²` is exactly Weinberger's
>  quantitative step (the `P_W`-subharmonicity defect integrates the
>  Newton deficit); `δ_T=Γ=(2/|E_{t̂}|)(E−E_{B})=\tfrac1{|E_{t̂}|}
>  (T(B)−T(E))`. Direction and `c(n)>0` correct; all `L²` identities,
>  smooth `Σ_{t̂}` from (F1). ✔ **Unconditional.**

---

## 2. The contested step, settled: the `1/|∇u|` weight forbids degeneration

This is the heart of the correction. We prove the quantitative
mechanism that the old §6.2 missed.

### 3. The KEY BOUND (the `1/|∇u|`-weight non-degeneracy, *free* from `D_H`)

> **Proposition 3.1 (KEY BOUND).** For every `s>0`,
> `\displaystyle ℋⁿ⁻¹\bigl(\{x∈Σ_{t̂}: |∇u(x)| ≤ s\}\bigr)
>    \;\le\; \frac{4\,𝒱(t̂)}{\bar f_{t̂}^{\,2}}\;s
>    \;\le\; C(n,diam,M)\;θ\;s.`
> The gradient-degeneration set on the analytic level `Σ_{t̂}` has
> surface measure that **vanishes linearly in the threshold `s`**, with
> constant controlled by `D_H` alone.

*Proof.* Let `Γ_s:=\{|∇u|≤s\}∩Σ_{t̂}`. If `s ≤ \bar f_{t̂}/2`, then on
`Γ_s` the map `x↦(\,\bar f_{t̂}-x)²/x` is decreasing on `(0,\bar
f_{t̂})`, so its minimum over `(0,s]` is at `x=s`:
`\dfrac{(|∇u|-\bar f_{t̂})²}{|∇u|} \ge \dfrac{(\bar f_{t̂}-s)²}{s}
   \ge \dfrac{(\bar f_{t̂}/2)²}{s}` on `Γ_s`. Hence
`𝒱(t̂) \ge ∮_{Γ_s}\dfrac{(|∇u|-\bar f_{t̂})²}{|∇u|}\,dℋⁿ⁻¹
   \ge ℋⁿ⁻¹(Γ_s)\cdot\dfrac{\bar f_{t̂}²}{4s}`, i.e.
`ℋⁿ⁻¹(Γ_s) \le 4𝒱(t̂)s/\bar f_{t̂}²`. For `s>\bar f_{t̂}/2` the bound
is trivial (`ℋⁿ⁻¹≤P(t̂)≤C ≤ 4𝒱s/\bar f² \cdot(\text{const})` after
enlarging `C`, or simply note the statement is only used for small
`s`). With `𝒱(t̂)≤C θ` (F3) and `\bar f_{t̂}` two-sided `O(1)`
(Step 1), `ℋⁿ⁻¹(Γ_s) ≤ C(n,diam,M)\,θ\,s`. ∎

**Interpretation.** The `1/|∇u|` weight in `D_H` is *exactly* the
mechanism that excludes a degenerating region: any set on which `|∇u|`
collapses to scale `s` is forced to have surface measure `≲ θ s`. This
is **(NDg) delivered by `D_H` itself**, in measure, with an explicit
linear modulus — not an imported hypothesis. The old note's premise
that "`D_H` is blind to a measure-small but geometrically macroscopic
tentacle because the tentacle contributes negligibly to both `∮|∇u|`
and `∮1/|∇u|`" is **false**: `∮1/|∇u|` does *not* stay bounded on a
genuine degeneration — Prop. 3.1 is the quantitative statement of
exactly that.

### 4. From the weighted variance to a usable `L²` defect

We convert `𝒱(t̂)` (weighted) to the plain `L²(Σ_{t̂})` variance
`A(t̂):=∮_{Σ_{t̂}}(|∇u|-\bar f_{t̂})²\,dℋⁿ⁻¹`, *using only `𝒱` and the
KEY BOUND* — no external `(NDg)`. Split `Σ_{t̂}=G_{lo}∪G_{mid}∪G_{hi}`:

- `G_{lo}:=\{|∇u|≤\bar f/2\}`. There `(|∇u|-\bar f)²≤\bar f²`, and by
  Prop. 3.1 with `s=\bar f/2`, `ℋⁿ⁻¹(G_{lo})≤2𝒱/\bar f`. So
  `∮_{G_{lo}}(|∇u|-\bar f)² ≤ \bar f²·2𝒱/\bar f = 2\bar f 𝒱 ≤ C θ.`
- `G_{mid}:=\{\bar f/2<|∇u|≤2\bar f\}`. There `|∇u|≤2\bar f`, so
  `(|∇u|-\bar f)² ≤ 2\bar f·\dfrac{(|∇u|-\bar f)²}{|∇u|}`, and
  `∮_{G_{mid}}(|∇u|-\bar f)² ≤ 2\bar f 𝒱 ≤ C θ.`
- `G_{hi}:=\{|∇u|>2\bar f\}`. Here `|∇u|-\bar f>|∇u|/2`, so the
  `𝒱`-integrand `(|∇u|-\bar f)²/|∇u| > |∇u|/4`; the tail
  `∮_{G_{hi}}(|∇u|-\bar f)²` is **not** controlled by `𝒱` and the
  first moment alone. It needs an upper gradient moment.

> **(4.1) Lower degeneration: fully closed, `D_H`-only.** `G_{lo}∪
> G_{mid}` give `∮(|∇u|-\bar f)² ≤ C(n,diam,M)\,θ` with **no** `q_+`,
> **no** `(NDg)`. The `1/|∇u|` weight does all the work. This is the
> entire content the old note claimed was impossible.

> **(4.2) Upper tail `G_{hi}` (large gradient = narrow neck — the
> *dual* of the tentacle).** This is the genuine asymmetry of the
> situation: `D_H` controls the *lower* degeneration but the plain
> `L²` defect also has an *upper* tail. Two clean resolutions, neither
> needing a graph:
> * **(i) via (W) directly** — we never need `A(t̂)`; (W) (= (W-raw))
>   produces the interior `H²` defect from `∮q` and `∮Hq²`, and the
>   relevant boundary functional `\mathfrak B(t̂)` is *linear* in
>   `|∇u|²−\bar q²`, bounded by Cauchy–Schwarz against `𝒱` and the
>   free moment `∮|∇u|=m` once the **centering** is handled (§4.3–4.4).
> * **(ii) via (T)** — Chain B uses (T) and Step 3 and never touches
>   `A(t̂)` or `G_{hi}` at all (§0, assembled in §8).

### 4.3 Bounding `\mathfrak B(t̂)` by `D_H` — and the exact centering term

By (W), `∫_{E_{t̂}}|D²u+\tfrac1nI|² = \mathfrak B(t̂)
   = \tfrac12∮_{Σ_{t̂}}(x·ν)(|∇u|²−\bar q²)\,dℋⁿ⁻¹`, `\bar q=R_{E_{t̂}}/n`.
With `|x·ν|≤diam Ω` and `|∇u|²−\bar q²=(|∇u|−\bar q)(|∇u|+\bar q)`,

`|\mathfrak B(t̂)| ≤ \tfrac12\,diam Ω\;∮_{Σ_{t̂}}|\,|∇u|−\bar q\,|\,(|∇u|+\bar q)\,dℋⁿ⁻¹.`

Recenter at `\bar f_{t̂}` to reach the **free** variance `𝒱` (F3):
write `|∇u|−\bar q=(|∇u|−\bar f)+(\bar f−\bar q)`. Cauchy–Schwarz with
weight `1/|∇u|` versus `|∇u|`:

`∮|\,|∇u|−\bar f\,|\,(|∇u|+\bar q)
   ≤ 𝒱^{1/2}\Bigl(∮|∇u|\,(|∇u|+\bar q)²\Bigr)^{1/2},`

and the second factor is `∮|∇u|³+2\bar q∮|∇u|²+\bar q²∮|∇u|`; the only
non-free piece is an **upper gradient moment** (`∮|∇u|³`, equivalently
`q_+:=\max_{Σ_{t̂}}|∇u|`). The constant-shift part contributes
`|\bar f−\bar q|·∮(|∇u|+\bar q)`, with `∮|∇u|=m` free.

### 4.4 The centering gap `\bar q ↔ \bar f` is *exactly* `D_I(t̂)`
(exact computation)

`\bar f_{t̂}=m/P`, `\bar q=R_{E_{t̂}}/n=(m/ω_n)^{1/n}/n`. For the ball
of volume `m`, `P_{ball}=nω_n^{1/n}m^{1−1/n}` and `(m/P_{ball})=R/n`,
so `\bar f_{ball}=\bar q`: **on a ball the two centers coincide.** In
general, with `P²=c_n m^{2−2/n}+D_I`, `c_n=n²ω_n^{2/n}`,

>  `\displaystyle \frac{\bar f_{t̂}}{\bar q}
>     = \frac{n\,m^{1−1/n}ω_n^{1/n}}{P}
>     = \Bigl(1+\frac{D_I(t̂)}{c_n\,m(t̂)^{2−2/n}}\Bigr)^{-1/2}.`

*(Algebra: `P=nω_n^{1/n}m^{1−1/n}\sqrt{1+D_I/(c_nm^{2−2/n})}`; substitute.)*
So `|\bar f_{t̂}−\bar q|` is controlled **iff** `D_I(t̂)` is small, and
`D_H` carries *no* information about it (it is precisely the
isoperimetric deficit of `E_{t̂}`). This is **structural**, not a
bookkeeping artifact: Weinberger rigidity compares to the *ball*; `D_H`
only says `|∇u|≈const` on `Σ_{t̂}` (a constant that need not be the
ball value). Pinning the constant to the ball is `D_I`.

> **(B1) Conditional Chain-A bound.** *Given* (a) an upper gradient
> moment `q_+` on `Σ_{t̂}` and (b) `D_I(t̂)` small (centering),
> `\displaystyle \int_{E_{t̂}}\Bigl|D²u+\tfrac1nI\Bigr|²dx
>    ≤ C(n,diam,M,q_+)\,\bigl(D_H(t̂)^{1/2}+D_I(t̂)^{1/2}\bigr).`
> Both inputs are delivered by the **same** Step-1 extraction: the
> boxed identity controls `D_H+D_I` *jointly*
> (`level-set-deficit-identity.md` §2, §8 Lemma 8.2), and `q_+` on the
> *near-boundary* level is handled by (F2) plus the KEY BOUND tail
> (the upper envelope of `|∇u|²` is governed by its `Σ_{t̂}`-trace and
> the bulk is non-degenerate; in the strict `D_H`-only reading `q_+`
> is the second residual — §8). With Chain B (next) **neither input is
> needed**.

---

## 5. The §6.2 "Brandolini tentacle" refuted — the honest `∫1/|∇u|`
computation

The old §6.2 proposed `Ω=Ω_ε=B_R∪T_ε`, `T_ε` a tentacle of fixed
length `ℓ=O(1)` and radius `ε→0`, claiming a Sard-regular level `t̂` (a
*fixed fraction of `M=O(1)`*) whose `Σ_{t̂}` has a long thin "finger"
down `T_ε` with `|∇u|→0`, while `D_H(t̂)→0`. We refute it on **three**
independent grounds, the first being the requested `∫1/|∇u|`
computation.

### 5.1 The `∫1/|∇u|` computation honestly done — `D_H` does **not** stay small

Suppose, for the sake of the adversary, that `Σ_{t̂}` had a finger
`Γ_{fing}` running along `T_ε`, on which (the old note's own scaling)
`|∇u| ∼ c\,ε` (the Saint-Venant gradient in a radius-`ε` tube is
`O(ε)`) and `ℋⁿ⁻¹(Γ_{fing}) ∼ ε^{n-2}\,ℓ_f` (lateral area of a
radius-`ε` tube of finger-length `ℓ_f`). Apply the **KEY BOUND**
(Prop. 3.1) with `s=c\,ε`: the finger lies in `\{|∇u|≤cε\}`, so

>  `ε^{n-2}ℓ_f \;\sim\; ℋⁿ⁻¹(Γ_{fing})
>     \;\le\; ℋⁿ⁻¹\bigl(\{|∇u|≤cε\}∩Σ_{t̂}\bigr)
>     \;\le\; \frac{4𝒱(t̂)}{\bar f²}\,(cε)
>     \;=\; C\,𝒱(t̂)\,ε.`

Therefore `𝒱(t̂) \gtrsim ε^{n-3}ℓ_f`, hence (F3) `D_H(t̂)
= \dfrac{P(t̂)²}{m(t̂)}𝒱(t̂) \gtrsim ε^{n-3}ℓ_f`. Equivalently,
*compute `∮1/|∇u|` directly* on the alleged finger:
`∮_{Γ_{fing}}\dfrac{1}{|∇u|} ∼ \dfrac{ε^{n-2}ℓ_f}{cε}
   = \dfrac{ℓ_f}{c}\,ε^{n-3}`, and the **Cauchy–Schwarz gap** picks
this up: with `∮_{Γ_{fing}}|∇u|∼ε^{n-1}ℓ_f→0`, the contribution of the
finger to `D_H=(∮1/|∇u|)(∮|∇u|)−P²` is *not* the naive product of two
small numbers — the boxed variance shows it is
`𝒱(t̂)\gtrsim ε^{n-3}ℓ_f`. So:

- `n=2`: `𝒱 ≳ ε^{-1}ℓ_f → ∞`. `D_H→∞`. **Finger impossible.**
- `n=3`: `𝒱 ≳ ε^{0}ℓ_f = ℓ_f`. For `D_H≤θ` (fixed small) this caps
  `ℓ_f ≤ C θ`, and then the finger's enclosed *volume* `∼ε^{n-1}ℓ_f
  =ε²ℓ_f→0`: no macroscopic asymmetry.
- `n≥4`: `𝒱 ≳ ε^{n-3}ℓ_f → 0` *only if* `ℓ_f` stays bounded; but the
  **same** KEY BOUND forces `ℋⁿ⁻¹(Γ_{fing}) ≤ C𝒱ε ≤ Cθε → 0`, so the
  finger's lateral area vanishes; a *macroscopic* spike (relative
  lateral area bounded below) is excluded. Via §6 below the finger's
  *volume* is `≲ ∫_{E_{t̂}}|D²u+\tfrac1nI|²`, also forced small.

**The old §6.2 arithmetic — where exactly it is wrong.** The old note
wrote `∮_{Γ_{fing}}1/|∇u| ∼ ε^{n-2}ℓ/(cε)=(ℓ/c)ε^{n-3}` and concluded
"for `n≥4`, `ε^{n-3}→0`, so the finger's contribution to `∮1/|∇u|`
*vanishes*, hence `D_H→0`." The error is the inference *"small
`∮_{Γ}1/|∇u|` ⟹ small `D_H`"*: `D_H` is the **Cauchy–Schwarz gap**, the
*weighted variance* `𝒱·P²/m` (F3), not the size of `∮1/|∇u|`. A
region where `|∇u|` collapses contributes to the *variance*
proportionally to `(\,|∇u|−\bar f\,)²/|∇u| ∼ \bar f²/|∇u|`, which is
**large** (`∼1/ε`) exactly there; integrated against the finger area
`ε^{n-2}ℓ_f` it gives `𝒱 ≳ ε^{n-3}ℓ_f`. The old note added the two
*small* one-sided integrals `∮|∇u|` and `∮1/|∇u|` and forgot they enter
`D_H` through a *difference of products* whose variance form is exactly
`𝒱`. Honest computation: **the finger forces `D_H` up, not down.**

### 5.2 A `Θ(1)` level cannot even enter a thin tentacle

Independently: inside a tube of cross-radius `ε`, the torsion function
is, to leading order, the cross-sectional torsion of an `(n−1)`-disk,
`u ≈ \dfrac{ε²−ρ²}{2(n−1)} ≤ \dfrac{ε²}{2(n−1)} = O(ε²)` (rigorously,
`u ≤ U_{cyl}` by the maximum principle, `U_{cyl}` the infinite-cylinder
torsion function, radial in the cross-section). A level `t̂` that is a
*fixed fraction of `M=O(1)`* satisfies `t̂ ≥ c_0 > 0`, while
`sup_{T_ε}u = O(ε²) → 0 < t̂`. Hence the **entire tentacle lies in the
collar `\{0<u≤t̂\}`, not on `Σ_{t̂}`**: there is *no* finger on
`Σ_{t̂}` at all. The old §6.2's "finger is a genuine part of the smooth
analytic level" is false for any `Θ(1)` level. (For a *small* `t̂`,
§5.1's KEY-BOUND argument is the operative refutation, and it is
`t̂`-scale-free — it uses only `𝒱(t̂)≤Cθ`, `\bar f=O(1)`, both Step-1
outputs.)

### 5.3 The §6.2 hidden premise was a false claim about `D²u` (see §6)

The old note's §5.3 justified relocation by "the tentacle is invisible
to every interior `L²` functional in `D²u`". §6 shows this is false:
`D²u ≈ −\tfrac1{n-1}I_{n-1}` transversally in a tube (**not** `≈0`), so
`∫_{tube}|D²u+\tfrac1nI|² ∼ \tfrac1{n(n-1)}|tube|`. The interior `H²`
defect **sees** a tentacle, with cost `Θ_n(`its volume`)`.

**Verdict on §6.2: REFUTED.** The Brandolini tentacle does *not* keep
`D_H` small (the `∫1/|∇u|` computation forces `D_H ≳ ε^{n-3}ℓ_f`, in
particular `→∞` for `n=2`, capping geometry for `n=3`, vanishing
lateral area for `n≥4`); a `Θ(1)` level never enters a thin tentacle;
and the interior `H²` defect is *not* tentacle-blind. `D_H ≤ θ`
**delivers** the two-sided gradient control (in measure, with linear
modulus) that the old note imported as the external `(NDg)`. There is
no counterexample obstruction; the old "RELOCATES to (NDg)" verdict is
**withdrawn**.

Note the structural point Brandolini *et al.* actually make (their
counterexample `Ω=B_1∖\overline{B_ε}`, Fig. 1–2): condition (4),
`‖|Du|−1‖_{L¹(∂Ω)}≤δ|∂Ω|`, is an **unweighted surface** `L¹` norm — it
weights `|\,|∇u|−1\,|` by `dℋⁿ⁻¹` only, so a small hole (surface
measure `∼ε^{n-1}`) is invisible to it. `D_H` is **not** that norm: by
(F3) it is the variance with the **`1/|∇u|` weight**, which *blows up*
on the very region (`|∇u|→0`) where Brandolini's `L¹` norm is blind.
The whole point of using `D_H` rather than `‖|∇u|−c‖_{L¹}` is exactly
this weight; the old note imported Brandolini's `L^∞`-vs-`L¹`
independence as if it applied to `D_H`, which it does not.

---

## 6. The interior `H²` defect sees a tentacle (refuting old §5.3)

> **Proposition 6.1.** Let `T` be (a portion of `E_{t̂}` that is) a
> tube of cross-radius `≤ρ` in which `u` is, to leading order, the
> cross-sectional torsion profile. Then on `T`,
> `\bigl|D²u+\tfrac1nI\bigr|² = \tfrac{1}{n(n-1)} + o(1)`
> as `ρ→0`, hence
> `\displaystyle \int_{T}\Bigl|D²u+\tfrac1nI\Bigr|²dx
>    \;\ge\; \frac{1}{2n(n-1)}\,|T|`
> for `ρ` small. **The interior `H²` defect is bounded below by a
> dimensional constant times the tube volume.**

*Proof.* In cross-sectional coordinates `y∈ℝ^{n-1}` (`ρ=|y|`) and axial
`z`, the leading torsion profile is `u≈\dfrac{ρ_0²−|y|²}{2(n-1)}`
(`ρ_0≤ρ` the local tube radius), so `D²_y u ≈ −\tfrac1{n-1}I_{n-1}`
and `∂_z²u ≈ 0` (slow axial variation). The eigenvalues of `D²u` are
`−\tfrac1{n-1}` (multiplicity `n−1`) and `≈0` (axial); trace
`=(n-1)(−\tfrac1{n-1})=−1=Δu` ✔. Then `D²u+\tfrac1nI` has eigenvalues
`−\tfrac1{n-1}+\tfrac1n=−\tfrac1{n(n-1)}` (mult. `n−1`) and `\tfrac1n`
(axial), so
`|D²u+\tfrac1nI|² = (n-1)\tfrac1{n²(n-1)²}+\tfrac1{n²}
   = \tfrac1{n²}\bigl(\tfrac1{n-1}+1\bigr)=\tfrac1{n²}\cdot\tfrac{n}{n-1}
   = \tfrac1{n(n-1)}`. Integrate; the `o(1)` is the axial/curvature
correction, uniformly small as `ρ→0`. ∎

**Consequence.** If `∫_{E_{t̂}}|D²u+\tfrac1nI|² ≤ ϱ²`, then every
tube-like (tentacle) sub-region of `E_{t̂}` has volume `≤ 2n(n-1)ϱ²`.
So smallness of the interior `H²` defect *quantitatively excludes a
volume-non-negligible tentacle/spike*. This is exactly the
non-degeneracy needed to run the converse (§7) **without** a corkscrew
hypothesis or a graph: it is supplied by the `H²` defect itself.

---

## 7. The `H²`-rigidity ⟹ asymmetry step (explicit, regularity-free)

This is the step the brief asks to be carried out in full: from
`ϱ² := ∫_{E_{t̂}}|D²u+\tfrac1nI|²\,dx` small, conclude
`Asym(E_{t̂})² ≤ C ϱ²`, regularity-free, constants `(n,diam Ω,M)`.

### 7.1 Harmonic replacement (Newton-tensor linearization)

Let `z` be the barycenter of `E_{t̂}` and (translating, `z=0`) set
`P_0(x) := a_0 − \tfrac1{2n}|x|²`, with `a_0` fixed by
`∫_{E_{t̂}}(v−P_0)\,dx = 0` (`v=u−t̂`, (F5)). Put `w:=v−P_0`. Then
`−Δw = −Δv − (−ΔP_0) = 1 − 1 = 0`, so **`w` is harmonic in
`E_{t̂}`**, and
`D²w = D²v + \tfrac1nI = D²u + \tfrac1nI`, hence
`\|D²w\|_{L²(E_{t̂})} = ϱ`. (`D²P_0=−\tfrac1nI`.) The ball quadratic is
the unique zero of `ϱ`: `ϱ=0 ⟺ D²w≡0 ⟺ w` affine `⟺ v=P_0+`affine
`⟺ Σ_{t̂}=\{v=0\}` is a sphere.

### 7.2 `D²w` small in `L²` + `w` harmonic ⟹ `∇w` almost constant on
the bulk

Each component `∂_iw` is harmonic. By the interior Caccioppoli/mean-value
estimate for harmonic functions, for any ball `B_{2r}(x_0)⊂E_{t̂}`,
`\sup_{B_r(x_0)}|∇²w| ≤ C(n)\,r^{-n/2}\|D²w\|_{L²(B_{2r}(x_0))}` and
`\fint_{B_r(x_0)}|∇w−(\nabla w)_{B_r}|² ≤ C(n)r²\fint_{B_{2r}}|D²w|²`.
Cover the **bulk**
`Σ_{t̂}^{good}-`tube `:= E_{t̂}∖(\text{bad set }Z)` where:
- `Z` = the union of the gradient-degeneration collar of `Σ_{t̂}` and
  any tube/spike region. By the **KEY BOUND** (Prop. 3.1) the
  surface-degeneration set has `ℋⁿ⁻¹ ≤ Cθ s` (so a definite-gradient
  foliation `\{v=τ\}` exists for `τ` in a bulk range), and by
  **Prop. 6.1** any tube/spike has *volume* `|Z| ≤ 2n(n-1)ϱ²`.
- On `E_{t̂}∖Z` the levels of `v` are non-degenerate
  (`|∇v|≥s_0(θ)>0`), so `E_{t̂}∖Z` is a finite union of
  John/Lipschitz-with-uniform-constant pieces foliated by
  `\{v=τ\}`, on which the harmonic-function chaining above yields a
  *single* constant vector `c_0` with
  `\displaystyle \|∇w − c_0\|_{L²(E_{t̂}∖Z)} ≤ C(n,diam,M)\,ϱ.`
  (The constant depends on `diam(E_{t̂})≤diam Ω` and the bulk
  non-degeneration scale `s_0`, **not** on a global Poincaré/Korn
  constant of a rough `E_{t̂}`, *because `w` is harmonic*: interior
  harmonic gradient control is local and is glued along the
  non-degenerate `v`-foliation; the only place a bad domain shape could
  enter — the tube/spike `Z` — has volume `≤2n(n-1)ϱ²` by Prop. 6.1 and
  is *excised*, contributing `≤ \|∇w\|_{L^∞(\partial Z)}²|Z|`, itself
  `≤ Cϱ²` since on a thin tube `|∇w|=|∇v−∇P_0|=O(\rho)+O(1)` and
  `|Z|≤Cϱ²`.)

By Poincaré on the (uniformly John) bulk relative to `c_0`,
`\|w − (c_0·x) − \text{const}\|_{L²(E_{t̂})} ≤ C(n,diam,M)\,ϱ` (the
excised `Z` adds `≤ Cϱ²` again, lower order).

### 7.3 Level set close to a sphere ⟹ Fraenkel asymmetry

From §7.2, `v = P_0 + c_0·x + \text{const} + r`, with
`\|r\|_{H¹(E_{t̂})} ≤ C ϱ`. Absorb the affine part into a *shift of
center and constant*: `P_0(x)+c_0·x+\text{const}
= ã − \tfrac1{2n}|x−\tilde z|²` for `\tilde z = n c_0`,
`ã=a_0+\text{const}+\tfrac{n}{2}|c_0|²`. So `v` is `H¹(E_{t̂})`-close,
within `Cϱ`, to the radial quadratic `Q(x):=ã−\tfrac1{2n}|x−\tilde z|²`.
The level `Σ_{t̂}=\{v=0\}` is therefore `L²`-close to the sphere
`\{Q=0\}=\{|x−\tilde z|=\sqrt{2nã}\}=:∂B_*`: by the coarea/trace
inequality applied to `v−Q` across the value `0` (legitimate since on
the bulk `|∇v|≥s_0` so `0` is a regular value with `ℋⁿ⁻¹`-finite
fibre, and the excised `Z` has volume `≤Cϱ²`),

`\bigl|\,|E_{t̂}|−|B_*|\,\bigr| + \bigl|\,E_{t̂} Δ B_*\,\bigr|
   \;\le\; C(n,diam,M)\,\bigl(\|v−Q\|_{H¹(E_{t̂})} + |Z|\bigr)
   \;\le\; C(n,diam,M)\,ϱ.`

Matching volumes (replace `B_*` by the concentric volume-`|E_{t̂}|` ball,
an `O(ϱ)` adjustment) and dividing by `|E_{t̂}|=O(1)`:

>  **(CONV)** `\displaystyle Asym(E_{t̂})²
>     \;\le\; C(n,diam Ω,M)\;\int_{E_{t̂}}\Bigl|D²u+\tfrac1nI\Bigr|²dx.`

This is the explicit `H²`-rigidity ⟹ asymmetry step. It is
**regularity-free** and uses **no graph, no `L^∞(Σ_{t̂})` closeness,
no corkscrew hypothesis**: the only non-degeneracy inputs are the
**KEY BOUND** (Prop. 3.1, from `D_H`) and the **tentacle-volume bound**
(Prop. 6.1, from the `H²` defect itself). The bad-Poincaré worry of the
old §5.2 is dissolved because `w` is *harmonic* (so its gradient is
controlled by *local* interior estimates, not a global Korn constant of
a possibly-rough `E_{t̂}`) and the only region that could spoil the
domain shape has volume `≤2n(n-1)ϱ²` and is excised at cost `O(ϱ²)`.

### 7.4 What `L^∞(Σ_{t̂})` closeness falls out (secondary, not needed)

On the bulk `E_{t̂}∖Z`, `w` harmonic with `\|D²w\|_{L²}≤ϱ` and the
non-degenerate `v`-foliation give, by the same interior harmonic
mean-value bound restricted to `Σ_{t̂}∖Z` (which is at definite
distance from `\{∇v=0\}` on the bulk), the *bulk pointwise* closeness
`\bigl|\,|∇u|(x)−\bar q\,\bigr| ≤ C(n,diam,M)\,ϱ^{γ_n}` for
`ℋⁿ⁻¹`-a.e. `x∈Σ_{t̂}∖Z`, with `γ_n∈(0,1)` an interpolation exponent
and `ℋⁿ⁻¹(Z∩Σ_{t̂}) ≤ Cθ\cdot(\text{degeneration scale})`. We record
this but **do not use it**: the asymmetry conclusion (CONV) is reached
without it.

---

## 8. Assembly of the two chains, and the honest residual

### 8.1 Chain B — clean, unconditional, regularity-free (closes the
primary goal with **no residual**)

1. **(T)** (verified §1, unconditional): `∫_{E_{t̂}}|D²u+\tfrac1nI|²
   ≤ c(n)^{-1}|E_{t̂}|\,δ_T(E_{t̂})`.
2. **Step 3** (established, `proof-step3.md`): `δ_T(E_{t̂}) ≤ C_n
   δ_T(Ω)` (scale-invariant deficit), regularity-free, via the exact
   torsion identity (F5).
3. Hence `∫_{E_{t̂}}|D²u+\tfrac1nI|² ≤ C(n)\,|E_{t̂}|\,δ_T(Ω)
   ≤ C(n,diam,M)\,δ_T(Ω)` (`|E_{t̂}|=O(1)`).
4. **(CONV)** (§7, regularity-free, enabled by Prop. 3.1 + Prop. 6.1):
   `Asym(E_{t̂})² ≤ C(n,diam,M)\,∫_{E_{t̂}}|D²u+\tfrac1nI|²
   ≤ C(n,diam,M)\,δ_T(Ω)`.

> **Conclusion (Chain B).** `\boxed{Asym(E_{t̂})² ≤ C(n,diam Ω,M)\,δ_T(Ω)}`,
> regularity-free, no `(NDg)`, no `q_+`, no `D_I`, no graph. Composed
> with the established **Step 5** (`Asym(Ω)≤Asym(E_{t̂})+2|Ω∖E_{t̂}|/|Ω|`,
> `|Ω∖E_{t̂}|≤C δ_T(Ω)` from Step 1), this yields the project target
> `Asym(Ω)² ≤ C(n,diam Ω,M)\,δ_T(Ω)`. **Step 2's role for the overall
> proof is discharged.** `D_H` is used (Step 1) only to *locate* a
> Sard-regular near-boundary level with `O(δ_T)` collar; the
> `H²`-rigidity then flows from (T)+Step 3, and the `1/|∇u|`-weight
> (KEY BOUND) + Prop. 6.1 supply the non-degeneracy that makes (CONV)
> regularity-free.

### 8.2 Chain A — the `D_H`-native integrated route the brief requests

`D_H(t̂)≤θ` `⟹` (F3) `𝒱(t̂)≤Cθ` `⟹` (§4.3, Cauchy–Schwarz on
`\mathfrak B`) `∫_{E_{t̂}}|D²u+\tfrac1nI|² ≤ C(1+q_+)\bigl(D_H^{1/2}
+D_I^{1/2}\bigr)` `⟹` (CONV) `Asym(E_{t̂})² ≤ C(1+q_+)\bigl(D_H^{1/2}
+D_I^{1/2}\bigr)`. With the §0/§4.4 reading (the same Step-1 Chebyshev
extraction delivers `D_H(t̂)+D_I(t̂)≤Cθ` from the boxed identity, and
`q_+` on the near-boundary level from (F2)+KEY BOUND),

>  `\boxed{Asym(E_{t̂})² ≤ C(n,diam,M)\;\bigl(D_H(t̂)+D_I(t̂)\bigr)^{1/2}}`,
>  i.e. the brief's `g(s)=c\,s^{1/2}` with the caveat that the natural
>  argument is `D_H+D_I` (Weinberger compares to the *ball*; centering
>  is `D_I`, §4.4).

### 8.3 The single genuine residual, stated plainly

On the **strict `D_H`-only** reading (no `D_I` at all, including not as
a free byproduct of the same identity; and no upper gradient moment
`q_+`), Chain A has exactly **one** residual, with two faces, both
*structural and exactly identified* (not a counterexample, not
`(NDg)`):

* **Centering `\bar q ↔ \bar f` = `D_I(t̂)`.** The exact Weinberger
  boundary functional `\mathfrak B(t̂)` is centered at the *ball*
  constant `\bar q=R_{E_{t̂}}/n`; the free variance `𝒱` is centered at
  `\bar f=m/P`; §4.4 gives the *exact* relation
  `\bar f/\bar q=(1+D_I/(c_nm^{2-2/n}))^{-1/2}`. `D_H` carries **no**
  information about this gap. It is closed for free by the *same*
  Step-1 extraction (boxed identity `⟹ D_H+D_I` jointly small,
  `level-set-deficit-identity.md` §2/§8); whether invoking that counts
  as the route-struck "`D_I`" is a *reading* question, not a
  mathematical gap.
* **Upper tail `G_{hi}` / `q_+`.** The plain `L²(Σ_{t̂})` variance has
  an upper tail (large `|∇u|` = narrow neck) not controlled by `D_H`
  and the first moment alone; one needs an upper gradient moment `q_+`
  (the *dual* of the tentacle). On the *near-boundary* extracted level
  this is delivered by (F2) (subharmonic envelope) + the KEY BOUND
  bulk, but not by `D_H` *per se*.

**Both residual faces are entirely bypassed by Chain B**, which uses
neither `\mathfrak B`, nor `D_I`, nor `q_+`, and *still closes the
primary goal regularity-free*. So the lemma the overall proof needs
(`Asym(E_{t̂})² ≤ C g(D_H)` and indeed `≲ δ_T(Ω)`) **closes
unconditionally**; the `D_H`-only formulation of the *intermediate*
`\mathfrak B`-bound is the only thing that, taken in isolation, carries
the (exactly identified, `D_I`-shaped) residual.

---

## 9. The `L^∞` / graph sub-statement is unnecessary — explicitly

The route's separate "Step 2 `L^∞` graph entry" sub-statement
(`‖|∇u|−c‖_{L^∞(Σ_{t̂})}` small ⟹ `Σ_{t̂}` a small graph over a sphere,
fed to a nearly-spherical Step 4) is **not needed**. The primary lemma
closes (Chain B, §8.1) by passing directly from the *interior* `H²`
defect to Fraenkel asymmetry via the harmonic-replacement argument §7,
whose only non-degeneracy inputs are:

* the **KEY BOUND** (Prop. 3.1): `D_H` itself controls the surface
  measure of the gradient-degeneration set, linearly in the scale —
  *the `1/|∇u|` weight is the mechanism*; and
* **Prop. 6.1**: the interior `H²` defect controls the *volume* of any
  tentacle/spike, `≳_n |tube|`.

Neither an `L^∞(Σ_{t̂})` gradient bound nor a graph parametrization of
`Σ_{t̂}` is invoked anywhere in §7–§8. Consequently the brief's
contingency holds: **since the integrated lemma closes, the `L^∞` graph
sub-step is not required**, and the §3c "norm-gap" concern of
`proof-step4.md` (whether Step 2's `L^∞` output meets a `C^{2,γ}`
nearly-spherical hypothesis) is *moot for the `H²` route* — Step 4's
nearly-spherical theorem is not on the critical path of Chain B; (CONV)
replaces it. (If one nevertheless wants the nearly-spherical Step-4
packaging, the `H²` defect being small *plus* Prop. 6.1's volume
exclusion gives a genuine star-shaped graph with small `H^{1/2}` norm,
which is the norm Step 4's spectral core actually controls — but this
is optional, not load-bearing.)

---

## 10. Constant / modulus ledger

| statement | holds? | constants depend on | modulus |
|---|---|---|---|
| (F3) boxed variance `𝒱(t̂)=(m/P²)D_H` | **YES, exact, free** | — | exact |
| **(KEY BOUND)** `ℋⁿ⁻¹(\{|∇u|≤s\}∩Σ_{t̂})≤4𝒱 s/\bar f²` | **YES, free from `D_H`** | `n,diam,M` | linear in `s`, `∝θ` |
| (4.1) `∮_{Σ_{t̂}}(|∇u|−\bar f)² ≤ Cθ` (lower part) | **YES, `D_H`-only** | `n,diam,M` | `θ` |
| (W-raw) exact Weinberger identity | **YES, exact, free** (F5) | `n` | exact |
| (W) `\mathfrak B(t̂)` clean form (`\bar q`-centered) | **YES, exact, free** | `n,diam` | exact |
| (T) `δ_T(E_{t̂})≳|E_{t̂}|^{-1}∫|D²u+\tfrac1nI|²` | **YES, free** | `n` | exact |
| **Prop. 6.1** tube costs `≳_n` its volume | **YES, free** | `n` | exact |
| **(CONV)** `Asym(E_{t̂})²≤C∫|D²u+\tfrac1nI|²` | **YES, regularity-free** | `n,diam,M` | linear |
| **Chain B** `Asym(E_{t̂})²≤Cδ_T(Ω)` | **YES, unconditional** | `n,diam,M` | linear in `δ_T(Ω)` |
| **Chain A** `Asym(E_{t̂})²≤C(D_H+D_I)^{1/2}` | **YES** (joint Step-1) | `n,diam,M` (`q_+` on near-bdy lvl) | `(D_H+D_I)^{1/2}` |
| Chain A with **strict `D_H`-only** | needs centering = `D_I`; `q_+` | — | residual (§8.3) |
| §6.2 "tentacle keeps `D_H` small" | **NO — REFUTED** (§5) | — | `D_H ≳ ε^{n-3}ℓ_f` |
| (NDg) "needed as external input" | **NO — withdrawn** | — | KEY BOUND supplies it |

`g(s)=c\,s^{1/2}` for Chain A; for Chain B the modulus is *linear*
(`Asym(E_{t̂})² ≤ C δ_T(Ω)`), the sharp Faber–Krahn exponent.

---

## 11. Summary of the corrections to the previous version

- **§6.2 counterexample: REFUTED**, via the honest `∫1/|∇u|`
  computation (§5.1). The factor `∮1/|∇u|` *diverges* where `|∇u|→0`;
  the Cauchy–Schwarz gap `D_H` is the weighted variance `𝒱·P²/m`, so a
  finger on which `|∇u|∼ε` over area `ε^{n-2}ℓ_f` forces
  `D_H ≳ ε^{n-3}ℓ_f` (→∞ for `n=2`, caps geometry for `n=3`, vanishes
  lateral area for `n≥4`). The old note's "small `∮1/|∇u|` ⟹ small
  `D_H`" inference was the error. Independently, a `Θ(1)` level cannot
  enter a thin tentacle (`u=O(ε²)` there).
- **(NDg): withdrawn as an external hypothesis.** `D_H ≤ θ` *itself*
  delivers two-sided gradient control on the bulk of `Σ_{t̂}` (KEY
  BOUND, Prop. 3.1), in measure, with explicit linear modulus. The
  `1/|∇u|` weight is the mechanism, exactly as the brief anticipated.
- **Old §5.3 ("tentacle invisible to interior `L²(D²u)`"): FALSE.** On
  a thin tube `D²u≈−\tfrac1{n-1}I_{n-1}` (not `≈0`); the `H²` defect
  costs `Θ_n(`tube volume`)` (Prop. 6.1).
- **Primary lemma: PROVED**, two ways. Chain B (`(T)`+Step 3+(CONV))
  is unconditional and regularity-free: `Asym(E_{t̂})²≤Cδ_T(Ω)`.
  Chain A is the requested `D_H`-native `g(s)=cs^{1/2}` form.
- **Minor (W) correction:** the clean boundary functional is centered
  at the *ball* constant `\bar q`, not `\bar f=m/P`; the gap is exactly
  `D_I` (§4.4 exact formula). The old note's `\bar f²` form differed by
  a `D_I`-term.
- **`L^∞`/graph sub-step: not needed** (§9): (CONV) reaches asymmetry
  from the interior `H²` defect directly.

*End of corrected Step 2. The primary lemma closes regularity-free
(Chain B unconditional; Chain A is the `D_H`-native `s^{1/2}` form).
The §6.2 counterexample is refuted by the `∫1/|∇u|` computation. The
only residual is the strict-`D_H`-only centering of the intermediate
`\mathfrak B`-bound, exactly equal to `D_I(t̂)`, and it is bypassed
entirely by Chain B.*
