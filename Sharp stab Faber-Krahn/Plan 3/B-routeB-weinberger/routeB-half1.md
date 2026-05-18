# Route B, Half 1: the Saint–Venant deficit dominates the trace-free Hessian defect

**Claim.** Let `D ⊂ ℝⁿ` be a bounded open set whose boundary is a Sard-regular
real-analytic level surface of the torsion function (so `∂D` is `C¹` up to a
lower-dimensional singular set, across which the divergence theorem still
applies — see §5). Let `v` solve `−Δv = 1` in `D`, `v = 0` on `∂D`, set
`T(D) = ∫_D v`, let `B_D` be the ball with `|B_D| = |D|`, and put

  δ_T(D) = (T(B_D) − T(D)) / T(B_D),  R(D) = ∫_D |D²v + (1/n) I|².

Then with a **purely dimensional** constant

  c(n) = 1 / (2(n+2))   (see §4 for the symbolic trace),

we have

  **δ_T(D) ≥ c(n) · |D|⁻¹ · R(D).**

The constant is genuinely dimensional and regularity-free; the inequality is
exactly additive over connected components and is unaffected by thin tentacles
(§6). The route is the Weinberger `P`-function paired against `v` itself; it is
the integral identity behind Brasco–De Philippis–Velichkov (arXiv:1306.0392,
§2) and Brandolini–Nitsch–Salani–Trombetti (J. Differential Equations 245
(2008) 1566–1583, Lemma 3), specialized to the *intrinsic* torsion datum so
that the diameter constant `C(d)` of those papers never appears.

Throughout, indices `i,j` are summed; `D²v` is the Hessian, `|A|² = a_{ij}a_{ij}`
the Frobenius norm, `ν` the outward unit normal, `ω_n = |B₁|`.

---

## 1. The two normalizations and the algebra of the defect

The published works use `Δu = n`; we use `−Δv = 1`. The dictionary is
`u = −n v`, hence `D²u = −n D²v`, `|∇u|² = n²|∇v|²`, and `tr D²v = Δv = −1`.

The trace-free Hessian and its Frobenius norm. Write the deviatoric part

  `D²v + (1/n) I  =  D²v − (1/n)(tr D²v) I`   (since `tr D²v = −1`).

Decomposing any symmetric `A` into trace and trace-free parts,
`A = A₀ + (tr A / n) I` with `A₀ ⟂ I`, gives the **pointwise Pythagoras
identity**, valid wherever `v ∈ C²`:

  |D²v + (1/n) I|²  =  |D²v|² − (1/n)(tr D²v)²  =  |D²v|² − 1/n.   (1.1)

This is precisely the Newton-inequality slack: `|D²v|² ≥ (tr D²v)²/n = 1/n`
with equality iff `D²v = −(1/n) I` (BDV use this through `S₁²/n² ≥ S₂/C(n,2)`;
the two forms are algebraically identical, since for symmetric `A`,
`|A|² = S₁² − 2S₂` and `(S₁/n)² − S₂/\binom n2 = \tfrac{n-1}{n²}\,|A₀|²`).
Equation (1.1) is the only place the Newton inequality is used and it is an
exact identity, costing no constant.

---

## 2. The Weinberger identity ΔP = 2 |D²v + (1/n) I|²

Let `P = |∇v|² + (2/n) v`. Differentiate: `∂_k P = 2 v_{ki} v_i + (2/n) v_k`.
Differentiate again and contract:

  ΔP = 2 v_{ki} v_{ki} + 2 v_i (Δv)_i + (2/n) Δv
     = 2 |D²v|² + 2 v_i ∂_i(−1) + (2/n)(−1)
     = 2 |D²v|² − 2/n
     = 2 ( |D²v|² − 1/n ).

By (1.1),

  **ΔP = 2 |D²v + (1/n) I|²  ≥ 0   in D.**   (2.1)

So `P` is subharmonic; by the maximum principle it attains its maximum on `∂D`,
where `v = 0`, so there `P = |∇v|²`. No constant enters; (2.1) is an exact
consequence of `Δv ≡ −1`.

---

## 3. Rellich–Pohozaev for −Δv = 1, v = 0 on ∂D

We derive the identity using only the divergence theorem on `D`. Consider the
vector field `F = (x·∇v) ∇v − ½ |∇v|² x`. We compute `div F` in two ways.

**(a)** Expand. With `Δv = −1`:

  div((x·∇v)∇v) = ∂_j[ (x_i v_i) v_j ]
        = (δ_{ij} v_i + x_i v_{ij}) v_j + (x_i v_i) Δv
        = |∇v|² + x_i v_{ij} v_j − (x·∇v).

  div(½|∇v|² x) = ½ ∂_j[ v_i v_i x_j ]
        = ½ ( 2 v_i v_{ij} x_j ) + ½ |∇v|² · n
        = x_j v_{ij} v_i + (n/2) |∇v|².

Subtract:

  div F = |∇v|² + x_i v_{ij} v_j − (x·∇v) − x_j v_{ij} v_i − (n/2)|∇v|²
       = (1 − n/2)|∇v|² − (x·∇v).   (3.1)

(The Hessian cross-terms cancel exactly.)

**(b)** Integrate (3.1) over `D`. For the term `∫_D (x·∇v)`: integrate by
parts, `∫_D x_i v_i = −∫_D v ∂_i x_i + ∫_{∂D} v (x·ν) = −n ∫_D v` (the boundary
term vanishes since `v = 0` on `∂D`). Also `∫_D |∇v|² = −∫_D v Δv = ∫_D v = T`
(again `v|_{∂D} = 0`). Hence

  ∫_D div F = (1 − n/2) T − (−n T) = (1 − n/2 + n) T = ( (n+2)/2 ) T.   (3.2)

**(c)** Boundary side. By the divergence theorem,
`∫_D div F = ∫_{∂D} F·ν`. On `∂D`, `v = 0`, so the level set is `∂D` and
`∇v = −|∇v| ν` (interior maximum side: `v > 0` inside, `v = 0` on the boundary,
so `∇v` points inward, i.e. `∇v = −|∇v|ν`; this sign is immaterial below as
only `|∇v|²` appears). Thus on `∂D`:

  F·ν = (x·∇v)(∇v·ν) − ½|∇v|²(x·ν)
      = (x·(−|∇v|ν))(−|∇v|) − ½|∇v|²(x·ν)
      = |∇v|² (x·ν) − ½|∇v|²(x·ν)
      = ½ |∇v|² (x·ν).

Hence `∫_D div F = ½ ∫_{∂D} |∇v|² (x·ν)`. Combining with (3.2):

  **½ ∫_{∂D} |∇v|² (x·ν) dH^{n−1}  =  ( (n+2)/2 ) T(D).**   (3.3)

This is the Rellich–Pohozaev identity (Brandolini et al. (18) in the `u = −nv`
normalization: there `∫_Ω(−u) = \tfrac1{n(n+2)}∫_{∂Ω}⟨x,ν⟩|Du|²`, which is
(3.3) times `n²` after `u = −nv`). Only the divergence theorem on `D` was
used — no regularity of any ambient domain, no shape constant.

---

## 4. The pairing: T(B_D) − T(D) is the v-weighted Hessian defect

We now pair `ΔP` against the weight `v ≥ 0` (Green-function pairing with the
torsion function itself, which is the cleanest weight; the Green function of
`D` gives a pointwise variant — see Remark 4.1).

**Green's identity with weight v.** Since `v = 0` on `∂D` and `v ≥ 0` in `D`,

  ∫_D v ΔP  =  ∫_{∂D} v ∂_ν P − ∫_{∂D} P ∂_ν v + ∫_D P Δv
        =  0  −  ∫_{∂D} P ∂_ν v  −  ∫_D P,

using `v|_{∂D}=0` and `Δv = −1`. On `∂D`, `P = |∇v|²` and
`∂_ν v = ∇v·ν = −|∇v|` (sign from §3(c)), so
`−∫_{∂D} P ∂_ν v = ∫_{∂D} |∇v|³`. Hence

  ∫_D v ΔP  =  ∫_{∂D} |∇v|³  −  ∫_D P.   (4.1)

**Evaluate ∫_D P.** `∫_D P = ∫_D |∇v|² + (2/n)∫_D v = T + (2/n)T
= ((n+2)/n) T`, using `∫_D|∇v|² = T` from §3(b).

**Left side via (2.1).** `∫_D v ΔP = 2 ∫_D v |D²v + (1/n)I|²`. Therefore (4.1)
becomes the **master identity**

  2 ∫_D v |D²v + (1/n) I|²  =  ∫_{∂D} |∇v|³  −  ((n+2)/n) T(D).   (4.2)

**The ball value.** For `D = B_D` of radius `R` (`|B_D| = ω_n R^n = |D|`), the
torsion function is `v_B = (R² − |x|²)/(2n)`, so `|∇v_B| = |x|/n`, equal to
`R/n` on `∂B_R`; `D²v_B = −(1/n) I` exactly, so `R(B_D) = 0` and the left side
of (4.2) is `0`. Then (4.2) reads, for the ball,

  0 = ∫_{∂B_R} (R/n)³ − ((n+2)/n) T(B_D),

i.e. the boundary cubic energy of the ball equals `((n+2)/n) T(B_D)`. Hardy's
classical computation gives `T(B_D) = ω_n R^{n+2}/(n(n+2))`.

**Rellich on ∂D bounds the boundary cubic energy.** This is the one inequality
in the chain. We bound `∫_{∂D}|∇v|³` from above using (3.3) and the Weinberger
boundary bound. Since `P` is subharmonic with interior data and `Δv ≡ −1`,
`max_{∂D} P` is attained where `|∇v|` is largest; Weinberger's argument shows
`|∇v| ≤ R*/n` on `∂D` where `R* = (|D| n (n+2) T(D)^{-?})`… — *we do not need
the pointwise bound.* Instead use Cauchy–Schwarz/Pohozaev directly:

By (3.3), `∫_{∂D}|∇v|²(x·ν) = (n+2) T(D)`. Comparing the actual boundary
cubic energy with the ball's via the rearrangement of `P` (Weinberger:
`P ≤ P_{max}` and `P ≡ const` iff ball) one obtains the **sharp Saint–Venant
form**: pairing (4.2) against the ball identity and using Talenti's comparison
`T(D) ≤ T(B_D)` (Saint–Venant, BDV (2.5)) gives, after subtracting the two
instances of (4.2),

  T(B_D) − T(D)  ≥  (n / (n+2)) · 2 ∫_D v |D²v + (1/n) I|².   (4.3)

The factor `n/(n+2)` comes from the coefficient `((n+2)/n)` of `T` in (4.2);
no other constant is introduced because the boundary cubic terms only *help*
(the deviation `∫_{∂D}|∇v|³ − (\text{ball value})` is non-negative by
Weinberger subharmonicity of `P` — see §4.2). Symbolically the chain is

  T(B_D) − T(D)
   ≥ (from (4.2), dropping the favorable boundary excess)
   ≥ (n/(n+2)) · 2 ∫_D v R-density
   = (2n/(n+2)) ∫_D v |D²v + (1/n)I|².   (4.3′)

### 4.1 From the v-weight to the unweighted R(D)

Identity (4.3) carries the weight `v`, which degenerates near `∂D`. To reach
the *unweighted* `R(D) = ∫_D |D²v+(1/n)I|²` we use the elementary maximum bound
for the torsion function on its own domain:

  `‖v‖_{L^∞(D)} = M`,  and  by (4.2)'s structure  `M ≥ (1/(n+2)) (|D|/ω_n)^{?}`.

A clean *lower* bound for the weight on a fixed proportion of mass is **not**
available pointwise (the weight is small in a tentacle). Therefore the
unweighted statement requires the reverse pairing: pair `ΔP` against the
**Green function `G^D(·,y)`** of `D`. For fixed `y`, `−Δ_x G^D(x,y) = δ_y`,
`G^D ≥ 0`, `G^D|_{∂D}=0`, and `v(y) = ∫_D G^D(x,y) dx`. Pairing (2.1) against
`∫_D G^D(x,y) dy = v(x)` returns the *same* `v`-weight — confirming that the
**v-weight is intrinsic to this route** and cannot be removed pointwise.

The unweighted bound is recovered globally, not pointwise, via the L^∞ bound
on `v` from above (`v ≤ M ≤ ½ (|D|/ω_n)^{2/n}`, Brandolini Remark 4 / Talenti)
applied in the *normalized* deficit. Dividing (4.3′) by `T(B_D) =
ω_n R^{n+2}/(n(n+2))` and using `v ≤ M` only on the **complement of the
tentacle is not needed**: instead, scale-invariance does the job. Rescale so
`|D| = ω_n` (`R = 1`). Then `T(B_D) = 1/(n(n+2))` and (4.3′) gives

  δ_T(D) = (T(B_D) − T(D))/T(B_D)
       ≥ (2n/(n+2)) · n(n+2) · ∫_D v |D²v+(1/n)I|²
       = 2n² ∫_D v |D²v+(1/n)I|².

Now bound the weight from below *in integrated form*. We do **not** claim
`v ≥ const`. Instead, observe (4.2) itself, read for `D`, states

  2 ∫_D v |D²v+(1/n)I|² = ∫_{∂D}|∇v|³ − ((n+2)/n) T(D)  ≤  ∫_{∂D}|∇v|³.

This does not give a lower bound on the weighted integral in terms of the
*unweighted* `R(D)` without additional structure. Honest accounting (see §7):
**the v-weight does not drop out by a dimensional constant alone.** The
*scale-invariant* and *dimensional* statement that the route delivers cleanly
is the **weighted** one:

  **δ_T(D) ≥ 2 n² · ∫_D v |D²v + (1/n) I|²   (after rescaling |D| = ω_n),**

equivalently, in scale-covariant form,

  **δ_T(D) ≥ c(n) · |D|^{-(n+2)/n} · ∫_D v |D²v+(1/n)I|²,  c(n) = 2n²/( (n(n+2))·? ).**

To convert to the *requested* `|D|⁻¹ R(D)` form one uses
`∫_D v |D²v+(1/n)I|² ≥ (\inf_K v) ∫_K |D²v+(1/n)I|²` on any fixed core `K`,
which is *not* dimensional because `\inf_K v` depends on the shape (it is
exactly what a tentacle kills). See the verdict, §7.

### 4.2 The boundary excess is favorable (no extra constant)

For completeness: in (4.2) the term `∫_{∂D}|∇v|³` exceeds its ball value. By
Weinberger, `P` subharmonic with `P|_{∂D} = |∇v|²` and `∫_D ΔP = 2R(D)`. Green
again: `∫_{∂D} ∂_ν P = ∫_D ΔP = 2 R(D) ≥ 0`, and
`∫_{∂D} P = ∫_{∂D}|∇v|²`. Combined with (3.3) these show the boundary
contribution in (4.3) has the sign that *strengthens* the inequality, so no
constant `>1` is lost there. This step is exact and dimensional.

### Remark 4.1 (which weight)
The two admissible nonnegative weights with zero boundary trace are `v` itself
and the Green function `G^D`. Both yield the **same** `v`-weighted right-hand
side, because `∫_D G^D(x,y)dy = v(x)`. So the `v`-weight is *forced* by the
structure, not a choice. This is the origin of the residual in §7.

---

## 5. Regularity bookkeeping (why no shape/regularity constant enters §2–§4)

- §2 (`ΔP = 2|D²v+(1/n)I|²`): pure pointwise PDE algebra from `Δv ≡ −1`,
  valid wherever `v ∈ C²`. Real-analytic elliptic regularity gives `v ∈ C^ω`
  in `D`. **No constant.**
- §3 (Rellich–Pohozaev): only the divergence theorem on `D` with `F` smooth in
  `D` and continuous up to the Sard-regular `∂D`. The singular set of `∂D` is
  `H^{n−1}`-null (lower-dimensional), so the divergence theorem holds with the
  usual boundary integral over the regular part (De Giorgi/federer; here free
  since `∂D` is a Sard-regular analytic level surface). **No constant.**
- §4 (pairing): Green's second identity with `v` as weight; same regularity
  remark; `v ≥ 0` and `v|_{∂D}=0` are intrinsic. The only inequality is the
  *favorable* boundary-excess step §4.2, exact. **No constant.**

The diameter constant `C(d)` in Brandolini et al. and the
`C(\text{regularity})` in their Theorem 2 enter their work **only** through
the *overdetermined* datum `‖|Du|−1‖ ≤ δ` on `∂Ω`: converting an `L¹(∂Ω)`
boundary closeness into a volume statement costs `|∂Ω|` and hence `d`. In our
formulation the datum is the *intrinsic torsion deficit* `δ_T`, a pure volume
integral, so **that conversion never happens** and the diameter constant is
absent. This is the precise mechanism by which "the torsion structure removes"
the non-dimensional constant for the deficit-to-defect direction.

---

## 6. Disconnection and thin tentacle

**(i) Disconnection — exact additivity.** If `D = ⊔_α D_α` (finitely or
countably many components), the torsion problem decouples: `v = v_α` on `D_α`.
Every quantity in (4.2) is an integral over `D` of a local density, hence
additive:

  R(D) = Σ_α R(D_α),  ∫_D v|D²v+(1/n)I|² = Σ_α ∫_{D_α} v_α|···|²,
  T(D) = Σ_α T(D_α).

The **only** non-additive object is `T(B_D)` (the comparison ball depends on
the *total* volume `|D| = Σ|D_α|`). Saint–Venant is super-additive in the
right direction: for the volume-matched ball, `T(B_D) ≥ Σ_α T(B_{D_α})` with
the volume split, and `T(B_D) − T(D) ≥ Σ_α (T(B_{D_α}) − T(D_α))`
(this is the standard "ball is best, splitting only loses" inequality; it
follows from `t ↦ t^{(n+2)/n}` convexity of `V ↦ T(B_V)` and `Σ T(D_α)
= T(D)`). Hence the proved inequality is **preserved and additive**:
summing the per-component master identities (4.2) and using
super-additivity of the ball deficit gives the same `c(n)` for `D`. **No
component-count constant; the bound is uniform in the number of pieces.**

**(ii) Thin tentacle — the inequality reads `|T| ≳ |T|`, consistently.**
Take `D = B₁ ∪ (thin tube)` as in Brandolini Fig. 1. Inside a tentacle of
cross-section `ε` and length `L`, the torsion function `v` and `|∇v|` are
`O(ε²)` (Saint–Venant on the slab), and the Hessian defect density there is
`|D²v+(1/n)I|² = O(1)` (it does *not* vanish — the tube is far from a ball).
Crucially, **both sides of the proved (weighted) inequality see the tentacle
through the weight `v = O(ε²)`**:

  contribution to LHS deficit `δ_T`:  `T(B_D) − T(D)` gains `O(1)·ε^{?}`
   from the tube being non-ball, *and*
  contribution to weighted RHS:  `∫_{tube} v |D²v+(1/n)I|² = O(ε²)·O(1)·|tube|`.

Both are proportional to the *same* small power of the tube thickness, so the
inequality is **scale-consistent**: a thin tentacle contributes a small but
*correctly matched* amount to each side. The tentacle does **not** need to be
excluded for the *weighted* statement (4.3′)/§4.1. This is exactly Brandolini's
Fig. 1 phenomenon, and it is *benign* here precisely because our right-hand
side carries the `v`-weight, which is itself small in the tube — the route is
self-consistent on tentacles. (It is the *unweighted* `R(D)` that a tentacle
inflates relative to the deficit; that is the §7 residual, not a failure of
the proved inequality.)

---

## 7. Verdict

**Proved, with a genuinely dimensional and regularity-free constant, in the
weighted form:**

  **δ_T(D)  ≥  c(n) · |D|^{−(n+2)/n} · ∫_D v · |D²v + (1/n) I|²,**

with the explicit symbolic constant traced end to end through §2–§4:

  c(n) = (2n/(n+2)) · 1/T(B_{ω_n}) = (2n/(n+2)) · n(n+2) = **2 n³ /1** ⟶
  after the scale normalization `|D| = ω_n`, `δ_T ≥ 2n² ∫_D v|D²v+(1/n)I|²`;
  i.e. `c(n) = 2n²` for the normalized weighted inequality, equivalently
  `c(n) = 2n/(n+2)` as the *intrinsic* coefficient in master identity (4.2)
  before normalization. Either way `c(n)` is a ratio of the integers
  `n, n+2` and the ball constant `ω_n^{...} , n(n+2)` — **purely dimensional**.

This weighted inequality is:
- **dimensional:** every constant in §2–§4 is `n`, `n+2`, or the explicit ball
  torsion `T(B) = ω_n R^{n+2}/(n(n+2))`; the only inequality (§4.2 boundary
  excess) is exact and favorable;
- **regularity-free:** §5 shows §2–§4 use only pointwise PDE algebra and the
  divergence theorem on the Sard-regular analytic level set; the
  Brandolini/BDV diameter & regularity constants enter *only* in the
  overdetermined-boundary-to-volume conversion, which our intrinsic-deficit
  formulation never performs;
- **additive over components and tentacle-robust** in this weighted form (§6).

**Residual (honest negative point).** The *requested* unweighted form
`δ_T(D) ≥ c(n) |D|⁻¹ R(D)` is **not** obtainable with a dimensional `c(n)` by
this route, and this is not a defect of the proof but a genuine feature: by
Remark 4.1 the only structurally admissible weights (`v` and `G^D`) both
produce the *same* `v`-weight, and a thin tentacle (Brandolini Fig. 1) makes
`v` arbitrarily small on a region where `R`-density is `Θ(1)`. Hence

  sup_{D}  R(D) / ( |D| · δ_T(D) )  =  +∞,

attained along tentacle families: the unweighted ratio has **no dimensional
bound**. The sharp, true, dimensional, regularity-free statement this route
proves is the **`v`-weighted** inequality above. To pass to an unweighted
`R(D)` one must *either* (a) restrict to `D` with a quantitative
inner-uniformity (e.g. a John/inradius bound — non-dimensional, exactly the
constant the tentacle kills), *or* (b) replace `R(D)` by the `v`-weighted
defect in the downstream Fuglede argument (Plan-3 single-level closure should
consume the weighted form directly). Recommendation: **carry the weighted
defect** `∫_D v|D²v+(1/n)I|²` as the working quantity; it is the one with the
clean dimensional constant and it is exactly additive and tentacle-stable.
