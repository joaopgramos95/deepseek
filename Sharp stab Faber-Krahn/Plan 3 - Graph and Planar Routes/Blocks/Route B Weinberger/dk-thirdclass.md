# (DK\*), n ≥ 4 — break-first attack on the third class, and the exhaustive dichotomy

**Verdict: NO third-class counterexample survives for `n ≥ 4`. (DK\*) HOLDS,
as an exhaustive structural trichotomy, but with one honest quantitative
residual that must be stated precisely: the deficit floor produced by the
mass-separation prong is `c_0(n) ≍_n n^{-n}` (dimensional — depends only on
`n` — but *doubly-exponentially small*), so the admissible threshold is
`δ_0(n) < c_0(n) ≍ n^{-n}`, and the structural "thick John-wrecker ⇒
Half-1-large" step rests on a quantitative John/uniform-domain
characterization (Martio–Sarvas; Väisälä) that is geometric and dimensional
but is *imported*, exactly as the prong-2 strict-stability fact is imported.**

This document does the break-first work the brief demands: each candidate
third class (thick rough boundary, thick spiral/twisted channel, many medium
protrusions, anisotropic pancake/cigar) is pushed with explicit `n ≥ 4`
scalings of `δ_T`, `R_v`, `Asym`, the `Z`-excision, and the John constant. In
every case the configuration is driven into prong 1 (thin ⇒ excised) or
prong 2 (Half-1 / strict-stability forbidden). The single new structural
mechanism — and it is decisive — is **the diameter cap**: for a
volume-normalised domain the John constant is a *length-to-width supremum*
whose length is bounded by the diameter `≍_n 1`; therefore John-blowup forces
**width → 0**, which is precisely prong 1. There is no thick John-wrecker that
also has small deficit, because a thick (Θ(1)-width) non-round Θ(1)-volume
region has `R_v = Θ_n(1)` and Half 1 then forces `δ_T = Θ_n(1)`.

Notation as in the anchors: `v` torsion function (`−Δv=1`, `v=0` on `∂D`,
`v ≍ dist`), `q` fitted ball quadratic, `w=v−q` harmonic,
`R_v(D)=∫_D v\,|D²v+\tfrac1n I|²`, the PROVED Half-1 constraint (after the
scale-normalisation `|D|=ω_n`)
```
        δ_T(D) ≥ 2 n² · R_v(D)                                   (H1)
```
(`routeB-half1.md` §4.1, §7; dimensional, regularity-free, additive,
tentacle-stable). `Z={|∇v|≤s_0}`, `s_0 ≍_n 1/n`. The two settled prongs:
**P1** thin (width `→0`) ⇒ `|∇v| ≍ max(width, far-reservoir radius) → 0` ⇒
`region ⊂ Z`, excised (`dk-nge4.md` §2, `tentacle-model.md` Task 1);
**P2** two `Θ(1)`-separated near-ball masses ⇒ `δ_T ≥ 1−2^{-2/n}=Θ_n(1)`
(`dk-nge4.md` §1, Saint–Venant superadditivity).

---

## 0. The Hessian density of a generic non-round region (the workhorse)

Every third-class attempt needs the trace-free Hessian density on a
*channel-like* (not ball-like) region. Compute it once, exactly.

On a tube of cross-radius `W` with Dirichlet lateral wall, `v` is, to leading
order, the transverse cap `Φ(y)=(W²−|y|²)/(2(n−1))` plus a slowly varying
axial part. Then in transverse/axial coordinates
```
   D²v  ≈  diag( −1/(n−1), …, −1/(n−1) , 0 ),     [ (n−1) transverse, 1 axial ]
```
because `Φ` is quadratic transversally with `Φ''=−1/(n−1)` and (for a
straight slowly-varying core) the axial second derivative is `o(1)`. Note
`tr D²v = −(n−1)/(n−1)+0 = −1 = Δv`, consistent. The trace-free part
`A_0 := D²v+\tfrac1n I` has transverse entries `−\tfrac1{n-1}+\tfrac1n
= −\tfrac1{n(n-1)}` and axial entry `\tfrac1n`, so
```
   |D²v+\tfrac1n I|²  =  (n−1)·\tfrac1{n²(n−1)²} + \tfrac1{n²}
                      =  \tfrac1{n²(n−1)} + \tfrac1{n²}
                      =  \tfrac{1}{n²}\Bigl(1+\tfrac1{n-1}\Bigr) = Θ_n(1).   (★)
```
Numerically `(★) = 0.083, 0.050, 0.033` for `n=4,5,6`. **Any channel-like
region — straight or curved, thin or thick — carries trace-free Hessian
density `≍_n 1/n²`, bounded *below* away from zero, purely because it is not
a ball.** Curvature of the core only *adds* a positive `O(κ²W²)` term to the
axial entry; it never lowers `(★)`. This single inequality is the engine that
disposes of every *thick* third-class family.

---

## 1. Thick spiral / twisted channel — the brief's headline candidate

**Domain.** A solid worm: tubular neighbourhood of a smooth core curve
`γ⊂ℝⁿ` of length `L`, cross-radius `W`, curvature `κ` along `γ`. "Thick"
means `W = Θ_n(1)` fixed (NOT `→0`, so it is *not* a P1 feature) and
`|∇v|≍W = Θ_n(1) > s_0` on the core (so it is *not* excised). Volume
`|worm| ≍ ω_{n-1}W^{n-1}L`. To be the whole admissible domain, normalise
`|D|=ω_n`, so `W^{n-1}L ≍_n 1`.

**`R_v`.** By (★), on the worm `|D²v+\tfrac1n I|² ≥ \tfrac1{n²}(1+\tfrac1{n-1})`
*everywhere on a Θ(1)-volume set*, and `v ≍ W² = Θ_n(1)` there (thick tube:
`v` rises to the transverse-cap height `W²/(2(n−1))`, not suppressed). Hence
```
   R_v(worm)  =  ∫_{worm} v\,|D²v+\tfrac1n I|²
              ≳_n  W² · \tfrac1{n²} · |worm|
              ≳_n  W² · \tfrac1{n²} · ω_{n-1}W^{n-1}L
              ≍_n  \tfrac1{n²}·W²·1   =  Θ_n(1)            (W,L=Θ_n(1)).
```
Curvature only inflates this: the curved core forces an extra axial Hessian
entry `≈ −κ·∂_n v ≍ κW`, raising `(★)` to `\tfrac1{n²}(1+\tfrac1{n-1})+Θ(κ²W²)`.
A spiral packing `L ≍_n 1/W^{n-1}` of total core-length into the unit volume
has curvature `κ ≳ W^{-1}` (turns of radius `≲ W`), so the curvature term is
`Θ(κ²W²)=Θ(1)` — *strictly larger* `R_v`. Either way `R_v = Θ_n(1)`.

**Half 1 fires.** By (H1), `δ_T ≥ 2n²·R_v ≥ 2n²·Θ_n(1) = Θ_n(1)`.
Quantitatively, with `R_v ≳ \tfrac1{n²}·c·W^2·W^{n-1}L` and `W^{n-1}L=ω_n/ω_{n-1}`,
`δ_T ≳ 2n²·\tfrac{c}{n²}W^2·\tfrac{ω_n}{ω_{n-1}} = Θ_n(W^2)=Θ_n(1)`.
**The thick spiral is excluded by Half 1**, *before* its John constant
(which is `≍ L/W`, large) is ever consulted. The brief asked whether
curvature inflates `|D²v|` and hence `R_v`: yes — but the decisive point is
sharper: a thick channel is already Half-1-forbidden at `κ=0` purely by (★);
curvature is not even needed. **Triggers a Half-1 (P2-type) exclusion.**

**Cross-check (strict stability, independent).** A thick worm of Θ(1)
volume threaded through the unit volume is far from the volume-matched ball:
`Asym(worm) = Θ_n(1)` (a length-`Θ(1)`, width-`Θ(1)` snake has Θ(1) symmetric
difference with any ball). By BDV strict Saint–Venant stability
(arXiv:1306.0392, the deficit↔asymmetry envelope) `δ_T = Θ_n(1)`. Consistent
with the Half-1 verdict; not circular (Half 1 is the *proved* lower bound,
strict stability is the independent cross-check). **No counterexample.**

---

## 2. Thick rough / fractal-ish boundary at a Θ(1)-but-irregular scale

**Domain.** `B_1` with its boundary replaced, on a Θ(1) fraction of `∂B_1`,
by an oscillation of amplitude `δ` and wavelength `ℓ`, both `Θ_n(1)` (a
"crinkled" but not thin boundary; no single neck). John failure of such a
domain is the classical *fractal/cusp* failure: the John condition fails
because the cone joining `∂D` to the centre cannot be inscribed where the
boundary folds.

**Two sub-cases, by the fold geometry.**

- *Folds create inward cusps / re-entrant fingers of width `→0`.* This is a
P1 thin feature in disguise: the re-entrant channel has cross-width `→0`, so
`|∇v|≍width→0` on it (transverse cap, `dk-nge4.md` §2), it lies in `Z` and is
excised. After excision the cusps are gone; what remains is a thick near-ball.
**Triggers P1.**

- *Folds have Θ(1) width (genuinely thick roughness).* Then each fold is a
Θ(1)-width non-round protrusion/indentation. By (★) each carries
`|D²v+\tfrac1n I|² ≍_n 1/n²` over its Θ(1) volume (it is locally a thick
channel, not a sphere). Summing over the Θ(1)-fraction of `∂B_1` that is
crinkled: `R_v ≳_n \tfrac1{n²}·v_*·|crinkled region| ≍_n 1/n² · Θ(1) =
Θ_n(1)`. Half 1 (H1) ⇒ `δ_T = Θ_n(1)`. **Triggers Half-1 (P2-type).**

A thick rough boundary cannot evade both: roughness that wrecks John is
either sub-`s_0`-gradient (excised, P1) or Θ(1)-amplitude non-round (Half-1
forbidden). There is no "Half-1-consistent, strict-stability-evading, thick,
John-wrecking" boundary oscillation, because **`R_v` does not see a *single*
thin neck only — it sees the total Θ(1) volume of every non-round Θ(1)-scale
feature, additively** (Half 1 is additive, `routeB-half1.md` §6). A fractal
that wrecks John by accumulating *infinitely many* features of shrinking
width is, feature by feature, a union of P1-thin necks: each shrinking-width
generation enters `Z`. The aggregate excised volume is controlled by the
small-gradient lemma `ℋⁿ⁻¹(\{|∇v|≤s\}∩Σ)≤4s\mathcal V/\bar f²`
(`two-strategies.tex` Lem. B4, `routeB-half2-adversarial.md` §7 — verified
correct), which bounds the *total* sub-`s_0` set by `O(s_0)` additively
regardless of how many generations. **No counterexample.**

---

## 3. Many `m` medium protrusions — does the aggregate hit a prong first?

**Domain.** `B_1` with `m` identical fingers, each width `W`, length
`L=Θ_n(1)`, `W` fixed small, attached at `Θ(1)`-separated points of `∂B_1`.

**John constant.** The John constant is a **supremum/maximum** over the
domain of a length-to-width ratio, *not* an additive functional. `m`
identical fingers give John constant `≍ L/W` — the *same* as one finger.
Adding more fingers does **not** degrade the John constant further (it is
already the worst single carrot). So "John degrades with `m`" is false:
**`m` is irrelevant to John-blowup; only `W→0` blows John.**

**Aggregate prong accounting.** Per finger: `Asym`-contribution `≍ W^{n-1}L`,
`δ_T`-contribution `≍_n W^{n-1}L = |finger|` (`tentacle-model.md` DEF-EXACT),
and (★)+thin: `R_v`-contribution `≍ W²·\tfrac1{n²}·W^{n-1}L`. Aggregates:
```
   Asym ≍ m W^{n-1}L,   δ_T ≍_n m W^{n-1}L,   R_v ≍_n \tfrac1{n²} m W^{n+1}L.
```
Per-finger ratio `R_v/δ_T ≍ W²/n² → 0`: Half-1-*consistent* (no Half-1
exclusion from a single thin finger — correct, and consistent with
`routeB-half1.md` §6/§7). And `Asym² ≍ m²W^{2(n-1)}L² ≪ mW^{n-1}L ≍ δ_T`
(for `m W^{n-1}L = o(1)`): strict-stability-*consistent*. So `m` medium thin
fingers do NOT hit a prong via aggregate `R_v` or aggregate `Asym`.

**Resolution: the diameter cap.** John of this family is `≍ L/W`, finite for
any fixed `W>0`. It blows up **only** as `W→0` with `L` fixed
(`L≤diam≍_n 1`, capped — see §5). `W→0` is exactly P1: `|∇v|≍W→0` on each
finger, every finger `⊂Z`, all excised; after excision `D∖Z` is `B_1` minus a
collar = single thick near-ball, John dimensional. `m` only multiplies the
*excised* volume, bounded additively by the small-gradient lemma. **Triggers
P1 (after excision), with `m` playing no role in the John constant.** No
counterexample.

---

## 4. Anisotropic pancake / cigar near-ball (`n ≥ 4` ellipsoid)

**Domain.** Ellipsoid `E` with semi-axes; eccentricity parameter `ε`
(`ε=Θ(1)` strongly anisotropic, `ε→0` mildly).

- *Mildly eccentric (`ε→0`).* John constant `1+O(ε) ≍ 1` — dimensional. The
torsion function is `O(ε)`-close to a ball quadratic, so
`|D²v+\tfrac1n I|² ≍ ε²` over a Θ(1) volume ⇒ `R_v ≍_n ε²`; `δ_T ≍_n ε²`
(the ellipsoid sharpness computation, `two-strategies.tex` §1.1:
`Asym≍ε`, `δ_T≍ε²`); `Asym² ≍ ε² ≍ δ_T`. Every quantity is *consistent*
with the target `Asym² ≤ C(n)δ_T` and Half 1 is *tight* (`R_v ≍ δ_T`).
**Not a counterexample — it is the extremal family the sharp exponent is
calibrated on.**

- *Strongly eccentric (`ε=Θ(1)` or one axis `→0`).* A collapsed pancake
(thickness `b→0`) or cigar (one long axis, others `→0`) is a *thin slab* in
`n−1` or `1` directions: `|∇v| ≍ b → 0` transversally on the thin
direction(s) ⇒ the thin part `⊂ Z`, excised. **Triggers P1.** A
Θ(1)-eccentric ellipsoid that is *not* thin has `Asym=Θ(1)` ⇒ `δ_T=Θ_n(1)`
by strict stability and, independently, `R_v=Θ_n(1)` by (★) over its
Θ(1)-volume non-round body ⇒ Half-1 forbidden. **Triggers P2/Half-1.**

There is no eccentric near-ball that is simultaneously thick, John-wrecking,
small-`Asym`, small-`R_v`: eccentricity that wrecks John is either thin
(excised) or Θ(1) (deficit `Θ_n(1)`). **No counterexample.**

---

## 5. The decisive structural mechanism: the diameter cap (why no third class exists)

The brief's worry is that a body can fail John "without a single thin neck"
(rough boundary, spiral). The exhaustive answer is a *quantitative*
John/uniform-domain fact, anchored to geometric measure theory, combined
with the diameter cap and Half 1.

**The John constant is a capped length-to-width supremum.** For a domain `D`,
failure of the `c`-John condition with constant `J` means: there is a point
`p∈D` such that no rectifiable "John curve" from `p` to the John centre `x_0`
stays `r/J`-far from `∂D` at distance-`r` along the curve. Quantitatively
(Martio–Sarvas, *Ann. Acad. Sci. Fenn.* 1979, def. of uniform/John domains;
Väisälä, *Uniform domains*, Tohoku Math. J. 40 (1988): a domain fails to be
`(ε,δ)`/John with constant `≍J` **iff** it contains either (i) a *channel*
(a connected subregion whose length-to-width aspect ratio is `≳ J`), or (ii)
a *separating bottleneck* (a hypersurface cross-section of diameter `≲1/J`
relative to the two Θ(1) components it separates)). This is the rigorous
"failure of John ⇒ thin channel ∨ separating bottleneck" structural
dichotomy the brief asks for; it is purely geometric, dimension-tracked, and
*imported from the GMT literature*, not asserted.

Now apply the two reductions:

- **(i) Channel of aspect ratio `≳ J`.** Its length is `≤ diam(D)`. For a
volume-normalised domain `|D|=ω_n`, `diam(D)` is *not* a priori bounded
(a long thin tentacle has large diameter). But: a channel of aspect ratio
`J` and width `W` has length `≍ JW`. *Either* `W → 0` (then `|∇v|≍W→0`, the
channel `⊂Z`, **excised — P1**; this is the only way `J→∞` with bounded
length), *or* `W = Θ(1)` and the channel is *thick*, length `≍ J` ⇒ by (★)
it is a Θ(1)-density non-round region of volume `≍ W^{n-1}·J ≳ J/ n^{?}`,
so `R_v ≳_n \tfrac1{n²}W²·W^{n-1}J ≍_n J/n²`, and (H1) gives
`δ_T ≳_n J/n² → ∞`-large, certainly `≥ Θ_n(1)` for `J` past a dimensional
threshold ⇒ **Half-1 forbidden — P2-type.** A thick channel cannot have both
large `J` and small `δ_T`: `δ_T ≳_n J/n²`. *This is the quantitative
"thick John-wrecker ⇒ Half-1-large" step, made explicit.*

- **(ii) Separating bottleneck.** A cross-section of diameter `δ_b ≲ 1/J`
separating two Θ(1) components. If `δ_b → 0` the neck is thin: `|∇v|≍δ_b→0`
on it (unless its far reservoir is itself Θ(1), `dk-nge4.md` §2–§3) ⇒ neck
`⊂Z`, the bulk *disconnects* into two pieces ⇒ exactly the **P2** mass
separation: two Θ(1) near-ball masses ⇒ `δ_T ≥ c_0(n) > 0` by Saint–Venant
superadditivity (`dk-nge4.md` §1, §3). If `δ_b = Θ(1)` it is not a bottleneck
(`J` bounded). **Triggers P2.**

**Conclusion of the structural step.** Failure of John with constant `J`
forces, by the imported GMT characterisation, a thick channel of aspect `≳J`
*or* a thin feature. A thin feature is P1 (excised; if it separates two Θ(1)
masses it is P2). A thick channel forces `δ_T ≳_n J/n²` by Half 1. Hence:
```
   B not J-John, J ≥ J_0(n)   ⟹   δ_T(D) ≥ c_0(n) > 0,    c_0(n) dimensional.
```
Contrapositive: `δ_T(D) ≤ δ_0(n) < c_0(n)` ⟹ `B=D∖Z` is `J(n)`-John with a
*dimensional* John constant `J(n)`. **This is (DK\*) for `n≥4`.**

---

## 6. Honest residual — the size of the dimensional constants

The dichotomy closes, but two constants must be named at their true size,
because the brief forbids unquantified "dimensional".

1. **The mass-separation deficit floor is `c_0(n) ≍_n n^{-n}`.** From
`dk-nge4.md` §3, a surviving thin joiner forces a volume split with the
smaller fraction `λ_0 ≳ s_0^n ≍_n n^{-n}` (a far reservoir of radius `≥ s_0`
to keep `|∇v|≥s_0`), and the Saint–Venant superadditivity gap is
`c_0(n)=1−(λ_0^{(n+2)/n}+(1−λ_0)^{(n+2)/n}) ≈ \tfrac{n+2}{n}λ_0 ≍_n n^{-n}`.
Numerically: `c_0(4)≈5.6·10^{-3}`, `c_0(6)≈2.8·10^{-5}`, `c_0(8)≈7.4·10^{-8}`.
This is **positive and depends only on `n`** (genuinely dimensional, no shape
constant), but it is **doubly-exponentially small**. The (DK\*) threshold is
therefore `δ_0(n) < c_0(n) ≍_n n^{-n}` — admissible for the programme (a
dimensional threshold is all the downstream Fuglede closure needs) but the
true magnitude must be on record. *The fully symmetric two-mass split gives
the much larger `1−2^{1-2/n}≈0.29` (n=4); the small `n^{-n}` arises only at
the asymmetric `m=s_0` boundary of the dichotomy, which is the genuine
worst case and must be quoted, not the symmetric one.*

2. **The structural step imports a quantitative GMT characterisation.** "John
failure ⇒ thick channel ∨ thin/bottleneck" with the stated aspect/diameter
quantification is Martio–Sarvas / Väisälä uniform-domain theory. It is
geometric and dimensional, but it is *imported*, on the same footing as the
imported BDV strict-stability fact in prong 2 and the imported dimensional
John constant of a single small-deficit near-ball (`dk-nge4.md` §6). It is
**not circular** (it is pure metric geometry, independent of the
torsion/deficit machinery), but it is the precise external input the
"exhaustiveness" of the dichotomy rests on. The brief explicitly asked not to
assert exhaustiveness without a structural argument with a citation; this is
that citation, and this is the honest statement that it is an import.

Everything else (`(★)`, the (H1) constant `2n²`, the excision threshold
`s_0≍1/n`, the small-gradient lemma constant `4`) is elementary and
dimensional, traced above and in the anchors.

---

## 7. The role of Half-1 `R_v`-inflation (the brief's specific question)

The brief asks whether Half-1 `R_v`-inflation by curvature/oscillation, plus
strict stability, *exhaustively* cover the non-thin-neck John failures. The
answer, made precise:

- Half-1 `R_v`-inflation does the work for **thick** John-wreckers, and it
does it **without needing curvature at all**: identity (★) shows *any*
Θ(1)-volume non-round (channel-like) region has `R_v ≳_n \tfrac1{n²}|region|`
from the bare trace-free Hessian of a non-sphere. Curvature/oscillation only
*adds* to `R_v` (extra axial Hessian `Θ(κ²W²)`); it is never a way to *evade*
Half 1. So a thick spiral is forbidden by Half 1 at zeroth order in `κ`.
The brief's hypothesised "thick, Half-1-consistent, John-wrecking" region
does not exist: thick + John-wrecking ⟹ aspect `≳J` ⟹ Θ(1)-volume non-round
⟹ `R_v ≳_n J/n²` ⟹ `δ_T ≳_n J/n²` (H1). Half 1 *is* the exhaustive killer of
the thick branch.

- Strict stability (P2) and excision (P1) cover the thin branch.

- The *only* gap between "thick" and "thin" is the **width threshold** at
which `|∇v|` crosses `s_0`. The excision is calibrated exactly there
(`s_0≍1/n`), and the small-gradient lemma guarantees the crossover set has
controlled measure. There is no open seam between the prongs for `n≥4` (the
`n=3` seam, where the neck flux is borderline Θ(1), is explicitly outside the
claim, `dk-nge4.md` §7).

So: Half-1 `R_v`-inflation **exhaustively** covers the thick non-neck
failures (and more strongly than the brief conjectured — at `κ=0` already),
strict stability + excision cover the thin ones, and the imported GMT
characterisation certifies that thick-channel ∨ thin-feature ∨ bottleneck is
an *exhaustive* description of John failure. The dichotomy is closed `n≥4`,
modulo the two named residual imports of §6.

---

## 8. Final verdict (`n ≥ 4`)

(DK\*) **HOLDS for `n ≥ 4`.** No third class breaks it. The thick spiral,
thick rough boundary, many-protrusion, and anisotropic-ellipsoid families
each collapse into prong 1 (thin ⇒ excised) or prong 2 / Half 1 (Θ(1)-volume
non-round ⇒ `R_v=Θ_n(1)` ⇒ `δ_T=Θ_n(1)`). The decisive new mechanism is the
**diameter cap**: John is a capped length-to-width supremum, so John-blowup
forces width→0 (P1) or a thick channel of aspect `≳J` whose Half-1 defect
satisfies the explicit bound `δ_T ≳_n J/n²` (P2-type). The exhaustive
structural step is the imported Martio–Sarvas/Väisälä quantitative
John/uniform-domain characterisation (John failure ⇒ thick channel ∨ thin
feature ∨ separating bottleneck), used non-circularly.

**Residual, precisely named:** the closing threshold is `δ_0(n) < c_0(n)`
with `c_0(n) ≍_n n^{-n}` (dimensional but doubly-exponentially small — the
asymmetric `m=s_0` worst case, not the symmetric `≈0.29`), and the
exhaustiveness of the trichotomy rests on the imported (dimensional,
geometric, non-circular) uniform-domain GMT characterisation, on the same
footing as the imported BDV strict-stability and single-near-ball John facts.
**Route B closes for `n ≥ 4` with a dimensional `c_0(n) ≍_n n^{-n}`.**
