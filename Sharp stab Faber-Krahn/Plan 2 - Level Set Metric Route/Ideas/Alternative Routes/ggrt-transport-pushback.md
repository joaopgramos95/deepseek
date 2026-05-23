# GGRT transport pushback: can it close torsion regularity-free?

This note answers one decidable question. Take the GGRT (Gómez–Guerra–Ramos–Tilli,
Inventiones 2024, `s00222-024-01248-2-3.pdf`) transport-plus-neutral-mode
mechanism for STFT Faber–Krahn stability and transport it to the torsion
Saint–Venant deficit. Does the chain

(a) profile gap small ⇒ ∫ D_I(s) ds ≲_n δ_T,
(b) per-level FMP (regularity-free) ⇒ Asym(E_s)² ≲_n D_I(s),
(c) layer-cake assembly of per-level closeness into Asym(Ω)²,

close `Asym(Ω)² ≤ C(n) δ_T` **regularity-free**, with the per-level FMP centre
drift controlled by GGRT's neutral-mode trick?

The verdict is **REDUCES TO (F)**: step (c) is exactly the Plan-2 moving-centre /
action-bound obstruction of `global-foliation-trace.md`, and GGRT's centre-fixing
device does not transfer because it relies on a structural ingredient that has no
torsion analogue for an unknown domain. The argument follows; constants are
tracked.

---

## 1. GGRT's actual mechanism, extracted from the paper

The proof has two halves: a one-dimensional profile/analytic half producing
*function* closeness, and a transport half producing *set* closeness. The
neutral-mode handling lives in BOTH and is the same device each time.

### 1.1 The one-dimensional skeleton (their §2, §1.2)

Their objects: `F ∈ F²(ℂ)` (Fock space), `u_F(z)=|F(z)|² e^{-π|z|²}`, superlevel
sets `A_t={u_F>t}`, distribution `μ(t)=|A_t|`, decreasing rearrangement
`u*(s)`. The optimizer profile is `e^{-s}` (their (1.25): `u*(s)+(u*)'(s)≥0`,
the exact analogue of the torsion `v'(s)≥b'(s)`). They quantify the area between
`u*(s)` and `e^{-s}`:

- Lemma 2.3 (their (2.41)): `(1-T)²/2 ≤ ∫₀^{s*}(e^{-s}-u*(s))ds ≤ δ_{s₀}e^{s₀}`,
  the suboptimal stability.
- Lemma 2.4 + the sharp distribution estimate (their (1.35), Lemma 2.1):
  `μ(t) ≤ (1+C(1-T)) log(T/t)`. This is *the* delicate estimate and it is the
  first place the analytic structure is essential.

This profile/area half is **structurally identical** to the existing torsion
dictionary: `nicola-tilli-stability-import.md §1` and
`level-set-deficit-identity.md §4` already record
`0 ≤ b(s)-v(s) ≤ 2δ_T/s`, with `∫₀^L(b-v)ds = 2(E(Ω)-E(B)) = |Ω|·Γ(Ω)`. So the
torsion (a) is the *same step* as GGRT's (1.32)–(1.33), and it transfers with no
regularity. No issue here.

### 1.2 Where GGRT controls the neutral modes — the harmonic-cancellation lemma

This is the heart of the question. GGRT kills the translation (centre) mode by a
single trick that appears twice.

**First appearance — distribution estimate, Lemma 2.1, Step V (their pp. 794–795).**
After normalizing so that `u_F` attains its maximum `T` at `z=0` and
`F(0)=√T` (their Step I, (2.8): the centre is *pinned at the maximizer of u_F*),
they write `F/√T = 1 + R(z)`, `R` entire with `R(0)=R'(0)=0`, and
`h(z)=2 Re R(z)` a *harmonic* function (their (2.13)). The level sets `E_σ` are
deformed through a parameter σ and the area `f(σ)=|E_σ|` satisfies
`|f''(σ)| ≤ (Cδ²/t₀³) f(0)` (their (2.35)). The crucial step is

> `f'(0) = φ(r₀) ∫₀^{2π} h(r₀ e^{iθ}) dθ = 0`,

because `h` is harmonic with `h(0)=0`, so its circular mean vanishes (their p.795,
mean-value property). This `f'(0)=0` is what upgrades the suboptimal estimate to
the sharp exponent: without it `f(σ)=f(0)+f'(0)σ+O(σ²)` would lose the square.

**Second appearance — set transport, Lemma 5.6 / (5.13)–(5.19) (their pp. 814–816).**
In the variational route, the second variation `∇²K[1](G,G)` is computed and the
neutral modes are removed by the orthogonality conditions
`⟨G,1⟩_{F²}=⟨G,z⟩_{F²}=0` (their (3.6)). The `⟨G,1⟩=0` is the volume mode;
`⟨G,z⟩=0` is the translation mode. The proof of (5.13) shows
`∫ Re G ⟨X₀,ν⟩ dH¹ = ∮ |G|² dH¹`, and this works only because (their (5.17))

> `(d/dε)|₀ μ_ε(t) = 2 ∮_{∂{u₀>t}} Re G dH¹ = 2 Re G(0) = 0`,

again **the circular mean of a harmonic/holomorphic G over a circle, equal to its
value at the centre, equal to 0** by the normalization `G(0)=0`. The paper states
explicitly (their p.818, after Remark 5.7):

> "(3.6) is crucial as a normalization … many of the cancellations in the proof
> of Lemma 5.6 only appeared since `G(0)=0`. Moreover, if `⟨G,z⟩≠0`, … the proof
> of sharp stability could collapse."

and the decisive structural sentence (their p.818):

> "the reduction to (3.6) … plays the pivotal role of providing us with a single
> point `z₀` — which, through translations, may be assumed to be the origin —
> for which one can compare the level sets of the functions `u_ε` to balls
> centered at `z₀`. The fact that `z₀` is given by the point where each `u_ε`
> attains its maximum allows … a connection between the analytic and geometric
> natures of the problem."

This is the precise mechanism. **GGRT's centre is not chosen level-by-level. It
is a single global point `z₀` = argmax of `u_F`, fixed once, the same for every
superlevel set.** The translation mode is then killed not by re-centring each
level set but by the algebraic fact that `F` is *holomorphic* and `G(0)=0`, so
every circular mean it produces vanishes simultaneously, at every radius. There
is one centre, valid on the whole foliation, supplied by the analytic structure.

### 1.3 The transport itself (their §4, pp. 807–809) — regularity-free, but on a fixed centred annulus

The set comparison (their Theorems 1.1/1.5 set part) is genuinely
regularity-free: `T` is *any* measure-preserving transport map
`A_Ω∖Ω → Ω∖A_Ω` (their (4.1), citing [11] for mere existence), and the bad set
`B={x∈A_Ω∖Ω : |T(x)|²-|x|² > C_{|Ω|}γ}` is controlled by the **strictly radial
fixed Gaussian weight** `e^{-π|z|²}`: a point pushed outward in `|z|` loses a
definite amount of weight (their (4.3): `u(z)-u(T(z)) ≥ 5γ` for `z∈B`), and
this loss is paid for by the deficit `d(Ω) ≤ 4(1-e^{-|Ω|})δ` (their (4.2)).
Then `A_Ω` is sandwiched between two concentric balls centred at `z₀`
(their (4.8)) and `|ΩΔS_Ω| ≤ Cδ^{1/2}` (their (4.9)–(4.10)).

So GGRT's transport needs **no boundary regularity** — but it needs (i) a fixed,
strictly radial, globally defined weight `e^{-π|z|²}` whose radial monotonicity
quantifies "mass moved outward = deficit", and (ii) the single global centre
`z₀` from §1.2 so that "outward" is unambiguous on the whole annulus. Both
ingredients come from the ambient Fock structure, not from `Ω`.

---

## 2. The torsion (a)+(b)+(c) analysis

### 2.1 (a) holds, regularity-free, exponent-clean

From `level-set-deficit-identity.md` (boxed identity §2 and §3):

```
2 δ_T(Ω) = ∫₀^{‖u‖_∞} (D_H(t)+D_I(t)) / (n² ω_n^{2/n} m(t)^{1-2/n}) dt,
```

with `δ_T = (E(Ω)-E(B))` (scale-normalized `|Ω|=ω_n`). Dropping `D_H≥0`:

```
∫₀^{‖u‖_∞} D_I(t) / (n² ω_n^{2/n} m(t)^{1-2/n}) dt  ≤  2 δ_T.            (a)
```

This is exact, holds for finite-perimeter sets (coarea), and uses no regularity.
The weight `w(t) = (n² ω_n^{2/n} m(t)^{1-2/n})^{-1}`: changing to the volume
variable `s=m(t)`, on any fixed outer annulus `s∈[ρ_*^n ω_n, ω_n]` the weight is
bounded above and below by dimensional constants (the `global-foliation-trace.md`
§2 observation: `w ≃_n ρ^{n-2}`, `O(1)` near the boundary). **(a) is solid and
regularity-free.** ✔

### 2.2 (b) holds, regularity-free, sharp exponent

FMP quantitative isoperimetry (Fusco–Maggi–Pratelli) is genuinely
assumption-free: for *any* set of finite perimeter,

```
D_I(s) = P(E_s)² - c_n m(s)^{2-2/n}  ≥  c_n m(s)^{2-2/n} Asym(E_s)².        (b)
```

Its own proof is a regularity-free symmetrization/transport argument. So
`Asym(E_s) ≤ C_n √(D_I(s)) / m(s)^{1-1/n}` per level, no regularity. ✔

But the exponent bookkeeping in s is exactly where the issue surfaces. (b) gives
**per-level** L¹-closeness to *some* ball `B_s(x_s)` — the optimal ball in FMP
depends on the level and its centre `x_s` is not pinned. The honest assembly
inequality is the triangle/layer-cake

```
Asym(Ω) ≲_n  (1/|Ω|) ∫ |E_s Δ B_s(x_s)| ds  +  (centre-misalignment terms).
```

If — and only if — the centres `x_s` could be taken **independent of s**, i.e.
`x_s ≡ x₀`, then the layer-cake reassembles the per-level slabs into a single
ball `B(x₀)` and one gets, by Cauchy–Schwarz in s against the bounded weight on
the fixed annulus,

```
Asym(Ω)²  ≲_n  ∫ Asym(E_s)² dμ(s)  ≲_n  ∫ D_I(s) w(s) ds  ≤  2 δ_T,
```

**exponent-tight** (the `√` from (b) is squared back by the L² assembly, no loss).
The Jensen/Cauchy–Schwarz bookkeeping is fine *provided the centres align*. With
free centres, the naive bound `Asym(Ω) ≲ ∫ Asym(E_s) dμ ≲ ∫√(D_I)` followed by
squaring would cost a factor and, more importantly, is simply false: a tube-like
domain has every `E_s` an almost-ball but `Ω` itself far from any ball, with the
centres `x_s` sweeping along the tube. **(c) is not a bookkeeping step; it is a
genuine geometric input — the alignment of `{x_s}`.**

### 2.3 (c) IS the Plan-2 (F) moving-centre obstruction — precise reduction

Write the volume variable as the radius `ρ`, `E_ρ` the level set of volume
`ω_n ρ^n`. FMP per level says `∂E_ρ` is, in the modulated graph gauge,

```
∂E_ρ = { z(ρ) + (ρ + h(ρ,θ)) θ : θ ∈ ∂B },     ∫h=0, ∫hθ_i=0,
```

with `z(ρ)=x_ρ` the per-level FMP centre and `h(ρ,·)` the non-neutral graph.
This is *verbatim* the coherent foliation gauge of `global-foliation-trace.md`
§1, the moving centre `z(ρ)` being the per-level FMP ball centre. The trace
estimate (T) of that note recovers `‖h(1)‖² ≲ δ_T` — hence
`Asym(Ω)² ≲ δ_T` — **if and only if** the action bound

```
∫_{ρ_*}^1 ( ρ^{n+1} ‖∂_ρ h(ρ)‖²_{L²} + ρ^{n-1} Q(h(ρ)) ) dρ  ≤  C_n δ_T   (F)
```

holds. Now decompose what (a)+(b) actually deliver:

- `D_I(ρ)` controls the **angular** part `ρ^{2n-4} Q(h(ρ))` (their §3 of
  `global-foliation-trace.md`, the Fuglede perimeter expansion). This is exactly
  FMP per level: ✔ supplied by (b).
- The **radial-kinetic** part `ρ^{n+1}‖∂_ρ h(ρ)‖²` is supplied by `D_H`, NOT by
  `D_I` (their §4). And the cross/error terms in the (F) integrand involve
  `∂_ρ z(ρ)` — the *velocity of the moving centre*. The centre-drift
  `z'(ρ)·θ` enters the normal velocity `V = 1 + z'(ρ)·θ + ∂_ρ h + …` and is a
  first spherical harmonic that the moving centre is *designed* to absorb.

The reduction is therefore exact: **torsion step (c) — assembling per-level FMP
balls `B_ρ(x_ρ)` into a single ball for `Ω` — is blocked precisely by
uncontrolled drift of `x_ρ=z(ρ)` in `ρ`, and controlling that drift is exactly
the open action bound (F)**, because the only mechanism that converts per-level
closeness into a global ball is the trace inequality (T), whose hypothesis is
(F), and the part of (F) not delivered by (a)+(b)+FMP is precisely the radial
kinetic energy `∫ ρ^{n+1}‖∂_ρ h‖²` together with the centre-velocity terms
`∫|z'(ρ)|²`. This is the Plan-2 moving-centre problem, named (F) in
`global-foliation-trace.md` §1/§6, verbatim. The "drop `D_H≥0`" in (a) discards
*exactly the term that would control the centre drift* — `D_H` is the radial
kinetic energy of the foliation (their §4). So (a)+(b) alone structurally cannot
see (c).

**Conclusion of §2: (a)+(b) hold cleanly and regularity-free, with sharp
exponent; (c) is not bookkeeping but is identically the Plan-2 (F)
moving-centre / action-bound obstruction.**

---

## 3. Does GGRT's neutral-mode trick break it? — No, and the precise reason

The candidate rescue (per the question) is the `K_s` second variation in the
harmonic variable `h_Ω = u_Ω + |x|²/(2n)` (note §6, §8), à la GGRT's
neutral-mode removal. Adversarially examined, it does not transfer. Three
independent reasons, in increasing order of severity.

### 3.1 GGRT's centre is one global point, supplied by the ambient structure

Re-read §1.2. GGRT never re-centres level sets. The translation mode is killed
by `G(0)=0` together with **`G` holomorphic**, which forces *every* circular
mean `∮_{|z|=r} Re G = Re G(0) = 0` to vanish *simultaneously at every radius
`r`*. One algebraic fact (mean value property of a global holomorphic/harmonic
function, valid on all circles about the fixed `z₀=argmax u_F`) kills the
translation mode on the entire foliation at once. There is **no moving centre in
GGRT**; `z(ρ)≡z₀` for all `ρ`. The torsion difficulty (c) is, by §2.3, *exactly*
the existence of a genuinely `ρ`-dependent `x_ρ` that cannot be frozen. GGRT does
not "control the drift" — its structure makes the drift *identically zero*. So
the comparison is not "does GGRT control the drift better"; it is "GGRT has no
drift because of an ambient holomorphic structure", and the question is whether
torsion has that structure.

### 3.2 No fixed global radial weight for an unknown Ω

GGRT's transport (their §4) quantifies "mass moved outward = deficit" using the
**fixed, strictly radial, globally defined** weight `e^{-π|z|²}`, the same for
every competitor `F` and every superlevel set, centred at the global `z₀`. The
torsion analogue would need a fixed strictly radial weight whose radial
monotonicity is paid by `δ_T`. The only candidate is `u_B` (the ball
comparison). But `u_B` is *not* a weight on `Ω`: it is the profile of the
*answer*, not of the *competitor*. The harmonic substitute `h_Ω=u_Ω+|x|²/(2n)`
(note §8) is `Δh_Ω=0` and `h_B≡const`, the correct analogue of GGRT's harmonic
`h=2Re R`. But here is the structural break: in GGRT, `R` (hence `h`) is a
*global entire function on all of ℂ*, so its circular means vanish on every
circle about the single fixed `z₀`. The torsion `h_Ω` is harmonic **only inside
the unknown `Ω`**, on no fixed centred family of circles, and there is no fixed
point playing the role of `z₀=argmax`: the maximum of `u_Ω` is at an unknown
interior point that itself can move with `Ω`, and `h_Ω` is harmonic only on the
domain whose shape is what we are trying to determine. The mean-value
cancellation `∮ h_Ω = h_Ω(centre)` requires the circles `{|z-z₀|=r}` to lie
*inside* the harmonicity domain for all `r` up to the boundary — which is true
in GGRT (entire, whole plane) and **false for torsion** unless `Ω` is already
known to be a near-centred near-ball, i.e. unless the conclusion is already in
hand. The cancellation is not regularity-free; it presumes the very
graph-over-a-fixed-ball structure that the regularity-free route is supposed to
produce.

### 3.3 The `K_s` second variation needs the gauge it is meant to supply

The `K_s = ∫_{{u>u*(s)}} u` second variation (note §6) does diagonalize in
spherical harmonics with a gap after removing `k=0,1` modes — *for nearly
spherical perturbations of the ball, in a fixed graph gauge over `∂B`*. That is
exactly GGRT's Theorem 5.1 / Proposition 5.3 setting: `F=1+εG`, `‖G‖=1`,
`⟨G,1⟩=⟨G,z⟩=0`, perturbation of the *known* optimizer in the *known* native
space. To even *write* the torsion `K_s` second variation with barycentre
orthogonality one must already have placed `∂E_ρ` in a normal graph over a
*fixed* sphere with a *fixed* centre — which is the graph-entry / fixed-centre
data that (c) is missing. The second variation is coercive *given* the gauge; it
does not *produce* the gauge. In GGRT the gauge is free because the native space
is fixed and the centre is the global argmax of the entire `F`. For torsion the
gauge is the unknown. This is the regularity wall in the form named in
`nicola-tilli-stability-import.md` §5–§6, §9 table row 5 ("Use BDV
selected-minimizer regularity, or harmonic/holomorphic native objects after
graph entry. This is where Plan 1 is needed") and §10.

### 3.4 Exactly where it punts

The reduction lands precisely on the Plan-2 outer-foliation entry lemma
(`global-foliation-trace.md` §6): one needs the actual torsion levels
`E_ρ, ρ∈[ρ_*,1]` to admit the modulated weak graph with the action bound (F),
and the `D_H` (radial-kinetic) half of (F) plus the centre-velocity terms
`∫|z'(ρ)|²` are not delivered by per-level FMP. GGRT obtains the analogous
control because its `D_H`-analogue (the `μ_ε`-derivative, their (5.17)) is killed
by the *global holomorphic* mean-value cancellation, which has **no torsion
counterpart for an unknown domain** (§3.1–§3.2). Hence the route punts exactly to
the selected-minimizer / graph-entry step — the regularity wall — equivalently to
proving (F).

---

## 4. Verdict

**REDUCES TO (F).** Precisely:

1. **(a) holds, regularity-free, exact.** `∫ D_I dν ≤ 2δ_T` from the level-set
   identity by dropping `D_H≥0`; weight `w=O(1)` on any fixed outer annulus.

2. **(b) holds, regularity-free, sharp exponent.** FMP per level is
   assumption-free: `Asym(E_s)² ≤ C_n D_I(s)/m(s)^{2-2/n}`.

3. **The s-bookkeeping is exponent-tight ONLY under centre alignment.** With
   per-level FMP centres `x_s` aligned (`x_s≡x₀`), the L² layer-cake gives
   `Asym(Ω)² ≲_n ∫ D_I dν ≤ 2δ_T` with no exponent loss. Without alignment the
   assembly is false (tube counterexample), so (c) is a genuine geometric input,
   not bookkeeping.

4. **(c) is identically the Plan-2 (F) moving-centre obstruction.** The per-level
   FMP balls `B_ρ(x_ρ)` assemble to a ball for `Ω` iff the trace inequality (T)
   of `global-foliation-trace.md` applies, whose hypothesis is the action bound
   (F). (a)+(b)+FMP deliver only the angular `ρ^{2n-4}Q(h)` part of (F); the
   radial-kinetic `ρ^{n+1}‖∂_ρ h‖²` part and the centre-velocity `∫|z'(ρ)|²`
   terms are exactly `D_H`, which (a) discarded. This is the open (F).

5. **GGRT's neutral-mode/transport trick does not transfer.** GGRT has *no*
   moving centre: a single global point `z₀=argmax u_F` and the *global
   holomorphic* mean-value cancellation `∮_{|z-z₀|=r} Re G = Re G(0)=0` kill the
   translation mode on the whole foliation at once. Torsion has no fixed global
   strictly-radial weight (`u_B` is the answer's profile, not the competitor's;
   `h_Ω` is harmonic only inside the unknown `Ω`, with no fixed centred family of
   circles up to the boundary). The `K_s` second variation is coercive only in a
   fixed graph gauge over a fixed sphere — exactly the data that (c)/(F) lacks;
   it presumes the conclusion. The route punts to the selected-minimizer /
   graph-entry step, i.e. to proving (F).

**Resulting status.** The GGRT transport pushback gives, regularity-free and
exponent-tight, every ingredient *except* the centre-drift control, which is
identically the open Plan-2 action bound (F). It does **not** close
`Asym(Ω)² ≤ C(n)δ_T` regularity-free. Constants in the *conditional* chain:
(a) factor `2`; (b) factor `c_n=n²ω_n^{2/n}`; (T) factor `C_{ρ_*}`,
all dimensional — but only conditional on (F).

---

## 5. ~250-word summary

**(1) Do (a)+(b) hold regularity-free, and is the s-bookkeeping exponent-tight?**
Yes to both, with one caveat. (a) is exact from the level-set deficit identity
(drop `D_H≥0`); the weight is `O(1)` on a fixed outer annulus; no regularity.
(b), per-level FMP quantitative isoperimetry, is genuinely assumption-free. The
Cauchy–Schwarz/Jensen assembly is exponent-tight (`√D_I` squares back to
`∫D_I=δ_T`) **provided the per-level FMP ball centres `x_s` align**. They need
not: for a tube every level set is an almost-ball but `Ω` is far from any ball,
centres sweeping along the tube. So (c) is a genuine geometric input, not
bookkeeping.

**(2) Is (c) the (F) moving-centre obstruction?** Yes, identically. Per-level
FMP gives the modulated graph gauge with a moving centre `z(ρ)=x_ρ` — verbatim
the coherent foliation gauge of `global-foliation-trace.md`. Assembling into one
ball requires the trace inequality (T), whose hypothesis is the action bound
(F). (a)+(b)+FMP supply only the angular `Q(h)` half of (F); the radial-kinetic
`‖∂_ρ h‖²` and centre-velocity halves are exactly `D_H`, discarded in (a). That
is the open (F).

**(3) Does GGRT's trick transfer?** No. GGRT has *no* moving centre: a single
global `z₀=argmax u_F` and the *global holomorphic* mean-value cancellation
`∮ Re G = Re G(0)=0` kill translation on the whole foliation at once. Torsion
has no fixed global radial weight for an unknown `Ω` (`u_B` is the answer;
`h_Ω` is harmonic only inside the unknown domain, with no centred circle family
to the boundary), and the `K_s` second variation is coercive only in a fixed
graph gauge it cannot itself supply. It punts to graph entry.

**Overall: REDUCES TO (F).**
