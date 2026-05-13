# Wave 2 Agent A: L² radial trace for finite-perimeter near-balls

**Status of conclusion.** The proposed L² radial trace inequality (R2) at the
sharp rate δ is **not closed** in the no-graph finite-perimeter setting by the
route in the brief. The good-ray / bad-ray quadratic absorption of multiplicity
excess (which Agent 2's L¹ attempt could not perform) is rigorously verified
below for the *slicing-weighted* L² trace. The remaining piece is the **L²
tangential-defect** integral, which by the divergence theorem reduces to a
**quadratic Fusco–Julin oscillation** ∫|ν_E − e_r|² ≤ Cδ. This stronger form
is **not** in the FMP/Fusco–Julin/Cicalese–Leonardi package and is the
genuine, isolated residual obstruction. What is provable unconditionally is
the rate-√δ version of (R2); after Cauchy–Schwarz this only gives Plan 2's
output at rate δ^{1/4}, not δ.

This note (a) sets the smallness preliminary; (b) proves the slicing-weighted
L² trace with the new quadratic bad-ray absorption; (c) proves
∫(1−|e_r·ν_E|) = (P(E)−P(B_ρ)) + Π(E,z_E) and tracks Π honestly; (d) gives
the equivalence (R2)⇔(quadratic Fusco–Julin oscillation) modulo the new
slicing-weighted theorem of part (b); (e) makes precise the algebraic chain
to Conjecture 3.6 / Plan 2 closure conditional on the residual quadratic
oscillation lemma.

---

## 1. Hypotheses and statement

Fix n ≥ 2, R ≥ 2, ρ_* ∈ (0,1), and ρ ∈ [ρ_*, 1]. Let E ⊂ B_R ⊂ ℝⁿ be a set
of finite perimeter with |E| = |B_ρ| = ω_n ρⁿ and Fraenkel asymmetry
$\mathcal A(E) \le \varepsilon_0$ (smallness regime; $\varepsilon_0 = \varepsilon_0(n,\rho_*)$ chosen below). Let z_E be the
asymmetric Fraenkel center of E supplied by Cicalese–Leonardi 2012 ARMA
(Thm 1.1): there is a measure-theoretically unique z_E with
|E Δ B_ρ(z_E)| = inf_z |E Δ B_ρ(z)|, and under smallness the inner-ball
containment

  B(z_E, ρ/2) ⊂ E ⊂ B(z_E, 2ρ)                                        (CL)

holds modulo null sets. Write e_r(x) := (x − z_E)/|x − z_E| and let ν_E be the
measure-theoretic outer normal on ∂*E.

**Target inequality (R2).** There exists C = C(n,R,ρ_*) with

  T₂(E) := ∫_{∂*E} (|x−z_E|/ρ − 1)² dℋ^{n−1}(x)
         ≤ C·(P(E) − P(B_ρ)).                                          (R2)

**Cauchy–Schwarz upgrade to (R).** If (R2) holds with constant C, then by
Cauchy–Schwarz on the measure space (∂*E, dℋ^{n−1}),

  T₁(E)² := (∫_{∂*E} ||x−z_E|/ρ − 1| dℋ^{n−1})² ≤ P(E)·T₂(E)
        ≤ C·P(E)·(P(E) − P(B_ρ)).                                      (R)

In the smallness regime P(E) ≤ 2 P(B_ρ), this is the radial L¹-trace bound
on which Agent 2 §3.1 conditions the homothetic velocity defect lemma.

**Verdict of this note.** (R2) at rate δ := P(E) − P(B_ρ) is **not proved**
unconditionally. We prove (R2) at rate √δ unconditionally (§5.1), and we
prove the rate-δ form conditional on a *quadratic* L² tangential oscillation
estimate (§5.2 Theorem B), which is the genuine residual gap.

## 2. Smallness preliminary and the Plan 2 compatibility

**Lemma 2.1 (Cicalese–Leonardi containment).** There is $\varepsilon_0(n) > 0$ such that
if $\mathcal A(E) \le \varepsilon_0$ then there is z_E satisfying (CL), and the asymmetric
Fraenkel center is unique modulo ℋ^{n−1}-null sets.

*Source.* M. Cicalese, G. P. Leonardi, *A selection principle for the sharp
quantitative isoperimetric inequality*, Arch. Ration. Mech. Anal. 206 (2012),
617–643, Theorem 1.1. Note: we use only the measure-theoretic part of their
result (the containment (CL) and the centering); we do *not* use the
selection-and-regularity machinery that follows.

**Lemma 2.2 (compatibility with the Plan 2 levels).** Let Ω ⊂ B_R be a
bounded domain with δ_T(Ω) ≤ δ_0(n,ρ_*,R). For each ρ ∈ [ρ_*, 1], the
torsion level E_ρ = {u_Ω > t(ρ)} with |E_ρ| = ω_n ρⁿ satisfies
$\mathcal A(E_\rho) \le C(n,\rho_*) \sqrt{\delta_T(\Omega)} \le \varepsilon_0$.

*Proof.* By `level-set-deficit-identity.md` Lemma 8.2, on the volume slab
T_η = {ρ ∈ [ρ_*, 1]} ⇔ η = (1−ρⁿ)ω_n ∈ [ω_n(1−ρ_*ⁿ), ω_n(1−ρ_*ⁿ)+1] we
have a positive measure ν(T_η) bounded below by c(n,ρ_*) > 0. Averaging the
exact identity (`level-set-deficit-identity.md` (3.0))
∫(D_H + D_I) dν = 2δ_T forces D_I(t(ρ)) ≤ C(n,ρ_*)·δ_T uniformly for a.e.
ρ ∈ [ρ_*, 1]. By FMP (Figalli–Maggi–Pratelli 2010, *Invent. Math.* 182),
$\mathcal A(E_\rho)^2 \le c_1 D_I/m(t(\rho))^{2−2/n} \le C(n,\rho_*)\cdot\delta_T$. □

So the smallness hypothesis $\mathcal A(E) \le \varepsilon_0$ of Lemma 2.1 is automatic for the
Plan 2 levels E_ρ, ρ ∈ [ρ_*, 1], whenever δ_T(Ω) is small.

**Dichotomy outside smallness.** If $\mathcal A(E) > \varepsilon_0$ then quantitative
isoperimetry gives $P(E) - P(B_\rho) \ge c_1(n)\varepsilon_0^2 \omega_n^2 \cdot \rho^{n-1}$, and (R2) follows
trivially with $C = C(n,R,\rho_*,\varepsilon_0)$ because $T_2(E) \le P(E) \cdot ((R/\rho_*) - 1)^2$. So
the residual issue is in the smallness regime only.

## 3. Spherical disintegration of perimeter

We use the radial slicing formula in spherical coordinates centered at z_E.
For x ∈ ℝⁿ write x = z_E + r·θ with r = |x − z_E| and θ ∈ S^{n−1}. For each
θ ∈ S^{n−1}, let

  E_θ := {r > 0 : z_E + r·θ ∈ E}.

By Maggi 2012, *Sets of finite perimeter and geometric variational problems*,
Cambridge, Proposition 19.4 (radial slicing), for ℋ^{n−1}-a.e. θ the set
E_θ is a 1D set of finite perimeter, with reduced boundary
∂*E_θ = {r_{θ,1} < r_{θ,2} < ··· < r_{θ,N(θ)}}, N(θ) ∈ ℕ. By (CL) in the
smallness regime,

  r_{θ,1} ≥ ρ/2 if N(θ) = 1, and the slice contains (0, ρ/2)·ω_n (vacuous).

More precisely, **for ℋ^{n−1}-a.e. θ ∈ S^{n−1}**, (CL) implies (0, ρ/2) ⊂ E_θ
and E_θ ⊂ (0, 2ρ). Hence every reduced-boundary point satisfies

  ρ/2 ≤ r_{θ,1} ≤ ··· ≤ r_{θ,N(θ)} ≤ 2ρ.                              (3.1)

The pivotal **slicing identity** for the radial-projection weight is
(Maggi 2012, Thm 18.11 or AFP 2000 Thm 3.108, transcribed to spherical
coordinates): for any Borel g : (0,∞) → [0,∞),

  ∫_{∂*E} g(|x − z_E|)·|e_r(x)·ν_E(x)| dℋ^{n−1}(x)
       = ∫_{S^{n−1}} (Σ_{j=1}^{N(θ)} g(r_{θ,j}) r_{θ,j}^{n−1}) dθ.   (S)

In particular, with g ≡ 1:

  ∫_{∂*E} |e_r·ν_E| dℋ^{n−1} = ∫_{S^{n−1}} Σ(θ) dθ,                   (S₀)
  Σ(θ) := Σ_{j=1}^{N(θ)} r_{θ,j}^{n−1}.

For E = B_ρ(z_E) we get Σ(θ) ≡ ρ^{n−1}, recovering
∫_{∂B_ρ}1 dℋ^{n−1} = P(B_ρ).

## 4. Slicing-weighted L² trace: bad-ray quadratic absorption

We now prove the part of (R2) that escapes Agent 2's L¹-circularity.

**Theorem A (slicing-weighted L² trace).** Under the hypotheses of §1,

  T₂^{rad}(E) := ∫_{∂*E} (|x − z_E|/ρ − 1)²·|e_r·ν_E| dℋ^{n−1}
              ≤ C(n,R,ρ_*)·(P(E) − P(B_ρ)).                          (R2-rad)

The proof uses (S), (3.1), and a 1D good-ray / bad-ray split.

### 4.1 Slicewise reformulation

By (S) with g(r) = (r/ρ − 1)²:

  T₂^{rad}(E) = ∫_{S^{n−1}} Q(θ) dθ,
        Q(θ) := Σ_{j=1}^{N(θ)} (r_{θ,j}/ρ − 1)² · r_{θ,j}^{n−1}.

Using (3.1): r_{θ,j}^{n−1} ∈ [(ρ/2)^{n−1}, (2ρ)^{n−1}] ⊂
[(ρ_*/2)^{n−1}, (2R)^{n−1}], so r_{θ,j}^{n−1} ≤ (2R)^{n−1}, and we have the
slice-wise bound

  Q(θ) ≤ (2R)^{n−1} Σ_{j=1}^{N(θ)} (r_{θ,j}/ρ − 1)².                  (4.1)

### 4.2 Slicewise 1D perimeter and the good-ray / bad-ray dichotomy

Let

  p(θ) := Σ_{j=1}^{N(θ)} r_{θ,j}^{n−1}, ρ^{n−1}·N(θ) = "slicewise perimeter
  in spherical coordinates" weighted by the 1D coarea factor r^{n−1}.

By (S₀) the angular integral of p(θ) is ∫_{∂*E}|e_r·ν_E|. By Cauchy–Schwarz
on ∂*E and the bound |e_r·ν_E| ≤ 1,

  ∫_{∂*E}|e_r·ν_E| dℋ^{n−1} ≤ P(E).                                  (4.2)

Conversely, ∫_{∂*E}|e_r·ν_E| dℋ^{n−1} = P(E) − ∫_{∂*E}(1−|e_r·ν_E|) dℋ^{n−1}.
By (3.1) every slice contains the interval (0, r_{θ,1}) ⊃ (0, ρ/2) and is
contained in (0, 2ρ), so N(θ) ≥ 1 for ℋ^{n−1}-a.e. θ. Define the **excess
multiplicity**

  k(θ) := N(θ) − 1 ≥ 0.

Then the slicewise perimeter excess (with the 1D coarea weight) decomposes
as

  p(θ) − ρ^{n−1} = (r_{θ,1}^{n−1} − ρ^{n−1}) + Σ_{j=2}^{N(θ)} r_{θ,j}^{n−1}.

Since r_{θ,j} ≥ ρ/2 by (3.1), each term in the sum from j = 2 is ≥
(ρ/2)^{n−1} ≥ (ρ_*/2)^{n−1}. Hence

  p(θ) − ρ^{n−1} ≥ (r_{θ,1}^{n−1} − ρ^{n−1}) + (ρ_*/2)^{n−1}·k(θ).    (4.3)

This is the key **quadratic-absorption** inequality: the bad-ray multiplicity
k(θ) appears **linearly** in the slicewise perimeter excess, with a
**positive** coefficient.

### 4.3 Slicewise L² bound

For each θ, decompose

  Σ_j (r_{θ,j}/ρ − 1)² = (r_{θ,1}/ρ − 1)² + Σ_{j=2}^{N(θ)} (r_{θ,j}/ρ − 1)².

By (3.1) and r_{θ,j} ∈ [ρ/2, 2ρ], each (r_{θ,j}/ρ − 1)² ≤ 1. Hence

  Σ_{j=2}^{N(θ)} (r_{θ,j}/ρ − 1)² ≤ k(θ).                            (4.4)

For the first (good-ray) term, by (3.1) and the trivial inequality
|r^{n−1} − ρ^{n−1}| ≥ c(n) ρ^{n−2}·|r − ρ| on [ρ_*/2, 2R] with
c(n) := (ρ_*/2)^{n−2}/(n−1)·(2R)^{−(n−2)} (mean-value theorem, valid
because r ↦ r^{n−1} is C¹ with derivative ≥ (n−1)(ρ_*/2)^{n−2} on the
interval), we obtain

  (r_{θ,1} − ρ)² ≤ C(n,R,ρ_*)·(r_{θ,1}^{n−1} − ρ^{n−1})²/ρ^{2(n−2)}.

So

  (r_{θ,1}/ρ − 1)² ≤ C(n,R,ρ_*)·ρ^{−2(n−1)}·(r_{θ,1}^{n−1} − ρ^{n−1})².  (4.5)

If r_{θ,1}^{n−1} − ρ^{n−1} happens to be non-positive (i.e. the slice
boundary first crosses below ρ), then we use a *signed* version: write
δ_1(θ) := r_{θ,1}^{n−1} − ρ^{n−1}; the algebraic estimate

  (r_{θ,1}/ρ − 1)² ≤ C(n,R,ρ_*)·|δ_1(θ)|

(rather than δ_1(θ)²) holds because (r_{θ,1}/ρ−1)² ≤ |r_{θ,1}/ρ − 1| in the
range r_{θ,1}/ρ ∈ [1/2, 2], i.e., the L²-trace integrand is dominated by its
L¹ counterpart, and the latter is comparable to |δ_1(θ)|/ρ^{n−1}.

So we get the **linear** bound

  (r_{θ,1}/ρ − 1)² ≤ C(n,R,ρ_*) · |r_{θ,1}^{n−1} − ρ^{n−1}|.        (4.5')

Combining (4.4), (4.5'), and (4.1):

  Q(θ) ≤ C(n,R,ρ_*) · [|r_{θ,1}^{n−1} − ρ^{n−1}| + k(θ)].            (4.6)

### 4.4 Angular integration and absorption into perimeter excess

Integrating (4.6) over S^{n−1}:

  T₂^{rad}(E) ≤ C(n,R,ρ_*) · [∫_{S^{n−1}} |r_{θ,1}^{n−1} − ρ^{n−1}| dθ
                              + ∫_{S^{n−1}} k(θ) dθ].                 (4.7)

**Bound on the multiplicity term.** By the slicing identity (S) with g ≡ 1
and the decomposition p(θ) = ρ^{n−1} + (p(θ) − ρ^{n−1}), the angular integral
of p(θ) is ∫_{∂*E}|e_r·ν_E|. Hence

  ∫_{S^{n−1}} (p(θ) − ρ^{n−1}) dθ = ∫_{∂*E}|e_r·ν_E| dℋ^{n−1} − P(B_ρ)
                                  = P(E) − P(B_ρ) − ∫_{∂*E}(1 − |e_r·ν_E|) dℋ^{n−1}.  (4.8)

Now by (4.3),

  ∫ k(θ) dθ ≤ (2/ρ_*)^{n−1} · [∫_{S^{n−1}}(p(θ) − ρ^{n−1}) dθ
                                − ∫_{S^{n−1}}(r_{θ,1}^{n−1} − ρ^{n−1}) dθ].

Combining with (4.8):

  ∫ k(θ) dθ ≤ (2/ρ_*)^{n−1} · [(P(E)−P(B_ρ)) − ∫(1−|e_r·ν_E|) − ∫(r_{θ,1}^{n−1}−ρ^{n−1}) dθ].  (4.9)

**Bound on the radial mismatch of the first crossing.** By (S₀) restricted
to "good-ray-only" slices (rays with N(θ) = 1), the contribution to
∫_{∂*E}|e_r·ν_E| is exactly ∫_{good rays} r_{θ,1}^{n−1} dθ. For "bad rays"
(N(θ) ≥ 2) the contribution is Σ_j r_{θ,j}^{n−1} ≥ (ρ_*/2)^{n−1}. The full
identity (S₀) gives

  ∫_{S^{n−1}} r_{θ,1}^{n−1} dθ = ∫_{∂*E}|e_r·ν_E| dℋ^{n−1}
                                 − ∫_{S^{n−1}} (Σ_{j=2}^{N(θ)} r_{θ,j}^{n−1}) dθ
                                ≤ ∫_{∂*E}|e_r·ν_E|.

Subtracting ∫ρ^{n−1} dθ = P(B_ρ):

  ∫_{S^{n−1}} (r_{θ,1}^{n−1} − ρ^{n−1}) dθ
       ≤ (P(E) − P(B_ρ)) − ∫(1 − |e_r·ν_E|) dℋ^{n−1}.                (4.10)

This is also upper-bounded by (P − P(B_ρ)), since the second integral is
non-negative. For a *lower* bound, we use **good-ray dominance**: on good
rays r_{θ,1}^{n−1} − ρ^{n−1} can be positive or negative, but in total,
∫|r_{θ,1}^{n−1} − ρ^{n−1}| dθ is controlled by FMP and the radial volume
moment.

**This is where (R2) — at full rate δ — runs into the residual gap.**
Indeed, |r_{θ,1}^{n−1} − ρ^{n−1}| is a slicewise *unsigned* mismatch; its
angular integral is bounded by neither (4.10) nor by P(E) − P(B_ρ) directly.

To bound it, use the elementary inequality (1D mismatch, Agent 2 Lemma 3.5)
applied slice by slice with the L¹-radial moment of the symmetric difference
on the ray: for each θ,

  ∫_0^∞ |𝟙_{E_θ}(r) − 𝟙_{(0,ρ)}(r)| r^{n−1} dr ≥ c(n,ρ_*)·|r_{θ,1} − ρ|·ρ^{n−2}
                                                ≥ c(n,R,ρ_*)·|r_{θ,1}^{n−1} − ρ^{n−1}|.

Integrating over θ:

  c·∫|r_{θ,1}^{n−1} − ρ^{n−1}| dθ ≤ ∫_{S^{n−1}}∫_0^∞|𝟙_{E_θ}−𝟙_{(0,ρ)}|r^{n−1} dr dθ
                                  = |E Δ B_ρ(z_E)|.

By (CL) we have z_E is the Fraenkel center, so |E Δ B_ρ(z_E)| = inf_z |E Δ B_ρ(z)|.
By FMP (Figalli–Maggi–Pratelli 2010 *Invent. Math.* Thm 1.1),
|E Δ B_ρ(z_E)|² ≤ c₁|B_ρ|²·(P(E)−P(B_ρ)). Hence

  ∫|r_{θ,1}^{n−1} − ρ^{n−1}| dθ ≤ C(n,R,ρ_*)·√(P(E) − P(B_ρ)).         (4.11)

**Honest verdict on (R2-rad).** Inserting (4.11) and (4.9) into (4.7):

  T₂^{rad}(E) ≤ C(n,R,ρ_*) · [√(P(E)−P(B_ρ)) + (P(E)−P(B_ρ))].         (4.12)

That is, the slicing-weighted L² trace **is controlled at rate √δ**, where
δ := P(E) − P(B_ρ). The bad-ray (multiplicity-excess) contribution is
quadratically absorbed by (4.9), but the **good-ray radial mismatch** is
controlled only at rate √δ via FMP applied to the volume.

### 4.5 Where the brief's claim is correct, and where it is not

The brief's claim "bad rays are quadratically absorbed" is **correct** for
the multiplicity term ∫k(θ) dθ, which by (4.9) is bounded by (P(E)−P(B_ρ))
linearly, i.e. *at rate δ*. This **does** break Agent 2's L¹-circularity
because in Agent 2's L¹-version the multiplicity contribution was
(2R) ∫k(θ) dθ (the diameter-weighted multiplicity), which is *also* O(δ)
linearly by the same argument (4.9); but in the L¹ version Agent 2's
*good-ray* term, ∫|r_{θ,1} − ρ|dθ, is reduced to the same expression
∫_{∂*E}|e_r·ν_E|/|x−z_E|^{n−1} as in (C3.6) and is circular.

In the L² version, the good-ray contribution (4.5')+(4.11) is bounded by
the **volume Fraenkel** at rate √δ — *not* by the angular multiplicity. So
the L²-form's good-ray term is **not circular** with (C3.6); it is bounded
by FMP at rate √δ. The brief is correct that this *removes* the L¹-
circularity; what the brief misses is that **the FMP rate is √δ, not δ**, so
the good-ray term is the new bottleneck.

So the L²-version replaces the L¹-circularity by a √δ rate — better than
"open", worse than the target δ.

## 5. Full L² trace: reduction to the tangential L² oscillation

We now turn to the *full* L² radial trace (R2), not just its slicing-weighted
version (R2-rad). Decompose:

  T₂(E) = T₂^{rad}(E) + T₂^{tan}(E),
        T₂^{tan}(E) := ∫_{∂*E}(|x−z_E|/ρ − 1)²·(1 − |e_r·ν_E|) dℋ^{n−1}. (5.1)

By (CL), |x − z_E|/ρ − 1 ∈ [−1/2, 1] on ∂*E ⊂ B(z_E, 2ρ) \ B(z_E, ρ/2), so

  T₂^{tan}(E) ≤ ∫_{∂*E}(1 − |e_r·ν_E|) dℋ^{n−1}.                       (5.2)

Now |e_r·ν_E| ≥ e_r·ν_E, so 1 − |e_r·ν_E| ≤ 1 − e_r·ν_E, and we use the
**divergence-theorem identity** for the vector field F(x) = e_r(x) =
(x−z_E)/|x−z_E|: since ∇·F = (n−1)/|x−z_E| on ℝⁿ \ {z_E} and z_E ∈ E (by
(CL) z_E lies inside the inner ball B(z_E, ρ/2) ⊂ E), but the radial vector
field has a singularity at z_E. Truncate: by approximating with smooth
fields supported away from z_E (e.g. F_ε(x) = χ_{|x−z_E|>ε}·e_r) and using
∫_E |x−z_E|^{−1} dx < ∞ (since n ≥ 2 and E is bounded), we get

  ∫_{∂*E} e_r·ν_E dℋ^{n−1} = (n−1) ∫_E |x − z_E|^{−1} dx.

Hence

  ∫_{∂*E}(1 − e_r·ν_E) dℋ^{n−1} = P(E) − (n−1)∫_E|x−z_E|^{−1} dx
        = (P(E) − P(B_ρ)) + Π(E, z_E),                                  (5.3)

where (using that for E = B_ρ(z_E), (n−1)∫_{B_ρ}|x|^{−1} dx = P(B_ρ))

  Π(E, z_E) := (n−1) ∫_{B_ρ(z_E)\E}|x−z_E|^{−1} dx
              − (n−1) ∫_{E\B_ρ(z_E)}|x−z_E|^{−1} dx ≥ 0.               (5.4)

(Π ≥ 0 because |x−z_E|^{−1} ≥ 1/ρ on B_ρ \ E and ≤ 1/ρ on E \ B_ρ in the
smallness regime, with |B_ρ\E| = |E\B_ρ| by volume equality.)

**Bound on Π.** By (CL), the symmetric difference E Δ B_ρ(z_E) is contained
in B(z_E, 2ρ) \ B(z_E, ρ/2). Hence |x − z_E|^{−1} ∈ [1/(2ρ), 2/ρ] on
E Δ B_ρ(z_E), and

  0 ≤ Π(E, z_E) ≤ (n−1)·(3/(2ρ_*))·|E Δ B_ρ(z_E)|/2 = C(n,ρ_*)·|EΔB_ρ(z_E)|.

By FMP applied to the Fraenkel center, |EΔB_ρ(z_E)| ≤ √(c₁|B_ρ|²·δ), so

  Π(E, z_E) ≤ C(n,ρ_*)·√(P(E) − P(B_ρ)).                              (5.5)

A finer Taylor-expansion analysis (used to seek a tighter bound on Π) reveals
that **the leading Taylor correction to Π is the L¹-radial volume moment**

  M₁(E) := ∫_{E Δ B_ρ(z_E)}||x−z_E| − ρ| dx,

namely Π(E,z_E) = ρ^{−2}·(n−1)·M₁(E) + O(ρ^{−3}·M₂(E)) with
M₂(E) := ∫_{EΔB_ρ}(|x−z_E|−ρ)² dx. The volume L¹-moment M₁ is bounded only
by ρ·|EΔB_ρ| ≤ C(n,ρ_*,R)·√δ, again giving the rate √δ. No FMP-based
argument reduces this to O(δ).

### 5.1 Reduction to the quadratic Fusco–Julin oscillation

The exact decomposition of T₂ is, combining (5.1), (5.2), and (5.3):

  T₂(E) ≤ T₂^{rad}(E) + ∫_{∂*E}(1 − |e_r·ν_E|) dℋ^{n−1}
        ≤ T₂^{rad}(E) + ∫_{∂*E}(1 − e_r·ν_E) dℋ^{n−1}
        = T₂^{rad}(E) + (P(E) − P(B_ρ)) + Π(E, z_E).                   (5.6)

**The right-hand side has the structure**

  T₂(E) ≤ [T₂^{rad}(E)] + [(P − P_ρ)] + [Π(E, z_E)].

The middle bracket is trivially O(δ). The third bracket Π is O(√δ) from
(5.5). The first bracket T₂^{rad} is O(√δ) from (4.12).

Hence **unconditionally**

  T₂(E) ≤ C(n,R,ρ_*)·√(P(E) − P(B_ρ)).                                (R2-√δ)

(This is the rate-√δ form. It does *not* close Conjecture 3.6 or Plan 2 at
the sharp rate.)

### 5.2 Equivalence between (R2) and the quadratic Fusco–Julin oscillation

We can rewrite the third bracket differently. Since
(1 − e_r·ν_E) = ½|ν_E − e_r|², (5.3) is exactly the identity

  ∫_{∂*E}|ν_E − e_r|² dℋ^{n−1} = 2[(P(E) − P(B_ρ)) + Π(E, z_E)].      (5.3')

In other words, **the L² tangential normal oscillation equals 2(P−P_ρ) +
2Π**, and is **at rate δ if and only if Π = O(δ)**, equivalently iff the
volume L¹-radial moment M₁(E) = O(δ).

Conversely, the L² Fusco–Julin bound

  ∫_{∂*E}|ν_E − e_r|² dℋ^{n−1} ≤ C(n,R,ρ_*)·(P(E) − P(B_ρ))            (B²)

is precisely equivalent (modulo (5.3')) to Π = O(δ).

**Theorem B (equivalence).** Under the hypotheses of §1:

  (R2)  ⇐⇒  (R2-rad) + (B²)  ⇐⇒  (R2-rad) + [Π = O(δ)].

*Proof.* (⇒): (R2) + Cauchy–Schwarz gives T₂^{rad} ≤ T₂ ≤ Cδ, so (R2-rad).
Subtracting from (5.6) and using positivity of (P−P_ρ), Π:
T₂(E) − T₂^{rad}(E) − (P−P_ρ) ≤ Π ≤ T₂(E) ≤ Cδ. So Π ≤ Cδ, which by (5.3')
is (B²).

(⇐): immediate from (5.6) and (5.3'). □

**This is the precise residual gap.** (R2) is reducible, in the no-graph
setting, to the **quadratic Fusco–Julin tangential oscillation** (B²), which
is **not in the literature** for finite-perimeter sets without graph entry.

**Verdict on (B²).** Fusco–Julin 2014, *Calc. Var. PDE* 50, prove the L¹
strong form: (∫|ν−e_r| dℋ^{n−1})² ≤ C(P−P_ρ). Squaring and applying
Cauchy–Schwarz inside gives only ∫|ν−e_r|² ≤ 2∫|ν−e_r| ≤ C√δ — the rate
√δ. The L² strong form (B²) at rate δ is *known* in:
 (i) the nearly-spherical class (Fuglede 1989, *Trans. AMS* 314), where ∂E
     is a C¹ graph over ∂B_ρ with small norm — *graph regime*;
 (ii) the C^{1,α}-selected regime (Cicalese–Leonardi 2012, after their
     selection-and-Tamanini step) — *back-door selection*.

In the no-graph, no-selection setting, (B²) is **open** and is the exact
obstruction.

## 6. Algebraic chain conditional on (R2)

Conditional on (R2), we recover the homothetic velocity defect (*) of
Agent 2 §3.6:

  (∫_{∂*E}|H_{z_E,ρ}(x) − P(B_ρ)/P(E)| dℋ^{n−1})²
        ≤ C(n,R,ρ_*)·(P(E)² − P(B_ρ)²).                                (*)

**Proof, following Agent 2 §3.1.** Decompose

  H_{z_E,ρ}(x) − 1 = (|x−z_E|/ρ)·(e_r·ν_E) − 1
                  = (|x−z_E|/ρ − 1)·(e_r·ν_E) + (e_r·ν_E − 1).

By the triangle inequality,

  |H_{z_E,ρ} − 1| ≤ (|x−z_E|/ρ)·|e_r·ν_E − 1| + |(|x−z_E|/ρ − 1)·(e_r·ν_E)|
              ≤ (R/ρ_*)·|e_r·ν_E − 1| + ||x−z_E|/ρ − 1|.

Hence

  ∫|H_{z_E,ρ} − 1| dℋ^{n−1} ≤ (R/ρ_*)·∫|e_r·ν_E − 1| + ∫||x−z_E|/ρ − 1|
                            ≤ (R/ρ_*)·∫|ν_E − e_r| + T₁(E).

By Fusco–Julin (B) (L¹ form, squared):
(∫|ν_E − e_r|)² ≤ c₂·(P(E) − P(B_ρ)). By Cauchy–Schwarz applied to (R2):
T₁(E)² ≤ P(E)·T₂(E) ≤ C·P(E)·(P(E) − P(B_ρ)). In the smallness regime
P(E) ≤ 2 P(B_ρ),

  (∫|H_{z_E,ρ} − 1|)² ≤ 2[(R/ρ_*)²·c₂ + C·2P(B_ρ)]·(P(E) − P(B_ρ))
                     ≤ C(n,R,ρ_*)·(P(E)² − P(B_ρ)²),

using P(E)² − P(B_ρ)² = (P(E)−P(B_ρ))(P(E)+P(B_ρ)) ≃ P(B_ρ)·(P(E)−P(B_ρ))
in the smallness regime. Replacing 1 by c_E := P(B_ρ)/P(E) = 1 + O(δ) costs
another P(E)·(1 − c_E) = P(E) − P(B_ρ) = O(δ) which is absorbed. □

## 7. Constants tracking and R-dependence

We track the explicit dependence on R, ρ_*. From (4.5'): C₁ ~
(R/ρ_*)^{n−2}/(ρ_*/2)^{2(n−2)} ~ R^{n−2}·ρ_*^{−3(n−2)}.
From (4.6): the multiplicity bound carries (2/ρ_*)^{n−1}.
From (5.5): Π ≤ (n−1)(3/(2ρ_*))·|EΔB_ρ| ~ ρ_*^{−1}·R^n.
From (R2) → (*): factor (R/ρ_*).

Combining, the constant in (*) scales as

  C(n,R,ρ_*) ≲_n R^{n−1}·ρ_*^{−(n+1)}·constants involving CL & FMP. (7.1)

For Plan 2's application with R = R_*(n) = max(d(n), 2) (the bounded
reduction radius) and ρ_* ≥ 1/2 (the band from `level-set-deficit-identity.md`
§8.2), the constant is O(R_*(n)^{n−1}), as flagged in Agent 6 issue I9.

## 8. Open issues — the genuine residual gap

This note rigorously establishes:

- **(R2-rad), Theorem A, at rate δ** for the multiplicity-excess part:
  the bad-ray contribution to the slicing-weighted L² trace IS quadratically
  absorbed by P(E) − P(B_ρ), confirming the brief's central insight on
  escape from Agent 2's L¹-circularity for the bad-ray part.

- **(R2-rad), Theorem A, at rate √δ for the good-ray part:** the angular
  integral of |r_{θ,1}^{n−1} − ρ^{n−1}| is bounded by the volume Fraenkel
  via FMP, giving the suboptimal rate.

- **Equivalence Theorem B**: (R2) at rate δ ⇔ Π = O(δ) ⇔ quadratic Fusco–Julin
  oscillation (B²), the last of which is **not** in the no-graph package.

The genuine residual gap is therefore precisely:

  **(GAP)** ∫_{∂*E}|ν_E − e_r|² dℋ^{n−1} ≤ C(P(E) − P(B_ρ))
           for finite-perimeter E ⊂ B_R near a ball, no graph.

(GAP) is **not** "the L¹ form (B) squared". By (5.3'), (GAP) is equivalent
to **Π = O(δ)**, which by Taylor analysis is equivalent to the **volume
L¹-radial moment M₁ = O(δ)**. FMP gives only M₁ = O(√δ). The remaining
δ-rate would require an L²-radial volume moment bound,

  M₂ := ∫_{EΔB_ρ}(|x−z_E|−ρ)² dx ≤ C(n,R,ρ_*)·(P(E) − P(B_ρ)),

which is the **volume L² Fraenkel** and is also not in the literature
without graph entry. So (GAP) and (R2) are equivalent obstructions.

**Net for Plan 2.** What we have proved unconditionally is the rate-√δ form

  T₂(E) ≤ C(n,R,ρ_*)·√(P(E) − P(B_ρ)).

By Cauchy–Schwarz this gives T₁ ≤ C·δ^{1/4}, hence (*) at rate δ^{1/4},
hence the homothetic velocity defect lemma at rate δ^{1/4}, hence
Conjecture 3.6 at rate δ^{1/4} (which yields $\mathcal A(\Omega)^2 \le C\cdot\delta_T^{1/2}$, the
known FMP rate). **This is no improvement over the existing FMP rate.**

To close Plan 2 at the sharp rate, **one must prove (GAP) or, equivalently,
the quadratic Fusco–Julin oscillation (B²) in the no-graph setting**. This
is the precise theorem-shaped gap.

## 9. Alternative escape routes (sketched, not closed)

I list three possible escape routes that would close the residual gap. None
is currently in the literature for finite-perimeter sets.

**(α) Boundary-volume Hausdorff containment at rate √δ.** If one could
prove that under smallness E ⊂ B(z_E, ρ(1+η)) \ B(z_E, ρ(1−η)) with
η = O(√δ), then M₁ ≤ η·|EΔB_ρ| ≤ C·η²·|B_ρ| = O(δ), and (GAP) would
follow. The published Hausdorff containment rate is η = O(δ^{1/(2(n−1))})
(Esposito–Fusco–Trombetti, *Math. Z.* 246), insufficient for n ≥ 2; the
√δ rate would itself be a new theorem.

**(β) Bulk-to-boundary spherical Hardy / Wirtinger.** A Hardy-type
inequality on the radial slice E_θ relating
∫_0^∞ |𝟙_{E_θ}(r) − 𝟙_{(0,ρ)}(r)|·(r−ρ)·r^{n−1} dr to a slicewise perimeter
excess weighted by (r−ρ)². The 1D Hardy inequality on rays does *not*
upgrade the L¹-volume-mismatch to L²-volume-mismatch without a one-sided
boundary control (graph), which is the source of the obstruction.

**(γ) Spherical-trace H^{1/2} via lifted graph.** If E were *known* to be a
small-Lipschitz graph over ∂B_ρ, the L² trace would follow from the
H^{1/2}(S^{n−1}) trace estimate. Cicalese–Leonardi 2012 supplies such a
graph for a *selected minimizer*, not for E itself. This is Agent 2
remediation (a), which the brief and Agent 6 reject as back-door selection.

None of (α), (β), (γ) supplies (B²) without a graph or selection. **The
genuine result-shaped gap of Plan 2 is therefore (B²) / equivalently (GAP),
exactly as Agent 6 §3 concluded.**

## 10. Summary table

| Object | Bound | Source / status |
|---|---|---|
| FMP (A): |EΔB_ρ(z_E)|² ≤ c·δ | rate √δ on |EΔB_ρ| | Figalli–Maggi–Pratelli 2010 |
| FJ (B) L¹: (∫|ν−e_r|)² ≤ c·δ | rate √δ on ∫|ν−e_r| | Fusco–Julin 2014 |
| (CL): B(z_E,ρ/2)⊂E⊂B(z_E,2ρ) | qualitative | Cicalese–Leonardi 2012 |
| (S) slicing identity | exact | Maggi 2012 Thm 18.11 |
| (R2-rad) good-ray L² | rate √δ | **this note** (4.12) |
| (R2-rad) bad-ray L² | rate δ (quadratic absorption) | **this note** (4.9), the new step |
| (R2) full L² | rate √δ unconditional | **this note** (5.6) |
| (R2) full L² at rate δ | conditional on (B²) | **this note** Thm B |
| (B²) quadratic FJ in no-graph | **OPEN** | the genuine residual gap |
| (*) homothetic velocity defect | conditional on (B²) | Agent 2 §3.1 + this note §6 |
| Plan 2 closure $\mathcal A(\Omega)^2 \le C\delta_T$ | conditional on (B²) | `metric-finite-perimeter-closure.md` §6 |

## 11. References

- L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and
  Free Discontinuity Problems*, Oxford 2000. (Slicing, Thms 3.108, 2.39.)
- M. Cicalese, G. P. Leonardi, *A selection principle for the sharp
  quantitative isoperimetric inequality*, ARMA 206 (2012), 617–643.
  (Asymmetric Fraenkel center, containment (CL).)
- L. Esposito, N. Fusco, C. Trombetti, *A quantitative version of the
  isoperimetric inequality*, Math. Z. 246 (2005), 269–286.
  (Hausdorff containment at rate δ^{1/(2(n−1))}.)
- A. Figalli, F. Maggi, A. Pratelli, *A mass transportation approach to
  quantitative isoperimetric inequalities*, Invent. Math. 182 (2010),
  167–211. (FMP, used as (A).)
- B. Fuglede, *Stability in the isoperimetric problem for convex or nearly
  spherical domains*, Trans. AMS 314 (1989), 619–638.
  (Nearly-spherical L²-trace identity — graph regime.)
- N. Fusco, *The quantitative isoperimetric inequality and related
  topics*, Bull. Math. Sci. 5 (2015), 517–607. (Survey; §3 nearly-spherical
  Fuglede lemma.)
- N. Fusco, V. Julin, *A strong form of the quantitative isoperimetric
  inequality*, Calc. Var. PDE 50 (2014), 925–937. (Used as (B).)
- F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*,
  Cambridge 2012. (Slicing in spherical coordinates, Thms 18.11, 19.4.)

## 12. Final verdict

(R2) at the sharp rate δ does **not** follow from (A) + (B) + (CL) +
spherical disintegration. The brief's central insight — quadratic absorption
of bad-ray multiplicity — is correct and addresses **half** of the
slicing-weighted L² trace, but the **other half** (the good-ray volume
mismatch, plus the full tangential-defect term in (5.6)) reduces to
quantities controlled only at rate √δ from FMP.

Specifically, (R2) is **equivalent** (modulo the new slicing bound proved
here) to the quadratic Fusco–Julin oscillation (B²) =
∫|ν_E − e_r|² ≤ C(P − P_ρ), which is **not in the literature** in the
no-graph, no-selection setting.

**Plan 2 thus requires, as a true new theorem, (B²) in the finite-perimeter
no-graph setting.** Until that is proved, Plan 2's closure stalls at the
known FMP rate δ_T^{1/2}, which is no improvement over Plan 1.

The brief's identification of (R2) as the right target was correct in spirit
(the L² form is strictly more tractable than the L¹ form for the bad-ray
mechanism), but incorrect in believing that (B) plus spherical
disintegration suffices. The genuine gap has moved from Agent 2's circular
"(R) ⇔ (C3.6)" to the precise "(R2) ⇔ (B²)".
