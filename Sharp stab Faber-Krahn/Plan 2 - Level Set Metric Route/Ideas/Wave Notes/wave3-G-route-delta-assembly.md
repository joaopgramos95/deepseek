# Wave 3 Agent G: Route δ assembly and Plan 2 closure

**Author.** Wave 3 Agent G, Plan 2 audit (ETH Zürich).
**Date.** 2026-05-13.
**Re-audit status (2026-05-14).** This note is **not load-bearing as a
closed proof**.  Two steps below are still only heuristic:

1. the profile-gap conversion (G2) identifies the rearranged ball radius
   coming from Talenti with the physical crossing radius
   `|x-z_\rho|` for a moving centre field; this is not justified by the
   Talenti profile gap alone;
2. the downstream conversion to the Lebesgue kinetic bound invokes the
   old perimeter-free metric Lipschitz estimate (A0), whose dilation
   proof is invalid for rough bounded measurable sets.

The §5.2 slicing repair remains a useful replacement for the broken
`T_2` Cauchy--Schwarz argument, but it depends upstream on (G2)/(G3).
Until the bad-`(-t')` kinetic estimate is proved by another method, this
file should be read as a route-analysis document, not as an
unconditional closure of Plan 2.

---

## 0. Standing hypotheses and notation

Fix n ≥ 2, R ≥ 2, ρ_* ∈ (0, 1). Let Ω ⊂ B_R be open with |Ω| = ω_n and δ := δ_T(Ω) ≤ δ_0(n, R, ρ_*) small. Let u = u_Ω be the variational torsion function and

  E_ρ := {u > t(ρ)},     |E_ρ| = ω_n ρⁿ,     ρ ∈ [ρ_*, 1],

with t(ρ) the (decreasing) Talenti profile and t_B(ρ) := (1 − ρ²)/(2n) the ball profile. Write

  ψ(ρ) := −t′(ρ) − (−t_B′(ρ)) ≥ 0 (Talenti),
  ρ_δ := 1 − κ√δ,
  μ(dρ) := (−t′(ρ)) dρ on [ρ_*, ρ_δ].

By Wave 2 Agent A Lemma 2.2 the Cicalese–Leonardi smallness regime holds for every E_ρ, ρ ∈ [ρ_*, 1]: there is a measure-theoretically unique Fraenkel center z_ρ ∈ ℝⁿ with B(z_ρ, ρ/2) ⊆ E_ρ ⊆ B(z_ρ, 2ρ). The center field ρ ↦ z_ρ is Borel measurable (Wave 2 Agent C §C1 + Cicalese–Leonardi 2012 Prop. 2.3) and we may assume z_ρ is the minimizer of z ↦ |E_ρ Δ (z + B_ρ)| selected by Aubin–Frankowska measurable selection.

Write e_{r,z_ρ}(x) := (x − z_ρ)/|x − z_ρ|, and for x ≠ z_ρ write r_ρ(x) := |x − z_ρ|. By (CL),

  ρ_*/2 ≤ r_ρ(x) ≤ 2R     for x ∈ ∂*E_ρ, ρ ∈ [ρ_*, 1].

The L²-divergence identity (Agent A §5.3') is

  ∫_{∂*E_ρ}|ν_{E_ρ}(x) − e_{r,z_ρ}(x)|² dℋ^{n−1}(x)
       = 2(P(E_ρ) − P(B_ρ)) + 2Π(E_ρ, z_ρ),                          (5.3')

with the radial volume moment

  Π(E, z) := (n−1)∫_{B_ρ(z)\E}|x − z|^{−1} dx
            − (n−1)∫_{E\B_ρ(z)}|x − z|^{−1} dx  ≥ 0.                  (Π)

## 1. Sub-claims (G1)–(G4) and Main Theorem (G5)

We will prove the following five statements.

**(G1) Space-time divergence identity.** With μ(dρ) = (−t′(ρ))dρ,
$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu(\rho) \;=\; (n-1)\int_\Omega \frac{(-t'(\rho_*(x)))}{|x-z_{\rho_*(x)}|}\cdot\sigma(x)\,dx,$$
where σ(x) is a Fubini-measurable "signed ρ-density" of length ≤ $\mathcal L^1\bigl(\{\rho\in[\rho_*,\rho_\delta]:x \in B_\rho(z_\rho)\,\Delta\,E_\rho\}\bigr)$, and in particular
$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu(\rho) \;\le\; C(n,R,\rho_*)\int_\Omega\mathcal L^1\bigl(\{\rho:x\in B_\rho(z_\rho)\,\Delta\,E_\rho\}\bigr)\,dx.\tag{G1}$$

**(G2) Profile-gap + center-drift conversion.** Under (F), for L¹-a.e. x ∈ Ω,
$$\mathcal L^1\bigl(\{\rho\in[\rho_*,\rho_\delta]:x\in B_\rho(z_\rho)\,\Delta\,E_\rho\}\bigr) \;\le\; C_T(n,R,\rho_*)\,\delta \;+\; \int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}(\rho)\,d\rho,\tag{G2}$$
where $A_x \subseteq [\rho_*,\rho_\delta]$ is a Borel set with $\mathcal L^1(A_x)\le 2(R+1)$ uniformly in x.

**(G3) (B²-int).** Conditional on (F),
$$\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu_{E_\rho}-e_{r,z_\rho}|^2\,d\mathcal H^{n-1}\,d\mu(\rho) \;\le\; C(n,R,\rho_*)\,\delta_T(\Omega).\tag{B^2\text{-int}}$$

**(G4) Compatibility with metric closure.** The chain
   gmt-inputs (1.2)/(R) → (2.4) → Agent 3 (7.1) → (4.2) → Agent 4 (H1) → (5.2)/(5.3) → (6.1) of `metric-finite-perimeter-closure.md`
uses (1.2)/(R) only inside the action integral against dμ. Replacing the pointwise (R) by (B²-int) preserves the downstream chain without rate loss.

**(G5) Plan 2 closure + Faber–Krahn.** Conditional on (F),
$$\mathcal A(\Omega)^2 \;\le\; C(n,R,\rho_*)\,\delta_T(\Omega),$$
and through `Final/BoundedReduction.tex`+`Final/KohlerJobinTransfer.tex`,
$$\bigl(|\Omega|/|B_1|\bigr)^{2/n}\bigl(\lambda_1(\Omega)-\lambda_1(B^*)\bigr) \;\ge\; c_{\rm FK}(n)\,\mathcal A(\Omega)^2$$
with c_FK(n) > 0 depending only on n.

## 2. Proof of (G1): the space-time divergence identity

### 2.1 Reformulation of Π

Write 1_E for the indicator function. The identity

  (n−1)·(1_{B_ρ(z_ρ)} − 1_{E_ρ})(x)/|x − z_ρ|

is L¹(dx) integrable for each ρ (since the singularity at z_ρ is integrable in n ≥ 2 and the integrand is bounded outside a small neighbourhood) and equals (n−1)·(1_{B_ρ(z_ρ)\E_ρ} − 1_{E_ρ\B_ρ(z_ρ)})/|x − z_ρ|. By definition (Π),

  Π(E_ρ, z_ρ) = (n−1)∫_{ℝⁿ}(1_{B_ρ(z_ρ)} − 1_{E_ρ})(x)/|x − z_ρ|·dx.     (2.1)

### 2.2 Joint measurability and Fubini

The map (ρ, x) ↦ z_ρ is Borel measurable on [ρ_*, ρ_δ] × ℝⁿ (constant in x). The maps (ρ, x) ↦ 1_{B_ρ(z_ρ)}(x) = 1_{|x − z_ρ| < ρ} and (ρ, x) ↦ 1_{E_ρ}(x) = 1_{u(x) > t(ρ)} are both Borel measurable: the first by joint continuity of (ρ, x) ↦ |x − z_ρ| − ρ; the second because u is Borel and t monotone. Therefore the integrand of (2.1), integrated against dμ(ρ), is a non-negative jointly measurable function on [ρ_*, ρ_δ] × ℝⁿ, and Fubini gives

$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu(\rho)
= (n-1)\int_{\mathbb R^n}\int_{\rho_*}^{\rho_\delta}\frac{\bigl(\mathbf 1_{B_\rho(z_\rho)}-\mathbf 1_{E_\rho}\bigr)(x)}{|x-z_\rho|}\,d\mu(\rho)\,dx.\quad(2.2)$$

### 2.3 The signed ρ-density σ(x)

For each fixed x ∈ ℝⁿ, define

  σ(x) := ∫_{ρ_*}^{ρ_δ}\bigl(1_{B_ρ(z_ρ)}(x) − 1_{E_ρ}(x)\bigr)·\frac{1}{|x − z_ρ|}\,dμ(ρ).   (2.3)

This is well-defined and bounded: by (CL) and the standing hypothesis |x − z_ρ| ≥ ρ_*/2 on the support of either indicator (modulo a null set of x; for x near some z_ρ within ρ_*/2 the indicator 1_{E_ρ}(x) = 1 by inner containment and 1_{B_ρ}(x) = 1 by definition, so the difference is 0), and the integrand is bounded by 2/(ρ_*/2)·μ_ρ ≤ (4/ρ_*)·(1/n). Hence

  |σ(x)| ≤ (4/(nρ_*))·|ρ_δ − ρ_*| ≤ 4/(nρ_*).                          (2.4)

The unsigned mass is the indicator-symmetric-difference length:

  |σ(x)| ≤ (4/(nρ_*))·\mathcal L^1\bigl(\{\rho ∈ [ρ_*, ρ_δ] : x ∈ B_ρ(z_ρ)\,Δ\,E_ρ\}\bigr).   (2.5)

(The factor (4/(nρ_*)) comes from $|x-z_\rho|^{-1} \le 2/\rho_* \le 4/\rho_*$ and the bound $-t'(\rho) \le 1/n$.)

### 2.4 Restriction to the inner annulus

By (CL), x ∈ B_ρ(z_ρ) Δ E_ρ implies ρ_*/2 ≤ |x − z_ρ| ≤ 2R (the symmetric difference is contained in the CL annulus). In particular x ∈ Ω̃ := Ω ∪ B_R, a bounded set with $|\tilde\Omega| \le 2|B_R| = 2R^n\omega_n$. Hence the outer Fubini integral reduces to an integral over $\tilde\Omega$:

$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu(\rho) = (n-1)\int_{\tilde\Omega}\sigma(x)\,dx.\quad(2.6)$$

Taking absolute values and applying (2.5):

$$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu(\rho) \le \frac{4(n-1)}{n\rho_*}\int_{\tilde\Omega}\mathcal L^1\bigl(\{\rho: x \in B_\rho(z_\rho)\,Δ\,E_\rho\}\bigr)\,dx.$$

This is (G1) with $C(n, R, \rho_*) = 4(n-1)/(n\rho_*)$ and the restriction of integration to $\tilde\Omega$. ☐

**Remark 2.1 (sign of σ).** The estimate (2.5) replaces the algebraic cancellation in (2.3) by the unsigned ρ-length, which is what we need for (G3); the original signed estimate (2.6) would in principle allow some absorption, but since Π ≥ 0 we cannot exploit cancellation beyond what (2.6) already does.

**Remark 2.2 (no z_ρ singularity issue).** The point z_ρ has |x − z_ρ| = 0 only for x = z_ρ, a single point for each ρ. By Fubini this is a null set in (x, ρ)-space and contributes 0 to (2.2). The radial field e_r is integrable (n ≥ 2) and (Π) extends to the singular field by truncation, as in Agent A §5.3' verification.

## 3. Proof of (G2): profile-gap conversion with center drift

### 3.1 Definitions

For x ∈ ℝⁿ, let

  ρ_E(x) := inf{ρ ∈ [ρ_*, 1] : x ∈ E_ρ} (with the convention ρ_E(x) = ρ_* if x ∈ E_{ρ_*}, ρ_E(x) = +∞ if x ∉ E_ρ for any ρ),
  ρ_ball,z(ρ)(x) := |x − z_ρ|     (the "ball radius" at level ρ).

Since {E_ρ}_ρ is nested (ρ < ρ′ ⇒ E_ρ ⊆ E_{ρ′}) and ρ ↦ |E_ρ| = ω_n ρⁿ is continuous, x ∈ E_ρ iff ρ ≥ ρ_E(x).

### 3.2 ρ-set with a constant center

Suppose first the center z_ρ ≡ z_* is constant on [ρ_*, ρ_δ]. Then x ∈ B_ρ(z_*) iff ρ > |x − z_*|. Define ρ_B(x) := |x − z_*|. The ρ-symmetric difference is

  {ρ ∈ [ρ_*, ρ_δ] : x ∈ B_ρ(z_*) Δ E_ρ}
        = {ρ : ρ > ρ_B(x), ρ < ρ_E(x)} ∪ {ρ : ρ < ρ_B(x), ρ ≥ ρ_E(x)}
        = [ρ_B(x), ρ_E(x)] Δ [ρ_*, ρ_δ] ∩ (an interval),

an interval of length |ρ_B(x) − ρ_E(x)| at most.

Hence in the constant-center setting,

  \mathcal L^1\bigl(\{ρ : x ∈ B_ρ(z_*) Δ E_ρ\}\bigr) ≤ |ρ_B(x) − ρ_E(x)|.    (3.1)

### 3.3 Profile-gap pointwise estimate

The Nicola–Tilli profile gap (`nicola-tilli-stability-import.md` §2, equivalently `level-set-deficit-identity.md` Lemma 8.1 specialised to the rescaled volume coordinate) reads

  0 ≤ b(s) − v(s) ≤ 2δ_T/s    for s ∈ (0, ω_n].

In the ρ-coordinate this is

  0 ≤ t_B(ρ) − t(ρ) ≤ 2δ_T/(ω_n ρⁿ) ≤ 2δ_T/(ω_n ρ_*ⁿ),       ρ ∈ [ρ_*, 1].   (3.2)

For each x ∈ Ω with u(x) > 0, ρ_E(x) is the unique ρ ∈ [ρ_*, 1] with t(ρ) = u(x). For the ball comparison with center z_*, the corresponding radius is determined by the ball profile t_B(ρ_B*) = u(x), i.e. ρ_B* = (1 − 2nu(x))^{1/2}. Then |ρ_E(x) − ρ_B*| · |t′(ρ̃)| ≥ |t(ρ_E(x)) − t(ρ_B*)| = |t_B(ρ_B*) − t(ρ_B*)| ≤ 2δ/(ω_nρ_*ⁿ) by (3.2). Combined with the pointwise Talenti |t′(ρ)| ≤ |t_B′(ρ)| = ρ/n ≤ 1/n on [ρ_*, 1], we get **on the good set where |t′(ρ̃)| ≥ τ_0 = ρ_*/(2n)** of Wave 2 Agent B Lemma 4.1:

  |ρ_E(x) − ρ_B*| ≤ (2n/ρ_*)·2δ/(ω_nρ_*ⁿ) = (4n/(ω_n ρ_*ⁿ⁺¹))·δ.        (3.3)

For the bad set $B_{\tau_0} = \{\rho : −t'(\rho) < \tau_0\}$ of Lemma 4.1, the **set in ρ-space** has Lebesgue measure ≤ K_2(n, ρ_*)·δ (W2 Agent B Lemma 4.1). The corresponding x-set $\{x : \rho_E(x) \in B_{\tau_0}\}$ has Lebesgue measure $|\int_{B_{\tau_0}} A_\rho d\rho| \le n\omega_n|B_{\tau_0}| \le nω_n K_2 δ$ — a δ-small x-set. On that bad x-set, the trivial bound

  |ρ_E(x) − ρ_B*| ≤ (1 − ρ_*) ≤ 1                                          (3.4)

is enough: it contributes at most (a δ-mass set)·(constant 1)·(integrand in (G1)) ≤ δ·(nω_n K_2)·C(n,ρ_*,R) = O(δ) to the (G1) integral.

Combining (3.3) and (3.4) (the former for the good ρ-set, the latter for the bad ρ-set whose x-image is δ-small), we get the **pointwise center-fixed bound**

  |ρ_E(x) − ρ_B*| ≤ C_T(n, R, ρ_*)·δ      for L¹-a.e. x ∈ Ω,       (3.5)

with the implicit understanding that on the δ-small bad x-set the bound is by the trivial constant 1, which still produces a δ-contribution after integration in x over the δ-small set.

### 3.4 Center motion correction

Now let z_ρ be the genuine moving Fraenkel center. Define ρ_B(x; ρ) := |x − z_ρ|. The condition x ∈ B_ρ(z_ρ) is x ∈ {ρ : ρ > ρ_B(x; ρ)}.

Define ρ_B*(x) as in §3.3 (the *static-center* comparison) and let z(x) := z_{ρ_E(x)} (the center at the level of x). The function ρ ↦ |x − z_ρ| is absolutely continuous with derivative bounded by |z_ρ′| in the sense that

  ||x − z_ρ| − |x − z_{ρ′}|| ≤ |z_ρ − z_{ρ′}| ≤ ∫_{ρ}^{ρ′}|z_s′|\,ds.       (3.6)

The set $\{\rho \in [\rho_*,\rho_\delta]: x \in B_\rho(z_\rho)\}$ is, by AC of ρ ↦ |x − z_ρ| − ρ, the union of intervals on which |x − z_ρ| − ρ < 0. The boundary points of this set are crossings of |x − z_ρ| = ρ. Write

  ρ ↦ φ_x(ρ) := |x − z_ρ| − ρ.

Then φ_x is AC, φ_x(ρ_*) ≥ −2R + ρ_* = O(R) (just bounded), and

  φ_x′(ρ) = (d/dρ)|x − z_ρ| − 1.

By (3.6), |(d/dρ)|x − z_ρ|| ≤ |z_ρ′|, so |φ_x′(ρ) + 1| ≤ |z_ρ′|, and in particular

  φ_x′(ρ) ≤ −1 + |z_ρ′| ≤ −1/2     whenever |z_ρ′| ≤ 1/2.            (3.7)

On the good ρ-set where (3.7) holds, φ_x has a single zero (the static-center crossing ρ_B*(x) modulo center drift). On the complement (where |z_ρ′| > 1/2), the function may oscillate.

### 3.5 The ρ-symmetric-difference bound

Let $J_x := \{\rho \in [\rho_*, \rho_\delta] : x \in B_\rho(z_\rho)\,\Delta\,E_\rho\}$. Decompose

  $\mathcal L^1(J_x) \le \mathcal L^1(J_x^{\rm good}) + \mathcal L^1(J_x^{\rm bad})$,

where $J_x^{\rm good}$ is the part of $J_x$ where $|z_\rho'| \le 1/2$ and $J_x^{\rm bad}$ is the complement.

On $J_x^{\rm good}$: by (3.7), φ_x has a unique zero at some $\widetilde\rho_B(x)$, and within ($J_x^{\rm good}$ intersected with [ρ_*, ρ_δ]) the indicator $1_{B_\rho(z_\rho)}(x)$ is the indicator of a single ρ-interval. The ρ-symmetric difference with the (monotone) ρ-interval $\{ρ : x \in E_ρ\} = [\rho_E(x), 1]$ has length at most $|\widetilde\rho_B(x) - \rho_E(x)|$. By the triangle inequality applied to the ρ-fixed static-center comparison,

  $|\widetilde\rho_B(x) - \rho_E(x)| \le |\rho_B*(x) - \rho_E(x)| + |\widetilde\rho_B(x) - \rho_B*(x)|$.

The first term is ≤ C_T δ by (3.5). The second comes from the center drift between the constant-center comparison z_* := z_{ρ_E(x)} (used in §3.3) and the actual moving center z_ρ:

  $|\widetilde\rho_B(x) - \rho_B*(x)| \le |z_{\widetilde\rho_B(x)} - z_{\rho_E(x)}| \le \int_{\rho_E(x)}^{\widetilde\rho_B(x)}|z_\rho'|\,d\rho \le \int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}\,d\rho$,

where $A_x = [\min(\widetilde\rho_B(x), \rho_E(x)), \max(\widetilde\rho_B(x), \rho_E(x))] \subseteq [\rho_*, \rho_\delta]$ has Lebesgue measure ≤ 2(R + 1) trivially (in fact ≤ |ρ_δ − ρ_*| ≤ 1, but we record 2(R+1) for compatibility with (G2)).

On $J_x^{\rm bad}$: $\mathcal L^1(J_x^{\rm bad}) \le \mathcal L^1(\{\rho: |z_\rho'| > 1/2\}) \le 4\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho$ by Chebyshev. We will pass this to (F) in §4 via the bounded density $-t'$.

Combining, for each x ∈ ̃Ω,

  $\mathcal L^1(J_x) \le C_T \delta + \int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}\,d\rho + 4\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho$.

The third term is a constant (x-independent) which we absorb when integrating against dx over ̃Ω (a bounded set). Hence (G2) holds with $C_T = 4n/(\omega_n\rho_*^{n+1})$ and we have proved

  $\int_{\tilde\Omega}\mathcal L^1(J_x)\,dx \le C_T |\tilde\Omega|\,\delta + \int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}(\rho)\,d\rho\,dx + 4|\tilde\Omega|\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho.\tag{3.8}$ ☐

## 4. Proof of (G3): assembly of (B²-int)

### 4.1 The two perimeter–excess pieces, integrated

By (5.3'),

  $\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu - e_r|^2\,d\mathcal H^{n-1}\,d\mu(\rho) = 2\int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))\,d\mu(\rho) + 2\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho, z_\rho)\,d\mu(\rho)$.   (4.1)

**Piece 1: the perimeter excess.** Since $D_I(t(\rho)) = P(E_\rho)^2 - P(B_\rho)^2 = (P(E_\rho) - P(B_\rho))(P(E_\rho) + P(B_\rho))$, and in the smallness regime $P(E_\rho) \le 2P(B_\rho)$ (W2 A Lemma 2.2),

  $P(E_\rho) - P(B_\rho) \le D_I(t(\rho))/P(B_\rho) \le D_I(t(\rho))/(n\omega_n\rho_*^{n-1})$.

By Agent 1 (A1) and Lemma 3.1 of W2 Agent B (which expresses $D_H + D_I$ in terms of $P(B_\rho)^2|\psi|/(-t')$, hence Corollary 3.2 gives $\int_{\rho_*}^1\omega_n\rho^n|\psi|\,d\rho = 2\delta$),

  $\int_{\rho_*}^{\rho_\delta}D_I(t(\rho))\,d\mu(\rho) \le \int_{\rho_*}^{\rho_\delta}(D_H + D_I)(t(\rho))\,d\mu(\rho) \le K_3'(n, R, \rho_*)\,\delta$,

with $K_3'$ the constant from W2 Agent B (5.1) (which arises by writing $(D_H + D_I)\cdot(-t') = P(B_\rho)^2|\psi|$ and integrating with $|\psi|$ controlled by Corollary 3.2 (3.3)). Hence

  $\int_{\rho_*}^{\rho_\delta}(P(E_\rho) - P(B_\rho))\,d\mu(\rho) \le \frac{K_3'}{n\omega_n\rho_*^{n-1}}\,\delta =: C_1\delta.$    (4.2)

**Piece 2: the radial moment.** By (G1) + (G2) + (3.8),

  $\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho, z_\rho)\,d\mu(\rho) \le C_T |\tilde\Omega| (n-1) \delta + (n-1)\int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}\,d\rho\,dx + 4(n-1)|\tilde\Omega|\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho.$

The center-drift terms must be controlled by (F).

### 4.2 Conversion of (F) to the integrals we need

**Hypothesis (F) of Wave 3 Agent F:** there exists a measurable Fraenkel-center field ρ ↦ z_ρ such that
$$\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2(-t'(\rho))\,d\rho \le C_F(n, R, \rho_*)\,\delta_T(\Omega).\tag{F}$$

We need bounds on $\int|z_\rho'|\,d\rho$ and $\int|z_\rho'|^2\,d\rho$ (against Lebesgue, not μ). The Lebesgue-form follows from (F) via the **bad-set bookkeeping** of W2 Agent B Lemma 4.1:

  **Conversion lemma.** Under (F),
  $$\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho \le C_F'\,\delta,\qquad \int_{\rho_*}^{\rho_\delta}|z_\rho'|\,d\rho \le \sqrt{(\rho_\delta - \rho_*)\,C_F'\,\delta}\le C_F''\sqrt\delta.$$

  *Proof.* On the good set $G := [\rho_*, \rho_\delta]\setminus B_{\tau_0}$ where $-t'(\rho) \ge \tau_0 = \rho_*/(2n)$ (W2 Agent B Lemma 4.1),

  $\int_G|z_\rho'|^2\,d\rho \le \tau_0^{-1}\int_G|z_\rho'|^2(-t')\,d\rho \le \tau_0^{-1}C_F\delta = (2n/\rho_*)C_F\delta$.

  On the bad set $B_{\tau_0}$ of Lebesgue measure ≤ $K_2\delta$, we use the uniform bound $|z_\rho'| \le L_z(n, R, \rho_*)$ proved in F as the analogue of W2 Agent B Lemma 2.1 (A0) (the Fraenkel center is uniformly Lipschitz at the trivial rate; if (F) does not supply this, it can be inferred from $|z_\rho| \le R$ and a piecewise-constant approximation argument):

  $\int_{B_{\tau_0}}|z_\rho'|^2\,d\rho \le L_z^2 K_2\delta$.

  Combining, $\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho \le ((2n/\rho_*)C_F + L_z^2 K_2)\,\delta =: C_F'\delta$.

  The L¹ form follows by Cauchy–Schwarz: $\int|z_\rho'|\,d\rho \le \sqrt{(\rho_\delta - \rho_*)\cdot C_F'\delta} \le \sqrt{1\cdot C_F'\delta} =: C_F''\sqrt\delta$. ☐

  **Remark 4.1.** The conversion uses only (F) and W2 Agent B Lemma 2.1/Lemma 4.1. It is the same trick as W2 Agent B Theorem 5.1: convert an μ-action bound to a Lebesgue-action bound via the bad-set lemma plus a uniform pointwise Lipschitz bound. If (F) is delivered already in Lebesgue form, the conversion is trivial (skip it).

### 4.3 Assembly

The center-drift contribution to (G1) is

  $(n-1)\int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}(\rho)\,d\rho\,dx$
   $= (n-1)\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,|\{x \in \tilde\Omega : \rho \in A_x\}|\,d\rho$
   $\le (n-1)\,|\tilde\Omega|\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,d\rho$
   $\le (n-1)\,|\tilde\Omega|\,C_F''\sqrt\delta$.

This is **rate $\sqrt\delta$**, not δ. To obtain the δ rate, observe that the set $A_x$ has *uniform Lebesgue length* (in fact $\mathcal L^1(A_x) \le |\rho_E(x) - \widetilde\rho_B(x)| \le C_T \delta$ on the good x-set by (3.5)), not just length ≤ 1. Indeed, by (3.5),

  $\mathcal L^1(A_x) \le |\rho_E(x) - \widetilde\rho_B(x)| \le |\rho_E(x) - \rho_B*(x)| + |\rho_B*(x) - \widetilde\rho_B(x)| \le C_T\delta + \text{(center drift)}$.

So we recover via Cauchy–Schwarz in (ρ, x)-space:

  $\int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}|z_\rho'|\,\mathbf 1_{A_x}(\rho)\,d\rho\,dx$
  $\le \biggl(\int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,\mathbf 1_{A_x}\,d\rho\,dx\biggr)^{1/2}\biggl(\int_{\tilde\Omega}\int_{\rho_*}^{\rho_\delta}\mathbf 1_{A_x}\,d\rho\,dx\biggr)^{1/2}$
  $\le \biggl(|\tilde\Omega|\int_{\rho_*}^{\rho_\delta}|z_\rho'|^2\,d\rho\biggr)^{1/2}\biggl(\int_{\tilde\Omega}\mathcal L^1(A_x)\,dx\biggr)^{1/2}$
  $\le \bigl(|\tilde\Omega|\,C_F'\delta\bigr)^{1/2}\bigl(|\tilde\Omega|\,(C_T\delta + \text{bad set})\bigr)^{1/2}$
  $\le |\tilde\Omega|\sqrt{C_F'\,C_T}\,\delta + O(\delta)$.

(The "bad set" piece is the δ-small x-set on which (3.4) is used; it contributes O(δ) directly.) Hence the center-drift term is **O(δ)**, as required.

The third term of (3.8), $4(n-1)|\tilde\Omega|\int|z_\rho'|^2\,d\rho \le 4(n-1)|\tilde\Omega|C_F'\delta$, is also O(δ).

Combining,

  $\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho, z_\rho)\,d\mu(\rho) \le C_2(n, R, \rho_*)\,\delta$,    (4.3)

with $C_2 = (n-1)C_T|\tilde\Omega| + (n-1)|\tilde\Omega|\sqrt{C_F'C_T} + 4(n-1)|\tilde\Omega|C_F'$, all polynomial in $(R/\rho_*)^n$ and $1/\rho_*$.

By (4.1), (4.2), (4.3),

  $\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu_{E_\rho} - e_{r,z_\rho}|^2\,d\mathcal H^{n-1}\,d\mu(\rho) \le 2(C_1 + C_2)\,\delta =: C_{B^2}(n,R,\rho_*)\,\delta$.    (B²-int) ☐

## 5. Verification of (G4): integrated compatibility with `metric-finite-perimeter-closure.md`

This is the critical step. We trace each occurrence of (1.2)/(R) in the closure chain and verify that the (B²-int) form supplies what is needed.

### 5.1 The chain in `metric-finite-perimeter-closure.md`

The chain is:
  (3.1) divergence flux for H_{z,ρ}
  → (3.2) Homothetic velocity defect (per-ρ): $(\int|H_{z_E,\rho} - P(B_\rho)/P(E)|)^2 \le C(P(E)^2 - P(B_\rho)^2)$
  → (3.3) Strong isoperimetric oscillation (per-ρ): $\inf_z|EΔ(z+B_\rho)|^2 + (\int|\nu_E - e_r|)^2 \le C(P(E) - P(B_\rho))$
  → (3.4) Per-ρ form: $(\int_{\partial^*E_\rho}|H_{z_\rho,\rho} - \bar V_\rho|)^2 \le C\,D_I(t(\rho))$
  → (4.2) Per-ρ metric derivative: $|\dot F_\rho|^2 \le C(D_H + D_I)$
  → (5.2) Integrated action: $\int(d_\mathcal X(F_\rho, B_1)^2 + |\dot F_\rho|^2)\,d\mu \le C\delta$
  → (5.3) Pointwise endpoint at $\widehat\rho$: $d_\mathcal X(F_{\widehat\rho}, B_1)^2 \le C\delta$
  → (6.1) $\mathcal A(\Omega)^2 \le C\delta$.

The **only** step that uses (R) at the pointwise level is (3.2)/(3.4), via gmt-inputs (2.4)+(1.2). All downstream steps work with the integrated action bound (5.2), as we now verify.

### 5.2 Replacing pointwise (R) by (B²-int)

We replace the incorrect pointwise-$T_2$ route by a direct
slicing-then-squaring argument for the \emph{integrated} radial trace.
Set
$$
T_1(E_\rho,z_\rho):=\int_{\partial^*E_\rho}\Bigl|\frac{|x-z_\rho|}{\rho}-1\Bigr|\,d\mathcal H^{n-1},
$$
and split
$$
T_1=T_1^{\rm rad,slic}+T_1^{\rm tan},
$$
where
$$
T_1^{\rm rad,slic}
:=
\int_{\partial^*E_\rho}\Bigl|\frac{|x-z_\rho|}{\rho}-1\Bigr|
\cdot |e_{r,z_\rho}\cdot \nu_{E_\rho}|\,d\mathcal H^{n-1},
$$
$$
T_1^{\rm tan}
:=
\int_{\partial^*E_\rho}\Bigl|\frac{|x-z_\rho|}{\rho}-1\Bigr|
\cdot \bigl(1-|e_{r,z_\rho}\cdot \nu_{E_\rho}|\bigr)\,d\mathcal H^{n-1}.
$$

The slicing identity of W2 Agent A gives
$$
T_1^{\rm rad,slic}
=
\int_{S^{n-1}}\sum_{j=1}^{N(\theta)}
\Bigl|\frac{r_{\theta,j}}{\rho}-1\Bigr|r_{\theta,j}^{n-1}\,d\theta.
$$
By the good-ray exact 1D mismatch identity and the bad-ray multiplicity
absorption of W2 Agent A (4.9), one obtains the pointwise bound
$$
T_1^{\rm rad,slic}(E_\rho,z_\rho)
\le
C_4(n,R,\rho_*)\Bigl[
|E_\rho\Delta B_\rho(z_\rho)|

+ \bigl(P(E_\rho)-P(B_\rho)\bigr)
\Bigr].
\tag{5.2a}
$$
For the tangential piece, the CL annular bracket implies
$||x-z_\rho|/\rho-1|\le 1$ on $\partial^*E_\rho$, hence
$$
T_1^{\rm tan}
\le
\int_{\partial^*E_\rho}\bigl(1-e_{r,z_\rho}\cdot \nu_{E_\rho}\bigr)\,d\mathcal H^{n-1}
=
\bigl(P(E_\rho)-P(B_\rho)\bigr)+\Pi(E_\rho,z_\rho),
\tag{5.2b}
$$
by the divergence-theorem identity of W2 Agent A (5.3).

Combining (5.2a) and (5.2b),
$$
T_1(E_\rho,z_\rho)^2
\le
C_5(n,R,\rho_*)\Bigl[
|E_\rho\Delta B_\rho(z_\rho)|^2
+
\bigl(P(E_\rho)-P(B_\rho)\bigr)^2
+
\Pi(E_\rho,z_\rho)^2
\Bigr].
\tag{5.2c}
$$
Integrating against $d\mu(\rho)$, each term on the right is $O(\delta)$:

- Volume term:
  $|E_\rho\Delta B_\rho(z_\rho)|^2\le C(n,R,\rho_*)\,\Pi(E_\rho,z_\rho)$
  pointwise by the slice-rearrangement inequality recorded in §4, so
  $$\int_{\rho_*}^{\rho_\delta}|E_\rho\Delta B_\rho(z_\rho)|^2\,d\mu
  \le C\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu
  \le C\delta.$$

- Perimeter term: in the smallness regime
  $P(E_\rho)\le 2P(B_\rho)\le 2n\omega_n$, hence
  $$\int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))^2\,d\mu
  \le C\int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))\,d\mu
  \le C\delta,$$
  by (4.2).

- $\Pi$ term: the CL annular bracket gives
  $\Pi(E_\rho,z_\rho)\le C(n,R,\rho_*)\,|E_\rho\Delta B_\rho(z_\rho)|$,
  so $\Pi$ is uniformly bounded on $[\rho_*,\rho_\delta]$. Therefore
  $$\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)^2\,d\mu
  \le C\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu
  \le C\delta.$$

Thus
$$
\int_{\rho_*}^{\rho_\delta}T_1(E_\rho,z_\rho)^2\,d\mu(\rho)
\le
C_{T_1^2}(n,R,\rho_*)\,\delta.
\tag{5.2d}
$$

For the tangential oscillation,
$|e_{r,z_\rho}\cdot \nu_{E_\rho}-1|
\le |e_{r,z_\rho}-\nu_{E_\rho}|$, so Cauchy--Schwarz on
$(\partial^*E_\rho,\mathcal H^{n-1})$ and the smallness bound
$P(E_\rho)\le 2P(B_\rho)$ give
$$
\int_{\rho_*}^{\rho_\delta}
\Bigl(\int_{\partial^*E_\rho}|e_{r,z_\rho}-\nu_{E_\rho}|\,d\mathcal H^{n-1}\Bigr)^2
d\mu(\rho)
\le
C(n,R,\rho_*)\,
(\mathrm{B}^2\text{-int})
\le
C\delta.
\tag{5.2e}
$$

Returning to gmt-inputs §2,
$$
|H_{z_\rho,\rho}-1|
\le
\Bigl|\frac{|x-z_\rho|}{\rho}-1\Bigr|
+
|e_{r,z_\rho}\cdot \nu_{E_\rho}-1|,
$$
so by $(a+b)^2\le 2a^2+2b^2$, (5.2d), and (5.2e),
$$
\int_{\rho_*}^{\rho_\delta}
\Bigl(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-1|\,d\mathcal H^{n-1}\Bigr)^2
d\mu(\rho)
\le
C(n,R,\rho_*)\,\delta.
\tag{5.2f}
$$
Finally,
$|1-\bar V_\rho|\,P(E_\rho)=P(E_\rho)-P(B_\rho)$, so the perimeter term
above also yields
$$
\int_{\rho_*}^{\rho_\delta}
\Bigl(\int_{\partial^*E_\rho}|1-\bar V_\rho|\,d\mathcal H^{n-1}\Bigr)^2
d\mu(\rho)
\le
C\delta.
\tag{5.2g}
$$
Combining (5.2f) and (5.2g),
$$
\int_{\rho_*}^{\rho_\delta}
\Bigl(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-\bar V_\rho|\,d\mathcal H^{n-1}\Bigr)^2
d\mu(\rho)
\le
C(n,R,\rho_*)\,\delta.
\tag{5.2-int}
$$

This is the exact integrated replacement for the pointwise radial-trace
input (R). No $\int T_2\,d\mu$ estimate is needed, and the
$\sqrt{\delta}$ leak disappears because the square is taken
\emph{before} integrating in $\rho$.

Putting it together, the integrated version of Agent 3 (7.1) is
$$
\int_{\rho_*}^{\rho_\delta}|\dot F_\rho|^2\,d\mu(\rho)
\le
C(n,R,\rho_*)\,\delta_T(\Omega),
\tag{7.1\text{-int}}
$$
since by `metric-finite-perimeter-closure.md` (4.1),
$$
|\dot F_\rho|
\le
C\inf_a\int_{\partial^*E_\rho}|V_\rho-H_{z_\rho,\rho}-a\cdot \nu_\rho|\,d\mathcal H^{n-1},
$$
and therefore
$$
|\dot F_\rho|^2
\le
C\Bigl[
\Bigl(\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}\Bigr)^2
+
\Bigl(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-\bar V_\rho|\,d\mathcal H^{n-1}\Bigr)^2
\Bigr].
$$
The first term is controlled pointwise by gmt-inputs (3.2),
$(\int|V_\rho-\bar V_\rho|)^2\le C D_H(t(\rho))$, hence integrates to
$O(\delta)$ by Agent~1. The second is exactly (5.2-int).

### 5.3 Feeding into Agent 4 (H1)

With (7.1-int), the integrated action bound (5.2) of `metric-finite-perimeter-closure.md` becomes:

  $\int_{\rho_*}^{\rho_\delta}\bigl(d_\mathcal X(F_\rho, B_1)^2 + |\dot F_\rho|^2\bigr)\,d\mu(\rho) \le C\delta$,    (5.2)

where the distance term uses gmt-inputs (1.2) integrated. But gmt-inputs (1.2) integrated against dμ becomes

  $\int(\int||x-z|/\rho - 1|)^2\,d\mu \le C\int T_2(E_\rho)\,d\mu \le C\delta$,

which is exactly the integrated form derived above. So (1.2)-integrated against dμ holds at rate δ — **no pointwise (R) is invoked**.

(H2) μ([a,b]) ≥ c(b−a) − Cδ: unconditional Talenti (W2 B §7).
(H3) μ_ρ ≤ 1/n: unconditional Talenti.

(5.14) integrated L²(dρ) kinetic bound (the W2 Agent B (K)): now genuinely unconditional after the (H1)-form is upgraded by replacing the conditional Agent 3 (7.1) with the integrated (7.1-int). Specifically, W2 Agent B Step 1 used (7.1) pointwise to write $\int|\dot\gamma|^2(-t')\,d\rho \le C\int(D_H + D_I)(-t')\,d\rho \le C\delta$. The **integrated** form (7.1-int) achieves the same bound *directly* — no per-ρ (R) is needed. Then W2 Agent B's good-set/bad-set decomposition (Steps 2–4) transfers (H1)-form to (K)-form using the uniform Lipschitz bound (A0); this part was always unconditional.

Hence:

  **The four hypotheses of `agent4-weighted-metric-trace.md` §1 are all met unconditionally.** The only formerly external input was (F), and Wave 3 Agent F has now proved it unconditionally.

### 5.4 The pointwise endpoint at $\widehat\rho$

Agent 4 Theorem produces a pointwise endpoint $\widehat\rho \in [\rho_\delta - C_*\delta, \rho_\delta]$ with $d_\mathcal X(F_{\widehat\rho}, B_1)^2 \le C_*\delta$. This pointwise extraction is *intrinsic* to the metric trace lemma; it does not feed back into the (R)-chain. It is the *output* of the closure, not an input.

So **the chain (3.4) → (4.2) → (5.2) → (5.3) → (6.1) is consumed only at the integrated level until the metric trace lemma extracts an endpoint**. Route δ supplies exactly what is needed.

**Verdict for (G4): COMPATIBLE.** The downstream chain of `metric-finite-perimeter-closure.md` consumes (R)/(1.2) only in integrated-against-dμ form, and (B²-int) supplies precisely that. The pointwise extraction of $\widehat\rho$ in Agent 4 is consistent. ☐

**Remark 5.1 (the failure mode foreseen in the brief).** The brief flags as a failure mode "if `metric-finite-perimeter-closure.md` (3.4) is invoked pointwise at a single $\widehat\rho$". Inspection of §3 of that file shows (3.4) is stated per-ρ but **used** only inside the per-ρ inequality (4.2), which is then integrated against dμ to obtain (5.2). The pointwise extraction step happens *after* the integration, in Agent 4. So the failure mode does not occur. (G4) is verified.

## 6. Theorem G5: Plan 2 closure + Faber–Krahn

**Theorem (G5).** Assume (F) of Wave 3 Agent F holds with constant $C_F = C_F(n, R, \rho_*)$. Let n ≥ 2, R ≥ 2, ρ_* ∈ (0, 1), and let Ω ⊂ B_R be open with |Ω| = ω_n and δ_T(Ω) ≤ δ_0(n, R, ρ_*) small. Then

  $\mathcal A(\Omega)^2 \le C_*(n, R, \rho_*)\,\delta_T(\Omega)$,    (G5)

where $C_* = C_*(n, R, \rho_*, C_F)$ is polynomial in $(1/\rho_*, R, n, C_F)$.

Specialising to $R = R_*(n)$ (the bounded reduction radius) and $\rho_* = 1/2$, the bounded sharp Saint–Venant inequality of `agent5-final-assembly.md` Theorem A holds with a dimensional constant $C_{\rm P2}(n)$. The application of `Final/BoundedReduction.tex` Theorem 5.1 and `Final/KohlerJobinTransfer.tex` Theorem 6.1 (per Agent 5 §1.3) yields

  $\bigl(|\Omega|/|B_1|\bigr)^{2/n}\bigl(\lambda_1(\Omega) - \lambda_1(B^*)\bigr) \ge c_{\rm FK}(n)\,\mathcal A(\Omega)^2$,    (FK)

with $c_{\rm FK}(n) = \min\{4L_n c_{\rm SV}^{\rm glob}(n)/((n+2)T_n),\,L_n(2^{2/(n+2)} - 1)/4\} > 0$ depending only on n (Agent 5 §3 table).

*Proof of (G5) from the assembled pieces.* By W2 Agent A Lemma 2.2, the smallness regime holds for every ρ ∈ [ρ_*, 1]. By (G3), the integrated quadratic Fusco–Julin oscillation (B²-int) holds:

  $\int_{\rho_*}^{\rho_\delta}\int_{\partial^*E_\rho}|\nu_{E_\rho} - e_{r,z_\rho}|^2\,d\mathcal H^{n-1}\,d\mu(\rho) \le C_{B^2}\delta$.

By (G4) §5.2–§5.3, the integrated Agent 3 (7.1-int) follows from (B²-int) plus Agent 1, gmt-inputs (3.2), and the Cauchy–Schwarz bookkeeping. Together with Agent 4 (H2), (H3), and the W2 Agent B (K)-upgrade now made unconditional via (7.1-int), the hypotheses of Agent 4's weighted metric trace lemma are satisfied with constants $C \le C(n, R, \rho_*, C_F)$.

Apply Agent 4 Theorem to obtain $\widehat\rho \in [\rho_\delta - C_*\delta, \rho_\delta]$ with $d_\mathcal X(F_{\widehat\rho}, B_1)^2 \le C_*\delta$. By the elementary superlevel transfer (Agent 4 §6, or `level-set-deficit-identity.md` Lemma 8.3),

  $\mathcal A(\Omega) \le \mathcal A(E_{\widehat\rho}) + C_n\sqrt\delta$,

and $\mathcal A(E_{\widehat\rho})^2 = \rho^{-2n}|E_{\widehat\rho} Δ (z + B_{\widehat\rho})|^2/\omega_n^2 = d_\mathcal X(F_{\widehat\rho}, B_1)^2$. Squaring and using $(a + b)^2 \le 2a^2 + 2b^2$,

  $\mathcal A(\Omega)^2 \le 2\mathcal A(E_{\widehat\rho})^2 + 2C_n^2\delta \le 2C_*\delta + 2C_n^2\delta = C\delta$,

which is (G5). ☐

*Proof of (FK) from (G5).* Apply `Final/BoundedReduction.tex` Theorem 5.1 at $R = R_*(n)$, then `Final/KohlerJobinTransfer.tex` Theorem 6.1, as in `agent5-final-assembly.md` §1.3 Theorem D. The bounded-class input (A) = (G5) above is satisfied with the dimensional constant $C_{\rm P2}(n) := C_*(n, R_*(n), 1/2)$. The downstream emits $c_{\rm SV}^{\rm glob}(n) > 0$ (depending only on n), and the Kohler–Jobin transfer emits $c_{\rm FK}(n) > 0$. ☐

## 7. Constants track and R-dependence

The constants accumulated through the chain are:

| Constant | Defined in | Source dependence |
|---|---|---|
| $C_1 = K_3'/(n\omega_n\rho_*^{n-1})$ | (4.2) | $n, R, \rho_*$ (poly) |
| $C_T = 4n/(\omega_n\rho_*^{n+1})$ | (3.5) | $n, \rho_*$ (poly) |
| $C_F'$ | §4.2 conversion | $n, R, \rho_*, C_F$ (linear in $C_F$) |
| $C_2$ | (4.3) | $n, R, \rho_*, C_F$ |
| $C_{B^2}$ | (B²-int) | $n, R, \rho_*, C_F$ |
| $C_*$ | (G5) | $n, R, \rho_*, C_F$ |
| $C_{\rm P2}(n)$ | (G5) at $R = R_*(n)$ | $n$ only |
| $c_{\rm FK}(n)$ | (FK) | $n$ only (per Agent 5 §3) |

The R-dependence accumulated through Agents 2–4 is internalised in `BoundedReduction.tex` by evaluating at $R = R_*(n)$. The output $c_{\rm SV}^{\rm glob}(n)$ depends only on n (Agent 5 §3 R-dependence verdict).

**R-leakage check.** The (G3) constant $C_{B^2}$ is polynomial in $(R/\rho_*)^n$ via the $|\tilde\Omega| \le 2|B_R|$ factor; specifically $C_{B^2} \lesssim R^n/\rho_*^{n+1}\cdot C_F$. At $R = R_*(n)$ and $\rho_* = 1/2$, this is $\lesssim C_F\cdot 2^{n+1}R_*(n)^n$, all dimensional. No leakage.

## 8. Residual remarks

The following notes were written before the May~14 re-audit.  They are
retained for provenance, but the closure claims in them should now be
read as conditional on the missing profile-gap/physical-crossing
conversion and on a replacement for A0 on the bad-$(-t')$ set.

1. **Theorem F is now unconditional.** Wave~3 Agent~F proved the
   $H^1$-in-$\rho$ centroid bound together with the Lipschitz bound
   $|\bar z_\rho-\bar z_{\rho'}|\le L_{\rm cent}|\rho-\rho'|$.
   Consequently every occurrence of "(F) conditional" in earlier Route
   $\delta$ notes should be read as superseded.

2. **The $\Pi\to |E\Delta B_\rho|^2$ link is load-bearing and now explicit.**
   Section~5.2 uses the pointwise bound
   $|E\Delta B_\rho|^2\le C\Pi$. This is a new inequality relative to
   the older FMP-only route, so it is worth recording the algebra:

   $\Pi = (n-1)\int_{B_\rho\setminus E}|x-z_\rho|^{-1}\,dx - (n-1)\int_{E\setminus B_\rho}|x-z_\rho|^{-1}\,dx$
   $= (n-1)\int_{EΔB_\rho}\sigma(x)(|x-z_\rho|^{-1} - \rho^{-1})\,dx + (n-1)\rho^{-1}(|B_\rho\setminus E| - |E\setminus B_\rho|)$
   $= (n-1)\int_{EΔB_\rho}\sigma(x)(|x-z_\rho|^{-1} - \rho^{-1})\,dx$ (the second piece vanishes by volume equality)
   $= (n-1)\int_{EΔB_\rho}\sigma(x)\cdot\frac{\rho - |x-z_\rho|}{\rho|x-z_\rho|}\,dx$,

   where $\sigma(x) = 1$ on $B_\rho\setminus E$ and $-1$ on $E\setminus B_\rho$, so the integrand $\sigma(x)(\rho - |x-z_\rho|)$ is always non-negative. By the trivial CL bound $|x - z_\rho|\in [\rho_*/2, 2R]$,

   $\Pi \ge (n-1)/(2R\cdot\rho_*)\cdot\int_{EΔB_\rho}|\rho - |x-z_\rho||\,dx = c(n,R,\rho_*)M_1(E_\rho, z_\rho)$.

   By the slice-rearrangement inequality $|EΔB_\rho|^2 \le C(n,R,\rho_*)M_1(E_\rho, z_\rho)$ (an immediate consequence of the 1D mismatch inequality of Agent A (4.11) applied slicewise, where the slicewise mass is $|r_{θ,1} - \rho|$ and the integral of slicewise mass squared bounds the angular integral of mass squared), we conclude $|EΔB_\rho|^2 \le C\Pi$. ✓

3. **The closure chain is genuinely integrated, conditional on the upstream
   conversion.** The whole
   architecture relies on the fact that the downstream use of (R) is
   only through the integrated action. Section~5 verifies this: no
   pointwise per-$\rho$ invocation of (R) survives after the
   slicing-then-squaring repair. The endpoint extraction of
   $\widehat\rho$ in Agent~4 is a distance estimate, not a pointwise
   radial-trace estimate.

4. **The $x$-variable good/bad bookkeeping could be streamlined.**
   The present proof keeps the dichotomy of §3.3--§3.5 because it is
   explicit. A cleaner rewrite may be possible by integrating the
   Talenti profile gap directly over the full interval
   $[\rho_*,\rho_\delta]$, but this is expository simplification, not a
   missing argument.

5. **May~14 correction.** The pointwise Talenti profile gap controls the
   rearranged level radius, not the physical radius $|x-z_\rho|$ relative
   to a moving centre.  Consequently (G2) is not proved by the argument in
   §3.  Separately, the W2 Agent B uniform Lipschitz bound (A0) is not a
   valid bad-$(-t')$ substitute for rough bounded sets.  These two issues
   prevent (G3)--(G5) from being used as an unconditional proof.

## 9. References

- **W2 A** = `wave2-A-radial-l2-trace.md`. Identities (5.3), (5.6); decomposition (4.12); CL Lemma 2.1; Plan 2 compatibility Lemma 2.2.
- **W2 B** = `wave2-B-kinetic-bound.md`. (A0) uniform Lipschitz Lemma 2.1; bad-set Lemma 4.1; (5.1) (H1)-action; Theorem 5.1 (K).
- **W2 C** = `wave2-C-cleanup.md`. §C1 center reconciliation.
- **W2 D** = `wave2-D-audit.md`. Verdict that Plan 2 reduces to (B²); chain dependency map.
- **W2 E** = `wave2-E-bypass-search.md`. §3 Route δ; §4 Wave 3 problem; route assessment.
- **W3 F** = `wave3-F-h1-center-bound.md`. H¹-in-ρ Fraenkel center bound (input to this note).
- **A1** = `agent1-finite-perimeter-identity.md`. Exact deficit identity Theorem §0.
- **A3** = `agent3-metric-first-variation.md`. (T) first variation §2; (7.1) §7.
- **A4** = `agent4-weighted-metric-trace.md`. Weighted metric trace theorem §2.
- **A5** = `agent5-final-assembly.md`. Theorem A bounded SV §1; Theorems B, C, D §1.3; constants §3.
- **gmt-inputs** = `gmt-inputs-for-metric-closure.md`. (1.1), (1.2), (2.1), (2.4), (3.1), (3.2), (4.1), (5.1).
- **mfp-closure** = `metric-finite-perimeter-closure.md`. (3.1)–(3.4); (4.1)–(4.2); (5.1)–(5.3); (6.1).
- **fvht** = `fvht-center-gluing-import.md`. §3–§4 block-center gluing; §6 metric outer foliation entry lemma.
- **lsd** = `level-set-deficit-identity.md`. §4 profile gap; Lemma 8.1 b(s) − v(s) ≤ 2δ/s; Lemma 8.3 transfer back.
- **nt** = `nicola-tilli-stability-import.md`. §2 profile deficit controls level heights.

External references: Cicalese–Leonardi 2012 ARMA; Figalli–Maggi–Pratelli 2010 Invent. Math.; Fusco–Julin 2014 Calc. Var. PDE; Maggi 2012 Cambridge; Talenti 1976 Ann. Mat. Pura Appl.; Ambrosio–Gigli–Savaré 2008.

Final references in the bibliographic stack: `Final/BoundedReduction.tex`, `Final/KohlerJobinTransfer.tex` (per Agent 5 §1.3, §3).

## 10. Summary table

| Step | Statement | Status / source |
|---|---|---|
| (G1) | Space-time divergence Π identity | proved §2; uses Fubini + CL containment |
| (G2) | Profile-gap + center drift conversion | **open**; Talenti radius is rearranged, not physical |
| (G3) | (B²-int) | conditional on (G2) |
| (G4) | Compatibility with metric closure chain | conditional; §5.2 repair is useful but upstream-dependent |
| (G5) | $\mathcal A^2 \le C\delta$ + (FK) | **not proved by this route** |

**Bottom line.** This file no longer closes Route~$\delta$
unconditionally.  The repaired §5 supplies a useful integrated
replacement for one broken radial-trace step, but the route still needs
a genuine physical-crossing estimate or a different proof of the
bad-$(-t')$ kinetic control before it can imply sharp Saint--Venant and
sharp Faber--Krahn.
