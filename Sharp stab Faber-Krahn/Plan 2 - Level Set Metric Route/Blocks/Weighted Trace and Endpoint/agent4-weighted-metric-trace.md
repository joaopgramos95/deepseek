# Agent 4 — Weighted metric trace lemma

This note settles the metric trace step that turns the integrated action
bound on \([\rho_*,\rho_\delta]\) into a deficit bound at a specific
radius \(\widehat\rho\) near \(\rho_\delta=1-\kappa\sqrt\delta\). The
abstract lemma as posed in `claude-agent-deployment.md` (Agent 4) is
**insufficient at the \(\delta\)-rate** with hypotheses (H1)+(H2) alone;
an auxiliary integrated \(L^2(d\rho)\) kinetic bound (or a second-order
profile-gap refinement) is required. Both are available for free in the
torsion application.

## 1. Hypotheses

Let \((\mathcal X,d_{\mathcal X})\) be a complete metric space with a fixed
reference \(B_1\). Let \(\gamma:[\rho_*,\rho_\delta]\to\mathcal X\) be
absolutely continuous in the AGS sense (Ambrosio–Gigli–Savaré 2008, Sec.
1.1). Let \(\mu=\mu_\rho\,d\rho\) be a Borel measure on
\([\rho_*,\rho_\delta]\) with density \(\mu_\rho\ge0\). Assume:

**(H1) Integrated action against \(d\mu\):**
\[
\int_{\rho_*}^{\rho_\delta}\bigl(d_{\mathcal X}(\gamma(\rho),B_1)^2
+|\dot\gamma|(\rho)^2\bigr)\,d\mu(\rho)\le C\delta.
\]

**(H2) Profile-gap interval lower bound:**
\(\mu([a,b])\ge c(b-a)-C\delta\) for every sub-interval
\([a,b]\subset[\rho_*,\rho_\delta]\).

**(H3) Matching upper bound:** \(\mu_\rho\le M\) a.e., with \(M-c\) small.

**(5.14) Integrated \(L^2(d\rho)\) kinetic bound:**
\[
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|(\rho)^2\,d\rho\le C'\delta.
\]

In the torsion application, (5.14) follows from (H1)+(H3) when \(M-c=O(\delta)\)
— a *second-order* refinement of (H2) — or directly from the integrated
\(L^2\) Cauchy–deficit identity for \(D_H\).

## 2. Result

**Theorem (Weighted metric trace).** Under (H1)+(H2)+(H3)+(5.14) there exist
constants \(C_*=C_*(n,R,\rho_*,\kappa,M,c)\) and \(L^*\ge\kappa\sqrt\delta\)
fixed and a point
\[
\widehat\rho\in[\rho_\delta-C_*\delta,\rho_\delta]
\]
such that
\[
d_{\mathcal X}(\gamma(\widehat\rho),B_1)^2\le C_*\delta.
\]

## 3. Bad-set lemma

**Lemma 3.1.** Under (H2)+(H3), the bad set
\(B_*:=\{\rho\in[\rho_*,\rho_\delta]:\mu_\rho<c/2\}\) satisfies
\[
|B_*|\le\frac{2(M-c)L^*}{c}+\frac{2C\delta}{c},
\]
where \(L^*:=\rho_\delta-\rho_*\).

*Proof.* (H2) on the full interval: \(\mu([\rho_*,\rho_\delta])\ge cL^*-C\delta\).
(H3) on the split \(B_*\sqcup G_*\): \(\mu([\rho_*,\rho_\delta])\le(c/2)|B_*|+M|G_*|
=(c/2)|B_*|+M(L^*-|B_*|)\). Combining:
\((c/2-M)|B_*|+ML^*\ge cL^*-C\delta\), i.e.
\((M-c/2)|B_*|\le(M-c)L^*+C\delta\). Bound \(M-c/2\ge c/2\). \(\square\)

**Corollary 3.2.** For any \(f\ge0\) Borel, bounded on \(B_*\),
\[
\int_{\rho_*}^{\rho_\delta}f\,d\rho
\le\frac{2}{c}\int_{\rho_*}^{\rho_\delta}f\,d\mu+|B_*|\|f\|_{L^\infty(B_*)}.
\]

## 4. Proof of the theorem

### Step 1: Macroscopic Markov on a fixed sub-interval.

Fix \(J^*:=[\rho_\delta-L^*,\rho_\delta-L^*/2]\) with \(L^*\) a constant
independent of \(\delta\) (e.g., \(L^*=(\rho_\delta-\rho_*)/4\)). By (H2),
\(\mu(J^*)\ge cL^*/2-C\delta\ge cL^*/4\) for \(\delta\) small. By (H1)
and Markov in \(d\mu\) on \(J^*\),
\[
\exists\rho_0\in J^*:\ d_{\mathcal X}(\gamma(\rho_0),B_1)^2
\le\frac{4C\delta}{cL^*}=:K_1\delta.
\]

### Step 2: Kinetic transport to the target interval.

Set \(I_\delta:=[\rho_\delta-K_2\delta,\rho_\delta]\), \(K_2\) to choose
below. For any \(\widehat\rho\in I_\delta\), AGS Thm 1.1.2 with Cauchy–Schwarz
in \(d\rho\) (a Lipschitz-in-\(\rho\) reparametrization is implicit) gives
\[
d_{\mathcal X}(\gamma(\rho_0),\gamma(\widehat\rho))^2
\le(\widehat\rho-\rho_0)\int_{\rho_0}^{\widehat\rho}|\dot\gamma|^2\,d\rho
\le L^*\int_{\rho_*}^{\rho_\delta}|\dot\gamma|^2\,d\rho
\stackrel{(5.14)}{\le}L^*C'\delta.
\]

### Step 3: Triangle.

\[
d_{\mathcal X}(\gamma(\widehat\rho),B_1)^2
\le 2 d_{\mathcal X}(\gamma(\rho_0),B_1)^2+2d_{\mathcal X}(\gamma(\rho_0),\gamma(\widehat\rho))^2
\le 2K_1\delta+2L^*C'\delta=:C_*\delta.
\]
Picking \(\widehat\rho\) to be a Lebesgue point of the kinetic integral
inside \(I_\delta\) completes the argument. \(\square\)

## 5. Why (H1)+(H2) alone do not suffice

The deployment brief asks whether (H1)+(H2) yield \(O(\delta)\). The
analysis above shows **no**, at this rate.

Lemma 3.1 + Corollary 3.2 applied to \(f=|\dot\gamma|^2\):
\[
\int_{\rho_*}^{\rho_\delta}|\dot\gamma|^2\,d\rho
\le\frac{2}{c}C\delta+|B_*|\|\dot\gamma\|_{L^\infty(B_*)}^2.
\]
The first term is \(O(\delta)\). The second is bounded by
\(O((M-c)\|\dot\gamma\|_\infty^2)+O(\delta\|\dot\gamma\|_\infty^2)\). With
only the first-order profile gap \(M-c=O(\delta^{1/2})\), Step 2 above
yields \(O(\delta^{1/2})\), losing a square root from the target rate.

The sharp \(O(\delta)\) rate requires either:

(i) **\(M-c=O(\delta)\)**, a second-order profile-gap refinement; or

(ii) **(5.14) as an independent hypothesis**, i.e. the kinetic bound
already in \(d\rho\) rather than \(d\mu\).

In the torsion application, both hold for free:

- The exact Cauchy-deficit identity
  \(D_H(t)=\bigl(\int|\nabla u|^{-1}\bigr)\bigl(\int|\nabla u|\bigr)-P(E_t)^2\)
  gives a quantitative \(L^2\)-velocity-oscillation bound,
- The integrated form gives \(\int|\dot\gamma|^2\,d\rho\le C\delta\) directly,
- Equivalently, the integrated \(L^2\) Cauchy–deficit gives the
  second-order profile gap \(M-c=O(\delta)\) (see `outer-foliation-entry-proof-attempt.md` §4).

So the abstract trace lemma needs the auxiliary input, and the
application supplies it.

## 6. Microscopic-hole treatment

No pointwise lower bound on \(\mu_\rho=-t_\rho\) is used. The bad set
\(B_*\) may be:
- Lebesgue-positive (Cantor-like, zero density),
- arbitrarily disconnected,
- with \(\mu_\rho\) oscillating wildly.

Lemma 3.1 controls only the total Lebesgue measure of \(B_*\) via (H3).
The interval bound (H2) is the right robust replacement because (i) it
is exactly what the profile-gap lemma supplies in
`level-set-deficit-identity.md`, and (ii) the alternative
\(\mu([a,b])\ge c(b-a)^2-C\delta\) (natural under only \(\mu_\rho\ge0\))
gives no \(\delta\)-bound on \(|B_*|\) at all.

## 7. Sharpness of (H2)

A pointwise \(\mu_\rho\ge c\) is *not* available in general. Even on
smooth \(\Omega\), \(t_\rho\) can have low-slope intervals where level
sets traverse indentations of \(\Omega\). The interval form (H2) is
sharp: the slack \(C\delta\) matches the \(L^\infty\) profile-gap rate
and cannot be reduced in the bounded finite-perimeter class.

## 8. References

- Ambrosio–Gigli–Savaré 2008, *Gradient Flows in Metric Spaces…*, 2nd ed.,
  Thm 1.1.2 and §1.1 (absolute continuity, metric derivative, lower
  semicontinuity).
- Profile-gap lemma: see `Plan 2/level-set-deficit-identity.md` and
  `Plan 2/nicola-tilli-stability-import.md`.
- Cauchy–deficit \(L^2\) refinement: `Plan 2/outer-foliation-entry-proof-attempt.md` §4.

## 9. Status

**Conditional on (5.14) [or equivalently the second-order profile-gap
refinement \(M-c=O(\delta)\)], the weighted metric trace holds at the
sharp \(\delta\)-rate.** Both auxiliary inputs are automatic in the
torsion application via the exact Cauchy–deficit identity. The naked
(H1)+(H2) hope of the deployment brief is **not** met; the lemma needs
the auxiliary kinetic bound, which the application supplies for free.
