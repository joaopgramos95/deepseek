# Quantifying the Selection-Principle Step in Sharp Faber–Krahn Stability

## 0. Goal

We want to investigate whether the contradiction/selection-principle mechanism in the proof of sharp quantitative Faber–Krahn stability can be made explicit or partially quantitative.

The classical target inequality is

\[
|\Omega|^{2/N}\lambda_1(\Omega)-|B|^{2/N}\lambda_1(B)
\ge c_N \mathcal A(\Omega)^2,
\]

where \(B\) is a ball with \(|B|=|\Omega|\), and

\[
\mathcal A(\Omega)
=
\inf_{|B|=|\Omega|}
\frac{|\Omega\Delta B|}{|\Omega|}.
\]

Brasco–De Philippis–Velichkov prove this sharp form. Their proof proceeds by reducing the problem to a sharp quantitative form of the Saint-Venant inequality for torsional rigidity, and then proving that inequality by a free-boundary/selection-principle argument.

The idea here is to revisit the selection-principle part and ask:

> Can the qualitative passage from an arbitrary near-counterexample to a smooth near-ball counterexample be made quantitative?

Equivalently:

> Given a set \(\Omega\) with small deficit and nontrivial asymmetry, can one produce a smoother competitor \(\widetilde\Omega\), eventually close to a ball, such that the relevant normalized deficit-to-asymmetry ratio is controlled in a precise way?

---

## 1. Normalize the problem

Work at fixed volume, say

\[
|\Omega|=|B|=1.
\]

Define the Faber–Krahn deficit

\[
\delta_\lambda(\Omega)
:=
\lambda_1(\Omega)-\lambda_1(B),
\]

and the Fraenkel asymmetry

\[
\mathcal A(\Omega)
:=
\inf_{|B|=1}
|\Omega\Delta B|.
\]

The desired estimate is

\[
\delta_\lambda(\Omega)\ge c_N\mathcal A(\Omega)^2.
\]

However, following Brasco–De Philippis–Velichkov, it is probably better to work first with torsion.

Let

\[
E(\Omega)
=
\min_{u\in H^1_0(\Omega)}
\left\{
\frac12\int_\Omega |\nabla u|^2-\int_\Omega u
\right\}.
\]

This is negative and is essentially minus one half of the torsional rigidity:

\[
E(\Omega)=-\frac12 T(\Omega).
\]

The sharp Saint-Venant stability form is

\[
E(\Omega)-E(B)\ge c_N\mathcal A(\Omega)^2
\]

after the correct normalization/sign convention. More invariantly, one uses the scale-invariant expression

\[
E(\Omega)|\Omega|^{-(N+2)/N}
-
E(B)|B|^{-(N+2)/N}
\ge c_N\mathcal A(\Omega)^2.
\]

Brasco–De Philippis–Velichkov show that a sharp quantitative estimate for \(E\) transfers to the sharp Faber–Krahn inequality through the Kohler–Jobin inequality. :contentReference[oaicite:1]{index=1}

So the real project should be formulated for the torsional energy first.

---

## 2. Define the badness ratio

The natural object is not just the deficit or the asymmetry separately, but the ratio

\[
Q(\Omega)
:=
\frac{\delta_E(\Omega)}{\mathcal A(\Omega)^2},
\]

where

\[
\delta_E(\Omega)
:=
E(\Omega)-E(B)
\]

with the correct normalized convention.

The sharp stability inequality is equivalent to

\[
\inf_\Omega Q(\Omega)>0.
\]

The contradiction proof assumes that this fails, so there exists a sequence \(\Omega_j\) such that

\[
Q(\Omega_j)\to 0.
\]

One then replaces \(\Omega_j\) by better objects through a penalized minimization problem. These selected sets are regular, satisfy an Euler–Lagrange/free-boundary condition, and eventually converge to a ball. The final contradiction comes from proving the desired inequality directly for small smooth perturbations of the ball.

The quantitative version should try to turn this into a map:

\[
\Omega \mapsto \widetilde\Omega
\]

such that

\[
Q(\widetilde\Omega)\lesssim Q(\Omega),
\]

while \(\widetilde\Omega\) is smoother and/or closer to a ball in a stronger topology.

This is the right version of the “asymmetry larger than before” idea.

---

## 3. Sanity correction: what should be preserved or improved?

The earlier informal version said:

> produce a smoother set whose asymmetry is larger than the original one.

That is not quite the right invariant.

What we really want is not merely

\[
\mathcal A(\widetilde\Omega)\ge \mathcal A(\Omega).
\]

That alone is not helpful, because the deficit may also increase.

The useful property is something like

\[
\frac{\delta_E(\widetilde\Omega)}
{\mathcal A(\widetilde\Omega)^2}
\le
C
\frac{\delta_E(\Omega)}
{\mathcal A(\Omega)^2}
+
\text{controlled error}.
\]

A slightly weaker but still useful form would be:

\[
\delta_E(\widetilde\Omega)
\le
C\delta_E(\Omega),
\]

and

\[
\mathcal A(\widetilde\Omega)
\ge
c\mathcal A(\Omega).
\]

Together these imply

\[
Q(\widetilde\Omega)\le \frac{C}{c^2}Q(\Omega).
\]

Thus the selected set remains a near-counterexample if the original one was a near-counterexample.

This is the quantitative selection principle one would need.

---

## 4. Penalized selection problem

Given an initial set \(\Omega\), introduce a penalized functional of the schematic form

\[
\mathcal F_{\Omega,\varepsilon,\eta}(U)
=
E(U)
+
\Lambda ||U|-1|
+
\varepsilon \, d(U,\Omega)^2
+
\eta \, \Phi(\mathcal A(U),\mathcal A(\Omega)).
\]

Possible choices:

- \(d(U,\Omega)=|U\Delta\Omega|\),
- \(\Phi\) penalizes losing too much asymmetry,
- \(\Lambda\) enforces volume,
- \(\varepsilon\) keeps the selected set near \(\Omega\).

A more faithful selection-principle functional would force the minimizer \(U\) to satisfy two competing requirements:

1. \(U\) has energy deficit no worse than \(\Omega\), up to a controlled error.
2. \(U\) does not collapse its asymmetry.

So one might impose something like

\[
\mathcal A(U)\ge c\mathcal A(\Omega)
\]

directly, or penalize violation of this lower bound.

The desired output is a minimizer \(\widetilde\Omega\) such that:

\[
\delta_E(\widetilde\Omega)
\le
C\delta_E(\Omega),
\]

\[
\mathcal A(\widetilde\Omega)
\ge
c\mathcal A(\Omega),
\]

and \(\widetilde\Omega\) enjoys regularity from the free-boundary theory attached to the torsion functional.

---

## 5. Regularity and compactness output

The main technical step is to show that the selected minimizer \(\widetilde\Omega\) is regular enough.

Expected output:

- \(\widetilde\Omega=\{u>0\}\) for a minimizer \(u\) of a one-phase-type variational problem.
- \(u\) satisfies nondegeneracy estimates.
- The free boundary \(\partial\widetilde\Omega\) is regular, perhaps up to a singular set.
- If the original deficit is sufficiently small, then \(\widetilde\Omega\) is close to a ball in measure.
- Then the free-boundary regularity improves this to a graphical representation:

\[
\partial\widetilde\Omega
=
\{(1+\varphi(\theta))\theta:\theta\in \mathbb S^{N-1}\},
\]

with \(\varphi\) small in a strong norm, after translating the ball appropriately.

This is the stage where the contradiction proof usually says: after selecting a sequence, regularity and compactness imply convergence to the ball, hence the sets are eventually smooth perturbations of the ball.

The quantitative project asks whether one can estimate something like

\[
\|\varphi\|_{C^{1,\alpha}}
\le
\Psi(\delta_E(\Omega),\mathcal A(\Omega),Q(\Omega)),
\]

or at least produce an explicit threshold:

\[
Q(\Omega)\ll 1
\quad\Longrightarrow\quad
\widetilde\Omega
\text{ is a small } C^{1,\alpha}\text{ perturbation of }B.
\]

---

## 6. Stability near the ball

For nearly spherical sets,

\[
\partial\Omega
=
\{(1+\varphi(\theta))\theta:\theta\in\mathbb S^{N-1}\},
\]

with volume and barycenter constraints, one expects a second-variation estimate of the form

\[
\delta_E(\Omega)
\ge
c_N\|\varphi\|_{H^{1/2}(\mathbb S^{N-1})}^2
\]

or an analogous norm depending on the functional.

Also,

\[
\mathcal A(\Omega)
\lesssim
\|\varphi\|_{L^2(\mathbb S^{N-1})}
\lesssim
\|\varphi\|_{H^{1/2}(\mathbb S^{N-1})}.
\]

Therefore,

\[
\delta_E(\Omega)\ge c_N\mathcal A(\Omega)^2.
\]

This is the local stability estimate.

The contradiction proof uses this after showing that selected bad sets must eventually be nearly spherical. The quantitative project asks whether we can reach this local regime with explicit, controlled losses.

---

## 7. Proposed theorem to aim for

A possible intermediate theorem:

**Quantitative Selection Principle.**
There exist dimensional constants \(c,C,\varepsilon_0>0\) such that for every set \(\Omega\subset\mathbb R^N\) with \(|\Omega|=|B|\), \(\delta_E(\Omega)\le\varepsilon_0\), and \(\mathcal A(\Omega)>0\), one can construct a set \(\widetilde\Omega\) satisfying:

1. \(|\widetilde\Omega|=|B|\),
2. \(\delta_E(\widetilde\Omega)\le C\delta_E(\Omega)\),
3. \(\mathcal A(\widetilde\Omega)\ge c\mathcal A(\Omega)\),
4. \(\widetilde\Omega\) is an almost-minimizer for the torsion free-boundary problem,
5. if \(Q(\Omega)\) is sufficiently small, then \(\widetilde\Omega\) is a small normal graph over \(B\).

Then local stability for \(\widetilde\Omega\) gives

\[
\delta_E(\widetilde\Omega)
\ge c_N\mathcal A(\widetilde\Omega)^2.
\]

Using points 2 and 3,

\[
C\delta_E(\Omega)
\ge
\delta_E(\widetilde\Omega)
\ge
c_N c^2\mathcal A(\Omega)^2.
\]

Thus

\[
\delta_E(\Omega)\ge c'_N\mathcal A(\Omega)^2.
\]

This proves sharp Saint-Venant stability quantitatively, and the known Kohler–Jobin transfer gives sharp Faber–Krahn stability.

---

## 8. Main mathematical obstacles

### Obstacle 1: asymmetry is nonlocal and nonsmooth

The Fraenkel asymmetry involves an infimum over balls:

\[
\mathcal A(\Omega)=\inf_B |\Omega\Delta B|.
\]

This is not smooth under domain variations, especially if the optimal ball is not unique.

Possible workaround:
fix a center by imposing barycenter zero, or work with a smoothed/asymmetric proxy that is equivalent to Fraenkel asymmetry near the ball.

### Obstacle 2: preserving asymmetry during selection

The selected minimizer might reduce the asymmetry too much. If

\[
\mathcal A(\widetilde\Omega)\ll\mathcal A(\Omega),
\]

then even if the selected set has small deficit, it may no longer encode the original counterexample.

So one needs either:

\[
\mathcal A(\widetilde\Omega)\ge c\mathcal A(\Omega),
\]

or a way to compensate for lost asymmetry.

### Obstacle 3: quantitative free-boundary regularity

The contradiction proof can use compactness:

\[
\widetilde\Omega_j\to B
\quad\Longrightarrow\quad
\partial\widetilde\Omega_j
\text{ is eventually smooth and graphical}.
\]

A quantitative version needs rates or at least explicit dependencies.

This may be the hardest point.

### Obstacle 4: singular sets in high dimension

In high dimensions, free-boundary singularities may appear. The selection principle must either avoid them in the near-ball regime or show that small deficit rules them out.

### Obstacle 5: constants may be terrible

Even if everything is quantitative in principle, the constants may be non-explicit or unusable because they pass through compactness, epiperimetric inequalities, or regularity thresholds.

A realistic first goal is not an optimal constant, but an explicit logical dependence.

---

## 9. Better first target

Instead of trying to make the whole proof fully quantitative immediately, target the following:

### Project A: Quantitative non-collapse of asymmetry under selection

Prove that the penalized minimizer \(\widetilde\Omega\) satisfies

\[
\mathcal A(\widetilde\Omega)\ge c\mathcal A(\Omega)
\]

and

\[
\delta_E(\widetilde\Omega)\le C\delta_E(\Omega).
\]

This isolates the part of the argument that your idea directly attacks.

### Project B: Quantitative entry into the nearly spherical regime

Prove that if

\[
Q(\Omega)=\frac{\delta_E(\Omega)}{\mathcal A(\Omega)^2}
\]

is sufficiently small, then the selected set \(\widetilde\Omega\) is a small \(C^{1,\alpha}\) perturbation of a ball.

### Project C: Local-to-global with explicit losses

Combine:

1. selection,
2. quantitative regularity,
3. local second variation,

to recover

\[
\delta_E(\Omega)\ge c_N\mathcal A(\Omega)^2.
\]

---

## 10. Sanity check: what would count as success?

The strategy is sound if one can prove a lemma of the following form:

**Selection Lemma.**
For every sufficiently bad set \(\Omega\), there exists a smoother set \(\widetilde\Omega\) such that

\[
Q(\widetilde\Omega)\le C Q(\Omega),
\]

and \(\widetilde\Omega\) belongs to a class where regularity theory applies.

Then the argument is:

1. Assume there are arbitrarily bad sets with \(Q(\Omega_j)\to0\).
2. Select smoother \(\widetilde\Omega_j\) with \(Q(\widetilde\Omega_j)\to0\).
3. Show \(\widetilde\Omega_j\) enters the nearly spherical regime.
4. Apply local stability:

\[
Q(\widetilde\Omega_j)\ge c_N>0.
\]

5. Contradiction.

The quantitative upgrade is to avoid merely saying “eventually”; instead prove an explicit implication:

\[
Q(\Omega)\le q_0
\quad\Longrightarrow\quad
\widetilde\Omega
\text{ is nearly spherical}.
\]

Then local stability gives the desired bound.

---

## 11. Summary of the refined idea

The good formulation is:

> Quantify the selection principle behind Brasco–De Philippis–Velichkov by constructing, from a near-counterexample \(\Omega\), a regularized near-counterexample \(\widetilde\Omega\) for which the quotient deficit/asymmetry\(^2\) is controlled. Then use quantitative free-boundary regularity to enter the perturbative regime, where second variation around the ball yields the sharp stability inequality.

The crucial object is not the asymmetry alone, but the quotient

\[
Q(\Omega)=\frac{\delta_E(\Omega)}{\mathcal A(\Omega)^2}.
\]

The key technical lemma should preserve smallness of \(Q\), not merely increase asymmetry.

---

## 12. Route status after sorting

The current Plan 1 route should now be read with the following refinements.

### What changed

The selection step is no longer formulated directly with the Fraenkel ratio
\(\delta_E/\mathcal A^2\). In the BDV proof the workable object is the smooth
barycentric asymmetry

\[
\alpha(\Omega)
=
\int_{\Omega\Delta B_1(x_\Omega)}
\bigl|1-|x-x_\Omega|\bigr|\,dx,
\]

and the single-set ratio

\[
Q_\alpha(\Omega)
:=
\frac{E(\Omega)-E(B_1)}{\alpha(\Omega)}.
\]

The note `quantitative-selection-principle.md` now records a sharpened
single-set selection map. If

\[
\varepsilon=\alpha(\Omega_0),\qquad
q=Q_\alpha(\Omega_0),\qquad
\tau=q^{1/4},
\]

with \(q\le q_{\rm sel}(N,R)\) and
\(\varepsilon\le\varepsilon_{\rm sel}(N,R)\), the selected and
volume-normalized set \(\widetilde\Omega\) satisfies

\[
\alpha(\widetilde\Omega)
\ge
(1-Cq^{1/4})\alpha(\Omega_0),
\qquad
E(\widetilde\Omega)-E(B_1)
\le
C(E(\Omega_0)-E(B_1)).
\]

Hence \(Q_\alpha(\widetilde\Omega)\le C Q_\alpha(\Omega_0)\). More generally
the loss is controlled by

\[
\rho(q,\tau)=\frac{\sqrt{2q+q^2}}{\tau}+Cq,
\]

so the quotient is preserved whenever \(\rho(q,\tau)<1\). This is the precise
replacement for the sequential estimate in BDV Proposition 4.4(iv).

### What remains unchanged

The global proof architecture remains BDV's:

1. prove the sharp Saint-Venant estimate for torsion,
2. transfer it to Faber-Krahn through Kohler-Jobin,
3. use the BDV nearly spherical second variation once the selected set is a
   smooth small graph over the ball.

The local perturbative theorem around the ball is not being changed. The
selection functional is also BDV's functional (4.10), with the sequence
parameter \(\sigma\) replaced by the single-set parameter \(\tau\).

### What is now isolated as open

The remaining compactness step has been split into three lemmas:

1. \(\alpha\)-to-Hausdorff: density estimates plus BDV Lemma 4.2 give
   \(d_H(\partial U,\partial B_1(x_U))\le C\alpha(U)^{1/(2N)}\).
2. Hausdorff-to-flatness: if this Hausdorff distance is below a fixed
   \(h_F(N,R,\mu,\rho_\mu)\), then the selected minimizer is of
   Alt-Caffarelli class \(F(C\mu,1,+\infty)\) on a fixed scale.
3. Flatness-to-global graph: local Alt-Caffarelli graphs patch by radial
   projection to a global \(C^{1,\gamma}\) normal graph over \(\partial B_1\).

The first lemma is essentially quantitative already. The most important
remaining theorem is the second one, because it converts the measurable
selection output into the exact flatness hypothesis of BDV Theorem 4.18 with
explicit dependencies.
