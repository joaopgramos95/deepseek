# Figalli--van Hintum--Tiba center gluing for Plan 2

This note imports the center-control mechanism from
`2501.04656v1.pdf`:

Alessio Figalli, Peter van Hintum, and Marius Tiba,
*Sharp Quantitative Stability for the Prekopa-Leindler and
Borell-Brascamp-Lieb Inequalities*, arXiv:2501.04656v1.

The goal is to use their idea to attack the outer foliation entry lemma in
`global-foliation-trace.md`.

## 1. What the paper does with centers

The relevant part is Section 6.3, "Gluing together level sets". Proposition
6.3 gives, for each truncation \(f_i=\min\{f,2^{-i}\}\), a translation \(v_i\)
such that the relevant level sets of \(f\) and \(g\) are close after translating
by \(v_i\). These translations are not a priori the same.

The key step is:

1. consecutive truncation windows overlap on a substantial interval of levels;
2. on the overlap, both \(v_i\) and \(v_{i+1}\) align essentially the same level
   sets;
3. therefore translating a nearly convex set by \(v_i-v_{i+1}\) changes it only
   little;
4. a convex core cannot be moved by a large vector without creating a large
   symmetric difference;
5. hence \(v_i-v_{i+1}\) is small in the gauge of the overlapping convex core;
6. nestedness of the level sets lets one sum these increments without losing
   the sharp exponent.

Two auxiliary ideas are important.

First, Lemma 4.9 says that once the level sets are nearly convex, small
translations are harmless in the integrated \(L^1\) distance. In other words,
after one has proved that a translation vector is small relative to a convex
core, one may remove it at acceptable cost.

Second, in the higher-dimensional reduction, Section 7.4 uses a positive-mass
core to pin local translations. A non-small translation of a cone cuts a
definite amount of a ball on which the functions are bounded below, so the
translation must be small. This is an anchoring argument: a large common core
forbids drift.

## 2. Translation to torsion level sets

For Plan 2 the analogue is the outer family
\[
E_\rho=\{u>t(\rho)\},
\qquad |E_\rho|=\omega_n\rho^n,
\qquad \rho\in[\rho_*,1].
\]
The exact level-set identity controls the integrated action
\[
\int_{\rho_*}^1 (D_I(t(\rho))+D_H(t(\rho)))\,w(\rho)\,d\rho
\lesssim \delta_T(\Omega),
\]
with a dimensional weight \(w(\rho)\simeq 1\) on the fixed annulus.

The problem is that quantitative isoperimetry gives centers level by level:
\[
E_\rho \approx z(\rho)+B_\rho,
\]
but those centers may not be coherent. The FvHT mechanism suggests not trying
to identify a canonical center first. Instead:

1. choose overlapping blocks \(I_j\subset[\rho_*,1]\);
2. in each block choose a best center \(z_j\) minimizing
   \[
   \Phi_j(z)
   :=
   \int_{I_j}|E_\rho\Delta(z+B_\rho)|\,d\rho;
   \]
3. use overlap to show \(z_j-z_{j+1}\) is small;
4. glue the block centers into one coherent center field, or into a single
   global center if the fixed-center version is desired.

This is exactly the same architecture as the truncation translations \(v_i\)
in FvHT Section 6.3.

## 3. Basic overlap lemma for balls

Let \(J\subset[\rho_*,1]\) be an interval of positive length, and let \(a,b\in
\mathbb R^n\). If \(|a-b|\le c\rho_*\), then
\[
\int_J |(a+B_\rho)\Delta(b+B_\rho)|\,d\rho
\ge
c_{n,\rho_*}|J|\,|a-b|.
\]
Indeed, for each \(\rho\in[\rho_*,1]\),
\[
|(a+B_\rho)\Delta(b+B_\rho)|
\ge c_n\rho^{n-1}|a-b|
\]
as long as \(|a-b|\le c\rho\), and \(\rho\ge\rho_*\).

Consequently, if
\[
\int_J
\bigl(
|E_\rho\Delta(a+B_\rho)|
+
|E_\rho\Delta(b+B_\rho)|
\bigr)\,d\rho
\le \varepsilon,
\]
then
\[
|a-b|\le C_{n,\rho_*,|J|}\varepsilon.
\]

This is the torsion analogue of the FvHT overlap step: two centers that both
work on the same level window must be close.

## 4. Block-center gluing lemma

Fix a finite overlapping cover
\[
[\rho_*,1]=\bigcup_{j=0}^N I_j
\]
with
\[
|I_j|\ge c_0,\qquad |I_j\cap I_{j+1}|\ge c_0,
\]
where \(c_0>0\) depends only on \(\rho_*\). Let \(z_j\) minimize
\[
\Phi_j(z)=\int_{I_j}|E_\rho\Delta(z+B_\rho)|\,d\rho.
\]
Assume that, for each \(j\),
\[
\Phi_j(z_j)\le \varepsilon_j.
\]
Then
\[
|z_j-z_{j+1}|
\le
C_{n,\rho_*}(\varepsilon_j+\varepsilon_{j+1}).
\]
Hence, after fixing \(z_0\),
\[
|z_j-z_0|
\le
C_{n,\rho_*}\sum_{k<j}(\varepsilon_k+\varepsilon_{k+1}).
\]

Since the cover is finite on the fixed annulus, this introduces no boundary
layer parameter and no \(\eta\)-loss. This is the first usable replacement for
the center part of the selection principle.

## 5. Sharpness issue: use squared action, not only \(L^1\) closeness

The preceding lemma controls centers in terms of integrated \(L^1\) closeness.
Levelwise quantitative isoperimetry gives
\[
|E_\rho\Delta(z(\rho)+B_\rho)|
\lesssim D_I(t(\rho))^{1/2}.
\]
If one uses only this, Cauchy--Schwarz gives an \(O(\delta_T^{1/2})\) center
error. That is acceptable for locating centers but not by itself a sharp
quadratic stability proof.

The sharp Plan 2 route must therefore combine FvHT center gluing with the
radial kinetic term \(D_H\). The right object is not merely the distance of
each level to the manifold of balls, but the Sobolev-in-\(\rho\) distance of the
whole curve \(\rho\mapsto E_\rho\) to that manifold.

The expected metric estimate is
\[
\operatorname{md}_{L^1}
\left(
\rho^{-1}(E_\rho-z(\rho))
\right)^2
\lesssim
D_H(t(\rho))+D_I(t(\rho)),
\]
for a coherently glued center field \(z(\rho)\), after projecting away
translations. If this is proved, then the Hilbert/metric trace theorem gives
the sharp endpoint bound:
\[
\mathcal A(\Omega)^2
\lesssim
\int_{\rho_*}^1
\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)w(\rho)\,d\rho
\lesssim
\delta_T(\Omega).
\]

So the FvHT import solves the center-coherence problem, but the sharp exponent
still comes from the \(D_H\)-controlled kinetic energy.

## 6. Proposed outer foliation entry lemma, FvHT version

The original entry lemma in `global-foliation-trace.md` asked directly for a
coherent graph
\[
\partial E_\rho=z(\rho)+(\rho+h(\rho,\theta))\theta.
\]
The FvHT-inspired version should be weaker and more robust:

**Metric outer foliation entry lemma.** Let \(\rho_*\in(0,1)\). If
\(\delta_T(\Omega)\) is sufficiently small, then there is a measurable center
field \(z:[\rho_*,1]\to\mathbb R^n\) such that the normalized sets
\[
F_\rho:=\rho^{-1}(E_\rho-z(\rho))
\]
satisfy
\[
\operatorname{dist}_{L^1}(F_\rho,B_1)^2
\lesssim D_I(t(\rho))
\quad\hbox{for a.e. }\rho,
\]
and
\[
\int_{\rho_*}^1
\left|\frac{d}{d\rho}F_\rho\right|_{L^1/\mathrm{translations}}^2\,d\rho
\lesssim
\int_{\rho_*}^1
\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)w(\rho)\,d\rho.
\]
Consequently,
\[
\operatorname{dist}_{L^1}(F_1,B_1)^2
\lesssim
\delta_T(\Omega).
\]

Here the derivative is meant in the metric-space sense for characteristic
functions, after quotienting out translations. In a smooth graph regime this
reduces exactly to the estimate in `global-foliation-trace.md`:
\[
\int_{\rho_*}^1
\left(
\rho^{n+1}\|\partial_\rho h_{\ge2}\|_2^2
+\rho^{n-1}Q(h)
\right)d\rho
\lesssim \delta_T(\Omega).
\]

## 7. Concrete proof tasks

The next hard tasks are now more precise.

1. **Overlap-center lemma for level families.** Prove the block-center gluing
   lemma above with \(E_\rho\) only measurable in \(\rho\). This is elementary
   and should be written first.

2. **Velocity-to-metric derivative lemma.** For a smooth foliation, prove that
   \[
   D_H(t(\rho))+D_I(t(\rho))
   \gtrsim
   \left|\frac{d}{d\rho}
   \rho^{-1}(E_\rho-z(\rho))
   \right|_{L^1/\mathrm{translations}}^2.
   \]
   The computation uses
   \[
   |\nabla u|=\frac{-t_\rho}{V},
   \]
   so \(D_H\) is the Cauchy deficit of the normal velocity \(V\).

3. **Weak approximation.** Extend the velocity lemma from smooth levels to
   finite-perimeter levels by coarea and approximation.

4. **Metric trace.** Apply the Sobolev trace theorem for curves in \(L^1\) or,
   in the near-spherical regime, pull back to the Hilbert graph variable
   \(h_{\ge2}\).

The FvHT lesson is that center drift should be handled by overlap and
anchoring, not by choosing a canonical center at the start. For Plan 2, this
means the selection principle is replaced by a global-in-level gluing theorem
plus the \(D_H\) kinetic estimate.
