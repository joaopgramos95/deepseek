# Metric finite-perimeter closure, no graph gauge

This note rewrites the outer-foliation argument without assuming that level
sets are graphs. The objects are finite-perimeter sets, their reduced
boundaries, and a metric curve in \(L^1\) modulo translations.

The conclusion is a sharp Plan 2 theorem under two standard non-graph inputs:

1. a strong quantitative isoperimetric estimate controlling the homothetic
   velocity defect of an almost minimizer;
2. the standard first-variation formula for \(L^1\)-curves of finite-perimeter
   sets.

These are not Plan 1-style graph-entry hypotheses. They are levelwise
geometric-measure estimates.

We keep the volume normalization
\[
|\Omega|=\omega_n,\qquad B=B_1,\qquad
\delta=\delta_T(\Omega)=E(\Omega)-E(B).
\]
Let
\[
E_\rho=\{u>t(\rho)\},\qquad |E_\rho|=\omega_n\rho^n,
\qquad \rho\in[\rho_*,1],
\]
where \(0<\rho_*<1\) is fixed.

## 1. The metric target

Let \({\mathcal X}\) be the metric quotient of finite-measure sets by
translations, with distance
\[
d_{\mathcal X}([A],[C])
:=
\inf_{a\in\mathbb R^n}|A\Delta(C+a)|.
\]
Normalize the level sets by
\[
F_\rho:=\rho^{-1}E_\rho,
\]
understood as an element of \({\mathcal X}\). Then
\[
d_{\mathcal X}(F_\rho,B_1)
=
\rho^{-n}\inf_z |E_\rho\Delta(z+B_\rho)|.
\]
The desired finite-perimeter entry theorem is
\[
d_{\mathcal X}(F_{\widehat\rho},B_1)^2\le C\delta
\]
for some
\[
\widehat\rho\in[1-\kappa\sqrt\delta-C\delta,\ 1-\kappa\sqrt\delta].
\]
The transfer back to \(\Omega\) costs only \(O(\sqrt\delta)\) in asymmetry, so
this gives
\[
\mathcal A(\Omega)^2\le C\delta.
\]

Thus the boundary graph \(h(1,\theta)\) is replaced by the metric trace of the
curve \(\rho\mapsto [F_\rho]\).

## 2. Normal speed for torsion levels

For a.e. regular level, the coarea structure gives a reduced boundary
\(\partial^*E_\rho\), outer normal \(\nu_\rho\), and normal speed
\[
V_\rho=\frac{-t_\rho(\rho)}{|\nabla u|}
\quad\hbox{on }\partial^*E_\rho.
\]
It satisfies
\[
\int_{\partial^*E_\rho}V_\rho\,d\mathcal H^{n-1}
=
\frac{d}{d\rho}|E_\rho|
=
n\omega_n\rho^{n-1}
=:A_\rho.
\tag{2.1}
\]
The Holder loss has the exact velocity form
\[
D_H(t(\rho))
=
\left(\int_{\partial^*E_\rho}V_\rho\right)
\left(\int_{\partial^*E_\rho}V_\rho^{-1}\right)
-P(E_\rho)^2.
\tag{2.2}
\]
Therefore
\[
\int_{\partial^*E_\rho}
\frac{(V_\rho-\bar V_\rho)^2}{V_\rho}\,d\mathcal H^{n-1}
=
\frac{A_\rho}{P(E_\rho)^2}D_H(t(\rho)),
\qquad
\bar V_\rho:=\frac{A_\rho}{P(E_\rho)}.
\tag{2.3}
\]
By Cauchy--Schwarz,
\[
\left(
\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*}D_H(t(\rho)).
\tag{2.4}
\]
This estimate is purely finite-perimeter and uses no graph representation.

## 3. Homothetic velocity defect from strong isoperimetry

For a ball \(z+B_\rho\), the homothetic velocity with respect to \(\rho\) is
\[
H_{z,\rho}(x):=\frac{(x-z)\cdot\nu_\rho(x)}{\rho}.
\]
For any finite-perimeter \(E_\rho\) with \(|E_\rho|=\omega_n\rho^n\),
the divergence theorem gives
\[
\int_{\partial^*E_\rho}H_{z,\rho}\,d\mathcal H^{n-1}
=
\frac{n|E_\rho|}{\rho}
=A_\rho.
\tag{3.1}
\]
Thus \(H_{z,\rho}\) and \(V_\rho\) have the same total flux.

The needed strong isoperimetric input is:

**Homothetic velocity defect lemma.** Suppose \(E\subset B_R\) has
\(|E|=|B_\rho|\), with \(\rho\in[\rho_*,1]\). Then there is a center \(z_E\)
such that
\[
\left(
\int_{\partial^*E}
\left|H_{z_E,\rho}-\frac{P(B_\rho)}{P(E)}\right|
\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}
\left(P(E)^2-P(B_\rho)^2\right).
\tag{3.2}
\]

This is the non-graph substitute for the Fuglede expansion. It should follow
from the strong FMP/Fusco--Julin oscillation-index form of the quantitative
isoperimetric inequality. Indeed that theory gives, for a suitable center
\(z_E\),
\[
\inf_z |E\Delta(z+B_\rho)|^2
+
\left(
\int_{\partial^*E}
\left|
\nu_E-\frac{x-z_E}{|x-z_E|}
\right|
d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}\bigl(P(E)-P(B_\rho)\bigr).
\tag{3.3}
\]
On bounded sets, (3.3) controls the \(L^1\) defect between the actual
homothetic normal speed \(H_{z_E,\rho}\) and the constant ball speed
\(P(B_\rho)/P(E)\). No parametrization of \(\partial E\) is involved.

For the torsion level \(E_\rho\), (3.2) gives
\[
\left(
\int_{\partial^*E_\rho}
\left|H_{z_\rho,\rho}-\bar V_\rho\right|
d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}D_I(t(\rho)),
\tag{3.4}
\]
because \(\bar V_\rho=A_\rho/P(E_\rho)=P(B_\rho)/P(E_\rho)\).

The boundedness assumption \(E\subset B_R\) is not a graph hypothesis. It is the
standard bounded reduction used in quantitative Saint--Venant/Faber--Krahn
arguments. If one wants the completely unbounded statement, this is the only
place where a tail truncation or bounded reduction is needed.

## 4. Metric derivative modulo translations

Let \(z_\rho\) be the center from the homothetic velocity defect lemma. The
normal velocity of the normalized set \(\rho^{-1}(E_\rho-z_\rho)\), modulo
translations, is represented by
\[
W_\rho
:=
V_\rho-H_{z_\rho,\rho}-a_\rho\cdot\nu_\rho,
\]
where \(a_\rho\in\mathbb R^n\) is arbitrary and corresponds to infinitesimal
translation. Taking \(a_\rho=0\) already suffices for an upper bound.

The finite-perimeter first variation of \(L^1\) gives
\[
|\dot F_\rho|_{\mathcal X}
\le
C_{n,\rho_*}
\inf_{a\in\mathbb R^n}
\int_{\partial^*E_\rho}
\left|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho\right|
d\mathcal H^{n-1}.
\tag{4.1}
\]
Combining (2.4) and (3.4),
\[
|\dot F_\rho|_{\mathcal X}^2
\le
C_{n,\rho_*,R}\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)
\tag{4.2}
\]
for a.e. \(\rho\in[\rho_*,1]\).

This is the desired velocity-to-metric derivative estimate with no graph
gauge.

## 5. Metric trace on the cutoff annulus

Let
\[
\rho_\delta=1-\kappa\sqrt\delta.
\]
The profile-gap estimate gives the interval lower bound for
\[
d\mu(\rho)=(-t_\rho(\rho))\,d\rho:
\]
on any interval \(J=[a,b]\subset[\rho_*,\rho_\delta]\),
\[
\mu(J)\ge c_{n,\rho_*}(b-a)-C_{n,\rho_*}\delta.
\tag{5.1}
\]
Thus \(\mu\) may have microscopic holes of length \(O(\delta)\), but not larger
holes.

The exact deficit identity, quantitative isoperimetry, and (4.2) give
\[
\int_{\rho_*}^{\rho_\delta}
\left(
d_{\mathcal X}(F_\rho,B_1)^2
+|\dot F_\rho|_{\mathcal X}^2
\right)\,d\mu(\rho)
\le
C_{n,\rho_*,R}\delta.
\tag{5.2}
\]
The metric Sobolev trace lemma applied with (5.1) yields a radius
\[
\widehat\rho\in[\rho_\delta-C\delta,\rho_\delta]
\]
such that
\[
d_{\mathcal X}(F_{\widehat\rho},B_1)^2
\le C_{n,\rho_*,R}\delta.
\tag{5.3}
\]
This is the metric version of the Hilbert trace estimate in the graph note.

## 6. Transfer back to the original set

Since
\[
|\Omega\setminus E_{\widehat\rho}|
=\omega_n(1-\widehat\rho^n)
\le C_n\sqrt\delta,
\]
the elementary superlevel transfer gives
\[
\mathcal A(\Omega)
\le
\mathcal A(E_{\widehat\rho})+C_n\sqrt\delta.
\]
But (5.3) is exactly
\[
\mathcal A(E_{\widehat\rho})^2\le C_{n,\rho_*,R}\delta.
\]
Therefore
\[
\boxed{
\mathcal A(\Omega)^2
\le C_{n,\rho_*,R}\delta_T(\Omega).
}
\tag{6.1}
\]

This is the sharp Saint--Venant stability estimate in the bounded class, proved
by the global level-set foliation route, without graph entry or selected
minimizers.

## 7. Exact status of the proof

The two finite-perimeter inputs are expanded in
`gmt-inputs-for-metric-closure.md`. With those inputs, the proof above gives a
complete sharp Plan 2 theorem in the bounded class.

1. **Homothetic velocity defect from strong isoperimetry**, (3.2). This is the
   only place where the FMP/Fusco--Julin oscillation-index theorem must be used.
   The expanded note reduces it to the normal oscillation index plus a bounded
   radial trace estimate.
2. **Metric first variation**, (4.1), for the normalized finite-perimeter
   level-set curve. The expanded note proves it for smooth flows and records
   the BV/coarea approximation needed for finite-perimeter torsion levels.

Neither input is a graph theorem. Neither constructs a smoother competitor.
They are intrinsic to the actual level sets \(E_\rho\). This is the cleanest
version of Plan 2 as a genuine replacement for the Plan 1 selection principle.
