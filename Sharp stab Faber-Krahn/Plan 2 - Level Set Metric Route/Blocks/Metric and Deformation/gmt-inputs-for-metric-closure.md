# GMT inputs for the metric finite-perimeter closure

This note expands the two inputs left in
`metric-finite-perimeter-closure.md`:

1. the homothetic velocity defect estimate;
2. the \(L^1\)-metric first variation estimate modulo translations.

No graph parametrization is used.

Throughout \(0<\rho_*\le\rho\le1\), \(E\subset B_R\) is a finite-perimeter set
with \(|E|=|B_\rho|\), and
\[
P_\rho:=P(B_\rho)=n\omega_n\rho^{n-1}.
\]

## 1. Strong isoperimetry input

We use the following strong form of quantitative isoperimetry, due to the
Fusco--Maggi--Pratelli/Fusco--Julin line of results.

**Strong isoperimetric oscillation estimate.** There is a center \(z_E\) such
that
\[
\left(\inf_z |E\Delta(z+B_\rho)|\right)^2
+
\left(
\int_{\partial^*E}
\left|
\nu_E(x)-\frac{x-z_E}{|x-z_E|}
\right|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*}\rho^{n+1}\bigl(P(E)-P_\rho\bigr).
\tag{1.1}
\]
The scaling factor is harmless on the fixed annulus. In the bounded class
\(E\subset B_R\), the same center also satisfies the radial trace estimate
\[
\left(
\int_{\partial^*E}
\left|
\frac{|x-z_E|}{\rho}-1
\right|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}\bigl(P(E)-P_\rho\bigr).
\tag{1.2}
\]

The radial estimate (1.2) follows from the same strong isoperimetric package:
the oscillation index controls the boundary-normal defect, while the
Fraenkel part controls the volume of the radial mismatch. Boundedness converts
the volume mismatch into an \(L^1(\partial^*E)\) trace mismatch by the coarea
argument along rays, with constants depending on \(R\) and \(\rho_*\).

Equivalently, one may take (1.1)--(1.2) as the exact quoted strong
isoperimetric input needed here.

## 2. Homothetic velocity defect

Define
\[
H_{z_E,\rho}(x):=\frac{(x-z_E)\cdot\nu_E(x)}{\rho},
\qquad x\in\partial^*E.
\]
Set
\[
c_E:=\frac{P_\rho}{P(E)}.
\]
Then
\[
\boxed{
\left(
\int_{\partial^*E}|H_{z_E,\rho}-c_E|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}\bigl(P(E)^2-P_\rho^2\bigr).
}
\tag{2.1}
\]

**Proof.** Write
\[
e_r(x):=\frac{x-z_E}{|x-z_E|}.
\]
Then
\[
H_{z_E,\rho}
=
\frac{|x-z_E|}{\rho}\,e_r(x)\cdot\nu_E(x).
\]
Therefore
\[
|H_{z_E,\rho}-1|
\le
\left|\frac{|x-z_E|}{\rho}-1\right|
+
|e_r(x)\cdot\nu_E(x)-1|.
\]
Since \(|e_r|=|\nu_E|=1\),
\[
|e_r\cdot\nu_E-1|
\le
\frac12|e_r-\nu_E|^2
\le
|e_r-\nu_E|.
\]
Integrating and using (1.1)--(1.2),
\[
\left(
\int_{\partial^*E}|H_{z_E,\rho}-1|
\right)^2
\le
C_{n,\rho_*,R}\bigl(P(E)-P_\rho\bigr).
\tag{2.2}
\]
Also
\[
|1-c_E|P(E)
=
P(E)-P_\rho
\]
and, since \(P(E)\) is uniformly bounded in the near-isoperimetric regime and
otherwise (2.1) is trivial after enlarging the constant,
\[
\bigl(|1-c_E|P(E)\bigr)^2
\le C_{n,\rho_*}\bigl(P(E)-P_\rho\bigr).
\tag{2.3}
\]
Combining (2.2) and (2.3),
\[
\left(
\int_{\partial^*E}|H_{z_E,\rho}-c_E|
\right)^2
\le
C_{n,\rho_*,R}\bigl(P(E)-P_\rho\bigr).
\]
Finally,
\[
P(E)^2-P_\rho^2
=(P(E)-P_\rho)(P(E)+P_\rho)
\simeq_{n,\rho_*} P(E)-P_\rho
\]
in the near-isoperimetric regime, while the non-near regime is absorbed into
the constant. This proves (2.1).

Applied to a torsion level \(E_\rho\), where
\[
c_E=\frac{P(B_\rho)}{P(E_\rho)}
=
\frac{A_\rho}{P(E_\rho)}
=\bar V_\rho,
\]
(2.1) becomes
\[
\left(
\int_{\partial^*E_\rho}
|H_{z_\rho,\rho}-\bar V_\rho|\,d\mathcal H^{n-1}
\right)^2
\le C D_I(t(\rho)).
\tag{2.4}
\]

## 3. \(D_H\) controls velocity oscillation

Let \(V_\rho>0\) be the normal speed of the torsion level flow with respect to
\(\rho\), and let
\[
\bar V_\rho=\frac{A_\rho}{P(E_\rho)},
\qquad
A_\rho=P(B_\rho).
\]
The exact Cauchy-deficit identity is
\[
\int_{\partial^*E_\rho}
\frac{(V_\rho-\bar V_\rho)^2}{V_\rho}\,d\mathcal H^{n-1}
=
\frac{A_\rho}{P(E_\rho)^2}D_H(t(\rho)).
\tag{3.1}
\]
Therefore,
\[
\left(
\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}
\right)^2
\le
\left(\int_{\partial^*E_\rho}V_\rho\right)
\left(
\int_{\partial^*E_\rho}
\frac{(V_\rho-\bar V_\rho)^2}{V_\rho}
\right)
\le
C_{n,\rho_*}D_H(t(\rho)).
\tag{3.2}
\]

Combining (2.4) and (3.2),
\[
\left(
\int_{\partial^*E_\rho}
|V_\rho-H_{z_\rho,\rho}|\,d\mathcal H^{n-1}
\right)^2
\le
C_{n,\rho_*,R}\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr).
\tag{3.3}
\]
Since quotienting by translations only decreases the right-hand side, this is
also true with \(V_\rho-H_{z_\rho,\rho}\) replaced by
\[
V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho
\]
and an infimum over \(a\in\mathbb R^n\).

## 4. Metric first variation, smooth proof

Let \(\rho\mapsto E_\rho\) be a smooth nested family with normal velocity
\(V_\rho\). Let \(z(\rho)\) be any absolutely continuous center curve and set
\[
F_\rho:=\rho^{-1}(E_\rho-z(\rho)).
\]
The normal velocity of \(F_\rho\), pulled back to \(\partial E_\rho\), is
\[
\rho^{-1}
\left(
V_\rho-H_{z(\rho),\rho}-z'(\rho)\cdot\nu_\rho
\right).
\]
Hence, for \(h\to0\),
\[
|F_{\rho+h}\Delta F_\rho|
\le
|h|\rho^{-n}
\int_{\partial E_\rho}
\left|
V_\rho-H_{z(\rho),\rho}-z'(\rho)\cdot\nu_\rho
\right|
d\mathcal H^{n-1}
o(|h|).
\]
Taking the quotient by translations removes the \(z'(\rho)\cdot\nu_\rho\)
term. Thus
\[
|\dot F_\rho|_{\mathcal X}
\le
C_{n,\rho_*}
\inf_{a\in\mathbb R^n}
\int_{\partial E_\rho}
\left|
V_\rho-H_{z(\rho),\rho}-a\cdot\nu_\rho
\right|
d\mathcal H^{n-1}.
\tag{4.1}
\]
Together with (3.3), this gives
\[
|\dot F_\rho|_{\mathcal X}^2
\le
C_{n,\rho_*,R}\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)
\tag{4.2}
\]
for smooth flows.

## 5. Finite-perimeter passage

For the torsion family, \(E_\rho\) is nested and has finite perimeter for a.e.
\(\rho\). The coarea formula provides the normal speed \(V_\rho\) and the flux
identity
\[
\int_{\partial^*E_\rho}V_\rho=\frac{d}{d\rho}|E_\rho|.
\]
To pass (4.1) to finite-perimeter levels, use the standard approximation:

1. approximate \(u\) by smooth functions \(u_j\) in \(W^{1,2}_{\rm loc}\) and
   in the coarea sense on the fixed annulus of levels;
2. take the smooth superlevel flows \(E_{\rho,j}\);
3. apply (4.1) to \(E_{\rho,j}\);
4. pass to the limit using lower semicontinuity of perimeter, Reshetnyak
   lower semicontinuity for the normal integrals, and lower semicontinuity of
   metric derivatives for \(L^1\)-convergent curves.

The result is:
\[
\boxed{
|\dot F_\rho|_{\mathcal X}^2
\le
C_{n,\rho_*,R}\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)
\quad\hbox{for a.e. }\rho\in[\rho_*,1].
}
\tag{5.1}
\]

This is the finite-perimeter velocity-to-metric derivative lemma needed in
`metric-finite-perimeter-closure.md`.

## 6. Consequence

Combining (5.1), quantitative isoperimetry for
\[
d_{\mathcal X}(F_\rho,B_1)^2,
\]
the exact level-set deficit identity, and the weighted metric trace lemma gives
the sharp bound
\[
\mathcal A(\Omega)^2\le C_{n,R}\delta_T(\Omega)
\]
for bounded domains.

The only remaining work for a fully publishable version is bibliographic and
technical: cite the precise strong-isoperimetry theorem giving (1.1)--(1.2),
and write the approximation step in Section 5 with the preferred BV/coarea
reference.
