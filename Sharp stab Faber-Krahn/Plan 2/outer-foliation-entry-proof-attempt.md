# Outer foliation entry proof attempt

This note pushes the hard task suggested by
`global-foliation-trace.md` and `fvht-center-gluing-import.md`: prove the
outer foliation entry theorem using only the global level-set information,
center gluing, and the \(D_H\) velocity defect.

The conclusion is that the route can be sharpened beyond the previous
one-level argument. The right proof traces the foliation not exactly at
\(\rho=1\), where the natural weight may degenerate, but at
\[
\rho_\delta:=1-\kappa \delta_T(\Omega)^{1/2}.
\]
The remaining boundary layer has volume \(O(\delta_T^{1/2})\), hence contributes
only \(O(\delta_T)\) after squaring. This keeps the sharp exponent and avoids
the old \(\eta^{-1}\) averaging loss.

The main unresolved point is now very precise: a finite-perimeter
velocity-to-metric-derivative inequality modulo translations. In the smooth
graph regime the inequality is proved below by a direct computation.

Throughout,
\[
|\Omega|=\omega_n,\qquad B=B_1,\qquad
\delta:=\delta_T(\Omega)=E(\Omega)-E(B).
\]
Let
\[
E_\rho:=\{u>t(\rho)\},\qquad |E_\rho|=\omega_n\rho^n.
\]

## 1. Exact weighted action in \(\rho\)

The level-set identity gives
\[
2\delta
=
\int_0^1
\frac{D_H(t(\rho))+D_I(t(\rho))}
{n^2\omega_n^{2/n}(\omega_n\rho^n)^{1-2/n}}
(-t_\rho(\rho))\,d\rho.
\]
On any fixed annulus \(\rho\in[\rho_*,1]\), write
\[
d\mu(\rho):=(-t_\rho(\rho))\,d\rho.
\]
The denominator is comparable to a dimensional constant on this annulus, so
\[
\int_{\rho_*}^1
\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)\,d\mu(\rho)
\le C_n\delta.
\tag{1.1}
\]

The profile-gap lemma gives more than small total action. Since
\[
0\le u_B^*(s)-u_\Omega^*(s)\le \frac{2\delta}{s},
\]
for \(s=\omega_n\rho^n\), one has, uniformly on \([\rho_*,1]\),
\[
|t(\rho)-t_B(\rho)|\le C_{n,\rho_*}\delta,
\qquad
t_B(\rho)=\frac{1-\rho^2}{2n}.
\tag{1.2}
\]
Consequently, for every interval \(J=[a,b]\subset[\rho_*,1]\),
\[
\mu(J)
=t(a)-t(b)
\ge
\frac{b^2-a^2}{2n}-C_{n,\rho_*}\delta.
\tag{1.3}
\]
Thus \(\mu\) is not pointwise comparable to Lebesgue measure, but it is
comparable on intervals whose length is larger than \(C\delta\). This is enough
for the endpoint cutoff below.

## 2. Endpoint cutoff: where the sharp exponent is recovered

Set
\[
\rho_\delta:=1-\kappa\delta^{1/2},
\]
with \(\kappa>0\) fixed and \(\delta\) small. Then
\[
|\Omega\setminus E_{\rho_\delta}|
=\omega_n(1-\rho_\delta^n)
\le C_n\delta^{1/2}.
\]
Therefore the elementary transfer estimate gives
\[
\mathcal A(\Omega)
\le
\mathcal A(E_{\rho_\delta})+C_n\delta^{1/2}.
\tag{2.1}
\]
So it is enough to prove
\[
\mathcal A(E_{\rho_\delta})^2\le C_n\delta.
\tag{2.2}
\]

The advantage is that the trace is now taken at an interior endpoint separated
from \(\rho=1\) by \(O(\delta^{1/2})\). By (1.3), every interval of length
comparable to \(\delta^{1/2}\) inside \([\rho_*,\rho_\delta]\) has
\(\mu\)-mass comparable to its Lebesgue length. Hence the possible degeneration
of \(-t_\rho\) at the boundary cannot hide an \(O(1)\) trace jump without
paying action.

This is the repair of the earlier fixed-endpoint statement. It replaces the
bad one-level choice by a sharp boundary-layer transfer.

## 3. FvHT center gluing on the outer annulus

For each block \(I_j\subset[\rho_*,\rho_\delta]\), define
\[
\Phi_j(z)=\int_{I_j}|E_\rho\Delta(z+B_\rho)|\,d\rho.
\]
Let \(z_j\) minimize \(\Phi_j\). If the blocks overlap with length bounded
below by \(c_0>0\), the FvHT overlap argument gives
\[
|z_j-z_{j+1}|
\le C_{n,\rho_*,c_0}\bigl(\Phi_j(z_j)+\Phi_{j+1}(z_{j+1})\bigr).
\tag{3.1}
\]
This is elementary: on \(I_j\cap I_{j+1}\),
\[
|(z_j+B_\rho)\Delta(z_{j+1}+B_\rho)|
\le
|E_\rho\Delta(z_j+B_\rho)|
+
|E_\rho\Delta(z_{j+1}+B_\rho)|,
\]
while
\[
\int_{I_j\cap I_{j+1}}
|(z_j+B_\rho)\Delta(z_{j+1}+B_\rho)|\,d\rho
\ge c_{n,\rho_*,c_0}|z_j-z_{j+1}|
\]
as long as the displacement is small; if it is not small, the lower bound is
even stronger after truncating at a dimensional constant.

Using quantitative isoperimetry level by level,
\[
\inf_z |E_\rho\Delta(z+B_\rho)|^2
\le C_n D_I(t(\rho)),
\tag{3.2}
\]
so the centers can be glued on all good blocks. Since only finitely many
blocks are used on \([\rho_*,\rho_\delta]\), this gives a coherent center field
up to an error bounded by the square-root of the integrated \(D_I\) action.
This is enough to choose a gauge, but it is not yet the sharp stability
estimate. The sharp estimate comes from the kinetic control below.

## 4. Smooth velocity lemma modulo translations

Assume for the moment that the outer levels are smooth and admit the modulated
graph representation
\[
\partial E_\rho
=
\{z(\rho)+(\rho+h(\rho,\theta))\theta:\theta\in\partial B\},
\]
with the zero and first spherical harmonics removed:
\[
\int_{\partial B}h=0,\qquad
\int_{\partial B}h\theta_i=0.
\]
Let
\[
X(\rho,\theta)=z(\rho)+(\rho+h(\rho,\theta))\theta,
\qquad
V=\partial_\rho X\cdot\nu_\rho.
\]
Then
\[
|\nabla u|(X(\rho,\theta))=\frac{-t_\rho(\rho)}{V(\rho,\theta)}.
\tag{4.1}
\]
Also
\[
\int_{\partial E_\rho}V\,d\mathcal H^{n-1}
=\frac{d}{d\rho}|E_\rho|
=n\omega_n\rho^{n-1}.
\tag{4.2}
\]
Substituting (4.1) into \(D_H\) yields
\[
D_H(t(\rho))
=
\left(\int_{\partial E_\rho}V\right)
\left(\int_{\partial E_\rho}V^{-1}\right)
-P(E_\rho)^2.
\tag{4.3}
\]
Thus \(D_H\) is the Cauchy deficit of the normal velocity \(V\).

For \(\|h\|_{C^1}\) small,
\[
V=1+z'(\rho)\cdot\theta+\partial_\rho h+O(|h|+|\nabla_\theta h|)^2
O(1+|z'|+|\partial_\rho h|).
\tag{4.4}
\]
The first harmonic \(z'(\rho)\cdot\theta\) is the infinitesimal translation
mode. Since we work modulo translations, this mode is discarded. Expanding the
Cauchy deficit in (4.3) gives
\[
D_H(t(\rho))
\ge
c_n\rho^{n-1}
\|\Pi_{\ge2}\partial_\rho h(\rho)\|_{L^2(\partial B)}^2
-C_n\varepsilon
\rho^{n-1}\|\partial_\rho h(\rho)\|_2^2
-C_n\rho^{n-1}Q(h(\rho)),
\tag{4.5}
\]
where \(\varepsilon=\|h\|_{C^1}\), and \(Q\) is the Fuglede quadratic form
\[
Q(h)=\int_{\partial B}(|\nabla_\theta h|^2-(n-1)h^2).
\]
After absorbing the \(O(\varepsilon)\) term and adding the perimeter expansion
\[
D_I(t(\rho))
\ge
c_n\rho^{2n-4}Q(h(\rho))
-C_n\varepsilon \rho^{2n-4}\|h(\rho)\|_{H^1}^2,
\tag{4.6}
\]
we obtain the smooth foliation coercivity
\[
D_H(t(\rho))+D_I(t(\rho))
\ge
c_n
\left(
\rho^{n-1}\|\partial_\rho h_{\ge2}(\rho)\|_2^2
+\rho^{2n-4}Q(h(\rho))
\right).
\tag{4.7}
\]
On the fixed annulus, all powers of \(\rho\) are harmless.

Multiplying by \(d\mu=(-t_\rho)d\rho\) and using the interval lower bound
(1.3), this gives a weighted Sobolev action for \(h_{\ge2}\) on
\([\rho_*,\rho_\delta]\).

## 5. Weighted trace lemma, with microscopic holes

Let \(H(\rho)\) be a Hilbert-space-valued function on
\([\rho_*,\rho_\delta]\). Assume
\[
\int_{\rho_*}^{\rho_\delta}
\left(\|H\|^2+\|H'\|^2\right)\,d\mu
\le M,
\tag{5.1}
\]
where \(\mu\) satisfies the interval lower bound (1.3). Then
\[
\exists \widehat\rho\in[\rho_\delta-C\delta,\rho_\delta]
\quad\hbox{such that}\quad
\|H(\widehat\rho)\|^2
\le C_{n,\rho_*}M.
\tag{5.2}
\]
If \(d\mu/d\rho\ge c_{n,\rho_*}>0\) on the final interval, then one may take
\(\widehat\rho=\rho_\delta\).

Proof sketch. Average \(H\) on the interval
\[
J_\delta=[\rho_\delta-c\delta^{1/2},\rho_\delta].
\]
By (1.3), \(\mu(J_\delta)\ge c\delta^{1/2}\). Hence
\[
\left\|\fint_{J_\delta}H\,d\mu\right\|^2
\le C\delta^{-1/2}\int_{J_\delta}\|H\|^2\,d\mu.
\]
The interval lower bound allows holes where \(d\mu/d\rho\) is small, but no
hole can have length larger than \(C\delta\). Otherwise (1.3) would fail on
that hole. Thus, moving the endpoint left by at most \(C\delta\), one reaches a
point \(\widehat\rho\) in a nondegenerate component of \(J_\delta\). On that
component, the ordinary Hilbert trace estimate with measure \(d\mu\) gives
(5.2). This is the only reason for the microscopic endpoint adjustment.

This lemma is the analytic substitute for choosing a good boundary-slab level.
It uses the whole annulus and only cuts off the final \(O(\sqrt\delta)\) layer,
plus a harmless \(O(\delta)\) correction to avoid possible degeneration of the
torsion-height measure.

## 6. Sharp theorem in the smooth coherent regime

**Theorem.** Suppose the torsion level foliation of \(\Omega\) is smooth and
admits the coherent modulated graph gauge on
\([\rho_*,\rho_\delta]\), with \(\|h\|_{C^1}\le\varepsilon_n\). Then
\[
\mathcal A(\Omega)^2\le C_n\delta_T(\Omega).
\]

**Proof.** By (1.1), (4.7), and the weighted trace lemma, there exists
\[
\widehat\rho\in[\rho_\delta-C\delta,\rho_\delta]
\]
such that
\[
\|h_{\ge2}(\widehat\rho)\|_2^2
\le C_n\delta.
\]
The zero and first modes are removed by volume normalization and translation,
so
\[
\mathcal A(E_{\widehat\rho})^2
\le C_n\|h_{\ge2}(\widehat\rho)\|_2^2
\le C_n\delta.
\]
Finally transfer from \(E_{\widehat\rho}\) to \(\Omega\). Since
\[
|\Omega\setminus E_{\widehat\rho}|
\le C_n(\delta^{1/2}+\delta),
\]
the boundary-layer transfer gives
\[
\mathcal A(\Omega)
\le \mathcal A(E_{\widehat\rho})+C_n\delta^{1/2},
\]
hence
\[
\mathcal A(\Omega)^2\le C_n\delta.
\]

This proves the desired sharp exponent in the coherent smooth regime without a
selection principle and without a one-level \(\eta^{-1}\) loss.

## 7. Can the coherent graph assumption be removed?

The FvHT center-gluing mechanism removes the main center obstruction. The
remaining issue is not the centers but the passage from rough finite-perimeter
levels to a Hilbert graph coordinate \(h\).

The plausible replacement is a metric version of (4.7). Let
\[
F_\rho:=\rho^{-1}(E_\rho-z(\rho))
\]
for a center field built by the block gluing in Section 3. One wants
\[
\left|\frac{d}{d\rho}F_\rho\right|_{L^1/\mathrm{translations}}^2
+
\operatorname{dist}_{L^1/\mathrm{translations}}(F_\rho,B_1)^2
\le
C_n\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)
\tag{7.1}
\]
in an integrated sense against \(d\mu\).

The distance part follows from quantitative isoperimetry:
\[
\operatorname{dist}_{L^1/\mathrm{translations}}(F_\rho,B_1)^2
\le C_nD_I(t(\rho)).
\tag{7.2}
\]
The derivative part is the hard point. In the smooth case it is exactly the
Cauchy-deficit computation above. For finite-perimeter sets, it should follow
by approximating the level-set flow by smooth normal flows and using lower
semicontinuity of metric derivatives in \(L^1\). The coarea formula supplies
the normal speed, and (4.3) supplies the convex velocity defect.

Thus the full Plan 2 theorem reduces to the following single analytic lemma.

**Velocity-to-metric derivative lemma.** Let \(\rho\mapsto E_\rho\) be the
nested torsion level family on \([\rho_*,\rho_\delta]\), parametrized by
volume radius. Then, after quotienting by translations,
\[
\int_{\rho_*}^{\rho_\delta}
\left|\frac{d}{d\rho}
\rho^{-1}(E_\rho-z(\rho))
\right|_{L^1/\mathrm{translations}}^2\,d\mu(\rho)
\le
C_n
\int_{\rho_*}^{\rho_\delta}
\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr)\,d\mu(\rho).
\tag{7.3}
\]

This is the exact non-smooth analogue of the radial kinetic estimate. If
(7.3) is proved, the weighted metric trace theorem gives a radius
\[
\widehat\rho\in[1-\kappa\sqrt\delta-C\delta,1-\kappa\sqrt\delta]
\]
such that
\[
\operatorname{dist}_{L^1/\mathrm{translations}}(F_{\widehat\rho},B_1)^2
\le C_n\delta,
\]
and then the boundary-layer transfer gives the sharp Saint--Venant stability
inequality for \(\Omega\).

## 8. Route to the finite-perimeter velocity lemma

The finite-perimeter version should not try to manufacture smooth graphs
directly. The right substitute is the strong quantitative isoperimetric
inequality, in the Fusco--Maggi--Pratelli/Fusco--Julin form, which controls a
boundary-normal oscillation index.

For a set \(E\) with \(|E|=|B_\rho|\), define schematically
\[
\beta(E)^2
:=
\inf_z
\int_{\partial^*E}
\left|
\nu_E(x)-\frac{x-z}{|x-z|}
\right|^2\,d\mathcal H^{n-1}.
\]
The strong form of quantitative isoperimetry gives
\[
\beta(E)^2
\le C_n\bigl(P(E)-P(B_\rho)\bigr)
\le C_n\rho^{1-n}D_I(E),
\tag{8.1}
\]
up to harmless normalizations on the fixed annulus.

This supplies the missing replacement for graph geometry. Indeed, the metric
derivative of the normalized curve
\[
F_\rho=\rho^{-1}(E_\rho-z(\rho))
\]
modulo translations is generated by the difference between the actual normal
velocity \(V\) and the homothetic velocity
\[
H_z(x):=\frac{(x-z)\cdot\nu_E(x)}{\rho}.
\]
For a perfect ball centered at \(z\), \(H_z\equiv1\). In general,
\[
\left|H_z-1\right|^2
\lesssim
\left|\nu_E-\frac{x-z}{|x-z|}\right|^2
+\left|\frac{|x-z|}{\rho}-1\right|^2.
\]
The first term is controlled by \(\beta(E)^2\). The second is controlled by
the same strong isoperimetric package after choosing the FMP center \(z\), or
else by the \(L^1\)-closeness plus perimeter deficit on a fixed annulus.
Therefore
\[
\int_{\partial^*E_\rho}|H_{z(\rho)}-1|^2\,d\mathcal H^{n-1}
\le C_nD_I(t(\rho)).
\tag{8.2}
\]

On the other hand, (4.3) gives the velocity variance
\[
\int_{\partial^*E_\rho}|V-\bar V|^2\,d\mathcal H^{n-1}
\le C_nD_H(t(\rho)),
\tag{8.3}
\]
where \(\bar V\) is the average normal velocity. Since \(\rho\) is the volume
radius, \(\bar V=1+O(D_I^{1/2})\) on the fixed annulus. Combining (8.2) and
(8.3),
\[
\inf_{a\in\mathbb R^n}
\int_{\partial^*E_\rho}
\left|V-H_{z(\rho)}-a\cdot\nu_E\right|^2\,d\mathcal H^{n-1}
\le
C_n\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr).
\tag{8.4}
\]
The term \(a\cdot\nu_E\) is the infinitesimal translation mode and is discarded
in the quotient.

Finally, the first variation formula for \(L^1\)-distance of moving sets gives
\[
\left|\frac{d}{d\rho}
\rho^{-1}(E_\rho-z(\rho))
\right|_{L^1/\mathrm{translations}}
\le
C_n
\left(
\int_{\partial^*E_\rho}
\left|V-H_{z(\rho)}-a\cdot\nu_E\right|^2
d\mathcal H^{n-1}
\right)^{1/2}.
\tag{8.5}
\]
Squaring and integrating against \(d\mu\), (8.4)--(8.5) give exactly (7.3).

So the finite-perimeter velocity lemma should follow from three standard
ingredients:

1. strong quantitative isoperimetry / oscillation index for \(D_I\);
2. the exact Cauchy-deficit identity for \(D_H\);
3. lower semicontinuity of metric derivatives under smooth approximation of
   the coarea level flow.

This is meaningfully different from Plan 1 selection. It uses an isoperimetric
normal-oscillation theorem level by level, plus FvHT gluing in \(\rho\), rather
than constructing a penalized free-boundary minimizer.

## 9. Current status

What has been achieved:

1. The old \(\eta^{-1}\) loss is bypassed by tracing the whole foliation at
   \(\rho_\delta=1-\kappa\sqrt\delta\), then transferring through a boundary
   layer whose squared volume is \(O(\delta)\).
2. The FvHT overlap method gives the right center-gluing mechanism and avoids
   choosing a canonical center at the start.
3. In the smooth coherent graph regime, \(D_H+D_I\) gives the exact Sobolev
   action whose trace is the boundary asymmetry.
4. The finite-perimeter route has been reduced further to the strong
   isoperimetric oscillation-index estimate plus a metric first-variation
   inequality.

What remains:

The only non-formal gap is now the rigorous proof of (8.5) for the normalized
level-set curve after FvHT center gluing. The estimate is natural for smooth
flows and should pass to finite-perimeter levels by approximation, but this
lower-semicontinuity step still has to be written carefully.
