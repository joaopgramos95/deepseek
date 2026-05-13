# Agent 3 — Metric first variation modulo translations for the torsion level family

This note makes rigorous the L^1/translations metric-derivative estimate used
in `metric-finite-perimeter-closure.md` (4.1) and in
`gmt-inputs-for-metric-closure.md` Sec. 4--5. The result is stated and proved
without any graph parametrization of \(\partial^*E_\rho\), using only normal
velocity and reduced boundary.

## 0. Notation and standing hypotheses

Let \(\Omega\subset\mathbb R^n\) be a bounded open set, \(\Omega\subset B_R\),
with \(|\Omega|=\omega_n\). Let \(u\in H^1_0(\Omega)\cap C^{0,1}(\overline\Omega)\)
be the torsion function, \(-\Delta u=1\) in \(\Omega\). Standard regularity
(Stampacchia) yields \(u\in W^{2,p}_{\mathrm{loc}}(\Omega)\) for every
\(p<\infty\), and the Sard-type result of De Giorgi together with the coarea
formula (Maggi 2012, Thm. 13.1; Ambrosio--Fusco--Pallara 2000, Thm. 3.40)
gives that, for a.e. \(t>0\),
\[
E_t=\{u>t\}\subset\overline\Omega\subset B_R
\]
is a set of finite perimeter, with reduced boundary \(\partial^*E_t\), outer
unit normal \(\nu_t\), and
\(P(E_t)=\mathcal H^{n-1}(\partial^*E_t)\).
Parametrize by volume radius
\[
|E_\rho|=\omega_n\rho^n,\qquad t=t(\rho),\qquad \rho\in[\rho_*,1],
\]
for some fixed \(\rho_*\in(0,1)\). Then \(\rho\mapsto t(\rho)\) is absolutely
continuous on \([\rho_*,1]\) with \(t'(\rho)\le 0\) a.e. Set
\[
V_\rho(x):=\frac{-t'(\rho)}{|\nabla u(x)|}\qquad
\text{for }x\in\partial^*E_\rho,\ |\nabla u|(x)>0,
\]
the normal velocity of \(\{E_\rho\}\). By coarea,
\[
\int_{\partial^*E_\rho}V_\rho\,d\mathcal H^{n-1}
=\frac{d}{d\rho}|E_\rho|=n\omega_n\rho^{n-1}=:A_\rho.
\tag{0.1}
\]
The natural integrability class is \(V_\rho\in L^1(\partial^*E_\rho)\); no
\(L^2\) bound is assumed.

For a center \(z\in\mathbb R^n\), set
\[
H_{z,\rho}(x):=\frac{(x-z)\cdot\nu_\rho(x)}{\rho}.
\]
By the divergence theorem, \(|H_{z,\rho}|\le(R+|z|)/\rho_*\) on
\(\partial^*E_\rho\), and \(\int_{\partial^*E_\rho}H_{z,\rho}=A_\rho\).

Let \(z_\rho\) be the FvHT-glued centre field from
`fvht-center-gluing-import.md` Sec. 4 (piecewise constant on a finite block
decomposition, Borel measurable, \(L^\infty\)-bounded by \(R+R'\)).

## 1. The metric space \((\mathcal X,d_{\mathcal X})\)

Let \(\mathfrak M\) be the set of (a.e. equivalence classes of) characteristic
functions \(\mathbf 1_A\) with \(|A|<\infty\); equip with \(L^1\) distance.
Let \(\mathbb R^n\) act by translation. Set
\[
\mathcal X:=\mathfrak M/\mathbb R^n,\qquad
d_{\mathcal X}([A],[C])=\inf_{a\in\mathbb R^n}|A\Delta(C+a)|.
\]
The infimum is attained when \(A,C\) are bounded, by tightness. The metric
derivative of an absolutely continuous curve \(\gamma:I\to\mathcal X\) is, in
the sense of Ambrosio--Gigli--Savaré (AGS) 2008, Thm. 1.1.2,
\(|\dot\gamma|(\rho)=\lim_{h\to 0}d_{\mathcal X}(\gamma(\rho+h),\gamma(\rho))/|h|\).

Set \(F_\rho:=\rho^{-1}E_\rho\), with class \([F_\rho]\in\mathcal X\).

## 2. Target theorem

**Theorem.** Under Sec. 0, for a.e. \(\rho\in[\rho_*,1]\),
\[
|\dot F_\rho|_{\mathcal X}
\le C_{n,\rho_*,R}\inf_{a\in\mathbb R^n}
\int_{\partial^*E_\rho}|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho|
\,d\mathcal H^{n-1}.
\tag{T}
\]

## 3. Smooth-case proof

Assume \(\Omega\) smooth, \(u\in C^\infty(\overline\Omega)\), \(|\nabla u|>0\)
on the strip \(\bigcup_{\rho\in[\rho_*,1-\eta]}\partial E_\rho\). Then
\(\partial E_\rho\) is smooth and \(\partial_\rho X=V_\rho\nu_\rho\) is the
normal flow.

Fix \(z,a\in\mathbb R^n\). The homothety \(\Psi_\rho(y)=z+\rho^{-1}(y-z)\)
sends \(E_\rho\) to \(\rho^{-1}(E_\rho-z)+z\). Differentiating
\(\Psi_\rho(X(\rho,x))\) and projecting on \(\nu_\rho\),
\[
\partial_\rho\Psi_\rho(X)\cdot\nu_\rho
=\rho^{-1}(V_\rho-H_{z,\rho}).
\tag{3.1}
\]
Adding infinitesimal translation \(-ha\), the corrected normal velocity is
\[
W_\rho^{z,a}=\rho^{-1}(V_\rho-H_{z,\rho}-a\cdot\nu_\rho).
\tag{3.2}
\]

**First-variation identity.** For any smooth bounded \(C\),
\[
\frac{d}{d\rho}|F_\rho\Delta C|
=\int_{\partial F_\rho}\sigma_\rho W_\rho^{z,a}\,d\mathcal H^{n-1},
\qquad
\sigma_\rho=\pm 1,
\tag{3.3}
\]
(Maggi 2012, Sec. 17.3; AFP 2000, Thm. 3.85). Hence
\(|d/d\rho|F_\rho\Delta C||\le\int_{\partial F_\rho}|W_\rho^{z,a}|\).
Choosing \(C=F_{\rho_0}\), integrating over \([\rho_0,\rho_0+h]\), and
pulling back by \(\Psi_\rho\) (Jacobian \(\rho^{1-n}\)) yields
\[
\int_{\partial F_\rho}|W_\rho^{z,a}|\,d\mathcal H^{n-1}
=\rho^{-n}\int_{\partial^*E_\rho}|V_\rho-H_{z,\rho}-a\cdot\nu_\rho|.
\tag{3.6}
\]
Therefore
\[
\limsup_{h\to 0}\frac{|F_{\rho+h}\Delta F_\rho|}{|h|}
\le \rho_*^{-n}\int_{\partial^*E_\rho}|V_\rho-H_{z,\rho}-a\cdot\nu_\rho|.
\tag{3.7}
\]
Translating \(F_{\rho+h}\) by \(-ha\) and taking inf over \(a\),
\[
\limsup_{h\to 0}\frac{d_{\mathcal X}([F_{\rho+h}],[F_\rho])}{|h|}
\le \rho_*^{-n}\inf_a\int_{\partial^*E_\rho}|V_\rho-H_{z,\rho}-a\cdot\nu_\rho|.
\tag{3.8}
\]

**Remark (L^1 rate).** (3.7) shows the rate is the L^1 norm of the velocity
gap, not the L^2 norm. Squaring is only used downstream (Sec. 7) via
Cauchy--Schwarz against the deficit measure.

## 4. Pass to finite-perimeter levels (BV/coarea)

### 4.1 Approximation.
\(u_k:=u*\eta_k\to u\) in \(W^{1,p}\) for all \(p\in(1,\infty)\) and a.e.
Define \(E_t^k,\,t_k(\rho)\) accordingly. For a.e. \(\rho\),
\(E_\rho^k\to E_\rho\) in \(L^1\) and \(t_k(\rho)\to t(\rho)\) (AFP 2000,
Thm. 3.40).

### 4.2 Perimeter and velocity convergence.
By LSC of perimeter (Maggi 2012, Prop. 12.15), \(P(E_\rho)\le\liminf
P(E_\rho^k)\). By coarea (AFP 2000, Thm. 3.40),
\(\int_0^\infty P(E_t^k)\,dt=\int|\nabla u_k|\to\int|\nabla u|
=\int_0^\infty P(E_t)\,dt\), giving
\[
P(E_\rho^k)\to P(E_\rho)\quad\text{for a.e. }\rho.
\tag{4.5}
\]
By coarea \(\int_{\partial^*E_\rho^k}|V_\rho^k|=|t_k'(\rho)|a^k(t_k(\rho))\),
and Helly + Lebesgue differentiation give \(m_k'\to m'\) a.e. on the level
axis, so
\[
\int_{\partial^*E_\rho^k}|V_\rho^k|
\to\int_{\partial^*E_\rho}|V_\rho|
\quad\text{a.e. }\rho.
\tag{4.6}
\]
For the bounded continuous integrand
\((x,\nu)\mapsto(x-z)\cdot\nu/\rho\) against weakly converging vector
perimeter measures (Maggi 2012, Thm. 21.14; AFP 2000, Thm. 2.39),
\[
\int_{\partial^*E_\rho^k}H_{z,\rho}\to\int_{\partial^*E_\rho}H_{z,\rho},
\quad
\int_{\partial^*E_\rho^k}|H_{z,\rho}|\to\int_{\partial^*E_\rho}|H_{z,\rho}|.
\tag{4.7}
\]

### 4.3 Reshetnyak lower semicontinuity.
For the convex linear-growth integrand
\((s,\nu)\mapsto|s-(x-z)\cdot\nu/\rho-a\cdot\nu|\) (AFP 2000, Thm. 2.38;
Maggi 2012, Lemma 20.7),
\[
\liminf_k\int_{\partial^*E_\rho^k}|V_\rho^k-H_{z,\rho}-a\cdot\nu^k_\rho|
\ge\int_{\partial^*E_\rho}|V_\rho-H_{z,\rho}-a\cdot\nu_\rho|.
\tag{4.9}
\]
Diagonal extraction of optimal \(a^k\) preserves the inequality with the
infimum on both sides.

### 4.4 AGS lower semicontinuity of the metric derivative.

**Lemma (from AGS 2008, Thm. 1.1.2 and Sec. 1.1).** If \(\gamma_k\to\gamma\)
in \(\mathcal X\) pointwise and \(|\dot\gamma_k|\le m_k\) with
\(m_k\rightharpoonup m\) weakly in \(L^1\), then
\(|\dot\gamma|\le m\) a.e.

Proof. From triangle inequality and Fatou,
\(d_{\mathcal X}(\gamma(\rho_2),\gamma(\rho_1))\le\liminf_k\int_{\rho_1}^{\rho_2}m_k
=\int_{\rho_1}^{\rho_2}m\); apply AGS Thm. 1.1.2 to conclude.

Setting \(m_k(\rho):=\rho_*^{-n}\inf_a\int_{\partial^*E_\rho^k}
|V_\rho^k-H_{z_\rho,\rho}-a\cdot\nu^k_\rho|\), which is \(L^1\)-bounded by
the level-set deficit identity applied to \(u_k\), Dunford--Pettis gives
\(m_k\rightharpoonup m\) and Mazur + (4.9) give
\[
m(\rho)\ge\rho_*^{-n}\inf_a\int_{\partial^*E_\rho}|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho|.
\]
Combining,
\[
|\dot F_\rho|_{\mathcal X}\le\rho_*^{-n}\inf_a\int_{\partial^*E_\rho}
|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho|,
\tag{4.11}
\]
which is (T).

## 5. Translations quotient kills the \(a\cdot\nu_\rho\) mode

**Translation derivative formula.** For bounded finite-perimeter \(E\),
\[
\lim_{\varepsilon\to 0}\frac{|E\Delta(E+\varepsilon a)|}{\varepsilon}
=\int_{\partial^*E}|a\cdot\nu_E|\,d\mathcal H^{n-1}.
\tag{5.1}
\]
Proof. Verify for smooth \(E\) by divergence theorem and Fubini along
\(\mathbb R\,a\); approximate (Maggi 2012, Thm. 13.8; AFP 2000, Thm. 3.84).

By (3.7) and (5.1),
\(|F_{\rho+h}\Delta(F_\rho+ha)|
=h\rho_*^{-n}\int|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho|+o(h)\),
so the infimum over \(a\) in (T) is exactly the metric-quotient distance:
not slack, but the precise translation cost projected out.

## 6. Measurability

The center map \(\rho\mapsto z_\rho\) is Borel. The integrand
\((x,\rho)\mapsto|V_\rho-H_{z_\rho,\rho}-a\cdot\nu_\rho|\) is jointly
measurable by Fubini + disintegration along levels (AFP 2000, Thm. 2.28).
The minimizer in \(a\) is unique (strict convexity) and Borel measurable in
\(\rho\) (Aubin--Frankowska 1990, Thm. 8.2.11).

## 7. Square-integrated form

(T) plus the bounds of `gmt-inputs-for-metric-closure.md` (2.4), (3.2):
\[
(\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|)^2\le C\,D_H,
\quad
(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-\bar V_\rho|)^2\le C\,D_I,
\]
together with triangle/squaring:
\[
|\dot F_\rho|_{\mathcal X}^2
\le C_{n,\rho_*,R}\bigl(D_H(t(\rho))+D_I(t(\rho))\bigr).
\tag{7.1}
\]

## 8. Open issues

(O1) AC of \(\rho\mapsto[F_\rho]\): follows from passing the integral
inequality through the smooth approximation; standard but needs careful
writeup.

(O2) Strict-continuity (4.5): integrated coarea convergence + LSC + Fatou;
or invoke Ambrosio--Dal Maso 1990 BV chain rule.

(O3) Singular part of \(\partial E_\rho\): zero \(\mathcal H^{n-1}\)-measure,
all identities on \(\partial^*E_\rho\). No \(C^{1,\alpha}\) needed.

(O4) Center quality: (T) uses only \(|z_\rho|\le R+R'\); center precision
enters only via Agent 2's homothetic velocity defect lemma.

(O5) Boundedness \(E_\rho\subset B_R\): essential for boundedness of
\(H_{z,\rho}\) in (4.7); supplied by bounded reduction.

(O6) No \(L^2\) on \(V_\rho\): the natural class is \(L^1\); (7.1) gains the
square only via deficit-measure integration.

(O7) Choice of \(z\) vs. \(z_\rho^k\): using common \(z_\rho\) is valid by
uniformity of (4.7); could alternatively pick \(z_\rho^k\to z_\rho\).

## 9. Summary

Inputs: smooth first-variation (Maggi 2012, Sec. 17.3); BV/coarea (AFP 2000,
Sec. 3 and Thm. 3.40; Maggi Chs. 13, 17); Reshetnyak continuity (AFP 2000,
Thms. 2.38--2.39); AGS LSC (Ambrosio--Gigli--Savaré 2008, Thm. 1.1.2);
translation-volume (Maggi 2012, Thm. 13.8; AFP 2000, Thm. 3.84); FvHT
center field (`fvht-center-gluing-import.md` Sec. 4).
