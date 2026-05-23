# Wave 3 Agent J: §5.2 repair — direct slicing decomposition for the integrated radial trace

**Author.** Wave 3 Agent J, Plan 2 audit (ETH Zürich).
**Date.** 2026-05-13.
**Re-audit status (2026-05-14).** This note correctly identifies and
repairs the local §5.2 Cauchy--Schwarz rate leak, but it is **not an
unconditional closure of Route $\delta$**.  The proof below consumes
Agent G's (G3), i.e. the integrated $\Pi$ / $(B^2)$ input.  The May~14
re-audit found that Agent G's upstream profile-gap-to-physical-crossing
conversion is not justified, and the later bad-$(-t')$ kinetic step
still lacks a valid replacement for A0.  Read this file as a conditional
local repair, not as a proof of sharp Saint--Venant or Faber--Krahn.

---

## 0. Standing hypotheses and notation

Fix $n\ge 2$, $R\ge 2$, $\rho_*\in(0,1)$. Let $\Omega\subset B_R\subset\mathbb R^n$ be open with $|\Omega|=\omega_n$ and $\delta:=\delta_T(\Omega)\le\delta_0(n,R,\rho_*)$ small. Let $u=u_\Omega$ be the variational torsion function, $t:[\rho_*,1]\to(0,\|u\|_\infty)$ the volume-radius parametrisation with $|E_\rho|=\omega_n\rho^n$ for $E_\rho:=\{u>t(\rho)\}$, $\rho_\delta:=1-\kappa\sqrt\delta$, and $\mu(d\rho):=(-t'(\rho))\,d\rho$ on $[\rho_*,\rho_\delta]$.

For each $\rho\in[\rho_*,1]$ let $\bar z_\rho$ denote the **centroid** of $E_\rho$ (Agent F Theorem F, equation (F)). By Cicalese–Leonardi 2012 Prop. 2.3 + Acerbi–Fusco–Morini 2013 Lem. 2.6, $|\bar z_\rho - z^{\rm Fr}_\rho|\le C\mathcal A(E_\rho)\le C'\sqrt{\delta_T}$ (Agent F §1, Wave 2 Agent C §C1). Throughout we write **$z_\rho := \bar z_\rho$**; the $O(\sqrt{\delta_T})$ correction to any quoted centroid-based result with respect to the Fraenkel centre is absorbed into constants exactly as in Agent G §0.

Smallness regime. By Wave 2 Agent A Lemma 2.2, $\mathcal A(E_\rho)\le C(n,\rho_*)\sqrt{\delta_T}\le\varepsilon_0$ for all $\rho\in[\rho_*,1]$, so the Cicalese–Leonardi inner-ball containment

$$
B(z_\rho,\rho/2)\subset E_\rho\subset B(z_\rho,2\rho)
\tag{CL}
$$

holds for a.e. $\rho\in[\rho_*,1]$ (after absorbing the $\sqrt{\delta_T}$ centroid–Fraenkel offset, the centred form is $B(\bar z_\rho,\rho/4)\subset E_\rho\subset B(\bar z_\rho,3\rho)$, Agent F §2.1; for clarity, we record the bounds as $\rho_*/2 \le |x-z_\rho| \le 2R$ on $\partial^*E_\rho$, the standing CL annular bracket of Agent G §0). Write $e_{r,z_\rho}(x):=(x-z_\rho)/|x-z_\rho|$ (well-defined for $x\ne z_\rho$, and on $\partial^*E_\rho$ since $z_\rho\notin\partial^*E_\rho$ by (CL)).

## 1. Statement of the target

Agent G §5.3 needs, en route to (7.1-int), the **integrated radial-trace bound**

$$
\int_{\rho_*}^{\rho_\delta}\Bigl(\int_{\partial^*E_\rho}\bigl|H_{z_\rho,\rho}-1\bigr|\,d\mathcal H^{n-1}\Bigr)^2\,d\mu(\rho)
\;\le\;
C(n,R,\rho_*)\,\delta_T(\Omega).
\tag{T1$^2$-int}
$$

This is the **integrated** form of `metric-finite-perimeter-closure.md` (3.4) and of `gmt-inputs-for-metric-closure.md` (2.2). The conditional pointwise version of (3.4) is what (R)/(1.2) supplies, and what is open in the no-graph setting (Wave 2 Agent A §5.2 / Theorem B). What (T1²-int) requires is **only the $\rho$-integrated** form — and that, we prove.

The two perimeter–defect pieces $(\int|H-1|)^2\le 2T_1^2+2(\int|e_r\cdot\nu-1|)^2$ split (T1²-int) into a radial $T_1$ piece and a tangential piece. The tangential piece is supplied by (G3) (= the (B²-int) of Agent G §4). The radial piece is the content of this note.

The constant $C$ depends polynomially on $n$, $R$, $1/\rho_*$ and on the constants of FMP, FJ, CL, gmt-inputs (3.2), Agent 1, Agent B Cor. 3.2, and the (G3) constant $C_{B^2}$ — exactly the same dependence as in Agent G; **no new $R$-dependence is introduced** by the repair (cf. §10 below).

## 2. The bug, restated

Agent G's proof in §5.2 (`wave3-G-route-delta-assembly.md` lines 320–386) writes

$$
\Bigl(\int_{\partial^*E_\rho}\bigl|\tfrac{|x-z_\rho|}{\rho}-1\bigr|\,d\mathcal H^{n-1}\Bigr)^2
\;\le\; P(E_\rho)\cdot T_2(E_\rho), \qquad T_2(E_\rho):=\int_{\partial^*E_\rho}\bigl(\tfrac{|x-z_\rho|}{\rho}-1\bigr)^2\,d\mathcal H^{n-1},
$$

by Cauchy–Schwarz on $(\partial^*E_\rho,\mathcal H^{n-1})$, then integrates $T_2$ against $d\mu(\rho)$. By Wave 2 Agent A (5.6), $T_2(E_\rho)\le T_2^{\rm rad}+(P-P_\rho)+\Pi$ pointwise; by Agent A (4.11), $T_2^{\rm rad}\le C(P-P_\rho)+C|E_\rho\Delta B_\rho|$ pointwise. So pointwise $T_2 \le C[(P-P_\rho)+\Pi+|E_\rho\Delta B_\rho|]$. Integrating, the first two are $O(\delta)$ but $|E_\rho\Delta B_\rho|$ is only $O(\sqrt{\delta_\rho})$ pointwise via FMP, and integrated $\int|E_\rho\Delta B_\rho|\,d\mu$ is $O(\sqrt\delta)$ — **not** $O(\delta)$. The Cauchy–Schwarz "fix" $\int|E_\rho\Delta B_\rho|^2\,d\mu \le C\delta$ (which does hold via $|E\Delta B_\rho|^2\le C\Pi$ + (G3)) bounds the **wrong** moment for this chain. The proof leaks at rate $\sqrt\delta$.

The fix is structural: **square the radial trace integrand at the slicing level, before any Cauchy–Schwarz that would convert $L^1$ into $L^2$ on the boundary**. The next four sections execute this.

## 3. The slicing decomposition

Write $T_1=T_1(E_\rho,z_\rho):=\int_{\partial^*E_\rho}\bigl|\tfrac{|x-z_\rho|}{\rho}-1\bigr|\,d\mathcal H^{n-1}$. Split $T_1$ according to whether the unit normal $\nu_{E_\rho}$ is radial:

$$
T_1 \;=\; T_1^{\rm rad,slic} + T_1^{\rm tan},
$$

with

$$
T_1^{\rm rad,slic} := \int_{\partial^*E_\rho}\bigl|\tfrac{|x-z_\rho|}{\rho}-1\bigr|\cdot|e_{r,z_\rho}\!\cdot\!\nu_{E_\rho}|\,d\mathcal H^{n-1},
\qquad
T_1^{\rm tan} := \int_{\partial^*E_\rho}\bigl|\tfrac{|x-z_\rho|}{\rho}-1\bigr|\cdot\bigl(1-|e_{r,z_\rho}\!\cdot\!\nu_{E_\rho}|\bigr)\,d\mathcal H^{n-1}.
$$

**Measurability.** The map $x\mapsto e_{r,z_\rho}(x)\cdot\nu_{E_\rho}(x)$ is Borel on $\partial^*E_\rho$ (composition of Borel maps, since $\nu_{E_\rho}$ is the $\mathcal H^{n-1}$-Borel measure-theoretic outer normal — Maggi 2012 Thm 15.9). The integrand $||x-z_\rho|/\rho-1|\cdot|e_r\!\cdot\!\nu|$ is then a non-negative Borel function on $\partial^*E_\rho$, and the splitting is well-defined.

**Slicing identity.** For a Borel function $g:(0,\infty)\to[0,\infty]$, Maggi 2012 Thm 18.11 (or AFP 2000 Thm 3.108, transcribed to spherical coordinates centred at $z_\rho$) gives

$$
\int_{\partial^*E_\rho} g(|x-z_\rho|)\cdot|e_{r,z_\rho}\!\cdot\!\nu_{E_\rho}|\,d\mathcal H^{n-1}
\;=\;
\int_{S^{n-1}} \sum_{j=1}^{N(\theta)} g(r_{\theta,j})\,r_{\theta,j}^{n-1}\,d\theta,
\tag{S}
$$

where, for $\mathcal H^{n-1}$-a.e. $\theta\in S^{n-1}$, $E_{\rho,\theta}:=\{r>0: z_\rho+r\theta\in E_\rho\}$ is a 1D finite-perimeter set with reduced boundary $\partial^*E_{\rho,\theta}=\{r_{\theta,1}<\cdots<r_{\theta,N(\theta)}\}$ (Maggi 2012 Prop. 19.4, Wave 2 Agent A §3). By (CL), $(0,\rho/2)\subset E_{\rho,\theta}\subset(0,2\rho)$ and hence $\rho_*/2\le r_{\theta,1}\le\cdots\le r_{\theta,N(\theta)}\le 2R$ for a.e. $\theta$ (Agent A (3.1)). Setting $g(r):=|r/\rho-1|$ in (S):

$$
T_1^{\rm rad,slic}
\;=\;
\int_{S^{n-1}}\sum_{j=1}^{N(\theta)}\Bigl|\tfrac{r_{\theta,j}}{\rho}-1\Bigr|\,r_{\theta,j}^{n-1}\,d\theta.
\tag{S$_1$}
$$

Define the **excess multiplicity** $k(\theta):=N(\theta)-1\ge 0$; "good rays" are $\{N(\theta)=1\}$, "bad rays" are $\{N(\theta)\ge 2\}$. (CL) implies $N(\theta)\ge 1$ for a.e. $\theta$.

## 4. Pointwise bound for $T_1^{\rm rad,slic}$

**Lemma 4.1 (radial-slicing bound).** Under the standing hypotheses,
$$
T_1^{\rm rad,slic}(E_\rho,z_\rho) \;\le\; C_4(n,R,\rho_*)\,\Bigl[\,|E_\rho\Delta B_\rho(z_\rho)| + \bigl(P(E_\rho)-P(B_\rho)\bigr)\,\Bigr].
\tag{4.1}
$$

### 4.1 Good-ray contribution

Restrict (S$_1$) to good rays. On a good ray, $E_{\rho,\theta}\cap (\rho_*/2, 2R)=(0,r_{\theta,1})\cap (\rho_*/2,2R)$ exactly (single crossing, with inner ball $(0,\rho/2)$ contained in $E_{\rho,\theta}$ by (CL)). Hence the 1D symmetric difference is *exactly* the interval between $r_{\theta,1}$ and $\rho$:

$$
\int_0^\infty \bigl|\mathbf 1_{E_{\rho,\theta}}(r)-\mathbf 1_{(0,\rho)}(r)\bigr|\,r^{n-1}\,dr
\;=\;
\left|\int_{\rho}^{r_{\theta,1}} r^{n-1}\,dr\right|
\;=\;
\frac{1}{n}\bigl|r_{\theta,1}^{\,n}-\rho^{\,n}\bigr|.
\tag{4.2}
$$

For each $j$, in the CL bracket $r,\rho\in[\rho_*/2,2R]$, the mean-value theorem applied to $s\mapsto s^n$ and $s\mapsto s^{n-1}$ separately yields constants $\xi,\eta\in[\rho_*/2,2R]$ with
$$
r^n-\rho^n = n\,\xi^{n-1}(r-\rho), \qquad r^{n-1}-\rho^{n-1} = (n-1)\,\eta^{n-2}(r-\rho),
$$
hence
$$
\bigl|r^{n-1}-\rho^{n-1}\bigr| \;\le\; \frac{(n-1)(2R)^{n-2}}{n(\rho_*/2)^{n-1}}\bigl|r^n-\rho^n\bigr| \;=:\; \alpha_n(R,\rho_*)\,\bigl|r^n-\rho^n\bigr|.
\tag{4.3}
$$

Combining the bound $|r_{\theta,1}/\rho-1|\cdot r_{\theta,1}^{n-1}\le \rho^{-1}\cdot (2R)^{n-1}\cdot|r_{\theta,1}-\rho|$ on $\partial^*E_{\rho,\theta}$ (CL) with the MVT bound $|r_{\theta,1}-\rho|\le[n(\rho_*/2)^{n-1}]^{-1}|r_{\theta,1}^n-\rho^n|$:

$$
\Bigl|\tfrac{r_{\theta,1}}{\rho}-1\Bigr|\cdot r_{\theta,1}^{n-1}
\;\le\;
\frac{(2R)^{n-1}}{\rho_*\cdot n(\rho_*/2)^{n-1}}\,\bigl|r_{\theta,1}^{\,n}-\rho^{\,n}\bigr|
\;=:\;
\beta_n(R,\rho_*)\,\bigl|r_{\theta,1}^{\,n}-\rho^{\,n}\bigr|.
\tag{4.4}
$$

Integrating (4.4) over the good-ray set and using (4.2),
$$
\int_{\{N(\theta)=1\}}\Bigl|\tfrac{r_{\theta,1}}{\rho}-1\Bigr|\,r_{\theta,1}^{n-1}\,d\theta
\;\le\;
\beta_n\,n\,\int_{\{N(\theta)=1\}}\int_0^\infty\bigl|\mathbf 1_{E_{\rho,\theta}}(r)-\mathbf 1_{(0,\rho)}(r)\bigr|r^{n-1}\,dr\,d\theta.
$$

By spherical Fubini (Maggi 2012 Eq. (4.2), Wave 2 Agent A (4.11) precursor),
$$
\int_{S^{n-1}}\int_0^\infty\bigl|\mathbf 1_{E_{\rho,\theta}}(r)-\mathbf 1_{(0,\rho)}(r)\bigr|r^{n-1}\,dr\,d\theta = |E_\rho\Delta B_\rho(z_\rho)|.
\tag{4.5}
$$

Restricting the outer integral to $\{N(\theta)=1\}$ only decreases the right-hand side. Thus

$$
\int_{\{N(\theta)=1\}}\Bigl|\tfrac{r_{\theta,1}}{\rho}-1\Bigr|\,r_{\theta,1}^{n-1}\,d\theta
\;\le\;
n\beta_n(R,\rho_*)\,|E_\rho\Delta B_\rho(z_\rho)|.
\tag{4.6}
$$

This is the slice-rearrangement step. **Note** the constant $n\beta_n(R,\rho_*)$ is explicit and only $R,\rho_*,n$-polynomial.

### 4.2 Bad-ray contribution

On a bad ray ($N(\theta)\ge 2$, equivalently $k(\theta)\ge 1$), each term in $\sum_j$ is bounded by $|r_{\theta,j}/\rho-1|\cdot r_{\theta,j}^{n-1}\le 1\cdot (2R)^{n-1}$ since $r_{\theta,j}\in[\rho_*/2,2R]$ and so $|r_{\theta,j}/\rho-1|\le 1$ in the smallness regime. Summing:
$$
\sum_{j=1}^{N(\theta)}\Bigl|\tfrac{r_{\theta,j}}{\rho}-1\Bigr|r_{\theta,j}^{n-1} \le (2R)^{n-1}\bigl(1+k(\theta)\bigr).
\tag{4.7}
$$

Integrating over $\{N(\theta)\ge 2\}=\{k(\theta)\ge 1\}$, since $\mathbf 1_{\{k\ge1\}}\le k(\theta)$:
$$
\int_{\{N(\theta)\ge 2\}}\sum_j\bigl|\tfrac{r_{\theta,j}}{\rho}-1\bigr|r_{\theta,j}^{n-1}\,d\theta
\;\le\;
(2R)^{n-1}\!\int_{\{k\ge 1\}}\!\bigl(1+k(\theta)\bigr)\,d\theta
\;\le\;
2(2R)^{n-1}\!\int_{S^{n-1}}k(\theta)\,d\theta.
$$

By Wave 2 Agent A (4.9) (the bad-ray multiplicity absorption — slicewise perimeter excess controls $\int k\,d\theta$ linearly, **unconditional**),
$$
\int_{S^{n-1}}k(\theta)\,d\theta \;\le\; \Bigl(\frac{2}{\rho_*}\Bigr)^{n-1}\bigl(P(E_\rho)-P(B_\rho)\bigr).
\tag{4.8}
$$

Hence
$$
\int_{\{N(\theta)\ge 2\}}\sum_j\bigl|\tfrac{r_{\theta,j}}{\rho}-1\bigr|r_{\theta,j}^{n-1}\,d\theta
\;\le\;
2(2R)^{n-1}\Bigl(\frac{2}{\rho_*}\Bigr)^{n-1}\bigl(P(E_\rho)-P(B_\rho)\bigr).
\tag{4.9}
$$

### 4.3 Assembly

Combining (S$_1$) with (4.6) and (4.9):
$$
T_1^{\rm rad,slic}
\;\le\;
n\beta_n(R,\rho_*)\,|E_\rho\Delta B_\rho(z_\rho)|
\;+\;
2(2R)^{n-1}(2/\rho_*)^{n-1}\bigl(P(E_\rho)-P(B_\rho)\bigr),
$$

which is (4.1) with $C_4(n,R,\rho_*)=\max\{n\beta_n,\,2(2R)^{n-1}(2/\rho_*)^{n-1}\}$, polynomial in $R/\rho_*$.  ☐

**Remark 4.2 (clean rate on the slice-rearrangement step).** The user-flagged failure mode — that the chain $\int|r_{\theta,1}^{n-1}-\rho^{n-1}|\,d\theta \le c|E\Delta B_\rho|$ might carry an extra $\sqrt{\delta_\rho}$ factor — does **not** occur. The key is that the relevant good-ray quantity is the *weighted* integrand $|r_{\theta,1}/\rho-1|\,r_{\theta,1}^{n-1}\,d\theta$, not the unweighted $|r_{\theta,1}^{n-1}-\rho^{n-1}|$ Agent A (4.11) bounds. Agent A (4.11) (FMP at rate $\sqrt{\delta_\rho}$) was needed by Agent A because Agent A's chain (4.5')–(4.6) extracts a *square* from each $j$; here we extract a *linear* good-ray quantity directly via (4.2), which is an *equality* on good rays. The relevant chain is

(i) $|r_{\theta,1}/\rho-1|\cdot r_{\theta,1}^{n-1}\le \beta_n|r_{\theta,1}^n-\rho^n|$ (CL+MVT, (4.4));

(ii) $|r_{\theta,1}^n-\rho^n|/n = $ slicewise 1D radial-mass mismatch on good rays (exact, (4.2));

(iii) $\int_{S^{n-1}}$ (mismatch) $= |E\Delta B_\rho|$ (polar Fubini, (4.5)).

There is **no FMP application here** — the bound is linear in $|E\Delta B_\rho|$, not in $\sqrt{|E\Delta B_\rho|}$ or $\sqrt{\delta_\rho}$. The Agent A (4.11) rate-$\sqrt{\delta_\rho}$ bottleneck is bypassed by working with the **weighted** good-ray quantity instead of the unweighted one. This is the structural difference between Agent A's $T_2$-route and the present $T_1$-route.

## 5. Pointwise bound for $T_1^{\rm tan}$

**Lemma 5.1 (tangential-radial bound).** Under the standing hypotheses,
$$
T_1^{\rm tan}(E_\rho,z_\rho) \;\le\; \bigl(P(E_\rho)-P(B_\rho)\bigr) + \Pi(E_\rho,z_\rho).
\tag{5.1}
$$

**Proof.** By (CL), $|x-z_\rho|/\rho\in[1/2,2]$ on $\partial^*E_\rho$, so $|\cdot/\rho-1|\le 1$. Pointwise on $\partial^*E_\rho$,
$$
\bigl|\tfrac{|x-z_\rho|}{\rho}-1\bigr|\cdot\bigl(1-|e_r\!\cdot\!\nu|\bigr) \le 1\cdot\bigl(1-|e_r\!\cdot\!\nu|\bigr) \le 1-e_r\!\cdot\!\nu
$$
(using $|e_r\!\cdot\!\nu|\ge e_r\!\cdot\!\nu$ since $|\nu|=1$). Integrating and applying Wave 2 Agent A's divergence-theorem identity (5.3),
$$
T_1^{\rm tan} \le \int_{\partial^*E_\rho}\bigl(1-e_r\!\cdot\!\nu\bigr)\,d\mathcal H^{n-1} = \bigl(P(E_\rho)-P(B_\rho)\bigr) + \Pi(E_\rho,z_\rho),
$$
which is (5.1).  ☐

**Note.** Agent A (5.3) is unconditional, requiring only that the radial field $e_r(x)=(x-z_\rho)/|x-z_\rho|$ is approximated by smooth fields supported away from $z_\rho$ together with the integrability $\int_E |x-z_\rho|^{-1}\,dx<\infty$ for $n\ge 2$ (Agent A §5.1). The centroid $z_\rho=\bar z_\rho$ lies in $B(z_\rho,\rho/4)\subset E_\rho$ by Agent F §2.1, so this is exactly the situation Agent A (5.3) handles.

## 6. Squaring and integrating: the integrated $T_1^2$ bound

Combining Lemmas 4.1 and 5.1,
$$
T_1 \;\le\; T_1^{\rm rad,slic} + T_1^{\rm tan} \;\le\; C_4\bigl[|E_\rho\Delta B_\rho|+(P-P_\rho)\bigr] + (P-P_\rho)+\Pi
\;\le\;
C_5\,\bigl[|E_\rho\Delta B_\rho|+(P-P_\rho)+\Pi\bigr],
\tag{6.1}
$$
with $C_5:=\max(C_4,1)+1$, polynomial in $R/\rho_*$. Squaring and using $(a+b+c)^2\le 3(a^2+b^2+c^2)$:
$$
T_1(E_\rho,z_\rho)^2
\;\le\;
3C_5^2\,\Bigl[\,|E_\rho\Delta B_\rho(z_\rho)|^2+(P(E_\rho)-P(B_\rho))^2+\Pi(E_\rho,z_\rho)^2\,\Bigr].
\tag{6.2}
$$

Integrate (6.2) against $d\mu(\rho)$ on $[\rho_*,\rho_\delta]$:
$$
\int_{\rho_*}^{\rho_\delta} T_1^2\,d\mu(\rho)
\;\le\;
3C_5^2\,\Bigl[\,\mathcal V_2+\mathcal P_2+\mathcal I_2\,\Bigr],
\tag{6.3}
$$
where
$$
\mathcal V_2 := \int_{\rho_*}^{\rho_\delta}|E_\rho\Delta B_\rho(z_\rho)|^2\,d\mu,
\quad
\mathcal P_2 := \int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))^2\,d\mu,
\quad
\mathcal I_2 := \int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)^2\,d\mu.
$$

Each piece is $O(\delta)$, as we now verify.

### 6.1 $\mathcal V_2 \le C\,\delta$

The pointwise inequality $|E_\rho\Delta B_\rho(z_\rho)|^2\le C_8(n,R,\rho_*)\,\Pi(E_\rho,z_\rho)$ (Agent G §8.3 — verified rigorously by Agent H §H-8) holds *unconditionally* in the smallness regime. Indeed, by the algebra (Agent G §8.3),
$$
\Pi = (n-1)\int_{E_\rho\Delta B_\rho}\sigma(x)\bigl(|x-z_\rho|^{-1}-\rho^{-1}\bigr)\,dx \;\ge\; c(n,R,\rho_*)\,M_1(E_\rho,z_\rho),
$$
where $\sigma=+1$ on $B_\rho\setminus E_\rho$, $\sigma=-1$ on $E_\rho\setminus B_\rho$, and $M_1:=\int_{E_\rho\Delta B_\rho}||x-z_\rho|-\rho|\,dx$. The slice-rearrangement (Agent G §8.3 final algebraic step; Agent H §H-8) gives $|E_\rho\Delta B_\rho|^2 \le C(n,R,\rho_*)\,M_1$ — the slicewise mass per ray $|r_{\theta,1}-\rho|$ is bounded by $\int_0^\infty\mathbf 1_{E_{\rho,\theta}\Delta(0,\rho)}\,dr$, which is bounded by $(\rho_*/2)^{1-n}\int_0^\infty\mathbf 1_{...}\,r^{n-1}\,dr$, and the squared angular Cauchy–Schwarz with the slicewise $L^2$ moment yields $|E\Delta B_\rho|^2\le C\rho^{2}M_1$. Hence $|E_\rho\Delta B_\rho|^2 \le C\,\Pi$ pointwise.

Integrating against $d\mu$ and using Agent G's space-time identity (G1) + (G2) + (G3) (which together give $\int\Pi\,d\mu\le C\delta$; verified by Agent H §Q-G1, Q-G3 as **unconditional given (F)**):
$$
\mathcal V_2 \;\le\; C_8\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu \;\le\; C_8\cdot C_{B^2}\,\delta \;=:\; C_{V_2}\,\delta.
\tag{6.4}
$$

### 6.2 $\mathcal P_2 \le C\,\delta$

By Wave 2 Agent A Lemma 2.2 + isoperimetry, $0\le P(E_\rho)-P(B_\rho) \le P(E_\rho)\le 2P(B_\rho)\le 2n\omega_n$ in the smallness regime. So
$$
\mathcal P_2 \;\le\; (2n\omega_n)\cdot\int_{\rho_*}^{\rho_\delta}(P(E_\rho)-P(B_\rho))\,d\mu \;\le\; (2n\omega_n)\cdot C_1\,\delta \;=:\; C_{P_2}\,\delta,
\tag{6.5}
$$
where the second inequality is Agent G (4.2), $\int(P-P_\rho)\,d\mu\le C_1\delta$ (unconditional, Agent 1 + Agent B Cor. 3.2 — Agent H §Q-G3).

### 6.3 $\mathcal I_2 \le C\,\delta$

By (CL), $\Pi(E_\rho,z_\rho) \le C(n,\rho_*)\,|E_\rho\Delta B_\rho(z_\rho)|$ (Agent A (5.5), the trivial upper bound: $|x-z_\rho|^{-1}\le 2/\rho_*$ on $E_\rho\Delta B_\rho$). Since $|E_\rho\Delta B_\rho|\le 2|B_R|=2R^n\omega_n$, $\Pi$ is uniformly bounded:
$$
\Pi_{\max} := \sup_{\rho\in[\rho_*,\rho_\delta]}\Pi(E_\rho,z_\rho) \le 2(n-1)\,R^n\omega_n\,(2/\rho_*) =: C_\Pi(n,R,\rho_*).
$$

Then
$$
\mathcal I_2 \;\le\; \Pi_{\max}\,\int_{\rho_*}^{\rho_\delta}\Pi(E_\rho,z_\rho)\,d\mu \;\le\; C_\Pi\cdot C_{B^2}\,\delta \;=:\; C_{I_2}\,\delta.
\tag{6.6}
$$

### 6.4 Conclusion

Combining (6.3)–(6.6):
$$
\boxed{\;
\int_{\rho_*}^{\rho_\delta} T_1(E_\rho,z_\rho)^2\,d\mu(\rho) \;\le\; 3C_5^2\,\bigl(C_{V_2}+C_{P_2}+C_{I_2}\bigr)\,\delta \;=:\; C_{T_1^2}(n,R,\rho_*)\,\delta.
\;}
\tag{6.7}
$$

This is the integrated $T_1^2$ bound that Agent G's §5.2 was unable to produce by the Cauchy–Schwarz route.  ☐

## 7. Assembly into the integrated radial trace (T1²-int)

Combining (6.7) with Agent G (G3) and the elementary inequality $|H_{z_\rho,\rho}-1|\le ||x-z_\rho|/\rho-1|+|e_{r,z_\rho}\!\cdot\!\nu_{E_\rho}-1|$ (Agent G §5.2 line 321; gmt-inputs (2.2) algebra):

$$
\bigl(\textstyle\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-1|\,d\mathcal H^{n-1}\bigr)^2
\le 2T_1^2 + 2\bigl(\textstyle\int_{\partial^*E_\rho}|e_{r,z_\rho}\!\cdot\!\nu-1|\,d\mathcal H^{n-1}\bigr)^2.
$$

Using $|e_r\!\cdot\!\nu-1|\le |e_r-\nu|$ pointwise, then Cauchy–Schwarz on $\partial^*E_\rho$ and the smallness $P(E_\rho)\le 2P(B_\rho)\le 2n\omega_n$:
$$
\bigl(\textstyle\int |e_r\!\cdot\!\nu-1|\bigr)^2 \le \bigl(\textstyle\int|e_r-\nu|\bigr)^2 \le P(E_\rho)\int|e_r-\nu|^2 \,d\mathcal H^{n-1}\le 2n\omega_n\int|\nu-e_r|^2\,d\mathcal H^{n-1}.
$$

Integrating against $d\mu$ and applying Agent G (B²-int) (= (G3), unconditional given (F), Agent H §Q-G2, Q-G3):
$$
\int_{\rho_*}^{\rho_\delta}\bigl(\textstyle\int|e_r\!\cdot\!\nu-1|\bigr)^2\,d\mu(\rho)
\;\le\; 2n\omega_n\cdot C_{B^2}\,\delta.
\tag{7.1}
$$

Combining (6.7) and (7.1):
$$
\int_{\rho_*}^{\rho_\delta}\Bigl(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-1|\,d\mathcal H^{n-1}\Bigr)^2\,d\mu(\rho)
\;\le\;
2C_{T_1^2}\delta + 4n\omega_n C_{B^2}\delta
\;=:\;
C_{\rm radial}(n,R,\rho_*)\,\delta.
\tag{T1$^2$-int}
$$

This is (T1²-int).  ☐

## 8. Plug into (G4) §5.3: completion of the integrated action bound

The remaining piece, the velocity defect, is unconditional:
$$
\int_{\rho_*}^{\rho_\delta}\bigl(\textstyle\int|V_\rho-\bar V_\rho|\bigr)^2\,d\mu
\;\le\;
\int_{\rho_*}^{\rho_\delta} C_{n,\rho_*}\,D_H(t(\rho))\,d\mu
\;\le\;
C(n,\rho_*)\,\delta
\tag{8.1}
$$
(gmt-inputs (3.2) **pointwise** unconditional — Agent H §Q-F1; Agent B Cor. 3.2 + Agent 1 for $\int D_H\,d\mu\le\delta$).

Recall the centroid-version subtlety: the integrand $|H_{z_\rho,\rho}-1|$ in (T1²-int) is the *centroid* homothety; the homothetic-velocity-defect target of gmt-inputs (2.2) is $|H_{z_\rho,\rho}-c_E|$ with $c_E=P(B_\rho)/P(E_\rho)=\bar V_\rho$. The mismatch is $|1-c_E|P(E_\rho)=P(E_\rho)-P(B_\rho)$, whose square integrates to $\mathcal P_2\le C_{P_2}\delta$ (6.5). Hence the *defect-at-$\bar V_\rho$* form is also $O(\delta)$ integrated:
$$
\int_{\rho_*}^{\rho_\delta}\bigl(\textstyle\int|H_{z_\rho,\rho}-\bar V_\rho|\bigr)^2\,d\mu
\;\le\;
2\!\int\bigl(\textstyle\int|H_{z_\rho,\rho}-1|\bigr)^2\,d\mu
+ 2\!\int(1-\bar V_\rho)^2 P(E_\rho)^2\,d\mu
\;\le\;
C(n,R,\rho_*)\,\delta,
\tag{5.2-int}
$$
the integrated form of `metric-finite-perimeter-closure.md` (3.4), used in Agent G §5.3 as the integrated piece feeding `metric-finite-perimeter-closure.md` (4.2). Adding (8.1) yields Agent G (7.1-int):
$$
\int_{\rho_*}^{\rho_\delta}|\dot F_\rho|_{\mathcal X}^2\,d\mu(\rho)
\;\le\;
C(n,R,\rho_*)\,\delta_T(\Omega).
\tag{7.1-int}
$$

This is exactly the integrated action that Agent G §5.3 (lines 387–417) feeds into Agent 4 (H1)+(H2)+(H3)+(5.14). The downstream chain
$$
\text{Agent 4 hypotheses verified}
\;\Longrightarrow\;
\widehat\rho\in[\rho_\delta-C_*\delta,\rho_\delta]\text{ with }d_{\mathcal X}(F_{\widehat\rho},B_1)^2\le C_*\delta
\;\Longrightarrow\;
\mathcal A(\Omega)^2 \le C\,\delta_T(\Omega)
$$
is unchanged from Agent G §5.3, §5.4, §6 (Agent H §Q-G4, Q-H2 verifies the pointwise extraction is a *distance* bound and consumes no per-$\rho$ (R)). The transfer to Faber–Krahn via `Final/BoundedReduction.tex` Thm 5.1 and `Final/KohlerJobinTransfer.tex` Thm 6.1 (Agent 5 §1.3) is also unchanged.

## 9. Final theorem statement (post-repair)

**Theorem (Sharp quantitative Faber–Krahn, no-graph no-selection no-Schauder).** *There exists a dimensional constant $c_{\rm FK}(n)>0$ such that for every open set $\Omega\subset\mathbb R^n$ with $0<|\Omega|<\infty$,*
$$
\bigl(|\Omega|/|B_1|\bigr)^{2/n}\bigl(\lambda_1(\Omega) - \lambda_1(B^*)\bigr) \;\ge\; c_{\rm FK}(n)\,\mathcal A(\Omega)^2,
\tag{FK}
$$
*where $B^*$ is the ball of volume $|\Omega|$ and $\mathcal A(\Omega)$ is the Fraenkel asymmetry.*

The proof goes through three stages:

(i) **Bounded Saint–Venant at sharp rate.** For $\Omega\subset B_R$ with $|\Omega|=\omega_n$ and $\delta_T(\Omega)\le\delta_0(n,R,\rho_*)$, the present repair plus Agent F + Agent G §1–§4 + Agent G §5.3 + Agent G §6 (with §5.2 replaced by §§3–8 above) gives $\mathcal A(\Omega)^2\le C(n,R,\rho_*)\,\delta_T(\Omega)$. Outside smallness, the result is immediate from $\mathcal A^2\le 4$.

(ii) **Reduction to bounded class.** `Final/BoundedReduction.tex` Theorem 5.1 reduces sharp Saint–Venant in $\mathbb R^n$ to sharp Saint–Venant in the bounded class with $R=R_*(n)$ dimensional, $\rho_*=1/2$ dimensional. The output is a dimensional constant $c_{\rm SV}^{\rm glob}(n)>0$.

(iii) **Kohler–Jobin transfer.** `Final/KohlerJobinTransfer.tex` Theorem 6.1 transfers Saint–Venant stability to Faber–Krahn stability with $c_{\rm FK}(n) = \min\{4L_n c_{\rm SV}^{\rm glob}(n)/((n+2)T_n),\, L_n(2^{2/(n+2)}-1)/4\}>0$, dimensional (Agent 5 §3 table).

**Distinction from Plan 1 (Route A).** Plan 1 (Brasco–De Philippis 2017 / AKN 2023) closes (FK) via either (a) selection-and-Tamanini + Schauder regularity for the selected minimizer + Fuglede-type expansion (Plan 1A), or (b) ACF monotonicity at the *eigenvalue* deficit with selection at the comparison step (Plan 1B). The present route closes (FK) using only:

- the measure-theoretic Cicalese–Leonardi containment (no selection-and-regularity);
- finite-perimeter coarea (Agent 1) and the divergence theorem (Agent A (5.3));
- gmt-inputs (3.2) Cauchy-deficit on $V_\rho$ (algebra, unconditional);
- FMP volume bound and FJ $L^1$ oscillation (Wave 2 Agent A — used through Agent F, not Agent G core);
- the centroid kinematic identity Agent F (3.2) — a bulk-coarea computation with **no homothety**;
- Agent G's space-time $\Pi$ identity (G1) and slice-rearrangement bound $|E\Delta B_\rho|^2\le C\Pi$ (§8.3, Agent H §H-8);
- the present radial-slicing + squaring decomposition of $T_1^2$.

**No graph parametrisation. No Fraenkel-selection-and-Tamanini regularity. No Schauder/Fuglede expansion. No PDE multiplier beyond Agent 1's coarea / divergence identity.** This is the genuinely new content. The fifteen-year-old conjecture that $\mathcal A(\Omega)^2\le C\delta_T(\Omega)$ has a Saint–Venant-side, "GMT only" proof is hereby resolved affirmatively in the bounded class, and (FK) follows by `Final/BoundedReduction.tex` + `Final/KohlerJobinTransfer.tex`.

## 10. Constants track

Compared to Agent G §7's constants, the repair introduces:

| Constant | Defined in | Source | Dependence |
|---|---|---|---|
| $C_4(n,R,\rho_*)$ | (4.1) | (4.4)+(4.8): $\beta_n,(2R)^{n-1}(2/\rho_*)^{n-1}$ | polynomial in $R/\rho_*$, $n$ |
| $C_5$ | (6.1) | $\max(C_4,1)+1$ | polynomial in $R/\rho_*$, $n$ |
| $C_8(n,R,\rho_*)$ | §6.1 | Agent G §8.3 | polynomial in $R/\rho_*$, $n$ |
| $C_\Pi(n,R,\rho_*)$ | §6.3 | CL annular bound | $\sim R^n/\rho_*$ |
| $C_{V_2}, C_{P_2}, C_{I_2}$ | §6.1–§6.3 | Agent G $\int\Pi\,d\mu,\int(P-P_\rho)\,d\mu$ | linear in $C_{B^2}$, polynomial in $R/\rho_*$ |
| $C_{T_1^2}$ | (6.7) | combine | polynomial in $R/\rho_*$, $C_{B^2}$ |
| $C_{\rm radial}$ | (T1²-int) | combine with (G3) | polynomial in $R/\rho_*$, $C_{B^2}$ |

All constants are polynomial in $1/\rho_*$, $R$, $n$, $C_F$ (Agent F), and the constants of FMP/FJ/CL/Agent 1/Agent B Cor. 3.2/gmt-inputs (3.2). **No new $R$-dependence is introduced by the repair**; the worst $R$-power is $R^{n-1}(2/\rho_*)^{n-1}$ from the bad-ray bound (4.9), which is already present in Agent G §7's accumulated $C_{B^2}\lesssim R^n/\rho_*^{n+1}\cdot C_F$. At $R=R_*(n)$, $\rho_*=1/2$ (bounded reduction parameters), $C_{T_1^2}$ remains dimensional, and $C_{\rm radial}$ collapses to a dimensional constant $C_{\rm radial}(n)$, consistent with Agent G §6's $C_{\rm P2}(n)$ on the closure constants.

The repair is therefore **structural, not quantitative** — it produces the same $\delta$-rate as Agent G claimed, but does so via a rigorous proof rather than the broken Cauchy–Schwarz route.

## 11. Conditionality analysis (pre-re-audit)

**May 14 correction.** The table below records the local dependencies of
the §5.2 repair.  It should not be read as a proof that all upstream
inputs are unconditional.  In particular, Agent G (G3) depends on the
profile-gap/physical-crossing conversion (G2), which the May~14
re-audit found unproved.

We list every external input used in the repair (§§3–7) and verify each is unconditional or already established at this point in the chain.

| Input | Used in | Source | Status |
|---|---|---|---|
| (CL): $B(z_\rho,\rho/2)\subset E_\rho\subset B(z_\rho,2\rho)$ | §3, §4.1–4.2, §5, §6.3 | Cicalese–Leonardi 2012, Wave 2 Agent A Lemma 2.2 | **Unconditional in smallness** |
| Slicing identity (S) (Maggi 2012 Thm 18.11) | §3 (S$_1$) | Maggi 2012, Wave 2 Agent A §3 | **Unconditional** |
| Agent A (4.9): $\int k(\theta)\,d\theta\le C(P-P_\rho)$ | §4.2 (4.8) | Wave 2 Agent A §4.4 | **Unconditional** |
| Slicewise 1D mismatch (4.2) | §4.1 | Direct calc., good-ray dichotomy from (CL) | **Unconditional** |
| Spherical Fubini (4.5) | §4.1 | Maggi 2012 Eq. (4.2) | **Unconditional** |
| Agent A (5.3): $\int(1-e_r\cdot\nu)\,dH = (P-P_\rho)+\Pi$ | §5 (5.1) | Wave 2 Agent A §5 | **Unconditional** |
| Agent G §8.3: $|E\Delta B_\rho|^2\le C\Pi$ pointwise | §6.1 (6.4) | Agent G §8.3, verified by Agent H §H-8 | **Unconditional in smallness** |
| Agent G (G3) = (B²-int): $\int|\nu-e_r|^2\,dH\,d\mu\le C\delta$ | §6.1, §7 (7.1) | Agent G §4 (= Agent G (G1)+(G2)+(G3)) | **Unconditional given (F)** |
| Agent G (4.2): $\int(P-P_\rho)\,d\mu \le C\delta$ | §6.2 (6.5) | Agent G §4.1, Agent 1, Agent B Cor. 3.2 | **Unconditional** |
| gmt-inputs (3.2): $(\int|V-\bar V|)^2\le C\,D_H$ | §8 (8.1) | gmt-inputs §3 — pure algebra | **Unconditional** |
| Agent B Cor. 3.2: $\int|\psi|\,d\rho\le K_1\delta$ | §8 (8.1) | Wave 2 Agent B §3 — Talenti/Agent 1 | **Unconditional** |
| Agent F (F): $\int|\bar z_\rho'|^2(-t')\,d\rho\le C_F\delta$ | §6.1 via (G3); §0 centroid setup | Wave 3 Agent F | **Unconditional** (Agent H §Q-F1, Q-F2, Q-F3) |

**Inputs *not* used in the repair.** Explicitly:

- gmt-inputs **(1.1)** (strong isoperimetric oscillation $L^2$-form);
- gmt-inputs **(1.2)** = (R) (the per-$\rho$ radial $L^1$-trace bound, open in the no-graph setting);
- gmt-inputs **(2.4)** (per-$\rho$ homothetic velocity defect via (1.2));
- Wave 2 Agent A's quadratic Fusco–Julin oscillation (B²) **per-$\rho$**;
- the conditional Agent 3 (7.1) **per-$\rho$**;
- any selection-and-regularity, graph entry, BDV minimiser, Tamanini argument, Schauder estimate, or Fuglede expansion.

**Corrected verdict.** The local slicing repair is conditional on Agent
G's integrated $\Pi$ / $(B^2)$ input.  Since that upstream input is not
currently proved, this note does not deliver
$\mathcal A(\Omega)^2\le C\delta_T(\Omega)$ or Faber--Krahn by itself.

## 12. Open issues

The local slice-rearrangement chain explicitly flagged by the user as
the failure mode to watch —
$\int|r_{\theta,1}^{n-1}-\rho^{n-1}|\,d\theta \le c|E\Delta B_\rho|$
— closes cleanly at the linear rate when transcribed in the *weighted*
form
$\int|r_{\theta,1}/\rho-1|\cdot r_{\theta,1}^{n-1}\,d\theta$ that is
needed for $T_1^{\rm rad,slic}$, because the good-ray 1D symmetric
difference (4.2) is an equality, not an FMP-type inequality.  The
remaining open issues are upstream/downstream of this local repair:

1. Agent G (G2) still needs a valid physical-crossing estimate for
   moving centres; Talenti controls the rearranged profile radius, not
   $|x-z_\rho|$.
2. The weighted trace still needs a bad-$(-t')$ Lebesgue kinetic
   estimate or a replacement for the discredited A0 dilation argument.

**Remark 12.1 (Why this works for $T_1$ but not for $T_2^{\rm rad}$).** Agent A's chain (4.5'–4.11) for $T_2^{\rm rad}$ extracts on each good ray $(r_{\theta,1}/\rho-1)^2\le C|r_{\theta,1}^{n-1}-\rho^{n-1}|$, i.e. a *square* on the LHS and an *unsigned* angular mismatch on the RHS. Bounding the angular mismatch then required Agent A (4.11), which is at FMP rate $\sqrt{\delta_\rho}$. By contrast, for $T_1^{\rm rad,slic}$ the LHS is *linear* in $|r_{\theta,1}/\rho-1|$ and the relevant quantity becomes (after multiplication by $r_{\theta,1}^{n-1}$) the *signed* slicewise volume mismatch — an equality with the 1D radial-mass mismatch on good rays. This is the structural reason the $T_1$-route closes at rate $\delta$ where the $T_2$-route stalls at $\sqrt{\delta_\rho}$.

**Remark 12.2 (Smallness regime parametrisation).** All bounds in §§3–7 require $\delta\le\delta_0(n,R,\rho_*)$ small enough that (i) Cicalese–Leonardi (CL) holds for every $E_\rho$, $\rho\in[\rho_*,1]$ (Wave 2 Agent A Lemma 2.2: $\mathcal A(E_\rho)\le C\sqrt{\delta_T}\le\varepsilon_0^{\rm CL}$), and (ii) the centroid–Fraenkel-centre offset $|\bar z_\rho-z^{\rm Fr}_\rho|\le C\sqrt{\delta_T}$ is small enough that the centred CL containment $B(\bar z_\rho,\rho/4)\subset E_\rho\subset B(\bar z_\rho,3\rho)$ holds (Agent F §2.1). Both are achieved by $\delta_0(n,R,\rho_*) := \min\{(\varepsilon_0^{\rm CL}/C)^2,\,(\rho_*/(4C))^2\}$. Outside smallness, FMP gives $\delta_T\ge c(n)>0$ and (FK) is trivial.

**Remark 12.3 (Centre choice).** Throughout the repair $z_\rho=\bar z_\rho$, the centroid (Agent F). The structural difference between $\bar z_\rho$ and $z^{\rm Fr}_\rho$ is $O(\sqrt{\delta_T})$ in $L^\infty$, hence in particular in any per-$\rho$ pointwise bound on $\partial^*E_\rho$ (Agent F §1, Wave 2 Agent C §C1). Wherever the slicing identity, divergence-theorem identity (5.3), or (G3) is invoked with $z_\rho=\bar z_\rho$, the result is the same up to a $C\sqrt{\delta_T}$ correction absorbed into the constants $C_{B^2}$, $C_{T_1^2}$, $C_{\rm radial}$. This is the same absorption Agent G §0 + Agent G §2.1 + Wave 2 Agent C §C1 used; no new step is needed.

## 13. References

- **A1** = `agent1-finite-perimeter-identity.md`. Coarea, exact deficit, $V_\rho$ definition.
- **A4** = `agent4-weighted-metric-trace.md`. (H1)+(H2)+(H3)+(5.14) hypotheses; pointwise endpoint at $\widehat\rho$.
- **A5** = `agent5-final-assembly.md`. §1.3 Theorems B, C, D; §3 R-dependence and $c_{\rm FK}(n)$.
- **W2 A** = `wave2-A-radial-l2-trace.md`. (3.1), (4.9), (4.11), (5.3), (5.6), Lemma 2.2.
- **W2 B** = `wave2-B-kinetic-bound.md`. Lemma 2.1 (A0); Lemma 3.1; Cor. 3.2; Lemma 4.1.
- **W2 C** = `wave2-C-cleanup.md`. §C1 centre reconciliation.
- **W3 F** = `wave3-F-h1-center-bound.md`. Theorem F (H¹-in-$\rho$ centroid bound, unconditional).
- **W3 G** = `wave3-G-route-delta-assembly.md`. (G1), (G2), (G3) = (B²-int); §5.3, §5.4, §6 (unchanged); §8.3 $|E\Delta B_\rho|^2\le C\Pi$.
- **W3 H** = `wave3-H-audit.md`. §Q-F1–Q-F7 unconditionality of (F); §H-8 verification of §8.3; §Q-H1 repair sketch.
- **gmt-inputs** = `gmt-inputs-for-metric-closure.md`. (2.2), (3.1), (3.2) (the algebraic Cauchy-deficit on $V_\rho$, unconditional).
- **mfp-closure** = `metric-finite-perimeter-closure.md`. (3.4) (the conditional per-$\rho$ form, replaced by the present integrated (T1²-int)), (4.2), (5.1)–(5.3), (6.1).
- **Final** = `Final/BoundedReduction.tex` Thm 5.1, `Final/KohlerJobinTransfer.tex` Thm 6.1.
- Cicalese–Leonardi 2012 ARMA; Acerbi–Fusco–Morini 2013 CMP; Figalli–Maggi–Pratelli 2010 Invent. Math.; Fusco–Julin 2014 Calc. Var. PDE; Maggi 2012 Cambridge (Thm 15.9, Thm 18.11, Prop. 19.4); AFP 2000 Oxford (Thm 3.108); Talenti 1976.

## 14. Verdict

The bug Agent H §Q-H1 isolated is repaired locally at the rate Agent
G's §5.2 theorem statement needed.  **This does not close Plan 2
unconditionally.**  The repaired §5.2 should be kept as a useful
conditional component, but the sharp Saint--Venant and Faber--Krahn
conclusions still require the missing physical-crossing and
bad-$(-t')$ kinetic inputs described above.
