# Analytic and native-space route

This note records a speculative but concrete route suggested by the GGRT
stability paper and by the analyticity of the torsion function inside the
domain.

The guiding idea is:

> The STFT proof works because the optimizer lives in a native global analytic
> space, the Bargmann--Fock space. For torsion, one should look for the closest
> native replacement: harmonic functions, modified complex gradients in
> dimension two, and boundary graph spaces after the BDV selection step.

The goal is not to replace the BDV route immediately, but to find a setting in
which a GGRT-style second variation can be computed cleanly.

## 1. The harmonic replacement of the torsion function

Let

\[
-\Delta u=1\quad\text{in }\Omega,\qquad u=0\quad\text{on }\partial\Omega.
\]

Define

\[
h(x):=u(x)+\frac{|x|^2}{2N}.
\]

Then

\[
\Delta h=0\quad\text{in }\Omega.
\]

For a ball \(B_R\) centered at the origin,

\[
u_B(x)=\frac{R^2-|x|^2}{2N},
\qquad
h_B(x)=\frac{R^2}{2N}.
\]

Thus the ball is characterized by the fact that the harmonic function \(h\) is
constant on the domain. On the boundary of a general domain,

\[
h|_{\partial\Omega}=\frac{|x|^2}{2N}.
\]

If \(\partial\Omega\) is a small graph over \(\partial B_R\),

\[
x=(R+\varphi(\theta))\theta,
\]

then

\[
h|_{\partial\Omega}
=
\frac{R^2}{2N}
+
\frac{R}{N}\varphi(\theta)
+
O(\varphi^2).
\]

After pulling back to \(B_R\), the first-order part of \(h-h_B\) is just the
harmonic extension of \((R/N)\varphi\). This is exactly why the BDV second
variation sees the \(H^{1/2}\)-norm of the boundary graph.

So the natural "native space" for the torsion problem is not an entire Fock
space, but the harmonic Hardy/Dirichlet space on the ball, after the selected
domain has been reduced to a graph.

## 2. Two-dimensional holomorphic formulation

In dimension \(N=2\), there is a sharper analytic object. With

\[
\partial_z=\frac12(\partial_x-i\partial_y),
\]

the equation \(\Delta u=-1\) gives

\[
\partial_{\bar z}\partial_z u=-\frac14.
\]

Therefore

\[
F_\Omega(z):=\partial_z u(z)+\frac{\bar z}{4}
\]

is holomorphic in \(\Omega\).

For the disk centered at the origin,

\[
u_B(z)=\frac{R^2-|z|^2}{4},
\qquad
\partial_z u_B=-\frac{\bar z}{4},
\]

so

\[
F_B\equiv0.
\]

Thus \(F_\Omega\) measures deviation from the disk in a genuinely holomorphic
space. If \(\Omega\) is a selected smooth near-disk domain, one can pull
\(F_\Omega\) back to the unit disk by a conformal map or by the normal graph.
This suggests a possible Bergman/Hardy-space analogue of the GGRT Fock-space
argument.

The boundary condition \(u=0\) implies that \(\nabla u\) is normal to
\(\partial\Omega\). If the Serrin condition is nearly satisfied, then
\(|\nabla u|\) is nearly constant on \(\partial\Omega\). In complex form, this
places an approximate boundary constraint on \(F_\Omega\). This may allow one
to turn the weighted Hölder deficit \(D_H\) into a boundary norm for a
holomorphic function.

## 3. Candidate GGRT-style functional for torsion

For a fixed volume level \(s\), define

\[
\mathcal K_s(\Omega)
:=
\int_{\{u_\Omega>u_\Omega^*(s)\}}u_\Omega\,dx.
\]

The ball maximizes \(\mathcal K_s\) among domains with fixed volume, at least
morally by the same rearrangement/level-set proof. A GGRT-style variational
route would try to prove, for nearly spherical sets,

\[
\mathcal K_s(B)-\mathcal K_s(\Omega)
\gtrsim_s
\|\varphi\|_{H^{1/2}(\partial B)}^2
\]

under the usual volume and translation orthogonality conditions.

This is a level-set-sensitive analogue of the BDV expansion for the full
torsion energy

\[
E(\Omega)-E(B)\gtrsim \|\varphi\|_{H^{1/2}}^2.
\]

The advantage is that \(\mathcal K_s\) interacts directly with the
Nicola--Tilli convexity proof and with the matched superlevel set
\(\{u>u^*(s)\}\). The obstacle is that differentiating \(\mathcal K_s\) moves
both the domain and the internal level surface.

## 4. How to compute the second variation

Work in the already-selected near-ball regime:

\[
\partial\Omega_\varepsilon
=
\{(1+\varepsilon\varphi(\theta))\theta:\theta\in\partial B\},
\]

with

\[
\int_{\partial B}\varphi=0,
\qquad
\int_{\partial B}\theta_i\varphi(\theta)\,d\theta=0.
\]

Let

\[
u_\varepsilon=u_{\Omega_\varepsilon},
\qquad
h_\varepsilon=u_\varepsilon+\frac{|x|^2}{2N}.
\]

Pull \(h_\varepsilon\) back to \(B\). To first order,

\[
h_\varepsilon-h_B
\approx
\varepsilon H(\varphi),
\]

where \(H(\varphi)\) is the harmonic extension of a multiple of \(\varphi\).
Expanding in spherical harmonics,

\[
\varphi=\sum_{k\ge2}\varphi_k,
\]

one expects a diagonal second variation

\[
\mathcal K_s(B)-\mathcal K_s(\Omega_\varepsilon)
=
\varepsilon^2
\sum_{k\ge2} a_k(s)\|\varphi_k\|_{L^2(\partial B)}^2
+o(\varepsilon^2).
\]

The key task is to prove a spectral gap

\[
a_k(s)\ge c(s)(1+k)
\]

or at least

\[
\sum_{k\ge2} a_k(s)\|\varphi_k\|_2^2
\gtrsim_s
\|\varphi\|_{H^{1/2}}^2.
\]

This would be the torsion analogue of GGRT's negative-definite second
variation for their functional \(K[F]\) after removing the neutral modes.

## 5. Entire/harmonic approximation idea

For arbitrary rough domains, \(u\) is only useful inside \(\Omega\). But after
BDV selection, \(\Omega\) is a smooth near-ball. Then one can try either:

1. Pull back \(h\) to the ball and work in the harmonic Dirichlet space there.
2. In dimension two, pull back the holomorphic field
   \[
   F_\Omega=\partial_z u+\bar z/4
   \]
   to the disk and work in a Bergman/Hardy space.
3. Approximate the pulled-back harmonic or holomorphic object by global
   harmonic polynomials or entire functions, using Runge-type approximation,
   while tracking boundary norms.

The third option is attractive but risky: approximation alone may not preserve
positivity of the level sets or the torsion boundary condition. The safer
version is to use approximation only after the selected minimizer has already
entered the graph regime, so the geometry is controlled independently.

## 6. Relation to the hybrid penalized route

This analytic route should be viewed as a possible replacement for the last
compactness-heavy step, not for the selection principle.

The proposed chain is:

1. Use the quantitative BDV selection lemma to replace \(\Omega\) by a selected
   minimizer \(U\), preserving \(Q_\alpha\).
2. Use density and flatness to put \(\partial U\) into a global graph regime.
3. Convert \(u_U\) to the harmonic object
   \[
   h_U=u_U+\frac{|x|^2}{2N}
   \]
   or, in \(N=2\), to the holomorphic object
   \[
   F_U=\partial_z u_U+\bar z/4.
   \]
4. Compute a GGRT-style second variation for \(\mathcal K_s\) or for the
   level-set deficit in this native space.
5. Use the profile-gap and superlevel replacement ideas to transfer the result
   to the original asymmetry.

If successful, this would give a more constructive proof of the final
near-ball contradiction and might also expose why the exponent \(2\) is sharp.

## 7. Most concrete first calculation

The first calculation to attempt is:

> For nearly spherical \(\Omega_\varepsilon\), compute the second variation of
> \[
> \mathcal K_s(\Omega)
> =
> \int_{\{u_\Omega>u_\Omega^*(s)\}}u_\Omega\,dx
> \]
> at the ball, for one fixed \(s\in(0,|B|)\).

Do it in spherical harmonics. The expected neutral modes are:

- \(k=0\), removed by volume normalization;
- \(k=1\), removed by translation/barycenter normalization.

If the coefficients for \(k\ge2\) have a positive lower bound comparable to the
\(H^{1/2}\) weights, then the GGRT variational strategy has a genuine torsion
analogue.

This calculation is probably the most meaningful way to test whether the
analytic/native-space idea can carry real proof weight.

## 8. Linearized native-space calculation at the ball

Here is the calculation in a form that can be proved next. Normalize the ball to
be \(B=B_1\subset\mathbb R^N\), and write a nearly spherical perturbation as

\[
\partial\Omega_\varepsilon
=
\{r_\varepsilon(\theta)\theta:\theta\in\partial B\},
\qquad
r_\varepsilon(\theta)
=
1+\varepsilon\varphi(\theta)+\frac{\varepsilon^2}{2}\psi(\theta)+o(\varepsilon^2).
\]

Volume preservation gives

\[
\int_{\partial B}\varphi=0,
\qquad
\int_{\partial B}\psi=-(N-1)\int_{\partial B}\varphi^2.
\]

Expand

\[
u_\varepsilon=u_B+\varepsilon u_1+\frac{\varepsilon^2}{2}u_2+o(\varepsilon^2),
\qquad
u_B(r)=\frac{1-r^2}{2N}.
\]

The first shape derivative is harmonic in \(B\) and satisfies

\[
\Delta u_1=0,\qquad
u_1|_{\partial B}=\frac{\varphi}{N}.
\]

Equivalently, for

\[
h_\varepsilon=u_\varepsilon+\frac{|x|^2}{2N},
\]

the first variation of \(h_\varepsilon-h_B\), pulled back to the ball, is the
harmonic extension of \(\varphi/N\). If

\[
\varphi=\sum_{k\ge1}\varphi_k
\]

is the spherical-harmonic decomposition, then

\[
u_1(r,\theta)=\frac1N\sum_{k\ge1}r^k\varphi_k(\theta),
\]

and

\[
\int_B |\nabla (Nu_1)|^2
=
\sum_{k\ge1} k\,\|\varphi_k\|_{L^2(\partial B)}^2.
\]

Thus the native harmonic object sees exactly the homogeneous \(H^{1/2}\) weights
on the boundary graph. This is the clean replacement for the Fock norm in the
GGRT variational proof.

The second boundary datum is also explicit. With the expansion convention above,
the boundary condition \(u_\varepsilon=0\) on \(\partial\Omega_\varepsilon\)
gives

\[
u_2|_{\partial B}
=
-2\varphi\,\partial_r u_1
-\varphi^2\,\partial_{rr}u_B
-\psi\,\partial_r u_B.
\]

Since \(\partial_r u_B(1)=-1/N\) and \(\partial_{rr}u_B(1)=-1/N\), this becomes

\[
u_2|_{\partial B}
=
-2\varphi\,\partial_r u_1
+\frac{\varphi^2+\psi}{N}.
\]

This formula is the input needed to compute the diagonal coefficients of the
second variation.

## 9. The moving-level part of \(\mathcal K_s\)

Fix \(s\in(0,|B|)\), set

\[
\rho:=\left(\frac{s}{\omega_N}\right)^{1/N},
\qquad
\tau:=u_B(\rho)=\frac{1-\rho^2}{2N}.
\]

The ball's matched superlevel set is \(B_\rho=\{u_B>\tau\}\). Write the
functional as

\[
\mathcal K_s(\Omega)
=
\int_{\mathbb R^N}(u_\Omega-t_\Omega)_+\,dx+t_\Omega s,
\qquad
|\{u_\Omega>t_\Omega\}|=s.
\]

This representation removes the first-order contribution of the moving level.
At the ball,

\[
\mathcal K_s'(B)[\varphi]
=
\int_{B_\rho}u_1\,dx.
\]

Therefore \(\mathcal K_s'(B)[\varphi]=0\) for every first-order
volume-preserving perturbation: the \(k=0\) mode is removed by volume, and all
nonzero spherical harmonics integrate to zero on \(B_\rho\).

The first variation \(t_1\) of the threshold is determined by preserving the
volume of the internal level set:

\[
0=
\int_{\partial B_\rho}
\frac{u_1-t_1}{|\nabla u_B|}\,d\mathcal H^{N-1}.
\]

Hence \(t_1\) is the average of \(u_1\) on \(\partial B_\rho\); in particular
\(t_1=0\) on every mode \(k\ge1\).

The expected second-variation formula is

\[
\mathcal K_s''(B)[\varphi,\varphi]
=
\int_{B_\rho}u_2\,dx
+
\int_{\partial B_\rho}
\frac{(u_1-t_1)^2}{|\nabla u_B|}\,d\mathcal H^{N-1}.
\]

Since \(|\nabla u_B|=\rho/N\) on \(\partial B_\rho\), the moving-level term is

\[
\frac{N}{\rho}
\int_{\partial B_\rho}(u_1-t_1)^2\,d\mathcal H^{N-1}.
\]

The remaining task is to insert the harmonic expansion for \(u_1\), solve for
the harmonic \(u_2\) from the boundary datum in Section 8, and obtain

\[
\mathcal K_s(B)-\mathcal K_s(\Omega_\varepsilon)
=
\frac{\varepsilon^2}{2}
\sum_{k\ge2}a_k(\rho)
\|\varphi_k\|_{L^2(\partial B)}^2
+o(\varepsilon^2).
\]

The GGRT analogue to prove is the spectral gap

\[
a_k(\rho)\ge c(\rho)(1+k)
\qquad(k\ge2),
\]

after removing \(k=0\) by volume and \(k=1\) by barycenter normalization. If this
holds, \(\mathcal K_s\) gives a direct native-space proof of the near-ball
quadratic stability estimate.

## 10. Two-dimensional holomorphic version

When \(N=2\), the same linearization has a holomorphic form. Let

\[
F_\Omega(z):=\partial_z u_\Omega(z)+\frac{\bar z}{4}.
\]

For the centered disk, \(F_B\equiv0\). In the fixed-disk linearization,

\[
F_{\Omega_\varepsilon}
=
\varepsilon\,\partial_z u_1+O(\varepsilon^2).
\]

If the boundary graph has Fourier expansion

\[
\varphi(e^{i\theta})
=
\sum_{k\ge2}\left(a_k e^{ik\theta}+\overline{a_k}e^{-ik\theta}\right)
\]

after removing volume and translation modes, then the holomorphic part of
\(\partial_z u_1\) has coefficients proportional to

\[
k\,a_k z^{k-1}.
\]

Bergman and Hardy norms of this holomorphic field therefore recover the same
\(k\)-weights as the harmonic Dirichlet norm. This gives a concrete
Bergman/Hardy-space version of the GGRT Fock-space calculation: prove the
second variation of \(\mathcal K_s\) is coercive in the norm of
\(\partial_z u_1\), then translate that coercivity back to
\(\|\varphi\|_{H^{1/2}(\partial B)}\).
