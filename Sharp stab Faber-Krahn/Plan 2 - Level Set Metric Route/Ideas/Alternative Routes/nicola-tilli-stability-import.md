# Ideas imported from the STFT Nicola--Tilli stability paper

This note records what can be imported from
`s00222-024-01248-2-3.pdf`, the 2024 Inventiones paper

> Gómez--Guerra--Ramos--Tilli, *Stability of the Faber--Krahn inequality for
> the short-time Fourier transform*.

The paper proves a sharp quantitative stability version of the Nicola--Tilli
Faber--Krahn theorem for the short-time Fourier transform. It is not directly a
torsion result, but several mechanisms are relevant to `plan2.md`.

## 1. The structural dictionary

In the STFT/Fock setting, the central object is

\[
u_F(z)=|F(z)|^2e^{-\pi |z|^2}
\]

and its superlevel sets

\[
A_t=\{u_F>t\}.
\]

The rearranged profile \(u^*(s)\) satisfies a one-dimensional convexity
inequality. The optimizer profile is \(e^{-s}\). Stability is obtained by
quantifying the area between \(u^*(s)\) and \(e^{-s}\), and then pushing the
information back to sets.

For torsion, the analogous objects are

\[
u=u_\Omega,\qquad E_t=\{u>t\},\qquad v(s)=u_\Omega^*(s),
\]

and the optimizer profile is the ball profile

\[
b(s)=u_B^*(s)
=
\frac{R^2-(s/\omega_n)^{2/n}}{2n},
\qquad |B|=\omega_n R^n.
\]

The torsion level-set inequality gives

\[
v'(s)\ge b'(s).
\]

Thus

\[
h(s):=b(s)-v(s)
\]

is nonnegative and nonincreasing, and

\[
\int_0^{|\Omega|}h(s)\,ds
=
\int_Bu_B-\int_\Omega u_\Omega
=
2(E(\Omega)-E(B)).
\]

This is the exact torsion analogue of the STFT paper's "area between profiles"
method.

## 2. Immediate lemma: profile deficit controls level heights

Since \(h\) is nonincreasing,

\[
0\le h(s)\le \frac{1}{s}\int_0^s h(r)\,dr
\le
\frac{2(E(\Omega)-E(B))}{s}.
\]

Therefore, for \(s\in[\theta|\Omega|,|\Omega|]\),

\[
|u_B^*(s)-u_\Omega^*(s)|
\le
\frac{2(E(\Omega)-E(B))}{\theta|\Omega|}.
\]

This gives quantitative control of near-boundary level heights. If \(s=L-\eta\)
and \(E(\Omega)-E(B)\ll \eta\), then the level

\[
t_\eta:=u_\Omega^*(L-\eta)
\]

is positive and comparable to the corresponding ball level. This selects a
boundary-layer set

\[
E_{t_\eta}=\{u>t_\eta\}
\]

with exactly

\[
|\Omega\setminus E_{t_\eta}|=\eta.
\]

This should be combined with the weighted level-set deficit identity to find
near-boundary levels that are also geometrically good.

## 3. Superlevel replacement

The STFT proof does not try to control an arbitrary set directly. It first
replaces the set \(\Lambda\) by the matched superlevel set

\[
A_\Lambda=\{u_F>u_F^*(|\Lambda|)\}.
\]

Then it proves:

1. the deficit controls the function's distance to the optimizer;
2. this makes \(A_\Lambda\) regular and close to a ball;
3. a transport argument controls \(|\Lambda\Delta A_\Lambda|\);
4. hence \(\Lambda\) itself is close to a ball.

For torsion, the analogous move is:

1. choose \(E_t=\{u_\Omega>t\}\) with prescribed volume \(s\);
2. prove \(E_t\) is close to a ball using the level-set identity;
3. use
   \[
   \mathcal A(\Omega)
   \le
   C\frac{|\Omega\setminus E_t|}{|\Omega|}
   +C\mathcal A(E_t)
   \]
   to transfer the result back to \(\Omega\).

The point of the profile-gap lemma is that it chooses near-boundary levels with
controlled height, while the exact level-set identity supplies averaged control
of \(D_H(t)+D_I(t)\).

## 4. Transport idea for the set comparison

In the STFT paper, set stability is proved by transporting mass from
\(A_\Lambda\setminus\Lambda\) to \(\Lambda\setminus A_\Lambda\). Points moved
farther away from the center lose a definite amount of Gaussian weight, so the
concentration deficit controls the amount of badly moved mass.

For torsion, a literal radial transport is unavailable for arbitrary domains.
But for selected minimizers or near-ball sets, a normal-transport analogue should
be possible:

- compare a near-boundary level \(E_t\) with \(\Omega\) along the flow lines of
  \(\nabla u\), or along the free-boundary normal when \(\Omega\) is already a
  selected minimizer;
- use the nondegeneracy
  \[
  c\operatorname{dist}(x,\partial\Omega)
  \le u(x)\le
  C\operatorname{dist}(x,\partial\Omega)
  \]
  near the free boundary to convert height \(t\) into boundary-layer thickness;
- use density/perimeter bounds to estimate the symmetric difference.

This is one reason the hybrid route looks more promising than the pure
level-set route: the selected minimizers have exactly the free-boundary
structure needed to make this transport quantitative.

## 5. Geometry of superlevel sets

The STFT proof obtains star-shapedness, smoothness, and convexity of relevant
superlevel sets from closeness of \(F\) to the Gaussian and analyticity.

For torsion, the replacement should be:

- for arbitrary domains, no comparable regularity is available;
- for selected minimizers, Alt--Caffarelli regularity gives \(C^{1,\gamma}\)
  free boundary once flatness is known;
- after entering the graph regime, Schauder estimates give \(u_\Omega\) close
  to \(u_B\), and then regular near-boundary level sets follow from the implicit
  function theorem.

So the STFT "regular superlevel geometry" mechanism should be imported only
after the BDV selection step.

## 6. Variational/Fuglede-style route

The STFT paper also proves stability by a variational second-variation argument
for

\[
K[F]=\frac{I_F(s)}{\|F\|^2},
\]

where \(I_F(s)\) is the integral of \(u_F\) over its superlevel set of measure
\(s\). Around the optimizer \(F\equiv1\), after removing neutral modes, the
second variation is uniformly negative.

The torsion analogue would be to study, near the ball,

\[
\mathcal K_s(\Omega)
:=
\int_{\{u_\Omega>u_\Omega^*(s)\}}u_\Omega\,dx
\]

under nearly spherical perturbations of \(\Omega\). The expected result is a
second-variation estimate of the form

\[
\mathcal K_s(B)-\mathcal K_s(\Omega)
\gtrsim_s
\|\varphi\|_{H^{1/2}(\partial B)}^2
\]

after imposing volume and barycenter orthogonality. This would be a
level-set-sensitive analogue of BDV's nearly spherical expansion for \(E\).

This is probably harder than the profile-gap lemma, but it could produce a
direct near-ball stability theorem for the level-set route.

## 7. Revised route for `plan2.md`

The most promising revised route is:

1. Prove the finite-perimeter level-set identity.
2. Add the profile-gap lemma \(0\le b(s)-v(s)\le 2\delta_E/s\).
3. Choose boundary-layer volumes \(s=L-\eta\), with \(\delta_E\ll\eta\ll1\).
4. Use the weighted deficit identity to find one such level with small
   \(D_H+D_I\).
5. Apply quantitative isoperimetry to \(D_I\), and the weighted variance
   identity to \(D_H\).
6. For arbitrary domains this still leaves a regularity gap; for selected
   minimizers, use the BDV free-boundary estimates to close it.
7. Transfer from \(E_t\) back to \(\Omega\) by the boundary-layer asymmetry
   lemma.

This is a genuine import from the STFT stability paper: first stabilize the
matched superlevel set, then transfer stability back to the original set.

## 8. Analytic/native-space refinement

The GGRT proof benefits from living in the Bargmann--Fock space. For torsion,
there is no global entire structure for arbitrary domains, but there is a
native harmonic substitute:

\[
h_\Omega(x):=u_\Omega(x)+\frac{|x|^2}{2N},
\qquad
\Delta h_\Omega=0.
\]

For a ball, \(h_B\) is constant. For a nearly spherical domain, after pulling
back to the ball, the first variation of \(h_\Omega-h_B\) is the harmonic
extension of the boundary graph. This is the natural space in which to try a
GGRT-style second variation.

In dimension two there is an even more literal analytic object:

\[
F_\Omega(z):=\partial_z u_\Omega(z)+\frac{\bar z}{4}.
\]

Since \(\partial_{\bar z}\partial_z u=-1/4\), the function \(F_\Omega\) is
holomorphic in \(\Omega\), and \(F_B\equiv0\) for disks centered at the origin.
For selected smooth near-disks, pulling \(F_\Omega\) back to the unit disk could
put the problem into a Bergman/Hardy-type setting, closer in spirit to the
Fock-space proof.

The concrete calculation to try is the second variation at the ball of

\[
\mathcal K_s(\Omega)
=
\int_{\{u_\Omega>u_\Omega^*(s)\}}u_\Omega\,dx.
\]

If the resulting quadratic form is diagonal in spherical harmonics and has a
spectral gap after removing the \(k=0\) and \(k=1\) modes, this would give a
native torsion analogue of the GGRT variational proof.

## 9. Explicit torsion replacement dictionary

The most useful import from GGRT is now the following concrete dictionary.

| GGRT/STFT step | Torsion replacement | Current status |
| --- | --- | --- |
| Compare \(u^*(s)\) with \(e^{-s}\). | Compare \(v(s)=u_\Omega^*(s)\) with the ball profile \(b(s)\). | Proved at the profile level: \(0\le b-v\le 2\delta_T/s\). |
| Select \(A_\Lambda=\{u_F>u_F^*(|\Lambda|)\}\). | Select \(E_t=\{u_\Omega>t\}\) with \(m(t)=L-\eta\). | Profile gap gives \(t\) in the correct boundary-height range. |
| Prove the matched superlevel set is regular and ball-like. | Prove \(E_t\) has small \(D_I\) and \(D_H\), hence small asymmetry and approximate Serrin data. | Averaged identity gives one such level on a slab; regularity is the open point. |
| Transport from \(A_\Lambda\) back to \(\Lambda\). | Use \(E_t\subset\Omega\) and \(\mathcal A(\Omega)\le \mathcal A(E_t)+2|\Omega\setminus E_t|/|\Omega|\). | Elementary and ready to use. |
| Use Fock analyticity for level-set geometry. | Use BDV selected-minimizer regularity, or harmonic/holomorphic native objects after graph entry. | This is where Plan 1 is needed. |

This table isolates the true gap. The one-dimensional part and the final
set-comparison part are already quantitative. What is missing is a theorem that
turns a selected near-boundary superlevel set into a regular approximate Serrin
domain without losing the sharp exponent.

## 10. Hybrid route with Plan 1 selection

The pure level-set method sees interior levels. Plan 1's selected minimizer
regularity is useful precisely because it turns small positive levels into a
controlled boundary layer.

Assume the Plan 1 selection principle has replaced \(\Omega\) by a selected
minimizer \(U=\{u>0\}\) with:

- density estimates on both phases;
- nondegeneracy of \(u\) at the free boundary;
- a Bernoulli coefficient \(q_U\) bounded above and below;
- \(C^{1,\gamma}\) free boundary once the flatness threshold is reached;
- eventually a global graph over the ball when \(\mathcal A(U)\) is small.

Then the level-set method gains four concrete tools.

First, height becomes thickness:

\[
c\,\operatorname{dist}(x,\partial U)
\le u(x)\le
C\,\operatorname{dist}(x,\partial U)
\]

near \(\partial U\). Thus \(u=t\) is at distance comparable to \(t\) from the
free boundary.

Second, small levels are normal graphs. If \(q_U=|\nabla u|\) on
\(\partial U\), then

\[
\{u=t\}
=
\left\{
y-\frac{t}{q_U(y)}\nu_U(y)+O(t^{1+\gamma})
:\ y\in\partial U
\right\}.
\]

Third, the coarea quantities in the level-set identity have boundary traces:

\[
|\nabla u|\to q_U,\qquad
P(\{u>t\})\to P(U),
\qquad
|U\setminus\{u>t\}|
=t\int_{\partial U}q_U^{-1}+o(t).
\]

Fourth, the weighted Holder defect can be upgraded. The identity gives

\[
\int_{\{u=t\}}
\frac{(|\nabla u|-\bar f_t)^2}{|\nabla u|}
\]

and selected-minimizer regularity supplies uniform \(C^\gamma\) control of
\(|\nabla u|\) on \(\{u=t\}\). Interpolation can then turn this weighted
\(L^2\) defect into the stronger boundary norms required by known Serrin
stability mechanisms.

The resulting hybrid target is:

> For selected minimizers \(U\), prove a boundary-layer good-level theorem:
> there exists \(t\downarrow0\), with
> \(|U\setminus\{u>t\}|=O(|U|\delta_T(U)^{1/2})\), where \(\delta_T\) is the
> scale-invariant torsion deficit, such that the matched
> superlevel set \(\{u>t\}\) is a regular approximate Serrin domain and
> \[
> \mathcal A(U)^2
> \le
> C\left(
> \frac{D_I(t)+D_H(t)}{|U|^{2-2/n}}
> +\delta_T(U)
> \right).
> \]

This is the sharp-exponent version of the GGRT replacement strategy in the
torsion setting. It uses Plan 1 only for the regularity and boundary-layer
trace estimates; the quantitative deficit information still comes from the
Nicola--Tilli identity.
