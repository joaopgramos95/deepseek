# A Talenti--Nicola--Tilli Route Toward Sharp Faber--Krahn Stability

## 0. Context and guiding idea

This note records a possible second strategy for proving, or at least re-understanding, sharp quantitative stability in the Faber--Krahn inequality.

The target inequality is

\[
\lambda_1(\Omega)-\lambda_1(B) \gtrsim \mathcal A(\Omega)^2,
\]

after fixing volume, where \(B\) is the ball with \(|B|=|\Omega|\) and \(\mathcal A(\Omega)\) is the Fraenkel asymmetry.

The usual Talenti-style proof of Faber--Krahn uses rearrangement or level-set arguments. The note by João and collaborator gives a Nicola--Tilli-inspired proof of the torsional/Faber--Krahn inequality using:

1. coarea formula,
2. Hölder on level sets,
3. the divergence theorem,
4. the isoperimetric inequality for the superlevel sets,
5. a one-dimensional convexity argument.

The new proposed stability idea is:

> If the Faber--Krahn deficit is small, then not only are many level sets \(\{u=s\}\) almost isoperimetric, but also \(|\nabla u|\) should be almost constant along many level sets. This extra information may allow one to invoke stability of Serrin-type overdetermined problems on interior level sets and recover strong regularity/closeness-to-ball information.

Here \(u\) is either the torsion function

\[
-\Delta u=1,\qquad u=0\text{ on }\partial\Omega,
\]

or, after suitable modifications, the first eigenfunction

\[
-\Delta u=\lambda_1(\Omega)u,
\qquad u=0\text{ on }\partial\Omega.
\]

The note currently proves the torsional inequality, so the first natural version of this project should be formulated for torsion/Saint-Venant stability. One can then try to transfer the result to Faber--Krahn using the Brasco--De Philippis--Velichkov/Kohler--Jobin mechanism.

---

## 1. The level-set proof and where inequalities enter

Let \(u=u_\Omega\) solve

\[
\begin{cases}
-\Delta u=1 & \text{in }\Omega,\\
u=0 & \text{on }\partial\Omega.
\end{cases}
\]

For \(t>0\), write

\[
E_t := \{u>t\},
\qquad
m(t):=|E_t|.
\]

The note uses a rearranged variable \(s=m(t)\), with \(u^*(s)=m^{-1}(s)\), and defines

\[
I(s):=\int_{\{u>u^*(s)\}} u\,dx.
\]

The proof has two main inequalities on a regular level set \(\{u=t\}\):

### Step A: Hölder on the level set

\[
\mathcal H^{n-1}(\{u=t\})^2
\le
\left(\int_{\{u=t\}}\frac{1}{|\nabla u|}\,d\mathcal H^{n-1}\right)
\left(\int_{\{u=t\}}|\nabla u|\,d\mathcal H^{n-1}\right).
\]

By the coarea formula,

\[
- m'(t)=\int_{\{u=t\}}\frac{1}{|\nabla u|}\,d\mathcal H^{n-1}.
\]

By the divergence theorem,

\[
\int_{\{u=t\}}|\nabla u|\,d\mathcal H^{n-1}=|E_t|=m(t).
\]

Therefore

\[
\mathcal H^{n-1}(\{u=t\})^2
\le
-m'(t)m(t).
\]

### Step B: isoperimetry of the superlevel set

\[
n\omega_n^{1/n}m(t)^{\frac{n-1}{n}}
\le
\mathcal H^{n-1}(\{u=t\}).
\]

Combining A and B gives

\[
n^2\omega_n^{2/n}m(t)^{1-2/n}
\le
-m'(t).
\]

In the note's variable \(s=m(t)\), this becomes the differential inequality that drives convexity of a one-dimensional functional \(G\).

---

## 2. Equality conditions: two independent rigidity mechanisms

The proof contains two inequalities, and hence two equality mechanisms.

### 2.1 Equality in isoperimetry

Equality in Step B says that, for almost every level \(t\), the set

\[
E_t=\{u>t\}
\]

is a ball.

This is the classical Talenti-style rigidity mechanism: equality forces spherical superlevel sets.

### 2.2 Equality in Hölder

Equality in Step A says that the functions

\[
|\nabla u|^{1/2}
\quad\text{and}\quad
|\nabla u|^{-1/2}
\]

are proportional on \(\{u=t\}\). Equivalently,

\[
|\nabla u|\equiv c(t)
\quad\text{on }\{u=t\}.
\]

So the level-set proof contains an overdetermined condition:

\[
u=t \quad\text{and}\quad |\nabla u|=c(t)
\quad\text{on }\partial E_t.
\]

Since \(-\Delta u=1\) in \(E_t\), and \(u=t\) on \(\partial E_t\), the shifted function

\[
w_t:=u-t
\]

satisfies

\[
\begin{cases}
-\Delta w_t=1 & \text{in }E_t,\\
w_t=0 & \text{on }\partial E_t,\\
|\nabla w_t|=c(t) & \text{on }\partial E_t.
\end{cases}
\]

This is exactly a Serrin-type overdetermined problem on the interior domain \(E_t\).

Therefore, the level-set proof does not merely say that equality means level sets are isoperimetric. It says something stronger:

> Equality simultaneously forces isoperimetric equality and Serrin overdetermined equality on almost every superlevel set.

The proposed stability route is to exploit both pieces, not just the isoperimetric one.

---

## 3. Deficit decomposition suggested by the proof

The proof should be made quantitative by tracking the losses in the two inequalities.

For a regular level \(t\), define:

\[
P(t):=\mathcal H^{n-1}(\{u=t\}),
\qquad
M(t):=m(t)=|E_t|.
\]

The Hölder deficit on \(\{u=t\}\) is

\[
D_H(t)
:=
\left(\int_{\{u=t\}}\frac{1}{|\nabla u|}\right)
\left(\int_{\{u=t\}}|\nabla u|\right)
-
P(t)^2.
\]

Since

\[
\int_{\{u=t\}}|\nabla u|=M(t),
\]

this becomes

\[
D_H(t)=(-m'(t))M(t)-P(t)^2.
\]

The isoperimetric deficit of the level set is

\[
D_I(t):=P(t)^2-n^2\omega_n^{2/n}M(t)^{2(n-1)/n}.
\]

The total level-set deficit is then

\[
D_{\mathrm{level}}(t)
:=D_H(t)+D_I(t)
=
(-m'(t))M(t)-n^2\omega_n^{2/n}M(t)^{2(n-1)/n}.
\]

The one-dimensional differential inequality is precisely

\[
D_{\mathrm{level}}(t)\ge 0.
\]

A quantitative stability proof should first establish an integral estimate of the form

\[
\int_0^{\|u\|_\infty} W(t)D_{\mathrm{level}}(t)\,dt
\lesssim
\text{global Faber--Krahn/Saint-Venant deficit},
\]

for an appropriate weight \(W(t)\).

If such a bound is available, then for many levels \(t\), both \(D_I(t)\) and \(D_H(t)\) must be small.

---

## 4. What small Hölder deficit should imply

The Hölder deficit has a useful variance interpretation.

On \(\Sigma_t:=\{u=t\}\), let

\[
f:=|\nabla u|.
\]

Then

\[
\left(\int_{\Sigma_t} f\right)
\left(\int_{\Sigma_t} f^{-1}\right)-P(t)^2
\]

measures how far \(f\) is from being constant on \(\Sigma_t\).

One expects an estimate of the schematic form

\[
\inf_{c>0}\int_{\Sigma_t}\left|\frac{|\nabla u|}{c}-1\right|^2 d\mathcal H^{n-1}
\lesssim
\frac{D_H(t)}{P(t)^2},
\]

possibly under upper/lower bounds on \(|\nabla u|\).

Thus, if the global deficit is small, then for many good levels \(t\),

\[
|\nabla u|\approx c(t)
\quad\text{on }\Sigma_t.
\]

This is the new information beyond isoperimetric stability.

---

## 5. Good-level selection

The global deficit should imply the existence of many levels \(t\) such that:

1. \(E_t=\{u>t\}\) has controlled volume, not too small and not too close to \(|\Omega|\),
2. \(D_I(t)\) is small,
3. \(D_H(t)\) is small,
4. \(\Sigma_t\) is regular enough to apply geometric/PDE stability tools,
5. \(|\nabla u|\) has nondegenerate upper and lower bounds on \(\Sigma_t\).

For such a good level, \(w_t=u-t\) solves

\[
\begin{cases}
-\Delta w_t=1 & \text{in }E_t,\\
w_t=0 & \text{on }\partial E_t,
\end{cases}
\]

and additionally satisfies an approximate overdetermined condition:

\[
|\nabla w_t|\approx c(t)
\quad\text{on }\partial E_t.
\]

So \(E_t\) is an approximate Serrin domain.

---

## 6. Serrin stability input

Serrin's theorem says that if

\[
\begin{cases}
-\Delta w=1 & \text{in }D,\\
w=0 & \text{on }\partial D,\\
|\nabla w|=\text{constant} & \text{on }\partial D,
\end{cases}
\]

then \(D\) is a ball.

A stability version should say, roughly:

> If \(|\nabla w|\) is almost constant on \(\partial D\), then \(D\) is close to a ball.

For this project, the relevant domain is not \(\Omega\) itself, but an interior superlevel set \(E_t\). This is potentially advantageous: even if \(\partial\Omega\) is rough, the interior level sets of \(u\) may be better behaved.

The desired conclusion from Serrin stability is something like:

\[
\operatorname{dist}(E_t,B_t)
\lesssim
\operatorname{osc}_{\partial E_t}|\nabla w_t|
\]

or, more realistically,

\[
\mathcal A(E_t)
\lesssim
\left(\inf_c \| |\nabla w_t|-c\|_{L^2(\partial E_t)}\right)^\alpha,
\]

possibly with geometric assumptions such as uniform interior/exterior ball conditions, Lipschitz regularity, or smallness of the isoperimetric deficit.

The hope is that the combination of:

- small isoperimetric deficit of \(E_t\), and
- small oscillation/variance of \(|\nabla u|\) on \(\partial E_t\),

places \(E_t\) in a strong regularity class, maybe even a nearly spherical class.

---

## 7. From interior regularity back to \(\Omega\)

The delicate part is transferring information from \(E_t\) to the original domain \(\Omega\).

If \(t\) is small, then \(E_t\) lies only slightly inside \(\Omega\). One might hope that

\[
|\Omega\setminus E_t|
\]

is small, so closeness of \(E_t\) to a ball implies closeness of \(\Omega\) to a ball.

But small \(t\) is also where regularity may be weakest, since \(E_t\) approaches the original boundary.

This suggests a two-scale strategy:

1. Choose a level \(t>0\) small enough that \(E_t\) captures most of the volume of \(\Omega\).
2. But choose \(t\) large enough that \(\partial E_t\) is regular and Serrin stability applies.

The key estimate needed is a quantitative balance:

\[
|\Omega\setminus E_t| \ll \mathcal A(\Omega)
\]

while still having good control of \(D_H(t)\) and \(D_I(t)\).

If this can be done, then:

\[
\mathcal A(\Omega)
\lesssim
\mathcal A(E_t)+|\Omega\setminus E_t|.
\]

Thus sharp stability for \(E_t\) could imply sharp stability for \(\Omega\).

---

## 8. Possible direct route from the convexity gap

The note observes that the gap

\[
G'(|\Omega|)-\frac{G(|\Omega|)}{|\Omega|}
\ge 0
\]

should characterize stability.

A natural direction is to express this endpoint convexity gap as an integral of the second derivative measure of \(G\). Schematically,

\[
G'(|\Omega|)-\frac{G(|\Omega|)}{|\Omega|}
\sim
\int_0^{|\Omega|} K(s)\,dG''(s).
\]

But \(G''\ge0\) is exactly the one-dimensional version of the level-set deficit.

So the global deficit should control an averaged level-set deficit:

\[
\text{global deficit}
\sim
\int \text{level-set deficit}.
\]

Then one can try to convert the averaged information into:

1. existence of good levels,
2. approximate Serrin on those levels,
3. near-sphericity of those levels,
4. near-sphericity of \(\Omega\).

This would be a direct Talenti/Nicola--Tilli stability proof, avoiding the full selection-principle machinery.

---

## 9. Relation to Brasco--De Philippis--Velichkov

The Brasco--De Philippis--Velichkov proof obtains sharp Faber--Krahn stability by:

1. reducing to sharp quantitative Saint-Venant stability,
2. proving the torsional stability inequality via a selection principle,
3. using regularity/free-boundary arguments to reach the perturbative regime,
4. applying a local second-variation inequality near the ball.

The present idea could interact with that proof in two ways.

### Route A: Direct Talenti--Serrin proof

Use the level-set deficit decomposition to prove sharp stability directly.

This would require proving that the convexity gap controls enough good levels, and that good levels control the Fraenkel asymmetry of \(\Omega\).

### Route B: Improved selection principle

Use the level-set/Serrin information as an alternative way to regularize near-counterexamples.

Given a near-counterexample \(\Omega\), choose a good interior level \(E_t\). Then \(E_t\) is smoother, approximately Serrin, and still captures much of the asymmetry of \(\Omega\). One could use \(E_t\) as the selected smooth near-counterexample instead of solving an auxiliary penalized problem.

This would be very close in spirit to the BDV strategy, but the smoothing/regularization would come from the PDE level sets themselves.

---

## 10. Main mathematical obstacles

### Obstacle 1: torsion versus eigenvalue

The note is currently written for the torsion function \(-\Delta u=1\). Faber--Krahn is about \(\lambda_1\). The cleanest route is probably:

1. prove sharp stability for Saint-Venant/torsion using this method;
2. transfer to Faber--Krahn using known inequalities.

A direct eigenfunction version is possible but will change the divergence theorem identity. For eigenfunctions,

\[
-\Delta u=\lambda u,
\]

so

\[
\int_{\{u>t\}} -\Delta u
=
\lambda\int_{\{u>t\}} u,
\]

not simply \(|\{u>t\}|\). The one-dimensional structure becomes more complicated.

### Obstacle 2: good levels may not be close enough to \(\Omega\)

If one must go too far inside \(\Omega\) to find regular almost-Serrin levels, then \(E_t\) may lose too much volume/asymmetry information.

### Obstacle 3: Serrin stability requires hypotheses

Most stability versions of Serrin's theorem require some a priori regularity or geometric control on the domain. We must derive these assumptions from the level-set structure and small deficits, not assume them for free.

### Obstacle 4: sharp exponent bookkeeping

The final goal is the exponent \(2\):

\[
\delta(\Omega)\gtrsim\mathcal A(\Omega)^2.
\]

Any intermediate estimate with a bad power, for example

\[
\mathcal A(E_t)\lesssim D_H(t)^\alpha
\]

with the wrong \(\alpha\), may only recover non-sharp stability.

The project must track powers carefully.

### Obstacle 5: Hölder deficit gives variance, not oscillation

Small Hölder deficit naturally gives an \(L^2\)-type control of \(|\nabla u|\), not necessarily an \(L^\infty\) oscillation bound. Serrin stability inputs must therefore be compatible with integral norms, or one must upgrade the control using regularity.

---

## 11. First concrete lemmas to try

### Lemma 1: Quantitative Hölder deficit

For a regular level \(\Sigma_t=\{u=t\}\), prove

\[
\inf_{c>0}\int_{\Sigma_t}\left|\frac{|\nabla u|}{c}-1\right|^2
\lesssim
\frac{D_H(t)}{P(t)}
\]

under natural nondegeneracy assumptions.

This turns the loss in the coarea/Hölder step into an almost-overdetermined boundary condition.

### Lemma 2: Global deficit controls averaged level deficits

Show that the endpoint convexity gap in the Nicola--Tilli proof controls

\[
\int W(t)\big(D_H(t)+D_I(t)\big)\,dt.
\]

This is the bridge from global near-optimality to many good levels.

### Lemma 3: Good-level extraction

Given small global deficit, find a level \(t\) such that:

\[
D_H(t)+D_I(t)\text{ is small},
\]

\[
|\Omega\setminus E_t|\text{ is controlled},
\]

and \(E_t\) is geometrically admissible.

### Lemma 4: Serrin stability for good levels

For such \(E_t\), use approximate constancy of \(|\nabla u|\) on \(\partial E_t\) to prove that \(E_t\) is close to a ball.

The desired form is:

\[
\mathcal A(E_t)^2
\lesssim
D_H(t)+D_I(t).
\]

### Lemma 5: Transfer from \(E_t\) to \(\Omega\)

Prove

\[
\mathcal A(\Omega)
\lesssim
\mathcal A(E_t)+|\Omega\setminus E_t|.
\]

Then combine with the previous estimates.

---

## 12. Possible final theorem shape

A plausible theorem to aim for is:

**Theorem.** Let \(\Omega\subset\mathbb R^n\) be a bounded domain with \(|\Omega|=|B|\). Let \(u\) be the torsion function. Suppose the Saint-Venant deficit is small. Then there exists a level \(t>0\) such that \(E_t=\{u>t\}\) satisfies:

1. \(|\Omega\setminus E_t|\) is small compared to the global deficit,
2. \(E_t\) is close to a ball in Fraenkel asymmetry,
3. \(\partial E_t\) is quantitatively regular,
4. \(|\nabla u|\) is almost constant on \(\partial E_t\).

Consequently,

\[
\delta_E(\Omega)
\gtrsim
\mathcal A(\Omega)^2.
\]

Then use the Kohler--Jobin/BDV transfer to obtain the sharp quantitative Faber--Krahn inequality.

---

## 13. Sanity checks

### Sanity check 1: equality case

For a ball, the torsion function is radial:

\[
u_B(x)=\frac{R^2-|x|^2}{2n}.
\]

Every level set is a sphere, and \(|\nabla u_B|=|x|/n\) is constant on each level set. Thus both the isoperimetric deficit and the Hölder deficit vanish level-by-level.

This exactly matches the proposed mechanism.

### Sanity check 2: why this could improve over pure isoperimetry

A stability proof based only on the isoperimetric inequality of level sets may lose sharpness because it only knows that many level sets are almost balls in measure.

The additional condition

\[
|\nabla u|\approx c(t)\quad\text{on }\{u=t\}
\]

is PDE information. It says the level set is not just geometrically near optimal, but also almost satisfies an overdetermined boundary condition. This should be much more rigid.

### Sanity check 3: likely best formulation

Do not try first to prove sharp Faber--Krahn stability directly for the eigenfunction.

The cleanest path is:

1. use the note's torsion proof;
2. quantify the level-set deficits;
3. prove sharp Saint-Venant stability;
4. transfer to Faber--Krahn.

### Sanity check 4: dangerous point

The hardest step is probably not proving that small Hölder deficit means \(|\nabla u|\) is almost constant. That is relatively plausible.

The hard step is using this information on interior level sets to control the original exterior domain \(\Omega\) with the sharp exponent.

---

## 14. Agent task list

### Agent 1: Extract the exact deficit identity from the convexity proof

Starting from the note's function

\[
G(s)=I(s)+\frac{s^{1+2/n}}{(4+2n)\omega_n^{2/n}},
\]

compute exactly how

\[
G'(|\Omega|)-\frac{G(|\Omega|)}{|\Omega|}
\]

can be represented as an integral of the level-set deficit.

Goal: identify the exact weight \(W(s)\) or \(W(t)\).

### Agent 2: Quantify the Hölder step

Prove a sharp or near-sharp relation between

\[
\left(\int_{\Sigma} f\right)
\left(\int_{\Sigma} f^{-1}\right)-|\Sigma|^2
\]

and the distance of \(f\) from the constants.

Specialize to \(f=|\nabla u|\) on \(\Sigma=\{u=t\}\).

### Agent 3: Survey Serrin stability theorems

Find stability results for Serrin's overdetermined problem, especially those using:

- \(L^2(\partial D)\) control of \(\partial_\nu w-c\),
- oscillation control of \(\partial_\nu w\),
- integral identities involving the torsion function,
- assumptions compatible with level sets of solutions.

Determine what regularity assumptions are needed.

### Agent 4: Good-level extraction

Given an averaged bound on \(D_H(t)+D_I(t)\), prove there exists a level \(t\) such that:

- the level deficit is small,
- \(|\Omega\setminus E_t|\) is small,
- \(E_t\) has enough regularity/nondegeneracy.

### Agent 5: Transfer asymmetry from interior level set to original domain

Prove inequalities of the form

\[
\mathcal A(\Omega)
\le
C\mathcal A(E_t)+C|\Omega\setminus E_t|.
\]

Optimize the choice of \(t\) to preserve the sharp exponent.

### Agent 6: Compare with BDV selection principle

Investigate whether the map

\[
\Omega\mapsto E_t=\{u>t\}
\]

can replace, or supplement, the penalized selection principle in BDV.

The target is to show that selected level sets satisfy

\[
Q(E_t)\lesssim Q(\Omega),
\]

where

\[
Q(D)=\frac{\delta_E(D)}{\mathcal A(D)^2}.
\]

---

## 15. One-sentence summary

The proposed strategy is to quantify every loss in the Nicola--Tilli/Talenti level-set proof, especially the Hölder loss, in order to show that near equality forces many interior level sets to be approximate Serrin domains; stability of Serrin's overdetermined problem may then convert this PDE rigidity into smooth near-sphericity and ultimately sharp Faber--Krahn stability.
