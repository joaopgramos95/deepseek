# FJ Attack: An Intrinsic Geometric Proof Programme

## 0. Purpose and verdict

The target is the normal-oscillation form of the Fusco--Julin theorem.  After
normalising \(|E|=|B_1|=\omega_n\), define
\[
  D(E):=P(E)-P(B_1),
  \qquad
  I_z(E):=\int_E\frac{dx}{|x-z|},
\]
\[
  {\cal B}_z(E)
  :=\frac12\int_{\partial^*E}
       \left|\nu_E(x)-\frac{x-z}{|x-z|}\right|^2\,d{\cal H}^{n-1}(x),
  \qquad
  \beta(E)^2:=\inf_z{\cal B}_z(E).
\]
We seek an intrinsic proof of
\[
  \beta(E)^2\le C_n D(E)                                      \tag{FJ}
\]
for every finite-perimeter set \(E\), with \(C_n\) computable from the proof.
The point of this programme is not to replace the completed computable
regularised-selection proof in `Sharp Faber-Krahn Manuscript/FJ_quantitative_attempts.tex`.
It is to find a proof which explains the geometry: how perimeter deficit pays
for both deformation of sections and motion of their centres.

**Current best strategy.**  The primary route should be an *oriented
Fusco--Maggi--Pratelli symmetrisation proof*: adapt the reflection-and-slicing
proof of the sharp quantitative isoperimetric inequality, replacing volume
asymmetry by \({\cal B}_z\).  The missing mechanism is a coherent-centre
lemma.  It should retain both reflected siblings, and during intermediate
reflection steps two orthogonal median cuts, until their approximate ball
centres have been compared.  This is the exact place where the
Figalli--van Hintum--Tiba level-gluing philosophy is relevant.

The earlier attempt to track one chosen descendant about one frozen radial
centre is useful but is not the recommended high-dimensional attack.  Once
one sibling is discarded, the information explaining an axial displacement
can be lost.  A translated ball is the warning example: it has zero deficit,
but its radial potential changes strictly when evaluated at a displaced
centre.

Optimal transport and Brunn--Minkowski stability should be run as sharply
specified auxiliary investigations, not asserted as complete solutions.
Figalli--Maggi--Pratelli transport already supplies an effective ordinary
quantitative isoperimetric input and a boundary direction associated with the
Brenier map.  What it does not currently supply is the required comparison of
that direction to a radial field about one centre.  The recent
Figalli--van Hintum--Tiba work supplies a model for gluing translations from
overlapping pieces; it does not itself estimate boundary normal oscillation.

## 1. Non-negotiable proof standard

Any agent working on this programme must observe the following rules.

1. Every claimed lemma must state its hypotheses, normalisation, dependence of
   constants, and whether it is proved, conditional, or conjectural.
2. Computability is sufficient: a constant may be represented as a finite
   composition of dimensional constants from proved inequalities.  A decimal
   evaluation is not required.
3. No proof of (FJ) may invoke the Fusco--Julin main inequality, even for
   reflected children or slices.
4. Ordinary sharp quantitative isoperimetry is allowed as a weaker,
   independent input.  Prefer the effective mass-transport theorem of
   Figalli--Maggi--Pratelli (2010), rather than a compactness-only version.
5. The elementary radial-potential rearrangement comparison may be reproved
   and used.  It is not circular.
6. A claim that transport, Brunn--Minkowski, Sobolev stability, or
   symmetrisation controls \({\cal B}_z\) is not admissible without a displayed
   lemma proving the same-centre boundary-normal estimate.
7. The final manuscript must remain readable without leaving calculations to
   the reader.  In particular, all centre changes and all boundary portions
   erased by reflection must be accounted for explicitly.

## 2. Exact structural identity

For unit volume the radial Gauss--Green formula gives
\[
  {\cal B}_z(E)=P(E)-(n-1)I_z(E).                             \tag{2.1}
\]
Since
\[
  (n-1)I_z(B_1(z))=P(B_1),
\]
we have
\[
  {\cal B}_z(E)
  =D(E)+(n-1)\{I_z(B_1(z))-I_z(E)\}.                          \tag{2.2}
\]
Both terms in (2.2) are nonnegative.  The second is the
same-centre radial displacement defect.  This identity is the reason that
ordinary Fraenkel-asymmetry control is insufficient by itself: it sees the
amount of displaced mass, while (2.2) requires the perimeter to pay for how
that displacement lowers radial potential about the same centre.

An elementary comparison which should be stated and proved near the start of
any intrinsic proof is:
\[
  |E\mathbin{\triangle}B_1(z)|^2
  \le c_n\{I_z(B_1(z))-I_z(E)\}
  \le \frac{c_n}{n-1}{\cal B}_z(E).                          \tag{2.3}
\]
The proof is a bathtub/rearrangement argument: for fixed removed and added
volume, the smallest loss of the decreasing kernel \(|x-z|^{-1}\) occurs by
exchanging adjacent spherical shells.  Formula (2.3) converts a small
oriented cost about \(z\) into closeness to the *same* ball \(B_1(z)\);
it must not be confused with (FJ).

## 3. Results already established in the current manuscript

The following are proved in the intrinsic section of
`Sharp Faber-Krahn Manuscript/FJ_quantitative_attempts.tex` and should be
treated as available inputs.

### 3.1 Centred reflection identity

If a hyperplane \(H\) contains \(q\), bisects \(G\), and \(G^+\), \(G^-\) are
obtained by reflecting each half across \(H\), then
\[
  D(G^+)+D(G^-)=2D(G)-2P(G;H),                               \tag{3.1}
\]
\[
  {\cal B}_q(G^+)+{\cal B}_q(G^-)
  =2{\cal B}_q(G)-2P(G;H).                                  \tag{3.2}
\]
In particular,
\[
  P(G;H)\le D(G),
\]
and one child satisfies
\[
  D(G^s)\le2D(G),\qquad
  {\cal B}_q(G^s)\ge {\cal B}_q(G)-D(G).                      \tag{3.3}
\]
The facet erased by reflection is therefore paid for exactly by deficit.

### 3.2 Fixed-centre transverse symmetry reduction

Starting at any \(q\), centred bisections can be iterated through \(n-1\)
orthogonal planes containing \(q\).  The output \(F\) is symmetric with
respect to those \(n-1\) planes and satisfies
\[
  D(F)\le2^{n-1}D(E),\qquad
  {\cal B}_q(E)\le{\cal B}_q(F)+(2^{n-1}-1)D(E).              \tag{3.4}
\]
The iteration stops at \(n-1\), because in the residual one-dimensional
normal space oddness no longer forces a bisecting plane through \(q\).

### 3.3 The exact last-axis obstruction

If \(q\) is retained in (3.4), \(L\) is the residual symmetry axis, and
\(c\in L\) is the intersection with the final axial median plane, then the
centred-reflection approach closes if one proves
\[
  (n-1)\{I_c(F)-I_q(F)\}\le K_nD(E).                         \tag{3.5}
\]
This is a correct sufficient condition, but it is not the preferred
high-dimensional target: the particular selected descendant \(F\) may have
forgotten the sibling data needed to prove (3.5).

### 3.4 Dimension two

Every finite planar mass which vanishes on lines, in particular the
Lebesgue measure restricted to a measurable set, admits a quadrisection by
two perpendicular lines.  Reflecting one quadrant gives a two-symmetric set
\(F\) with
\[
  D(F)\le4D(E),\qquad
  \beta(E)^2\le{\cal B}_0(F)+D(E),                           \tag{3.6}
\]
after translation.  Thus the *oriented symmetry-reduction step* is proved in
dimension two.  The planar intrinsic proof of (FJ) is not complete: it still
requires the symmetric closure described in Section 7 below.

### 3.5 Why orthogonal equipartition is not the general solution

Maldonado and Roldan-Pensado prove that for every \(n\ge3\) there are masses
which cannot be split into \(2^n\) equal pieces by \(n\) mutually orthogonal
hyperplanes.  Therefore the planar quadrisection shortcut cannot be used as
the high-dimensional proof of full centred symmetry.

### 3.6 Transverse symmetrisation and meridian action

Writing \(x=(s,y)\), let \(E^\sharp\) replace each transverse slice
\(E_s\subset\mathbb R^{n-1}\) by a centred \((n-1)\)-ball of the same
measure.  Then
\[
  I_0(E)\le I_0(E^\sharp),\qquad P(E^\sharp)\le P(E),
\]
and
\[
  {\cal B}_0(E)-{\cal B}_0(E^\sharp)
  =[P(E)-P(E^\sharp)]
   +(n-1)[I_0(E^\sharp)-I_0(E)]\ge0.                         \tag{3.7}
\]
Thus symmetrisation discards part of the oriented cost.  The discarded
quantity must be estimated, not ignored.

For an axially symmetric set
\[
  F=\{(s,y): |y|<r(s)\}
\]
the exact one-dimensional action is
\[
  {\cal B}_0(F)=\sigma_{n-2}\int r^{n-2}
  \left[
    \sqrt{1+(r')^2}
    -\frac{r-sr'}{\sqrt{s^2+r^2}}
  \right]\,ds.                                               \tag{3.8}
\]
Its integrand is nonnegative and vanishes exactly on circular arcs centred at
the origin.  This is the geometric endpoint of the proposed proof.

## 4. Why the primary route must change from the first attempt

Tracking \({\cal B}_q\) under planes through a fixed \(q\) is exact, but it is
not stable under the last required axial median.  The problem is not a
technical loss: it is an information loss.

The decisive model is \(G=B_1(ae_1)\) with \(q=0\) and \(a\ne0\).  Then
\[
  D(G)=0,\qquad {\cal B}_{ae_1}(G)=0,\qquad {\cal B}_0(G)>0.
\]
Consequently no estimate of the form
\[
  I_c(G)-I_q(G)\le C_nD(G)
\]
can hold for an arbitrary transversely symmetric descendant.  A proof of
(3.5), if true for descendants created from \(E\), has to use the genealogy
of the reflection process and not only the final set.

The FMP proof already contains the correct cure for the analogous volume
problem.  It does not follow one arbitrary half.  At each intermediate stage
it considers four reflected candidates obtained from two orthogonal median
planes.  If neither cut retained a large asymmetry, the shifted half-ball
models would be incompatible on their overlap.  This is Lemma 2.5 of FMP,
built on their shifted half-ball Lemma 2.4.

For the oriented problem, the corresponding comparison must be made for
radial-potential centres and oriented costs, not merely for symmetric
difference.  This is the central new work package.

## 5. Primary high-dimensional target: oriented FMP reduction

### 5.1 Set-up for a reflection generation

Suppose \(A\) already has \(k\) mutually orthogonal reflection symmetries
through affine hyperplanes \(H_1,\ldots,H_k\), with \(0\le k\le n-2\).
Choose two orthogonal directions perpendicular to the previous symmetry
directions.  Let \(K_1,K_2\) be median hyperplanes for \(A\) with these
normals.  Reflect each of the two halves cut by each \(K_i\), obtaining four
children
\[
  A_i^+,\ A_i^-,\qquad i=1,2.
\]
Each child retains the previous \(k\) symmetries and gains reflection
symmetry across its new median plane.  The elementary perimeter argument
gives
\[
  D(A_i^\pm)\le2D(A).                                       \tag{5.1}
\]

### 5.2 Oriented two-plane reflection lemma (main missing lemma)

The first principal theorem to prove is:

**Lemma OFR\((n,k)\) (oriented FMP reflection).**  There are computable
constants \(\delta_n>0\) and \(C_n<\infty\) such that, if
\(|A|=\omega_n\), \(D(A)\le\delta_n\), and \(A\) has the \(k\) prior
symmetries above, then its four children satisfy
\[
  \beta(A)^2
  \le C_n D(A)+C_n\max_{i\in\{1,2\},\,s\in\{+,-\}}
                         \beta(A_i^s)^2.                    \tag{OFR}
\]
The constants must not depend on \(A\), the selected median locations, or
an unrecorded compactness modulus.

This formulation permits the child with the largest oriented obstruction to
be retained.  It is the analogue of the selection in FMP Lemma 2.5.

### 5.3 Terminal one-plane reflection lemma

After \(n-1\) successful generations, the parent \(A\) has \(n-1\)
orthogonal symmetries, whose intersection is an axis \(L\).  Let \(K_n\) be
the median hyperplane orthogonal to \(L\), and let \(q=K_n\cap L\).  Reflect
its two halves to obtain \(A^+\) and \(A^-\), which are fully \(n\)-symmetric
about \(q\).

The final lemma required is:
\[
  \beta(A)^2
  \le C_nD(A)+C_n\max\{\beta(A^+)^2,\beta(A^-)^2\}.           \tag{TERM}
\]
Unlike (OFR), (TERM) should not require a second unused direction.  Each
child is fully symmetric about \(q\); the centre-localisation lemma in
Section 6.2 below must show that its near-optimal radial centre can be
replaced by \(q\) at quadratic cost.  Then (3.2), used with the centre
\(q\) and the median plane \(K_n\), glues the two children back to the
parent.

### 5.4 Consequence of OFR and TERM

Iterate (OFR) for \(k=0,\ldots,n-2\), always retaining a child achieving the
maximum in the displayed estimate, then apply (TERM).  The resulting
fully \(n\)-symmetric set \(F\), with symmetry centre translated to \(0\),
satisfies
\[
  D(F)\le2^nD(E),\qquad
  \beta(E)^2\le C_n\{D(E)+\beta(F)^2\}.                      \tag{5.2}
\]
All constants are computable once OFR and TERM are proved with computable
constants.  For \(D(E)>\delta_n/2^n\), the estimate is elementary since
\(\beta(E)^2\le P(E)=P(B_1)+D(E)\); hence only the small-deficit branch is
substantive.

## 6. Proof architecture for the oriented reflection lemmas

This section records the exact subordinate lemmas.  An agent should not try
to prove (OFR) in one unstructured computation: each item below is a
separate deliverable.

### 6.1 Same-centre ball comparison

**Lemma C1 (potential to same-centre volume).**  For
\(|A|=|B_\rho|\), prove (2.3) (when \(\rho=1\)), with a written constant
\(c_n\).  More generally, record its radius-\(\rho\) scaling:
\[
  \rho^{-n-1}|A\mathbin{\triangle}B_\rho(z)|^2
  \le c_n\left\{
    P(B_\rho)-(n-1)\int_A|x-z|^{-1}\,dx
  \right\}.                                                  \tag{C1}
\]

**Use.**  If \(z\) realises or nearly realises \(\beta(A_i^s)\), then
\(A_i^s\) is close in measure to the ball centred at that *same* \(z\).
This is what permits centre geometry to be extracted without invoking (FJ).

**Do not use instead.**  Ordinary Fraenkel asymmetry alone gives a nearby
ball, but it does not connect its centre to the centre entering the
oriented cost.

### 6.2 Symmetry localises an approximate radial centre

**Lemma C2 (centre near the symmetry flat).**  Let \(G\) be invariant under
reflections across mutually orthogonal hyperplanes
\(H_1,\ldots,H_m\), and put \(L=\cap_{j=1}^mH_j\).  If
\[
  |G\mathbin{\triangle}B_1(z)|\le\varepsilon
\]
with \(\varepsilon\) below an explicit dimensional threshold, prove
\[
  \operatorname{dist}(z,L)
  \le C_n\varepsilon.                                       \tag{C2a}
\]
Equivalently, by (C1), if \(z\) is a \(\beta\)-centre then
\[
  \operatorname{dist}(z,L)^2
  \le C_n\beta(G)^2.                                        \tag{C2b}
\]

**Proof model.**  Since \(G=R_jG\),
\[
  |B_1(z)\mathbin{\triangle}B_1(R_jz)|
  \le2|G\mathbin{\triangle}B_1(z)|.
\]
For small displacement, symmetric difference of two unit balls bounds their
centre distance from below.  Apply this for each reflection and sum the
orthogonal components.

**Important warning.**  Do not assert that a potential maximiser of an
arbitrary symmetric set lies on \(L\).  A multi-lobed symmetric set can have
off-flat maximisers.  Lemma C2 uses closeness to one ball, not an unsupported
concavity claim.

### 6.3 Quadratic recentering of oriented cost

**Lemma C3 (recentring near a symmetry flat).**  Under the hypotheses of C2,
let \(\bar z\) be the orthogonal projection of \(z\) onto \(L\).  Establish a
form of
\[
  {\cal B}_{\bar z}(G)
  \le C_n\bigl\{{\cal B}_z(G)+|z-\bar z|^2+D(G)\bigr\}.       \tag{C3}
\]
For a fully \(n\)-symmetric child, \(L=\{q\}\), and this becomes the
required estimate at its geometric symmetry centre.

**Why this is delicate.**  Estimating
\(|\,|x-z|^{-1}-|x-\bar z|^{-1}|\) by a crude Lipschitz bound near the
centre loses the required quadratic order.  The proof must use one of:

1. the cancellation and quadratic centre loss for an exact ball, plus a
   controlled error term using (C1);
2. a direct layer-cake/rearrangement comparison of potentials;
3. a counterexample showing that C3 needs an additional hypothesis, followed
   by a corrected statement.

An agent claiming C3 must explicitly test a ball plus a small remote
satellite, a ball with a narrow inward cavity, and a two-lobed symmetric set.

### 6.4 Compatibility of sibling and transverse centres

For one median plane \(K\), the two children can be modelled by balls whose
centres lie close to \(K\) after C2.  Gluing these models back produces a
union of two half-balls whose two centres may differ by a vector parallel to
\(K\).  One median direction alone does not force this mismatch to be small.

**Lemma C4 (two-plane centre compatibility).**  In the setting of (OFR),
assume that all four child costs satisfy
\[
  \max_{i,s}\beta(A_i^s)^2\le\varepsilon
\]
and \(D(A)\le\delta_n\).  Construct projected child centres on their median
planes using C2.  Prove that the broken-ball models associated with the two
orthogonal median cuts have mutually compatible centres:
\[
  \max\{\text{all required centre mismatch squares}\}
  \le C_n\{D(A)+\varepsilon\}.                               \tag{C4}
\]

**Required geometric core.**  Reprove, in the notation needed here, the
shifted half-ball comparison underlying FMP Lemma 2.4: if two unions of
half-balls associated with orthogonal cuts are close on common quadrants,
then their parallel shifts are controlled by their symmetric difference.
The overlap must have a displayed positive volume lower bound.  Do not cite
``overlap'' without specifying which quadrant carries it and how its mass is
bounded below.

**Connection to recent work.**  This is the finite-family analogue of the
Figalli--van Hintum--Tiba gluing step: local comparison objects initially
come with independent translations; an overlapping core forces their
translations to agree.  Here the overlapping objects are reflected
half-ball models, rather than function level sets.

### 6.5 Oriented gluing back to the parent

**Lemma C5 (common-centre oriented gluing).**  Assuming C1--C4, construct a
single point \(z_A\) such that
\[
  {\cal B}_{z_A}(A)
  \le C_n\left\{D(A)+\max_{i,s}\beta(A_i^s)^2\right\}.       \tag{C5}
\]
This proves (OFR), because \(\beta(A)^2\le{\cal B}_{z_A}(A)\).

The proof should be organised cut by cut:

1. Choose the median direction for which C4 supplies compatible sibling
   centres.
2. Replace each sibling centre by the common projected centre using C3.
3. Because this centre lies on the reflecting median plane, the radial kernel
   and radial field are invariant under reflection.
4. Use the exact centred reflection identity for the two siblings and charge
   the erased median facet to \(D(A)\).

This is the point at which retaining both siblings matters.  A proof which
chooses one reflected child before Step 2 has discarded the datum needed for
the gluing.

### 6.6 Proof of the terminal step

For (TERM), C2 and C3 apply to the two fully symmetric final children with
the same point \(q\), the intersection of all symmetry planes.  Thus
\[
  {\cal B}_q(A^\pm)
  \le C_n\{\beta(A^\pm)^2+D(A^\pm)\}.
\]
Apply the exact centred reflection identity across the final median plane:
\[
  2{\cal B}_q(A)
  ={\cal B}_q(A^+)+{\cal B}_q(A^-)+2P(A;K_n).
\]
Use \(P(A;K_n)\le D(A)\) and \(D(A^\pm)\le2D(A)\) to obtain (TERM).
This argument should be written before any attempt at the more involved C4,
because it verifies that the terminal obstruction is genuinely resolved once
fully symmetric children are available.

## 7. Symmetric closure: from an \(n\)-symmetric set to a ball

Once (5.2) is obtained, the remaining theorem is:
\[
  \text{If \(F\) is \(n\)-symmetric about \(0\), then }
  {\cal B}_0(F)\le C_nD(F).                                 \tag{SC}
\]
Since \(\beta(F)^2\le{\cal B}_0(F)\), this closes (FJ).  Full symmetry is
essential here: it removes the translated-ball zero mode geometrically.

The correct analogue of the FMP slicing induction has two parts.

### 7.1 Oriented transverse slice-motion lemma

Let \(F^\sharp\) be transverse Schwarz symmetrisation about the \(x_1\)-axis.
The needed estimate is
\[
  {\cal B}_0(F)-{\cal B}_0(F^\sharp)
  \le C_n\{P(F)-P(F^\sharp)\}.                               \tag{SM}
\]
The identity (3.7) proves only that the left side is nonnegative.  Lemma
(SM) says that the perimeter lost in centring the sections pays not merely
for volume asymmetry of sections but for their discarded *oriented* defect.

**How to attempt (SM).**

1. Start with smooth sets satisfying the nonvertical-boundary condition used
   in FMP Section 3; defer BV approximation until the formula is correct.
2. Write the boundary by slices.  Compute the full radial-normal integrand
   before applying any inequality.  It has a transverse angular component and
   a longitudinal velocity component.
3. Identify the weighted lower-dimensional oriented cost of a slice
   \(F_s\).  The weight depends on \(s\) and \(|y|\); on a fixed central strip
   it is comparable to a dimensional constant.
4. On the central strip apply the already established
   \((n-1)\)-dimensional symmetric closure, with the slice centre fixed at
   the origin by the inherited coordinate symmetries.
5. Treat polar slices by the same type of cap estimate used in FMP: for
   small global deficit, the ordinary effective quantitative isoperimetric
   inequality locates most mass near the unit ball, while excessive polar
   contribution is itself charged to perimeter deficit.
6. Pass to finite-perimeter sets by the slicing and lower-semicontinuity
   framework, displaying where vertical facets are removed or approximated.

This makes (SC) an induction on dimension, just as the FMP proof is an
induction for volume asymmetry.  The required base case is \(n=2\).

### 7.2 Axial meridian lemma

For \(F^\sharp=\{(s,y):|y|<r(s)\}\), full symmetry implies
\(r(s)=r(-s)\) after choosing the \(x_1\)-axis.  The target is
\[
  {\cal B}_0(F^\sharp)
  \le C_n\{P(F^\sharp)-P(B_1)\}.                             \tag{MA}
\]
Use the exact action (3.8), not a statement of qualitative compactness.

**Proposed proof decomposition for (MA).**

1. Dispose of \(D(F^\sharp)\ge\delta_n\) by
   \({\cal B}_0(F^\sharp)\le P(F^\sharp)\).
2. In the small-deficit branch, use effective ordinary isoperimetry and
   evenness to select a central interval on which the reference ball profile
   \(\rho(s)=\sqrt{1-s^2}\) is bounded below and \(r\) carries the relevant
   mass.
3. On that central interval rewrite the bracket in (3.8) as the squared
   angular mismatch between the generating normal
   \((-r',1)/\sqrt{1+(r')^2}\) and the radial direction
   \((s,r)/\sqrt{s^2+r^2}\).  Establish its comparison with the coercive
   profile energy measuring \(r-\rho\) and \(r'-\rho'\).
4. Use the volume constraint to remove the constant profile mode and the
   even symmetry \(r(s)=r(-s)\) to remove the axial translation mode.
5. Bound the contribution outside the central interval by the perimeter paid
   in creating or moving polar caps.  This is where the central-strip
   machinery in FMP Section 4 should be imitated, with (3.8) carried through
   each estimate.
6. Prove approximation from admissible \(W^{1,1}\) profiles to arbitrary
   axially symmetric finite-perimeter sets.

### 7.3 The planar proving ground

In \(n=2\), the symmetry-reduction step (3.6) is already proved.  The first
substantive target should therefore be:
\[
  {\cal B}_0(F)\le C_2D(F)
  \quad\text{for a set symmetric about two perpendicular axes}.              \tag{P2}
\]
Here transverse slices are one-dimensional, so the slice-shape part reduces
to counting intervals and paying for extra boundary points; the meridian
part is an even planar profile calculation.  A complete proof of (P2) would
finish the intrinsic proof in the plane and test every centre and cap issue
before the higher-dimensional induction is attempted.

## 8. Precise role of transport theory

The relevant transport paper is by **Figalli--Maggi--Pratelli**, not
``Ratelli''.  For \(K=B_1\) and \(|E|=|B_1|\), let \(T\) be the Brenier map
transporting \(E\) to \(B_1\).  Their Gromov-type proof, read in the Euclidean
case, yields a boundary trace \(\operatorname{tr}_E(T)\in\overline{B_1}\)
and the deficit chain implies
\[
  D(E)\ge
  \int_{\partial^*E}
       \bigl(1-\operatorname{tr}_E(T)\cdot\nu_E\bigr)\,
       d{\cal H}^{n-1}.                                    \tag{8.1}
\]
Consequently, as an elementary inference from
\(|\operatorname{tr}_E(T)|\le1\),
\[
  \frac12\int_{\partial^*E}
       |\nu_E-\operatorname{tr}_E(T)|^2\,d{\cal H}^{n-1}
  \le D(E).                                                  \tag{8.2}
\]
This is already an oriented statement, but its comparison direction is the
Brenier boundary trace, not the radial vector field \(e_z\).

The missing transport theorem is therefore exactly:
\[
  \inf_{z\in\mathbb R^n}
  \int_{\partial^*E}
     |\operatorname{tr}_E(T)-e_z|^2\,d{\cal H}^{n-1}
  \le C_nD(E).                                               \tag{TR}
\]
If (TR) holds, then (8.2) and the triangle inequality immediately prove
(FJ).  Conversely, no statement that transport gives an intrinsic FJ proof
is justified until (TR), or a valid replacement, is proved.

**Transport work package.**

1. Reproduce (8.1)--(8.2) rigorously from the finite-perimeter trace
   formulation in Figalli--Maggi--Pratelli.
2. Test (TR) first on radial graphs, convex sets, and axially symmetric
   profiles, where the Brenier map has additional structure.
3. Identify whether the FMP controls
   \(\int_E|\nabla T-\mathrm{Id}|\) and their boundary \(L^1\) trace estimate
   can ever yield the boundary \(L^2\) estimate in (TR) without added
   regularity.  A mere \(L^1\)-to-\(L^2\) interpolation generally loses the
   sharp \(D(E)\) order.
4. If (TR) succeeds only in the \(n\)-symmetric or axial class, use it as an
   alternative proof of (SC) or (MA), not as a global reduction.
5. If it fails on a concrete finite-perimeter example, record that
   counterexample: it would justify definitively keeping transport only as
   the effective ordinary-isoperimetry input.

At present transport is best used unconditionally for the computable weaker
input
\[
  \alpha(E)^2\le C_n^{\rm FMP}D(E),                          \tag{8.3}
\]
needed to obtain ball-scale localisation in small-deficit branches.  It
should not be asked to solve centre-motion before (TR) is understood.

## 9. Precise role of recent Brunn--Minkowski and Prekopa--Leindler stability

Figalli--van Hintum--Tiba prove sharp stability for Brunn--Minkowski on
arbitrary sets and then sharp stability for Prekopa--Leindler and
Borell--Brascamp--Lieb.  The feature relevant here is their proof
architecture: translations are obtained for comparison objects on different
level or truncation ranges, and substantial overlap forces these translations
to be compatible before the ranges are glued.

This is not a black-box proof of (FJ), because their conclusions concern
volume or functional closeness, not boundary normal direction.  Its proper
use is concrete:

1. In C4, regard the half-ball models created by different median cuts as
   local comparison objects carrying initially independent translations.
2. Use a common quadrant of two orthogonal cuts as the analogue of an
   overlapping level range.
3. Establish a quantitative anchoring estimate: a unit ball segment of
   volume bounded below cannot be nearly invariant under a translation larger
   than its symmetric-difference error.
4. Glue the resulting centre data before evaluating radial potentials.

There is also an experimental outer-parallel-set route.  For sufficiently
regular \(E\),
\[
  \left.\frac{d}{dt}\right|_{t=0^+}|E+tB_1|=P(E).            \tag{9.1}
\]
Thus an oriented first-variation refinement of sharp Brunn--Minkowski
stability would be relevant.  The required new statement would have to
control
\[
  \inf_z\int_{\partial^*E}|\nu_E-e_z|^2
\]
by the first variation of the Brunn--Minkowski gap at \(t=0\).  Such a
statement is not supplied by current BM stability, and differentiating a
volume-closeness estimate does not produce it automatically.  Agents may
investigate this route only as:

**Lemma BM-ORIENT (experimental).**  Formulate a regularity class for which
an oriented first-variation estimate is meaningful; prove it there or
produce a counterexample.  Do not import it into the main proof unless the
boundary-normal estimate is proved with computable constants.

## 10. Sobolev equivalence: diagnostic only

The \(BV\)-Sobolev equivalence gives a genuine integrated level-set splitting.
For \(q=n/(n-1)\) and nonnegative compactly supported \(f\in BV\), coarea and
Minkowski yield
\[
\begin{aligned}
 |Df|(\mathbb R^n)-n\omega_n^{1/n}\|f\|_{L^q}
 &=
 \int_0^\infty
 \{P(\{f>t\})-n\omega_n^{1/n}|\{f>t\}|^{(n-1)/n}\}\,dt\\
 &\quad+
 n\omega_n^{1/n}
 \left\{
 \int_0^\infty|\{f>t\}|^{(n-1)/n}\,dt-\|f\|_{L^q}
 \right\}.
\end{aligned}                                                \tag{10.1}
\]
This resembles the level-set deficit/kinetic structure sought here.
However, \(f=\mathbf1_E\) has only one nontrivial level and contains no
centre-motion information.  Choosing a smoothing or a potential associated
with \(E\) would require a non-circular estimate of its Sobolev deficit and a
trace recovery of \({\cal B}_z(E)\).  Until such a bridge is written,
Sobolev is a source of analogy, not a proof module.

## 11. Work packages for agents

Each package has a defined deliverable.  Proof notes should state every
constant dependency and explicitly mark failed statements.

### WP0: Definitions and permissible-input audit

**Deliverable:** a two-page notation and dependency note.

1. Verify (2.1)--(2.3), including scaling.
2. Record the computable constant available in the ordinary FMP transport
   inequality (8.3).
3. Confirm that no proposed input already invokes Fusco--Julin.
4. Cross-reference established results in
   `Sharp Faber-Krahn Manuscript/FJ_quantitative_attempts.tex`.

### WP1: Same-centre and symmetry-centre lemmas

**Deliverable:** proofs of C1 and C2 with explicit constants.

1. Prove the bathtub shell estimate C1.
2. Prove the unit-ball translation lower bound used in C2.
3. Prove C2 for one hyperplane and for an orthogonal family.
4. Include tests on translated balls and symmetric unions of two balls.

This package is elementary and should be completed first.

### WP2: Quadratic recentering

**Deliverable:** a proof or a precise counterexample to C3.

1. Compute \(I_z(B_1(a))\) to second order in \(z-a\).
2. Separate the exact-ball term from the error \(G\triangle B_1(z)\).
3. Seek a rearrangement estimate preserving quadratic order.
4. Test satellite, cavity, and thin-neck examples.
5. If C3 fails as stated, formulate the weakest corrected hypothesis
   inherited by reflected children.

This is the first go/no-go point for the oriented-FMP programme.

### WP3: Two-plane coherent-centre lemma

**Deliverable:** C4, initially for smooth bounded sets and then for finite
perimeter sets.

1. Rewrite FMP Lemma 2.4 in current notation with all overlap constants.
2. Build half-ball models from the four children using C1--C2.
3. Track projections of the four centres to the appropriate median flats.
4. Use two orthogonal overlaps to control incompatible shifts.
5. Check that the error is \(O(D(A)+\max\beta(A_i^s)^2)\), not its square
   root.

The last requirement is essential: a square-root loss does not prove (FJ).

### WP4: Oriented reflection theorem

**Deliverable:** OFR, TERM, and the iterated reduction (5.2).

1. Prove C5 from WP1--WP3.
2. Prove TERM separately using full symmetry of final children.
3. Iterate without suppressing constants or deficit thresholds.
4. Add the large-deficit branch and any required truncation/confinement.

### WP5: Planar symmetric closure

**Deliverable:** a complete proof or a precisely identified remaining lemma
for (P2).

1. Start from the already proved perpendicular-quadrisection reduction.
2. Establish the one-dimensional transverse slice-motion estimate.
3. Prove the even-profile meridian estimate from (3.8) with \(n=2\).
4. Pass to arbitrary finite-perimeter planar sets.

A successful WP5 gives a complete intrinsic proof in dimension two and is
the most informative early milestone.

### WP6: Higher-dimensional oriented slice induction

**Deliverable:** (SM), conditional only on the lower-dimensional symmetric
closure.

1. Derive the exact weighted slice decomposition of \({\cal B}_0\).
2. Identify central-strip weights and polar errors.
3. Apply the lower-dimensional result only to symmetric slices with fixed
   centre.
4. Prove the BV approximation step and track erased facets.

### WP7: Meridian action closure

**Deliverable:** (MA) for even axially symmetric profiles.

1. Write all profile regularity and support hypotheses.
2. Produce central coercivity and cap estimates.
3. Remove volume and translation modes explicitly.
4. Extend from smooth profiles to finite-perimeter profiles.

### WP-T: Transport radialisation test

**Deliverable:** proof or failure report for (TR).

This may be run in parallel with WP1--WP3.  It must not delay the primary
oriented-FMP attack.

### WP-BM: Oriented first-variation experiment

**Deliverable:** a rigorously formulated BM-ORIENT lemma in a restricted
class, or a written reason the route cannot preserve the sharp order.

This is exploratory and should not be allowed to substitute for WP3 without
a proved boundary-normal inequality.

## 12. Falsification suite

Every new lemma should be checked against the following configurations before
it is trusted.

1. **Translated ball.**  Detects any failure to remove the translation mode
   or any false fixed-centre estimate in terms of deficit alone.
2. **Two shifted half-balls glued across a median plane.**  Detects whether a
   one-cut argument has ignored tangential centre mismatch.
3. **Four half-ball models from orthogonal cuts.**  Tests the C4 overlap
   mechanism at the geometry it is meant to control.
4. **Ball plus a small remote satellite with compensating removed mass.**
   Tests potential estimates against small far-away components.
5. **Ball with a thin inward cavity and compensating outer shell.**  Tests
   singular-kernel recentering and trace estimates.
6. **Symmetric two-lobed set.**  Detects the false assertion that every
   symmetric potential maximiser lies on the symmetry flat.
7. **Near-spherical degree-two perturbation.**  Checks the sharp quadratic
   scaling and catches a square-root loss.
8. **Polar-cap perturbation of an axial profile.**  Tests whether meridian
   estimates properly pay for cap motion.

An agent encountering a failure should record it as a mathematical result:
knowing which natural lemma is false materially narrows the proof search.

## 13. Dependency graph and recommended execution order

The recommended order is:

1. Complete WP0 and WP1.
2. Run WP2 and WP5 in parallel.  WP2 tests the high-dimensional reduction;
   WP5 can close the planar case independently of the two-plane problem.
3. If C3 survives, execute WP3 and then WP4.
4. Once a fully symmetric reduction exists, execute WP7 in parallel with
   WP6; the former is a one-dimensional endpoint, the latter is the
   dimensional induction.
5. Run WP-T and WP-BM as side investigations throughout, promoting either
   only if its missing oriented estimate is proved.

The final proof chain, if successful, will read:
\[
  \text{C1--C5}
  \Longrightarrow \text{OFR + TERM}
  \Longrightarrow \text{fully symmetric reduction}
  \Longrightarrow \text{SM + MA}
  \Longrightarrow \text{(FJ)}.
\]
Every arrow represents a finite list of inequalities.  Hence this route, if
closed as stated, provides not only an intrinsic proof but also a certificate
that its dimensional constant is computable.

## 14. Present status

The geometric programme is not presently complete.

1. The fixed-centre identity, \(n-1\) centred-reflection reduction,
   transverse symmetrisation identity, and meridian action are proved.
2. The full initial oriented symmetry reduction is proved in dimension two.
3. In dimensions \(n\ge3\), the previous last-axis fixed-centre target remains
   open and is now superseded as the primary target by OFR, TERM, and
   C1--C5.
4. Even in dimension two, the planar symmetric closure (P2) remains to be
   proved.
5. The regularised-selection branch elsewhere in the manuscript already
   certifies a computable Fusco--Julin constant; the present document is the
   plan for a more revealing geometric proof.

## 15. Primary sources and the exact reason each is used

1. N. Fusco and V. Julin, *A strong form of the quantitative isoperimetric
   inequality*, Calc. Var. PDE 50 (2014), 925--937.
   Preprint: <https://arxiv.org/abs/1111.4866>.
   Source of the theorem and the radial-normal quantity.
2. N. Fusco, F. Maggi, and A. Pratelli, *The sharp quantitative
   isoperimetric inequality*, Ann. of Math. 168 (2008), 941--980.
   <https://annals.math.princeton.edu/2008/168-3/p06>.
   Source of the geometric reflection/slicing architecture, especially
   Lemmas 2.4--2.5 and the reduction to axially symmetric sets.
3. A. Figalli, F. Maggi, and A. Pratelli, *A mass transportation approach to
   quantitative isoperimetric inequalities*, Invent. Math. 182 (2010),
   167--211.
   <https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf>.
   Source of the effective ordinary quantitative inequality and the transport
   boundary-direction comparison which motivates (TR).
4. A. Figalli, P. van Hintum, and M. Tiba, *Sharp quantitative stability of
   the Brunn--Minkowski inequality*, arXiv:2310.20643 (2023).
   <https://arxiv.org/abs/2310.20643>.
   Source of current sharp BM stability; used only as motivation for an
   oriented first-variation experiment unless a new boundary estimate is
   proved.
5. A. Figalli, P. van Hintum, and M. Tiba, *Sharp Quantitative Stability for
   the Prekopa--Leindler and Borell--Brascamp--Lieb Inequalities*,
   arXiv:2501.04656 (2025).
   <https://arxiv.org/abs/2501.04656>.
   Source of the overlapping-level coherent-translation architecture to be
   adapted concretely in C4.
6. G. L. Maldonado and E. Roldan-Pensado, *On the orthogonal Grunbaum
   partition problem in dimension three*, arXiv:2404.01504 (2024);
   published in Computational Geometry 126 (2025), 102149.
   <https://arxiv.org/abs/2404.01504>.
   Source of the obstruction to extending the planar orthogonal-equipartition
   shortcut to \(n\ge3\).
