# Weighted Route B repair attempt: spectral obstruction

This note tests the proposed repair from
`00-route-specs/PLAN3_AFTER_PLAN1_PATCH_ASSESSMENT.md`: keep the torsion weight
and prove a weighted square-function theorem of the form

```text
integral_D v |D^2 w|^2  controls boundary H^{1/2} / asymmetry,
```

where `v` is the torsion function of `D` and

```text
w = v - q,        q(x)=a-|x-z|^2/(2n).
```

The outcome is negative in this form. The proposed weighted square function is
one derivative too strong. It sees an `H^1` boundary scale, whereas sharp
Saint-Venant stability sees exactly the `H^{1/2}` scale. Consequently the
single-level weighted Weinberger inequality used by the newer Route B notes
cannot be true with a dimensional constant.

## 1. Exact ball calculation

Work on `B_1`, with

```text
v_B(x) = (1-|x|^2)/(2n).
```

Let `Y_k` be a spherical harmonic of degree `k`, normalized by
`||Y_k||_{L^2(S^{n-1})}=1`, and let

```text
H_k(r,theta) = r^k Y_k(theta)
```

be its harmonic extension.

The Dirichlet energy is the usual Dirichlet-to-Neumann identity:

```text
integral_{B_1} |grad H_k|^2 = k.
```

The weighted Hessian energy is explicit. Since `H_k` is harmonic,

```text
Delta |grad H_k|^2 = 2 |D^2 H_k|^2.
```

Pair this with `v_B`. Because `v_B=0` and `partial_nu v_B=-1/n` on
`partial B_1`, and `Delta v_B=-1`,

```text
2 integral_{B_1} v_B |D^2 H_k|^2
 = integral_{B_1} v_B Delta |grad H_k|^2
 = - integral_{B_1} |grad H_k|^2
   + (1/n) integral_{S^{n-1}} |grad H_k|^2.
```

On the boundary,

```text
integral_{S^{n-1}} |grad H_k|^2
 = k^2 + k(k+n-2) = k(2k+n-2).
```

Therefore

```text
integral_{B_1} v_B |D^2 H_k|^2
 = (1/2) [ -k + k(2k+n-2)/n ]
 = k(k-1)/n.
```

So the two natural energies have different spectral order:

```text
Dirichlet energy:          k |Y_k|^2        H^{1/2} boundary scale
weighted Hessian energy:   k(k-1) |Y_k|^2   H^1 boundary scale
```

This is the decisive mismatch.

## 2. Near-ball contradiction to weighted Half-1

The newer Route B notes require a weighted Half-1 statement of the form

```text
delta_T(D) >= c(n) integral_D v |D^2 v + (1/n)I|^2
```

after volume normalization.

This cannot hold. Take a smooth nearly spherical domain

```text
D_{eps,k} = { r < 1 + eps Y_k(theta) },
```

with `k >= 2`, and add the usual `O(eps^2)` zero/first-mode corrections to
keep volume and barycenter normalized. For each fixed `k`, choose `eps` small
enough that the second-variation expansion is valid.

The first variation of `v + |x|^2/(2n)` is the harmonic extension of
`eps Y_k / n`. Hence the weighted Hessian defect has leading term

```text
R_v(D_{eps,k})
 := integral_{D_{eps,k}} v |D^2 v + (1/n)I|^2
 = c_n eps^2 k(k-1) + o_k(eps^2).
```

But the sharp Saint-Venant deficit has the standard nearly spherical second
variation

```text
delta_T(D_{eps,k})
 = c'_n eps^2 (k-1) + o_k(eps^2).
```

Thus

```text
R_v(D_{eps,k}) / delta_T(D_{eps,k}) -> C_n k
```

as `eps -> 0`. Letting `k -> infinity` contradicts any dimensional constant
in the claimed weighted Half-1 inequality.

This is a smooth near-ball obstruction. It is not caused by tentacles,
pinching, disconnectedness, weak regularity, or the false `v >= c(n)` shortcut.
The inequality has the wrong derivative count.

## 3. Consequence for the proposed square-function repair

The weighted square function

```text
integral_D v |D^2 w|^2
```

is not the right object for sharp Faber-Krahn/Saint-Venant stability. On the
ball it controls an `H^1` boundary norm. Sharp stability only supplies, and
only needs, an `H^{1/2}` boundary norm.

Therefore the following chain cannot be repaired as stated:

```text
delta_T(D)
  -> weighted Hessian defect
  -> weighted square-function trace
  -> boundary H^{1/2} / asymmetry.
```

The first arrow is false at high spherical frequencies.

The earlier issue found in `dk-nge4.md`,

```text
|grad v| >= s0  does not imply  v >= c(n),
```

is still a real error. But it is no longer the deepest obstruction: even if one
keeps the weight correctly, the weighted Hessian defect is too strong to be
controlled by the torsion deficit.

## 4. What object would have the correct scale?

On the ball, the correct harmonic object is the first-order Dirichlet energy.
If `h = sum h_k` is a boundary graph and `H` is its harmonic extension, then

```text
integral_{B_1} |grad H|^2
 = sum_{k>=1} k ||h_k||_{L^2(S^{n-1})}^2
 ~ ||h||_{\dot H^{1/2}(S^{n-1})}^2.
```

This is exactly the scale of the nearly spherical Saint-Venant deficit and the
BDV/Fuglede spectral closure.

So a viable graph-free Route B would need a mechanism producing a
first-order harmonic energy, or an integrated-in-level trace estimate that
loses half a derivative. That points back toward the Plan 2 metric/radial trace
machinery, not toward a single-level Weinberger Hessian defect.

## 5. Tentacles are not the main obstruction here

The weighted Hessian defect can be useful for some thin appendage bookkeeping.
For a tube of width `w` and volume `V`, the weighted defect scales like

```text
R_v(tube) ~ w^2 V.
```

This can dominate `V^2` when `V <= w^2`, and when `V >> w^2` the appendage is
usually paid for by the `O(delta_T)` escape layer. This split remains a
possible geometric bookkeeping tool.

But it does not solve Route B, because the smooth high-frequency near-ball
family above has no tentacle at all and already breaks the claimed
`delta_T -> R_v` step.

## 6. Updated verdict

The weighted square-function repair does **not** close Route B.

What survives:

```text
Plan 1 / Strategy A:
  selection gives high regularity, then H^{1/2} deficit control can be
  interpolated into the small C^{2,gamma} regime.
```

What remains possible but different:

```text
Plan 2 / metric trace style:
  use the level-set identity over an interval of levels to obtain a true
  H^{1/2}-scale trace, rather than a single-level weighted Hessian square
  function.
```

Route B as currently written should not use the weighted or unweighted
Hessian-defect Half-1 inequality. That inequality is false by the spherical
harmonic test above.

