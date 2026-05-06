# Ambiguity function on the unit disk — working notes

## Problem
For f ∈ L²(ℝ), maximize Φ(f) = ‖A(f)‖²_{L²(D)} / ‖f‖₂⁴ where D ⊂ ℂ is the
unit disk and A(f) is the auto-ambiguity function. Conjecture: max is
1 − e^{−π}, achieved by the Gaussian h₀.

## Status

| Case                                  | Status                                  |
|---------------------------------------|-----------------------------------------|
| f = single Hermite h_n                | Proved: Φ(h_n) = λ_n ≤ λ_0 = 1−e^{−π}   |
| f = α h_0 + β h_n (two-mode)          | Proved conditional on (★) below         |
| General f                             | OPEN (see correction below)             |

**Correction (important).** I previously cited a "Nicola–Tilli 2024" result
extending Faber–Krahn to the auto-ambiguity. As far as I can verify, no
such paper exists. What is real is:

- Nicola & Tilli, Invent. Math. 230 (2022): Faber–Krahn for the STFT with
  Gaussian window, i.e., the **cross-ambiguity** A(f, h_0). The proof uses
  the Bargmann–Fock factorisation |A(f, h_0)|² = e^{−π|z|²} |Bf(z)|²,
  with |Bf|² logarithmically subharmonic.

- The **auto-ambiguity** A(f, f) statement (our problem) appears to be
  **open**. The Wigner function is real but signed (Hudson's theorem), so
  there is no Bargmann–Fock factorisation, and the heat-flow argument
  doesn't transfer.

So the conjecture is **not** settled by citation.

Conditional inequality (★), verified numerically for n ≤ 30:
∫₀^π L_{n−1}(s) ds ≤ Σ_{j=1}^n π^j/j!.

Equivalently (cleaner form):
β_n := a_n + g_n ≤ λ_0,
where a_n = ∫₀^π e^{−u} L_n(u) du and g_n = (1/n!) ∫₀^π u^n e^{−u} du.
β_1 = λ_0 (equality), β_n strictly less for n ≥ 2.

## Key observations

1. **Hermite-angular-harmonic decomposition.** With f = Σ c_n h_n and
   z = re^{iθ}, the ambiguity function decomposes by angular harmonic:
       A(f)(re^{iθ}) = Σ_k e^{ikθ} R_k(r)
   so by orthogonality on the rotation-invariant disk,
       ∫_D |A(f)|² = Σ_k ∫_D |R_k|².

2. **Diagonal (k=0) bound via Jensen.** Φ_0 = Σ |c_n|² ρ_{n,n} is a
   convex combination, so
       ∫_D |Φ_0|² ≤ Σ |c_n|² λ_n ≤ λ_0.
   Equality only at f = h_0.

3. **Operator norm of G^(k) is 1.** The Gram matrix G^(0)_{m,n} =
   ∫₀^π e^{−u} L_m L_n du has supremum 1 over ℓ²-vectors (achieved by
   v with Σ v_n L_n(u) ≈ 1_{[0,π]}(u)). So generic operator-norm bounds
   on G^(k) cannot give the desired estimate. The rank-1 constraint
   b^(k)_n = c_{n+k} c̄_n is essential and global.

4. **Two-mode closed form.** For f = α h_0 + β h_n, t = |β|²:
       J_n(t) = (1−t)² λ_0 + 2t(1−t) β_n + t² λ_n
   The bracket B(t) = J_n(t)/t is linear in t, with B(0) = 2(β_n−λ_0)
   and B(1) = λ_n − λ_0; both ≤ 0 (using (★) and Lemma 4.1), so J_n ≤ λ_0.

5. **n=1 closed form.**
       J_1(t) = λ_0 − π² e^{−π} t².
   The deficit is exactly π² e^{−π} |β|⁴.

## Open subproblems for a self-contained proof

(a) Prove (★) analytically. Cleanest formulation:
       (π/n) L_{n−1}^{(1)}(π) ≤ Σ_{j=1}^n π^j/j!.

(b) Hessian of J at h_0 is negative semidefinite in Hermite coordinates
    — would prove h_0 is a local max in every direction; combined with
    the symmetry argument and a coercivity estimate, would give global.

(c) Three-mode case: explicit but tedious computation involving Laguerre
    integrals like ∫₀^π e^{−u} L_1 L_2 du = (π − π² + π³/2) e^{−π}.

## References

- Lieb, "Integral bounds for radar ambiguity functions and Wigner
  distributions", J. Math. Phys. 31 (1990) — L^p bounds for |A(f)|, sharp
  at Gaussians. Real and proven, but not strong enough to imply the disk
  inequality (gives only the trivial bound 1).
- Nicola & Tilli, "The Faber–Krahn inequality for the short-time Fourier
  transform", Invent. Math. 230 (2022) — for the cross-ambiguity with
  Gaussian window only. **Does not directly imply our auto-ambiguity
  conjecture.**

## Apologies

In an earlier draft I cited a non-existent "Nicola–Tilli 2024" paper as
settling the auto-ambiguity case. That citation was a hallucination; the
auto-ambiguity Faber–Krahn is, to my knowledge, open.
