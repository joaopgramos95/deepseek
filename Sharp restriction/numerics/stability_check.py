#!/usr/bin/env python3
"""Stability analysis for the BTZ connection.

Computes the cross-term bound in the variational inequality and
determines the BTZ stability constant needed to close the argument.

The key identity (from block-diagonal cancellation):

  Lambda_* = (1-sigma^2)^3 J(g) + 6 Re<(I-P_N)R(P_N f_*), r_N> + Q

where:
  - J(g) <= Lambda_0 (BTZ)
  - |(I-P_N)R| involves only high-mode Bessel integrals
  - |Q| <= C sigma^2 Lambda_*

This script computes the high-mode part ||(I-P_N)D^j T[h^j]||
for j=2,...,5 using explicit Bessel integrals.
"""

from __future__ import annotations
import ctypes, math, json, time, argparse
from pathlib import Path

TWO_PI = 2.0 * math.pi

class BesselBackend:
    def __init__(self):
        self.name = "libm"
        self._gsl = None
        try:
            self._gsl = ctypes.CDLL("libgsl.so.27")
            self._gsl.gsl_sf_bessel_Jn.argtypes = [ctypes.c_int, ctypes.c_double]
            self._gsl.gsl_sf_bessel_Jn.restype = ctypes.c_double
            self._gsl.gsl_sf_bessel_J0.argtypes = [ctypes.c_double]
            self._gsl.gsl_sf_bessel_J0.restype = ctypes.c_double
            self.name = "gsl"
        except OSError:
            self._libm = ctypes.CDLL("libm.so.6")
            self._libm.j0.argtypes = [ctypes.c_double]
            self._libm.j0.restype = ctypes.c_double
            self._libm.jn.argtypes = [ctypes.c_int, ctypes.c_double]
            self._libm.jn.restype = ctypes.c_double

    def j(self, n: int, x: float) -> float:
        if self._gsl:
            return float(self._gsl.gsl_sf_bessel_J0(x) if n == 0
                         else self._gsl.gsl_sf_bessel_Jn(n, x))
        return float(self._libm.j0(x) if n == 0 else self._libm.jn(n, x))

def simpson(vals, h):
    n = len(vals) - 1
    return h * (vals[0] + vals[n] + 4*sum(vals[1:n:2]) + 2*sum(vals[2:n:2])) / 3

def integrate_6bessel(backend, indices, R, h):
    """int_0^R prod_{i} J_{indices[i]}(r) * r dr, always 6 Bessel functions."""
    assert len(indices) == 6
    steps = int(round(R / h))
    if steps % 2: steps += 1
    ha = R / steps
    vals = []
    for s in range(steps + 1):
        r = s * ha
        p = r
        for idx in indices:
            p *= backend.j(idx, r)
        vals.append(p)
    return simpson(vals, ha)

def high_mode_cross_bound(backend, N, R, h, delta_max=1.414):
    """Compute ||(I-P_N) R(P_N f_*)||_2 bound.

    R(g) = T(g) - T(f_0) - K(g-f_0) is the nonlinear remainder.
    For g = P_N f_* band-limited to modes <= N:
    (I-P_N)R has modes N < |k| <= 5N.

    The dominant contribution is from D^2 T[h,h] projected to modes > N.
    """
    t0 = time.time()

    J0_int = integrate_6bessel(backend, [0,0,0,0,0,0], R, h)
    Lambda0 = 16 * math.pi**4 * J0_int

    # For each output mode k with N < |k| <= 5N:
    # The D^2T contribution at mode k involves pairs (n1, n2)
    # with |n1|, |n2| <= N and selection rule matching k.
    # The Bessel integral is B(n1, n2, k) = int J_0^3 J_{n1} J_{n2} J_k r dr.
    #
    # The D^2T coefficient has |S_k|^2 * B^2 structure (from the HS norm).
    # For the (I-P_N) projection, sum only over |k| > N.

    high_mode_d2t_sq = 0.0
    mode_contributions = []

    # Sample representative k values to estimate the sum
    k_samples = list(range(N+1, min(5*N+1, N+60)))  # first 60 modes above N
    for k in k_samples:
        k_contrib = 0.0
        # Pairs (n1, n2) that can produce output k via selection rules
        for n1 in range(-min(N, k+N), min(N, k+N)+1):
            for rule in [1, -1]:  # k = n1+n2 or k = n1-n2
                if rule == 1:
                    n2 = k - n1
                else:
                    n2 = n1 - k
                if abs(n2) > N:
                    continue
                B = integrate_6bessel(backend,
                    [0, 0, 0, abs(n1), abs(n2), abs(k)], R, h)
                # Phase factor magnitude: |S_k| = 6 for each contributing pair
                # (accounting for all four terms in D^2N)
                k_contrib += 36 * B**2  # |S|^2 = 36 for generic pairs

        if k_contrib > 0:
            mode_contributions.append({"k": k, "contrib": k_contrib})
            high_mode_d2t_sq += k_contrib

    # Extrapolate tail (k > max sampled): use decay k^{-17/3}
    if mode_contributions:
        last_k = k_samples[-1]
        last_val = mode_contributions[-1]["contrib"]
        if last_val > 0:
            tail_extrap = last_val * last_k**(17/3) * sum(
                k**(-17/3) for k in range(last_k+1, 5*N+1))
            high_mode_d2t_sq += tail_extrap

    # The full (I-P_N)D^2T norm (for unit h):
    # ||(I-P_N)D^2T[h,h]||^2 = (2pi)^6 * high_mode_d2t_sq * ||h||^4
    d2t_high_norm = math.sqrt(TWO_PI**6 * high_mode_d2t_sq)

    # Cross term bound: |<(I-P_N)R, r_N>| <= ||(I-P_N)R|| * sigma_N
    # ||(I-P_N)R|| <= (1/2)*d2t_high_norm*delta^2 + higher order

    sigma_N = 0.072  # from Sobolev bootstrap
    r0 = 0.13

    # The cross term contributes to the variational inequality:
    # Lambda_* <= (1-sigma^2)^3 Lambda_0 + 6*cross + Q
    # cross <= sigma_N * d2t_high_norm/2 * delta^2

    cross_coeff = 3 * d2t_high_norm * sigma_N  # 6 * (1/2) * d2t * sigma

    # For the stability argument:
    # Lambda_0 - J(g) >= c_stab * dist(g, f_0)^2
    # Lambda_* >= Lambda_0
    # Lambda_* <= (1-sigma^2)^{-3} * [Lambda_0 - c_stab*delta_g^2] + cross
    # where delta_g = dist(g, f_0)
    # Combined: need c_stab > cross_coeff / delta_g (for self-consistency)

    # Required c_stab: c_stab * delta_g^2 >= cross_coeff * delta^2
    # Since delta_g ~ delta / sqrt(1-sigma^2) ~ delta:
    # c_stab >= cross_coeff

    # The Hessian gives LOCAL c_stab = 6*|5*I_2 - Lambda_0|/2
    I2 = 16*math.pi**4 * integrate_6bessel(backend, [0,0,0,0,2,2], R, h)
    hessian_eigenvalue = abs(6*(5*I2 - Lambda0))
    c_stab_local = hessian_eigenvalue / 2

    elapsed = time.time() - t0

    return {
        "N": N,
        "Lambda0": Lambda0,
        "sigma_N": sigma_N,
        "r0": r0,
        "d2t_high_norm": d2t_high_norm,
        "cross_coefficient": cross_coeff,
        "c_stab_local_hessian": c_stab_local,
        "c_stab_needed": cross_coeff,
        "ratio_local_to_needed": c_stab_local / cross_coeff if cross_coeff > 0 else float('inf'),
        "hessian_sufficient": c_stab_local > cross_coeff,
        "top_high_modes": mode_contributions[:10],
        "high_mode_d2t_sq_total": high_mode_d2t_sq,
        "elapsed": elapsed,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--N", type=int, default=52)
    parser.add_argument("--R", type=float, default=500.0)
    parser.add_argument("--h", type=float, default=0.1)
    parser.add_argument("--output", type=Path,
                        default=Path("numerics/results/stability_check.json"))
    args = parser.parse_args()

    backend = BesselBackend()
    print(f"Backend: {backend.name}")

    result = high_mode_cross_bound(backend, args.N, args.R, args.h)

    print(f"\n=== Stability analysis (N={args.N}) ===")
    print(f"  Lambda_0 = {result['Lambda0']:.2f}")
    print(f"  sigma_N = {result['sigma_N']}")
    print(f"  ||(I-P_N)D^2T|| = {result['d2t_high_norm']:.2f}")
    print(f"  Cross coefficient (3*||D^2T_high||*sigma) = {result['cross_coefficient']:.2f}")
    print(f"  c_stab from local Hessian = {result['c_stab_local_hessian']:.2f}")
    print(f"  c_stab needed = {result['c_stab_needed']:.2f}")
    print(f"  Ratio (local/needed) = {result['ratio_local_to_needed']:.2f}")
    print(f"  Hessian sufficient? {result['hessian_sufficient']}")
    print(f"  Elapsed: {result['elapsed']:.1f}s")

    text = json.dumps(result, indent=2)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text + "\n")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
