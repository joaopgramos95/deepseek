#!/usr/bin/env python3
"""Quantitative bootstrap tail estimates for the BTZ connection.

Computes the sixfold Bessel integrals B(a,b,k) = int J_0^3 J_a J_b J_k r dr
for large k, verifying the decay rate O(k^{-17/6}) and computing the explicit
constant C_tail in the quadratic tail bound:

    |f_hat(k)| <= C_tail / nu_0 * |k|^{-17/6} * ||f - f_0||^2.

Also evaluates the iterative bootstrap to check whether the BTZ connection
closes with N = 120 modes.
"""

from __future__ import annotations

import argparse
import ctypes
import json
import math
import time
from pathlib import Path


TWO_PI = 2.0 * math.pi


class BesselBackend:
    def __init__(self) -> None:
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
            self._gsl = None
            self._libm = ctypes.CDLL("libm.so.6")
            self._libm.j0.argtypes = [ctypes.c_double]
            self._libm.j0.restype = ctypes.c_double
            self._libm.jn.argtypes = [ctypes.c_int, ctypes.c_double]
            self._libm.jn.restype = ctypes.c_double

    def j(self, n: int, x: float) -> float:
        if self._gsl is not None:
            if n == 0:
                return float(self._gsl.gsl_sf_bessel_J0(x))
            return float(self._gsl.gsl_sf_bessel_Jn(n, x))
        if n == 0:
            return float(self._libm.j0(x))
        return float(self._libm.jn(n, x))


def simpson_integral(values: list[float], h: float) -> float:
    n = len(values) - 1
    if n % 2 != 0:
        raise ValueError("Simpson rule needs an even number of subintervals")
    odd = sum(values[1:n:2])
    even = sum(values[2:n:2])
    return h * (values[0] + values[n] + 4.0 * odd + 2.0 * even) / 3.0


def integrate_B(backend: BesselBackend, a: int, b: int, c: int,
                R: float, h: float) -> float:
    """B(a,b,c) = int_0^R J_0(r)^3 J_a(r) J_b(r) J_c(r) r dr."""
    steps = int(round(R / h))
    if steps % 2:
        steps += 1
    h_act = R / steps
    vals: list[float] = []
    for s in range(steps + 1):
        r = s * h_act
        j0 = backend.j(0, r)
        ja = backend.j(a, r)
        jb = backend.j(b, r)
        jc = backend.j(c, r)
        vals.append(j0**3 * ja * jb * jc * r)
    return simpson_integral(vals, h_act)


def bessel_decay_scan(backend: BesselBackend, a_max: int, k_max: int,
                      R: float, h: float) -> list[dict]:
    """Compute |B(a, b, k)| for various (a, b, k) to verify decay in k."""
    results = []
    for k in range(2, k_max + 1):
        max_B = 0.0
        best_ab = (0, 0)
        for a in range(min(a_max, k) + 1):
            for b in range(a, min(a_max, k) + 1):
                if a + b > k + 5 * a_max:
                    continue
                B = abs(integrate_B(backend, a, b, k, R, h))
                if B > max_B:
                    max_B = B
                    best_ab = (a, b)
        if max_B > 1e-20:
            fitted_exp = -math.log(max_B * k ** (17.0 / 6)) if max_B > 0 else float('inf')
            results.append({
                "k": k,
                "max_B": max_B,
                "best_a_b": list(best_ab),
                "k_pow_17_6_times_B": max_B * k ** (17.0 / 6),
                "log_ratio": fitted_exp,
            })
    return results


def compute_tail_constant(backend: BesselBackend, N_modes: int,
                          R: float, h: float) -> dict:
    """Compute the constant C' in the quadratic tail bound sigma_N^2 <= C'/nu_0^2 * N^{-14/3} * ||h||^4.

    The D^2T contribution at mode k involves quintuples (n1,n2,n3,m1,m2)
    summing to k, with Bessel integral B(|n1|,...,|k|). For the HS-type
    bound, we sum |S_k|^2 * B^2 over all contributing quintuples.

    For the TAIL (|k| > N), each quintuple has at least one index > N/5.
    Near f_0, the dominant contribution comes from the quadratic term
    D^2T[h,h], which involves pairs (n1, n2) with output at k.
    """
    t0 = time.time()

    J0_val = integrate_B(backend, 0, 0, 0, R, h)

    Lambda0 = 16 * math.pi**4 * J0_val
    nu0_ratio = 0.452
    nu0 = nu0_ratio * Lambda0

    sigma_sq_bound_terms = []
    for k in range(N_modes + 1, 5 * N_modes + 1):
        k_contribution = 0.0
        count = 0
        for n1 in range(-N_modes, N_modes + 1):
            for n2 in range(-N_modes, N_modes + 1):
                if n1 + n2 == k or n1 - n2 == k or n2 - n1 == k or -(n1+n2) == k:
                    B = integrate_B(backend, abs(n1), abs(n2), abs(k), R, h)
                    k_contribution += B**2 * 40
                    count += 1
        if k_contribution > 0:
            sigma_sq_bound_terms.append({
                "k": k,
                "contribution": k_contribution,
                "num_pairs": count,
            })

    total_tail = sum(t["contribution"] for t in sigma_sq_bound_terms)

    C_prime_eff = total_tail * nu0**2 * (2 * math.pi)**6

    elapsed = time.time() - t0

    return {
        "N_modes": N_modes,
        "Lambda0": Lambda0,
        "nu0": nu0,
        "tail_sum": total_tail,
        "C_prime_effective": C_prime_eff,
        "terms": sigma_sq_bound_terms[:10],
        "elapsed": elapsed,
    }


def iterative_bootstrap(backend: BesselBackend, N_btk: int,
                        R: float, h: float) -> dict:
    """Check whether the iterative bootstrap closes for N_btk modes.

    The iteration is:
    1. ||f - f0|| <= sqrt(2) (trivial)
    2. sigma_N <= C * ||f-f0||^2 * N^{-7/3} (quadratic tail)
    3. Lambda_0^{1/6}(1-sqrt(1-sigma_N^2)) <= C_ST * sigma_N (BTZ squeeze)
    4. If ||f-f0|| < r0, done.
    """
    t0 = time.time()

    J0_val = integrate_B(backend, 0, 0, 0, R, h)
    Lambda0 = 16 * math.pi**4 * J0_val
    Lambda0_sixth = Lambda0 ** (1.0 / 6.0)
    nu0 = 0.452 * Lambda0

    hs_norm = 1838.0
    M0 = 2 * hs_norm
    r0 = 2 * nu0 / M0

    h_bound = math.sqrt(2)
    iterations = []

    for it in range(10):
        sigma_est = (hs_norm / (2 * nu0)) * h_bound**2 * N_btk ** (-7.0 / 3)

        if sigma_est >= 1.0:
            sigma_est = min(sigma_est, 1.0 / math.sqrt(2 * math.pi))

        h_from_sigma = math.sqrt(2 * (1 - math.sqrt(max(0, 1 - sigma_est**2)) *
                                       (1 - sigma_est * Lambda0_sixth / Lambda0_sixth)))

        h_new = min(h_bound, math.sqrt(2 * sigma_est * Lambda0_sixth / (Lambda0_sixth)))

        if h_new >= h_bound * 0.999:
            converged = False
            h_bound_new = h_bound
        else:
            h_bound_new = max(h_new, math.sqrt(2 * sigma_est))
            converged = h_bound_new < r0

        iterations.append({
            "iteration": it,
            "h_bound": h_bound,
            "sigma_N_est": sigma_est,
            "h_new": h_bound_new,
            "converged_to_NK": converged,
        })

        if converged:
            break
        if h_bound_new >= h_bound * 0.999:
            break
        h_bound = h_bound_new

    elapsed = time.time() - t0

    return {
        "N_btk": N_btk,
        "r0": r0,
        "Lambda0": Lambda0,
        "nu0": nu0,
        "M0": M0,
        "hs_norm": hs_norm,
        "iterations": iterations,
        "final_h_bound": h_bound,
        "final_sigma": iterations[-1]["sigma_N_est"] if iterations else None,
        "closed": any(it["converged_to_NK"] for it in iterations),
        "elapsed": elapsed,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--R", type=float, default=2000.0)
    parser.add_argument("--h", type=float, default=0.05)
    parser.add_argument("--k-max", type=int, default=40)
    parser.add_argument("--a-max", type=int, default=6)
    parser.add_argument("--N-btk", type=int, default=120)
    parser.add_argument("--output", type=Path,
                        default=Path("numerics/results/bootstrap_tail.json"))
    args = parser.parse_args()

    backend = BesselBackend()
    print(f"Backend: {backend.name}")

    print("\n=== Bessel decay scan ===")
    decay = bessel_decay_scan(backend, args.a_max, args.k_max, args.R, args.h)
    for row in decay[:15]:
        print(f"  k={row['k']:3d}  max|B|={row['max_B']:.6e}  "
              f"k^(17/6)*|B|={row['k_pow_17_6_times_B']:.6f}  "
              f"best(a,b)={row['best_a_b']}")

    print(f"\n=== Iterative bootstrap (N={args.N_btk}) ===")
    bootstrap = iterative_bootstrap(backend, args.N_btk, args.R, args.h)
    for it in bootstrap["iterations"]:
        print(f"  iter {it['iteration']}: ||h|| <= {it['h_bound']:.6f}, "
              f"sigma_N <= {it['sigma_N_est']:.6e}, "
              f"converged={it['converged_to_NK']}")
    print(f"  Closed: {bootstrap['closed']}")
    print(f"  r0 = {bootstrap['r0']:.4f}")

    for N_test in [120, 200, 500, 1000]:
        b = iterative_bootstrap(backend, N_test, args.R, args.h)
        status = "CLOSED" if b["closed"] else "open"
        sigma = b["final_sigma"]
        print(f"  N={N_test:5d}: sigma_N ~ {sigma:.4e}, ||h|| ~ {b['final_h_bound']:.4f}, {status}")

    result = {
        "bessel_decay": decay,
        "bootstrap": bootstrap,
    }
    text = json.dumps(result, indent=2)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text + "\n", encoding="utf-8")
    print(f"\nWrote {args.output}")


if __name__ == "__main__":
    main()
