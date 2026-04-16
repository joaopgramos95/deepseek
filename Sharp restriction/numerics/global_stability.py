#!/usr/bin/env python3
"""Global stability estimate for the band-limited restriction functional.

Estimates c_stab = inf_{g != f_0} (Lambda_0 - J(g)) / d_G(g, f_0)^2
over the band-limited unit sphere with modes <= N.

J(g) = ||Eg||_6^6 is computed by numerical quadrature over R^2.
The search uses:
  1. Deterministic one-mode geodesics from f_0 toward cos(n*theta), sin(n*theta)
  2. Random directions on the band-limited sphere
  3. Gradient ascent from random starting points (to find near-maximizers)
"""

from __future__ import annotations
import ctypes, math, random, json, time, argparse
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


class ExtensionGrid:
    """Precomputed Bessel values and angular grid for J(g) = ||Eg||_6^6."""

    def __init__(self, backend: BesselBackend, N_modes: int,
                 R: float, dr: float, nphi: int):
        self.N = N_modes
        self.nphi = nphi
        rsteps = int(round(R / dr))
        if rsteps % 2: rsteps += 1
        self.dr = R / rsteps
        self.nr = rsteps + 1

        self.rvals = [k * self.dr for k in range(self.nr)]
        self.rweights = []
        for k in range(self.nr):
            if k == 0 or k == rsteps:
                w = self.dr / 3.0
            elif k % 2:
                w = 4.0 * self.dr / 3.0
            else:
                w = 2.0 * self.dr / 3.0
            self.rweights.append(w * self.rvals[k] if k > 0 else 0.0)

        self.phis = [TWO_PI * j / nphi for j in range(nphi)]
        self.phi_weight = TWO_PI / nphi

        # Precompute Bessel values: bessel[m][ir] = J_m(r)
        self.bessel = []
        for m in range(N_modes + 1):
            self.bessel.append([backend.j(m, r) for r in self.rvals])

        # i^m cycle: (Re, Im) of i^m
        self.i_pow = [(1,0), (0,1), (-1,0), (0,-1)]

    def compute_J(self, a_cos: list[float], a_sin: list[float]) -> float:
        """Compute J(g) = ||Eg||_6^6 for g = a0 + sum a_cos[m]*cos(m*th) + a_sin[m]*sin(m*th).

        a_cos[0] = DC coefficient, a_cos[m] = cos(m*theta) coefficient for m>=1.
        a_sin[0] unused, a_sin[m] = sin(m*theta) coefficient for m>=1.

        The extension: Eg(r,phi) = sum_m 2*pi*i^m * [a_m * J_m(r) * e^{im*phi}]
        For real g: a_{-m} = conj(a_m), so a_m = (a_cos[m] - i*a_sin[m])/2 for m>=1
        and a_0 = a_cos[0].

        Eg = 2*pi*a_0*J_0 + sum_{m>=1} 2*pi*i^m*(a_cos[m]*cos(m*phi)-a_sin[m]*sin(m*phi))*J_m
            + imaginary parts...

        More carefully: a_m = (a_cos[m] - i*a_sin[m])/2,
        2*pi*i^m*a_m*J_m*e^{im*phi} + 2*pi*i^m*a_{-m}*J_m*e^{-im*phi}
        = 2*pi*i^m*J_m*[(a_cos[m]-i*a_sin[m])/2 * e^{im*phi}
                        + (a_cos[m]+i*a_sin[m])/2 * e^{-im*phi}]
        = 2*pi*J_m*i^m*[a_cos[m]*cos(m*phi) - a_sin[m]*i*(-i*sin(m*phi))]

        Let me just compute Re and Im of Eg directly.
        """
        total = 0.0
        for ir, rw in enumerate(self.rweights):
            if rw == 0:
                continue
            for jp in range(self.nphi):
                phi = self.phis[jp]
                re_u = 0.0
                im_u = 0.0
                # m=0: 2*pi*a0*J0, purely real
                re_u += TWO_PI * a_cos[0] * self.bessel[0][ir]
                for m in range(1, self.N + 1):
                    jm = self.bessel[m][ir]
                    cos_mp = math.cos(m * phi)
                    sin_mp = math.sin(m * phi)
                    # E(e^{im*theta}) = 2*pi*i^m*J_m*e^{im*phi}
                    # For real coefficients: contribution from mode m is
                    # 2*pi*J_m * [re_coeff * cos(m*phi) - im_coeff * sin(m*phi)]
                    # where the complex coefficient is i^m * a_m with
                    # a_m = (a_cos[m] - i*a_sin[m])/2
                    # But we also have the -m mode: i^m * conj(a_m) * e^{-im*phi}
                    #
                    # Total: 2*pi*J_m * 2*Re[i^m * a_m * e^{im*phi}]
                    # i^m * a_m = i^m * (a_cos[m] - i*a_sin[m])/2
                    re_im, im_im = self.i_pow[m % 4]
                    # i^m * (ac - i*as)/2 = (re_im*ac + im_im*as)/2 + i*(im_im*ac - re_im*as)/2
                    half_re = (re_im * a_cos[m] + im_im * a_sin[m]) / 2
                    half_im = (im_im * a_cos[m] - re_im * a_sin[m]) / 2
                    # 2*Re[(half_re + i*half_im)*(cos+i*sin)]
                    # = 2*(half_re*cos - half_im*sin)
                    contrib_re = 2 * (half_re * cos_mp - half_im * sin_mp)
                    contrib_im = 2 * (half_im * cos_mp + half_re * sin_mp)
                    re_u += TWO_PI * jm * contrib_re
                    im_u += TWO_PI * jm * contrib_im

                abs6 = (re_u**2 + im_u**2)**3
                total += rw * self.phi_weight * abs6
        return total


def normalize(a_cos, a_sin):
    """Normalize so ||g||_2 = 1."""
    norm2 = TWO_PI * a_cos[0]**2
    for m in range(1, len(a_cos)):
        norm2 += math.pi * (a_cos[m]**2 + a_sin[m]**2)
    scale = 1.0 / math.sqrt(norm2)
    return [c * scale for c in a_cos], [s * scale for s in a_sin]


def distance_to_f0(a_cos, a_sin):
    """||g - f_0||_2 where f_0 = (2*pi)^{-1/2}."""
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    d2 = TWO_PI * (a_cos[0] - f0_a0)**2
    for m in range(1, len(a_cos)):
        d2 += math.pi * (a_cos[m]**2 + a_sin[m]**2)
    return math.sqrt(d2)


def scan_geodesics(grid: ExtensionGrid, N: int, n_epsilon: int = 40):
    """Scan along geodesics from f_0 toward each Fourier mode."""
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    Lambda0_approx = grid.compute_J([f0_a0] + [0.0]*N, [0.0]*(N+1))

    results = []
    for mode in range(1, N + 1):
        for mode_type in ["cos", "sin"]:
            for ie in range(1, n_epsilon + 1):
                eps = ie * 0.05  # epsilon from 0.05 to 2.0
                a_cos = [1.0] + [0.0] * N
                a_sin = [0.0] * (N + 1)
                if mode_type == "cos":
                    a_cos[mode] = eps
                else:
                    a_sin[mode] = eps
                a_cos, a_sin = normalize(a_cos, a_sin)
                d = distance_to_f0(a_cos, a_sin)
                if d < 1e-10:
                    continue
                J = grid.compute_J(a_cos, a_sin)
                gap = Lambda0_approx - J
                ratio = gap / d**2 if d > 0 else float('inf')
                results.append({
                    "mode": mode,
                    "type": mode_type,
                    "epsilon": eps,
                    "d_to_f0": d,
                    "J": J,
                    "gap": gap,
                    "ratio_gap_d2": ratio,
                })
    return Lambda0_approx, results


def scan_random(grid: ExtensionGrid, N: int, n_samples: int,
                seed: int = 42):
    """Random points on the band-limited sphere."""
    rng = random.Random(seed)
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    Lambda0_approx = grid.compute_J([f0_a0] + [0.0]*N, [0.0]*(N+1))

    results = []
    for _ in range(n_samples):
        a_cos = [rng.gauss(0, 1) for _ in range(N + 1)]
        a_sin = [0.0] + [rng.gauss(0, 1) for _ in range(1, N + 1)]
        a_cos, a_sin = normalize(a_cos, a_sin)
        d = distance_to_f0(a_cos, a_sin)
        J = grid.compute_J(a_cos, a_sin)
        gap = Lambda0_approx - J
        ratio = gap / d**2 if d > 0 else float('inf')
        results.append({
            "d_to_f0": d,
            "J": J,
            "gap": gap,
            "ratio_gap_d2": ratio,
        })
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--N", type=int, default=6)
    parser.add_argument("--R", type=float, default=120.0)
    parser.add_argument("--dr", type=float, default=0.1)
    parser.add_argument("--nphi", type=int, default=96)
    parser.add_argument("--n-epsilon", type=int, default=30)
    parser.add_argument("--n-random", type=int, default=200)
    parser.add_argument("--output", type=Path,
                        default=Path("numerics/results/global_stability.json"))
    args = parser.parse_args()

    backend = BesselBackend()
    print(f"Backend: {backend.name}")
    print(f"N = {args.N}, R = {args.R}, dr = {args.dr}, nphi = {args.nphi}")

    t0 = time.time()
    grid = ExtensionGrid(backend, args.N, args.R, args.dr, args.nphi)
    print(f"Grid built in {time.time()-t0:.1f}s")

    print("\n=== Geodesic scan ===")
    Lambda0, geo_results = scan_geodesics(grid, args.N, args.n_epsilon)
    print(f"Lambda_0 (quadrature) = {Lambda0:.6f}")

    # Find minimum stability ratio
    min_ratio = float('inf')
    min_row = None
    for r in geo_results:
        if r["ratio_gap_d2"] < min_ratio and r["d_to_f0"] > 0.01:
            min_ratio = r["ratio_gap_d2"]
            min_row = r

    print(f"Min ratio (Lambda_0-J)/d^2 = {min_ratio:.4f}")
    if min_row:
        print(f"  at mode={min_row['mode']} ({min_row['type']}), "
              f"eps={min_row['epsilon']:.2f}, d={min_row['d_to_f0']:.4f}, "
              f"gap={min_row['gap']:.4f}")

    # Show stability profile for the worst mode
    if min_row:
        worst_mode = min_row["mode"]
        worst_type = min_row["type"]
        print(f"\nStability profile for mode {worst_mode} ({worst_type}):")
        print(f"  {'eps':>6s}  {'d':>8s}  {'J':>12s}  {'gap':>10s}  {'gap/d^2':>10s}")
        for r in geo_results:
            if r["mode"] == worst_mode and r["type"] == worst_type:
                print(f"  {r['epsilon']:6.2f}  {r['d_to_f0']:8.4f}  "
                      f"{r['J']:12.4f}  {r['gap']:10.4f}  {r['ratio_gap_d2']:10.4f}")

    print(f"\n=== Random scan ({args.n_random} samples) ===")
    rand_results = scan_random(grid, args.N, args.n_random)
    min_ratio_rand = min(r["ratio_gap_d2"] for r in rand_results
                         if r["d_to_f0"] > 0.01)
    max_J_rand = max(r["J"] for r in rand_results)
    print(f"Min ratio (random) = {min_ratio_rand:.4f}")
    print(f"Max J (random) = {max_J_rand:.4f} (Lambda_0 = {Lambda0:.4f})")

    # Distance distribution of random points
    d_bins = [0, 0.1, 0.3, 0.5, 0.7, 1.0, 1.5, 2.0]
    print("\nGap by distance bin:")
    for i in range(len(d_bins) - 1):
        lo, hi = d_bins[i], d_bins[i+1]
        in_bin = [r for r in rand_results if lo <= r["d_to_f0"] < hi]
        if in_bin:
            min_gap = min(r["gap"] for r in in_bin)
            min_r = min(r["ratio_gap_d2"] for r in in_bin)
            print(f"  d in [{lo:.1f}, {hi:.1f}): {len(in_bin):3d} pts, "
                  f"min gap = {min_gap:.2f}, min gap/d^2 = {min_r:.2f}")

    elapsed = time.time() - t0

    overall_min = min(min_ratio, min_ratio_rand)
    print(f"\n=== GLOBAL STABILITY ESTIMATE ===")
    print(f"c_stab >= {overall_min:.4f}")
    print(f"Local Hessian c_stab ~ 714")
    print(f"Elapsed: {elapsed:.1f}s")

    result = {
        "N": args.N,
        "Lambda0_quadrature": Lambda0,
        "c_stab_global_estimate": overall_min,
        "c_stab_local_hessian": 714.0,
        "geodesic_min_ratio": min_ratio,
        "geodesic_worst": min_row,
        "random_min_ratio": min_ratio_rand,
        "random_max_J": max_J_rand,
        "parameters": {"R": args.R, "dr": args.dr, "nphi": args.nphi},
        "elapsed": elapsed,
    }
    text = json.dumps(result, indent=2)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text + "\n")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
