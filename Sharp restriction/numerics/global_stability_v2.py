#!/usr/bin/env python3
"""Global stability estimate, v2: quotient out symmetries correctly.

The symmetry group G = U(1) x SO(2) x R^2 acts on S^1 densities.
For real functions near the constant f_0:
  - Phase (U(1)): fixes f_0 (already quotiented for real functions).
  - Rotation (SO(2)): fixes f_0 (constant is rotationally invariant).
  - Translation (R^2): acts by modulation e^{-ix_0.omega}, producing
    mode-1 perturbations. The direction sin(theta) IS a translation.

So d_G(g, f_0) = ||g - f_0|| after projecting out modes n = +/-1.
We restrict the search to g with hat{g}(+/-1) = 0, i.e., modes >= 2.

The stability modulus is:
  c_stab = inf_{g: modes >= 2, ||g||=1} (Lambda_0 - J(g)) / ||g - f_0||^2
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
    def __init__(self, backend, N_modes, R, dr, nphi):
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
                w = self.dr / 3
            elif k % 2:
                w = 4 * self.dr / 3
            else:
                w = 2 * self.dr / 3
            self.rweights.append(w * self.rvals[k] if k > 0 else 0.0)
        self.phis = [TWO_PI * j / nphi for j in range(nphi)]
        self.phi_weight = TWO_PI / nphi
        self.bessel = [[backend.j(m, r) for r in self.rvals]
                       for m in range(N_modes + 1)]
        self.i_pow = [(1,0), (0,1), (-1,0), (0,-1)]

    def compute_J(self, a_cos, a_sin):
        """J(g) = ||Eg||_6^6 for real g with given cosine/sine coefficients.

        For real g, Ef is real-valued:
        Ef(r,phi) = 2*pi*a_0*J_0(r)
                  + sum_{m>=1} 4*pi*J_m(r)*Re[i^m * a_m * e^{im*phi}]
        where a_m = (a_cos[m] - i*a_sin[m])/2.
        """
        total = 0.0
        for ir, rw in enumerate(self.rweights):
            if rw == 0: continue
            for jp in range(self.nphi):
                phi = self.phis[jp]
                u = TWO_PI * a_cos[0] * self.bessel[0][ir]
                for m in range(1, self.N + 1):
                    jm = self.bessel[m][ir]
                    cos_mp = math.cos(m * phi)
                    sin_mp = math.sin(m * phi)
                    cm = math.cos(m * math.pi / 2)
                    sm = math.sin(m * math.pi / 2)
                    ac, asn = a_cos[m], a_sin[m]
                    # Re[i^m * (ac - i*as)/2 * e^{im*phi}]
                    alpha = (cm * ac + sm * asn) / 2
                    beta  = (sm * ac - cm * asn) / 2
                    u += TWO_PI * jm * 2 * (alpha * cos_mp - beta * sin_mp)
                total += rw * self.phi_weight * u**6
        return total


def normalize(a_cos, a_sin):
    norm2 = TWO_PI * a_cos[0]**2
    for m in range(1, len(a_cos)):
        norm2 += math.pi * (a_cos[m]**2 + a_sin[m]**2)
    s = 1.0 / math.sqrt(norm2)
    return [c*s for c in a_cos], [c*s for c in a_sin]


def dist_to_f0_modG(a_cos, a_sin):
    """||g - f_0|| excluding mode-1 (translation) contribution.
    d_G^2 = 2*pi*(a0 - f0_a0)^2 + sum_{|n|>=2} pi*(a_cos[n]^2 + a_sin[n]^2)
    """
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    d2 = TWO_PI * (a_cos[0] - f0_a0)**2
    for m in range(2, len(a_cos)):  # skip m=1
        d2 += math.pi * (a_cos[m]**2 + a_sin[m]**2)
    return math.sqrt(d2)


def scan_one_mode_geodesics(grid, N, n_eps=40):
    """Geodesics from f_0 toward cos(n*theta) and sin(n*theta) for n >= 2."""
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    Lambda0 = grid.compute_J([f0_a0] + [0.0]*N, [0.0]*(N+1))

    results = []
    for mode in range(2, N + 1):
        for mtype in ["cos", "sin"]:
            for ie in range(1, n_eps + 1):
                eps = ie * 0.04
                a_cos = [1.0] + [0.0]*N
                a_sin = [0.0]*(N+1)
                if mtype == "cos": a_cos[mode] = eps
                else: a_sin[mode] = eps
                a_cos, a_sin = normalize(a_cos, a_sin)
                d = dist_to_f0_modG(a_cos, a_sin)
                if d < 1e-10: continue
                J = grid.compute_J(a_cos, a_sin)
                gap = Lambda0 - J
                results.append({
                    "mode": mode, "type": mtype, "eps": round(eps,3),
                    "d_G": round(d, 6), "J": round(J, 4),
                    "gap": round(gap, 4), "ratio": round(gap/d**2, 2),
                })
    return Lambda0, results


def scan_random_no_mode1(grid, N, n_samples, seed=42):
    """Random on band-limited sphere with mode-1 zeroed out."""
    rng = random.Random(seed)
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    Lambda0 = grid.compute_J([f0_a0]+[0.0]*N, [0.0]*(N+1))

    results = []
    for _ in range(n_samples):
        a_cos = [rng.gauss(0,1)] + [0.0] + [rng.gauss(0,1) for _ in range(2, N+1)]
        a_sin = [0.0, 0.0] + [rng.gauss(0,1) for _ in range(2, N+1)]
        a_cos, a_sin = normalize(a_cos, a_sin)
        d = dist_to_f0_modG(a_cos, a_sin)
        if d < 1e-10: continue
        J = grid.compute_J(a_cos, a_sin)
        gap = Lambda0 - J
        results.append({
            "d_G": d, "J": J, "gap": gap, "ratio": gap/d**2,
        })
    return results


def scan_two_mode_mix(grid, N, n_pts=20):
    """Mix two modes simultaneously for a 2D search."""
    f0_a0 = 1.0 / math.sqrt(TWO_PI)
    Lambda0 = grid.compute_J([f0_a0]+[0.0]*N, [0.0]*(N+1))
    results = []
    for m1 in range(2, min(N+1, 6)):
        for m2 in range(m1, min(N+1, 6)):
            for i1 in range(-n_pts, n_pts+1):
                for i2 in range(-n_pts, n_pts+1):
                    e1 = i1 * 0.06
                    e2 = i2 * 0.06
                    if abs(e1) + abs(e2) < 0.01: continue
                    a_cos = [1.0]+[0.0]*N
                    a_sin = [0.0]*(N+1)
                    a_cos[m1] = e1; a_cos[m2] = e2
                    a_cos, a_sin = normalize(a_cos, a_sin)
                    d = dist_to_f0_modG(a_cos, a_sin)
                    if d < 1e-10: continue
                    J = grid.compute_J(a_cos, a_sin)
                    gap = Lambda0 - J
                    results.append({
                        "modes": [m1,m2], "eps": [round(e1,3),round(e2,3)],
                        "d_G": d, "J": J, "gap": gap, "ratio": gap/d**2,
                    })
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--N", type=int, default=6)
    parser.add_argument("--R", type=float, default=200.0)
    parser.add_argument("--dr", type=float, default=0.1)
    parser.add_argument("--nphi", type=int, default=128)
    parser.add_argument("--n-epsilon", type=int, default=35)
    parser.add_argument("--n-random", type=int, default=500)
    parser.add_argument("--output", type=Path,
                        default=Path("numerics/results/global_stability_v2.json"))
    args = parser.parse_args()

    backend = BesselBackend()
    print(f"Backend: {backend.name}, N={args.N}, R={args.R}")

    t0 = time.time()
    grid = ExtensionGrid(backend, args.N, args.R, args.dr, args.nphi)
    print(f"Grid: {grid.nr} radial x {grid.nphi} angular, built in {time.time()-t0:.1f}s")

    print("\n=== One-mode geodesics (modes >= 2, no translations) ===")
    Lambda0, geo = scan_one_mode_geodesics(grid, args.N, args.n_epsilon)
    print(f"Lambda_0 (quadrature at R={args.R}) = {Lambda0:.6f}")

    # Print stability profile for each mode
    for mode in range(2, args.N+1):
        for mtype in ["cos", "sin"]:
            subset = [r for r in geo if r["mode"]==mode and r["type"]==mtype]
            if not subset: continue
            min_r = min(r["ratio"] for r in subset if r["d_G"] > 0.01)
            best = min(subset, key=lambda r: r["ratio"] if r["d_G"]>0.01 else 1e18)
            sign = "+" if min_r > 0 else "!!NEG!!"
            print(f"  mode {mode:2d} {mtype:3s}: min ratio = {min_r:10.2f} {sign}"
                  f"  (at d={best['d_G']:.3f}, gap={best['gap']:.2f})")

    all_geo_pos = [r for r in geo if r["d_G"] > 0.01]
    min_ratio_geo = min(r["ratio"] for r in all_geo_pos) if all_geo_pos else float('inf')

    print(f"\n=== Random scan (modes >= 2, {args.n_random} samples) ===")
    rand = scan_random_no_mode1(grid, args.N, args.n_random)
    rand_pos = [r for r in rand if r["d_G"] > 0.01]
    min_ratio_rand = min(r["ratio"] for r in rand_pos) if rand_pos else float('inf')
    max_J_rand = max(r["J"] for r in rand_pos) if rand_pos else 0

    d_bins = [0, 0.05, 0.1, 0.2, 0.4, 0.6, 0.8, 1.0, 1.4]
    print(f"  Max J = {max_J_rand:.4f}, Lambda_0 = {Lambda0:.4f}")
    for i in range(len(d_bins)-1):
        lo, hi = d_bins[i], d_bins[i+1]
        inb = [r for r in rand_pos if lo <= r["d_G"] < hi]
        if inb:
            mg = min(r["gap"] for r in inb)
            mr = min(r["ratio"] for r in inb)
            print(f"  d_G in [{lo:.2f},{hi:.2f}): {len(inb):3d} pts, "
                  f"min gap={mg:8.2f}, min ratio={mr:8.2f}")

    overall = min(min_ratio_geo, min_ratio_rand)
    print(f"\n{'='*60}")
    print(f"GLOBAL STABILITY ESTIMATE: c_stab >= {overall:.2f}")
    print(f"Local Hessian value: c_stab_local ~ 714")
    print(f"Global/Local ratio: {overall/714:.4f}")
    if overall > 0:
        print(f"STABLE: J(g) < Lambda_0 for all tested g != f_0 (mod G)")
    else:
        print(f"UNSTABLE: found g with J(g) > Lambda_0!")
    print(f"Elapsed: {time.time()-t0:.1f}s")

    result = {
        "N": args.N, "Lambda0": Lambda0,
        "c_stab_global": overall,
        "c_stab_local": 714.0,
        "geodesic_min": min_ratio_geo,
        "random_min": min_ratio_rand,
        "mix_min": min_ratio_mix,
        "stable": overall > 0,
        "elapsed": time.time()-t0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
