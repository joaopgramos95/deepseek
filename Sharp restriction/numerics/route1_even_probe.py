#!/usr/bin/env python3
"""Floating-point Route 1 probe for the annular eigenvalue exclusion.

This is deliberately *not* a proof.  It tests whether the restricted
annular eigenvalue search is computationally plausible before replacing
the pieces by Arb/interval arithmetic.

Restriction used here:
  f(theta) = b_0 + sum_{j=1}^M b_j cos(2j theta),
  f real, antipodally even, and mesh-positive.

The restriction removes phase, rotation, and translation complications.  It
also makes Ef real-valued because i^(2j)=(-1)^j.  For such f we compute

  J(f) = ||Ef||_6^6,
  T(f) = E^*((Ef)^5),
  residual = P_N T(f) - J(f) f.

The script scans the normalized coefficient sphere outside a local ball
around the constant and reports the smallest residual seen in a chosen
Lambda slab [Lambda0, Lambda0 + eta].
"""

from __future__ import annotations

import argparse
import ctypes
import json
import math
import random
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


def simpson_weights(R: float, dr: float) -> tuple[list[float], list[float]]:
    steps = int(round(R / dr))
    if steps % 2:
        steps += 1
    dr = R / steps
    rvals = [k * dr for k in range(steps + 1)]
    weights = []
    for k, r in enumerate(rvals):
        if k == 0 or k == steps:
            w = dr / 3.0
        elif k % 2:
            w = 4.0 * dr / 3.0
        else:
            w = 2.0 * dr / 3.0
        weights.append(w * r)
    return rvals, weights


class EvenCosineModel:
    def __init__(self, modes: int, R: float, dr: float, nphi: int) -> None:
        self.modes = modes
        self.orders = [2 * j for j in range(modes + 1)]
        self.backend = BesselBackend()
        self.rvals, self.rweights = simpson_weights(R, dr)
        self.nphi = nphi
        self.phis = [TWO_PI * j / nphi for j in range(nphi)]
        self.phi_weight = TWO_PI / nphi
        self.bessel = [
            [self.backend.j(order, r) for r in self.rvals]
            for order in self.orders
        ]
        self.cos = [
            [math.cos(order * phi) for phi in self.phis]
            for order in self.orders
        ]
        # E(cos(2j theta)) = 2*pi*(-1)^j J_{2j}(r) cos(2j phi).
        self.signs = [1.0 if j % 2 == 0 else -1.0 for j in range(modes + 1)]
        self.basis = []
        for j in range(modes + 1):
            rows = []
            for ir in range(len(self.rvals)):
                row = [
                    TWO_PI * self.signs[j] * self.bessel[j][ir] * self.cos[j][ip]
                    for ip in range(nphi)
                ]
                rows.append(row)
            self.basis.append(rows)

    def x_to_b(self, x: list[float]) -> list[float]:
        # x_0 = sqrt(2*pi) b_0; x_j = sqrt(pi) b_j for j >= 1.
        b = [x[0] / math.sqrt(TWO_PI)]
        b.extend(xj / math.sqrt(math.pi) for xj in x[1:])
        return b

    def b_to_x(self, b: list[float]) -> list[float]:
        x = [math.sqrt(TWO_PI) * b[0]]
        x.extend(math.sqrt(math.pi) * bj for bj in b[1:])
        return x

    def normalize_x(self, x: list[float]) -> list[float]:
        nrm = math.sqrt(sum(v * v for v in x))
        if nrm == 0:
            raise ValueError("zero vector")
        if x[0] < 0:
            nrm = -nrm
        return [v / nrm for v in x]

    def distance_to_constant(self, x: list[float]) -> float:
        return math.sqrt((x[0] - 1.0) ** 2 + sum(v * v for v in x[1:]))

    def min_on_theta_mesh(self, b: list[float], ntheta: int) -> float:
        best = float("inf")
        for k in range(ntheta):
            theta = TWO_PI * k / ntheta
            val = b[0]
            for j in range(1, self.modes + 1):
                val += b[j] * math.cos(2 * j * theta)
            best = min(best, val)
        return best

    def evaluate(self, x: list[float]) -> dict:
        b = self.x_to_b(x)
        inner = [0.0 for _ in range(self.modes + 1)]
        J = 0.0

        for ir, rw in enumerate(self.rweights):
            if rw == 0.0:
                continue
            for ip in range(self.nphi):
                u = 0.0
                for j, bj in enumerate(b):
                    u += bj * self.basis[j][ir][ip]
                u5 = u ** 5
                J += rw * self.phi_weight * u5 * u
                for j in range(self.modes + 1):
                    inner[j] += rw * self.phi_weight * u5 * self.basis[j][ir][ip]

        # If T(f)=sum t_j cos(2j theta), then
        # <T(f),1> = 2*pi t_0 and <T(f),cos(2j theta)> = pi t_j.
        t = [inner[0] / TWO_PI]
        t.extend(inner[j] / math.pi for j in range(1, self.modes + 1))

        residual_b = [tj - J * bj for tj, bj in zip(t, b)]
        residual_x = [math.sqrt(TWO_PI) * residual_b[0]]
        residual_x.extend(math.sqrt(math.pi) * rb for rb in residual_b[1:])
        residual_norm = math.sqrt(sum(v * v for v in residual_x))
        return {
            "b": b,
            "J": J,
            "T_coeffs": t,
            "residual_norm": residual_norm,
            "residual_x": residual_x,
            "distance": self.distance_to_constant(x),
        }


def random_sphere_point(dim: int, rng: random.Random) -> list[float]:
    x = [rng.gauss(0.0, 1.0) for _ in range(dim)]
    if x[0] < 0:
        x[0] *= -1.0
    nrm = math.sqrt(sum(v * v for v in x))
    return [v / nrm for v in x]


def geodesic_point(direction: list[float], rho: float) -> list[float]:
    # Unit sphere point at Euclidean distance rho from e_0.
    # If x=(cos alpha, sin alpha d), then ||x-e0||=2 sin(alpha/2).
    alpha = 2.0 * math.asin(min(1.0, max(0.0, rho / 2.0)))
    return [math.cos(alpha)] + [math.sin(alpha) * v for v in direction]


def unit_direction(dim_tail: int, rng: random.Random) -> list[float]:
    v = [rng.gauss(0.0, 1.0) for _ in range(dim_tail)]
    nrm = math.sqrt(sum(z * z for z in v))
    return [z / nrm for z in v]


def local_descent(model: EvenCosineModel, x0: list[float], eta: float,
                  lambda0: float, r0: float, positive_mesh: int,
                  steps: int, rng: random.Random) -> tuple[list[float], dict]:
    """Crude derivative-free descent for a penalty target.

    The target is residual^2 plus penalties for missing the Lambda slab,
    positivity, and the annulus.
    """
    x = x0[:]
    ev = model.evaluate(x)
    b = ev["b"]

    def score(xcand: list[float]) -> tuple[float, dict]:
        e = model.evaluate(xcand)
        minval = model.min_on_theta_mesh(e["b"], positive_mesh)
        lower = lambda0
        upper = lambda0 + eta
        slab_pen = max(0.0, lower - e["J"], e["J"] - upper)
        ann_pen = max(0.0, r0 - e["distance"])
        pos_pen = max(0.0, -minval)
        # Keep these penalties large: this search is meant to find plausible
        # constrained residual zeros, not just slide back to the known constant.
        s = (
            e["residual_norm"] ** 2
            + 1.0e4 * (slab_pen / max(1.0, eta)) ** 2
            + 1.0e6 * ann_pen ** 2
            + 1.0e6 * pos_pen ** 2
        )
        e["min_value"] = minval
        e["slab_penalty"] = slab_pen
        e["annulus_penalty"] = ann_pen
        e["positivity_penalty"] = pos_pen
        e["feasible_for_probe"] = (
            slab_pen <= 1.0e-8 and ann_pen <= 1.0e-8 and pos_pen <= 1.0e-8
        )
        e["score"] = s
        return s, e

    best_score, best = score(x)
    step = 0.25
    dim = len(x)
    for _ in range(steps):
        proposal = [x[j] + step * rng.gauss(0.0, 1.0) for j in range(dim)]
        proposal = model.normalize_x(proposal)
        s, e = score(proposal)
        if s < best_score:
            x, best_score, best = proposal, s, e
            step *= 1.03
        else:
            step *= 0.995
    return x, best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--modes", type=int, default=3,
                        help="Use modes cos(0), cos(2 theta), ..., cos(2M theta).")
    parser.add_argument("--R", type=float, default=160.0)
    parser.add_argument("--dr", type=float, default=0.08)
    parser.add_argument("--nphi", type=int, default=96)
    parser.add_argument("--eta-rel", type=float, default=1.0e-3)
    parser.add_argument("--r0", type=float, default=0.13)
    parser.add_argument("--positive-mesh", type=int, default=720)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--descent-starts", type=int, default=60)
    parser.add_argument("--descent-steps", type=int, default=400)
    parser.add_argument("--seed", type=int, default=1234)
    parser.add_argument("--output", type=Path,
                        default=Path("numerics/results/route1_even_probe.json"))
    args = parser.parse_args()

    rng = random.Random(args.seed)
    t0 = time.time()
    model = EvenCosineModel(args.modes, args.R, args.dr, args.nphi)
    print(f"Backend: {model.backend.name}")
    print(f"Model: even cosine modes 0..{2*args.modes}, "
          f"grid {len(model.rvals)} x {args.nphi}")

    x_const = [1.0] + [0.0] * args.modes
    ev0 = model.evaluate(x_const)
    lambda0 = ev0["J"]
    eta = args.eta_rel * lambda0
    print(f"Lambda0(grid) = {lambda0:.8f}")
    print(f"Searching slab [Lambda0, Lambda0 + eta], eta = {eta:.6g} "
          f"({args.eta_rel:g} Lambda0)")
    print(f"Annulus: distance >= {args.r0}")

    candidates = []

    # Deterministic one-direction geodesic scans.
    for j in range(1, args.modes + 1):
        direction = [0.0] * args.modes
        direction[j - 1] = 1.0
        for rho_i in range(1, 120):
            rho = args.r0 + rho_i * (1.6 - args.r0) / 120.0
            x = geodesic_point(direction, rho)
            ev = model.evaluate(x)
            ev["min_value"] = model.min_on_theta_mesh(ev["b"], args.positive_mesh)
            ev["source"] = f"geodesic_cos{2*j}"
            if ev["min_value"] >= -1e-6:
                candidates.append((x, ev))

    # Random positive-ish samples.
    for _ in range(args.samples):
        x = random_sphere_point(args.modes + 1, rng)
        ev = model.evaluate(x)
        ev["min_value"] = model.min_on_theta_mesh(ev["b"], args.positive_mesh)
        ev["source"] = "random"
        if ev["distance"] >= args.r0 and ev["min_value"] >= -1e-6:
            candidates.append((x, ev))

    in_slab = [
        (x, ev) for x, ev in candidates
        if lambda0 <= ev["J"] <= lambda0 + eta
    ]
    near_slab = sorted(
        candidates,
        key=lambda xe: max(lambda0 - xe[1]["J"], xe[1]["J"] - (lambda0 + eta), 0.0)
                    + 0.01 * xe[1]["residual_norm"],
    )[:args.descent_starts]

    best_any = min(candidates, key=lambda xe: xe[1]["residual_norm"], default=None)
    best_slab = min(in_slab, key=lambda xe: xe[1]["residual_norm"], default=None)

    print(f"Positive annular candidates sampled: {len(candidates)}")
    print(f"Candidates in Lambda slab: {len(in_slab)}")
    if best_any:
        print("Best residual among all positive annular samples:")
        print(f"  source={best_any[1]['source']} d={best_any[1]['distance']:.4f} "
              f"J-L0={best_any[1]['J']-lambda0:.4g} "
              f"res={best_any[1]['residual_norm']:.4g} "
              f"min f={best_any[1]['min_value']:.4g}")
    if best_slab:
        print("Best residual inside slab:")
        print(f"  source={best_slab[1]['source']} d={best_slab[1]['distance']:.4f} "
              f"J-L0={best_slab[1]['J']-lambda0:.4g} "
              f"res={best_slab[1]['residual_norm']:.4g} "
              f"min f={best_slab[1]['min_value']:.4g}")

    print(f"Running local penalty descent from {len(near_slab)} starts...")
    descent_results = []
    for x, _ in near_slab:
        _, ev = local_descent(
            model, x, eta, lambda0, args.r0, args.positive_mesh,
            args.descent_steps, rng,
        )
        descent_results.append(ev)
    descent_results.sort(key=lambda e: e["score"])
    best_descent = descent_results[0] if descent_results else None
    feasible_descent = [e for e in descent_results if e.get("feasible_for_probe")]
    best_feasible_descent = (
        min(feasible_descent, key=lambda e: e["residual_norm"])
        if feasible_descent else None
    )
    if best_descent:
        print("Best penalty-descent result:")
        print(f"  score={best_descent['score']:.4g} d={best_descent['distance']:.4f} "
              f"J-L0={best_descent['J']-lambda0:.4g} "
              f"res={best_descent['residual_norm']:.4g} "
              f"min f={best_descent['min_value']:.4g} "
              f"feasible={best_descent['feasible_for_probe']}")
        print(f"  b={['%.6g' % z for z in best_descent['b']]}")
    if best_feasible_descent:
        print("Best feasible descent result:")
        print(f"  d={best_feasible_descent['distance']:.4f} "
              f"J-L0={best_feasible_descent['J']-lambda0:.4g} "
              f"res={best_feasible_descent['residual_norm']:.4g} "
              f"min f={best_feasible_descent['min_value']:.4g}")

    result = {
        "rigorous": False,
        "warning": "Floating-point restricted probe only; not an exclusion proof.",
        "backend": model.backend.name,
        "modes": args.modes,
        "orders": model.orders,
        "R": args.R,
        "dr": args.dr,
        "nphi": args.nphi,
        "eta_rel": args.eta_rel,
        "eta": eta,
        "r0": args.r0,
        "Lambda0_grid": lambda0,
        "positive_annular_candidates": len(candidates),
        "candidates_in_slab": len(in_slab),
        "best_any": best_any[1] if best_any else None,
        "best_slab": best_slab[1] if best_slab else None,
        "best_descent": best_descent,
        "best_feasible_descent": best_feasible_descent,
        "elapsed_seconds": time.time() - t0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Wrote {args.output}")
    print(f"Elapsed: {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
