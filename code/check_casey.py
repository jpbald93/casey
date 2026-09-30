#!/usr/bin/env python3
"""Numeric check of Casey's theorem, mirroring the Lean definitions.

c_i = O + (1 - r_i/R)(T_i - O),  t_ij = sqrt(|c_i c_j|^2 - (r_i - r_j)^2).
Positive test: T_1..T_4 in cyclic order on Gamma, 0 <= r_i < R:
    t12*t34 + t23*t41 == t13*t24   (to 1e-9 relative)
Negative control: same circles, points in NON-cyclic order (T1,T3,T2,T4): identity fails.
Also checks the signed (externally tangent, r_i < 0) variant from `casey_of_le`.
"""
import math
import random


def centre(O, T, R, r):
    k = 1 - r / R
    return (O[0] + k * (T[0] - O[0]), O[1] + k * (T[1] - O[1]))


def tlen(c1, c2, r1, r2):
    d2 = (c1[0] - c2[0]) ** 2 + (c1[1] - c2[1]) ** 2
    v = d2 - (r1 - r2) ** 2
    assert v > -1e-9, v
    return math.sqrt(max(v, 0.0))


def casey_residual(O, R, Ts, rs):
    c = [centre(O, T, R, r) for T, r in zip(Ts, rs)]
    t = lambda i, j: tlen(c[i], c[j], rs[i], rs[j])
    lhs = t(0, 1) * t(2, 3) + t(1, 2) * t(3, 0)
    rhs = t(0, 2) * t(1, 3)
    return abs(lhs - rhs) / max(1.0, abs(rhs)), lhs, rhs


def rand_config(rng, signed=False):
    O = (rng.uniform(-5, 5), rng.uniform(-5, 5))
    R = rng.uniform(0.5, 10)
    angs = sorted(rng.uniform(0, 2 * math.pi) for _ in range(4))
    Ts = [(O[0] + R * math.cos(a), O[1] + R * math.sin(a)) for a in angs]
    lo = -2 * R if signed else 0.0
    rs = [rng.uniform(lo, R * 0.999) for _ in range(4)]
    if rng.random() < 0.2:  # sometimes point-circles
        rs[rng.randrange(4)] = 0.0
    return O, R, Ts, rs


def main():
    rng = random.Random(20260930)
    N = 20000
    worst = 0.0
    for _ in range(N):
        O, R, Ts, rs = rand_config(rng)
        worst = max(worst, casey_residual(O, R, Ts, rs)[0])
    print(f"positive (internal, 0<=r<R): N={N} worst rel residual = {worst:.3e}")
    assert worst < 1e-9

    worst_s = 0.0
    for _ in range(N):
        O, R, Ts, rs = rand_config(rng, signed=True)
        worst_s = max(worst_s, casey_residual(O, R, Ts, rs)[0])
    print(f"signed radii (r<=R, some external): N={N} worst rel residual = {worst_s:.3e}")
    assert worst_s < 1e-9

    fails, min_res = 0, float("inf")
    for _ in range(N):
        O, R, Ts, rs = rand_config(rng)
        Ts2 = [Ts[0], Ts[2], Ts[1], Ts[3]]
        rs2 = [rs[0], rs[2], rs[1], rs[3]]
        res = casey_residual(O, R, Ts2, rs2)[0]
        min_res = min(min_res, res)
        if res > 1e-6:
            fails += 1
    print(f"negative control (non-cyclic order): {fails}/{N} violate identity by >1e-6; "
          f"min residual {min_res:.3e}")
    assert fails > 0.99 * N

    # degenerate: all radii 0 -> Ptolemy
    O, R, Ts, _ = rand_config(rng)
    print("all radii 0 (Ptolemy): residual = %.3e" % casey_residual(O, R, Ts, [0] * 4)[0])
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
