"""Numerical illustration 1: the gain as a function of depth and resolution (Example ex:iso, Corollary cor:sched).

Protocol, fixed before running:
  d = 4, N = 8, X_1 = [I_4 I_4]/sqrt(2).
  Teacher A: W_l = I_4 (fixed).  Teacher B: W_l = I_4 + V_l, entries of V_l iid uniform on [-1/32, 1/32] (random).
  nu in {1e-4, 1e-3, 1e-2, 5e-2}; step Delta with Delta^2/12 = gamma*nu/d, gamma = 1 (A) or 1 + d a^2/3 (B).
  Strengths: all 0, all 1/2, all 1.  Depths read off one run of depth 64: L in {1, 2, 4, 8, 16, 32, 64}.
  The actual algorithm is run: corrected target with the Gram inverse, entrywise subtractive dither, propagate.
  The same dither draws are used for the three strengths (variance reduction only; the rounding errors differ).
  Teacher A: 20000 runs.  Teacher B: 100 teachers x 200 dither draws; standard errors clustered by teacher.
Reported: q_L = E||delta_{L+1}||^2 / E||X_{L+1}||^2 against q_L = [(1-alpha)^2 + nu] q_{L-1} + nu.
"""
import json
import math
import random
import sys
from la import mm, add, eye, fro2, quantize_dither, corrected_target

D, N, LMAX = 4, 8, 64
DEPTHS = [1, 2, 4, 8, 16, 32, 64]
NUS = [1e-4, 1e-3, 1e-2, 5e-2]
ALPHAS = [0.0, 0.5, 1.0]
A_TEACH = 1.0 / 32
X1 = [[(1.0 if j % D == i else 0.0) / math.sqrt(2) for j in range(N)] for i in range(D)]


def run_once(Ws, Xs, step, alpha, seed):
    rng = random.Random(seed)
    Z = X1
    errs = {}
    for l in range(LMAX):
        Wt = corrected_target(Ws[l], Xs[l], Z, alpha if l > 0 else 0.0)
        Q = quantize_dither(Wt, step, rng)
        Z = mm(Q, Z)
        if l + 1 in DEPTHS:
            errs[l + 1] = fro2(add(Z, Xs[l + 1], -1.0))
    return errs


def teacher(rng):
    if rng is None:
        Ws = [eye(D) for _ in range(LMAX)]
    else:
        Ws = [[[(1.0 if i == j else 0.0) + (2 * rng.random() - 1) * A_TEACH for j in range(D)] for i in range(D)] for _ in range(LMAX)]
    Xs = [X1]
    for W in Ws:
        Xs.append(mm(W, Xs[-1]))
    return Ws, Xs


def theory(nu, alpha, L):
    q = 0.0
    for _ in range(L):
        q = ((1 - alpha) ** 2 + nu) * q + nu
    return q


def main():
    out = {"protocol": __doc__, "fixed": [], "random": []}
    # ---- teacher A (fixed identity) ----
    Ws, Xs = teacher(None)
    n_runs = 20000
    for nu in NUS:
        step = math.sqrt(12 * nu / D)
        acc = {(a, L): [0.0, 0.0] for a in ALPHAS for L in DEPTHS}
        for r in range(n_runs):
            for a in ALPHAS:
                e = run_once(Ws, Xs, step, a, 10_000 + r)
                for L in DEPTHS:
                    v = e[L] / fro2(Xs[L])
                    acc[(a, L)][0] += v
                    acc[(a, L)][1] += v * v
        for a in ALPHAS:
            for L in DEPTHS:
                m = acc[(a, L)][0] / n_runs
                se = math.sqrt(max(acc[(a, L)][1] / n_runs - m * m, 0.0) / n_runs)
                out["fixed"].append(dict(nu=nu, alpha=a, L=L, q_sim=m, se=se, q_theory=theory(nu, a, L)))
        print("fixed teacher, nu =", nu, "done", file=sys.stderr, flush=True)
    # ---- teacher B (random near identity) ----
    gamma = 1 + D * A_TEACH ** 2 / 3
    n_teach, n_dith = 100, 200
    for nu in NUS:
        step = math.sqrt(12 * gamma * nu / D)
        num = {(a, L): [] for a in ALPHAS for L in DEPTHS}      # per-teacher mean error
        den = {L: [] for L in DEPTHS}                           # per-teacher signal energy
        for k in range(n_teach):
            Ws, Xs = teacher(random.Random(777_000 + k))
            for L in DEPTHS:
                den[L].append(fro2(Xs[L]))
            tmp = {(a, L): 0.0 for a in ALPHAS for L in DEPTHS}
            for r in range(n_dith):
                for a in ALPHAS:
                    e = run_once(Ws, Xs, step, a, 50_000_000 + 1000 * k + r)
                    for L in DEPTHS:
                        tmp[(a, L)] += e[L] / n_dith
            for key, v in tmp.items():
                num[key].append(v)
        for a in ALPHAS:
            for L in DEPTHS:
                mnum = sum(num[(a, L)]) / n_teach
                mden = sum(den[L]) / n_teach
                q = mnum / mden
                # delta-method standard error of a ratio of means, clustered by teacher
                res = [x - q * y for x, y in zip(num[(a, L)], den[L])]
                se = math.sqrt(sum(v * v for v in res) / (n_teach - 1) / n_teach) / mden
                out["random"].append(dict(nu=nu, alpha=a, L=L, q_sim=q, se=se, q_theory=theory(nu, a, L)))
        print("random teacher, nu =", nu, "done", file=sys.stderr, flush=True)
    json.dump(out, open("sim1_gain_depth.json", "w"), indent=1)
    print("written sim1_gain_depth.json")


if __name__ == "__main__":
    main()
