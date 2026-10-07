"""Cross-check of the pure-Python computations with NumPy.

Two kinds of check.
 (A) Same inputs, two implementations: the hand-written linear algebra of la.py against NumPy, on random matrices
     and on complete runs of the algorithm with identical dither draws.  Agreement should be at rounding level.
 (B) Independent reruns: the three computations are repeated with NumPy's own random generator and a separate
     implementation of the algorithm (np.linalg.solve instead of an explicit inverse).  Agreement should be within
     the Monte Carlo standard errors; the exact enumeration of sim3 part (b) should agree at rounding level.

Run with an interpreter that has NumPy:  python crosscheck_numpy.py
"""
import itertools
import json
import math
import os
import random
import numpy as np
import la
import sim1_gain_depth as S1
import sim2_gain_split as S2

out = {}

# ---------------------------------------------------------------- (A1) primitives
rng = random.Random(1)
worst_inv = worst_tgt = 0.0
for _ in range(2000):
    n = rng.randint(2, 8)
    m = n + rng.randint(0, 8)
    A = [[rng.gauss(0, 1) for _ in range(n)] for _ in range(n)]
    worst_inv = max(worst_inv, np.abs(np.array(la.inv(A)) - np.linalg.inv(np.array(A))).max() / max(1.0, np.abs(np.linalg.inv(np.array(A))).max()))
    r = rng.randint(1, n)
    W = [[rng.gauss(0, 1) for _ in range(n)] for _ in range(r)]
    X = [[rng.gauss(0, 1) for _ in range(m)] for _ in range(n)]
    Z = [[x + 0.1 * rng.gauss(0, 1) for x in row] for row in X]
    a = rng.random()
    Wn, Xn, Zn = map(np.array, (W, X, Z))
    ref = Wn + a * np.linalg.solve(Zn @ Zn.T, Zn @ (Wn @ (Xn - Zn)).T).T
    worst_tgt = max(worst_tgt, np.abs(np.array(la.corrected_target(W, X, Z, a)) - ref).max())
out["A1_inverse_max_rel_diff"] = worst_inv
out["A1_corrected_target_max_abs_diff"] = worst_tgt


# ---------------------------------------------------------------- (A2) complete runs, identical dither
def np_quantize_same_draws(Wt, step, prng):
    Q = np.empty_like(Wt)
    for i in range(Wt.shape[0]):
        for j in range(Wt.shape[1]):
            u = (prng.random() - 0.5) * step
            Q[i, j] = step * round((Wt[i, j] + u) / step) - u
    return Q


def np_target(W, X, Z, a):
    if a == 0.0:
        return W
    return W + a * np.linalg.solve(Z @ Z.T, Z @ (W @ (X - Z)).T).T


worst_path = 0.0
Ws, Xs = S1.teacher(random.Random(5))
for seed in range(40):
    for a in (0.0, 0.5, 1.0):
        e_py = S1.run_once(Ws, Xs, 0.05, a, seed)
        prng = random.Random(seed)
        Z = np.array(S1.X1)
        for l in range(S1.LMAX):
            Q = np_quantize_same_draws(np_target(np.array(Ws[l]), np.array(Xs[l]), Z, a if l > 0 else 0.0), 0.05, prng)
            Z = Q @ Z
            if l + 1 in S1.DEPTHS:
                e_np = float(((Z - np.array(Xs[l + 1])) ** 2).sum())
                worst_path = max(worst_path, abs(e_np - e_py[l + 1]) / max(e_np, 1e-300))
out["A2_sim1_paths_max_rel_diff"] = worst_path
worst_path2 = 0.0
Ws2, Xs2 = S2.build_teacher()
for seed in range(200):
    for a in (0.0, 0.25, 1.0):
        e_py = S2.path(Ws2, Xs2, a, seed)
        prng = random.Random(seed)
        Z = np.array(S2.X1)
        for l in range(3):
            Z = np_quantize_same_draws(np_target(np.array(Ws2[l]), np.array(Xs2[l]), Z, a if l > 0 else 0.0), S2.STEP, prng) @ Z
        e_np = float(((Z - np.array(Xs2[3])) ** 2).sum())
        worst_path2 = max(worst_path2, abs(e_np - e_py) / e_np)
out["A2_sim2_paths_max_rel_diff"] = worst_path2
print("(A) same inputs, two implementations:", json.dumps(out, indent=1))

# ---------------------------------------------------------------- (B1) sim1, independent rerun, vectorized over runs
g = np.random.default_rng(20261005)


def batch_run(Wstack, Xstack, step, a, nrun):
    """Wstack: (L,d,d) one teacher; all runs share the teacher.  Returns errors (nrun, len(DEPTHS))."""
    d = Wstack.shape[1]
    Z = np.broadcast_to(Xstack[0], (nrun,) + Xstack[0].shape).copy()
    res = []
    for l in range(S1.LMAX):
        W, X = Wstack[l], Xstack[l]
        if a == 0.0 or l == 0:
            T = np.broadcast_to(W, (nrun, d, d))
        else:
            H = Z @ Z.transpose(0, 2, 1)
            K = np.linalg.solve(H, Z @ (W @ (X - Z)).transpose(0, 2, 1)).transpose(0, 2, 1)
            T = W + a * K
        u = (g.random((nrun, d, d)) - 0.5) * step
        Q = step * np.rint((T + u) / step) - u
        Z = Q @ Z
        if l + 1 in S1.DEPTHS:
            res.append(((Z - Xstack[l + 1]) ** 2).sum(axis=(1, 2)))
    return np.stack(res, axis=1)


def th(nu, a, L):
    q = 0.0
    for _ in range(L):
        q = ((1 - a) ** 2 + nu) * q + nu
    return q


rows = []
d = S1.D
Wst = np.stack([np.eye(d)] * S1.LMAX)
Xst = [np.array(S1.X1)]
for l in range(S1.LMAX):
    Xst.append(Wst[l] @ Xst[-1])
for nu in S1.NUS:
    step = math.sqrt(12 * nu / d)
    for a in S1.ALPHAS:
        e = batch_run(Wst, Xst, step, a, 20000)
        for i, L in enumerate(S1.DEPTHS):
            v = e[:, i] / (Xst[L] ** 2).sum()
            rows.append(dict(kind="fixed", nu=nu, alpha=a, L=L, q=float(v.mean()), se=float(v.std(ddof=1) / math.sqrt(len(v))), q_theory=th(nu, a, L)))
gamma = 1 + d * S1.A_TEACH ** 2 / 3
for nu in S1.NUS:
    step = math.sqrt(12 * gamma * nu / d)
    num = {a: [] for a in S1.ALPHAS}
    den = []
    for k in range(100):
        Wst = np.eye(d) + (2 * g.random((S1.LMAX, d, d)) - 1) * S1.A_TEACH
        Xst = [np.array(S1.X1)]
        for l in range(S1.LMAX):
            Xst.append(Wst[l] @ Xst[-1])
        den.append([float((Xst[L] ** 2).sum()) for L in S1.DEPTHS])
        for a in S1.ALPHAS:
            num[a].append(batch_run(Wst, Xst, step, a, 200).mean(axis=0))
    den = np.array(den)
    out.setdefault("B1_per_teacher", {})[repr(nu)] = dict(den=den.tolist(), num={repr(a): np.array(num[a]).tolist() for a in S1.ALPHAS})
    for a in S1.ALPHAS:
        nm = np.array(num[a])
        for i, L in enumerate(S1.DEPTHS):
            q = nm[:, i].mean() / den[:, i].mean()
            resid = nm[:, i] - q * den[:, i]
            se = math.sqrt((resid ** 2).sum() / 99 / 100) / den[:, i].mean()
            rows.append(dict(kind="random", nu=nu, alpha=a, L=L, q=float(q), se=float(se), q_theory=th(nu, a, L)))
out["B1_rows"] = rows
dev = [abs(r["q"] - r["q_theory"]) / r["se"] for r in rows]
out["B1_summary"] = dict(n=len(rows), within_two_se=int(sum(x <= 2 for x in dev)), worst_in_se=max(dev))
print("(B1) NumPy rerun of sim1 against the closed form:", out["B1_summary"])

# ---------------------------------------------------------------- (B2) sim2, independent rerun
Wn = [np.array(W) for W in Ws2]
Xn = [np.array(X) for X in Xs2]
V = S2.V


def np_paths(a, nrun, collect):
    Z = np.broadcast_to(Xn[0], (nrun,) + Xn[0].shape).copy()
    S = {}
    B = {}
    for l in range(3):
        al = a if l > 0 else 0.0
        W, X = Wn[l], Xn[l]
        if al > 0:
            H = Z @ Z.transpose(0, 2, 1)
            Hi = np.linalg.inv(H)
            P = Z.transpose(0, 2, 1) @ Hi @ Z
            R = Z - X
            if collect:
                n = P.shape[1]
                S[l] = al * (2 - al) * (W @ (R @ P @ R.transpose(0, 2, 1)).mean(axis=0) @ W.T)
                ZmXP = Z - X @ P
                inner = al * (X @ (np.eye(n) - P) @ X.T) + al * (1 - al) * (ZmXP @ ZmXP.transpose(0, 2, 1))
                B[l] = W @ inner.mean(axis=0) @ W.T
            T = W + al * (W @ (X - Z) @ Z.transpose(0, 2, 1) @ Hi)
        else:
            T = np.broadcast_to(W, (nrun,) + W.shape)
        u = (g.random(T.shape) - 0.5) * S2.STEP
        Z = (S2.STEP * np.rint((T + u) / S2.STEP) - u) @ Z
    return ((Z - Xn[3]) ** 2).sum(axis=(1, 2)), S, B


C2 = V * (Xn[0] ** 2).sum() * np.eye(6)
py2 = json.load(open("sim2_gain_split.json"))["rows"]
rows2 = []
for r in py2:
    a = r["alpha"]
    _, S, B = np_paths(a, 20000, True)
    direct = float(np.trace(Wn[2] @ S[1] @ Wn[2].T) + np.trace(S[2]))
    delayed = float(2 * V * (a * np.trace(Wn[1] @ C2 @ Wn[1].T) + np.trace(B[1])))
    eb, _, _ = np_paths(0.0, 40000, False)
    eq, _, _ = np_paths(a, 40000, False)
    gain = float(eb.mean() - eq.mean())
    se = float(math.sqrt(eb.var(ddof=1) / len(eb) + eq.var(ddof=1) / len(eq)))
    rows2.append(dict(alpha=a, direct=direct, delayed=delayed, predicted=direct + delayed, measured=gain, se=se,
                      py_predicted=r["predicted"], py_measured=r["measured"], py_se=r["se"]))
out["B2_rows"] = rows2
print("(B2) NumPy rerun of sim2:")
for r in rows2:
    print("   alpha=%.2f  predicted %.4f (pure Python %.4f)   measured %.4f +- %.4f (pure Python %.4f +- %.4f)" %
          (r["alpha"], r["predicted"], r["py_predicted"], r["measured"], r["se"], r["py_measured"], r["py_se"]))

# ---------------------------------------------------------------- (B3) sim3
py3 = json.load(open("sim3_relu.json"))
relu = lambda A: np.maximum(A, 0.0)
X = np.array([[1.0, -1.0, 1.0], [-1.0, 1.0, 1.0]])
W1 = np.eye(2)
W2 = np.array([[1.0, -2.0], [-1.0, -1.0]])
X2 = relu(W1 @ X)
P3 = W2 @ X2
X3 = relu(P3)
rows3 = []
for r in py3["noflip"]:
    t = r["t"]
    n = 1000000
    E1 = (2 * g.random((n, 2, 2)) - 1) * t
    E2 = (2 * g.random((n, 2, 2)) - 1) * t
    pre2 = (W1 + E1) @ X
    Z2 = relu(pre2)
    Hi = np.linalg.inv(Z2 @ Z2.transpose(0, 2, 1))
    K = W2 @ (X2 - Z2) @ Z2.transpose(0, 2, 1) @ Hi
    preb = (W2 + E2) @ Z2
    preq = (W2 + K + E2) @ Z2
    flips = int((((pre2 > 0) != (W1 @ X > 0)).any(axis=(1, 2)) | ((preb > 0) != (P3 > 0)).any(axis=(1, 2)) | ((preq > 0) != (P3 > 0)).any(axis=(1, 2))).sum())
    dd = (((relu(preq) - X3) ** 2).sum(axis=(1, 2)) - ((relu(preb) - X3) ** 2).sum(axis=(1, 2))) / t ** 2
    rows3.append(dict(t=t, excess_over_t2=float(dd.mean()), se=float(dd.std(ddof=1) / math.sqrt(n)), flips=flips, py=r["excess_over_t2"], py_se=r["se"]))
out["B3_noflip"] = rows3
print("(B3a) NumPy rerun of the no-flip example, 10^6 independent runs per t:")
for r in rows3:
    print("   t=%.5f  %.4f +- %.4f   (pure Python %.4f +- %.4f)   activation changes: %d" % (r["t"], r["excess_over_t2"], r["se"], r["py"], r["py_se"], r["flips"]))

worst_b = 0.0
for r in py3["bottleneck"]:
    eta, t = r["eta"], r["t"]
    X1 = np.array([[2.0, 2, 1, 1], [1, 1, 2, 2], [0, 0, eta, -eta]])
    Wa = np.array([[1.0, 0, 0], [0, 1, 0]])
    Wb = np.array([[1.0, -1.0], [-1.0, 1.5]])
    Xb = relu(Wa @ X1)
    pre3 = Wb @ Xb
    X3b = relu(pre3)
    Js = [np.diag([1.0, 1, 0, 0]), np.diag([0.0, 0, 1, 1])]
    Ds = [np.diag((pre3[:, 0] > 0).astype(float)), np.diag((pre3[:, 2] > 0).astype(float))]
    mq = mb = trK = kmax = 0.0
    s1 = list(itertools.product([-t, t], repeat=6))
    s2 = list(itertools.product([-t, t], repeat=4))
    for e1 in s1:
        Z2 = relu((Wa + np.array(e1).reshape(2, 3)) @ X1)
        P = Z2.T @ np.linalg.solve(Z2 @ Z2.T, Z2)
        R = Z2 - Xb
        for c in range(2):
            k = np.linalg.norm(P @ Js[c] - Js[c] @ P, 2)
            kmax = max(kmax, k)
            F = Ds[c] @ Wb
            trK += k * np.trace(F @ R @ R.T @ F.T) / len(s1)
        for e2 in s2:
            EZ = np.array(e2).reshape(2, 2) @ Z2
            mq += ((relu(Wb @ Xb @ P + EZ) - X3b) ** 2).sum() / (len(s1) * len(s2))
            mb += ((relu(Wb @ Z2 + EZ) - X3b) ** 2).sum() / (len(s1) * len(s2))
    for key, val in (("kmax", kmax), ("bound", trK), ("mse_base", mb), ("mse_qep", mq)):
        worst_b = max(worst_b, abs(val - r[key]) / abs(r[key]))
out["B3_bottleneck_max_rel_diff"] = worst_b
print("(B3b) exact enumeration of the bottleneck family, largest relative difference to pure Python: %.2e" % worst_b)

json.dump(out, open("crosscheck_numpy.json", "w"), indent=1)
print("written crosscheck_numpy.json")
