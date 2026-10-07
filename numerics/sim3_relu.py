"""Numerical illustration 3: ReLU networks.

Part (a): Example ex:noflip.  Two ReLU layers, X = [[1,-1,1],[-1,1,1]], W_1 = I, W_2 = [[1,-2],[-1,-1]],
  independent errors uniform on [-t, t] on every weight (the law of subtractive dither with step 2t), alpha_2 = 1.
  Protocol: t in {5e-4, 1e-3, 1/600, 5e-3, 1e-2, 2e-2, 5e-2, 1e-1}; 400000 runs per t, independent across t
  (a first run used common random numbers across t; it was replaced so that the plotted points are independent);
  the same error draws for both schemes; record (D_QEP - D_BASE)/t^2 with its standard error and the number of activation
  changes relative to the teacher, in either scheme, at either layer.

Part (b): the bottleneck family after Corollary cor:hr, sign-valued errors +-t on every weight, exact enumeration
  of the 1024 realizations.  eta in {0.03, 0.1}; t in {1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2}.
  Record the largest commutator norm, the bound sum_c tr K of Theorem thm:relu, the two mean-square errors and
  the number of activation changes.
"""
import itertools
import json
import math
import random
import sys
from la import mm, tr, add, sc, zeros, inv, fro2

relu = lambda A: [[x if x > 0 else 0.0 for x in r] for r in A]
sg = lambda A: [[x > 0 for x in r] for r in A]


# ------------------------------------------------------------------ part (a)
def part_a():
    X = [[1.0, -1.0, 1.0], [-1.0, 1.0, 1.0]]
    W1 = [[1.0, 0.0], [0.0, 1.0]]
    W2 = [[1.0, -2.0], [-1.0, -1.0]]
    P2 = mm(W1, X)
    X2 = relu(P2)
    P3 = mm(W2, X2)
    X3 = relu(P3)
    g2, g3 = sg(P2), sg(P3)
    rows = []
    n = 400000
    for t in [5e-4, 1e-3, 1.0 / 600, 5e-3, 1e-2, 2e-2, 5e-2, 1e-1]:
        rng = random.Random(4242 + int(round(t * 1e7)))      # independent draws for each t
        s = ss = 0.0
        sb = sq = 0.0
        flips = 0
        for _ in range(n):
            E1 = [[(2 * rng.random() - 1) * t for _ in range(2)] for _ in range(2)]
            E2 = [[(2 * rng.random() - 1) * t for _ in range(2)] for _ in range(2)]
            pre2 = mm(add(W1, E1), X)
            Z2 = relu(pre2)
            Zt = tr(Z2)
            K = mm(mm(mm(W2, add(X2, Z2, -1.0)), Zt), inv(mm(Z2, Zt)))
            preb = mm(add(W2, E2), Z2)
            preq = mm(add(add(W2, K), E2), Z2)
            if sg(pre2) != g2 or sg(preb) != g3 or sg(preq) != g3:
                flips += 1
            eb = fro2(add(relu(preb), X3, -1.0))
            eq = fro2(add(relu(preq), X3, -1.0))
            d = (eq - eb) / (t * t)
            s += d
            ss += d * d
            sb += eb
            sq += eq
        m = s / n
        se = math.sqrt(max(ss / n - m * m, 0.0) / n)
        rows.append(dict(t=t, excess_over_t2=m, se=se, flips=flips, mse_base=sb / n, mse_qep=sq / n,
                         lower_bound=2.0 / 27 - 42 * t * (1 + t)))
        print(rows[-1], file=sys.stderr, flush=True)
    return rows


# ------------------------------------------------------------------ part (b)
def eig_sym_max(S):
    """largest eigenvalue of a small symmetric PSD matrix by Jacobi rotations"""
    A = [list(r) for r in S]
    n = len(A)
    for _ in range(60):
        off = sum(A[i][j] ** 2 for i in range(n) for j in range(n) if i != j)
        if off < 1e-28:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if abs(A[p][q]) < 1e-300:
                    continue
                th = 0.5 * math.atan2(2 * A[p][q], A[q][q] - A[p][p])
                c, s_ = math.cos(th), math.sin(th)
                for k in range(n):
                    a, b = A[k][p], A[k][q]
                    A[k][p], A[k][q] = c * a - s_ * b, s_ * a + c * b
                for k in range(n):
                    a, b = A[p][k], A[q][k]
                    A[p][k], A[q][k] = c * a - s_ * b, s_ * a + c * b
    return max(A[i][i] for i in range(n))


def part_b():
    rows = []
    for eta in (0.03, 0.1):
        for t in (1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2):
            X1 = [[2.0, 2.0, 1.0, 1.0], [1.0, 1.0, 2.0, 2.0], [0.0, 0.0, eta, -eta]]
            W1 = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0]]
            W2 = [[1.0, -1.0], [-1.0, 1.5]]
            pre2t = mm(W1, X1)
            X2 = relu(pre2t)
            pre3 = mm(W2, X2)
            X3 = relu(pre3)
            g2, g3 = sg(pre2t), sg(pre3)
            Js = [[[1.0 if i == j and i < 2 else 0.0 for j in range(4)] for i in range(4)],
                  [[1.0 if i == j and i >= 2 else 0.0 for j in range(4)] for i in range(4)]]
            Ds = [[[float(g3[0][0]), 0.0], [0.0, float(g3[1][0])]], [[float(g3[0][2]), 0.0], [0.0, float(g3[1][2])]]]
            s1 = list(itertools.product([-t, t], repeat=6))
            s2 = list(itertools.product([-t, t], repeat=4))
            mq = mb = trK = 0.0
            kmax, flips = 0.0, 0
            for e1 in s1:
                E1 = [list(e1[:3]), list(e1[3:])]
                pre2 = mm(add(W1, E1), X1)
                flips += sg(pre2) != g2
                Z2 = relu(pre2)
                Zt = tr(Z2)
                P = mm(mm(Zt, inv(mm(Z2, Zt))), Z2)
                R = add(Z2, X2, -1.0)
                RRt = mm(R, tr(R))
                for c, J in enumerate(Js):
                    Cm = add(mm(P, J), mm(J, P), -1.0)
                    k = math.sqrt(max(eig_sym_max(mm(tr(Cm), Cm)), 0.0))
                    kmax = max(kmax, k)
                    Fm = mm(Ds[c], W2)
                    trK += k * sum(sum(x * y for x, y in zip(r1, r2)) for r1, r2 in zip(mm(Fm, RRt), Fm)) / len(s1)
                WT = mm(W2, mm(X2, P))
                WZ = mm(W2, Z2)
                for e2 in s2:
                    EZ = mm([list(e2[:2]), list(e2[2:])], Z2)
                    pq, pb = add(WT, EZ), add(WZ, EZ)
                    flips += (sg(pq) != g3) + (sg(pb) != g3)
                    mq += fro2(add(relu(pq), X3, -1.0)) / (len(s1) * len(s2))
                    mb += fro2(add(relu(pb), X3, -1.0)) / (len(s1) * len(s2))
            rows.append(dict(eta=eta, t=t, kmax=kmax, bound=trK, mse_base=mb, mse_qep=mq, excess=mq - mb, flips=int(flips)))
            print(rows[-1], file=sys.stderr, flush=True)
    return rows


if __name__ == "__main__":
    out = {"protocol": __doc__}
    if "b" in sys.argv[1:] or len(sys.argv) == 1:
        out["bottleneck"] = part_b()
    if "a" in sys.argv[1:] or len(sys.argv) == 1:
        out["noflip"] = part_a()
    json.dump(out, open("sim3_relu.json", "w"), indent=1)
    print("written sim3_relu.json")
