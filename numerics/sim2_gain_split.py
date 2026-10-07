"""Numerical illustration 2: where the gain comes from (Proposition prop:gain), in a network with bottlenecks.

Protocol, fixed before running:
  Linear network 8 -> 6 -> 4 -> 2, N = 16, X_1 = [I_8 I_8]/sqrt(2).
  Teacher: W_l = diag(s) Q_l, Q_l with orthonormal rows obtained by Gram-Schmidt from a fixed pseudo-random matrix
  (seed 2026), singular values s equally spaced in [0.8, 1.2].
  Entrywise subtractive dither with step 0.3 at every layer, so Psi_l(M) = v tr(M) I with v = 0.3^2/12.
  Strengths (alpha_2, alpha_3) = (a, a) for a in {0.25, 0.5, 0.75, 1}; layer 1 needs no correction.
  Batch A (10000 runs per a): estimate the sources S_2, S_3, B_2 of Proposition prop:gain along the corrected
  trajectory, and predict the terminal gain
        gain = tr(W_3 S_2 W_3^T) + tr(S_3)                      (error removed directly)
             + 2 v [ a tr(W_2 C_2 W_2^T) + tr(B_2) ]            (less excitation of later rounding noise)
  with C_2 = v tr(X_1 X_1^T) I known exactly.
  Batch B (10000 runs, independent seeds): measure the terminal mean-square errors of the two schemes,
  with the same dither draws for both (pairing reduces variance; the rounding errors differ).
The prediction uses batch A only and the measurement batch B only.
"""
import json
import math
import random
import sys
from la import mm, tr, add, sc, eye, zeros, trace, fro2, inv, gram_schmidt_rows, quantize_dither, corrected_target

N = 16
DIMS = [8, 6, 4, 2]
STEP = 0.3
V = STEP * STEP / 12
AS = [0.25, 0.5, 0.75, 1.0]
NA = NB = 10000
X1 = [[(1.0 if j % 8 == i else 0.0) / math.sqrt(2) for j in range(N)] for i in range(8)]


def build_teacher():
    rng = random.Random(2026)
    Ws = []
    for l in range(3):
        r, c = DIMS[l + 1], DIMS[l]
        Q = gram_schmidt_rows([[rng.gauss(0, 1) for _ in range(c)] for _ in range(r)])
        s = [0.8 + 0.4 * i / (r - 1) for i in range(r)]
        Ws.append([[s[i] * x for x in Q[i]] for i in range(r)])
    Xs = [X1]
    for W in Ws:
        Xs.append(mm(W, Xs[-1]))
    return Ws, Xs


def path(Ws, Xs, a, seed, collect=None):
    rng = random.Random(seed)
    Z = X1
    for l in range(3):
        al = a if l > 0 else 0.0
        W, X = Ws[l], Xs[l]
        if collect is not None and al > 0:
            Zt, Xt = tr(Z), tr(X)
            Hi = inv(mm(Z, Zt))
            R = add(Z, X, -1.0)
            RZt = mm(R, Zt)
            RPR = mm(mm(RZt, Hi), tr(RZt))                         # R P R^T
            XZt = mm(X, Zt)
            XPX = mm(mm(XZt, Hi), tr(XZt))                         # X P X^T
            XXt, ZZt = mm(X, Xt), mm(Z, Zt)
            ZXt = tr(XZt)
            inner = add(sc(add(XXt, XPX, -1.0), al), sc(add(add(add(ZZt, ZXt, -1.0), XZt, -1.0), XPX), al * (1 - al)))
            collect["S"][l] = add(collect["S"][l], sc(mm(mm(W, RPR), tr(W)), al * (2 - al)))
            collect["B"][l] = add(collect["B"][l], mm(mm(W, inner), tr(W)))
        Q = quantize_dither(corrected_target(W, X, Z, al), STEP, rng)
        Z = mm(Q, Z)
    return fro2(add(Z, Xs[3], -1.0))


def main():
    Ws, Xs = build_teacher()
    out = {"protocol": __doc__, "rows": []}
    C2 = sc(eye(6), V * fro2(X1))                                  # exact: E delta_2 delta_2^T
    for a in AS:
        col = {"S": {1: zeros(4, 4), 2: zeros(2, 2)}, "B": {1: zeros(4, 4), 2: zeros(2, 2)}}
        for r in range(NA):
            path(Ws, Xs, a, 1_000_000 + r, col)
        S2, S3, B2 = sc(col["S"][1], 1.0 / NA), sc(col["S"][2], 1.0 / NA), sc(col["B"][1], 1.0 / NA)
        direct = trace(mm(mm(Ws[2], S2), tr(Ws[2]))) + trace(S3)
        delayed = 2 * V * (a * trace(mm(mm(Ws[1], C2), tr(Ws[1]))) + trace(B2))
        sb = sq = sd = sdd = 0.0
        for r in range(NB):
            eb = path(Ws, Xs, 0.0, 9_000_000 + r)
            eq = path(Ws, Xs, a, 9_000_000 + r)
            sb += eb
            sq += eq
            sd += eb - eq
            sdd += (eb - eq) ** 2
        gain = sd / NB
        se = math.sqrt(max(sdd / NB - gain * gain, 0.0) / NB)
        out["rows"].append(dict(alpha=a, direct=direct, delayed=delayed, predicted=direct + delayed,
                                measured=gain, se=se, mse_base=sb / NB, mse_qep=sq / NB))
        print(out["rows"][-1], file=sys.stderr, flush=True)
    json.dump(out, open("sim2_gain_split.json", "w"), indent=1)
    print("written sim2_gain_split.json")


if __name__ == "__main__":
    main()
