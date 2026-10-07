"""Small dense linear algebra in pure Python (no numpy on this machine). Matrices are lists of rows of floats."""
import math


def mm(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, c)) for c in Bt] for r in A]


def tr(A):
    return [list(r) for r in zip(*A)]


def add(A, B, s=1.0):
    return [[a + s * b for a, b in zip(r, q)] for r, q in zip(A, B)]


def sc(A, s):
    return [[s * a for a in r] for r in A]


def eye(n):
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def zeros(n, m):
    return [[0.0] * m for _ in range(n)]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def fro2(A):
    return sum(x * x for r in A for x in r)


def inv(A):
    n = len(A)
    M = [list(r) + e for r, e in zip(A, eye(n))]
    for i in range(n):
        p = max(range(i, n), key=lambda r: abs(M[r][i]))
        if abs(M[p][i]) < 1e-300:
            raise ZeroDivisionError("singular")
        M[i], M[p] = M[p], M[i]
        d = M[i][i]
        M[i] = [x / d for x in M[i]]
        for r in range(n):
            if r != i:
                f = M[r][i]
                if f != 0.0:
                    M[r] = [x - f * y for x, y in zip(M[r], M[i])]
    return [r[n:] for r in M]


def gram_schmidt_rows(A):
    """Orthonormalize the rows of A (assumed independent)."""
    out = []
    for r in A:
        v = list(r)
        for q in out:
            c = sum(a * b for a, b in zip(v, q))
            v = [a - c * b for a, b in zip(v, q)]
        nrm = math.sqrt(sum(a * a for a in v))
        out.append([a / nrm for a in v])
    return out


def quantize_dither(Wt, step, rng):
    """Entrywise subtractive dither on the unbounded grid step*Z: Q = step*round((w+u)/step) - u."""
    out = []
    for row in Wt:
        new = []
        for w in row:
            u = (rng.random() - 0.5) * step
            new.append(step * round((w + u) / step) - u)
        out.append(new)
    return out


def corrected_target(W, X, Z, alpha):
    """W* = W + alpha W (X - Z) Z^T (Z Z^T)^{-1}; the correction is skipped when alpha == 0."""
    if alpha == 0.0:
        return W
    Zt = tr(Z)
    K = mm(mm(mm(W, add(X, Z, -1.0)), Zt), inv(mm(Z, Zt)))
    return add(W, K, alpha)
