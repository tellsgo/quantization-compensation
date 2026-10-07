"""C6 local frozen-input accounting. No model or external runner execution."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np


def sq(a):
    return float(np.einsum('ij,ij->', a, a))


def inner(a, b):
    return float(np.einsum('ij,ij->', a, b))


def derived_seed(model, module, seed):
    return int.from_bytes(hashlib.sha256(f'{model}|{module}|{seed}'.encode()).digest()[:16], 'little')


def scales(w):
    m = np.max(np.abs(w), axis=1, keepdims=True)
    return np.where(m > 0, m / 7., 1.)


def encode_decode(target, delta, path, seed=None):
    """Save integer indices + row scale + RNG seed, reload, decode in float64."""
    u = np.zeros_like(target) if seed is None else (np.random.Generator(np.random.PCG64(seed)).random(target.shape)-.5)*delta
    indices = np.rint((target+u)/delta)
    if not np.isfinite(indices).all() or np.max(np.abs(indices)) > np.iinfo(np.int32).max:
        raise ArithmeticError('unbounded lattice index exceeded int32 container; no clipping allowed')
    metadata = {'format': 'c6_uniform_lattice_v1', 'shape': list(target.shape),
                'seed': None if seed is None else str(seed), 'rng': 'numpy.PCG64',
                'numpy': np.__version__, 'decode_dtype': 'float64', 'rounding': 'ties_to_even'}
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(path, indices=indices.astype(np.int32), delta=delta.astype(np.float64),
                        metadata=np.array(json.dumps(metadata, sort_keys=True)))
    with np.load(path, allow_pickle=False) as f:
        meta = json.loads(str(f['metadata']))
        if meta != metadata or f['indices'].shape != target.shape:
            raise ArithmeticError('packet metadata roundtrip mismatch')
        regenerated = np.zeros(target.shape) if meta['seed'] is None else (np.random.Generator(np.random.PCG64(int(meta['seed']))).random(tuple(meta['shape']))-.5)*f['delta']
        decoded = f['indices'].astype(np.float64)*f['delta']-regenerated
    expected = indices*delta-u
    if not np.array_equal(decoded, expected):
        raise ArithmeticError('packet decoded values differ from encoder reconstruction')
    return decoded, {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                     'bytes': path.stat().st_size, 'max_abs_index': int(np.max(np.abs(indices)))}


def correction(w, x, z, rcond=1e-10):
    """SVD-defined orthogonal retained-space extension; never ridge."""
    a = w @ (x-z)
    uz, sigma, vt = np.linalg.svd(z, full_matrices=False)
    keep = sigma > (rcond*sigma[0] if sigma.size and sigma[0] else 0)
    rank = int(keep.sum())
    if rank:
        vr = vt[keep].T
        av = a @ vr
        c = (av / sigma[keep]) @ uz[:, keep].T
        target_s = av @ vr.T
        orth = np.linalg.norm(vr.T @ vr - np.eye(rank), 'fro') / max(np.sqrt(rank), 1)
    else:
        c = np.zeros_like(w)
        target_s = np.zeros_like(a)
        orth = 0.
    s = c @ z
    denom = max(np.sqrt(sq(a)*sq(s)), sq(s), 1e-30)
    report = {'effective_rank': rank, 'input_dim': z.shape[0], 'full_effective_rank': rank == z.shape[0],
              'svd_rcond': rcond, 'sigma_max': float(sigma[0]) if sigma.size else 0.,
              'sigma_min_retained': float(sigma[keep][-1]) if rank else None,
              'condition_retained': float(sigma[0]/sigma[keep][-1]) if rank else None,
              'basis_orthogonality_relative': float(orth),
              'projection_identity_relative': float(np.sqrt(sq(s-target_s)/max(sq(a),1e-30))),
              'projection_inner_relative': abs(inner(a,s)-sq(s))/denom,
              'all_zero_z': not np.any(z)}
    report['projection_quality_pass'] = all(report[k] <= 1e-8 for k in
        ['basis_orthogonality_relative','projection_identity_relative','projection_inner_relative'])
    return c, report


def prepare_accounting(w, cmat, x, z):
    return {'a':w@(x-z), 's':cmat@z, 'teacher':w@x}


def prepare_baseline(w,q0,z,context):
    return {'b0':(q0-w)@z, 'direct0':context['teacher']-q0@z}


def audit(w, cmat, q0, qa, x, z, alpha, calibration=True, context=None, baseline=None):
    n = x.shape[1]
    context = prepare_accounting(w,cmat,x,z) if context is None else context
    baseline = prepare_baseline(w,q0,z,context) if baseline is None else baseline
    a, s = context['a'], context['s']
    b0 = baseline['b0']
    ba = (qa-(w+alpha*cmat)) @ z
    j = ba-b0
    r0 = a-b0
    rb = r0-alpha*s
    direct0, directa = baseline['direct0'], context['teacher']-qa@z
    d, c0, ca = sq(s), inner(s,b0), inner(s,ba)
    fixed = alpha*alpha*d-2*alpha*inner(r0,s)
    fixed_projected = -alpha*(2-alpha)*d+2*alpha*c0
    j_energy, j_cross = sq(j), -2*inner(rb,j)
    change = j_energy+j_cross
    direct_gap = sq(directa)-sq(direct0)
    scale = max(sq(direct0),sq(directa),abs(fixed),j_energy,abs(j_cross),1e-30)
    closure = abs(direct_gap-fixed-change)/scale
    residual_scale=max(np.sqrt(sq(direct0)),np.sqrt(sq(directa)),np.sqrt(sq(a)),1e-30)
    residual_closure=max(np.sqrt(sq(r0-direct0)),np.sqrt(sq(a-alpha*s-ba-directa)))/residual_scale
    eligible = d/n > 1e-12*max(sq(a)/n,1e-30)
    margin=(2*c0-(2-alpha)*d)/n
    margin_tol=1e-8*max(d/n,abs(2*c0)/n,sq(b0)/n,1e-30)
    actual_tol=1e-8*max(sq(direct0)/n,sq(directa)/n,1e-30)
    result = {'alpha': alpha, 'tokens': n, 'calibration_projection_interpretation': calibration,
              'd': d/n, 'c0': c0/n, 'c_alpha': ca/n, 'a_energy': sq(a)/n, 'b0_energy': sq(b0)/n,
              'eligible_ratio': bool(eligible), 'c0_over_d': c0/d if eligible else None,
              'c_alpha_over_d': ca/d if eligible else None,
              'fixed_margin': margin, 'fixed_margin_tolerance': margin_tol,
              'fixed_harm_raw': bool(margin>0) if calibration else None,
              'fixed_harm_tolerant': bool(margin>margin_tol) if calibration else None,
              'baseline_loss': sq(direct0)/n, 'candidate_loss': sq(directa)/n,
              'actual_gap': direct_gap/n, 'actual_gap_tolerance': actual_tol,
              'actual_harm_tolerant': bool(direct_gap/n>actual_tol),
              'fixed_generic_gap': fixed/n, 'fixed_projected_gap': fixed_projected/n if calibration else None,
              'requantization_energy': j_energy/n, 'requantization_cross': j_cross/n,
              'requantization_total': change/n, 't4_reconstructed_gap': (fixed+change)/n,
              't4_closure_absolute': abs(direct_gap-fixed-change)/n,
              't4_closure_relative': closure, 't4_closure_denominator': scale/n,
              'direct_residual_closure_relative': residual_closure,
              'same_error_energy': sq(j)/n,
              'accounting_quality_pass': bool(closure<=1e-8 and residual_closure<=1e-8)}
    if not np.isfinite([v for v in result.values() if isinstance(v,(int,float))]).all():
        raise ArithmeticError('nonfinite scalar accounting')
    return result
