#!/usr/bin/env python3
"""Verify stored certificates; --replay recomputes all three frozen witnesses."""
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt
import argparse
import ast
import datetime
import hashlib
import itertools
import json

ROOT = Path(__file__).resolve().parent
PORTABLE = ROOT  # Flat manuscript artifact layout; historical files remain byte-identical.
NAMES = (
    "checkG_climb_3_1.json",
    "checkG_climb_variant_a_1.json",
    "checkG_search_seed5.json",
)
SOURCE_SHA256 = "de87e4c76989278d21c96d816b2f0d9baab750f585ee5140bda270bf79291f54"
RECEIPT_SHA256 = "3f852e55826b0f23e143b08ed7d9269fc3344cfb7d54b5e3f4cceae038aa6605"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_receipt(result):
    b, q, excess = (Q(result[k]) for k in ("mseB", "mseQ", "excess"))
    lower, upper = map(Q, result["bound_interval"])
    cut_lower, cut_upper = map(Q, result["no_psi_bound_interval"])
    assert q - b == excess
    assert 0 < excess <= lower <= upper
    assert 0 <= cut_lower <= cut_upper
    assert (excess > cut_upper) == result["certifies_omitted_psi_violation"]
    assert result["paper_first_layer_zero"]
    assert result["flips"] == 0
    assert result["all_required_Gram_inversions_exact"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    source = PORTABLE / "replay_saved_witnesses.py"
    receipt_path = PORTABLE / "SAVED_WITNESS_REPLAY.json"
    assert digest(source) == SOURCE_SHA256
    assert digest(receipt_path) == RECEIPT_SHA256
    historical = json.loads(receipt_path.read_text())
    namespace = {"Q": Q, "isqrt": isqrt, "itertools": itertools}
    if args.replay:
        # Only function definitions are loaded, with their source bytes frozen.
        tree = ast.parse(source.read_text())
        definitions = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
        exec(compile(ast.Module(body=definitions, type_ignores=[]), str(source), "exec"), namespace)
    results = {}
    for name in NAMES:
        old = historical["results"][name]
        path = PORTABLE / name
        assert digest(path) == old["input_sha256"]
        check_receipt(old)
        if args.replay:
            raw = json.loads(path.read_text())
            cfg = raw.get("cfg") or raw["best"]
            new = namespace["evaluate"](cfg, paper_first=True)
            check_receipt(new)
            compared = {k: v for k, v in old.items() if k != "input_sha256"}
            assert new == compared, name
            results[name] = {"deterministic_replay_matches_historical_receipt": True, "result": new}
        else:
            results[name] = {"hash_and_existing_rational_receipt_checks": True, "network_replay": False}
    report = {
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "operation": "fixed_finite_support_replay" if args.replay else "stored_receipt_arithmetic_only",
        "new_search_or_random_inputs": False,
        "results": results,
    }
    destination = ROOT / ("FIXED_REPLAY_RESULT.json" if args.replay else "RECEIPT_CHECK_RESULT.json")
    destination.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(destination)


if __name__ == "__main__":
    main()
