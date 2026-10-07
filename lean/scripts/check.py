#!/usr/bin/env python3
"""Run from any working directory. Uses only relative artifact resources."""
from pathlib import Path
import argparse, json, re, subprocess, sys
from hashlib import sha256

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--log-dir", type=Path, help="Optional directory for full validation transcripts")
args = parser.parse_args()
LOG_DIR = args.log_dir.resolve() if args.log_dir else None
if LOG_DIR:
    LOG_DIR.mkdir(parents=True, exist_ok=False)
sequence = 0

def run(args):
    p = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    global sequence
    sequence += 1
    if LOG_DIR:
        stem = LOG_DIR / f"{sequence:02d}"
        stem.with_suffix(".stdout.txt").write_text(p.stdout)
        stem.with_suffix(".stderr.txt").write_text(p.stderr)
        stem.with_suffix(".json").write_text(json.dumps({"command": args,
            "exit_code": p.returncode,
            "stdout_sha256": sha256(p.stdout.encode()).hexdigest(),
            "stderr_sha256": sha256(p.stderr.encode()).hexdigest()}, indent=2) + "\n")
    return p, p.stdout + p.stderr

def require(ok, message, output=""):
    if not ok:
        print(message, file=sys.stderr)
        if output:
            print(output, file=sys.stderr)
        raise SystemExit(1)

for name, expected_hash in json.loads((ROOT / "SOURCE_HASHES.json").read_text()).items():
    require(sha256((ROOT / name).read_bytes()).hexdigest() == expected_hash, "Source hash mismatch: " + name)
p, out = run(["lake", "build"])
require(p.returncode == 0, "Build failed", out)
print("PASS: lake build")
p, out = run(["lake", "env", "lean", "-j", "1", "-M", "8192", "Audit.lean"])
require(p.returncode == 0, "Axiom audit did not elaborate", out)
expected = set(json.loads((ROOT / "audit_targets.json").read_text()))
declared = set()
for module in json.loads((ROOT / "CLAIMS.json").read_text())["modules"]:
    source = (ROOT / (module["module"] + ".lean")).read_text()
    namespace = re.search(r"^namespace (\w+)", source, re.M).group(1)
    declared.update(namespace + "." + name for name in
                    re.findall(r"^\s*theorem\s+([^\s(:{\[]+)", source, re.M))
    require(not re.search(r"\b(sorry|admit|native_decide|unsafe)\b|^axiom\s", source, re.M),
            "Disallowed proof shortcut or custom axiom in " + module["module"])
require(declared == expected, "The central audit omits a source theorem or lists a stale target")
found = {}
for target, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
    found[target] = {a.strip() for a in axioms.split(",") if a.strip()}
for target in re.findall(r"'([^']+)' does not depend on any axioms", out):
    found[target] = set()
require(set(found) == expected, "Missing or unexpected axiom targets", out)
require(all(a <= ALLOWED for a in found.values()), "Unapproved axiom dependency", out)
print(f"PASS: {len(found)} theorem declarations; standard axioms only")
p, out = run(["lake", "env", "lean", "-j", "1", "-M", "8192", "ArtifactCurrentControls.lean"])
require(p.returncode == 0 and "sorry" not in out, "Current positive controls failed", out)
p, out = run(["lake", "env", "lean", "-j", "1", "-M", "8192", "tests/PositiveControls.lean"])
require(p.returncode == 0, "Positive controls failed", out)
require("sorry" not in out, "Positive controls contain an admitted proof", out)
print("PASS: positive controls")
negative = sorted((ROOT / "tests/negative").glob("*.lean"))
require(len(negative) == len(json.loads((ROOT / "CONTROL_INVENTORY.json").read_text())["negative"]), "Unexpected negative-control inventory")
for f in negative:
    rel = f.relative_to(ROOT).as_posix()
    p, out = run(["lake", "env", "lean", "-j", "1", "-M", "8192", rel])
    require(p.returncode != 0, f"False statement unexpectedly accepted: {rel}", out)
    require("error:" in out, f"No Lean rejection diagnostic: {rel}", out)
    # A missing module, stale binary, syntax error or resource failure is not
    # evidence that the intended false proposition was rejected.
    forbidden = ["unknown module", "unknown constant", "Unknown identifier", "unknown identifier",
                 "object file", "failed to synthesize", "unexpected token", "unknown tactic",
                 "maximum recursion", "maximum number of heartbeats", "out of memory",
                 "interrupted", "segmentation fault", "No such file"]
    require(not any(s.lower() in out.lower() for s in forbidden),
            f"Invalid negative-control failure: {rel}", out)
    require("unsolved goals" in out or "failed to find a contradiction" in out,
            f"Unexpected semantic diagnostic: {rel}", out)
    print(f"PASS: rejected {f.name}")
print("ALL CHECKS PASSED (build and proof checks; scientific review remains separate)")
