"""Compare the pure-Python Monte Carlo runs with the NumPy runs used for the figures.

Two independent estimates q1 +- s1 and q2 +- s2 of the same quantity should differ by a few times
sqrt(s1^2 + s2^2).  Prints the distribution of z = (q1 - q2)/sqrt(s1^2 + s2^2).
"""
import json
import math

py = json.load(open("sim1_gain_depth.json"))
nu = json.load(open("results_sim1.json"))
zs = []
for kind in ("fixed", "random"):
    a = {(r["nu"], r["alpha"], r["L"]): r for r in py[kind]}
    b = {(r["nu"], r["alpha"], r["L"]): r for r in nu[kind]}
    assert a.keys() == b.keys()
    for k in a:
        zs.append((a[k]["q_sim"] - b[k]["q_sim"]) / math.hypot(a[k]["se"], b[k]["se"]))
n = len(zs)
print("sim1: %d values; |z| <= 2 for %d; largest |z| = %.2f; mean z = %+.2f" % (n, sum(abs(z) <= 2 for z in zs), max(abs(z) for z in zs), sum(zs) / n))

py3 = json.load(open("sim3_relu.json"))["noflip"]
nu3 = json.load(open("results_sim3.json"))["noflip"]
z3 = [(a["excess_over_t2"] - b["excess_over_t2"]) / math.hypot(a["se"], b["se"]) for a, b in zip(py3, nu3)]
print("no-flip example: z by t:", ["%+.2f" % z for z in z3], "; activation changes in the pure-Python runs:", sum(r["flips"] for r in py3))
