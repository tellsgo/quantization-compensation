"""Turn the JSON results into pgfplots figures and a table (plain LaTeX; no plotting library needed)."""
import json
import math

s1 = json.load(open("results_sim1.json"))
s2 = json.load(open("sim2_gain_split.json"))
s3 = json.load(open("results_sim3.json"))


def theory(nu, alpha, L):
    q = 0.0
    for _ in range(L):
        q = ((1 - alpha) ** 2 + nu) * q + nu
    return q


def coords(pts, err=False):
    if err:
        return " ".join("(%.6g,%.6g) +- (0,%.3g)" % p for p in pts)
    return " ".join("(%.6g,%.6g)" % p for p in pts)


DEPTHS = sorted({r["L"] for r in s1["fixed"]})
NUS = sorted({r["nu"] for r in s1["fixed"]})
Lfine = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
sty = {0.0: ("black", "o", "no compensation"), 0.5: ("blue", "square", r"$\alpha=\tfrac12$"), 1.0: ("red", "triangle", r"$\alpha=1$")}

# ---------------- figure 1 ----------------
nu0 = 1e-2
left = []
for a in (0.0, 0.5, 1.0):
    col, mark, name = sty[a]
    left.append(r"\addplot[%s,thick] coordinates {%s};" % (col, coords([(L, theory(nu0, a, L)) for L in Lfine])))
    left.append(r"\addlegendentry{%s}" % name)
    pts = [(r["L"], r["q_sim"], 2 * r["se"]) for r in s1["fixed"] if r["nu"] == nu0 and r["alpha"] == a]
    left.append(r"\addplot[%s,only marks,mark=o,mark size=2.2pt,forget plot,error bars/.cd,y dir=both,y explicit] coordinates {%s};" % (col, coords(pts, True)))
    pts = [(r["L"], r["q_sim"], 2 * r["se"]) for r in s1["random"] if r["nu"] == nu0 and r["alpha"] == a]
    left.append(r"\addplot[%s,only marks,mark=x,mark size=2.6pt,forget plot,error bars/.cd,y dir=both,y explicit] coordinates {%s};" % (col, coords(pts, True)))

right = [r"\addplot[gray,dashed,thick] coordinates {%s};" % coords([(L, 10 * math.log10(L)) for L in Lfine]),
         r"\addlegendentry{$10\log_{10}L$}"]
cols = ["black", "blue", "red", "teal"]
for c, nu in zip(cols, NUS):
    right.append(r"\addplot[%s,thick] coordinates {%s};" % (c, coords([(L, 10 * math.log10(theory(nu, 0, L) / theory(nu, 1, L))) for L in Lfine])))
    right.append(r"\addlegendentry{$\nu=%s$}" % ("10^{%d}" % round(math.log10(nu)) if abs(math.log10(nu) - round(math.log10(nu))) < 1e-9 else "%g" % nu))
    # ratio of the two errors with standard errors paired by teacher (both schemes use the same teachers)
    pts = [(g["L"], g["gain_db"], 2 * g["se_db"]) for g in s1["gain_paired"] if abs(g["nu"] - nu) < 1e-15]
    right.append(r"\addplot[%s,only marks,mark=x,mark size=2.6pt,forget plot,error bars/.cd,y dir=both,y explicit] coordinates {%s};" % (c, coords(pts, True)))

fig1 = r"""\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[width=0.5\textwidth,height=5.4cm,xmode=log,ymode=log,log basis x=2,xlabel={depth $L$},ylabel={normalized error $q_L$},
legend style={font=\scriptsize,at={(0.03,0.97)},anchor=north west,draw=none,fill=none},xtick={1,2,4,8,16,32,64},xticklabels={1,2,4,8,16,32,64},tick label style={font=\scriptsize},label style={font=\small}]
%s
\end{axis}
\end{tikzpicture}\hfill
\begin{tikzpicture}
\begin{axis}[width=0.5\textwidth,height=5.4cm,xmode=log,log basis x=2,xlabel={depth $L$},ylabel={gain of full compensation (dB)},
legend style={font=\scriptsize,at={(0.03,0.97)},anchor=north west,draw=none,fill=none},xtick={1,2,4,8,16,32,64},xticklabels={1,2,4,8,16,32,64},tick label style={font=\scriptsize},label style={font=\small},ymin=-1]
%s
\end{axis}
\end{tikzpicture}
\caption{Gain as a function of depth in the class of Example~\ref{ex:iso}, $d=4$, with the actual algorithm and dithered rounding of the weights. Lines are the closed form; marks are simulations with two standard errors. Left: $\nu=10^{-2}$; circles, fixed teacher $W_l=I$ ($2\times10^4$ runs); crosses, random teachers ($100$ teachers, $200$ runs each, errors clustered by teacher). Right: ratio of the two errors, random teachers, with standard errors paired by teacher. At depth one the two schemes coincide.}\label{fig:gain}
\end{figure}
""" % ("\n".join(left), "\n".join(right))
open("fig_gain.tex", "w").write(fig1)

# ---------------- table (gain split) ----------------
rows = []
for r in s2["rows"]:
    rows.append(r"$%g$ & $%.4f$ & $%.4f$ & $%.4f$ & $%.4f\pm%.4f$ & $%.4f$\\" % (r["alpha"], r["direct"], r["delayed"], r["predicted"], r["measured"], 2 * r["se"], r["mse_qep"]))
tab = r"""\begin{table}[t]
\centering\small
\begin{tabular}{@{}cccccc@{}}
\toprule
$\alpha$ & removed directly & through later noise & predicted gain & measured gain & error of QEP\\
\midrule
%s
\bottomrule
\end{tabular}
\caption{The two parts of the gain in Proposition~\ref{prop:gain}, in a linear network $8\to6\to4\to2$ with dither of step $0.3$ and strengths $\alpha_2=\alpha_3=\alpha$. The prediction is computed from the recursions \eqref{eq:gainD}--\eqref{eq:gainL} with sources estimated on $10^4$ runs; the measured gain comes from $10^4$ independent runs and is given with two standard errors. The mean-square error without compensation is $%.4f$.}\label{tab:split}
\end{table}
""" % ("\n".join(rows), s2["rows"][0]["mse_base"])
open("tab_split.tex", "w").write(tab)

# ---------------- figure 2 (ReLU) ----------------
nf = s3["noflip"]
pts = [(r["t"], r["excess_over_t2"], 2 * r["se"]) for r in nf]
lb = [(t, 2.0 / 27 - 42 * t * (1 + t)) for t in (5e-4, 7e-4, 1e-3, 1.3e-3, 1.0 / 600)]
left = [r"\addplot[gray,dashed,thick,domain=4e-4:0.12,samples=2] {2/27};", r"\addlegendentry{$2/27$}",
        r"\addplot[black,only marks,mark=o,mark size=1.8pt,error bars/.cd,y dir=both,y explicit] coordinates {%s};" % coords(pts, True),
        r"\addlegendentry{simulation}",
        r"\addplot[red,thick] coordinates {%s};" % coords(lb), r"\addlegendentry{proved lower bound}"]
bt = [r for r in s3["bottleneck"] if abs(r["eta"] - 0.1) < 1e-12]
right = [r"\addplot[black,thick,mark=o,mark size=1.6pt] coordinates {%s};" % coords([(r["t"], r["mse_base"]) for r in bt]), r"\addlegendentry{error without compensation}",
         r"\addplot[blue,thick,mark=square,mark size=1.6pt] coordinates {%s};" % coords([(r["t"], r["mse_qep"]) for r in bt]), r"\addlegendentry{error of QEP}",
         r"\addplot[red,thick,mark=triangle,mark size=1.8pt] coordinates {%s};" % coords([(r["t"], r["bound"]) for r in bt]), r"\addlegendentry{bound $\sum_c\mathrm{tr}\,K$ on the excess}",
         r"\addplot[teal,thick,mark=x,mark size=2.2pt] coordinates {%s};" % coords([(r["t"], r["kmax"]) for r in bt]), r"\addlegendentry{largest commutator norm}"]
fig2 = r"""\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[width=0.5\textwidth,height=5.4cm,xmode=log,xlabel={error size $t$},ylabel={$(\text{excess of QEP})/t^2$},ymin=0,ymax=0.11,
legend style={font=\scriptsize,at={(0.97,0.05)},anchor=south east,draw=none,fill=none},tick label style={font=\scriptsize},label style={font=\small}]
%s
\end{axis}
\end{tikzpicture}\hfill
\begin{tikzpicture}
\begin{axis}[width=0.5\textwidth,height=5.4cm,xmode=log,ymode=log,xlabel={error size $t$},ymax=1e6,
legend style={font=\scriptsize,at={(0.03,0.97)},anchor=north west,draw=none,fill=none,legend cell align=left},tick label style={font=\scriptsize},label style={font=\small}]
%s
\end{axis}
\end{tikzpicture}
\caption{ReLU networks. Left: Example~\ref{ex:noflip}, rounding errors sampled from the uniform law of subtractive dither, $10^6$ independent runs per value of $t$, two standard errors; no activation changed state in any run. Right: the bottleneck family after Corollary~\ref{cor:hr} with $\eta=\tfrac1{10}$ and sign-valued errors, exact enumeration; here the correction helps, the bound on the excess decreases as $t^3$ and the commutator as $t$.}\label{fig:relu}
\end{figure}
""" % ("\n".join(left), "\n".join(right))
open("fig_relu.tex", "w").write(fig2)
print("flips in noflip runs:", [r["flips"] for r in nf])
print("flips in bottleneck runs:", sum(r["flips"] for r in s3["bottleneck"]))
print("written fig_gain.tex tab_split.tex fig_relu.tex")
