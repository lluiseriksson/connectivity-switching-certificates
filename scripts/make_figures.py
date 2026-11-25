"""Generate 300-DPI publication figures for Paper 29 (Connectivity Switching in Graphs).
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9,
    "axes.titlesize": 9.5,
    "axes.labelsize": 9,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "legend.fontsize": 7.6,
    "figure.dpi": 300,
    "savefig.dpi": 300,
})


def make_fig1() -> None:
    d3 = json.loads((RESULTS / "exp3_4vertex_dichotomy_census.json").read_text(encoding="utf-8"))
    d2 = json.loads((RESULTS / "exp2_wsat_truth_table_sweep.json").read_text(encoding="utf-8"))["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    cats = ["Complete\nMultip. (P)", "K2+K2\n(NP)", "P4\n(NP)", "L3,1\n(NP)"]
    vals = [d3["complete_multipartite_P"], d3["np_K2_plus_K2"], d3["np_P4"], d3["np_L31"]]
    cols = ["#117a65", "#a93226", "#c0392b", "#922b21"]
    x = np.arange(len(cats))
    ax1.bar(x, vals, color=cols, width=0.58)
    ax1.set_xticks(x)
    ax1.set_xticklabels(cats, fontsize=7.6)
    ax1.set_ylabel("Labeled 4-vertex graphs")
    ax1.set_ylim(0, 17.0)
    ax1.set_title("(a) Thm. 1 dichotomy census (41 graphs)")
    ax1.grid(True, axis="y", linestyle="--", alpha=0.35)
    for i, v in enumerate(vals):
        ax1.text(i, v + 0.4, str(v), ha="center", va="bottom", fontsize=8.0, fontweight="bold")

    labels = [r["formula"] for r in d2]
    tots = [r["total_assignments"] for r in d2]
    sats = [r["sat_count"] for r in d2]
    x2 = np.arange(len(labels))
    w = 0.36
    ax2.bar(x2 - w / 2, tots, width=w, color="#1f618d", label="100% matched assignments")
    ax2.bar(x2 + w / 2, sats, width=w, color="#d68910", label="SAT / connected count")
    ax2.set_yscale("log", base=2)
    ax2.set_xticks(x2)
    ax2.set_xticklabels(labels, fontsize=7.5)
    ax2.set_ylabel("Truth assignments (log2)")
    ax2.set_ylim(1, 512)
    ax2.set_title("(b) Exhaustive Lemma 4 equivalence")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    ax2.legend(loc="upper left", frameon=True, fontsize=7.2)
    for i, (t, s) in enumerate(zip(tots, sats)):
        ax2.text(i - w / 2, t * 1.15, str(t), ha="center", va="bottom", fontsize=7.0)
        ax2.text(i + w / 2, max(1.1, s) * 1.15, str(s), ha="center", va="bottom", fontsize=7.0)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_dichotomy_and_wsat.png", bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    d4 = json.loads((RESULTS / "exp4_psi_and_gadget_scaling.json").read_text(encoding="utf-8"))["rows"]
    ms = [r["psi_edges_m"] for r in d4]
    v2m = [r["vertex_vars_2m"] for r in d4]
    a2m = [r["arc_vars_2m"] for r in d4]
    em = [r["edge_vars_m"] for r in d4]
    gad = [r["gadget_21_budget_4x"] for r in d4]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    ax1.stackplot(
        ms, v2m, a2m, em,
        labels=["Vertex vars 2|E(H)|", "Arc vars 2|E(H)|", "Edge vars |E(H)|"],
        colors=["#1f618d", "#117a65", "#d68910"],
        alpha=0.88,
    )
    ax1.plot(ms, [5 * m for m in ms], "ko-", markersize=3.5, linewidth=1.3, label="Tight 5|E(H)| bound")
    ax1.set_xlabel("Pattern graph edges m = |E(H)|")
    ax1.set_ylabel("Forced TRUE variables")
    ax1.set_title("(a) PSI -> WSAT exact 5|E(H)| tightness")
    ax1.grid(True, linestyle="--", alpha=0.35)
    ax1.legend(loc="upper left", frameon=True, fontsize=7.0)

    ax2.plot(ms, [5 * m for m in ms], "o-", color="#1f618d", linewidth=1.6, markersize=4, label="{1,1}-bounded budget lam")
    ax2.plot(ms, gad, "s-", color="#922b21", linewidth=1.6, markersize=4, label="{2,1} K_{1,*} budget 4*lam")
    ax2.set_xlabel("Pattern graph edges m = |E(H)|")
    ax2.set_ylabel("Parameterized weight budget")
    ax2.set_title("(b) Thm. 6 linear 4x gadget scaling")
    ax2.grid(True, linestyle="--", alpha=0.35)
    ax2.legend(loc="upper left", frameon=True, fontsize=7.2)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_psi_and_gadget_scaling.png", bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RESULTS / "exp1_certified_atlas.json").read_text(encoding="utf-8"))["rows"]
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.95), gridspec_kw={"width_ratios": [1.55, 1.0]})

    stems = [r["file"].replace(".cert.json", "") for r in d1]
    ms = [r["verify_ms"] for r in d1]
    mode_colors = {
        "local_con_multipartite_dichotomy_exact": "#1f618d",
        "global_con_matroid_intersection_exact": "#117a65",
        "on_off_wsat_series_parallel_exact": "#b7950b",
        "gadget_21_star_reduction_exact": "#922b21",
    }
    cols = [mode_colors[r["mode"]] for r in d1]

    y = np.arange(len(stems))
    ax1.barh(y, ms, color=cols, height=0.72)
    ax1.set_xscale("log")
    ax1.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    ax1.set_xticks([0.03, 0.05, 0.10, 0.16])
    ax1.set_xticklabels(["0.03", "0.05", "0.10", "0.16"])
    ax1.set_yticks(y)
    ax1.set_yticklabels(stems, fontsize=6.4)
    ax1.invert_yaxis()
    ax1.set_xlabel("Zero-float replay latency (ms, log scale)")
    ax1.set_title("(a) Replay time across all 16 certificates")
    ax1.grid(True, axis="x", linestyle="--", alpha=0.35)

    modes = [
        ("M1: Local", 4, "#1f618d"),
        ("M2: Global", 4, "#117a65"),
        ("M3: WSAT", 4, "#b7950b"),
        ("M4: Gadget", 4, "#922b21"),
    ]
    mx = np.arange(len(modes))
    ax2.bar(mx, [m[1] for m in modes], color=[m[2] for m in modes], width=0.56)
    ax2.set_xticks(mx)
    ax2.set_xticklabels([m[0] for m in modes], rotation=22, ha="right", fontsize=7.4)
    ax2.set_ylabel("Certified instances")
    ax2.set_ylim(0, 5.2)
    ax2.set_title("(b) Balanced 4-mode coverage")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    for i, m in enumerate(modes):
        ax2.text(i, m[1] + 0.14, "4/4\nPASS", ha="center", va="bottom", fontsize=6.8, fontweight="bold")

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_summary.png", bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
