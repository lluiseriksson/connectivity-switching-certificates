"""Generate all 16 canonical SWITCH-GRAPH-CONN-CERT-1.0 certificates and 4 experiment JSONs for Paper 29.
ZERO floating-point arithmetic in any certificate generation or verification.
Author: Lluis Eriksson
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.switch_certifier import verify_switch_graph_certificate_exact
from src.switch_exact import (
    bfs_connected,
    build_series_parallel_switch_graph,
    eval_bformula,
    graphic_matroid_rank,
)

RESULTS = ROOT / "results"
CERT_DIR = RESULTS / "certificates"
CERT_DIR.mkdir(parents=True, exist_ok=True)


def _emit_cert(filename: str, cert: Dict[str, Any]) -> Dict[str, Any]:
    path = CERT_DIR / filename
    path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    t0 = time.perf_counter()
    res = verify_switch_graph_certificate_exact(cert)
    dt_ms = round((time.perf_counter() - t0) * 1000.0, 3)
    return {"file": filename, "mode": cert["mode"], "verify_ms": dt_ms, "summary": res}


def main() -> None:
    atlas_rows: List[Dict[str, Any]] = []

    # =========================================================================
    # MODE 1: 4 Local-Con Switching Dichotomy Certificates (Thm 1 & Lemma 2)
    # =========================================================================
    # 1a. Tractable complete-multipartite path: K_3, K_{1,3}, K_{2,2}, K_2 switches
    atlas_rows.append(_emit_cert("local_tractable_multipartite.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "local_con_multipartite_dichotomy_exact",
        "name": "mode1_tractable_multipartite_path",
        "num_vertices": 7,
        "switches": [
            [[[0, 1]], [[1, 2]], [[0, 2]]],                       # K_3 (complete 3-partite)
            [[[1, 3]], [[1, 4]], [[1, 5]]],                       # K_{1,3} (complete bipartite)
            [[[3, 4]], [[3, 6]], [[5, 4]], [[5, 6]]],             # K_{2,2} (complete bipartite)
            [[[6, 2]], []],                                       # K_2 (complete bipartite)
        ],
        "source_a": 0,
        "target_b": 6,
        "branch": "tractable_path",
        "config": [0, 0, 1, 0],
        "path_vertices": [0, 1, 3, 6],
        "path_switches": [0, 1, 2],
        "obstruction_switch_idx": None,
        "obstruction_quad": [],
        "claimed_obstruction_type": "",
    }))

    # 1b. NP-hard obstruction: K2 + K2
    atlas_rows.append(_emit_cert("local_obstruction_K2K2.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "local_con_multipartite_dichotomy_exact",
        "name": "mode1_np_obstruction_K2K2",
        "num_vertices": 5,
        "switches": [
            [[[0, 1]], [[2, 3]]],   # K_2 + K_2!
            [[[3, 4]]],
        ],
        "source_a": 0,
        "target_b": 4,
        "branch": "np_obstruction",
        "config": [],
        "path_vertices": [],
        "path_switches": [],
        "obstruction_switch_idx": 0,
        "obstruction_quad": [0, 1, 2, 3],
        "claimed_obstruction_type": "K2+K2",
    }))

    # 1c. NP-hard obstruction: P4 (path 0-1-3-2 -> u=0, v=1, w=2, x=3: uv in E, uw/vw not in E, wx in E, vx in E, ux not in E)
    atlas_rows.append(_emit_cert("local_obstruction_P4.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "local_con_multipartite_dichotomy_exact",
        "name": "mode1_np_obstruction_P4",
        "num_vertices": 5,
        "switches": [
            [[[0, 1]], [[1, 3]], [[3, 2]]],  # P_4: 0-1-3-2
            [[[2, 4]]],
        ],
        "source_a": 0,
        "target_b": 4,
        "branch": "np_obstruction",
        "config": [],
        "path_vertices": [],
        "path_switches": [],
        "obstruction_switch_idx": 0,
        "obstruction_quad": [0, 1, 2, 3],
        "claimed_obstruction_type": "P4",
    }))

    # 1d. NP-hard obstruction: L3,1 (paw: triangle 0-1-3 + pendant 3-2 -> u=0, v=1, w=2, x=3)
    atlas_rows.append(_emit_cert("local_obstruction_L31.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "local_con_multipartite_dichotomy_exact",
        "name": "mode1_np_obstruction_L31",
        "num_vertices": 5,
        "switches": [
            [[[0, 1]], [[0, 3]], [[1, 3]], [[3, 2]]],  # L_{3,1} (paw)
            [[[2, 4]]],
        ],
        "source_a": 0,
        "target_b": 4,
        "branch": "np_obstruction",
        "config": [],
        "path_vertices": [],
        "path_switches": [],
        "obstruction_switch_idx": 0,
        "obstruction_quad": [0, 1, 2, 3],
        "claimed_obstruction_type": "L3,1",
    }))

    # =========================================================================
    # MODE 2: 4 Global-Con Switching Matroid Intersection Certificates (Thms 7-8)
    # =========================================================================
    # 2a. YES weighted spanning tree (n=5, 6 switches)
    atlas_rows.append(_emit_cert("global_yes_weighted_n5.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "global_con_matroid_intersection_exact",
        "name": "mode2_yes_weighted_n5",
        "num_vertices": 5,
        "switches": [
            [[[0, 1]], [[0, 2]]],
            [[[1, 2]], [[1, 3]]],
            [[[2, 3]], [[2, 4]]],
            [[[3, 4]], [[0, 4]]],
            [[[0, 3]], []],
            [[[1, 4]], []],
        ],
        "position_weights": [
            [2, 5],
            [4, 1],
            [3, 2],
            [6, 1],
            [5, 0],
            [4, 0],
        ],
        "budget_lambda": 7,
        "outcome": "YES_spanning_tree",
        "config": [0, 1, 1, 1, 1, 1],  # edges: (0,1), (1,3), (2,4), (0,4) -> spanning tree! weights: 2+1+2+1+0+0=6
        "tree_switch_indices": [0, 1, 2, 3],
        "claimed_config_weight": 6,
        "claimed_shifted_tree_weight": 0,  # each tree switch picked its min-weight position!
        "obstruction_A_edges": [],
        "obstruction_B_switches": [],
        "claimed_r1_A": None,
        "claimed_r2_B": None,
    }))

    # 2b. YES weighted spanning tree with non-zero shifted tree weight (n=8, 9 switches)
    atlas_rows.append(_emit_cert("global_yes_shifted_n8.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "global_con_matroid_intersection_exact",
        "name": "mode2_yes_shifted_n8",
        "num_vertices": 8,
        "switches": [
            [[[0, 1]], [[0, 2]]],     # min=1, pick pos1 (0,2) w=3 -> shift=2
            [[[1, 2]], [[1, 3]]],     # min=2, pick pos0 (1,2) w=2 -> shift=0
            [[[2, 3]], [[2, 4]]],     # min=1, pick pos1 (2,4) w=4 -> shift=3
            [[[3, 4]], [[3, 5]]],     # min=2, pick pos1 (3,5) w=2 -> shift=0
            [[[4, 5]], [[4, 6]]],     # min=1, pick pos1 (4,6) w=5 -> shift=4
            [[[5, 6]], [[5, 7]]],     # min=2, pick pos1 (5,7) w=2 -> shift=0
            [[[6, 7]], [[0, 3]]],     # min=1, pick pos1 (0,3) w=3 -> shift=2
            [[[0, 7]], []],           # unused min=0
            [[[1, 6]], []],           # unused min=0
        ],
        "position_weights": [
            [1, 3],
            [2, 6],
            [1, 4],
            [5, 2],
            [1, 5],
            [7, 2],
            [1, 3],
            [9, 0],
            [8, 0],
        ],
        "budget_lambda": 22,
        "outcome": "YES_spanning_tree",
        "config": [1, 0, 1, 1, 1, 1, 1, 1, 1],
        # Tree edges: (0,2),(1,2),(2,4),(3,5),(4,6),(5,7),(0,3) -> connected & acyclic on 8 verts!
        # Weights: 3+2+4+2+5+2+3+0+0 = 21; mins sum = 1+2+1+2+1+2+1+0+0 = 10; shifted = 11!
        "tree_switch_indices": [0, 1, 2, 3, 4, 5, 6],
        "claimed_config_weight": 21,
        "claimed_shifted_tree_weight": 11,
        "obstruction_A_edges": [],
        "obstruction_B_switches": [],
        "claimed_r1_A": None,
        "claimed_r2_B": None,
    }))

    # 2c. NO Edmonds matroid-intersection rank obstruction (n=6: 3 clusters {0,1,2}, {3,4}, {5}, only 1 bridge switch!)
    # Switches 0..3 stay inside {0,1,2} (rank 2) and {3,4} (rank 1) -> A has r1(A) = 3; switch 4 is the ONLY bridge -> B={4}, r2(B)=1 -> 3+1=4 <= n-2=4!
    atlas_rows.append(_emit_cert("global_no_edmonds_n6.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "global_con_matroid_intersection_exact",
        "name": "mode2_no_edmonds_rank_n6",
        "num_vertices": 6,
        "switches": [
            [[[0, 1]], [[1, 2]]],
            [[[0, 2]], [[0, 1]]],
            [[[3, 4]], []],
            [[[1, 2]], [[0, 2]]],
            [[[2, 3]], [[4, 5]], [[0, 5]]],  # single switch covering ALL cross-cluster bridges!
        ],
        "position_weights": [[1, 1], [1, 1], [1, 0], [1, 1], [1, 1, 1]],
        "budget_lambda": 10,
        "outcome": "NO_edmonds_rank_obstruction",
        "config": [],
        "tree_switch_indices": [],
        "claimed_config_weight": None,
        "claimed_shifted_tree_weight": None,
        "obstruction_A_edges": [
            [0, [0, 1]], [0, [1, 2]],
            [1, [0, 2]], [1, [0, 1]],
            [2, [3, 4]],
            [3, [1, 2]], [3, [0, 2]],
        ],
        "obstruction_B_switches": [4],
        "claimed_r1_A": 3,
        "claimed_r2_B": 1,
    }))

    # 2d. NO Edmonds rank obstruction (n=8: 4 clusters of size 2 => r1(A)=4, only 2 bridge switches => r2(B)=2 -> 4+2=6 <= n-2=6!)
    atlas_rows.append(_emit_cert("global_no_edmonds_n8.cert.json", {
        "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
        "mode": "global_con_matroid_intersection_exact",
        "name": "mode2_no_edmonds_rank_n8",
        "num_vertices": 8,
        "switches": [
            [[[0, 1]], []],
            [[[2, 3]], []],
            [[[4, 5]], []],
            [[[6, 7]], []],
            [[[1, 2]], [[3, 4]], [[5, 6]]],
            [[[0, 3]], [[2, 5]], [[4, 7]]],
        ],
        "position_weights": [[1, 0], [1, 0], [1, 0], [1, 0], [1, 1, 1], [1, 1, 1]],
        "budget_lambda": 20,
        "outcome": "NO_edmonds_rank_obstruction",
        "config": [],
        "tree_switch_indices": [],
        "claimed_config_weight": None,
        "claimed_shifted_tree_weight": None,
        "obstruction_A_edges": [
            [0, [0, 1]], [1, [2, 3]], [2, [4, 5]], [3, [6, 7]],
        ],
        "obstruction_B_switches": [4, 5],
        "claimed_r1_A": 4,
        "claimed_r2_B": 2,
    }))

    # =========================================================================
    # MODE 3: 4 Series-Parallel On-Off WSAT & PSI 5|E(H)| Certificates (Thm 3, Lemma 4)
    # =========================================================================
    f1 = {
        "op": "and",
        "left": {"op": "or", "left": {"op": "var", "name": "x1"}, "right": {"op": "var", "name": "x2"}},
        "right": {"op": "or", "left": {"op": "var", "name": "x3"}, "right": {"op": "neg", "arg": {"op": "var", "name": "x4"}}},
    }
    f2 = {
        "op": "and",
        "left": {"op": "var", "name": "x1"},
        "right": {"op": "and", "left": {"op": "var", "name": "x2"}, "right": {"op": "or", "left": {"op": "var", "name": "x3"}, "right": {"op": "var", "name": "x4"}}},
    }
    f3 = {
        "op": "and",
        "left": {"op": "or", "left": {"op": "and", "left": {"op": "var", "name": "x1"}, "right": {"op": "var", "name": "x2"}},
                 "right": {"op": "and", "left": {"op": "var", "name": "x3"}, "right": {"op": "neg", "arg": {"op": "var", "name": "x4"}}}},
        "right": {"op": "or", "left": {"op": "var", "name": "x5"}, "right": {"op": "neg", "arg": {"op": "var", "name": "x6"}}},
    }
    f4 = {
        "op": "and",
        "left": {"op": "and", "left": {"op": "var", "name": "x1"}, "right": {"op": "or", "left": {"op": "var", "name": "x2"}, "right": {"op": "var", "name": "x3"}}},
        "right": {"op": "and", "left": {"op": "or", "left": {"op": "var", "name": "x4"}, "right": {"op": "var", "name": "x5"}},
                  "right": {"op": "or", "left": {"op": "var", "name": "x6"}, "right": {"op": "neg", "arg": {"op": "var", "name": "x7"}}}},
    }

    m3_specs = [
        ("wsat_sp_sat_k2.cert.json", "mode3_wsat_sat_k2", ["x1", "x2", "x3", "x4"], f1, {"x1": 1, "x2": 0, "x3": 1, "x4": 1}, 3, 3),
        ("wsat_sp_unsat_k1.cert.json", "mode3_wsat_unsat_k1", ["x1", "x2", "x3", "x4"], f2, {"x1": 1, "x2": 0, "x3": 0, "x4": 0}, 1, 4),
        ("wsat_sp_deep_sat_k3.cert.json", "mode3_wsat_deep_k3", ["x1", "x2", "x3", "x4", "x5", "x6"], f3, {"x1": 1, "x2": 1, "x3": 0, "x4": 0, "x5": 1, "x6": 1}, 4, 6),
        ("wsat_sp_psi_k4.cert.json", "mode3_wsat_psi_k4", ["x1", "x2", "x3", "x4", "x5", "x6", "x7"], f4, {"x1": 1, "x2": 1, "x3": 0, "x4": 1, "x5": 0, "x6": 0, "x7": 0}, 3, 10),
    ]
    for fname, cname, vlist, form, asg, bud, psi_m in m3_specs:
        fv = eval_bformula(form, asg)
        atlas_rows.append(_emit_cert(fname, {
            "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
            "mode": "on_off_wsat_series_parallel_exact",
            "name": cname,
            "variables": vlist,
            "formula": form,
            "assignment": asg,
            "budget_k": bud,
            "claimed_formula_val": fv,
            "claimed_connected": fv,
            "psi_pattern_edges_m": psi_m,
            "claimed_psi_tight_weight": 5 * psi_m,
        }))

    # =========================================================================
    # MODE 4: 4 {1,1} -> {2,1} K_{1,*} Gadget Reduction Certificates (Thm 6 p.15)
    # =========================================================================
    m4_specs = [
        (
            "gadget_21_single_on.cert.json", "mode4_gadget_single_on",
            4, [[0, 1, 2, 3]], 1, 3,
            [1], [1, 1, 1, 1], 1,
        ),
        (
            "gadget_21_chain3_mixed.cert.json", "mode4_gadget_chain3",
            6, [[0, 0, 1, 2], [1, 2, 3, 4], [3, 4, 5, 5]], 0, 5,
            [0, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1], 2,
            # Wait: orig edges: sw0 pos0=(0,1), sw1 pos1=(2,4) -> not connected! Let's make connected chain!
        ),
    ]
    # Replace m4_specs with 4 cleanly connected switch chains!
    m4_specs_clean = [
        (
            "gadget_21_single_on.cert.json", "mode4_gadget_single_on",
            4, [[0, 1, 2, 3]], 1, 3,
            [1], [1, 1, 1, 1], 1,
        ),
        (
            "gadget_21_chain3_mixed.cert.json", "mode4_gadget_chain3",
            6,
            [[0, 0, 1, 2], [2, 1, 4, 3], [3, 4, 5, 5]],  # pos0: (0,1),(2,4),(3,5); pos1: (0,2),(1,3),(4,5)
            # config [0, 1, 0]: (0,1) -> (1,3) -> (3,5)! Connected 0->1->3->5, orig_w=1, gad_w=4!
            0, 5, [0, 1, 0], [0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0], 1,
        ),
        (
            "gadget_21_asymmetric_backward.cert.json", "mode4_gadget_asymmetric_min",
            6,
            # 2 active switches on path 0->2->5 + 1 unused bypass switch with non-uniform [0,0,0,1] (min=0, sum=1!)
            [[0, 1, 2, 3], [1, 2, 4, 5], [0, 3, 4, 5]],
            0, 5, [0, 1, 0], [0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1], 2,
            # orig_w=1 <= 2, gad_w=5 <= 8, 4*1 = 4 < 5!
        ),
        (
            "gadget_21_chain5_path.cert.json", "mode4_gadget_chain5",
            8,
            [
                [0, 0, 1, 2],  # pos1: (0,2)
                [1, 2, 3, 3],  # pos1: (2,3)
                [3, 2, 4, 5],  # pos0: (3,4)
                [5, 4, 6, 6],  # pos1: (4,6)
                [6, 5, 7, 7],  # pos0: (6,7)
            ],
            0, 7, [1, 1, 0, 1, 0],
            [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0], 3,
        ),
    ]
    for fname, cname, n_orig, osw, sa, tb, oc, gc, lam in m4_specs_clean:
        atlas_rows.append(_emit_cert(fname, {
            "schema": "SWITCH-GRAPH-CONN-CERT-1.0",
            "mode": "gadget_21_star_reduction_exact",
            "name": cname,
            "num_orig_vertices": n_orig,
            "orig_switches": osw,
            "source_a": sa,
            "target_b": tb,
            "orig_config": oc,
            "gadget_config": gc,
            "orig_budget_lambda": lam,
            "claimed_orig_weight": sum(oc),
            "claimed_gadget_weight": sum(gc),
        }))

    (RESULTS / "exp1_certified_atlas.json").write_text(
        json.dumps({"experiment": "exp1_certified_atlas", "count": len(atlas_rows), "rows": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 2: Exhaustive Truth-Table Verification of Lemma 4 Series-Parallel G_phi
    # =========================================================================
    exp2_rows = []
    for label, vlist, form in [("F1_4var", ["x1", "x2", "x3", "x4"], f1),
                               ("F2_4var", ["x1", "x2", "x3", "x4"], f2),
                               ("F3_6var", ["x1", "x2", "x3", "x4", "x5", "x6"], f3),
                               ("F4_7var", ["x1", "x2", "x3", "x4", "x5", "x6", "x7"], f4)]:
        nv, src, dst, sp_edges = build_series_parallel_switch_graph(form)
        total = 1 << len(vlist)
        sat_cnt = 0
        matches = 0
        for bits in itertools.product((0, 1), repeat=len(vlist)):
            asg = dict(zip(vlist, bits))
            fv = eval_bformula(form, asg)
            active = [(u, v) for u, v, var, rv in sp_edges if asg[var] == rv]
            cv = 1 if bfs_connected(nv, active, src, dst) else 0
            if fv == cv:
                matches += 1
            sat_cnt += fv
        exp2_rows.append({
            "formula": label,
            "num_vars": len(vlist),
            "sp_vertices": nv,
            "sp_edges": len(sp_edges),
            "total_assignments": total,
            "exact_matches": matches,
            "sat_count": sat_cnt,
        })
    (RESULTS / "exp2_wsat_truth_table_sweep.json").write_text(
        json.dumps({"experiment": "exp2_wsat_truth_table_sweep", "rows": exp2_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 3: Exhaustive 4-Vertex Switch Dichotomy Census (All 11 non-iso 4-vertex graphs without isolated verts)
    # =========================================================================
    # Enumerate all 64 labeled graphs on 4 vertices without isolated vertices -> exact P vs NP count!
    all_edges_4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    p_count = 0
    obs_counts = {"K2+K2": 0, "P4": 0, "L3,1": 0}
    from src.switch_exact import is_complete_multipartite_graph, classify_4vertex_obstruction
    for mask in range(1 << 6):
        es = [all_edges_4[idx] for idx in range(6) if (mask >> idx) & 1]
        deg = [0, 0, 0, 0]
        for u, v in es:
            deg[u] += 1
            deg[v] += 1
        if any(d == 0 for d in deg):
            continue
        ok, bad = is_complete_multipartite_graph([0, 1, 2, 3], es)
        if ok:
            p_count += 1
        else:
            assert bad is not None
            u, v, w = bad
            x = (set(range(4)) - {u, v, w}).pop()
            otype = classify_4vertex_obstruction(es, (u, v, w, x))
            obs_counts[otype] += 1
    exp3 = {
        "experiment": "exp3_4vertex_dichotomy_census",
        "total_no_isolated": p_count + sum(obs_counts.values()),
        "complete_multipartite_P": p_count,
        "np_K2_plus_K2": obs_counts["K2+K2"],
        "np_P4": obs_counts["P4"],
        "np_L31": obs_counts["L3,1"],
    }
    (RESULTS / "exp3_4vertex_dichotomy_census.json").write_text(
        json.dumps(exp3, indent=2) + "\n", encoding="utf-8"
    )

    # =========================================================================
    # EXP 4: PSI Tight Weight 5|E(H)| & {2,1} Gadget 4x Scaling Table
    # =========================================================================
    exp4_rows = []
    for m in (1, 2, 3, 4, 6, 8, 10, 15):
        exp4_rows.append({
            "psi_edges_m": m,
            "vertex_vars_2m": 2 * m,
            "arc_vars_2m": 2 * m,
            "edge_vars_m": m,
            "psi_tight_5m": 5 * m,
            "gadget_21_budget_4x": 4 * (5 * m),
        })
    (RESULTS / "exp4_psi_and_gadget_scaling.json").write_text(
        json.dumps({"experiment": "exp4_psi_and_gadget_scaling", "rows": exp4_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"[PASS] Generated & verified {len(atlas_rows)}/16 exact-Z certificates and 4 experiment JSONs.")
    for r in atlas_rows:
        print(f"  {r['file']:44s} {r['verify_ms']:6.3f} ms  {r['summary']}")


if __name__ == "__main__":
    main()
