"""Comprehensive verification, exhaustive cross-checks, and 57-attack red-team suite
for SWITCH-GRAPH-CONN-CERT-1.0 (Paper 29).
Author: Lluis Eriksson
"""
from __future__ import annotations

import copy
import itertools
import json
import sys
from decimal import Decimal
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.switch_certifier import (
    SwitchGraphCertificateError,
    verify_switch_graph_certificate_exact,
)
from src.switch_exact import (
    bfs_connected,
    build_series_parallel_switch_graph,
    classify_4vertex_obstruction,
    eval_bformula,
    is_complete_multipartite_graph,
)

CERT_DIR = ROOT / "results" / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / name).read_text(encoding="utf-8"))


def test_exhaustive_dichotomy_census_and_wsat_truth_tables() -> None:
    """1. Exhaustively classify all 64 labeled 4-vertex graphs without isolated vertices.
    2. Exhaustively verify Lemma 4 series-parallel equivalence across all 2^7 = 128 assignments."""
    all_e = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    no_iso = 0
    p_cnt = 0
    np_cnt = 0
    for mask in range(64):
        es = [all_e[i] for i in range(6) if (mask >> i) & 1]
        deg = [0] * 4
        for u, v in es:
            deg[u] += 1
            deg[v] += 1
        if any(d == 0 for d in deg):
            continue
        no_iso += 1
        ok, bad = is_complete_multipartite_graph([0, 1, 2, 3], es)
        if ok:
            p_cnt += 1
        else:
            assert bad is not None
            u, v, w = bad
            x = (set(range(4)) - {u, v, w}).pop()
            otype = classify_4vertex_obstruction(es, (u, v, w, x))
            assert otype in ("K2+K2", "P4", "L3,1")
            np_cnt += 1
    assert no_iso == 41  # 41 labeled graphs on 4 vertices with min degree >= 1
    assert p_cnt + np_cnt == 41
    assert p_cnt == 14 and np_cnt == 27  # 3 K2+K2 + 12 P4 + 12 L3,1 = 27!

    # Exhaustive 128-assignment Lemma 4 equivalence on 7-variable formula from Mode 3
    m3 = _load("wsat_sp_psi_k4.cert.json")
    vlist = m3["variables"]
    form = m3["formula"]
    nv, src, dst, sp_edges = build_series_parallel_switch_graph(form)
    for bits in itertools.product((0, 1), repeat=len(vlist)):
        asg = dict(zip(vlist, bits))
        fv = eval_bformula(form, asg)
        active = [(u, v) for u, v, var, rv in sp_edges if asg[var] == rv]
        cv = 1 if bfs_connected(nv, active, src, dst) else 0
        assert fv == cv


def test_all_16_certificates_verify_cleanly() -> None:
    cert_files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(cert_files) == 16
    for p in cert_files:
        cert = json.loads(p.read_text(encoding="utf-8"))
        res = verify_switch_graph_certificate_exact(cert)
        assert res["verified"] is True


def test_57_live_adversarial_red_team_attacks_rejected() -> None:
    m1_p = _load("local_tractable_multipartite.cert.json")
    m1_np = _load("local_obstruction_P4.cert.json")
    m2_yes = _load("global_yes_shifted_n8.cert.json")
    m2_no = _load("global_no_edmonds_n6.cert.json")
    m3 = _load("wsat_sp_sat_k2.cert.json")
    m4 = _load("gadget_21_chain3_mixed.cert.json")

    def mutate(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
        c = copy.deepcopy(base)
        fn(c)
        return c

    attacks: List[Tuple[str, Any]] = [
        # --- Global AST / schema / type attacks (1-11) ---
        ("01_root_not_dict", [1, 2, 3]),
        ("02_bad_schema", mutate(m1_p, lambda c: c.__setitem__("schema", "SWITCH-GRAPH-CONN-CERT-2.0"))),
        ("03_unknown_mode", mutate(m1_p, lambda c: c.__setitem__("mode", "fake_mode"))),
        ("04_empty_name", mutate(m1_p, lambda c: c.__setitem__("name", "  "))),
        ("05_float_injected", mutate(m2_yes, lambda c: c.__setitem__("budget_lambda", 22.0))),
        ("06_bool_as_int", mutate(m1_p, lambda c: c.__setitem__("num_vertices", True))),
        ("07_decimal_injected", mutate(m2_yes, lambda c: c.__setitem__("budget_lambda", Decimal("22")))),
        ("08_complex_injected", mutate(m3, lambda c: c.__setitem__("budget_k", 3 + 0j))),
        ("09_tuple_injected", mutate(m1_p, lambda c: c.__setitem__("path_vertices", (0, 1, 3, 6)))),
        ("10_non_str_key", {**m3, 99: "bad"}),
        ("11_extra_key", mutate(m3, lambda c: c.__setitem__("rogue", 1))),

        # --- Mode 1: Local-Con dichotomy attacks (12-25) ---
        ("12_m1_missing_key", mutate(m1_p, lambda c: c.pop("branch"))),
        ("13_m1_bad_branch", mutate(m1_p, lambda c: c.__setitem__("branch", "maybe"))),
        ("14_m1_source_eq_target", mutate(m1_p, lambda c: c.__setitem__("target_b", 0))),
        ("15_m1_self_loop_edge", mutate(m1_p, lambda c: c["switches"][0].__setitem__(0, [[0, 0]]))),
        ("16_m1_violates_1star", mutate(m1_p, lambda c: c["switches"][0].__setitem__(0, [[0, 1], [1, 2]]))),
        ("17_m1_tractable_dirty_obs", mutate(m1_p, lambda c: c.__setitem__("claimed_obstruction_type", "P4"))),
        ("18_m1_tractable_not_multipartite", mutate(m1_p, lambda c: c["switches"][3].append([[4, 5]]))),
        ("19_m1_path_wrong_end", mutate(m1_p, lambda c: c["path_vertices"].__setitem__(-1, 5))),
        ("20_m1_path_reuses_switch", mutate(m1_p, lambda c: c["path_switches"].__setitem__(1, 0))),
        ("21_m1_path_edge_not_realized", mutate(m1_p, lambda c: c["config"].__setitem__(0, 1))),
        ("22_m1_np_dirty_config", mutate(m1_np, lambda c: c.__setitem__("config", [0, 0]))),
        ("23_m1_np_wrong_obs_type", mutate(m1_np, lambda c: c.__setitem__("claimed_obstruction_type", "L3,1"))),
        ("24_m1_np_duplicate_quad_vertex", mutate(m1_np, lambda c: c.__setitem__("obstruction_quad", [0, 1, 2, 2]))),
        ("25_m1_np_invalid_quad_not_obs", mutate(m1_np, lambda c: c.__setitem__("obstruction_quad", [0, 2, 1, 3]))),

        # --- Mode 2: Global-Con matroid intersection attacks (26-38) ---
        ("26_m2_missing_key", mutate(m2_yes, lambda c: c.pop("outcome"))),
        ("27_m2_neg_weight", mutate(m2_yes, lambda c: c["position_weights"][0].__setitem__(0, -1))),
        ("28_m2_yes_dirty_obs", mutate(m2_yes, lambda c: c.__setitem__("claimed_r1_A", 0))),
        ("29_m2_yes_duplicate_tree_sw", mutate(m2_yes, lambda c: c["tree_switch_indices"].__setitem__(0, 1))),
        ("30_m2_yes_cycle_not_tree", mutate(m2_yes, lambda c: c["config"].__setitem__(2, 0))),
        ("31_m2_yes_exceeds_budget", mutate(m2_yes, lambda c: c.__setitem__("budget_lambda", 20))),
        ("32_m2_yes_wrong_cfg_weight", mutate(m2_yes, lambda c: c.__setitem__("claimed_config_weight", 20))),
        ("33_m2_yes_wrong_shifted_w", mutate(m2_yes, lambda c: c.__setitem__("claimed_shifted_tree_weight", 10))),
        ("34_m2_no_dirty_yes_field", mutate(m2_no, lambda c: c.__setitem__("claimed_config_weight", 0))),
        ("35_m2_no_uncovered_ground_elem", mutate(m2_no, lambda c: c["obstruction_A_edges"].pop())),
        ("36_m2_no_duplicate_B_switch", mutate(m2_no, lambda c: c["obstruction_B_switches"].append(4))),
        ("37_m2_no_rank_too_high", mutate(m2_no, lambda c: c["obstruction_B_switches"].append(0))),
        ("38_m2_no_wrong_r1_A", mutate(m2_no, lambda c: c.__setitem__("claimed_r1_A", 2))),

        # --- Mode 3: Series-Parallel WSAT & PSI 5m attacks (39-47) ---
        ("39_m3_missing_key", mutate(m3, lambda c: c.pop("budget_k"))),
        ("40_m3_dup_variable", mutate(m3, lambda c: c["variables"].append("x1"))),
        ("41_m3_unknown_var_in_formula", mutate(m3, lambda c: c["formula"]["left"].__setitem__("left", {"op": "var", "name": "z9"}))),
        ("42_m3_non_nnf_neg", mutate(m3, lambda c: c.__setitem__("formula", {"op": "neg", "arg": c["formula"]}))),
        ("43_m3_nonbinary_asg", mutate(m3, lambda c: c["assignment"].__setitem__("x1", 2))),
        ("44_m3_exceeds_budget_k", mutate(m3, lambda c: c.__setitem__("budget_k", 1))),
        ("45_m3_wrong_formula_val", mutate(m3, lambda c: c.__setitem__("claimed_formula_val", 0))),
        ("46_m3_wrong_connected", mutate(m3, lambda c: c.__setitem__("claimed_connected", 0))),
        ("47_m3_wrong_psi_5m", mutate(m3, lambda c: c.__setitem__("claimed_psi_tight_weight", 14))),

        # --- Mode 4: {1,1}->{2,1} K_{1,*} gadget attacks (48-57) ---
        ("48_m4_missing_key", mutate(m4, lambda c: c.pop("gadget_config"))),
        ("49_m4_bad_gadget_len", mutate(m4, lambda c: c["gadget_config"].pop())),
        ("50_m4_nonbinary_cfg", mutate(m4, lambda c: c["orig_config"].__setitem__(0, 2))),
        ("51_m4_consensus_broken", mutate(m4, lambda c: c["gadget_config"].__setitem__(4, 0))),
        ("52_m4_orig_exceeds_lam", mutate(m4, lambda c: c.__setitem__("orig_budget_lambda", 0))),
        ("53_m4_gad_exceeds_4lam", mutate(m4, lambda c: c["gadget_config"].__setitem__(0, 1))),
        ("54_m4_disconnected_orig", mutate(m4, lambda c: c.__setitem__("orig_config", [1, 1, 0]) or c.__setitem__("gadget_config", [1,1,1,1,1,1,1,1,0,0,0,0]) or c.__setitem__("orig_budget_lambda", 3))),
        ("55_m4_wrong_orig_w", mutate(m4, lambda c: c.__setitem__("claimed_orig_weight", 2))),
        ("56_m4_wrong_gad_w", mutate(m4, lambda c: c.__setitem__("claimed_gadget_weight", 5))),
        ("57_m4_self_loop_orig_sw", mutate(m4, lambda c: c["orig_switches"].__setitem__(0, [0, 0, 0, 2]))),
    ]

    assert len(attacks) == 57
    for label, payload in attacks:
        with pytest.raises(SwitchGraphCertificateError, match="."):
            verify_switch_graph_certificate_exact(payload)
