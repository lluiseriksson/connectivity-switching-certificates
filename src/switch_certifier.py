"""Pure-stdlib zero-float verifier for SWITCH-GRAPH-CONN-CERT-1.0 certificates.
Supports four exact-Z verification modes aligned with Christoph Kern, Alexander Firbas,
& Manuel Sorge (TU Wien, arXiv:2611.32927, Nov 24, 2026) "Algorithms and Complexity of
Connectivity Switching in Graphs":
  1. local_con_multipartite_dichotomy_exact (Thm 1 & Lemma 2: complete-multipartite P-path OR 4-vertex K2+K2/P4/L3,1 NP obstruction)
  2. global_con_matroid_intersection_exact  (Thms 7-8: weighted graphic cap partition spanning tree OR Edmonds rank obstruction r1(A)+r2(B)<=n-2)
  3. on_off_wsat_series_parallel_exact      (Thm 3, Lemma 4, Sec 3.3: series-parallel G_phi equivalence + PSI tight 5|E(H)| check)
  4. gadget_21_star_reduction_exact         (Thm 6 p.15: {1,1}->{2,1} K_{1,*} 4x weight forward & backward consensus audit)

Author: Lluis Eriksson
"""
from __future__ import annotations

from typing import Any, Dict, List, Set, Tuple

from src.switch_exact import (
    bfs_connected,
    build_21_star_gadget_for_switch,
    build_series_parallel_switch_graph,
    classify_4vertex_obstruction,
    eval_bformula,
    graphic_matroid_rank,
    is_acyclic,
    is_complete_multipartite_graph,
    norm_edge,
)

SCHEMA_VERSION = "SWITCH-GRAPH-CONN-CERT-1.0"


class SwitchGraphCertificateError(ValueError):
    """Raised whenever any SWITCH-GRAPH-CONN-CERT-1.0 verification check fails."""


def _assert_strict_json_types(obj: Any, path: str = "root") -> None:
    t = type(obj)
    if t is int or t is str or obj is None:
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise SwitchGraphCertificateError(f"Non-str dict key at {path}: {type(k).__name__}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    raise SwitchGraphCertificateError(f"Forbidden type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise SwitchGraphCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_edge(val: Any, n: int, name: str) -> Tuple[int, int]:
    if type(val) is not list or len(val) != 2:
        raise SwitchGraphCertificateError(f"{name} must be [u, v]")
    u, v = _parse_int(val[0], f"{name}[0]"), _parse_int(val[1], f"{name}[1]")
    if not (0 <= u < n and 0 <= v < n) or u == v:
        raise SwitchGraphCertificateError(f"{name} invalid simple edge ({u}, {v}) for n={n}")
    return norm_edge(u, v)


def _parse_1star_switches(raw: Any, n: int) -> List[List[List[Tuple[int, int]]]]:
    if type(raw) is not list or len(raw) == 0 or len(raw) > 64:
        raise SwitchGraphCertificateError("switches must be non-empty list of length <= 64")
    switches: List[List[List[Tuple[int, int]]]] = []
    for s_idx, sw in enumerate(raw):
        if type(sw) is not list or len(sw) == 0 or len(sw) > 32:
            raise SwitchGraphCertificateError(f"switches[{s_idx}] must have 1..32 positions")
        pos_list: List[List[Tuple[int, int]]] = []
        for p_idx, pos in enumerate(sw):
            if type(pos) is not list or len(pos) > 1:
                raise SwitchGraphCertificateError(f"switches[{s_idx}][{p_idx}] violates {{1*}}-bounded (<=1 edge)")
            pos_list.append([_parse_edge(e, n, f"sw[{s_idx}][{p_idx}]") for e in pos])
        switches.append(pos_list)
    return switches


def _verify_mode1_local_dichotomy(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "num_vertices", "switches",
        "source_a", "target_b", "branch",
        "config", "path_vertices", "path_switches",
        "obstruction_switch_idx", "obstruction_quad", "claimed_obstruction_type",
    }
    if set(cert.keys()) != req:
        raise SwitchGraphCertificateError(f"Mode 1 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["num_vertices"], "num_vertices")
    a = _parse_int(cert["source_a"], "source_a")
    b = _parse_int(cert["target_b"], "target_b")
    if not (2 <= n <= 64) or not (0 <= a < n and 0 <= b < n) or a == b:
        raise SwitchGraphCertificateError("Invalid num_vertices, source_a, or target_b")
    switches = _parse_1star_switches(cert["switches"], n)
    branch = cert["branch"]
    if branch not in ("tractable_path", "np_obstruction"):
        raise SwitchGraphCertificateError(f"Invalid branch: {branch!r}")

    if branch == "tractable_path":
        # Strictly enforce empty obstruction fields!
        if cert["obstruction_switch_idx"] is not None or cert["obstruction_quad"] != [] or cert["claimed_obstruction_type"] != "":
            raise SwitchGraphCertificateError("tractable_path requires empty obstruction fields")
        # Every switch-induced graph G[s] MUST be complete multipartite (Theorem 1!)
        for s_idx, sw in enumerate(switches):
            edges = [e for pos in sw for e in pos]
            verts = sorted({v for e in edges for v in e})
            ok, bad = is_complete_multipartite_graph(verts, edges)
            if not ok:
                raise SwitchGraphCertificateError(f"switches[{s_idx}] is NOT complete multipartite (K2+K1={bad})")
        cfg_raw = cert["config"]
        if type(cfg_raw) is not list or len(cfg_raw) != len(switches):
            raise SwitchGraphCertificateError("config length must match switches")
        cfg = [_parse_int(c, f"config[{i}]") for i, c in enumerate(cfg_raw)]
        realized_by_switch: List[Set[Tuple[int, int]]] = []
        for s_idx, pos_i in enumerate(cfg):
            if not (0 <= pos_i < len(switches[s_idx])):
                raise SwitchGraphCertificateError(f"config[{s_idx}]={pos_i} out of range")
            realized_by_switch.append(set(switches[s_idx][pos_i]))

        pv_raw = cert["path_vertices"]
        ps_raw = cert["path_switches"]
        if type(pv_raw) is not list or type(ps_raw) is not list or len(pv_raw) < 2 or len(ps_raw) != len(pv_raw) - 1:
            raise SwitchGraphCertificateError("Invalid path_vertices / path_switches lengths")
        pv = [_parse_int(v, f"pv[{i}]") for i, v in enumerate(pv_raw)]
        ps = [_parse_int(s, f"ps[{i}]") for i, s in enumerate(ps_raw)]
        if pv[0] != a or pv[-1] != b or len(set(pv)) != len(pv):
            raise SwitchGraphCertificateError("path_vertices must be a simple a-b path")
        if len(set(ps)) != len(ps):
            raise SwitchGraphCertificateError("path_switches must use distinct {1*}-bounded switches (Lemma 2)")
        for i in range(len(ps)):
            s_idx = ps[i]
            if not (0 <= s_idx < len(switches)):
                raise SwitchGraphCertificateError(f"path_switches[{i}] out of range")
            e = norm_edge(pv[i], pv[i + 1])
            if e not in realized_by_switch[s_idx]:
                raise SwitchGraphCertificateError(f"Path edge {e} not realized by switch {s_idx} at pos {cfg[s_idx]}")
        return {
            "verified": True,
            "mode": cert["mode"],
            "branch": branch,
            "num_switches": len(switches),
            "path_edges": len(ps),
            "transition_path_edges": 2 * len(ps),
        }

    # branch == "np_obstruction": strictly enforce empty tractable fields!
    if cert["config"] != [] or cert["path_vertices"] != [] or cert["path_switches"] != []:
        raise SwitchGraphCertificateError("np_obstruction requires empty config/path fields")
    s_idx = _parse_int(cert["obstruction_switch_idx"], "obstruction_switch_idx")
    if not (0 <= s_idx < len(switches)):
        raise SwitchGraphCertificateError("obstruction_switch_idx out of range")
    q_raw = cert["obstruction_quad"]
    if type(q_raw) is not list or len(q_raw) != 4:
        raise SwitchGraphCertificateError("obstruction_quad must have 4 vertices [u, v, w, x]")
    quad = tuple(_parse_int(v, f"quad[{i}]") for i, v in enumerate(q_raw))
    if any(not (0 <= v < n) for v in quad):
        raise SwitchGraphCertificateError("obstruction_quad vertex out of range")
    sw_edges = [e for pos in switches[s_idx] for e in pos]
    try:
        obs_type = classify_4vertex_obstruction(sw_edges, quad)  # type: ignore[arg-type]
    except ValueError as exc:
        raise SwitchGraphCertificateError(str(exc)) from exc
    if cert["claimed_obstruction_type"] != obs_type:
        raise SwitchGraphCertificateError(f"claimed_obstruction_type mismatch: exact={obs_type!r}")
    return {
        "verified": True,
        "mode": cert["mode"],
        "branch": branch,
        "obstruction_switch": s_idx,
        "obstruction_type": obs_type,
    }


def _verify_mode2_global_matroid(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "num_vertices", "switches", "position_weights",
        "budget_lambda", "outcome",
        "config", "tree_switch_indices", "claimed_config_weight", "claimed_shifted_tree_weight",
        "obstruction_A_edges", "obstruction_B_switches", "claimed_r1_A", "claimed_r2_B",
    }
    if set(cert.keys()) != req:
        raise SwitchGraphCertificateError(f"Mode 2 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["num_vertices"], "num_vertices")
    lam = _parse_int(cert["budget_lambda"], "budget_lambda")
    if not (2 <= n <= 64) or lam < 0:
        raise SwitchGraphCertificateError("Invalid num_vertices or budget_lambda")
    switches = _parse_1star_switches(cert["switches"], n)
    pw_raw = cert["position_weights"]
    if type(pw_raw) is not list or len(pw_raw) != len(switches):
        raise SwitchGraphCertificateError("position_weights length mismatch")
    pos_weights: List[List[int]] = []
    for s_idx, row in enumerate(pw_raw):
        if type(row) is not list or len(row) != len(switches[s_idx]):
            raise SwitchGraphCertificateError(f"position_weights[{s_idx}] length mismatch")
        ws = [_parse_int(w, f"pw[{s_idx}][{j}]") for j, w in enumerate(row)]
        if any(w < 0 for w in ws):
            raise SwitchGraphCertificateError(f"position_weights[{s_idx}] contains negative weight")
        pos_weights.append(ws)

    outcome = cert["outcome"]
    if outcome not in ("YES_spanning_tree", "NO_edmonds_rank_obstruction"):
        raise SwitchGraphCertificateError(f"Invalid outcome: {outcome!r}")

    if outcome == "YES_spanning_tree":
        if (
            cert["obstruction_A_edges"] != []
            or cert["obstruction_B_switches"] != []
            or cert["claimed_r1_A"] is not None
            or cert["claimed_r2_B"] is not None
        ):
            raise SwitchGraphCertificateError("YES_spanning_tree requires empty obstruction fields")
        cfg_raw = cert["config"]
        ts_raw = cert["tree_switch_indices"]
        if type(cfg_raw) is not list or len(cfg_raw) != len(switches):
            raise SwitchGraphCertificateError("config length mismatch")
        cfg = [_parse_int(c, f"config[{i}]") for i, c in enumerate(cfg_raw)]
        for s_idx, pi in enumerate(cfg):
            if not (0 <= pi < len(switches[s_idx])):
                raise SwitchGraphCertificateError(f"config[{s_idx}] out of range")
        if type(ts_raw) is not list or len(ts_raw) != n - 1:
            raise SwitchGraphCertificateError(f"tree_switch_indices must have exactly n-1={n-1} switches")
        ts = [_parse_int(s, f"ts[{i}]") for i, s in enumerate(ts_raw)]
        if len(set(ts)) != n - 1 or any(not (0 <= s < len(switches)) for s in ts):
            raise SwitchGraphCertificateError("tree_switch_indices must be n-1 distinct valid switches (partition matroid M2)")

        tree_edges: List[Tuple[int, int]] = []
        shifted_tree_w = 0
        for s_idx in ts:
            chosen_edges = switches[s_idx][cfg[s_idx]]
            if len(chosen_edges) != 1:
                raise SwitchGraphCertificateError(f"Tree switch {s_idx} selected empty position")
            e = chosen_edges[0]
            tree_edges.append(e)
            # Theorem 8 shifted edge weight w'(e) = min_{i: e in s[i]} w(s,i) - min_i w(s,i)
            w_e = min(pos_weights[s_idx][p] for p, pos in enumerate(switches[s_idx]) if e in pos)
            w_min = min(pos_weights[s_idx])
            shifted_tree_w += w_e - w_min

        if not is_acyclic(n, tree_edges) or graphic_matroid_rank(n, tree_edges) != n - 1:
            raise SwitchGraphCertificateError("Selected edges do NOT form a spanning tree in M1")

        total_min = sum(min(ws) for ws in pos_weights)
        total_cfg_w = sum(pos_weights[s][cfg[s]] for s in range(len(switches)))
        if shifted_tree_w + total_min > total_cfg_w:
            raise SwitchGraphCertificateError("Impossible: Theorem 8 telescoping inequality violated")
        if total_cfg_w > lam:
            raise SwitchGraphCertificateError(f"Configuration weight {total_cfg_w} exceeds budget lambda={lam}")
        if _parse_int(cert["claimed_config_weight"], "claimed_config_weight") != total_cfg_w:
            raise SwitchGraphCertificateError(f"claimed_config_weight mismatch: exact={total_cfg_w}")
        if _parse_int(cert["claimed_shifted_tree_weight"], "claimed_shifted_tree_weight") != shifted_tree_w:
            raise SwitchGraphCertificateError(f"claimed_shifted_tree_weight mismatch: exact={shifted_tree_w}")
        return {
            "verified": True,
            "mode": cert["mode"],
            "outcome": outcome,
            "n": n,
            "config_weight": total_cfg_w,
            "shifted_tree_weight": shifted_tree_w,
            "budget_lambda": lam,
        }

    # outcome == "NO_edmonds_rank_obstruction"
    if (
        cert["config"] != []
        or cert["tree_switch_indices"] != []
        or cert["claimed_config_weight"] is not None
        or cert["claimed_shifted_tree_weight"] is not None
    ):
        raise SwitchGraphCertificateError("NO_edmonds_rank_obstruction requires empty YES fields")
    # Every ground-set element (switch_idx, edge) MUST be covered by either A (graphic rank) or B (partition rank)!
    obsA_raw = cert["obstruction_A_edges"]
    obsB_raw = cert["obstruction_B_switches"]
    if type(obsA_raw) is not list or type(obsB_raw) is not list:
        raise SwitchGraphCertificateError("obstruction_A_edges and obstruction_B_switches must be lists")
    obsA_set: Set[Tuple[int, Tuple[int, int]]] = set()
    A_edges: List[Tuple[int, int]] = []
    for i, item in enumerate(obsA_raw):
        if type(item) is not list or len(item) != 2:
            raise SwitchGraphCertificateError(f"obsA[{i}] must be [switch_idx, [u, v]]")
        si = _parse_int(item[0], f"obsA[{i}][0]")
        e = _parse_edge(item[1], n, f"obsA[{i}][1]")
        if not (0 <= si < len(switches)):
            raise SwitchGraphCertificateError(f"obsA[{i}] invalid switch_idx")
        obsA_set.add((si, e))
        A_edges.append(e)
    obsB_set: Set[int] = set()
    for i, sv in enumerate(obsB_raw):
        si = _parse_int(sv, f"obsB[{i}]")
        if not (0 <= si < len(switches)) or si in obsB_set:
            raise SwitchGraphCertificateError(f"obsB[{i}] invalid or duplicate switch index")
        obsB_set.add(si)

    # Verify complete ground-set coverage: every (si, e) appearing in any switch position lies in A or in switches B!
    for si, sw in enumerate(switches):
        if si in obsB_set:
            continue
        for pos in sw:
            for e in pos:
                if (si, e) not in obsA_set:
                    raise SwitchGraphCertificateError(f"Ground element (switch={si}, edge={e}) NOT covered by A U B!")

    r1_A = graphic_matroid_rank(n, A_edges)
    r2_B = len(obsB_set)
    if r1_A + r2_B > n - 2:
        raise SwitchGraphCertificateError(f"Edmonds obstruction invalid: r1(A)+r2(B)={r1_A+r2_B} > n-2={n-2}")
    if _parse_int(cert["claimed_r1_A"], "claimed_r1_A") != r1_A:
        raise SwitchGraphCertificateError(f"claimed_r1_A mismatch: exact={r1_A}")
    if _parse_int(cert["claimed_r2_B"], "claimed_r2_B") != r2_B:
        raise SwitchGraphCertificateError(f"claimed_r2_B mismatch: exact={r2_B}")
    return {
        "verified": True,
        "mode": cert["mode"],
        "outcome": outcome,
        "n": n,
        "r1_A": r1_A,
        "r2_B": r2_B,
        "max_common_indep": r1_A + r2_B,
    }


def _validate_formula_ast(node: Any, vars_allowed: Set[str], depth: int = 0) -> None:
    if depth > 12 or type(node) is not dict or "op" not in node:
        raise SwitchGraphCertificateError("Invalid or too-deep formula AST node")
    op = node["op"]
    if op == "var":
        if set(node.keys()) != {"op", "name"} or type(node["name"]) is not str or node["name"] not in vars_allowed:
            raise SwitchGraphCertificateError("Invalid var node in formula AST")
    elif op == "neg":
        if set(node.keys()) != {"op", "arg"} or type(node["arg"]) is not dict or node["arg"].get("op") != "var":
            raise SwitchGraphCertificateError("neg node must wrap a var node (NNF)")
        _validate_formula_ast(node["arg"], vars_allowed, depth + 1)
    elif op in ("and", "or"):
        if set(node.keys()) != {"op", "left", "right"}:
            raise SwitchGraphCertificateError(f"{op} node requires op, left, right")
        _validate_formula_ast(node["left"], vars_allowed, depth + 1)
        _validate_formula_ast(node["right"], vars_allowed, depth + 1)
    else:
        raise SwitchGraphCertificateError(f"Unknown formula op: {op!r}")


def _verify_mode3_wsat_series_parallel(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "variables", "formula", "assignment",
        "budget_k", "claimed_formula_val", "claimed_connected",
        "psi_pattern_edges_m", "claimed_psi_tight_weight",
    }
    if set(cert.keys()) != req:
        raise SwitchGraphCertificateError(f"Mode 3 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    v_raw = cert["variables"]
    if type(v_raw) is not list or not (1 <= len(v_raw) <= 32) or any(type(v) is not str or not v for v in v_raw):
        raise SwitchGraphCertificateError("variables must be 1..32 non-empty strings")
    if len(set(v_raw)) != len(v_raw):
        raise SwitchGraphCertificateError("Duplicate variable name")
    vset = set(v_raw)
    _validate_formula_ast(cert["formula"], vset)

    asg_raw = cert["assignment"]
    if type(asg_raw) is not dict or set(asg_raw.keys()) != vset:
        raise SwitchGraphCertificateError("assignment keys must match variables exactly")
    asg = {k: _parse_int(v, f"asg[{k}]") for k, v in asg_raw.items()}
    if any(v not in (0, 1) for v in asg.values()):
        raise SwitchGraphCertificateError("assignment values must be 0 or 1")
    k_budget = _parse_int(cert["budget_k"], "budget_k")
    weight = sum(asg.values())
    if k_budget < 0 or weight > k_budget:
        raise SwitchGraphCertificateError(f"Assignment weight {weight} exceeds budget_k={k_budget}")

    fval = eval_bformula(cert["formula"], asg)
    nv, src, dst, sp_edges = build_series_parallel_switch_graph(cert["formula"])
    active_edges = [(u, v) for u, v, var, req_val in sp_edges if asg[var] == req_val]
    conn = 1 if bfs_connected(nv, active_edges, src, dst) else 0
    if fval != conn:
        raise SwitchGraphCertificateError(f"Lemma 4 equivalence failed: fval={fval} != conn={conn}")
    if _parse_int(cert["claimed_formula_val"], "claimed_formula_val") != fval:
        raise SwitchGraphCertificateError(f"claimed_formula_val mismatch: exact={fval}")
    if _parse_int(cert["claimed_connected"], "claimed_connected") != conn:
        raise SwitchGraphCertificateError(f"claimed_connected mismatch: exact={conn}")

    psi_m = _parse_int(cert["psi_pattern_edges_m"], "psi_pattern_edges_m")
    if psi_m < 1 or psi_m > 1000:
        raise SwitchGraphCertificateError("psi_pattern_edges_m must lie in [1, 1000]")
    if _parse_int(cert["claimed_psi_tight_weight"], "claimed_psi_tight_weight") != 5 * psi_m:
        raise SwitchGraphCertificateError(f"claimed_psi_tight_weight mismatch: exact={5 * psi_m}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "formula_val": fval,
        "connected": conn,
        "weight": weight,
        "sp_vertices": nv,
        "psi_tight_5m": 5 * psi_m,
    }


def _verify_mode4_gadget_21_star(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "num_orig_vertices", "orig_switches",
        "source_a", "target_b", "orig_config", "gadget_config",
        "orig_budget_lambda", "claimed_orig_weight", "claimed_gadget_weight",
    }
    if set(cert.keys()) != req:
        raise SwitchGraphCertificateError(f"Mode 4 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["num_orig_vertices"], "num_orig_vertices")
    a = _parse_int(cert["source_a"], "source_a")
    b = _parse_int(cert["target_b"], "target_b")
    lam = _parse_int(cert["orig_budget_lambda"], "orig_budget_lambda")
    if not (4 <= n <= 40) or not (0 <= a < n and 0 <= b < n) or a == b or lam < 0:
        raise SwitchGraphCertificateError("Invalid num_orig_vertices, endpoints, or budget")

    sw_raw = cert["orig_switches"]
    if type(sw_raw) is not list or not (1 <= len(sw_raw) <= 16):
        raise SwitchGraphCertificateError("orig_switches must be 1..16 {1,1}-bounded switches")
    orig_switches: List[Tuple[int, int, int, int]] = []
    for idx, sw in enumerate(sw_raw):
        if type(sw) is not list or len(sw) != 4:
            raise SwitchGraphCertificateError(f"orig_switches[{idx}] must be [v0, v1, v2, v3]")
        v0, v1, v2, v3 = (_parse_int(sw[j], f"sw[{idx}][{j}]") for j in range(4))
        if any(not (0 <= v < n) for v in (v0, v1, v2, v3)) or v0 == v2 or v1 == v3:
            raise SwitchGraphCertificateError(f"orig_switches[{idx}] invalid vertices")
        orig_switches.append((v0, v1, v2, v3))

    oc_raw = cert["orig_config"]
    gc_raw = cert["gadget_config"]
    if type(oc_raw) is not list or len(oc_raw) != len(orig_switches):
        raise SwitchGraphCertificateError("orig_config length mismatch")
    if type(gc_raw) is not list or len(gc_raw) != 4 * len(orig_switches):
        raise SwitchGraphCertificateError("gadget_config length must be 4 * |orig_switches|")
    oc = [_parse_int(v, f"oc[{i}]") for i, v in enumerate(oc_raw)]
    gc = [_parse_int(v, f"gc[{i}]") for i, v in enumerate(gc_raw)]
    if any(v not in (0, 1) for v in oc) or any(v not in (0, 1) for v in gc):
        raise SwitchGraphCertificateError("On-Off configurations must be 0 or 1")

    # Verify exact Theorem 6 backward consensus: c(s) == min(c'(s_0..s_3)) and 4*c(s) <= sum c'(s_i)
    for idx in range(len(orig_switches)):
        quad = gc[4 * idx : 4 * idx + 4]
        if oc[idx] != min(quad):
            raise SwitchGraphCertificateError(f"Backward consensus failed at switch {idx}: {oc[idx]} != min({quad})")

    orig_w = sum(oc)
    gad_w = sum(gc)
    if orig_w > lam or gad_w > 4 * lam or 4 * orig_w > gad_w:
        raise SwitchGraphCertificateError(f"Weight bounds violated: orig_w={orig_w}, gad_w={gad_w}, lam={lam}")

    # Build realized original graph and realized {2,1}-bounded K_{1,*} gadget graph
    orig_edges = [
        norm_edge(v0, v2) if oc[i] == 0 else norm_edge(v1, v3)
        for i, (v0, v1, v2, v3) in enumerate(orig_switches)
    ]
    gad_n = n + 6 * len(orig_switches)
    gad_edges: List[Tuple[int, int]] = []
    for i, (v0, v1, v2, v3) in enumerate(orig_switches):
        g = build_21_star_gadget_for_switch(v0, v1, v2, v3, n + 6 * i)
        for sub in range(4):
            # Verify each sub-switch is genuinely {2,1}-bounded and K_{1,*}-shaped
            pos0, pos1 = g["switches"][sub][0], g["switches"][sub][1]
            if sorted([len(pos0), len(pos1)]) != [1, 2]:
                raise SwitchGraphCertificateError("Internal gadget is not {2,1}-bounded")
            gad_edges.extend(g["switches"][sub][gc[4 * i + sub]])

    orig_conn = bfs_connected(n, orig_edges, a, b)
    gad_conn = bfs_connected(gad_n, gad_edges, a, b)
    if not (orig_conn and gad_conn):
        raise SwitchGraphCertificateError(f"Connectivity failed: orig={orig_conn}, gadget={gad_conn}")

    if _parse_int(cert["claimed_orig_weight"], "claimed_orig_weight") != orig_w:
        raise SwitchGraphCertificateError(f"claimed_orig_weight mismatch: exact={orig_w}")
    if _parse_int(cert["claimed_gadget_weight"], "claimed_gadget_weight") != gad_w:
        raise SwitchGraphCertificateError(f"claimed_gadget_weight mismatch: exact={gad_w}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "orig_switches": len(orig_switches),
        "gadget_switches": len(gc),
        "orig_weight": orig_w,
        "gadget_weight": gad_w,
        "both_connected": True,
    }


def verify_switch_graph_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise SwitchGraphCertificateError("Certificate root must be a dict")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise SwitchGraphCertificateError(f"Invalid schema: {cert.get('schema')!r}")
    name = cert.get("name")
    if type(name) is not str or not name.strip():
        raise SwitchGraphCertificateError(f"Certificate name must be non-empty str, got {name!r}")
    mode = cert.get("mode")
    if mode == "local_con_multipartite_dichotomy_exact":
        return _verify_mode1_local_dichotomy(cert)
    if mode == "global_con_matroid_intersection_exact":
        return _verify_mode2_global_matroid(cert)
    if mode == "on_off_wsat_series_parallel_exact":
        return _verify_mode3_wsat_series_parallel(cert)
    if mode == "gadget_21_star_reduction_exact":
        return _verify_mode4_gadget_21_star(cert)
    raise SwitchGraphCertificateError(f"Unknown mode: {mode!r}")
