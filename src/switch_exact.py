"""Pure-stdlib exact-Z switch-graph, matroid-intersection, and WSAT reduction engine for Paper 29:
Algorithms and Complexity of Connectivity Switching in Graphs
(Christoph Kern, Alexander Firbas, & Manuel Sorge, TU Wien, arXiv:2611.32927, Nov 24, 2026).

ZERO floating-point arithmetic anywhere.
Author: Lluis Eriksson
"""
from __future__ import annotations

from collections import deque
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple


def norm_edge(u: int, v: int) -> Tuple[int, int]:
    if u == v:
        raise ValueError(f"Self-loop ({u}, {v}) forbidden in simple switch graph")
    return (u, v) if u < v else (v, u)


def connected_components_count(n: int, edges: Sequence[Tuple[int, int]]) -> int:
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    comps = n
    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv
            comps -= 1
    return comps


def graphic_matroid_rank(n: int, edges: Sequence[Tuple[int, int]]) -> int:
    """Exact rank of edge set in the graphic matroid M_1 = n - #connected_components."""
    return n - connected_components_count(n, edges)


def is_acyclic(n: int, edges: Sequence[Tuple[int, int]]) -> bool:
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        parent[ru] = rv
    return True


def is_complete_multipartite_graph(vertices: Sequence[int], edges: Sequence[Tuple[int, int]]) -> Tuple[bool, Optional[Tuple[int, int, int]]]:
    """Check if simple graph (vertices, edges) is complete multipartite iff non-adjacency is transitive
    (no induced K_2 + K_1). Returns (True, None) or (False, (u, v, w)) with uv in E, uw, vw not in E."""
    vset = sorted(set(vertices))
    eset = {norm_edge(u, v) for u, v in edges}
    for u, v in sorted(eset):
        for w in vset:
            if w == u or w == v:
                continue
            if norm_edge(u, w) not in eset and norm_edge(v, w) not in eset:
                return False, (u, v, w)
    return True, None


def classify_4vertex_obstruction(edges: Sequence[Tuple[int, int]], quad: Tuple[int, int, int, int]) -> str:
    """Given (u, v, w, x) with uv in E, uw, vw not in E, wx in E, classify H[{u,v,w,x}]
    into one of Kern-Firbas-Sorge p. 8 exact obstruction types: 'K2+K2', 'P4', or 'L3,1'."""
    u, v, w, x = quad
    if len({u, v, w, x}) != 4:
        raise ValueError("Obstruction vertices must be 4 distinct vertices")
    eset = {norm_edge(a, b) for a, b in edges}
    if norm_edge(u, v) not in eset:
        raise ValueError("Require uv in E(H)")
    if norm_edge(u, w) in eset or norm_edge(v, w) in eset:
        raise ValueError("Require uw, vw not in E(H)")
    if norm_edge(w, x) not in eset:
        raise ValueError("Require wx in E(H) (no isolated vertices)")
    ux = norm_edge(u, x) in eset
    vx = norm_edge(v, x) in eset
    if not ux and not vx:
        return "K2+K2"
    if ux and vx:
        return "L3,1"
    return "P4"


def eval_bformula(formula: Dict[str, Any], assign: Dict[str, int]) -> int:
    """Evaluate exact Boolean formula AST {'op': 'var'|'neg'|'and'|'or', ...} -> 0 or 1."""
    op = formula["op"]
    if op == "var":
        return assign[formula["name"]]
    if op == "neg":
        return 1 - eval_bformula(formula["arg"], assign)
    if op == "and":
        return 1 if (eval_bformula(formula["left"], assign) == 1 and eval_bformula(formula["right"], assign) == 1) else 0
    if op == "or":
        return 1 if (eval_bformula(formula["left"], assign) == 1 or eval_bformula(formula["right"], assign) == 1) else 0
    raise ValueError(f"Unknown formula op: {op!r}")


def build_series_parallel_switch_graph(
    formula: Dict[str, Any],
) -> Tuple[int, int, int, List[Tuple[int, int, str, int]]]:
    """Build exact Lemma 4 On-Off series-parallel switch graph G_phi from formula AST.
    Returns (num_vertices, source_a, target_b, edges) where each edge is (u, v, var_name, required_val)."""
    next_v = 0
    edges: List[Tuple[int, int, str, int]] = []

    def new_v() -> int:
        nonlocal next_v
        v = next_v
        next_v += 1
        return v

    def rec(node: Dict[str, Any], a: int, b: int) -> None:
        op = node["op"]
        if op == "var":
            edges.append((a, b, node["name"], 1))
        elif op == "neg":
            if node["arg"]["op"] != "var":
                raise ValueError("Negation in Lemma 4 NNF applies to variables")
            edges.append((a, b, node["arg"]["name"], 0))
        elif op == "and":
            mid = new_v()
            rec(node["left"], a, mid)
            rec(node["right"], mid, b)
        elif op == "or":
            rec(node["left"], a, b)
            rec(node["right"], a, b)
        else:
            raise ValueError(f"Unsupported op {op!r}")

    src = new_v()
    dst = new_v()
    rec(formula, src, dst)
    return next_v, src, dst, edges


def bfs_connected(n: int, edges: Sequence[Tuple[int, int]], src: int, dst: int) -> bool:
    adj: List[List[int]] = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = {src}
    q = deque([src])
    while q:
        cur = q.popleft()
        if cur == dst:
            return True
        for nxt in adj[cur]:
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return False


def build_21_star_gadget_for_switch(
    v0: int, v1: int, v2: int, v3: int, base_aux: int
) -> Dict[str, Any]:
    """Exact page 15 {1,1}-bounded -> {2,1}-bounded K_{1,*} gadget for a single switch s
    with pos 0 = {v0 v2} and pos 1 = {v1 v3}.
    Auxiliary vertices: u0=base, u1=base+1, u2=base+2, u3=base+3, w0=base+4, w1=base+5.
    4 switches s0, s1, s2, s3 where for i,j in [2]:
      s_{i+2j}[i]     = {(v_{i+2j}, u_{i+2j})}
      s_{i+2j}[1 - i] = {(u_{2j}, u_{1+2j}), (u_{i+2j}, w_i)}
    """
    vs = [v0, v1, v2, v3]
    us = [base_aux + r for r in range(4)]
    ws = [base_aux + 4, base_aux + 5]
    switches: List[List[List[Tuple[int, int]]]] = [[[], []] for _ in range(4)]
    for i in (0, 1):
        for j in (0, 1):
            idx = i + 2 * j
            switches[idx][i] = [norm_edge(vs[idx], us[idx])]
            switches[idx][1 - i] = [
                norm_edge(us[2 * j], us[1 + 2 * j]),
                norm_edge(us[idx], ws[i]),
            ]
    return {"us": us, "ws": ws, "switches": switches}
