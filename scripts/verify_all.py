"""End-to-end Gate-2 verification script for Paper 29:
  1. Lean 4 kernel build + zero-sorry / zero-warning / zero-Classical.choice axiom audit (18/18 theorems)
  2. Pure-stdlib zero-float replay of all 16 SWITCH-GRAPH-CONN-CERT-1.0 certificates
  3. Full pytest suite (41-graph dichotomy census + 128-assignment WSAT check + 57 live adversarial attacks)
  4. SHA-256 manifest verification (or generation via --write-manifest)

Author: Lluis Eriksson
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.switch_certifier import verify_switch_graph_certificate_exact

EXPECTED_THEOREMS = [
    "ConnectivitySwitching.complete_multipartite_nonadj_equiv",
    "ConnectivitySwitching.obstruction_k2_plus_k1_not_multipartite",
    "ConnectivitySwitching.transition_path_alternating_length",
    "ConnectivitySwitching.switch_count_edge_bound",
    "ConnectivitySwitching.spanning_tree_edge_count_exact",
    "ConnectivitySwitching.edmonds_matroid_intersection_duality",
    "ConnectivitySwitching.edmonds_global_con_impossibility",
    "ConnectivitySwitching.shifted_weight_nonneg",
    "ConnectivitySwitching.shifted_weight_telescoping_list",
    "ConnectivitySwitching.shifted_weight_budget_equiv",
    "ConnectivitySwitching.wsat_series_and_semantics",
    "ConnectivitySwitching.wsat_parallel_or_semantics",
    "ConnectivitySwitching.wsat_formula_eval_sound",
    "ConnectivitySwitching.psi_wsat_tight_weight_5m",
    "ConnectivitySwitching.handshaking_endpoint_count_2m",
    "ConnectivitySwitching.gadget_21_forward_weight_4x",
    "ConnectivitySwitching.gadget_21_backward_min_avg_bound",
    "ConnectivitySwitching.gadget_21_backward_total_budget",
]

MANIFEST_FILES = [
    "README.md",
    "pyproject.toml",
    "lean/lakefile.lean",
    "lean/lean-toolchain",
    "lean/ConnectivitySwitching.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/switch_exact.py",
    "src/switch_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "results/exp1_certified_atlas.json",
    "results/exp2_wsat_truth_table_sweep.json",
    "results/exp3_4vertex_dichotomy_census.json",
    "results/exp4_psi_and_gadget_scaling.json",
    "paper/main.tex",
    "paper/references.bib",
    "paper/main.pdf",
    "paper/figures/fig1_dichotomy_and_wsat.png",
    "paper/figures/fig2_psi_and_gadget_scaling.png",
    "paper/figures/fig3_atlas_summary.png",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def check_lean() -> None:
    lean_dir = ROOT / "lean"
    p1 = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True, check=False)
    if p1.returncode != 0:
        raise RuntimeError(f"lake build failed:\n{p1.stdout}\n{p1.stderr}")
    if "warning:" in (p1.stdout + p1.stderr).lower():
        raise RuntimeError(f"Lean build emitted warnings:\n{p1.stdout}\n{p1.stderr}")

    p2 = subprocess.run(["lake", "env", "lean", "AuditAxioms.lean"], cwd=lean_dir, capture_output=True, text=True, check=False)
    if p2.returncode != 0:
        raise RuntimeError(f"AuditAxioms failed:\n{p2.stdout}\n{p2.stderr}")
    out = p2.stdout + p2.stderr
    for forbidden in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if forbidden in out:
            raise RuntimeError(f"Forbidden Lean axiom {forbidden!r} found:\n{out}")
    for thm in EXPECTED_THEOREMS:
        if f"'{thm}'" not in out:
            raise RuntimeError(f"Missing theorem {thm} in AuditAxioms output")
    print(f"[PASS] Lean 4 kernel: {len(EXPECTED_THEOREMS)}/18 theorems, 0 warnings, 0 sorry, 0 Classical.choice")


def check_certs() -> list[str]:
    cert_dir = ROOT / "results" / "certificates"
    cert_files = sorted(cert_dir.glob("*.cert.json"))
    if len(cert_files) != 16:
        raise RuntimeError(f"Expected 16 certificates, found {len(cert_files)}")
    rel_list = []
    for cf in cert_files:
        data = json.loads(cf.read_text(encoding="utf-8"))
        res = verify_switch_graph_certificate_exact(data)
        if not res.get("verified"):
            raise RuntimeError(f"Certificate failed verification: {cf.name}")
        rel_list.append(cf.relative_to(ROOT).as_posix())
    print("[PASS] Exact-Z certificates: 16/16 independently verified (0 floats)")
    return rel_list


def check_pytest() -> None:
    p = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, capture_output=True, text=True, check=False)
    if p.returncode != 0:
        raise RuntimeError(f"pytest failed:\n{p.stdout}\n{p.stderr}")
    print(f"[PASS] pytest: {p.stdout.strip()}")


def handle_manifest(cert_rels: list[str], write_manifest: bool) -> None:
    manifest_path = ROOT / "SHA256SUMS.json"
    all_files = sorted(set(MANIFEST_FILES + cert_rels))
    computed = {}
    for rel in all_files:
        p = ROOT / rel
        if not p.exists():
            raise RuntimeError(f"Manifest file missing: {rel}")
        computed[rel] = sha256_file(p)
    if write_manifest:
        manifest_path.write_text(json.dumps(computed, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[PASS] Wrote SHA256SUMS.json ({len(computed)} files)")
        return
    if not manifest_path.exists():
        raise RuntimeError("SHA256SUMS.json missing; run with --write-manifest first")
    expected = json.loads(manifest_path.read_text(encoding="utf-8"))
    if expected != computed:
        diff_keys = sorted(set(expected.keys()) ^ set(computed.keys()))
        bad_hashes = [k for k in computed if expected.get(k) != computed[k]]
        raise RuntimeError(f"SHA256SUMS mismatch! diff_keys={diff_keys}, bad_hashes={bad_hashes}")
    print(f"[PASS] SHA256SUMS.json: {len(computed)}/{len(computed)} files verified")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    args = ap.parse_args()
    check_lean()
    cert_rels = check_certs()
    check_pytest()
    handle_manifest(cert_rels, args.write_manifest)
    print("=== ALL PAPER 29 GATE-2 VERIFICATION CHECKS PASSED ===")


if __name__ == "__main__":
    main()
