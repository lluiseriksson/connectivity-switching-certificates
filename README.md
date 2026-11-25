# Machine-Checked Exact-Integer Dichotomy, Matroid-Intersection, and Parameterized WSAT Certificates for Connectivity Switching in Graphs

**Author:** Lluis Eriksson (with transparent AI assistance via Google Antigravity)  
**License:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript)

Zero-dependency Lean 4 formalization and pure-stdlib exact-$\mathbb{Z}$ certificate verifier (`SWITCH-GRAPH-CONN-CERT-1.0`) for the complexity dichotomy, matroid-intersection primal-dual structure, series-parallel WSAT reduction, and $\{1,1\}\to\{2,1\}$ $K_{1,\star}$ gadget bounds of Christoph Kern, Alexander Firbas, & Manuel Sorge (*Algorithms and Complexity of Connectivity Switching in Graphs*, `arXiv:2611.32927`, November 24, 2026).

## Verification Summary
- **Lean 4 Kernel (`lean/ConnectivitySwitching.lean`, Lean 4.35.0):** 18/18 constructive theorems, 0 warnings, 0 `sorry`, 0 `Classical.choice`, 5 zero-axiom theorems (`complete_multipartite_nonadj_equiv`, `obstruction_k2_plus_k1_not_multipartite`, `wsat_series_and_semantics`, `wsat_parallel_or_semantics`, `wsat_formula_eval_sound`) + 13 `[propext, Quot.sound]`, formalizing complete-multipartite $K_2+K_1$-freeness, alternating transition paths, Edmonds matroid-intersection weak duality & rank obstruction, Theorem 8 shifted-weight telescoping on `List`, Lemma 4 series-parallel formula semantics, PSI tight $5|E(H)|$ equality, and Theorem 6 backward $4\min_i c'_i \le \sum c'_i$ total budget preservation.
- **Exact-$\mathbb{Z}$ Certificate Atlas (`results/certificates/*.cert.json`):** 16 canonical certificates across 4 modes (Local-Con complete-multipartite paths & all three NP obstructions $K_2+K_2, P_4, L_{3,1}$; Global-Con weighted spanning trees & Edmonds rank obstructions $r_1(A)+r_2(B) \le n-2$; series-parallel WSAT equivalences & PSI $5|E(H)|$; $\{1,1\}\to\{2,1\}$ $K_{1,\star}$ gadgets including asymmetric backward consensus).
- **Cross-Checks & Red-Team Suite (`tests/test_suite.py`):** Exhaustive 41-graph 4-vertex dichotomy census (14 complete-multipartite P vs. 27 NP: 3 $K_2+K_2$, 12 $P_4$, 12 $L_{3,1}$), exhaustive $2^7=128$-assignment Lemma 4 equivalence check, 16/16 certificate replays, and **57/57** live adversarial attacks rejected.

## One-Command Reproducibility
```bash
python scripts/verify_all.py
```
To regenerate all certificates, experiment JSONs, and 300-DPI figures from scratch:
```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
