# LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks

This directory contains the Lean 4 proof results presented in the LEAP paper:
**"LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks"**
([pdf](LEAP.pdf)).

LEAP (**L**LM-in-**L**ean **E**nvironment **A**gentic **P**rover) is an agentic
framework that decomposes complex mathematical problems into smaller subgoals
(using an AND-OR DAG blueprint) and iteratively refines formal proofs using Lean
compiler feedback and LLM-based reviews.

## Structure of Proof Results

The formal proofs are organized in the `solutions/` directory:

*   **[Putnam 2025](solutions/Putnam-2025)**: Full formal solutions in Lean 4
    for all 12 problems from the 2025 William Lowell Putnam Mathematical
    Competition, where LEAP achieved a 100% solve rate.
    *   For the original math statements, please refer to
        [AxiomMath/putnam2025](https://github.com/AxiomMath/putnam2025).
*   **[Lean-IMO-Bench](solutions/LEAN-IMO-Bench)**: A benchmark of IMO-style
    problems formalized in Lean. The formal solutions are split into:
    *   **[Basic](solutions/LEAN-IMO-Bench/Basic)**: Pre-IMO to IMO-Medium
        difficulty.
    *   **[Advanced](solutions/LEAN-IMO-Bench/Advanced)**: Up to IMO-Hard
        difficulty.
    *   For the original IMO-Bench problem statements, please refer to
        [lean_proof_bench.csv][imo-csv-link].
*   **[Open Problems](solutions/Open-Problems)**: Formal proofs for complex
    combinatorial challenges and open problems:
    *   `knuth-color2_solution.lean`: A verified proof for a key subproblem
        (planar projection routing dynamics) in Knuth's Hamiltonian
        decomposition of even-order Cayley graphs.
    *   `erdos_457_solution.lean`: A verified proof for Erdős Problem 457
        concerning the density of triangle-free graphs.
    *   Statements:
        [original_statements](solutions/Open-Problems/original_statements)

## Citing this work

```
@misc{kung2026leapsuperchargingllmsformal,
  title         = {LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks},
  author        = {Po-Nien Kung and Linfeng Song and Dawsen Hwang and Jinsung Yoon and Chun-Liang Li and Simone Severini and Mirek Olšák and Edward Lockhart and Quoc V Le and Burak Gokturk and Thang Luong and Tomas Pfister and Nanyun Peng},
  year          = {2026},
  eprint        = {2606.03303},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  url           = {https://arxiv.org/abs/2606.03303}
}
```

## License and disclaimer

Copyright 2026 Google LLC

All software is licensed under the Apache License, Version 2.0 (Apache 2.0);
you may not use this file except in compliance with the Apache 2.0 license.
You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY licenses are
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.

[imo-csv-link]: https://github.com/google-deepmind/superhuman/blob/main/imobench/lean_proof_bench.csv
