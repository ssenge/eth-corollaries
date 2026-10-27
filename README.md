# eth-corollaries

This repository contains machine-checked algorithmic consequences of the October 2026 claims that the Exponential Time
Hypothesis (ETH) is false. Every result below is a Lean 4 theorem about Turing machines, proved on
top of Anthropic's formalized 2^{o(n)} algorithm for #k-SAT, and depends only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Background

**ETH** [3] says that 3-SAT on n variables cannot be solved in time 2^{o(n)}.
A large part of fine-grained complexity rests on it: tight lower bounds for coloring, Hamiltonian
cycle, Max-Cut, the 2^{O(√n)} barrier for planar problems, parameterized lower bounds, and more.

In October 2026 two groups independently claimed that ETH is false. Both papers are unrefereed; both
come with Lean formalizations.

| | OpenAI | Anthropic |
|---|---|---|
| Paper | "The Exponential Time Hypothesis is False" [1] (17 Oct, rev. 25 Oct 2026) | "A 2^{o(n)} Time Algorithm for 3-SAT" [2] (26 Oct 2026) |
| Claim | #k-SAT for every fixed k in (n+m)^{O_k(1)}·2^{O_k(n·loglog n/√log n)}, deterministic, polynomial space | #k-SAT with **one machine for all k** in 2^{C·min(k²·n·lglg n/√lg n, k·m/√lg m)}, C absolute |
| Lean | a weaker exponent, n(loglog n)²/√log n | both bounds, multi-stack Turing machines (Mathlib's TM2), standard axioms |
| Core tool | contraction of Boolean tensor networks: s wires in 2^{O(s/√log s)} | sum-product on the clause graph with recursive merge/cut steps |

A review is led by Impagliazzo, Paturi and Ryan Williams, who stress that taking part is not a
certification. If the claims hold, ETH, SETH, #ETH, Gap-ETH and NSETH all fall. Still standing: the
OV conjecture, the CNF-SAT hypothesis for poly(n) clauses of unbounded width, the k-Clique conjecture,
the Set Cover conjecture, and of course P ≠ NP. The algorithms are galactic; Anthropic reports no
gain over 2^n below n ≈ 10^{10}.

**Why corollaries are not automatic.** A refuted lower bound gives no algorithm by itself. To get a
2^{o(n)} algorithm for a problem X one needs a reduction from X to (#)SAT with o(n·√log n/loglog n)
variables, and, for the uniform bound, small clause width. Problems in size-constrained SNP reduce
this way [4]. Problems with global constraints (connectivity, orderings,
large numbers, dense pairwise interaction) do not reduce this way.

## Results

All theorems are in [`lean/EthCor/`](lean/EthCor). "One machine" means one
`M : TM2ComputableAux Bool Bool` with finite alphabets; time is the number of TM2 steps until M
halts with the stated output (`Wrap.Outputs`). Inputs are bit strings: a graph is `code G` = 1ⁿ0
followed by its adjacency matrix; a CNF is `SatFree.enc φ` = 1ⁿ0, then each clause as 1, (1, literal
in ⌊log₂ 2n⌋+1 bits)*, 0, then a final 0; unary t = 1ᵗ0.

| # | Lean theorem | Statement | Novelty |
|---|---|---|---|
| A2 | `EthCor.colorings_subexp` (also `colorings_uniform`) | One machine counts the proper k-colorings of an n-vertex graph within 2^{εn} steps, for every ε > 0, n ≥ n₀(ε) and all k with lg k ≤ (lg n)^{1/7}. | direct corollary; the growing range of k is the new part |
| A1 | `EthCor.CnfTM.cnf_counts` | For every D and δ > 0, one machine counts the satisfying assignments of any CNF with ≤ D·n clauses of **any width** within C·2^{δn} steps. | known equivalence ([5] + ¬ETH); formalized |
| A1′ | `EthCor.GrowTM.cnf_grow` | One machine counts the satisfying assignments of any CNF on n ≥ n₀(δ) variables with **m ≤ n·2^{(lg n)^{1/7}} clauses** of any width within 2^{δn} steps, for every δ > 0. | ours |
| A4 | `EthCor.Spectrum.maxsat_spectrum` | For every width r, density D and δ > 0, one machine outputs, given t and a CNF with clauses of ≤ r literals and ≤ D·n clauses, the number of assignments satisfying **exactly t clauses**, within C·2^{δn} steps. | ours |
| A5a | `EthCor.HamTM.hc_parity_subexp` (also `hc_parity_tm`) | For every Δ, one machine decides whether a graph on n ≥ n₀(ε) vertices with all degrees ≤ Δ has an **odd number of Hamiltonian cycles**, within 2^{εn} steps, for every ε > 0. | ours |

`cnf_counts` and `cnf_grow` assume that no clause repeats a literal. In A2, k ≥ 2. The number of
Hamiltonian cycles is `numHamCycles G`, the number of connected spanning subgraphs H ≤ G with every
degree 2. The "ours" entries are our derivations; we have not finished a literature check.

### Proof ideas

- **A2, colorings.** Write each color in b = ⌈log₂ k⌉ bits. This gives a CNF on n·b + 4 variables
  of width 2b with exactly one satisfying assignment per proper coloring (`cntN_colB`). The uniform
  bound C·k²·N·r(N) with k = 2b and N = n·b is o(n) as long as b ≤ 2(lg n)^{1/7}.
- **A1, any width, constant density.** Literal (u, b) becomes variable 2u or 2u+1, plus pair
  clauses, so every clause is positive. Then Anthropic's shortening tree from their Dominating Set
  corollary (`stepD`) cuts clauses to width w, with a new invariant for M = D·n clauses (theirs
  needs M ≤ n). Their `SIZED` counter runs at the leaves, combined by `walkSum` and `tm_of_stepped`.
- **A1′, growing density.** The same tree with width w ≈ lg(2n)^{1/6} read off the node. The leaves
  are counted by Anthropic's uniform compact-code machine, simulated as a stepped machine. The
  exponent C·w²·N·lglg N/√lg N is at most 328C·n·lg(2n)^{−11/84}. The number of leaves is
  2^{(2/w)·lg(e·w·(D+2))·n}, and the coefficient goes to 0.
- **A4, Max-SAT spectrum.** Use 2n + m variables: x_u, ¬x_u, and y_j ↔ (clause j holds). Assignments
  with exactly n + t true variables correspond to assignments with exactly t satisfied clauses
  (`cntS_specF`, explicit bijection). They are counted by Anthropic's `SIZED` counter. This covers
  the Max-Cut spectrum and the density of states of the ±1 Ising model on O(n)-edge graphs.
- **A5a, parity of Hamiltonian cycles (Cut & Count [6]).** The CNF has one bit per edge and one side
  bit per vertex. It says: every vertex is on exactly two chosen edges, the two ends of a chosen edge
  share a side, and s₀ is false. A chosen 2-factor with c cycles has 2^{c−1} side maps. That number
  is odd exactly when the 2-factor is connected (`parity_sides`: flip the sides on a component that
  avoids vertex 0). So #SAT ≡ #HC (mod 2) (`hc_parity`). The machine keeps the low bit of Anthropic's
  count. The formula has width Δ + 3 and N = m + n ≤ (Δ+1)n variables, so the bound is 2^{o(n)}.

## Checking the proofs

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.33.1) is pinned in
`lean/lean-toolchain`, and Anthropic's development [8] is pinned in `lean/lakefile.toml`
(rev 16a5ce4, subdirectory `eth`).

```sh
git clone https://github.com/ssenge/eth-corollaries
cd eth-corollaries/lean
lake exe cache get        # prebuilt Mathlib
lake build                # also builds Anthropic's development; the first run takes a while
lake env lean CheckAxioms.lean
```

`CheckAxioms.lean` prints the axioms of every main theorem. The expected output is
`[propext, Classical.choice, Quot.sound]` for each of them.

### What Lean checks and what it does not

- Lean checks that every proof is complete, with no `sorry`, and uses only the standard axioms.
- The 2^{o(n)} algorithm is itself a Lean theorem in the dependency. These results are therefore not
  conditional on an unproved hypothesis. They are as sound as Anthropic's formalization.
- Lean cannot tell whether a formal statement means what it should. Read the theorem statements and
  the definitions they use by hand. Ours: `numHamCycles`, `spectrum`, the input codes. Anthropic's:
  the TM2 machine model and their statement files. Nobody has reviewed Anthropic's statements by
  hand yet.

## Status and next steps

- **A5b, deciding Hamiltonian cycle:** blocked for now. Cut & Count needs isolation, and the cheap
  isolation methods all blow up the number of variables. The likely route is randomized, using the
  sparse-hash isolation lemma of [7].
- **A3, linear-kernel FPT problems in 2^{o(k)}·poly(n):** Vertex Cover, Nonblocker. The plan avoids
  a kernel: branch on vertices of degree > d, then run `SIZED` on the ≤ 2kd vertices left. Next up.
- The full list of ten candidate problems is in [NOTES.md](NOTES.md), together with the research
  log and the deep dive on both papers. It includes harder Tier B items: dense Max-Cut, the
  permanent, CNF-SAT with poly(n) clauses, planar problems below 2^{O(√n)}, and Subset Sum.

## Layout

```
README.md            this file
NOTES.md             deep dive on both papers, ten candidate problems, research log
lean/
  lakefile.toml      pins Anthropic's formal-math `eth` development
  CheckAxioms.lean   prints the axioms of the main theorems
  EthCor.lean        imports everything
  EthCor/
    TimeArith.lean                        shared time-bound arithmetic
    ColorFormula, ColorTM, ColorSubexp    A2
    CnfTree, CnfTM                        A1
    GrowTree, GrowArith, GrowTM           A1′
    Spectrum                              A4
    HamFormula, HamTM                     A5a
```

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop
and check proofs, to write the Lean formalisation, and to draft the text.

## References

1. OpenAI. The Exponential Time Hypothesis is False. Preprint, 17 October 2026, revised 25 October
   2026. https://github.com/openai/math, family 378.
2. Anthropic. A 2^{o(n)} Time Algorithm for 3-SAT. hexagon:2610.00577v1, 26 October 2026.
3. R. Impagliazzo and R. Paturi. On the complexity of k-SAT. J. Comput. System Sci. 62(2):367–375,
   2001.
4. R. Impagliazzo, R. Paturi, and F. Zane. Which problems have strongly exponential complexity?
   J. Comput. System Sci. 63(4):512–530, 2001.
5. C. Calabro, R. Impagliazzo, and R. Paturi. A duality between clause width and clause density for
   SAT. CCC 2006.
6. M. Cygan, J. Nederlof, M. Pilipczuk, M. Pilipczuk, J. M. M. van Rooij, and J. O. Wojtaszczyk.
   Solving connectivity problems parameterized by treewidth in single exponential time. FOCS 2011.
7. C. Calabro, R. Impagliazzo, V. Kabanets, and R. Paturi. The complexity of Unique k-SAT: an
   isolation lemma for k-CNFs. J. Comput. System Sci. 74(3):386–393, 2008.
8. Anthropic. formal-math: Lean formalizations, subdirectory `eth`.
   https://github.com/anthropics/formal-math.

## Citation

Until a paper appears, please cite this repository:

> *Machine-checked corollaries of a 2^{o(n)} algorithm for #k-SAT.*
> GitHub repository, https://github.com/ssenge/eth-corollaries, 2026.
