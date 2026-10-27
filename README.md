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
| A2 | `EthCor.colorings_subexp` (also `colorings_uniform`) | One machine counts the proper k-colorings of an n-vertex graph within 2^{εn} steps, for every ε > 0 and θ > 0, n ≥ n₀(θ, ε) and all k with lg k ≤ (lg n)^{1/6−θ}. | direct corollary; the growing range of k is the new part |
| A1 | `EthCor.CnfTM.cnf_counts` | For every D and δ > 0, one machine counts the satisfying assignments of any CNF with ≤ D·n clauses of **any width** within C·2^{δn} steps. | known equivalence ([5] + ¬ETH); formalized |
| A1′ | `EthCor.GrowTM.cnf_grow` | One machine counts the satisfying assignments of any CNF on n ≥ n₀(δ) variables with **m ≤ n·2^{(lg n)^{1/4}/(lg lg n)²} clauses** of any width within 2^{δn} steps, for every δ > 0. This density exceeds n·2^{(lg n)^{1/4−ε}} for every ε > 0. | ours |
| A4 | `EthCor.Spectrum.maxsat_spectrum` | For every width r, density D and δ > 0, one machine outputs, given t and a CNF with clauses of ≤ r literals and ≤ D·n clauses, the number of assignments satisfying **exactly t clauses**, within C·2^{δn} steps. | ours |
| A5a | `EthCor.HamTM.hc_parity_subexp` (also `hc_parity_tm`) | For every Δ, one machine decides whether a graph on n ≥ n₀(ε) vertices with all degrees ≤ Δ has an **odd number of Hamiltonian cycles**, within 2^{εn} steps, for every ε > 0. | ours |
| A5a′ | `EthCor.HamSTM.hc_parity_sparse` (also `hc_parity_bounded`, `hcS_tm`) | One machine decides whether a graph on n ≥ n₀(θ, ε) vertices with **at most n·(lg n)^{1/2−θ} edges**, of any degree, has an odd number of Hamiltonian cycles, within 2^{εn} steps, for every θ, ε > 0. As a consequence, a single machine handles every degree bound Δ (`hc_parity_bounded`). | ours |
| A5b | `EthCor.HamITM.ham_randomized` (also `hcI_tm`) | **Hamiltonian cycle, randomized, one-sided error.** One machine, run on `code G` followed by the code of a seed ω, halts within 2^{εn} steps with one bit. This holds for every D, δ > 0 and ε > 0, for k, t and n₀ depending on them, for every graph on n ≥ n₀ vertices with **at most D·n edges**, and for every seed ω. If G has no Hamiltonian cycle, the bit is 0 for every seed. If G has one, the bit is 1 for at least a 2^{−δn} fraction of the seeds. | ours |

**Supporting theorem (for A5b): isolation for arbitrary sets.** `EthCor.Iso.isolation`: for every
δ > 0 there are k and t such that for all M ≥ M₀(δ) and **every** nonempty S ⊆ {0,1}^M, at least a
2^{−δM} fraction of the seeds ω leaves exactly one point of S. A seed consists of 3M + 3 parity checks
on k coordinates each, a number m of them to use, and for every coordinate a value in {0,…,t−1} and a
bit; the coordinate is fixed to the bit when the value is 0. This is the isolation lemma of [7].
[7] states it for solution sets of k-CNFs, but its proof uses only that S is nonempty, and that is
what we formalize. Sparse checks matter here: a check on k coordinates is 2^{k−1} clauses of width k
on the same variables. So isolating among the solutions of a CNF keeps the number of variables, which
Valiant–Vazirani hashing does not.

`cnf_counts` and `cnf_grow` assume that no clause repeats a literal. In A2, k ≥ 2. The number of
Hamiltonian cycles is `numHamCycles G`, the number of connected spanning subgraphs H ≤ G with every
degree 2. The "ours" entries are our derivations; we have not finished a literature check.

In A5b, the seeds are the elements of the finite type `Seed m k t (3m + 3)`, m being the number of
edges, and the fraction is taken over all of them, so it is the probability for a uniformly random
seed. A seed has O(m·k·log m) bits. Its code `seedCode ω` is W = m + k + (3m + 3) + 1 in unary,
followed by the numbers of ω, each written as a block 1^v 0^{W−v} of W bits. Repeating the run with
2^{2δn} independent seeds gives error at most e^{−2^{δn}}. This amplification step is standard and is
not part of the Lean statement.

### Proof ideas

- **A2, colorings.** Write each color in b = ⌈log₂ k⌉ bits. This gives a CNF on n·b + 4 variables
  of width 2b with exactly one satisfying assignment per proper coloring (`cntN_colB`). The uniform
  bound C·k²·N·r(N) with k = 2b, N = n·b and r(N) = lglg N/√lg N is O(n·(lg n)^{−2θ}) = o(n) when
  b ≤ 2(lg n)^{1/6−θ}, because b³ ≤ 8(lg n)^{1/2−3θ} and lglg N ≤ (lg N)^θ/(θ ln 2). The method
  stops at b³ ≈ √lg n/lglg n.
- **A1, any width, constant density.** Literal (u, b) becomes variable 2u or 2u+1, plus pair
  clauses, so every clause is positive. Then Anthropic's shortening tree from their Dominating Set
  corollary (`stepD`) cuts clauses to width w, with a new invariant for M = D·n clauses (theirs
  needs M ≤ n). Their `SIZED` counter runs at the leaves, combined by `walkSum` and `tm_of_stepped`.
- **A1′, growing density.** The same tree, with the width w read off the node. Let ℓ = ⌊lg 2n⌋ and
  L = ⌊lg ℓ⌋; then w = 2^{⌊L/4⌋−⌊lg L⌋} + 1 ≈ ℓ^{1/4}/L. The leaves are counted by Anthropic's
  uniform compact-code machine, simulated as a stepped machine. Since
  w²·L² ≤ 16√ℓ, the exponent C·w²·N·lglg N/√lg N is at most 32C·N/L = o(n). The tree has
  2^{(2/w)·lg(e·w·(D+2))·n} leaves for D·n clauses. With lg D ≤ (lg n)^{1/4}/(lglg n)² ≤ 4w/(L−1)
  the coefficient is at most (8 + 6√w)/w + 8/(L−1), which goes to 0. The method itself stops at
  density n·2^{o((lg n)^{1/4}/√lglg n)}.
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
- **A5a′, any degree.** At a vertex of degree d, "at most two chosen edges" takes C(d, 3) clauses
  and "at least two" a clause of width d. A sequential counter replaces both. Each pair (edge, end)
  gets two bits, "one edge at this end chosen so far" and "two chosen so far". Clauses of width ≤ 3
  fix these bits from the edge bits (`auxOK_iff`) and forbid a third edge. The formula has
  N = 5m + n + 2 variables, width 3, and as many satisfying assignments as before (`cntN_hcS`).
  Anthropic's bound c·2^{9c·N·lglg N/√lg N} is then 2^{o(n)} whenever m = o(n·√lg n/lglg n).
  We prove the case m ≤ n·(lg n)^{1/2−θ}.
- **Isolation for arbitrary sets [7].** One check on k coordinates fails to separate two points at
  distance w with probability (1 + (1 − w/M)^k)/2 (`two_mul_card_rv`, by flipping one coefficient).
  Step I: call x ∈ S semi-isolated if no point of S at distance ≥ r passes the same first m checks.
  For the least m with 2|S|·q^m ≤ 1, half of the check arrays make a given x semi-isolated
  (`card_not_semi`, union bound). The semi-isolated points with the same check values lie in one
  Hamming ball (`card_fiber_le`). Step II: if the surviving points lie within distance < 2r of each
  other, fix the coordinates where the two furthest of them differ; then one point is left (`stepII`).
  The count `iso_count` is exact. `iso_real` takes r = ⌊M/a⌋ + 1 and k = a·b and bounds the ball by
  a^{r−1}·e^{M/a}. `isolation` then picks t, b and a, in this order, against δ.
- **A5b, Hamiltonian cycle with one-sided error.** Isolate among the Hamiltonian cycles, then count
  mod 2. Each check of a seed becomes a chain of k auxiliary variables
  a_l = a_{l−1} ⊕ (c_l ∧ x_{j_l}), written as clauses of width ≤ 3; each fixing becomes a unit
  clause (`HamI.sat_isoF_iff`). The edge bits determine the auxiliary variables. Added to the formula
  of A5a′, the checks give a formula on N = 5m + n + 2 + (3m+3)·k variables with
  #SAT ≡ #{Hamiltonian cycles that pass the checks} (mod 2) (`iso_parity`). If G has no Hamiltonian
  cycle, the parity is 0 for every seed. If G has one, the isolation lemma leaves exactly one
  Hamiltonian cycle for at least a 2^{−δm} fraction of the seeds, so the parity is 1 there
  (`iso_decide`). The machine reads k, the number of checks used, the checks and the fixings from
  the input (`decode_seedCode`), so one machine serves every δ. Its bound c·2^{9c·N·lglg N/√lg N}
  is 2^{o(n)} because N = O(n) for m ≤ D·n.

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
  the definitions they use by hand. Ours: `numHamCycles`, `spectrum`, `Seed`, the input codes
  (including `seedCode`). Anthropic's:
  the TM2 machine model and their statement files. Nobody has reviewed Anthropic's statements by
  hand yet.

## Status and next steps

- **A5b** is done (see the table). Open: a deterministic version, and graphs with more than O(n)
  edges. The formula has N ≈ 3m·k variables, so the bound stays 2^{o(n)} only while
  m·k = o(n·√lg n/lglg n).
- **A3, linear-kernel FPT problems in 2^{o(k)}·poly(n):** Vertex Cover, Nonblocker. The plan avoids
  a kernel: branch on vertices of degree > d, then run `SIZED` on the ≤ 2kd vertices left. Planned.
- **Parity of other connected structures:** next. The Cut & Count argument of A5a/A5a′ should
  carry over to Steiner trees and connected vertex covers of a given size.
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
    HamCounter, HamSparseTM               A5a′
    Isolation, IsoBound                   isolation lemma for arbitrary sets (A5b)
    HamIso                                checks as clauses, one-sided-error parity (A5b)
    HamIsoTM                              seed code, the machine, ham_randomized (A5b)
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
