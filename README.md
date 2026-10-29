# eth-corollaries

This repository contains machine-checked algorithmic consequences of the October 2026 claims that the Exponential Time
Hypothesis (ETH) is false. Every result below is a Lean 4 theorem about Turing machines, proved on
top of Anthropic's formalized 2^{o(n)} algorithm for #k-SAT, and depends only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

Every algorithm is written out step by step under [Algorithms](#algorithms), next to the Lean
definitions it consists of. [`python/`](python) has a reference implementation of each one, tested
against brute force (see [Running the algorithms](#running-the-algorithms)). A write-up of all
results, with statements and proof sketches, is in
[`paper/eth-corollaries.pdf`](paper/eth-corollaries.pdf) (source `paper/eth-corollaries.tex`).

Some of the results have since turned out to be known or superseded. In particular, Tulsyan [15]
counts Hamiltonian cycles exactly and deterministically, which subsumes A5a, A5a′ and A5b; see
[Related and concurrent work](#related-and-concurrent-work). The Novelty column of the table says
which results are still ours.

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
followed by its adjacency matrix; a relation H on {0,…,h−1} is `hmat H`, its h² entries row by row; a CNF is `SatFree.enc φ` = 1ⁿ0, then each clause as 1, (1, literal
in ⌊log₂ 2n⌋+1 bits)*, 0, then a final 0; unary t = 1ᵗ0.

| # | Lean theorem | Statement | Novelty |
|---|---|---|---|
| A2 | `EthCor.colorings_subexp` (also `colorings_uniform`) | One machine counts the proper k-colorings of an n-vertex graph within 2^{εn} steps, for every ε > 0 and θ > 0, n ≥ n₀(θ, ε) and all k with lg k ≤ (lg n)^{1/6−θ}. | fixed k is in [1, Cor. 1.3] and [2, Cor. 7]; the growing range of k is ours |
| N5 | `EthCor.Hom.hom_subexp` (also `hom_uniform`, `hom_subexp_graph`; `Hom.numColorings_eq`, `Hom.numHom_simple`) | **Counting homomorphisms G → H with H in the input.** One machine is given h in unary, the h × h matrix of a relation H on {0,…,h−1} (loops allowed, not necessarily symmetric) and a graph G on n vertices. It outputs the number of maps f : V(G) → [h] that send every edge of G into H, within 2^{εn} steps, for every ε > 0 and θ > 0, n ≥ n₀(θ, ε) and all h with lg h ≤ (lg n)^{1/6−θ}. For a simple graph H this is the number of Mathlib homomorphisms `G →g H`; for H = K_h it is the number of proper h-colorings, so A2 is the special case. Another special case: the independent sets (H = an edge with a loop at one end; `Special.numHom_hInd`, `Special.indep_subexp`, with Mathlib's `IsIndepSet`); these counts are already in [1, Cor. 1.3] and, for every size s, in [2, Cor. 7]. Under ETH, deciding G → H takes \|V(H)\|^{Ω(\|V(G)\|)} time in general [12]. | direct corollary; generalizes A2 |
| A1 | `EthCor.CnfTM.cnf_counts` | For every D and δ > 0, one machine counts the satisfying assignments of any CNF with ≤ D·n clauses of **any width** within C·2^{δn} steps. | known: [5] for decision; counting uses the same count-preserving branching, as in [2, Cor. 7]; formalized |
| A1′ | `EthCor.GrowTM.cnf_grow` | One machine counts the satisfying assignments of any CNF on n ≥ n₀(δ) variables with **m ≤ n·2^{(lg n)^{1/4}/(lg lg n)²} clauses** of any width within 2^{δn} steps, for every δ > 0. This density exceeds n·2^{(lg n)^{1/4−ε}} for every ε > 0. | ours |
| A4 | `EthCor.Spectrum.maxsat_spectrum` | For every width r, density D and δ > 0, one machine outputs, given a CNF with m ≤ D·n clauses of ≤ r literals and t ≤ m, the number of assignments satisfying **exactly t clauses**, within C·2^{δn} steps. | ours (the spectrum); for the maximum, the equivalence with ETH is known [16, Thm 8] |
| A5a | `EthCor.HamTM.hc_parity_subexp` (also `hc_parity_tm`) | For every Δ, one machine decides whether a graph on n ≥ n₀(ε) vertices with all degrees ≤ Δ has an **odd number of Hamiltonian cycles**, within 2^{εn} steps, for every ε > 0. | independent; superseded by the exact count of [15] |
| A5a′ | `EthCor.HamO.hc_parity_little_o` (also `HamSTM.hc_parity_sparse`, `hc_parity_bounded`, `hcS_tm`) | One machine decides whether a graph on n ≥ n₀(g, ε) vertices with **at most n·g(n) edges**, of any degree, has an odd number of Hamiltonian cycles, within 2^{εn} steps, for every ε > 0 and every g with g(n)·lglg n/√lg n → 0, i.e. for **m = o(n·√lg n/lglg n)** edges. Special cases: m ≤ n·(lg n)^{1/2−θ} (`hc_parity_sparse`) and every degree bound Δ (`hc_parity_bounded`). | independent; superseded by [15, Theorem 2], which counts exactly for m = o(n·√lg n) |
| N2 | `EthCor.ConnTM.conn_parity_tm` (also `cvc_parity_tm`) | **Parity of connected solutions.** For every width r, exponent D and δ > 0, one machine is given a graph G on n vertices of **any density**, 1 ≤ ℓ ≤ n, and a CNF φ on the vertices with clauses of ≤ r literals and ≤ (n+2)^D clauses. It outputs whether the number of vertex sets X with \|X\| = ℓ, X ⊨ φ and G[X] connected is odd, within C·2^{δn} steps. Special cases: with φ = unit clauses for a terminal set T, the sets X ⊇ T of size ℓ with G[X] connected, which are the vertex sets of the Steiner trees on ℓ vertices; and the connected vertex covers of size ℓ. The latter has its own machine on input `code G ++ unary ℓ` (`cvc_parity_tm`). | ours |
| N2′ | `EthCor.ConnITM.conn_randomized` | **Steiner tree and connected vertex cover, randomized, one-sided error.** For every width r, exponent D, δ > 0 and ε > 0 there are k, t, n₀ and one machine with the following property. Run on G, ℓ, the code of a seed ω and φ (`codeCI`), for any graph on n ≥ n₀ vertices of **any density** and φ as in N2, it halts within C·2^{εn} steps with one bit. If no vertex set of size ℓ satisfies φ and induces a connected subgraph, the bit is 0 for every seed. If one does, the bit is 1 for at least a 2^{−δn} fraction of the seeds. With φ = the terminals this decides whether a Steiner tree on ℓ vertices exists; with φ = the edges, whether a connected vertex cover of size ℓ exists. | ours |
| N7 | `EthCor.CdsTM.cds_parity_tm` (also `CdsTree.shortensN`) | **Parity of connected dominating sets.** For every δ > 0, one machine is given a graph G on n vertices of **any density** and 1 ≤ ℓ ≤ n in unary. It outputs whether G has an odd number of connected dominating sets with ℓ vertices (every vertex is in X or has a neighbour in X, and G[X] is connected), within C·2^{δn} steps. Unlike in N2, the clauses of domination have unbounded width; Anthropic's shortening tree for dominating sets cuts them inside the Cut & Count formula. | ours |
| N7′ | `EthCor.CdsITM.cds_randomized` (also `cds_amplified`) | **Connected dominating set, randomized, one-sided error.** For every δ > 0 and ε > 0 there are k, t, n₀ and one machine with the following property. Run on G, ℓ and the code of a seed ω (`codeCD`), for any graph on n ≥ n₀ vertices of **any density**, it halts within C·2^{εn} steps with one bit. If G has no connected dominating set of size ℓ, the bit is 0 for every seed. If it has one, the bit is 1 for at least a 2^{−δn} fraction of the seeds. | ours |
| N7″ | `EthCor.MaxLeafTM.maxleaf_randomized` (also `mincds_randomized`; `Leaf.leaf_iff`, `Leaf.cds_le_iff`) | **Max Leaf Spanning Tree and minimum connected dominating set, randomized, one-sided error.** The machine of N7′, run on `codeCD G (n − L) ω` for n ≥ n₀ and 1 ≤ L < n, outputs 0 for every seed if G has no spanning tree with at least L leaves, and 1 for at least a 2^{−δn} fraction of the seeds if it has one. Spanning trees are subgraphs T ≤ G with Mathlib's `IsTree`. Run on `codeCD G ℓ ω` for 1 ≤ ℓ ≤ n, it decides in the same sense whether G has a connected dominating set with **at most** ℓ vertices. Both for graphs of **any density**, within C·2^{εn} steps. | ours |
| N8 | `EthCor.PosTM.pos_parity_tm` (also `CdsTree.shortensP`) | **Parity of connected solutions of a positive CNF of any width.** For every D and δ > 0, one machine is given a graph G on n vertices of **any density**, 1 ≤ ℓ ≤ n in unary, and a CNF φ on the vertices with only positive literals, at most n literals per clause and **at most D·n clauses of any width**. It outputs whether the number of vertex sets X with \|X\| = ℓ that meet every clause of φ and induce a connected subgraph is odd, within C·2^{δn} steps. N2 allows negative literals but needs clauses of bounded width; N7 is the special case where φ is the closed neighbourhoods. | ours |
| N8′ | `EthCor.PosTM.pos_randomized` | **Group Steiner tree, connected hitting set and connected total domination, randomized, one-sided error.** The same as N2′, for φ as in N8 (input `codeCI`): the bit is 0 for every seed if no X as in N8 exists, and 1 for at least a 2^{−δn} fraction of the seeds if one does, within C·2^{εn} steps, for graphs of **any density**. Special cases: with φ = the groups, the sets X are the vertex sets of the group Steiner trees with ℓ vertices (at most D·n groups of any size); with φ = a system of at most D·n sets of vertices, the connected hitting sets of size ℓ; with φ = the open neighbourhoods, the connected total dominating sets of size ℓ. | ours |
| N8″ | `EthCor.MinTM.min_conn_randomized`, `min_pos_randomized` (also `conn_grow`, `min_iff`) | **Minimum Steiner tree, minimum connected vertex cover and minimum Group Steiner tree, randomized, one-sided error.** For a connected graph G of **any density** and a positive φ, the machines of N2′ (clauses of at most r literals, at most (n+2)^D clauses) and N8′ (any width, at most D·n clauses), run with ℓ, decide in the same sense whether some X with **at most** ℓ vertices meets every clause of φ and induces a connected subgraph. With φ = the terminals, the edges or the groups, this is minimum Steiner tree (size counted in vertices), minimum connected vertex cover and minimum Group Steiner tree. | ours |
| N9 | `EthCor.ForestTM.fvs_parity_tm` (also `Forest.sides_edges`, `Forest.fvs_parity`, `ForestTM.numFVS_eq`) | **Parity of feedback vertex sets on sparse graphs.** For every D and δ > 0, one machine is given a graph G on n vertices with **at most D·n edges** and n − k in unary (k ≤ n). It outputs whether G has an odd number of feedback vertex sets with k vertices (sets X with G − X a forest, Mathlib's `IsAcyclic`), within C·2^{δn} steps. | ours |
| N9′ | `EthCor.ForestITM.fvs_randomized` (also `for_randomized`, `Forest.fi_decide`, `ForestTM.fvs_iff`) | **Feedback vertex set on sparse graphs, randomized, one-sided error.** For every D, δ > 0 and ε > 0 there are k₀, t, n₀ and one machine with the following property. Run on G, n − k and the code of a seed ω (`codeFI`), for any graph on n ≥ n₀ vertices with **at most D·n edges** and k ≤ n, it halts within C·2^{εn} steps with one bit. If G has no feedback vertex set with **at most** k vertices, the bit is 0 for every seed. If it has one, the bit is 1 for at least a 2^{−δn} fraction of the seeds. | ours |
| A5b | `EthCor.HamITM.ham_randomized` (also `hcI_tm`, `ham_randomized_mathlib`) | **Hamiltonian cycle, randomized, one-sided error.** One machine, run on `code G` followed by the code of a seed ω, halts within 2^{εn} steps with one bit. This holds for every D, δ > 0 and ε > 0, for k, t and n₀ depending on them, for every graph on n ≥ n₀ vertices with **at most D·n edges**, and for every seed ω. If G has no Hamiltonian cycle, the bit is 0 for every seed. If G has one, the bit is 1 for at least a 2^{−δn} fraction of the seeds. `ham_randomized_mathlib` states the same with Mathlib's `G.IsHamiltonian`. | independent; superseded by the deterministic exact count of [15] |
| N3 | `EthCor.PottsTM.potts_spectrum` (also `tutte_tm`; identities `Potts.potts_fk`, `Potts.tutte_hyperbola`) | **Potts model and Tutte polynomial on sparse graphs.** For every number of colors q ≥ 1, density D and δ > 0, one machine is given a graph G on n vertices with ≤ D·n edges and j ≤ \|E(G)\| in unary. It outputs the number N_j of colorings σ : V → [q] with exactly j monochromatic edges (the density of states of the q-state Potts model), within C·2^{δn} steps. The N_j give the Potts partition function Σ_j N_j·y^j, its random-cluster form Σ_{A ⊆ E} q^{k(A)}·v^{\|A\|} with y = 1 + v [9], and the Tutte polynomial on the hyperbola (x−1)(y−1) = q: (x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j for x, y ≠ 1 (`tutte_tm`). Special cases (`EthCor.Special`): for q = 2 the Max-Cut spectrum (`maxcut_spectrum`) and the density of states of the ±1 Ising model (`ising_spectrum`); N₀ is the number of Mathlib colorings `G.Coloring (Fin q)` (`pottsSpec_zero`), which is (−q)^{k(E)}·(−1)^n·T(G; 1−q, 0) (`chromatic_tutte`); and T(G; 0, 1−q) (`flow_tutte`), which by Tutte's classical theorem is ± the flow polynomial at q. | direct corollary; formalized |
| N6 | `EthCor.PermTM.perm_fpt` (also `Perm.cntS_permF`, `Perm.permanent_eq`) | **The 0/1 permanent in 2^{εm}·poly(n).** For every ε > 0, one machine is given n in unary and the n² entries of a 0/1 matrix A. It outputs Mathlib's `Matrix.permanent` of A (for a bipartite graph, its number of perfect matchings) within C·(n+2)^C·2^{εm} steps, m the number of ones of A. Under #ETH, no exp(o(m/log m)) algorithm exists for this problem [10]. | known: perfect matchings in 2^{o(v+e)} [1, Cor. 1.3]; formalized |
| N6′ | `EthCor.SPermTM.sperm_fpt` (also `SPerm.cnt_sperm`, `SPerm.permanent_signed`) | **The permanent of a {−1, 0, 1} matrix in 2^{εm}·poly(n).** For every ε > 0, one machine is given a bit b, n in unary and two n × n 0/1 matrices A (the nonzero entries) and S (the entries −1). It outputs the number of permutations σ with A(σ i, i) for all i and an even (b = 0) or odd (b = 1) number of i with S(σ i, i), within C·(n+2)^C·2^{εm} steps, m the number of nonzero entries. The permanent of the matrix over ℤ (Mathlib's `Matrix.permanent`) is the first count minus the second (`permanent_signed`), so two runs give it. Under #ETH, no exp(o(m)) algorithm exists for this problem [10, Thm 1.3]. | direct corollary; formalized |
| A3 | `EthCor.VcTM.vc_fpt` (also `Vc.good_step`, `Vc.leaves_le`, `VcTM.tm_fpt`) | **Vertex Cover in 2^{εk}·poly(n).** For every ε > 0, one machine is given a graph G on n vertices (of **any density**) and k ≤ n in unary. It outputs whether G has a vertex cover with at most k vertices, within C·(n+2)^C·2^{εk} steps. No kernel is used. | known: Vertex Cover is complete for size-constrained SNP [4, Thm 5], and a 2k-vertex kernel gives 2^{o(k)}·poly(n); see also [11]; formalized |
| A3′ | `EthCor.NbTM.nb_fpt` (also `Nb.ore`, `Nb.nb_iff`, `Nb.nb_answer`) | **Nonblocker in 2^{εk}·poly(n).** For every ε > 0, one machine is given a graph G on n vertices (of any density) and k ≤ n in unary. It outputs whether G has a dominating set with at most n − k vertices (equivalently, k vertices whose complement dominates), within C·(n+2)^C·2^{εk} steps. | known: Nonblocker is in Linear Monadic NP [17], with Ore's bound [13] or the kernel [14]; formalized |

**Supporting theorem (for A5b): isolation for arbitrary sets.** `EthCor.Iso.isolation`: for every
δ > 0 there are k and t such that for all M ≥ M₀(δ) and **every** nonempty S ⊆ {0,1}^M, at least a
2^{−δM} fraction of the seeds ω leaves exactly one point of S. A seed consists of 3M + 3 parity checks
on k coordinates each, a number m of them to use, and for every coordinate a value in {0,…,t−1} and a
bit; the coordinate is fixed to the bit when the value is 0. This is the isolation lemma of [7].
[7] states it for solution sets of k-CNFs, but its proof uses only that S is nonempty; Calabro calls
the technique oblivious to the formula [18, §9.3]. That is what we formalize. Tulsyan [15] formalizes
the same lemma for arbitrary finite sets. Sparse checks matter here: a check on k coordinates is 2^{k−1} clauses of width k
on the same variables. So isolating among the solutions of a CNF keeps the number of variables, which
Valiant–Vazirani hashing does not.

`cnf_counts` and `cnf_grow` assume that no clause repeats a literal. In A2, k ≥ 2. The number of
Hamiltonian cycles is `numHamCycles G`, the number of connected spanning subgraphs H ≤ G with every
degree 2. This agrees with Mathlib. For n ≠ 1, `0 < numHamCycles G` if and only if
`G.IsHamiltonian` (`EthCor.Ham.numHamCycles_pos_iff`). And `numHamCycles G` is the number of edge
sets of walks in G with Mathlib's `IsHamiltonianCycle` (`EthCor.Ham.numHamCycles_eq`), so each
Hamiltonian cycle counts once, whatever its start and direction. The "ours" entries are results we did not find in the literature search of 28 October 2026 (see [Related and concurrent work](#related-and-concurrent-work)). That means we did not find them, not that they are certainly new.

In A5b, the seeds are the elements of the finite type `Seed m k t (3m + 3)`, m being the number of
edges. In N2′, N7′, N8′ and N9′ they are the elements of `Seed n k t (3n + 3)`, checks on the vertex bits. The fraction
is taken over all seeds, so it is the probability for a uniformly random seed. A seed has
O(M·k·log M) bits, for M = m or n. Its code `seedCode ω` is W = M + k + (3M + 3) + 1 in unary,
followed by the numbers of ω, each written as a block 1^v 0^{W−v} of W bits. In N2′ and N7′ the
input carries the seed's length in unary in front of it (`seedL`); so does the input of N9′. Running the machine on R independent
seeds and answering yes if some run outputs 1 never errs on no-instances. On yes-instances it errs on
at most a fraction e^{−R·2^{−δn}} of the R-tuples of seeds, which is at most e^{−2^{δn}} for
R ≥ 2^{2δn} (`EthCor.Amplify.ham_amplified`, `conn_amplified`, `EthCor.CdsITM.cds_amplified`, from
the counting lemma `amplify`).

### Proof ideas

- **A2, colorings.** Write each color in b = ⌈log₂ k⌉ bits. This gives a CNF on n·b + 4 variables
  of width 2b with exactly one satisfying assignment per proper coloring (`cntN_colB`). The uniform
  bound C·k²·N·r(N) with k = 2b, N = n·b and r(N) = lglg N/√lg N is O(n·(lg n)^{−2θ}) = o(n) when
  b ≤ 2(lg n)^{1/6−θ}, because b³ ≤ 8(lg n)^{1/2−3θ} and lglg N ≤ (lg N)^θ/(θ ln 2). The method
  stops at b³ ≈ √lg n/lglg n.
- **N5, homomorphisms.** The same encoding with b = ⌈log₂ h⌉ bits per vertex. Instead of «the two
  ends of an edge have different colors», there is one clause of width 2b for every edge uv of G
  and every pair (a, c) with H(a, c) false: not both u ↦ a and v ↦ c (`homB`). The satisfying
  assignments are exactly the homomorphisms (`cntN_homB`). There are at most n²h² + O(nh) clauses,
  still polynomial in n for h ≤ n, so the time bound of A2 carries over unchanged.
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
  the Max-Cut spectrum and the density of states of the ±1 Ising model on O(n)-edge graphs; for
  these two the formal statements go through N3 with q = 2 (`Special.maxcut_spectrum`,
  `Special.ising_spectrum`).
- **N3, Potts and Tutte.** The variables are x_{vq+c} (vertex v has color c) and y_i (edge i is
  monochromatic), nq + m in all. The clauses say: at least one color per vertex (width q), at most
  one (width 2), and for every edge (a, b) and color c, x_{aq+c} ∧ x_{bq+c} → y_i and
  y_i ∧ x_{aq+c} → x_{bq+c} (width 3). The satisfying assignments are the colorings, with
  n + (number of monochromatic edges) true variables (`cnt_pottsF`), so `SIZED` counts N_j. For the
  identities, expand Π_e (1 + v·[e monochromatic]) over the subsets A ⊆ E. The colorings constant on
  the components of (V, A) are q^{k(A)} many (`card_const`), which gives the Fortuin–Kasteleyn
  identity (`potts_fk`). With v = y − 1 and q = (x−1)(y−1), the term q^{k(A)}·(y−1)^{|A|} is
  (x−1)^{k(E)}·(y−1)^n times the term of A in the Tutte polynomial (`tutte_hyperbola`). Under #ETH,
  [10] proves lower bounds of the form 2^{Ω(n/polylog n)} for these evaluations on sparse simple
  graphs; here they take 2^{δn} for every δ > 0.
- **N6, the permanent.** One variable per one of A. A clause of width 2 for every two ones in the
  same row or column says that they are not both chosen (`permF`). An assignment with exactly n
  true variables chooses n ones, no two in a column, so one in every column; their rows are
  distinct, so it is a permutation σ with A(σ i, i) for all i (`cntS_permF`, a bijection both
  ways). These σ are what Mathlib's `Matrix.permanent` of the 0/1 matrix adds up (`permanent_eq`).
  `SIZED` counts the solutions of size n in c·2^{εm}. The number of clauses, up to m², does not
  enter the exponent.
- **N6′, signs.** Add a parity chain over the r entries g₀, …, g_{r−1} that are −1: a variable z
  set to false, p_k = p_{k−1} ⊕ x_{g_k} (p_{−1} = z, four clauses of width 3), a complement
  q_k = ¬p_k for every chain bit, and the unit clause p_{r−1} = b. The chain bits are determined by
  the choice (`chain_det`), and each pair (p_k, q_k) has exactly one true bit, so the solutions with
  n + r true variables are the permutations whose number of −1 entries has parity b (`cnt_sperm`).
  The formula has m + 1 + 2r ≤ 3m + 1 variables and width 3, so `SIZED` at δ = ε/3 counts it in
  c·2^{εm}. Each permutation contributes (−1)^{#(−1 entries)} to the permanent
  (`permanent_signed`).
- **A3, Vertex Cover parameterized by k.** Branch instead of kernelizing. While the budget is
  positive and some vertex v has at least d distinct neighbours, either v is in the cover (budget
  − 1) or all of its neighbours N(v) are (budget − |N(v)| ≤ budget − d) (`stepV`, `good_step`).
  Every step lowers the budget by 1 or by at least d, so the tree has at most
  Σ_{j ≤ (k+d)/d} C(k+d, j) ≤ 2^{ε(k+d)} leaves once (1/d)·lg(e·d) ≤ ε (`leaves_le`, from
  Anthropic's tree bound). At a leaf every vertex has fewer than d neighbours, so a cover of size
  ≤ k′ leaves at most k′·d vertices on the edges (`card_V_le`). `SIZED` then decides the leaf on these
  vertices in 2^{δkd} steps (`cnt_leafV_pos`). With δ = ε/(4d) this is 2^{εk/4} per leaf. The host
  `tm_fpt` makes one Turing machine of the walk with time poly(n)·2^{εk}. Cai and Juedes [11] showed
  that a 2^{o(k)}·poly(n) algorithm for Vertex Cover refutes ETH; this is the converse direction,
  with the claimed refutation as input.
- **A3′, Nonblocker.** Isolated vertices are in every dominating set, so G has a dominating set of
  size ≤ n − k exactly if the graph induced on the n′ vertices with a neighbour has one of size
  ≤ n′ − k (`nb_iff`). That graph has no isolated vertex, so by Ore's theorem [13] it has a
  dominating set with at most n′/2 vertices: the complement of a minimum dominating set dominates
  (`compl_dominating`, `ore`). Hence the answer is yes if 2k ≤ n′ and no if n′ < k. Otherwise
  n′ < 2k, and the front end hands the induced graph and s = n′ − k to Anthropic's counter of
  dominating sets of size s (`DOMcount`), which takes c·2^{(ε/2)n′} ≤ c·2^{εk} steps. The host
  `tm_fpt` of A3 makes one Turing machine of it.
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
  Anthropic's bound c·2^{9c·N·lglg N/√lg N} is then 2^{o(n)} whenever m = o(n·√lg n/lglg n)
  (`hc_parity_little_o`). Since m ≤ n², N + 4 ≤ (n + 4)³, and then r(N) ≤ 3·r(n) for the rate
  r(n) = lglg(n+4)/√lg(n+4) (`rate_three`), so the exponent is at most 27c·(5n·g(n) + n + 2)·r(n),
  which is below εn/2 for large n since g(n)·r(n) → 0 and r(n) → 0 (`boundO_le`).
- **N2, connected solutions.** Cut & Count on vertex sets. The variables are a vertex bit x_v, a
  side bit s_v and its complement s̄_v. The clauses are those of φ, then s̄_v = ¬s_v, s_v = 0 outside
  X, and s_u = s_v on every edge inside X (width ≤ max(r, 4)). Each complementary pair has exactly
  one true bit, so the satisfying assignments with n + ℓ true variables are the pairs (X, s) with
  \|X\| = ℓ, X ⊨ φ and s constant on the edges of G[X] (`cnt_stepA`, `cnt_stepB`). There are 2^{cc(G[X])} of
  them, so half their number is odd exactly when G[X] is connected (`sig_parity`, the flip argument
  of A5a with a root in X). Anthropic's `SIZED` counter for "exactly s true variables" counts the
  3n-variable formula, and the machine keeps bit 1 of the count (`conn_parity`). The number of edges
  does not matter: it changes the number of clauses, not the number of variables.
- **N2′, the decision versions.** Add the isolation checks of A5b on the n vertex bits: a variable z
  set to false, the Tseitin chains of the checks, and a complement bit for every chain bit
  (`compF`). Each chain bit and its complement hold exactly one true bit, so the target becomes
  n + ℓ + (3n+3)·k. The chain bits are determined (`stepC`, `stepD`, `stepE`). Half the count then
  has the parity of the number of connected solutions that pass the checks (`ci_parity`, through
  `conn_parity_P` with the checks as the property P). The isolation lemma on the set of connected
  solutions, a subset of {0,1}^n, gives `ci_decide`. The formula has 3n + 1 + 2(3n+3)k = O(n)
  variables for fixed k, so `SIZED` runs in C·2^{εn}.
- **N7, N7′, connected dominating set.** Take the formula of N2 with φ the clauses of domination:
  for every vertex v, x_v or x_u for a neighbour u. These n clauses have unbounded width, so the
  formula cannot go to `SIZED` directly. Anthropic's tree for dominating sets [2, Cor. 7] cuts long
  positive clauses: in a clause with more than w variables, either one of its first w variables is
  true (the clause is replaced by these w) or all w are false (they are deleted from every open
  clause). Every assignment satisfies exactly one child, so the counts of the leaves add up
  (`cntS_step`). Here the domination clauses are open and the clauses of the side bits and the edges
  are closed and carried along (`CdsTree.rootN`). The invariant of [2] bounds the variables of the
  open clauses by the number of variables; ours bounds them by n while the formula has 3n variables
  (`InvC`). So a path still has at most n light and n/w heavy steps, the tree has at most
  Σ_{j ≤ 2n/w} C(2n, j) ≤ 2^{εn} leaves for a suitable w, and every leaf has width at most w + 4
  (`shortensN`). `SIZED_{w+4}` counts each leaf with n + ℓ true variables, and bit 1 of the sum is
  the parity of N2 (`cds_parity_tm`). N7′ puts the closed clauses of N2′ (z, the chains of ω and
  their complements) at the root instead (`CdsITM.rootR`); the tree and its bound are the same,
  and `ci_decide` with φ the domination clauses gives the one-sided error (`cds_randomized`).
- **N7″, Max Leaf Spanning Tree and minimum connected dominating set.** Two facts about graphs
  reduce both problems to N7′. They are proved in `EthCor.Leaf` with Mathlib's trees.
  - A connected dominating set X with |X| ≤ ℓ ≤ n grows to one with exactly ℓ vertices: add a
    vertex outside X that has a neighbour in X (`cds_grow`, `cds_le_iff`).
  - For n ≥ 3 and 1 ≤ L < n, G has a spanning tree with at least L leaves exactly if G has a
    connected dominating set with n − L vertices [19] (`leaf_iff`). In a spanning tree with n ≥ 3
    vertices, the non-leaves form a connected dominating set: the inner vertices of a path have
    degree at least 2 (`cds_of_tree`). Conversely, take a spanning tree of G[X] and join every
    vertex outside X to one of its neighbours in X. The result is a spanning tree in which every
    vertex outside X is a leaf (`tree_of_cds`).

  So the run of N7′ with ℓ = n − L decides Max Leaf, and the run with ℓ decides whether the
  connected domination number is at most ℓ. A disconnected graph has neither a spanning tree nor a
  connected dominating set, and N7′ already answers 0 on it.
- **N8, N8′, positive CNFs of any width.** The tree of N7 uses only that the open clauses are
  positive, have no repeated variables and live on the n vertex bits. `CdsTree.shortensP` allows D·n
  of them: its invariant `InvP` bounds the number of open clauses by D·n and the variables in them by
  n, separately, as `CnfTree.Inv2` does for A1. So a path has at most D·n light and n/w heavy steps,
  and the tree of depth (D+1)·n has at most Σ_{j ≤ 2n/w} C((D+2)·n, j) ≤ 2^{εn} leaves for a suitable w.
  The front end reads φ and keeps the variables of each clause without repeats (`PosTM.opens`); a
  positive clause has the same models as the clause of its variables (`cntS_opens`). The rest is N7
  and N7′ with φ in place of the clauses of domination.
- **N8″, minimum versions.** For a positive φ, adding a neighbour to a connected set that meets φ
  gives another one. In a connected graph some vertex outside X has a neighbour in X: a walk from X
  to a vertex outside crosses the boundary (Mathlib's `exists_boundary_dart`). So a solution with
  fewer than ℓ ≤ n vertices grows to one with exactly ℓ (`conn_grow`, `min_iff`), and the runs of N2′
  and N8′ with ℓ decide the minimum. G must be connected; otherwise run each component.
- **N9, N9′, feedback vertex set.** Count induced forests instead of connected sets. Add to the
  formula of N2 an edge bit b_e for every edge e = uv, with b_e → x_u ∧ x_v, and its complement.
  The formula has 3n + 2m variables. A vertex set X then has sig(X)·2^{e(X)} solutions, sig(X) the
  side maps of G[X] and e(X) its number of edges. The new identity is `Forest.sides_edges`: a graph
  H on W with S side maps (maps to {0,1} constant on edges) and e edges has S·2^e = 2^{|W|+j} with
  j = 0 exactly if H is acyclic. It is proved by induction on the edges. An edge between two
  components halves S (`card_sides_eq`, the flip of A5a on the component of one end), and an edge
  inside a component leaves S unchanged and closes a cycle (Mathlib's
  `isAcyclic_add_edge_iff_of_not_reachable`, `isAcyclic_sup_fromEdgeSet_iff`). So with target
  n + s + m, the count divided by 2^s is odd exactly when the number of induced forests of size s
  is odd (`fvs_parity`). The machine reads s again from the input to keep bit s of the count
  (`Stepped.bind`). For m ≤ D·n the formula has O(n) variables. Induced forests are closed under
  removing vertices, so a feedback vertex set with at most k vertices exists iff an induced forest
  with exactly n − k vertices does (`fvs_iff`). N9′ adds the checks of a seed as in N2′. Steps C–E
  are now proved for any formula on N₀ variables (`Forest.iso_count`), not only for `connF`.
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

## Related and concurrent work

This is a literature search of 28 October 2026. It covered papers, preprints, blogs and GitHub. It
could not reach X/Twitter or some journal full texts, and the review of the two claims has not
published anything yet.

- **Tulsyan [15]**, posted 27–28 October 2026, independently of this repository, also builds on
  Anthropic's Lean development. His `theorem1` counts the Hamiltonian cycles of graphs with
  |E| ≤ D·n exactly and deterministically in C·2^{δn} steps. His `theorem2` is one machine with
  C·2^{C(m+n)/√lg(n+2)} steps. His method uses Anthropic's network machinery with a matrix-tree
  identity, not the CNF counter. An exact count gives parity and a deterministic decision, so it
  subsumes A5a, A5a′ and A5b. Our A5a and A5b were pushed earlier (27 October, 12:20 and
  19:33 UTC), but his result is stronger. He also formalizes the isolation lemma for arbitrary sets,
  and sketches Steiner tree and feedback vertex set on sparse graphs. We rebuilt
  `theorem1` and `theorem2` from his repository (commit ae323a3) on our copy of Anthropic's
  development (same revision, 16a5ce4). Both compile and depend only on `propext`,
  `Classical.choice` and `Quot.sound`. His `hamCycles G` is the set of edge sets of G in which every
  vertex meets exactly two edges and which form a connected graph, the same quantity as our
  `numHamCycles G`. We have not reviewed his proofs beyond that.

  **Update, 29 October 2026.** We checked his repository again, at commit ba4c161 (29 October,
  07:13 UTC). Since our first check (commit ae323a3) he has added:
  - **Sparse TSP**, verified in Lean (`EthFollowup.ExactHC.theoremTSP`, `theoremTSP_decode`): the
    tours of every weight on graphs with |E| ≤ D·n and integer weights ≤ W, in 2^{δn}·poly(W).
  - **#HC for average degree d̄**: exact #HC in 2^{O(n·log d̄/√lg n)}, subexponential for
    d̄ = 2^{o(√lg n)}. This goes beyond the range of A5a′. At ba4c161 it was a written proof; at
    c01f010 (29 October, 11:06 UTC) it is verified in Lean (`theorem3`, `theorem3_maxdeg`).
  - **A sketch of Steiner tree, feedback vertex set, connected vertex cover, connected dominating
    set and k-leaf spanning trees**, deterministic, for graphs with |E| ≤ D·n and bounded degree. It
    is conditional on Anthropic's paper lemmas and checked numerically on graphs with up to seven
    vertices only. He labels it "conjectured, not claimed" and gives only decision and minimum for
    connected vertex cover and connected dominating set. Their exact counts he lists as open.
  - **Informal notes on barriers** for the dense permanent, the k-dependence of #k-SAT, and
    crossover estimates. He puts Anthropic's Lean algorithm's first gain over 2^n at about
    n ≈ 2^{552 000}.

  At commit 16fe4eb (29 October, 08:05 UTC) he has also added Lean proofs of decision, search and
  Hamiltonian paths at the level of Turing machines, a mathematical layer for directed
  Hamiltonian cycle and ATSP, and lemmas behind his barrier notes. At c01f010 (11:06 UTC) exact
  directed Hamiltonian cycle and ATSP are verified in Lean too. None of this is about domination,
  leaves, hitting sets or groups.

  None of this touches the labels below. N2, N2′, N7, N7′, N7″, N8, N8′ and N8″ hold on graphs of **any density**
  and are machine-checked. His sketch, if it were proved, would give deterministic decisions for
  Steiner tree, connected vertex cover, connected dominating set and k-leaf spanning trees on sparse
  graphs only.

  **Feedback vertex set (checked at commit 60d1679, 29 October, 15:30 UTC).** His research notes
  list the exact number of induced forests of each size, and so the exact minimum feedback vertex
  set and the number of minimum ones, for |E| = O(n), via a determinant identity. They mark it
  "numerically verified, unrefereed" and as a claim "if the core holds"; it is not in Lean. If it
  were proved it would be deterministic and exact, so stronger than N9 and N9′. N9 and N9′ are also
  for sparse graphs only, but they are machine-checked.
- **The two papers themselves** list corollaries. OpenAI [1, Cor. 1.3] counts independent sets and,
  for each fixed q, proper q-colorings in 2^{o(v)}, and perfect matchings in 2^{o(v+e)}; this
  covers N6. Anthropic [2, Cor. 7] counts independent sets, cliques, vertex covers and dominating
  sets of each size s, and proper k-colorings for fixed k, on graphs of any density. In their Lean
  code these are `stIndep`, `stCliques`, `stDominatingCounted` and `tm_of_colorings`.
- **Decision and optimization forms known before.**
  - A1: Calabro, Impagliazzo and Paturi [5]; see [18, Lemma 10.12].
  - The maximum in A4 (Max-r-SAT and Max-Cut with linearly many constraints):
    Jonsson, Lagerkvist, Schmidt and Uppman [16, Thm 8].
  - A3: Impagliazzo, Paturi and Zane [4, Thm 5], with a kernel.
  - A3′: Ganian, de Haan, Kanj and Szeider [17], with Ore's bound or the kernel.
- **Not found anywhere:** A1′, A2 for growing k, N5, the spectrum in A4, N3, N6′, N2, N2′, N7, N7′,
  N7″, N8, N8′, N8″, and N9, N9′ as proved results (Tulsyan sketches an exact count, see above). Tulsyan lists dominating set on dense graphs as not covered and sketches connected
  dominating set and k-leaf spanning trees only for sparse graphs [15]. Under ETH, connected dominating set has no 2^{o(n)} algorithm
  even on some geometric intersection graphs [20].
  Connectivity problems were open in this direction. Impagliazzo, Paturi and Zane list Hamiltonian
  Circuit only as SNP-hard [4], and Ganian et al. state as an open problem whether Feedback Vertex
  Set reduces to 3-CNF-SAT in this way [17]. N9′ does not answer that question. It reduces sparse
  Feedback Vertex Set to counting with a prescribed number of true variables, not to satisfiability,
  and it is randomized.

## Algorithms

Every algorithm here has the same three parts. A front end reads the input and writes a CNF; it
runs in polynomial time, which Lean proves (`PolyT`). One of Anthropic's counters counts the CNF.
A short post-step reads the answer off the count. No result needs a new exponential-time
algorithm: the work is in choosing a CNF whose number of variables (not clauses) is linear in the
parameter, and in proving that its count is the quantity we want.

The three counters, all from Anthropic's development [8]:

| Name below | Computes | Time | Lean |
|---|---|---|---|
| `COUNT(N, F)` | the number of satisfying assignments of F on N variables | 2^{C·w²·N·lglg N/√lg N} for width w, one machine for all w | `MainTheoremForms.MainTheoremCompact` (our `EthCor.compact`) |
| `SIZED_w(N, s, F)` | the number of satisfying assignments with exactly s true variables, F of width ≤ w | c·2^{δN} for every δ > 0, one machine per (w, δ) | `FromPrinted.Consequences.SIZED w`, theorem `SIZED_counts` |
| `DOMCOUNT(G, s)` | the number of dominating sets of size s of G | c·2^{δn} | `FromPrinted.Consequences.DOMcount`, theorem `stDominatingCounted` |

A literal (i, b) holds when x_i = b; |x| is the number of true variables. In Lean the front end and
the counter are joined by `Stepped.mapIn` and `Stepped.mapOut`. The walks over search trees (A1, A1′,
A3) are Anthropic's `walkSum` or our host `VcTM.tm_fpt`, which turn a stepped program into one
Turing machine. The Python names refer to the package in [`python/`](python), where every front end
is written clause for clause as in Lean.

### A2, N5: colorings and homomorphisms

```
HOM(G on n vertices, H a relation on {0..h−1}):        # A2 is H = K_k: H(a, c) ⇔ a ≠ c
  b := ⌈log₂ h⌉                                         # bits x_{vb}, …, x_{vb+b−1} spell the image of v
  F := for every vertex v and every code c with h ≤ c < 2^b:  "the bits of v do not spell c"
       for every edge {u, v}, in both orders, and every (a, c) with not H(a, c):
           "not (the bits of u spell a and the bits of v spell c)"          # width 2b
       x_i ∨ ¬x_i for every i < nb;   unit clauses x_{nb}, …, x_{nb+3}
  return COUNT(nb + 4, F)
```

Lean: `nb`, `forbid`, `colB`, `Hom.homB`; front ends `preC`, `Hom.preHom`; `cntN_colB`,
`Hom.cntN_homB`, `colorings_subexp`, `Hom.hom_subexp`. Python: `colorings.colB`, `homB`,
`num_colorings`, `num_hom`.

### A1: #SAT of any clause width, D·n clauses

```
CNF_ANY_WIDTH(φ on n variables, w):                     # w from δ and D (CnfTree.exists_width)
  root: 2n variables, x_{2u} = "u is true", x_{2u+1} = "u is false";
        closed: x_{2u} ∨ x_{2u+1} and ¬x_{2u} ∨ ¬x_{2u+1} for every u;
        open:   every clause of φ as a set of positive variables, (u, b) ↦ x_{2u + [b false]}
  total := 0
  depth-first over the tree:
    if some open clause C has more than w variables, with H its first w:
      light child: drop C from the open clauses, add the positive clause H to the closed ones
      heavy child: add ¬x_i for every i ∈ H, delete H from every open clause
    else (a leaf): total += SIZED_w(2n, n, open clauses ++ closed clauses)
  return total
```

Every leaf has width ≤ w. Exactly n true variables means one of x_{2u}, x_{2u+1} per u, so the
leaves count the assignments of φ, and each one exactly once. Lean: `CnfTree.lv`, `pairF`, `rootX`,
`cntS_rootX`, `shortens_of`; Anthropic's `stepD`, `leafD`, `walkSum`; machine `CnfTM.cnfM`,
`cnf_counts`. Python: `cnf_anywidth.rootX`, `stepD`, `leafD`, `walk_sum`, `count_any_width`.

### A1′: #SAT of any width, m ≤ n·2^{(lg n)^{1/4}/(lglg n)²} clauses

```
CNF_GROW(φ on n variables):
  as CNF_ANY_WIDTH, but at a node on N variables the width is
      w(N) := 2^{⌊L/4⌋ − ⌊lg L⌋} + 1,   L = ⌊lg ⌊lg N⌋⌋
  and every leaf F is counted with COUNT(2n, dedup F)
```

Lean: `GrowTree.wN`, `stepW`; `GrowTM.leafF`, `leafM`, `growM`, `cnf_grow`. Python:
`cnf_anywidth.wN`, `stepW`, `count_grow`.

### A4: the Max-SAT spectrum

```
MAXSAT_SPECTRUM(φ = C_0 … C_{m−1} on n variables, width r, t):
  variables x_0 … x_{2n−1} as in A1, y_j = x_{2n+j} for j < m
  F := x_{2u} ∨ x_{2u+1}, ¬x_{2u} ∨ ¬x_{2u+1} for every u
       y_j ↔ C_j for every j, with the literal (u, b) of C_j read as (x_{2u}, b)    # width r + 1
  return SIZED_{r+2}(2n + m, n + t, F)                 # = #assignments satisfying exactly t clauses
```

Lean: `Spectrum.xl`, `yC`, `specF`, `preS`, `specM`, `cntS_specF`, `maxsat_spectrum`. Python:
`spectrum.specF`, `maxsat_spectrum`.

### N3: Potts density of states and the Tutte polynomial on a hyperbola

```
POTTS(G on n vertices with edges e_0 … e_{m−1}, q, j):
  x_{vq+c} = "v has color c",  y_i = x_{nq+i} = "e_i is monochromatic"
  F := for every v: x_{vq} ∨ … ∨ x_{vq+q−1};  ¬x_{vq+c} ∨ ¬x_{vq+c′} for c′ < c
       for every edge e_i = (a, b) and color c:  x_{aq+c} ∧ x_{bq+c} → y_i,   y_i ∧ x_{aq+c} → x_{bq+c}
  return SIZED_{q+3}(nq + m, n + j, F)                 # N_j: colorings with exactly j monochromatic edges

TUTTE(G, x, y) with (x−1)(y−1) = q, x, y ≠ 1:          # post-step, exact arithmetic
  return Σ_j N_j·y^j / ((x−1)^{k(E)}·(y−1)^n)
```

Lean: `PottsTM.amo`, `vtxF`, `colF`, `edgeM`, `monoF`, `pottsF`, `preP`, `pottsM`, `cnt_pottsF`,
`potts_spectrum`, `tutte_tm`; `Potts.potts_fk`, `tutte_hyperbola`. Python: `potts.pottsF`,
`potts_spectrum`, `tutte_hyperbola`.

### N6, N6′: the permanent

```
PERMANENT_01(A, n × n 0/1):
  E := the ones of A, row by row, as e_0 … e_{m−1}       # one variable x_t per one
  if m < n: return 0
  F := ¬x_s ∨ ¬x_t for every s < t such that e_s and e_t share a row or a column    # width 2
  return SIZED_2(m, n, F)

PERMANENT_SIGNED(A, S):            # entry (i, j) is 0 if not A, −1 if A and S, 1 if A and not S
  E as above; g_0 … g_{r−1} := the indices t with S at e_t
  if m < n: return 0
  for b in {0, 1}:
    F_b := F of PERMANENT_01, then
           ¬z  with z = x_m
           p_k = p_{k−1} ⊕ x_{g_k} for k < r, p_k = x_{m+1+k}, p_{−1} = z     # 4 clauses of width 3
           q_k = ¬p_k for k < r, q_k = x_{m+1+r+k}
           p_{r−1} = b
    N_b := SIZED_3(m + 1 + 2r, n + r, F_b)            # permutations with (#(−1 entries) mod 2) = b
  return N_0 − N_1
```

Lean: `Perm.ents`, `clash`, `permF`, `cntS_permF`, `permanent_eq`, `PermTM.leafP`, `permM`,
`perm_fpt`; `SPerm.xorC`, `compC`, `chainF`, `sF`, `negs`, `numPar`, `cnt_sperm`,
`permanent_signed`, `SPermTM.leafS`, `spermM`, `sperm_fpt`. Python: `permanent.permF`,
`permanent01`, `chainF`, `sF`, `num_parity`, `permanent_signed`.

### A3: Vertex Cover in poly(n)·2^{εk}

```
VERTEX_COVER(G, k):                # a degree d, large enough for ε (CnfTree.exists_width)
  total := 0
  depth-first from the node (k, E(G)):
    node (k′, E′): if k′ > 0 and some end v of an edge of E′ has ≥ d distinct neighbours N(v):
        children: (k′ − 1, E′ minus the edges at v)
                  (k′ − |N(v)|, E′ minus the edges at N[v])        # a dead leaf if |N(v)| > k′
    leaf (k′, E′): V′ := the ends of the edges of E′
        if |V′| ≤ k′·d:
            total += SIZED_2(|V′|, min(k′, |V′|), {x_u ∨ x_v : uv ∈ E′})
  return total > 0
```

Lean: `Vc.nbs`, `cand`, `pick`, `delV`, `delN`, `stepV`, `verts`, `vcClauses`, `leafV`,
`good_step`, `leaves_le`, `cnt_leafV_pos`; `VcTM.rootV`, `vcM`, `tm_fpt`, `vc_fpt`. Python:
`vertex_cover.stepV`, `leafV`, `vc_word`, `has_vertex_cover`.

### A3′: Nonblocker in poly(n)·2^{εk}

```
NONBLOCKER(G, k):                  # is there a dominating set with ≤ n − k vertices?
  J := the vertices with a neighbour;  n′ := |J|
  if 2k ≤ n′: return yes                                # Ore: G[J] has a dominating set of ≤ n′/2
  if n′ < k:  return no
  return DOMCOUNT(G[J], n′ − k) > 0                     # n′ < 2k vertices, so 2^{δn′} ≤ 2^{2δk}
```

A dominating set of size exactly n′ − k suffices, because supersets of dominating sets dominate.
Lean: `Nb.niL`, `subM`, `ore`, `nb_iff`, `nb_answer`; `NbTM.preN`, `postN`, `nbM`, `nb_fpt`.
Python: `nonblocker.niL`, `subM`, `preN`, `has_nonblocker`.

### A5a, A5a′: the parity of the number of Hamiltonian cycles

```
HC_PARITY(G on n vertices, edges e_0 … e_{m−1}):
  x_i = "e_i is chosen" (i < m),  s_v = x_{m+v} = the side of v
  F := for every v: exactly two chosen edges at v
           A5a:  ¬x_a ∨ ¬x_b ∨ ¬x_c for distinct a, b, c at v; at least two (width deg v)
           A5a′: a sequential counter along the edges at v, 2 bits per (edge, end), width 3
       for every edge e_i = (a, b): x_i → (s_a = s_b)
       ¬s_0;   x_i ∨ ¬x_i for every variable
  return COUNT(N, F) mod 2                              # N = m + n (A5a), 5m + n + 2 (A5a′)
```

A 2-factor with c cycles has 2^{c−1} side maps, which is odd exactly for c = 1. Lean:
`Ham.inc`, `atMost2`, `atLeast2`, `edgeC`, `tautC`, `hcF`, `hc_parity`, `HamTM.formH`, `postH`,
`hc_parity_tm`; `HamS.stepC`, `cntC`, `hcS`, `cntN_hcS`, `HamSTM.hcS_tm`, `hc_parity_sparse`,
`HamO.hc_parity_little_o`.
Python: `hamcycle.hcF`, `hc_parity`, `hcS`, `hc_parity_sparse`.

### A5b: Hamiltonian cycle with one-sided error

```
HAM_RANDOMIZED(G, seed ω):         # ω: m₁ ≤ 3m + 3 parity checks on k edge bits each, fixings
  F := the formula of A5a′ on N = 5m + n + 2 variables, then for every check i < 3m + 3
       with terms (j_0, c_0) … (j_{k−1}, c_{k−1}):
           a_{i,l} = a_{i,l−1} ⊕ (c_l ∧ x_{j_l}),  a_{i,−1} = z, a variable fixed to false   # width ≤ 3
       a_{i,k−1} = (right-hand side of check i) for i < m₁
       x_j = bit_j for every fixed coordinate j            # unit clauses
  return COUNT(N + (3m + 3)·k, F) mod 2
```

If G has no Hamiltonian cycle the bit is 0. If it has one, at least a 2^{−δm} fraction of the seeds
leaves exactly one Hamiltonian cycle passing all checks (`Iso.isolation`), and then the bit is 1.
Lean: `HamI.xstep`, `rowF`, `isoF`, `hcI`, `iso_parity`, `iso_decide`; `HamITM.seedCode`,
`decode_seedCode`, `formI`, `hcI_tm`, `ham_randomized`. Python: `hamcycle.isoF`, `hcI`, `formI`,
`ham_randomized`; seeds in `isolation.Seed`, `random_seed`.

### N2, N2′: connected solutions (Steiner tree, connected vertex cover)

```
CONN_PARITY(G on n vertices, ℓ, φ a CNF on the vertex bits):
  x_v = "v ∈ X",  s_v = x_{n+v} (side),  s̄_v = x_{2n+v}
  F := φ;  s̄_v = ¬s_v;  x_v ∨ ¬s_v  (s_v = 0 outside X)
       for every edge uv: x_u ∧ x_v → (s_u = s_v)                         # width ≤ max(r, 4)
  c := SIZED_{r+4}(3n, n + ℓ, F)                        # = Σ_X 2^{#components of G[X]}
  return ⌊c/2⌋ mod 2                                    # parity of #{X : |X| = ℓ, X ⊨ φ, G[X] connected}

CONN_RANDOMIZED(G, ℓ, ω, φ):       # ω: checks on the n vertex bits, as in A5b
  F := F of CONN_PARITY, ¬z with z = x_{3n}, the chains of ω at x_{3n+1}, …,
       and a complement for every chain bit
  c := SIZED(3n + 1 + 2·(3n+3)·k, n + ℓ + (3n+3)·k, F)
  return ⌊c/2⌋ mod 2
```

For Steiner tree φ is the unit clauses x_t for the terminals t; for connected vertex cover it is
x_u ∨ x_v for every edge. Lean: `Conn.sideF`, `edgeCC`, `connF`, `conn_parity`; `ConnTM.vcF`,
`preC`, `preV`, `postC`, `conn_parity_tm`, `cvc_parity_tm`; `ConnI.compF`, `ciF`, `ci_parity`,
`ci_decide`; `ConnITM.codeCI`, `preR`, `conn_randomized`. Python: `connected.connF`,
`conn_parity`, `cvc_parity`, `steiner`, `ciF`, `conn_randomized`, `cvc_randomized`.

### N7, N7′: connected dominating set

```
CDS_PARITY(G on n vertices, ℓ):
  open   := for every v: [v] + neighbours(v)                  # domination, unbounded width
  closed := s̄_v = ¬s_v;  x_v ∨ ¬s_v;  for every edge uv: x_u ∧ x_v → (s_u = s_v)
  c := 0
  for every leaf (open', closed') of the tree of stepD_w from (open, closed):   # ≤ 2^{εn} leaves
    c += SIZED_{w+4}(3n, n + ℓ, open' as positive clauses + closed')
  return ⌊c/2⌋ mod 2                                 # parity of #connected dominating sets of size ℓ

CDS_RANDOMIZED(G, ℓ, ω):
  the same walk, with closed := the clauses of CONN_RANDOMIZED for φ = [], on
  3n + 1 + 2·(3n+3)·k variables with target n + ℓ + (3n+3)·k
```

w comes from `CdsTree.shortensN_exists` for ε = δ/4. Lean: `CdsTree.rootN`, `InvC`, `shortensN`;
`CdsTM.numCDS`, `rootC`, `cdsM`, `cds_parity_tm`; `CdsITM.codeCD`, `formD`, `rootR`, `cdrM`,
`cds_randomized`, `cds_amplified`. Python: `cds.rootC`, `rootR`, `cds_parity`, `cds_randomized`,
`num_cds`.

### N7″: Max Leaf Spanning Tree and minimum connected dominating set

```
MAX_LEAF(G on n ≥ 3 vertices, 1 ≤ L < n, ω):   # a spanning tree with ≥ L leaves?
  return CDS_RANDOMIZED(G, n − L, ω)
MIN_CDS(G, 1 ≤ ℓ ≤ n, ω):                      # a connected dominating set with ≤ ℓ vertices?
  return CDS_RANDOMIZED(G, ℓ, ω)
```

Lean: `Leaf.IsCDS`, `leaves`, `cds_of_tree`, `tree_of_cds`, `cds_grow`, `cds_le_iff`, `leaf_iff`;
`MaxLeafTM.numCDS_pos_iff`, `mincds_randomized`, `maxleaf_randomized`. Python:
`cds.maxleaf_randomized`, `mincds_randomized`; `tests/test_maxleaf.py` checks `leaf_iff` and
`cds_le_iff` against all spanning trees of small graphs.

### N8, N8′: positive CNF of any width

```
POS_PARITY(G, ℓ, φ):            # φ positive, ≤ D·n clauses of any width
  CDS_PARITY, with open := for every clause of φ: its variables without repeats
POS_RANDOMIZED(G, ℓ, ω, φ):
  CDS_RANDOMIZED, with the same open clauses
```

w comes from `CdsTree.shortensP_exists D` for ε = δ/4; the tree has depth (D+1)·n. Lean:
`CdsTree.InvP`, `shortensP`; `PosTM.opens`, `cntS_opens`, `rootP`, `posM`, `pos_parity_tm`, `rootQ`,
`posrM`, `pos_randomized`. Python: `cds.opens`, `rootP`, `rootQ`, `pos_parity`, `pos_randomized`;
`tests/test_pos.py` with random positive CNFs and open neighbourhoods. N8″ is the same run with ℓ on
a connected graph (`MinTM.min_conn_randomized`, `min_pos_randomized`); `test_min_iff` checks
`min_iff` by brute force.

### N9, N9′: feedback vertex set on sparse graphs

```
FVS_PARITY(G on n vertices with m ≤ D·n edges, s = n − k):
  F := CONN(G, φ = [])                               # x_v, s_v, s̄_v as in N2, 3n variables
  for every edge e = (u, v), the i-th:  b_i → x_u,  b_i → x_v,  b̄_i = ¬b_i   # b_i = 3n + i
  c := SIZED_4(3n + 2m, n + s + m, F)                # Σ over X with |X| = s of sig(X)·2^{e(X)}
  return ⌊c/2^s⌋ mod 2                 # parity of #induced forests of size s = #FVS of size k

FVS_RANDOMIZED(G, s = n − k, ω):
  N₀ := 3n + 2m
  F := the formula above, z = N₀ false, the chains of ω on the vertex bits at N₀ + 1 + …,
       their complements                             # N₀ + 1 + 2·(3n+3)·k₀ variables
  c := SIZED_4(N₀ + 1 + 2·(3n+3)·k₀, n + s + m + (3n+3)·k₀, F)
  return ⌊c/2^s⌋ mod 2      # 0 for every ω if no FVS with ≤ k vertices
```

Lean: `Forest.card_sides_eq`, `sides_edges`, `ebF`, `fvsF`, `stepF`, `stepG`, `fvs_count`,
`weight_eq`, `fvs_parity_P`, `fvs_parity`, `isoAdd`, `iso_count`, `fi_parity`, `fi_decide`;
`ForestTM.preF`, `postF`, `forM`, `for_parity_tm`, `numFVS_eq`, `fvs_iff`, `fvs_parity_tm`;
`ForestITM.codeFI`, `preQ`, `fiM`, `for_randomized`, `fvs_randomized`. Python: `forest.fvsF`,
`fvs_parity`, `fvs_randomized`, `num_fvs`; `tests/test_forest.py` checks `sides_edges` (and that j
is the cyclomatic number), both machines against brute force, and `fvs_iff`.

## Running the algorithms

[`python/`](python) is a reference implementation in plain Python (3.10 or later, no dependencies
besides pytest). It builds exactly the formulas above, from the same input words as the Lean
machines (`code G`, `unary`, `SatFree.enc`, `seedCode`). Anthropic's counters are replaced by an
exact DPLL counter with component caching that returns the weight enumerator of the solutions
(`ethcor.cnf.weight_counts`), so `SIZED_w(N, s, F)` is `count_sized(F, N, s)` and `COUNT(N, F)`
is `count(F, N)`. The Python code therefore runs in exponential time; it is meant for checking the
reductions, not for speed. The 2^{o(n)} counters exist only as Lean objects, and Anthropic reports
no gain over 2^n below n ≈ 10^{10}.

```sh
cd python
python3 -m pytest -q                  # 69 tests: every algorithm against brute force on small inputs,
                                      # and every front end against the Lean definitions
python3 -c "from ethcor.permanent import permanent_signed as p; \
  print(p([[True, True], [True, True]], [[False, True], [True, False]]))"   # [[1,-1],[-1,1]]: 2
```

The tests compare each algorithm with a direct enumeration of the quantity in the Lean statement
(colorings, homomorphisms, assignments, covers, dominating sets, permutations, Hamiltonian cycles,
connected vertex sets, connected dominating sets, spanning trees, induced forests). They also check the shape bounds
the Lean proofs use (width, number of variables and clauses), and the one-sided error of A5b, N2′,
N7′, N7″, N8′ and N9′ over random seeds.

`tests/test_lean_agreement.py` checks that the Python front ends are the Lean ones. It sends 131
random input words to [`lean/Dump.lean`](lean/Dump.lean), which evaluates the Lean definitions
(`formOf`, `Hom.formHom`, `Spectrum.preS`, `PottsTM.preP`, `PermTM.leafP`, `SPermTM.leafS`,
`HamTM.formH`, `HamSTM.formS`, `HamITM.formI`, `ConnTM.preC`, `preV`, `ConnITM.preR`,
`ForestTM.preF`, `ForestITM.preQ`, `NbTM.preN`, and the leaves of the trees of A1, A1′, A3, N7, N7′,
N8 and N8′), and compares the formulas clause for clause. It
needs the built Lean development (`cd lean && lake build`, about 1 minute per run of the test) and is
skipped if `lake` is not on the PATH or `ETHCOR_SKIP_LEAN` is set.

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
  the definitions they use by hand. Ours: `numHom`, `hmat` (proved to match Mathlib's `G →g H` and
  `numColorings`), `numHamCycles` (proved equal to Mathlib's count, see
  above), `spectrum`, `pottsSpec`, `mono`, `comps`, `tutte` (the rank-generating form; Mathlib has no
  Tutte polynomial to compare with), `cutSize`, `isingSum`, `Seed`, the input codes
  (including `seedCode`). Anthropic's:
  the TM2 machine model and their statement files. Nobody has reviewed Anthropic's statements by
  hand yet.

## Status and next steps

- **A5a, A5a′, A5b** are done (see the table), and superseded by Tulsyan's exact count [15], which
  is now machine-checked up to average degree 2^{o(√lg n)} [15]. Open: Hamiltonian cycle on denser
  graphs.
- **N2′** is randomized. Open: deterministic Steiner tree and connected vertex cover on dense
  graphs, and the exact number of connected vertex sets of size ℓ on dense graphs (we have its
  parity, N2).
- **A3** is done for Vertex Cover and Nonblocker (A3, A3′ in the table). Nonblocker needs no
  branching: Ore's bound leaves at most 2k relevant vertices.
- **N9, N9′** are done for sparse graphs (see the table). Open: feedback vertex set on denser
  graphs (the edge bits make the formula grow with m), and a deterministic version.
- **N2, N2′, N7, N7′, N7″, N8, N8′ and N8″** are done (see the table). N7 and N8 combine the Cut & Count
  formula with Anthropic's shortening tree, so they handle positive clauses of unbounded width. Open:
  more than linearly many such clauses (for example Group Steiner tree with n·ω(1) groups), long
  clauses with negative literals, and deterministic versions.
- **N5** is done (see the table). The range of h is that of A2; it ends where b³ ≈ √lg n/lglg n.
  The number of clauses grows with h², not the number of variables, so dense targets cost nothing extra.
- **N6 and N6′** are done (see the table): 0/1 and {−1, 0, 1} entries. Open: the matching
  polynomial of general graphs (the same formula with clauses for edges sharing an endpoint, s = j)
  and permanents with larger integer weights, which need a counter modulo small primes or a
  binary expansion of the weights.
- **S3** is done: `numHamCycles` is checked against Mathlib's `IsHamiltonian` and
  `IsHamiltonianCycle` (see the notes under the table).
- **N3** is done (see the table). Here q is a constant: the formula has width q + 3, and `SIZED`
  takes a fixed width. Open: the Tutte polynomial off the hyperbolas (x−1)(y−1) ∈ ℕ.
- The full list of ten candidate problems is in [NOTES.md](NOTES.md), together with the research
  log and the deep dive on both papers. It includes harder Tier B items: dense Max-Cut, the
  permanent, CNF-SAT with poly(n) clauses, planar problems below 2^{O(√n)}, and Subset Sum.

## Layout

```
README.md            this file
paper/               the write-up (LaTeX source and PDF)
NOTES.md             deep dive on both papers, ten candidate problems, research log
lean/
  lakefile.toml      pins Anthropic's formal-math `eth` development
  CheckAxioms.lean   prints the axioms of the main theorems
  Dump.lean          evaluates the Lean front ends on input words (for the Python agreement test)
  EthCor.lean        imports everything
  EthCor/
    TimeArith.lean                        shared time-bound arithmetic
    ColorFormula, ColorTM, ColorSubexp    A2
    HomFormula, HomTM                     homomorphisms G → H, H in the input (N5)
    CnfTree, CnfTM                        A1
    GrowTree, GrowArith, GrowTM           A1′
    Spectrum                              A4
    HamFormula, HamTM                     A5a
    HamCounter, HamSparseTM               A5a′
    HamLittleO                            A5a′ for m = o(n·√lg n/lglg n) edges
    Isolation, IsoBound                   isolation lemma for arbitrary sets (A5b)
    HamIso                                checks as clauses, one-sided-error parity (A5b)
    HamIsoTM                              seed code, the machine, ham_randomized (A5b)
    HamMathlib                            numHamCycles vs Mathlib's IsHamiltonian (S3)
    Potts                                 Fortuin–Kasteleyn, Tutte polynomial on hyperbolas (N3)
    PottsTM                               the Potts formula and machine, potts_spectrum (N3)
    VcTree, VcTM                          Vertex Cover in poly(n)·2^{εk}, FPT host (A3)
    Nonblocker, NonblockerTM              Ore's theorem, Nonblocker in poly(n)·2^{εk} (A3′)
    Perm, PermTM                          the 0/1 permanent in poly(n)·2^{εm} (N6)
    SignedPerm, SignedPermTM              the {−1, 0, 1} permanent: parity chain, sperm_fpt (N6′)
    Special                               independent sets, Max-Cut, Ising, chromatic and flow points
    Amplify                               error e^{−R·2^{−δn}} for R independent seeds (A5b, N2′)
    ConnFormula, ConnTM                   parity of connected solutions (N2)
    ConnIso, ConnIsoTM                    Steiner tree / connected vertex cover, randomized (N2′)
    CdsTree                               the shortening tree under any closed clauses (N7, N8)
    CdsTM, CdsIsoTM                       connected dominating set: parity (N7), randomized (N7′)
    LeafTree                              spanning trees with many leaves vs connected dominating sets
    MaxLeafTM                             Max Leaf Spanning Tree, minimum connected dominating set (N7″)
    PosConnTM                             positive CNF of any width: parity (N8), randomized (N8′)
    MinConnTM                             minimum Steiner tree, connected vertex cover, Group Steiner tree (N8″)
    ForestFormula                         side maps × 2^{edges} = 2^{|V|+j}; induced forests by Cut & Count
    ForestTM, ForestIsoTM                 feedback vertex set on sparse graphs: parity (N9), randomized (N9′)
python/              reference implementations of all algorithms (see "Running the algorithms")
  pyproject.toml     pytest configuration
  ethcor/
    cnf.py           formulas as in Lean; exact counters standing in for COUNT and SIZED
    graphs.py, lists.py   input codes (code G, unary, hmat) and Lean's list functions
    colorings.py     A2, N5            cnf_anywidth.py   A1, A1′ (incl. SatFree.enc and its reader)
    spectrum.py      A4                potts.py          N3
    permanent.py     N6, N6′           vertex_cover.py   A3
    nonblocker.py    A3′               hamcycle.py       A5a, A5a′, A5b
    isolation.py     seeds, isolation  connected.py      N2, N2′
    cds.py           N7, N7′, N7″, N8, N8′   forest.py   N9, N9′
  tests/             one test file per module, against brute force; test_lean_agreement.py
                     against the Lean front ends (via lean/Dump.lean)
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
9. C. M. Fortuin and P. W. Kasteleyn. On the random-cluster model I. Introduction and relation to
   other models. Physica 57(4):536–564, 1972.
10. H. Dell, T. Husfeldt, D. Marx, N. Taslaman, and M. Wahlén. Exponential time complexity of the
    permanent and the Tutte polynomial. ACM Trans. Algorithms 10(4):21, 2014.
11. L. Cai and D. Juedes. On the existence of subexponential parameterized algorithms. J. Comput.
    System Sci. 67(4):789–807, 2003.
12. M. Cygan, F. V. Fomin, A. Golovnev, A. S. Kulikov, I. Mihajlin, J. Pachocki, and A. Socała.
    Tight lower bounds on graph embedding problems. J. ACM 64(3):18, 2017.
13. O. Ore. Theory of Graphs. AMS Colloquium Publications 38, 1962.
14. F. Dehne, M. Fellows, H. Fernau, E. Prieto, and F. Rosamond. Nonblocker: parameterized
    algorithmics for minimum dominating set. SOFSEM 2006, LNCS 3831, 237–245.
15. V. Tulsyan. Counting Hamiltonian cycles in sparse graphs in subexponential time, assuming the
    new #SAT algorithms. October 2026. https://github.com/xennygrimmato/eth-hamiltonicity (Lean:
    `EthFollowup.ExactHC.theorem1`, `theorem2`, `theoremTSP`; checked at commits ae323a3,
    ba4c161, 16fe4eb, c01f010 and 60d1679).
16. P. Jonsson, V. Lagerkvist, J. Schmidt, and H. Uppman. Relating the time complexity of
    optimization problems in light of the exponential-time hypothesis. MFCS 2014, LNCS 8635,
    408–419. arXiv:1406.3247.
17. R. Ganian, R. de Haan, I. Kanj, and S. Szeider. On existential MSO and its relation to ETH.
    MFCS 2016, LIPIcs 58:42.
18. C. Calabro. The Exponential Complexity of Satisfiability Problems. PhD thesis, UC San Diego,
    2009.
19. Y. Caro, D. B. West, and R. Yuster. Connected domination and spanning trees with many leaves.
    SIAM J. Discrete Math. 13(2):202–211, 2000.
20. M. de Berg and S. Kisfaludi-Bak. Lower bounds for dominating set in ball graphs and for
    weighted dominating set in unit-ball graphs. arXiv:2601.08425, 2026.

## Citation

Until a paper appears, please cite this repository:

> *Machine-checked corollaries of a 2^{o(n)} algorithm for #k-SAT.*
> GitHub repository, https://github.com/ssenge/eth-corollaries, 2026.
