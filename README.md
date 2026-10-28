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
| A2 | `EthCor.colorings_subexp` (also `colorings_uniform`) | One machine counts the proper k-colorings of an n-vertex graph within 2^{εn} steps, for every ε > 0 and θ > 0, n ≥ n₀(θ, ε) and all k with lg k ≤ (lg n)^{1/6−θ}. | direct corollary; the growing range of k is the new part |
| N5 | `EthCor.Hom.hom_subexp` (also `hom_uniform`, `hom_subexp_graph`; `Hom.numColorings_eq`, `Hom.numHom_simple`) | **Counting homomorphisms G → H with H in the input.** One machine is given h in unary, the h × h matrix of a relation H on {0,…,h−1} (loops allowed, not necessarily symmetric) and a graph G on n vertices. It outputs the number of maps f : V(G) → [h] that send every edge of G into H, within 2^{εn} steps, for every ε > 0 and θ > 0, n ≥ n₀(θ, ε) and all h with lg h ≤ (lg n)^{1/6−θ}. For a simple graph H this is the number of Mathlib homomorphisms `G →g H`; for H = K_h it is the number of proper h-colorings, so A2 is the special case. Another special case: the independent sets (H = an edge with a loop at one end). Under ETH, deciding G → H takes \|V(H)\|^{Ω(\|V(G)\|)} time in general [12]. | direct corollary; generalizes A2 |
| A1 | `EthCor.CnfTM.cnf_counts` | For every D and δ > 0, one machine counts the satisfying assignments of any CNF with ≤ D·n clauses of **any width** within C·2^{δn} steps. | known equivalence ([5] + ¬ETH); formalized |
| A1′ | `EthCor.GrowTM.cnf_grow` | One machine counts the satisfying assignments of any CNF on n ≥ n₀(δ) variables with **m ≤ n·2^{(lg n)^{1/4}/(lg lg n)²} clauses** of any width within 2^{δn} steps, for every δ > 0. This density exceeds n·2^{(lg n)^{1/4−ε}} for every ε > 0. | ours |
| A4 | `EthCor.Spectrum.maxsat_spectrum` | For every width r, density D and δ > 0, one machine outputs, given a CNF with m ≤ D·n clauses of ≤ r literals and t ≤ m, the number of assignments satisfying **exactly t clauses**, within C·2^{δn} steps. | ours |
| A5a | `EthCor.HamTM.hc_parity_subexp` (also `hc_parity_tm`) | For every Δ, one machine decides whether a graph on n ≥ n₀(ε) vertices with all degrees ≤ Δ has an **odd number of Hamiltonian cycles**, within 2^{εn} steps, for every ε > 0. | ours |
| A5a′ | `EthCor.HamSTM.hc_parity_sparse` (also `hc_parity_bounded`, `hcS_tm`) | One machine decides whether a graph on n ≥ n₀(θ, ε) vertices with **at most n·(lg n)^{1/2−θ} edges**, of any degree, has an odd number of Hamiltonian cycles, within 2^{εn} steps, for every θ, ε > 0. As a consequence, a single machine handles every degree bound Δ (`hc_parity_bounded`). | ours |
| N2 | `EthCor.ConnTM.conn_parity_tm` (also `cvc_parity_tm`) | **Parity of connected solutions.** For every width r, exponent D and δ > 0, one machine is given a graph G on n vertices of **any density**, 1 ≤ ℓ ≤ n, and a CNF φ on the vertices with clauses of ≤ r literals and ≤ (n+2)^D clauses. It outputs whether the number of vertex sets X with \|X\| = ℓ, X ⊨ φ and G[X] connected is odd, within C·2^{δn} steps. Special cases: with φ = unit clauses for a terminal set T, the sets X ⊇ T of size ℓ with G[X] connected, which are the vertex sets of the Steiner trees on ℓ vertices; and the connected vertex covers of size ℓ. The latter has its own machine on input `code G ++ unary ℓ` (`cvc_parity_tm`). | ours |
| N2′ | `EthCor.ConnITM.conn_randomized` | **Steiner tree and connected vertex cover, randomized, one-sided error.** For every width r, exponent D, δ > 0 and ε > 0 there are k, t, n₀ and one machine with the following property. Run on G, ℓ, the code of a seed ω and φ (`codeCI`), for any graph on n ≥ n₀ vertices of **any density** and φ as in N2, it halts within C·2^{εn} steps with one bit. If no vertex set of size ℓ satisfies φ and induces a connected subgraph, the bit is 0 for every seed. If one does, the bit is 1 for at least a 2^{−δn} fraction of the seeds. With φ = the terminals this decides whether a Steiner tree on ℓ vertices exists; with φ = the edges, whether a connected vertex cover of size ℓ exists. | ours |
| A5b | `EthCor.HamITM.ham_randomized` (also `hcI_tm`, `ham_randomized_mathlib`) | **Hamiltonian cycle, randomized, one-sided error.** One machine, run on `code G` followed by the code of a seed ω, halts within 2^{εn} steps with one bit. This holds for every D, δ > 0 and ε > 0, for k, t and n₀ depending on them, for every graph on n ≥ n₀ vertices with **at most D·n edges**, and for every seed ω. If G has no Hamiltonian cycle, the bit is 0 for every seed. If G has one, the bit is 1 for at least a 2^{−δn} fraction of the seeds. `ham_randomized_mathlib` states the same with Mathlib's `G.IsHamiltonian`. | ours |
| N3 | `EthCor.PottsTM.potts_spectrum` (also `tutte_tm`; identities `Potts.potts_fk`, `Potts.tutte_hyperbola`) | **Potts model and Tutte polynomial on sparse graphs.** For every number of colors q ≥ 1, density D and δ > 0, one machine is given a graph G on n vertices with ≤ D·n edges and j ≤ \|E(G)\| in unary. It outputs the number N_j of colorings σ : V → [q] with exactly j monochromatic edges (the density of states of the q-state Potts model), within C·2^{δn} steps. The N_j give the Potts partition function Σ_j N_j·y^j, its random-cluster form Σ_{A ⊆ E} q^{k(A)}·v^{\|A\|} with y = 1 + v [9], and the Tutte polynomial on the hyperbola (x−1)(y−1) = q: (x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j for x, y ≠ 1 (`tutte_tm`). Special cases are the chromatic polynomial at q, at (1−q, 0), and the flow polynomial at q, at (0, 1−q). | direct corollary; formalized |
| N6 | `EthCor.PermTM.perm_fpt` (also `Perm.cntS_permF`, `Perm.permanent_eq`) | **The 0/1 permanent in 2^{εm}·poly(n).** For every ε > 0, one machine is given n in unary and the n² entries of a 0/1 matrix A. It outputs Mathlib's `Matrix.permanent` of A (for a bipartite graph, its number of perfect matchings) within C·(n+2)^C·2^{εm} steps, m the number of ones of A. Under #ETH, no exp(o(m/log m)) algorithm exists for this problem [10]. | direct corollary; formalized |
| N6′ | `EthCor.SPermTM.sperm_fpt` (also `SPerm.cnt_sperm`, `SPerm.permanent_signed`) | **The permanent of a {−1, 0, 1} matrix in 2^{εm}·poly(n).** For every ε > 0, one machine is given a bit b, n in unary and two n × n 0/1 matrices A (the nonzero entries) and S (the entries −1). It outputs the number of permutations σ with A(σ i, i) for all i and an even (b = 0) or odd (b = 1) number of i with S(σ i, i), within C·(n+2)^C·2^{εm} steps, m the number of nonzero entries. The permanent of the matrix over ℤ (Mathlib's `Matrix.permanent`) is the first count minus the second (`permanent_signed`), so two runs give it. Under #ETH, no exp(o(m)) algorithm exists for this problem [10, Thm 1.3]. | direct corollary; formalized |
| A3 | `EthCor.VcTM.vc_fpt` (also `Vc.good_step`, `Vc.leaves_le`, `VcTM.tm_fpt`) | **Vertex Cover in 2^{εk}·poly(n).** For every ε > 0, one machine is given a graph G on n vertices (of **any density**) and k ≤ n in unary. It outputs whether G has a vertex cover with at most k vertices, within C·(n+2)^C·2^{εk} steps. No kernel is used. | known equivalence ([11] + ¬ETH); formalized |
| A3′ | `EthCor.NbTM.nb_fpt` (also `Nb.ore`, `Nb.nb_iff`, `Nb.nb_answer`) | **Nonblocker in 2^{εk}·poly(n).** For every ε > 0, one machine is given a graph G on n vertices (of any density) and k ≤ n in unary. It outputs whether G has a dominating set with at most n − k vertices (equivalently, k vertices whose complement dominates), within C·(n+2)^C·2^{εk} steps. | known equivalence (Ore [13], kernel [14] + ¬ETH); formalized |

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
degree 2. This agrees with Mathlib. For n ≠ 1, `0 < numHamCycles G` if and only if
`G.IsHamiltonian` (`EthCor.Ham.numHamCycles_pos_iff`). And `numHamCycles G` is the number of edge
sets of walks in G with Mathlib's `IsHamiltonianCycle` (`EthCor.Ham.numHamCycles_eq`), so each
Hamiltonian cycle counts once, whatever its start and direction. The "ours" entries are our derivations; we have not finished a literature check.

In A5b, the seeds are the elements of the finite type `Seed m k t (3m + 3)`, m being the number of
edges. In N2′ they are the elements of `Seed n k t (3n + 3)`, checks on the vertex bits. The fraction
is taken over all seeds, so it is the probability for a uniformly random seed. A seed has
O(M·k·log M) bits, for M = m or n. Its code `seedCode ω` is W = M + k + (3M + 3) + 1 in unary,
followed by the numbers of ω, each written as a block 1^v 0^{W−v} of W bits. In N2′ the input
carries the seed's length in unary in front of it (`seedL`). Repeating the run with
2^{2δn} independent seeds gives error at most e^{−2^{δn}}. This amplification step is standard and is
not part of the Lean statement.

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
  the Max-Cut spectrum and the density of states of the ±1 Ising model on O(n)-edge graphs.
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
  Anthropic's bound c·2^{9c·N·lglg N/√lg N} is then 2^{o(n)} whenever m = o(n·√lg n/lglg n).
  We prove the case m ≤ n·(lg n)^{1/2−θ}.
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
`hc_parity_tm`; `HamS.stepC`, `cntC`, `hcS`, `cntN_hcS`, `HamSTM.hcS_tm`, `hc_parity_sparse`.
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
  c := SIZED_{max(r,4)}(3n, n + ℓ, F)                   # = Σ_X 2^{#components of G[X]}
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
python3 -m pytest -q                  # 51 tests: every algorithm against brute force on small inputs
python3 -c "from ethcor.permanent import permanent_signed as p; \
  print(p([[True, True], [True, True]], [[False, True], [True, False]]))"   # [[1,-1],[-1,1]]: 2
```

The tests compare each algorithm with a direct enumeration of the quantity in the Lean statement
(colorings, homomorphisms, assignments, covers, dominating sets, permutations, Hamiltonian cycles,
connected vertex sets). They also check the shape bounds the Lean proofs use (width, number of
variables and clauses), and the one-sided error of A5b and N2′ over random seeds.

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
  Tutte polynomial to compare with), `Seed`, the input codes
  (including `seedCode`). Anthropic's:
  the TM2 machine model and their statement files. Nobody has reviewed Anthropic's statements by
  hand yet.

## Status and next steps

- **A5b** is done (see the table). Open: a deterministic version, and graphs with more than O(n)
  edges. The formula has N ≈ 3m·k variables, so the bound stays 2^{o(n)} only while
  m·k = o(n·√lg n/lglg n).
- **A3** is done for Vertex Cover and Nonblocker (A3, A3′ in the table). Nonblocker needs no
  branching: Ore's bound leaves at most 2k relevant vertices.
- **N2 and N2′** are done (see the table). The same formula should handle other "connected X with
  a CNF property" problems, for example connected dominating set on bounded-degree graphs, where
  the domination clauses have width Δ + 1.
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
    ConnFormula, ConnTM                   parity of connected solutions (N2)
    ConnIso, ConnIsoTM                    Steiner tree / connected vertex cover, randomized (N2′)
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
  tests/             one test file per module, against brute force
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

## Citation

Until a paper appears, please cite this repository:

> *Machine-checked corollaries of a 2^{o(n)} algorithm for #k-SAT.*
> GitHub repository, https://github.com/ssenge/eth-corollaries, 2026.
