# ETH refutation: deep dive + candidate problems (2026-10-27)

## Sources (both unrefereed, both Lean-formalized)
- **OpenAI**, "The Exponential Time Hypothesis is False" (17 Oct, rev. 25 Oct 2026). github.com/openai/math, family 378:
  `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf`, Lean scope `lean/docs/378.md`.
- **Anthropic/Claude**, "A 2^{o(n)} Time Algorithm for 3-SAT", hexagon:2610.00577v1 (26 Oct 2026; pdf at hexagonmath.org/pdf/2610.00577v1).
- Review led by Impagliazzo, Paturi, Ryan Williams. They state explicitly that taking part is *not* certification.

## What is claimed
| | OpenAI | Anthropic |
|---|---|---|
| Problem | #k-SAT, every fixed k ≥ 2, deterministic, poly space | #k-SAT, one uniform machine for all k |
| Time (general) | (n+m)^{O_k(1)} · 2^{O_k(n loglog n/√log n)} | 2^{C·min{k² n loglog n/√log n, k m/√log m}}, C absolute |
| Time (m ≤ Dn) | 2^{O_{k,D}(n/√log n)} | 2^{O(k n/√log n)} |
| Lean proves | weaker exponent n(loglog n)²/√log n | both statements, TM2 model, std axioms only, nobody has reviewed it by hand yet |
| Core tool | Boolean tensor-network contraction (Thm D.1): **s wires → 2^{O(s/√log s)}**; entries in (Z/2^P)[V]/(V^ℓ), ℓ,P ≤ Cs; node degree ≤ s^{0.9} | sum-product on clause graph; recursive merge/cut; edge "cost" decompositions via the **eight-square (octonion) identity** |
| Also | sparse F2 polynomial systems (Thm 2.2, ≤ polylog monomials each); local-function (Goldreich OWF) inversion; #PM / #IS / #q-col in 2^{o(v)}; E^NP ⊄ SIZE(c·n√log n) | Corollary 7 (counting; any number of edges): IS, Clique, VC, **Dominating Set** of size s in O(2^{δn}) |

Refuted: ETH, SETH, #ETH, Gap-ETH, NSETH (plus their randomized versions).
**Not** refuted: OV conjecture, the CNF-SAT hypothesis with poly(n) clauses of unbounded width, the k-Clique conjecture, the Set Cover conjecture, P≠NP.
Galactic: Anthropic reports no gain over 2^n until n > 10^10 (the n-bound) or n > 10^{10000} (m = 5n).

## Rule for "now improvable"
A refuted lower bound gives **no** algorithm by itself. A speedup needs a reduction *to* SAT/tensor contraction with
o(n·√log n / loglog n) variables or wires. A reduction with mild superlinear blowup, e.g. n·(log n)^{0.49}, still yields 2^{o(n)}.
Every problem in size-constrained SNP is covered (IPZ01 SERF-completeness). Problems with global constraints
(connectivity, ordering, permutations, big numbers, dense pairwise interaction) are not.

## Ten candidates
Tier A: derivable now from the claimed theorems plus known tools. Tier B: lower bound gone, new ideas needed.
Items marked (*) are my own derivations and have not been checked.

A1 (*) **Growing width + mild density CNF-SAT.** Anthropic's uniform k² gives 2^{o(n)} for width k ≤ (log n)^{1/4−ε}.
   Combined with the CIP06 width-reduction branching (leaves ≤ 2^{(n/w)·log(e(cw+1))}, where c = m/n), this gives
   CNF-SAT with m ≤ n·2^{(log n)^{1/4−ε}} clauses of *any* width in 2^{o(n)}. The same goes for Hitting Set and Set Splitting with that many sets.
A2 (*) **Chromatic number, small-χ regime.** k-coloring with ⌈log k⌉ bits per vertex gives width 2⌈log k⌉ on n⌈log k⌉ variables,
   so 2^{o(n)} for k ≤ 2^{(log n)^{1/6−ε}} (decision and counting). The large-χ regime is still stuck at the BHK 2^n wall.
A3 **Linear-kernel FPT problems in 2^{o(k)}·poly(n).** Examples: Vertex Cover (2k-vertex kernel, then subexponential MIS) and Nonblocker (5k/3 kernel,
   then Dominating Set via Anthropic Cor. 7). This is folklore-equivalent to ¬ETH (Cai–Juedes) but nobody has written it down.
A4 (*) **Sparse partition functions / weighted #CSP** via OpenAI Thm D.1 with generating variable V (ℓ ≤ Cs).
   Gives the full Ising density of states, integer-q Potts, Tutte polynomial on the hyperbolas (x−1)(y−1) = q ∈ ℕ, the Max-Cut spectrum,
   and exact discrete graphical-model inference, all in 2^{O(n/√log n)} on O(n)-edge graphs. This voids and beats the #ETH bounds of Dell et al.
A5 (*) **Connectivity problems via Cut&Count + D.1 on sparse graphs.** Network: edge bits, one side bit per vertex, degree-2 checks.
   The count Σ_C 2^{cc(C)−1} is odd exactly when C is Hamiltonian, so **⊕HC is computable in 2^{o(n)} now**.
   Deciding HC, TSP, FVS or Steiner Tree also needs isolation weights of size ~n², and D.1 only allows ℓ ≤ Cs.
   Ways forward: lift D.1 to Galois rings, or use sparse Valiant–Vazirani hashing.
B6 **Dense quadratic problems**: Max-Cut / Max-2-CSP (Williams 2^{ωn/3}, unchanged since 2004) and dense MQ over F2 (Dinur 2^{0.694n}; relevant to UOV/MAYO).
   Obstacle: Θ(n²) pairwise wires. Thm 2.2 only handles polylog-sparse equations.
B7 **Permanent / #PM in dense bipartite graphs.** Ryser's 2^n has only seen lower-order improvements (Bjö16). The sparse case is OpenAI Cor 1.3.
   Obstacle: the natural encodings need v·log v bits, and at that size the √log savings are lost.
B8 **CNF-SAT with poly(n) clauses in 2^{(1−ε)n}**, the next domino after A1. It would void the LMS18 treewidth-tightness bounds
   (IS 2^tw, DS 3^tw) and unbounded Hitting Set / Set Splitting bounds. It would not touch OVC.
B9 **Planar / geometric below 2^{O(√n)}**: planar IS / 3-Col / HC and Euclidean TSP in R². All the square-root lower bounds are ETH-based.
   This needs a *treewidth-sensitive* contraction, 2^{O(tw/√log tw)}. For general graphs that is blocked by the CNF-SAT hypothesis (B8); for planar graphs it is not.
B10 **Subset Sum / Knapsack**: 2^{o(n)}, or T^{1−ε}·2^{o(n)} (the ABHS19 bound was SETH-based and is now void).
   Obstacle: huge coefficients. D.1's measurements need bounded-coefficient linear forms.

Not candidates (barrier still stands): edit distance, LCS, Fréchet, OV-based quadratic bounds (OVC); k-Clique in n^{o(k)} (k-Clique conjecture);
Set Cover in (2−ε)^n (Set Cover conjecture); practical SAT speedups.

## Lean results (built on anthropics/formal-math@16a5ce4 `eth`, project `lean/`, std axioms only)
Check with `cd lean && lake build && lake env lean CheckAxioms.lean`.
- **A2 done.** `EthCor.colorings_uniform` (EthCor/ColorTM.lean): one TM counts the proper k-colorings of G for all
  2 ≤ k ≤ n, input `unary k ++ code G`, within c·2^{c·(2b)²·(nb)·r(nb)} steps, b = ⌈log₂k⌉, r(N) = lglg(N+4)/√lg(N+4).
  `EthCor.colorings_subexp` (EthCor/ColorSubexp.lean): the same machine runs in 2^{εn} for every ε > 0 and 0 < θ < 1/6,
  n ≥ n₀(θ, ε), lg k ≤ (lg n)^{1/6−θ} (first version: 1/7). Numbers: b ≤ 2(lg n)^{1/6−θ}, so (2b)²·nb ≤ 32·n·(lg n)^{1/2−3θ},
  and r(N) ≤ lg(N+4)^{a−1/2}/(a·ln 2) for any a > 0 (`rate_le_rpow`, a = θ); the exponent is O(n·(lg n)^{−2θ}) (`boundNK_le`).
  Proof: binary color CNF (n·b+4 vars, width 2b) → Anthropic's compact-code machine, via `Wrap.everyMachineCanBeWrapped`.
- A1 correction: width k = o((log n)^{1/4}/√loglog n) is already in Anthropic's remark after Thm D(b). Only the
  arbitrary-width / m ≤ n·2^{(log n)^{1/4−ε}} part (CIP06 branching + many machine calls) is new.
- **A1, constant density, done.** `EthCor.CnfTM.cnf_counts` (EthCor/CnfTree.lean, CnfTM.lean): for every D and δ > 0, one TM
  counts the satisfying assignments of any CNF φ on n variables with ≤ D·n clauses (any width, no repeated literal in a clause),
  input `SatFree.enc φ`, within C·2^{δn} steps. Proof: literal (u,b) ↦ variable 2u / 2u+1 plus pair clauses, so every clause is
  positive; Anthropic's Dominating-Set shortening tree (`stepD`) with a new invariant for M = D·n clauses (theirs needs M ≤ n);
  their `SIZED` counter at the leaves; `walkSum`; `tm_of_stepped`. Mathematically this is CIP06 + ¬ETH (known equivalence);
  the growing-density version is below.
- **A1, growing density, done.** `EthCor.GrowTM.cnf_grow` (EthCor/GrowTree.lean, GrowArith.lean, GrowTM.lean): ONE TM; for every
  δ > 0 there is n₀ such that for every CNF φ on n ≥ n₀ variables with m ≤ n·2^{(lg n)^{1/7}} clauses (first version; now
  n·2^{(lg n)^{1/4}/(lglg n)²}, see below; any width, no repeated literal) it outputs #SAT(φ) within ⌊2^{δn}⌋ steps. Proof: same
  tree with width w = 2^{⌊lglg(2n)/6⌋}+1 ≈ lg(2n)^{1/6} read off
  the node (`stepW`); leaves counted by Anthropic's uniform compact-code machine (`MainTheoremCompact`), simulated as a
  stepped machine via `Wrap.sim`/`coding_exists` (space linear in time); `CountKSat.stHostW` for the final TM.
  Numbers: C·w²·N·lglgN/√lgN ≤ 328C·n·lg(2n)^{−11/84}; leaves ≤ 2^{(2/w)lg(e·w·(D+2))·n} with (2/w)lg(...) ≤ 96·y^{1/7}/w → 0.
  **Improved (S1):** density m ≤ n·2^{s}, s = (lg n)^{1/4}/(lg lg n)², so above n·2^{(lg n)^{1/4−ε}} for every ε. Width
  w = 2^{⌊L/4⌋−⌊lg L⌋}+1 with ℓ = ⌊lg 2n⌋, L = ⌊lg ℓ⌋, q = ⌊lg L⌋ (`wN`), so (w−1)⁴·2^{4q} ≤ ℓ < 16(w−1)⁴·2^{4q}
  (`wN_bounds`, needs L ≥ 16), w²L² ≤ 16√ℓ and ℓ < 16(w−1)⁴L⁴ (`wN_facts`). Exponent ≤ 32C·N/L (`expN_le`); s ≤ 4(w−1)/(L−1)
  (`sN_le`); (2/w)lg(e·w·(D+2)) ≤ (2/w)(4 + 3√w + s) → 0 (`log_part`, `width_small`). The method's limit is
  w = o((lg n)^{1/4}/√lglg n), i.e. density n·2^{o((lg n)^{1/4}/√lglg n)}; we give up a factor (lg lg n)^{3/2} for simpler
  arithmetic.
- **A4 (Max-SAT spectrum), done.** `EthCor.Spectrum.maxsat_spectrum` (EthCor/Spectrum.lean): for every width r, density D, δ > 0,
  one TM, input `unary t ++ SatFree.enc φ` (φ width ≤ r, ≤ D·n clauses, t ≤ m), outputs #{a : exactly t clauses true} in
  C·2^{δn}. Proof: 2n+m variables (x_u on 2u, ¬x_u on 2u+1 via pairF, y_j ↔ C_j on 2n+j); satisfying assignments with
  n+t true variables ↔ assignments with t satisfied clauses (`cntS_specF`, explicit bijection); Anthropic's `SIZED (r+2)`.
  Covers Max-Cut spectrum / ±1 Ising density of states on O(n)-edge graphs (edge uv ↦ (u∨v),(¬u∨¬v); #sat = |E| + cut);
  the graph-input corollary is not formalized separately.
- **A5a (⊕Hamiltonian Cycle, bounded degree), done.** `EthCor.HamTM.hc_parity_subexp` (EthCor/HamFormula.lean, HamTM.lean): for every
  Δ, one TM; for every ε > 0 there is n₀ such that for every graph G on n ≥ n₀ vertices with all degrees ≤ Δ, input `code G`, it
  outputs [#HC(G) is odd] within ⌊2^{εn}⌋ steps. #HC = `numHamCycles G` = #{H ≤ G spanning, connected, every degree 2}.
  Proof (Cut & Count): CNF on m + n variables (edge bits x, side bits s; every vertex on exactly two chosen edges via
  atMost2/atLeast2 clauses, chosen edges inside one side, s₀ false); #SAT = Σ over 2-factors x of #side maps (`cntN_hcF`);
  the side maps number 2^{cc−1}, odd iff connected (`parity_sides`, flip s on a component missing 0); edge choices ↔ H ≤ G
  (`card_hc`); so #SAT ≡ #HC mod 2 (`hc_parity`). Low bit of Anthropic's compact-code count, width Δ + 3 (`hc_parity_tm`,
  bound c·2^{c(Δ+3)²·N·r(N)}, N = m + n ≤ (Δ+1)n, `boundH_le`).
- **A5a′ (⊕HC, sparse, any degree), done.** `EthCor.HamSTM.hc_parity_sparse` (EthCor/HamCounter.lean, HamSparseTM.lean):
  ONE TM; for every θ, ε > 0 there is n₀ such that for every G on n ≥ n₀ vertices with |E(G)| ≤ n·(lg n)^{1/2−θ} it
  outputs [#HC(G) odd] within ⌊2^{εn}⌋ steps. Corollary `hc_parity_bounded`: one TM for all Δ (A5a had one per Δ).
  Proof: `hcS` replaces atMost2/atLeast2 by a sequential counter. Bits m+n+4e+2b (+1) = "≥1 (≥2) of the edges at end b of
  e, up to e, chosen"; the start counter is the pair z = 5m+n, z+1 forced false. Steps: c = p ∨ x, c+1 = (p+1) ∨ (x ∧ p),
  ¬(p+1 ∧ x), final c_d+1 (`stepC`, `cntC`, `sat_cntC` by induction on the list). The bits are determined (`auxOK_iff` on
  the sorted incidence list, `aux_iff`), so cntN(5m+n+2, hcS) = cntN(m+n, hcF) (`cntN_hcS`, via Fin.appendEquiv and
  card_nbij'). Width 3 → `hcS_tm` with bound c·2^{9c·N·r(N)}, N = 5m+n+2; `boundS_le` (rate_le_rpow with a = θ/2) gives
  2^{εn} for N ≤ 8n·(lg n)^{1/2−θ}. `length_edges_le_card`: the edge list injects into G.edgeFinset (Sym2).
  Limit of the method: m = o(n·√lg n/lglg n).
- A5b (deciding HC) status: blocked for "fast". Cut & Count needs isolation. MVV weights (≤ 2m per edge) blow the variables up
  to ~m², and the cntS "exactly t true" trick only carries O(n) total weight. Dense Valiant–Vazirani XORs need ~n·m auxiliary
  variables. The workable route is randomized: CIKP08 sparse-hash isolation (k-sparse XORs, no new variables, success
  ≥ 2^{−εn}), stated as "∃ M on (G, seed): no HC ⇒ 0 for all seeds; HC ⇒ 1 for ≥ 2^{−εn} of the seeds". That means
  formalizing the CIKP isolation lemma (heavy). Deterministically, "¬ETH ⇒ HC in 2^{o(n)}" is not known (HC is not known
  to be SERF-reducible to SAT).

## N1: deciding HC (sparse graphs) in randomized 2^{o(n)} — paper proof (2026-10-27)
Paper check of [CIKP08] Lemma 3 (ECCC TR06-062 / JCSS 74(3)): the proof never uses that S is the solution set of a
k-CNF. Step I (k′-sparse hyperplanes, semi-isolated solutions, Hamming-ball count) and Step II (fix the coordinates where
the two furthest surviving solutions differ) only use S ⊆ {0,1}^M nonempty. The k-CNF only makes the output a k′-CNF.
So it isolates an element of ANY nonempty S with probability 2^{−O(h(ε))M}, using O(M) XORs of width k′ = O(ε⁻¹ ln ε⁻¹).

Version for Lean (all probabilities = counts over a product Fintype Ω; parameters t, k, mm, r = ⌈M/t⌉):
- Row = (Fin k → Fin M) × (Fin k → Bool): indices J (with repetition), coefficients C; rv ρ x = Σ_l [C_l ∧ x(J_l)] ∈ ZMod 2.
  rv x + rv y = rv (x xor y). For |z| = w: #{ρ : rv ρ z = 0} = 2^{k−1}(M^k + (M−w)^k) (flip C at the first hit index:
  involution), so Pr ≤ q := (1 + (1 − r/M)^k)/2 when w ≥ r.
- ω = (m ∈ Fin (mm+1), rows : Fin mm → Row, B : Fin mm → Bool, U : Fin M → Fin t, V : Fin M → Bool).
  H(ω) = {x : rv(row_i) x = B_i for i < m, and x_j = V_j wherever U_j = 0}.
- Step I. x ∈ S′(rows) iff no y ∈ S with dist(x,y) ≥ r agrees with x on rows < m. Union bound: #{rows : x ∉ S′} ≤ |S| q^m
  |Row|^{mm}. Take m minimal with |S| q^m ≤ 1/2 (m ≥ 1, m ≤ mm = 3M+3 as q ≤ 3/4); then |S|2^{−m} ≥ (1+η)^{−mm}/4,
  η = (1 − r/M)^k ≤ e^{−kr/M}. Σ_{x∈S} #{(rows,B) : x ∈ S′, rows(x) = B} ≥ |S|·½·|Row|^{mm}·2^{mm−m}; for fixed (rows,B)
  the semi-isolated x with rows(x)=B lie in one ball of radius r−1, volume V ≤ (eM/(r−1))^{r−1} (Σ_{i≤R} C(M,i)(R/M)^R ≤
  (1+R/M)^M ≤ e^R). So #{(rows,B) : T := S ∩ {rows = B} has a semi-isolated point} ≥ |S|2^{−m}|Row|^{mm}2^{mm}/(2V);
  such T is nonempty with diameter < 2r.
- Step II. u, ū ∈ T furthest apart, C = diff(u, ū), |C| < 2r. If U_j = 0 for j ∈ C and V_j = u_j wherever U_j = 0,
  then S ∩ H(ω) = {u} (w ≠ u agreeing with u on C has dist(w, ū) = |C| + dist(w,u) > |C|). Per coordinate: j ∈ C:
  1 of 2t choices; j ∉ C: 2t−1 of 2t. Fraction ≥ (2t)^{−2r}(1 − 1/(2t))^M.
- Total: Pr[|S ∩ H(ω)| = 1] ≥ 1/(mm+1) · e^{−η·mm}/(8V) · (2t)^{−2r}(1−1/(2t))^M = 2^{−(O(lg t / t) + O(e^{−k/t}))M}.
  With k = t², width t², this is 2^{−δM} for t = t(δ).
- Use: S = Hamiltonian cycles of G as edge sets (M = m edges). Cut & Count with the extra edge clauses: #SAT ≡ |S ∩ H(ω)|
  (mod 2). An XOR row is a CNF on the same variables: one clause per violating σ ∈ {0,1}^k (inconsistent σ give
  tautologies). Width max(3, t²), N = 5m + n + 2 variables. No HC ⇒ output 0 for every ω; HC ⇒ output 1 for ≥ 2^{−δm}
  of the ω. For m ≤ D·n: one-sided-error HC decision in 2^{δn}·2^{o(n)} for every δ.
- Formalization plan: (1) EthCor/Isolation.lean — the lemma above for arbitrary S (pure counting); (2) XOR rows as CNF +
  Cut & Count with extra edge clauses (parity = |S ∩ H| mod 2); (3) the machine: input = code G ++ the seed, as in HamTM.

### N1 progress (2026-10-27)

Step (1) is done: `lean/EthCor/Isolation.lean` (pure counting) and `lean/EthCor/IsoBound.lean`
(parameters). Main theorems:
- `Iso.iso_count`: exact counting form, for every nonempty S and all r, mm, t;
- `Iso.iso_real`: explicit bound with r = ⌊M/a⌋+1, k = ab, mm = 3M+3;
- `Iso.isolation`: ∀ δ > 0, ∃ k t M₀, ∀ M ≥ M₀, ∀ S ≠ ∅: |Ω| ≤ 2^{δM}·#{ω : |S ∩ H ω| = 1}.

Standard axioms only. Next is step (2): XOR rows as CNF clauses. A row's support is
{j : Σ_{l : J l = j} C l odd}, of size ≤ k, so the row is 2^{|T|−1} clauses of width |T| on the edge
variables. The fixings become unit clauses. Then Cut & Count gives #SAT ≡ |HC ∩ H ω| (mod 2).
