import EthCor.HamIsoTM
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! # The count of Hamiltonian cycles against Mathlib's definition

`numHamCycles G` counts the connected spanning subgraphs H ≤ G with every degree 2. Mathlib's
`G.IsHamiltonian` says that G has a walk that is a cycle and visits every vertex once (and, by
convention, holds for the one-vertex graph). For n ≠ 1 the two agree: `0 < numHamCycles G` if and
only if `G.IsHamiltonian` (`numHamCycles_pos_iff`). More: `numHamCycles G` is the number of edge sets
of Mathlib Hamiltonian cycles of G (`numHamCycles_eq`), so the parity results count Hamiltonian
cycles in the usual sense. One direction takes the subgraph of the edges of
a Hamiltonian cycle. The other uses Mathlib's `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`:
a connected graph with every degree 2 is one cycle through all its vertices.

With this, the randomized algorithm of A5b decides Mathlib's `IsHamiltonian` (`ham_randomized_mathlib`). -/

namespace EthCor.Ham

open SimpleGraph Finset

theorem degree_eq_ncard {V : Type} (H : SimpleGraph V) (v : V) [Fintype (H.neighborSet v)] :
    H.degree v = (H.neighborSet v).ncard := by
  rw [← card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card', Set.toFinset_card]

open Classical in
/-- A connected graph with every degree 2 is a Hamiltonian cycle: it is the graph of the edges of a
Hamiltonian cycle of itself. -/
theorem exists_cycle_of_two {n : ℕ} {H : SimpleGraph (Fin n)} (hdeg : ∀ v, H.degree v = 2) (hconn : H.Connected) :
    ∃ v, ∃ p : H.Walk v v, p.IsHamiltonianCycle ∧ p.toSubgraph.spanningCoe = H := by
  have hcyc : H.IsCycles := fun v _ => by rw [← degree_eq_ncard, hdeg v]
  obtain ⟨v⟩ := hconn.nonempty
  have hne : (H.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [← degree_eq_ncard, hdeg v]; norm_num)
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk v) ((ConnectedComponent.mem_supp_iff _ _).2 rfl) hne
  have hall' : ∀ w, w ∈ p.toSubgraph.verts := fun w => by
    rw [hverts, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact hconn.preconnected w v
  have hall : ∀ w, w ∈ p.support := fun w => (Walk.mem_verts_toSubgraph p).1 (hall' w)
  have htail : ∀ w, w ∈ p.tail.support := fun w => by
    by_cases hw : w = v
    · subst hw; exact p.tail.end_mem_support
    · rw [Walk.support_tail_of_not_nil p hp.not_nil]
      have := hall w
      rw [← Walk.cons_tail_support] at this
      exact (List.mem_cons.1 this).resolve_left hw
  refine ⟨v, p, ⟨hp, hp.isPath_tail.isHamiltonian_of_mem htail⟩, ?_⟩
  ext u w
  rw [Subgraph.spanningCoe_adj]
  exact hp.adj_toSubgraph_iff_of_isCycles hcyc (hall' u) w

open Classical in
/-- The graph of the edges of a Hamiltonian cycle of G is a connected spanning subgraph of G with
every degree 2. -/
theorem two_of_cycle {n : ℕ} {G : SimpleGraph (Fin n)} {a : Fin n} {p : G.Walk a a} (hp : p.IsHamiltonianCycle) :
    p.toSubgraph.spanningCoe ≤ G ∧ (∀ w, p.toSubgraph.spanningCoe.degree w = 2) ∧
      p.toSubgraph.spanningCoe.Connected := by
  refine ⟨p.toSubgraph.spanningCoe_le, fun w => ?_, ?_⟩
  · rw [degree_eq_ncard]
    exact hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support w)
  · have hv : ∀ w, w ∈ p.toSubgraph.verts := fun w => (Walk.mem_verts_toSubgraph p).2 (hp.mem_support w)
    let f : p.toSubgraph.coe →g p.toSubgraph.spanningCoe := ⟨Subtype.val, fun h => h⟩
    exact p.toSubgraph_connected.coe.map f (fun w => ⟨⟨w, hv w⟩, rfl⟩)

open Classical in
theorem edgeFinset_toSubgraph {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
  ext e
  rw [mem_edgeFinset, Subgraph.edgeSet_spanningCoe, Walk.edgeSet_toSubgraph, Walk.mem_edgeSet, List.mem_toFinset]

open Classical in
/-- **The count agrees with Mathlib.** For n ≠ 1, G has a connected spanning subgraph with every
degree 2 if and only if G is Hamiltonian in the sense of Mathlib. -/
theorem numHamCycles_pos_iff {n : ℕ} (G : SimpleGraph (Fin n)) (hn : n ≠ 1) :
    0 < numHamCycles G ↔ G.IsHamiltonian := by
  rw [numHamCycles, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨H, -, hHG, hdeg, hconn⟩ -
    obtain ⟨v, p, hp, -⟩ := exists_cycle_of_two hdeg hconn
    exact ⟨v, p.map (Hom.ofLE hHG), hp.map (f := Hom.ofLE hHG) Function.bijective_id⟩
  · intro hG
    obtain ⟨a, p, hp⟩ := hG (by simpa using hn)
    exact ⟨p.toSubgraph.spanningCoe, mem_univ _, two_of_cycle hp⟩

open Classical in
/-- **`numHamCycles G` is the number of Hamiltonian cycles of G**, each cycle counted once as its
set of edges (Mathlib's `IsHamiltonianCycle`; a cycle and its rotations and reversal have the same
edges). -/
theorem numHamCycles_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    numHamCycles G = (univ.filter fun s : Finset (Sym2 (Fin n)) =>
      ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle ∧ p.edges.toFinset = s).card := by
  rw [numHamCycles]
  refine Finset.card_bij (fun H _ => H.edgeFinset) (fun H hH => ?_) (fun H _ H' _ h => edgeFinset_inj.1 h)
    (fun s hs => ?_)
  · obtain ⟨hHG, hdeg, hconn⟩ := (mem_filter.1 hH).2
    obtain ⟨v, p, hp, he⟩ := exists_cycle_of_two hdeg hconn
    refine mem_filter.2 ⟨mem_univ _, v, p.map (Hom.ofLE hHG), hp.map (f := Hom.ofLE hHG) Function.bijective_id, ?_⟩
    have h1 : (p.map (Hom.ofLE hHG)).edges = p.edges := Walk.edges_mapLe_eq_edges hHG p
    have h2 : H.edgeFinset = p.edges.toFinset := by
      ext e
      rw [mem_edgeFinset, List.mem_toFinset, ← Walk.mem_edgeSet, ← Walk.edgeSet_toSubgraph,
        ← Subgraph.edgeSet_spanningCoe, he]
    rw [h1, h2]
  · obtain ⟨a, p, hp, rfl⟩ := (mem_filter.1 hs).2
    exact ⟨p.toSubgraph.spanningCoe, mem_filter.2 ⟨mem_univ _, two_of_cycle hp⟩, edgeFinset_toSubgraph p⟩

end EthCor.Ham

namespace EthCor.HamITM

open Finset Turing

open Classical in
/-- **Hamiltonian Cycle with one-sided error in time 2^{o(n)}, for O(n) edges, with Mathlib's
definition.** As `ham_randomized`, with `G.IsHamiltonian` in place of the count. -/
theorem ham_randomized_mathlib : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (D : ℕ) (δ ε : ℝ), 0 < δ → 0 < ε → ∃ k t n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      G.edgeFinset.card ≤ D * n →
      ∃ out : Iso.Seed (Ham.edges n (GraphProblems.matrix G)).length k t
          (3 * (Ham.edges n (GraphProblems.matrix G)).length + 3) → Bool,
        (∀ ω, Wrap.Outputs M (GraphProblems.code G ++ seedCode ω) [out ω] ⌊(2 : ℝ) ^ (ε * n)⌋₊) ∧
        (¬ G.IsHamiltonian → ∀ ω, out ω = false) ∧
        (G.IsHamiltonian →
          (Fintype.card (Iso.Seed (Ham.edges n (GraphProblems.matrix G)).length k t
              (3 * (Ham.edges n (GraphProblems.matrix G)).length + 3)) : ℝ) ≤
            2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨M, hfin, hM⟩ := ham_randomized
  refine ⟨M, hfin, fun D δ ε hδ hε => ?_⟩
  obtain ⟨k, t, n₀, h⟩ := hM D δ ε hδ hε
  refine ⟨k, t, n₀ + 2, fun n G hn hm => ?_⟩
  obtain ⟨out, h1, h2, h3⟩ := h n G (by omega) hm
  have hiff := Ham.numHamCycles_pos_iff G (show n ≠ 1 by omega)
  exact ⟨out, h1, fun hG => h2 (Nat.eq_zero_of_not_pos fun hpos => hG (hiff.1 hpos)), fun hG => h3 (hiff.2 hG)⟩

end EthCor.HamITM
