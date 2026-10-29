import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! # Spanning trees with many leaves and connected dominating sets

For a graph on n ≥ 3 vertices and 1 ≤ L < n: G has a spanning tree with at least L leaves if and
only if it has a connected dominating set with exactly n − L vertices (`leaf_iff`). The non-leaves
of a spanning tree dominate (a leaf hangs on a non-leaf when n ≥ 3) and induce a connected
subgraph, since an inner vertex of a path has two neighbours on it (`cds_of_tree`). Conversely,
for a connected dominating set X, the graph with the edges inside X and one edge from every other
vertex into X is connected, and in each of its spanning trees the vertices outside X are leaves
(`tree_of_cds`). A vertex outside a connected dominating set has a neighbour in it, so the sizes of
connected dominating sets are all k from the minimum up to n (`cds_grow`, `cds_le_iff`); this is the
classical identity γ_c(G) = n − (maximum number of leaves) of Hedetniemi and Laskar. -/

namespace EthCor.Leaf

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- X is a connected dominating set of G. -/
def IsCDS (G : SimpleGraph V) (X : Finset V) : Prop :=
  (∀ v, v ∈ X ∨ ∃ u ∈ X, G.Adj v u) ∧ (G.induce (X : Set V)).Connected

open Classical in
/-- The leaves of T: its vertices of degree 1. -/
noncomputable def leaves (T : SimpleGraph V) : Finset V := univ.filter fun v => T.degree v = 1

/-- An inner vertex of a path has degree at least 2. -/
theorem two_le_degree {T : SimpleGraph V} [DecidableRel T.Adj] {x y : V} (p : T.Walk x y) (hp : p.IsPath)
    {z : V} (hz : z ∈ p.support) (hx : z ≠ x) (hy : z ≠ y) : 2 ≤ T.degree z := by
  obtain ⟨i, hi, rfl⟩ : ∃ i ≤ p.length, p.getVert i = z := by
    refine ⟨p.support.idxOf z, ?_, p.getVert_support_idxOf hz⟩
    have := List.idxOf_lt_length_of_mem hz
    rw [Walk.length_support] at this
    omega
  have h0 : i ≠ 0 := by rintro rfl; exact hx p.getVert_zero
  have hl : i < p.length := by
    rcases lt_or_eq_of_le hi with h | rfl
    · exact h
    · exact absurd p.getVert_length hy
  have a1 : T.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hl
  have a2 : T.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have := p.adj_getVert_succ (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm
  have hne : p.getVert (i + 1) ≠ p.getVert (i - 1) := by
    intro h
    have := hp.getVert_injOn (show i + 1 ≤ p.length by omega) (show i - 1 ≤ p.length by omega) h
    omega
  rw [← card_neighborFinset_eq_degree]
  calc 2 = ({p.getVert (i + 1), p.getVert (i - 1)} : Finset V).card := (card_pair hne).symm
    _ ≤ _ := card_le_card fun w hw => by
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> simp [mem_neighborFinset, a1, a2]

open Classical in
/-- **The non-leaves of a spanning tree form a connected dominating set**, for n ≥ 3. -/
theorem cds_of_tree {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (h3 : 3 ≤ Fintype.card V) :
    IsCDS G (univ.filter fun v => T.degree v ≠ 1) := by
  set X := univ.filter fun v => T.degree v ≠ 1 with hXdef
  have hmem : ∀ v, v ∈ X ↔ T.degree v ≠ 1 := fun v => by simp [hXdef]
  -- a path in T: its inner vertices are in X
  have hpath : ∀ {x y : V} (p : T.Walk x y), p.IsPath → ∀ z ∈ p.support, z ≠ x → z ≠ y → z ∈ X :=
    fun p hp z hz hx hy => (hmem z).2 (by have := two_le_degree p hp hz hx hy; omega)
  have hdom : ∀ v, v ∈ X ∨ ∃ u ∈ X, G.Adj v u := by
    intro v
    by_cases hv : T.degree v = 1
    · obtain ⟨u, hu⟩ := card_eq_one.1 (show (T.neighborFinset v).card = 1 by rw [card_neighborFinset_eq_degree, hv])
      have huv : T.Adj v u := (mem_neighborFinset T v u).1 (by rw [hu]; exact mem_singleton_self u)
      obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card (s := {u, v}) (t := univ)
        (by rw [card_univ]; exact lt_of_le_of_lt (card_le_two) (by omega))
      simp only [mem_insert, mem_singleton, not_or] at hw
      obtain ⟨p, hp⟩ : ∃ p : T.Walk v w, p.IsPath := ⟨(hT.1 v w).some.bypass, Walk.bypass_isPath _⟩
      have hlen : 0 < p.length := by
        rcases Nat.eq_zero_or_pos p.length with h | h
        · exact absurd (Walk.eq_of_length_eq_zero h) (Ne.symm hw.2)
        · exact h
      have h1 : T.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hlen
      have h1u : p.getVert 1 = u := by
        have := (mem_neighborFinset T v _).2 h1
        rw [hu] at this
        exact mem_singleton.1 this
      refine Or.inr ⟨u, ?_, hTG huv⟩
      rw [← h1u]
      exact hpath p hp _ (p.getVert_mem_support 1) (by rw [h1u]; exact huv.ne.symm) (by rw [h1u]; exact Ne.symm hw.1)
    · exact Or.inl ((hmem v).2 hv)
  refine ⟨hdom, ?_⟩
  -- a vertex of X
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∈ X := by
    obtain ⟨v⟩ := hne
    rcases hdom v with h | ⟨u, hu, -⟩
    · exact ⟨v, h⟩
    · exact ⟨u, hu⟩
  refine induce_connected_of_patches x0 (mem_coe.2 hx0) fun {v} hv => ?_
  obtain ⟨p, hp⟩ : ∃ p : T.Walk x0 v, p.IsPath := ⟨(hT.1 x0 v).some.bypass, Walk.bypass_isPath _⟩
  have hsub : {z | z ∈ (p.mapLe hTG).support} ⊆ (X : Set V) := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Walk.support_mapLe_eq_support] at hz
    rw [mem_coe]
    by_cases h1 : z = x0
    · exact h1 ▸ hx0
    by_cases h2 : z = v
    · exact h2 ▸ mem_coe.1 hv
    exact hpath p hp z hz h1 h2
  exact ⟨_, hsub, (p.mapLe hTG).start_mem_support, (p.mapLe hTG).end_mem_support,
    (p.mapLe hTG).connected_induce_support.preconnected _ _⟩

/-- **A connected dominating set X gives a spanning tree in which every vertex outside X is a
leaf**, for n ≥ 2. -/
theorem tree_of_cds {X : Finset V} (hX : IsCDS G X) (h2 : 2 ≤ Fintype.card V) :
    ∃ T ≤ G, T.IsTree ∧ Xᶜ ⊆ leaves T := by
  classical
  choose! f hf using fun v (hv : v ∉ X) => (hX.1 v).resolve_left hv
  -- the edges inside X and one edge from every other vertex into X
  let r : V → V → Prop := fun a b => G.Adj a b ∧ ((a ∈ X ∧ b ∈ X) ∨ (a ∉ X ∧ b = f a))
  let H := SimpleGraph.fromRel r
  have hHG : H ≤ G := by
    intro a b h
    rw [fromRel_adj] at h
    rcases h.2 with h' | h'
    · exact h'.1
    · exact h'.1.symm
  have hHadj : ∀ {a b}, a ∈ X → b ∈ X → G.Adj a b → H.Adj a b := fun ha hb h =>
    (fromRel_adj _ _ _).2 ⟨h.ne, Or.inl ⟨h, Or.inl ⟨ha, hb⟩⟩⟩
  have hHf : ∀ {v}, v ∉ X → H.Adj v (f v) := fun {v} hv =>
    (fromRel_adj _ _ _).2 ⟨(hf v hv).2.ne, Or.inl ⟨(hf v hv).2, Or.inr ⟨hv, rfl⟩⟩⟩
  obtain ⟨⟨x0, hx0⟩⟩ := hX.2.nonempty
  have hreach : ∀ v, H.Reachable x0 v := by
    let φ : G.induce (X : Set V) →g H := ⟨Subtype.val, fun {a b} h => hHadj a.2 b.2 h⟩
    have hin : ∀ {v}, v ∈ X → H.Reachable x0 v := fun {v} hv =>
      (hX.2.preconnected ⟨x0, hx0⟩ ⟨v, mem_coe.2 hv⟩).map φ
    intro v
    by_cases hv : v ∈ X
    · exact hin hv
    · exact (hin (hf v hv).1).trans (hHf hv).symm.reachable
  have : Nonempty V := ⟨x0⟩
  have hH : H.Connected := ⟨fun u v => (hreach u).symm.trans (hreach v)⟩
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  refine ⟨T, hTH.trans hHG, hT, fun v hv => ?_⟩
  have hvX : v ∉ X := mem_compl.1 hv
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hpos := hT.1.preconnected.degree_pos_of_nontrivial v
  have hle : T.degree v ≤ 1 := by
    rw [← card_neighborFinset_eq_degree]
    refine (card_le_card (t := {f v}) fun w hw => ?_).trans (card_singleton _).le
    have h := (fromRel_adj _ _ _).1 (hTH ((mem_neighborFinset T v w).1 hw))
    rcases h.2 with ⟨-, ⟨h1, -⟩ | ⟨-, rfl⟩⟩ | ⟨-, ⟨-, h1⟩ | ⟨hw', rfl⟩⟩
    · exact absurd h1 hvX
    · exact mem_singleton_self _
    · exact absurd h1 hvX
    · exact absurd (hf w hw').1 hvX
  simp only [leaves, mem_filter, mem_univ, true_and]
  omega

/-- **Growing a connected dominating set**: one of size k ≤ ℓ ≤ n gives one of size exactly ℓ. -/
theorem cds_grow {X : Finset V} (hX : IsCDS G X) {ℓ : ℕ} (hXℓ : X.card ≤ ℓ) (hℓ : ℓ ≤ Fintype.card V) :
    ∃ Y, IsCDS G Y ∧ Y.card = ℓ := by
  obtain ⟨d, hd⟩ : ∃ d, ℓ = X.card + d := ⟨ℓ - X.card, by omega⟩
  subst hd
  induction d generalizing X with
  | zero => exact ⟨X, hX, rfl⟩
  | succ d ih =>
    obtain ⟨v, -, hv⟩ := exists_mem_notMem_of_card_lt_card (s := X) (t := univ) (by rw [card_univ]; omega)
    obtain ⟨u, hu, hvu⟩ := (hX.1 v).resolve_left hv
    have hY : IsCDS G (insert v X) := by
      refine ⟨fun w => ?_, ?_⟩
      · rcases hX.1 w with h | ⟨u', hu', h⟩
        · exact Or.inl (mem_insert_of_mem h)
        · exact Or.inr ⟨u', mem_insert_of_mem hu', h⟩
      · have e : ((insert v X : Finset V) : Set V) = (X : Set V) ∪ {v, u} := by
          ext w
          simp only [coe_insert, Set.mem_insert_iff, mem_coe, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro (h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
          · rintro (h | h | h)
            · exact Or.inr h
            · exact Or.inl h
            · exact Or.inr (h ▸ hu)
        rw [e]
        exact induce_union_connected hX.2.preconnected (induce_pair_connected_of_adj hvu).preconnected
          ⟨u, mem_coe.2 hu, by simp⟩
    have hc : (insert v X).card = X.card + 1 := card_insert_of_notMem hv
    obtain ⟨Y, hY', hYc⟩ := ih hY (by rw [hc]; omega) (by rw [hc]; omega)
    exact ⟨Y, hY', by rw [hYc, hc]; omega⟩

/-- A connected dominating set with at most ℓ vertices exists iff one with exactly ℓ does, ℓ ≤ n. -/
theorem cds_le_iff {ℓ : ℕ} (hℓ : ℓ ≤ Fintype.card V) :
    (∃ X, IsCDS G X ∧ X.card ≤ ℓ) ↔ ∃ X, IsCDS G X ∧ X.card = ℓ :=
  ⟨fun ⟨_, hX, h⟩ => cds_grow hX h hℓ, fun ⟨X, hX, h⟩ => ⟨X, hX, h.le⟩⟩

/-- **Max Leaf Spanning Tree and connected domination.** For n ≥ 3 vertices and 1 ≤ L < n, G has a
spanning tree with at least L leaves iff it has a connected dominating set with n − L vertices. -/
theorem leaf_iff (h3 : 3 ≤ Fintype.card V) {L : ℕ} (hL : L < Fintype.card V) :
    (∃ T ≤ G, T.IsTree ∧ L ≤ (leaves T).card) ↔ ∃ X, IsCDS G X ∧ X.card = Fintype.card V - L := by
  classical
  constructor
  · rintro ⟨T, hTG, hT, hl⟩
    have hX := cds_of_tree hTG hT h3
    have hc := card_filter_add_card_filter_not (s := (univ : Finset V)) fun v => T.degree v = 1
    rw [card_univ] at hc
    have e1 : (leaves T).card = (univ.filter fun v => T.degree v = 1).card := rfl
    refine cds_grow hX ?_ (by omega)
    show (univ.filter fun v => ¬ T.degree v = 1).card ≤ _
    omega
  · rintro ⟨X, hX, hc⟩
    obtain ⟨T, hTG, hT, hsub⟩ := tree_of_cds hX (by omega)
    refine ⟨T, hTG, hT, ?_⟩
    have := card_le_card hsub
    rw [card_compl] at this
    omega

end EthCor.Leaf
