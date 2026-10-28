import GraphProblems.Read
import GraphProblems.Defs
import GraphProblems.Interfaces
import Mathlib.Tactic

/-! # Nonblocker: dominating sets with at most n − k vertices

A graph G has a dominating set D with |D| + k ≤ n exactly if the graph `core G` induced on the
vertices with a neighbour has a dominating set D′ with |D′| + k ≤ n′, n′ its number of vertices: the
isolated vertices are in every dominating set (`nb_iff`). `core G` has no isolated vertex, so by Ore's
theorem it has a dominating set with at most n′/2 vertices (`ore`): the complement of a minimum
dominating set dominates (`compl_dominating`). So the answer is yes if 2k ≤ n′, no if n′ < k, and
otherwise, with n′ < 2k, it is whether `core G` has a dominating set with exactly n′ − k vertices
(`nb_answer`). The vertices with a neighbour (`niL`) and the matrix of `core G` (`subM`,
`matrix_core`) are read off the matrix of G by lists. -/

noncomputable section

namespace EthCor.Nb

open GraphProblems Finset

variable {n : ℕ}

/-! ### Ore's theorem -/

theorem isDominating_univ (G : SimpleGraph (Fin n)) : IsDominating G univ := fun v => Or.inl (mem_univ v)

theorem IsDominating.mono {G : SimpleGraph (Fin n)} {D D' : Finset (Fin n)} (h : IsDominating G D) (hs : D ⊆ D') :
    IsDominating G D' := fun v => (h v).imp (fun hv => hs hv) fun ⟨u, hu, ha⟩ => ⟨u, hs hu, ha⟩

/-- Without isolated vertices, the complement of a minimum dominating set dominates. -/
theorem compl_dominating {G : SimpleGraph (Fin n)} (hG : ∀ v, ∃ u, G.Adj v u) {D : Finset (Fin n)}
    (hD : IsDominating G D) (hmin : ∀ D', IsDominating G D' → D.card ≤ D'.card) : IsDominating G (univ \ D) := by
  intro v
  by_cases hv : v ∈ D
  · right
    by_contra hno
    have hno' : ∀ u, u ∉ D → ¬ G.Adj v u := fun u hu ha => hno ⟨u, mem_sdiff.2 ⟨mem_univ _, hu⟩, ha⟩
    have hE : IsDominating G (D.erase v) := by
      intro x
      by_cases hx : x = v
      · subst hx
        obtain ⟨u, hu⟩ := hG x
        have huD : u ∈ D := by
          by_contra h
          exact hno' u h hu
        exact Or.inr ⟨u, mem_erase.2 ⟨(G.ne_of_adj hu).symm, huD⟩, hu⟩
      · rcases hD x with hxD | ⟨u, huD, hxu⟩
        · exact Or.inl (mem_erase.2 ⟨hx, hxD⟩)
        · by_cases huv : u = v
          · subst huv
            by_cases hxD : x ∈ D
            · exact Or.inl (mem_erase.2 ⟨hx, hxD⟩)
            · exact absurd hxu.symm (hno' x hxD)
          · exact Or.inr ⟨u, mem_erase.2 ⟨huv, huD⟩, hxu⟩
    have h1 := hmin _ hE
    rw [card_erase_of_mem hv] at h1
    have h2 : 0 < D.card := card_pos.2 ⟨v, hv⟩
    omega
  · exact Or.inl (mem_sdiff.2 ⟨mem_univ _, hv⟩)

/-- **Ore's theorem.** A graph without isolated vertices has a dominating set with at most n/2 vertices. -/
theorem ore (G : SimpleGraph (Fin n)) (hG : ∀ v, ∃ u, G.Adj v u) : ∃ D, IsDominating G D ∧ 2 * D.card ≤ n := by
  classical
  obtain ⟨D, hD, hmin⟩ := (univ.filter fun D : Finset (Fin n) => IsDominating G D).exists_min_image card
    ⟨univ, mem_filter.2 ⟨mem_univ _, isDominating_univ G⟩⟩
  rw [mem_filter] at hD
  have hmin' : ∀ D', IsDominating G D' → D.card ≤ D'.card := fun D' h => hmin D' (mem_filter.2 ⟨mem_univ _, h⟩)
  refine ⟨D, hD.2, ?_⟩
  have h1 := hmin' _ (compl_dominating hG hD.2 hmin')
  have h2 : (univ \ D).card + D.card = n := by
    rw [card_sdiff_add_card_eq_card (subset_univ D), card_univ, Fintype.card_fin]
  omega

/-! ### The vertices with a neighbour -/

/-- The vertices with a neighbour, read off the matrix. -/
def niL (n : ℕ) (m : List Bool) : List ℕ :=
  (List.range n).filter fun v => (List.range n).any fun u => adjB n m v u

/-- The matrix of the graph induced on the vertices of the list J. -/
def subM (n : ℕ) (m : List Bool) (J : List ℕ) : List Bool := J.flatMap fun u => J.map fun v => adjB n m u v

theorem nodup_niL (n : ℕ) (m : List Bool) : (niL n m).Nodup := List.nodup_range.filter _

theorem lt_of_mem_niL {n : ℕ} {m : List Bool} {v : ℕ} (h : v ∈ niL n m) : v < n :=
  List.mem_range.1 (List.mem_of_mem_filter h)

theorem mem_niL (G : SimpleGraph (Fin n)) {v : ℕ} : v ∈ niL n (matrix G) ↔ ∃ h : v < n, ∃ u, G.Adj ⟨v, h⟩ u := by
  simp only [niL, List.mem_filter, List.mem_range, List.any_eq_true]
  constructor
  · rintro ⟨hv, u, hu, ha⟩
    exact ⟨hv, ⟨u, hu⟩, (stAdj n G ⟨v, hv⟩ ⟨u, hu⟩).1 ha⟩
  · rintro ⟨hv, u, ha⟩
    exact ⟨hv, u, u.2, (stAdj n G ⟨v, hv⟩ u).2 ha⟩

section Core

variable (G : SimpleGraph (Fin n))

/-- The i-th vertex with a neighbour. -/
def emb (i : Fin (niL n (matrix G)).length) : Fin n :=
  ⟨(niL n (matrix G))[i], lt_of_mem_niL (List.getElem_mem _)⟩

theorem emb_injective : Function.Injective (emb G) := by
  intro i j h
  have h' : (niL n (matrix G))[i] = (niL n (matrix G))[j] := congrArg Fin.val h
  exact Fin.ext ((nodup_niL n _).getElem_inj_iff.1 h')

theorem mem_range_emb (v : Fin n) : (∃ i, emb G i = v) ↔ ∃ u, G.Adj v u := by
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨_, u, hu⟩ := (mem_niL G).1 (List.getElem_mem (l := niL n (matrix G)) i.2)
    exact ⟨u, hu⟩
  · intro h
    have hm : v.val ∈ niL n (matrix G) := (mem_niL G).2 ⟨v.2, h⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
    exact ⟨⟨i, hi⟩, Fin.ext he⟩

/-- The graph induced on the vertices with a neighbour. -/
def core : SimpleGraph (Fin (niL n (matrix G)).length) := G.comap (emb G)

theorem core_adj (i j : Fin (niL n (matrix G)).length) : (core G).Adj i j ↔ G.Adj (emb G i) (emb G j) := Iff.rfl

/-- `core G` has no isolated vertex. -/
theorem core_noiso (i : Fin (niL n (matrix G)).length) : ∃ j, (core G).Adj i j := by
  obtain ⟨u, hu⟩ := (mem_range_emb G (emb G i)).1 ⟨i, rfl⟩
  obtain ⟨j, rfl⟩ := (mem_range_emb G u).2 ⟨_, hu.symm⟩
  exact ⟨j, hu⟩

theorem matrix_core : matrix (core G) = subM n (matrix G) (niL n (matrix G)) := by
  classical
  conv_rhs => rw [subM, ← List.map_getElem_finRange (niL n (matrix G))]
  conv_lhs => unfold matrix
  rw [List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun v _ => ?_
  have h := stAdj n G (emb G u) (emb G v)
  change decide (G.Adj (emb G u) (emb G v)) = adjB n (matrix G) (emb G u) (emb G v)
  cases hb : adjB n (matrix G) (emb G u) (emb G v)
  · rw [hb] at h; simpa using h
  · rw [hb] at h; simpa using h

open Classical in
/-- The isolated vertices and the others make up all n. -/
theorem card_iso_add : (univ.filter fun v : Fin n => ¬ ∃ u, G.Adj v u).card + (niL n (matrix G)).length = n := by
  classical
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun v : Fin n => ∃ u, G.Adj v u
  have h2 : (univ.filter fun v : Fin n => ∃ u, G.Adj v u) = univ.image (emb G) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_image]
    exact (mem_range_emb G v).symm
  rw [h2, card_image_of_injective _ (emb_injective G), card_univ, card_univ, Fintype.card_fin,
    Fintype.card_fin] at h1
  omega

/-- The isolated vertices are in every dominating set, so G and `core G` have the same answer. -/
theorem nb_iff (k : ℕ) : (∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n) ↔
    ∃ D : Finset (Fin (niL n (matrix G)).length), IsDominating (core G) D ∧ D.card + k ≤ (niL n (matrix G)).length := by
  classical
  have hI := card_iso_add G
  constructor
  · rintro ⟨D, hD, hk⟩
    refine ⟨univ.filter fun i => emb G i ∈ D, fun i => ?_, ?_⟩
    · by_cases hi : emb G i ∈ D
      · exact Or.inl (mem_filter.2 ⟨mem_univ _, hi⟩)
      · rcases hD (emb G i) with hv | ⟨u, hu, ha⟩
        · exact absurd hv hi
        · obtain ⟨j, rfl⟩ := (mem_range_emb G u).2 ⟨_, ha.symm⟩
          exact Or.inr ⟨j, mem_filter.2 ⟨mem_univ _, hu⟩, ha⟩
    · have hID : (univ.filter fun v : Fin n => ¬ ∃ u, G.Adj v u) ⊆ D := fun v hv => by
        rcases hD v with h | ⟨u, -, ha⟩
        · exact h
        · exact absurd ⟨u, ha⟩ (mem_filter.1 hv).2
      have hmap : ((univ.filter fun i => emb G i ∈ D).map ⟨emb G, emb_injective G⟩) ⊆
          D \ univ.filter fun v : Fin n => ¬ ∃ u, G.Adj v u := by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := mem_map.1 hv
        exact mem_sdiff.2 ⟨(mem_filter.1 hi).2, fun h => (mem_filter.1 h).2 ((mem_range_emb G _).1 ⟨i, rfl⟩)⟩
      have h1 := card_le_card hmap
      have h2 := card_sdiff_add_card_eq_card hID
      rw [card_map] at h1
      omega
  · rintro ⟨D, hD, hk⟩
    refine ⟨D.map ⟨emb G, emb_injective G⟩ ∪ univ.filter fun v : Fin n => ¬ ∃ u, G.Adj v u, fun v => ?_, ?_⟩
    · by_cases hv : ∃ u, G.Adj v u
      · obtain ⟨i, rfl⟩ := (mem_range_emb G v).2 hv
        rcases hD i with h | ⟨j, hj, ha⟩
        · exact Or.inl (mem_union_left _ (mem_map_of_mem _ h))
        · exact Or.inr ⟨emb G j, mem_union_left _ (mem_map_of_mem _ hj), ha⟩
      · exact Or.inl (mem_union_right _ (mem_filter.2 ⟨mem_univ _, hv⟩))
    · have := card_union_le (D.map ⟨emb G, emb_injective G⟩) (univ.filter fun v : Fin n => ¬ ∃ u, G.Adj v u)
      rw [card_map] at this
      omega

end Core

/-! ### The answer -/

theorem numDom_pos_iff {N : ℕ} (H : SimpleGraph (Fin N)) {s : ℕ} (hs : s ≤ N) :
    0 < numDominatingSets H s ↔ ∃ D, IsDominating H D ∧ D.card ≤ s := by
  rw [numDominatingSets, Set.ncard_pos (Set.toFinite _)]
  constructor
  · rintro ⟨D, hD, hc⟩
    exact ⟨D, hD, hc.le⟩
  · rintro ⟨D, hD, hc⟩
    obtain ⟨D', h1, -, h3⟩ := Finset.exists_subsuperset_card_eq (subset_univ D) hc (by simp [hs])
    exact ⟨D', IsDominating.mono hD h1, h3⟩

/-- **The answer.** With n′ the number of vertices with a neighbour: yes if 2k ≤ n′; otherwise
whether k ≤ n′ and `core G` has a dominating set with exactly n′ − k vertices. -/
theorem nb_answer (G : SimpleGraph (Fin n)) (k : ℕ) :
    (∃ D : Finset (Fin n), IsDominating G D ∧ D.card + k ≤ n) ↔
      (2 * k ≤ (niL n (matrix G)).length ∨
        (k ≤ (niL n (matrix G)).length ∧ 0 < numDominatingSets (core G) ((niL n (matrix G)).length - k))) := by
  rw [nb_iff G k]
  constructor
  · rintro ⟨D, hD, hk⟩
    by_cases h2 : 2 * k ≤ (niL n (matrix G)).length
    · exact Or.inl h2
    · exact Or.inr ⟨by omega, (numDom_pos_iff _ (Nat.sub_le _ _)).2 ⟨D, hD, by omega⟩⟩
  · rintro (h2 | ⟨hk, hpos⟩)
    · obtain ⟨D, hD, hc⟩ := ore (core G) (core_noiso G)
      exact ⟨D, hD, by omega⟩
    · obtain ⟨D, hD, hc⟩ := (numDom_pos_iff _ (Nat.sub_le _ _)).1 hpos
      exact ⟨D, hD, by omega⟩

end EthCor.Nb

end
