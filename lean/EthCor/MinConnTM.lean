import EthCor.PosConnTM

/-! # Minimum Steiner tree, connected vertex cover and Group Steiner tree with one-sided error

For a positive CNF φ, the vertex sets X that meet every clause of φ and induce a connected subgraph
are closed under adding a neighbour. So in a connected graph, one with at most ℓ ≤ n vertices
exists iff one with exactly ℓ does (`conn_grow`, `min_iff`), and the machines of N2′
(`ConnITM.conn_randomized`) and N8′ (`PosTM.pos_randomized`), run with ℓ, decide whether one with
at most ℓ vertices exists. With φ = the terminals this is minimum Steiner tree, with φ = the edges
minimum connected vertex cover, with φ = the groups minimum Group Steiner tree. -/

namespace EthCor.MinTM

open Finset SimpleGraph

section Grow

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Growing a connected set** in a connected graph: one of size k ≤ ℓ ≤ n lies in one of size
exactly ℓ. -/
theorem conn_grow (hG : G.Connected) {X : Finset V} (hX : (G.induce (X : Set V)).Connected) {ℓ : ℕ}
    (hXℓ : X.card ≤ ℓ) (hℓ : ℓ ≤ Fintype.card V) :
    ∃ Y, X ⊆ Y ∧ (G.induce (Y : Set V)).Connected ∧ Y.card = ℓ := by
  obtain ⟨d, hd⟩ : ∃ d, ℓ = X.card + d := ⟨ℓ - X.card, by omega⟩
  subst hd
  induction d generalizing X with
  | zero => exact ⟨X, subset_refl _, hX, rfl⟩
  | succ d ih =>
    obtain ⟨y, -, hy⟩ := exists_mem_notMem_of_card_lt_card (s := X) (t := univ) (by rw [card_univ]; omega)
    obtain ⟨x⟩ := hX.nonempty
    obtain ⟨e, -, hu, hv⟩ := (hG.preconnected x.1 y).some.exists_boundary_dart (X : Set V) x.2 (by simpa using hy)
    have hY : (G.induce ((insert e.snd X : Finset V) : Set V)).Connected := by
      have h : ((insert e.snd X : Finset V) : Set V) = (X : Set V) ∪ {e.snd, e.fst} := by
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
      rw [h]
      exact induce_union_connected hX.preconnected (induce_pair_connected_of_adj e.adj.symm).preconnected
        ⟨e.fst, hu, by simp⟩
    have hc : (insert e.snd X).card = X.card + 1 := card_insert_of_notMem (by simpa using hv)
    obtain ⟨Y, hXY, hY', hYc⟩ := ih hY (by rw [hc]; omega) (by rw [hc]; omega)
    exact ⟨Y, (subset_insert _ X).trans hXY, hY', by rw [hYc, hc]; omega⟩

end Grow

open Turing Classical EthCor.Iso EthCor.ConnTM EthCor.ConnITM

/-- X meets every clause of φ. -/
def Meets {n : ℕ} (φ : Sat3.CNF n) (X : Finset (Fin n)) : Prop := ∀ C ∈ φ, ∃ l ∈ C, l.1 ∈ X

/-- For a positive φ, the count of `numConn` is positive iff a connected X of size ℓ meets φ. -/
theorem numConn_pos_iff {n : ℕ} (G : SimpleGraph (Fin n)) {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, ∀ l ∈ C, l.2 = true)
    (ℓ : ℕ) : 0 < numConn G φ ℓ ↔ ∃ X, Meets φ X ∧ X.card = ℓ ∧ (G.induce (X : Set (Fin n))).Connected := by
  unfold numConn
  rw [card_pos]
  constructor
  · rintro ⟨x, hx⟩
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hs, hc, hconn⟩ := hx
    have e : ((univ.filter fun v => x v = true : Finset (Fin n)) : Set (Fin n)) = {v | x v = true} := by
      ext v; simp
    refine ⟨univ.filter fun v => x v = true, fun C hC => ?_, by convert hc, by rw [e]; exact hconn⟩
    obtain ⟨l, hl, h⟩ := hs C hC
    exact ⟨l, hl, by simpa [hφ C hC l hl] using h⟩
  · rintro ⟨X, hm, hc, hconn⟩
    refine ⟨fun v => decide (v ∈ X), ?_⟩
    have e : ({v | decide (v ∈ X) = true} : Set (Fin n)) = (X : Set (Fin n)) := by ext v; simp
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun C hC => ?_, ?_, by rw [e]; exact hconn⟩
    · obtain ⟨l, hl, h⟩ := hm C hC
      exact ⟨l, hl, by simpa [hφ C hC l hl] using h⟩
    · convert hc using 2
      ext v; simp

/-- In a connected graph, a connected X with at most ℓ ≤ n vertices that meets a positive φ exists
iff the count of `numConn` for ℓ is positive. -/
theorem min_iff {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected) {φ : Sat3.CNF n}
    (hφ : ∀ C ∈ φ, ∀ l ∈ C, l.2 = true) {ℓ : ℕ} (hℓ : ℓ ≤ n) :
    (∃ X, Meets φ X ∧ X.card ≤ ℓ ∧ (G.induce (X : Set (Fin n))).Connected) ↔ 0 < numConn G φ ℓ := by
  rw [numConn_pos_iff G hφ]
  constructor
  · rintro ⟨X, hm, hc, hconn⟩
    obtain ⟨Y, hXY, hY, hYc⟩ := conn_grow hG hconn hc (by rw [Fintype.card_fin]; exact hℓ)
    exact ⟨Y, fun C hC => (hm C hC).imp fun l h => ⟨h.1, hXY h.2⟩, hYc, hY⟩
  · rintro ⟨X, hm, hc, hconn⟩
    exact ⟨X, hm, hc.le, hconn⟩

/-- **Minimum Steiner tree and minimum connected vertex cover with one-sided error in time
C·2^{εn}.** For every width r, exponent D, δ > 0 and ε > 0 there are k, t, n₀ and one Turing machine
with finite alphabets such that for every connected graph G on n ≥ n₀ vertices (of any density),
1 ≤ ℓ ≤ n and every positive CNF φ on the vertices with clauses of at most r literals and at most
(n+2)^D clauses: run on `codeCI G ℓ ω φ` for a seed ω, it halts within ⌊C·2^{εn}⌋ steps with one bit
out(ω); if no X with at most ℓ vertices meets φ and induces a connected subgraph, out(ω) = 0 for every
seed; if one does, out(ω) = 1 for at least a 2^{−δn} fraction of the seeds. -/
theorem min_conn_randomized (r D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), G.Connected → n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ r ∧ ∀ l ∈ C, l.2 = true) → φ.length ≤ (n + 2) ^ D →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCI G ℓ ω φ) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        ((¬∃ X, Meets φ X ∧ X.card ≤ ℓ ∧ (G.induce (X : Set (Fin n))).Connected) → ∀ ω, out ω = false) ∧
        ((∃ X, Meets φ X ∧ X.card ≤ ℓ ∧ (G.induce (X : Set (Fin n))).Connected) →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := conn_randomized r D hδ hε
  refine ⟨k, t, n₀, M, C, hfin, fun n ℓ G φ hG hn h1 h2 hr hm => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n ℓ G φ hn h1 h2 (fun C hC => (hr C hC).1) hm
  have hiff := min_iff hG (fun C hC => (hr C hC).2) h2
  exact ⟨out, hrun, fun h => hno (by rw [hiff] at h; omega), fun h => hyes (hiff.1 h)⟩

/-- **Minimum Group Steiner tree with one-sided error in time C·2^{εn}.** As `min_conn_randomized`,
for positive CNFs φ with clauses of any width (at most n literals) and at most D·n clauses, with the
machine of `PosTM.pos_randomized`. -/
theorem min_pos_randomized (D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), G.Connected → n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ n ∧ ∀ l ∈ C, l.2 = true) → φ.length ≤ D * n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCI G ℓ ω φ) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        ((¬∃ X, Meets φ X ∧ X.card ≤ ℓ ∧ (G.induce (X : Set (Fin n))).Connected) → ∀ ω, out ω = false) ∧
        ((∃ X, Meets φ X ∧ X.card ≤ ℓ ∧ (G.induce (X : Set (Fin n))).Connected) →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := PosTM.pos_randomized D hδ hε
  refine ⟨k, t, n₀, M, C, hfin, fun n ℓ G φ hG hn h1 h2 hr hm => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n ℓ G φ hn h1 h2 hr hm
  have hiff := min_iff hG (fun C hC => (hr C hC).2) h2
  exact ⟨out, hrun, fun h => hno (by rw [hiff] at h; omega), fun h => hyes (hiff.1 h)⟩

end EthCor.MinTM
