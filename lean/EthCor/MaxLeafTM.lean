import EthCor.LeafTree
import EthCor.CdsIsoTM

/-! # Max Leaf Spanning Tree and minimum connected dominating set with one-sided error

The machine of `EthCor.CdsITM.cds_randomized`, run on `codeCD G ℓ ω`, answers whether G has a
connected dominating set with ℓ vertices. `numCDS_pos_iff` states this count in terms of
`EthCor.Leaf.IsCDS`. With `Leaf.cds_le_iff` the same run decides whether some connected dominating
set has at most ℓ vertices (`mincds_randomized`), and with `Leaf.leaf_iff`, for ℓ = n − L, whether G
has a spanning tree with at least L leaves (`maxleaf_randomized`). The graph may be dense. -/

namespace EthCor.MaxLeafTM

open Finset GraphProblems Turing EthCor.Iso EthCor.CdsTM EthCor.CdsITM EthCor.Leaf

/-- The count of `numCDS` is positive iff a connected dominating set of size ℓ exists. -/
theorem numCDS_pos_iff {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) :
    0 < numCDS G ℓ ↔ ∃ X, IsCDS G X ∧ X.card = ℓ := by
  classical
  unfold numCDS
  rw [card_pos]
  constructor
  · rintro ⟨x, hx⟩
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hd, hc, hconn⟩ := hx
    have e : ((univ.filter fun v => x v = true : Finset (Fin n)) : Set (Fin n)) = {v | x v = true} := by
      ext v; simp
    refine ⟨univ.filter fun v => x v = true, ⟨fun v => ?_, by rw [e]; exact hconn⟩, by convert hc⟩
    rcases hd v with h | ⟨u, hu, h⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨u, by simpa using hu, h⟩
  · rintro ⟨X, ⟨hd, hconn⟩, hc⟩
    refine ⟨fun v => decide (v ∈ X), ?_⟩
    have e : ({v | decide (v ∈ X) = true} : Set (Fin n)) = (X : Set (Fin n)) := by ext v; simp
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun v => ?_, ?_, by rw [e]; exact hconn⟩
    · rcases hd v with h | ⟨u, hu, h⟩
      · exact Or.inl (by simpa using h)
      · exact Or.inr ⟨u, by simpa using hu, h⟩
    · convert hc using 2
      ext v; simp

open Classical in
/-- **Minimum connected dominating set with one-sided error in time C·2^{εn}.** For every δ > 0 and
ε > 0 there are k, t, n₀ and one Turing machine with finite alphabets such that for every graph G on
n ≥ n₀ vertices (of any density) and 1 ≤ ℓ ≤ n, run on `codeCD G ℓ ω` for a seed ω it halts within
⌊C·2^{εn}⌋ steps with one bit out(ω); if G has no connected dominating set with at most ℓ vertices,
out(ω) = 0 for every seed; if it has one, out(ω) = 1 for at least a 2^{−δn} fraction of the seeds. -/
theorem mincds_randomized {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCD G ℓ ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        ((¬∃ X, IsCDS G X ∧ X.card ≤ ℓ) → ∀ ω, out ω = false) ∧
        ((∃ X, IsCDS G X ∧ X.card ≤ ℓ) →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := cds_randomized hδ hε
  refine ⟨k, t, n₀, M, C, hfin, fun n ℓ G hn h1 h2 => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n ℓ G hn h1 h2
  have hiff : (∃ X, IsCDS G X ∧ X.card ≤ ℓ) ↔ 0 < numCDS G ℓ := by
    rw [numCDS_pos_iff, cds_le_iff (by rw [Fintype.card_fin]; exact h2)]
  refine ⟨out, hrun, fun h => hno (by rw [hiff] at h; omega), fun h => hyes (hiff.1 h)⟩

open Classical in
/-- **Max Leaf Spanning Tree with one-sided error in time C·2^{εn}.** For every δ > 0 and ε > 0
there are k, t, n₀ and one Turing machine with finite alphabets such that for every graph G on
n ≥ n₀ vertices (of any density) and 1 ≤ L < n, run on `codeCD G (n − L) ω` for a seed ω it halts
within ⌊C·2^{εn}⌋ steps with one bit out(ω); if G has no spanning tree (a subgraph T ≤ G with
Mathlib's `IsTree`) with at least L leaves, out(ω) = 0 for every seed; if it has one, out(ω) = 1
for at least a 2^{−δn} fraction of the seeds. -/
theorem maxleaf_randomized {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n L : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → 1 ≤ L → L < n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCD G (n - L) ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        ((¬∃ T ≤ G, T.IsTree ∧ L ≤ (leaves T).card) → ∀ ω, out ω = false) ∧
        ((∃ T ≤ G, T.IsTree ∧ L ≤ (leaves T).card) →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := cds_randomized hδ hε
  refine ⟨k, t, max n₀ 3, M, C, hfin, fun n L G hn h1 h2 => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n (n - L) G (le_of_max_le_left hn) (by omega) (by omega)
  have hiff : (∃ T ≤ G, T.IsTree ∧ L ≤ (leaves T).card) ↔ 0 < numCDS G (n - L) := by
    rw [numCDS_pos_iff, leaf_iff (by rw [Fintype.card_fin]; exact le_of_max_le_right hn)
      (by rw [Fintype.card_fin]; exact h2), Fintype.card_fin]
  refine ⟨out, hrun, fun h => hno (by rw [hiff] at h; omega), fun h => hyes (hiff.1 h)⟩

end EthCor.MaxLeafTM
