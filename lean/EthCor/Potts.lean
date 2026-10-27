import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # The q-state Potts model, the random-cluster expansion and the Tutte polynomial

For a graph G on Fin n and q colors, `pottsSpec G q j` is the number of colorings σ : Fin n → Fin q
with exactly j monochromatic edges (the density of states of the Potts model). The Potts partition
function is Σ_σ y^{mono σ} = Σ_j N_j·y^j.

The Fortuin–Kasteleyn identity (`potts_fk`): for every v in a commutative ring,
Σ_j N_j·(1+v)^j = Σ_{A ⊆ E} q^{k(A)}·v^{|A|}, with k(A) the number of connected components of the
graph (Fin n, A) (`comps A`). Expanding Π_e (1 + v·[e monochromatic]) gives the right side; the
colorings that are constant on the components of A are q^{k(A)} many (`card_const`).

The Tutte polynomial is T(G; x, y) = Σ_{A ⊆ E} (x−1)^{k(A)−k(E)}·(y−1)^{|A|+k(A)−n} (`tutte`, the
rank-generating function with r(A) = n − k(A)). On the hyperbola (x−1)(y−1) = q, with x, y ≠ 1,
(x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j (`tutte_hyperbola`). So the spectrum (N_j)_j gives T
on every hyperbola (x−1)(y−1) = q with q a positive integer; for example the chromatic polynomial
at q (the point (1−q, 0)) and the flow polynomial at q (the point (0, 1−q)). -/

namespace EthCor.Potts

open SimpleGraph Finset

variable {n : ℕ}

open Classical in
/-- The number of edges of G whose two ends σ colors alike. -/
noncomputable def mono (G : SimpleGraph (Fin n)) {q : ℕ} (σ : Fin n → Fin q) : ℕ :=
  (G.edgeFinset.filter fun e => (e.map σ).IsDiag).card

open Classical in
/-- **The Potts density of states:** the number of colorings with q colors and exactly j
monochromatic edges. -/
noncomputable def pottsSpec (G : SimpleGraph (Fin n)) (q j : ℕ) : ℕ :=
  (univ.filter fun σ : Fin n → Fin q => mono G σ = j).card

open Classical in
/-- The number of connected components of the graph on Fin n with edge set A. -/
noncomputable def comps (A : Finset (Sym2 (Fin n))) : ℕ :=
  Fintype.card (fromEdgeSet (A : Set (Sym2 (Fin n)))).ConnectedComponent

open Classical in
/-- The random-cluster form of the Potts partition function, Σ_{A ⊆ E} q^{k(A)}·v^{|A|}. -/
noncomputable def fk {R : Type} [CommRing R] (G : SimpleGraph (Fin n)) (q : ℕ) (v : R) : R :=
  ∑ A ∈ G.edgeFinset.powerset, (q : R) ^ comps A * v ^ A.card

open Classical in
/-- **The Tutte polynomial**, T(G; x, y) = Σ_{A ⊆ E} (x−1)^{k(A)−k(E)}·(y−1)^{|A|+k(A)−n}, evaluated
in a field. The exponents are r(E) − r(A) and |A| − r(A) for the rank r(A) = n − k(A). -/
noncomputable def tutte {K : Type} [Field K] (G : SimpleGraph (Fin n)) (x y : K) : K :=
  ∑ A ∈ G.edgeFinset.powerset,
    (x - 1) ^ ((comps A : ℤ) - comps G.edgeFinset) * (y - 1) ^ ((A.card : ℤ) + comps A - n)

/-! ### Colorings constant on the components -/

/-- A coloring that agrees on the ends of every edge is constant along walks. -/
theorem const_walk {V β : Type} {H : SimpleGraph V} {σ : V → β} (hσ : ∀ u v, H.Adj u v → σ u = σ v) :
    ∀ {u v : V} (_ : H.Walk u v), σ u = σ v
  | _, _, .nil => rfl
  | _, _, .cons h p => (hσ _ _ h).trans (const_walk hσ p)

/-- The colorings that agree on the ends of every edge are the colorings of the components. -/
theorem card_const_adj {V β : Type} [Fintype V] [DecidableEq V] [Fintype β] (H : SimpleGraph V)
    [Fintype H.ConnectedComponent] [DecidablePred fun σ : V → β => ∀ u v, H.Adj u v → σ u = σ v] :
    (univ.filter fun σ : V → β => ∀ u v, H.Adj u v → σ u = σ v).card =
      Fintype.card β ^ Fintype.card H.ConnectedComponent := by
  classical
  rw [← Fintype.card_fun, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun σ => ConnectedComponent.lift σ.1 fun v w p _ => const_walk σ.2 p
      invFun := fun f => ⟨fun v => f (H.connectedComponentMk v), fun u v h =>
        congrArg f (ConnectedComponent.eq.2 h.reachable)⟩
      left_inv := fun σ => by ext v; rfl
      right_inv := fun f => by funext c; induction c using ConnectedComponent.ind; rfl }

open Classical in
/-- **The colorings constant on the components of A are q^{k(A)} many.** -/
theorem card_const (q : ℕ) (A : Finset (Sym2 (Fin n))) :
    (univ.filter fun σ : Fin n → Fin q => ∀ e ∈ A, (e.map σ).IsDiag).card = q ^ comps A := by
  have h := card_const_adj (β := Fin q) (fromEdgeSet (A : Set (Sym2 (Fin n))))
  rw [Fintype.card_fin] at h
  rw [comps, ← h]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, fromEdgeSet_adj, Finset.mem_coe]
  constructor
  · intro hσ u v ⟨huv, _⟩
    have := hσ _ huv
    rwa [Sym2.map_mk, Sym2.mk_isDiag_iff] at this
  · intro hσ e he
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      by_cases huv : u = v
      · rw [huv]
      · exact hσ u v ⟨he, huv⟩

/-! ### The Fortuin–Kasteleyn identity -/

open Classical in
theorem prod_mono {R : Type} [CommRing R] (G : SimpleGraph (Fin n)) {q : ℕ} (σ : Fin n → Fin q) (v : R) :
    (1 + v) ^ mono G σ = ∏ e ∈ G.edgeFinset, (v * (if (e.map σ).IsDiag then 1 else 0) + 1) := by
  have : ∀ e ∈ G.edgeFinset, v * (if (e.map σ).IsDiag then 1 else 0) + 1 =
      if (e.map σ).IsDiag then 1 + v else 1 := fun e _ => by split_ifs <;> ring
  rw [prod_congr rfl this, prod_ite, prod_const, prod_const_one, mul_one, mono]

open Classical in
/-- Σ_σ (1+v)^{mono σ} = Σ_{A ⊆ E} q^{k(A)}·v^{|A|}. -/
theorem sum_mono {R : Type} [CommRing R] (G : SimpleGraph (Fin n)) (q : ℕ) (v : R) :
    ∑ σ : Fin n → Fin q, (1 + v) ^ mono G σ = fk G q v := by
  simp_rw [prod_mono, prod_add, prod_const_one, mul_one, prod_mul_distrib, prod_const, prod_boole]
  rw [sum_comm, fk]
  refine sum_congr rfl fun A _ => ?_
  rw [← mul_sum, mul_comm]
  congr 1
  rw [← Nat.cast_pow, ← card_const q A, natCast_card_filter]
  exact sum_congr rfl fun σ _ => by split_ifs <;> simp_all

open Classical in
/-- **The Fortuin–Kasteleyn identity:** Σ_j N_j·(1+v)^j = Σ_{A ⊆ E} q^{k(A)}·v^{|A|}. -/
theorem potts_fk {R : Type} [CommRing R] (G : SimpleGraph (Fin n)) (q : ℕ) (v : R) :
    ∑ j ∈ range (G.edgeFinset.card + 1), (pottsSpec G q j : R) * (1 + v) ^ j = fk G q v := by
  rw [← sum_mono]
  have hmaps : ∀ σ ∈ (univ : Finset (Fin n → Fin q)), mono G σ ∈ range (G.edgeFinset.card + 1) :=
    fun σ _ => mem_range.2 (Nat.lt_succ_of_le (card_filter_le _ _))
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun j _ => ?_
  rw [pottsSpec, ← nsmul_eq_mul, ← sum_const]
  exact sum_congr rfl fun σ hσ => by rw [(mem_filter.1 hσ).2]

/-! ### The Tutte polynomial on the hyperbolas (x−1)(y−1) = q -/

open Classical in
/-- **The Tutte polynomial from the Potts spectrum.** If (x−1)(y−1) = q with x, y ≠ 1, then
(x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j. -/
theorem tutte_hyperbola {K : Type} [Field K] (G : SimpleGraph (Fin n)) (q : ℕ) {x y : K} (hx : x ≠ 1)
    (hy : y ≠ 1) (hq : (x - 1) * (y - 1) = q) :
    (x - 1) ^ comps G.edgeFinset * (y - 1) ^ n * tutte G x y =
      ∑ j ∈ range (G.edgeFinset.card + 1), (pottsSpec G q j : K) * y ^ j := by
  have hx' : x - 1 ≠ 0 := sub_ne_zero.2 hx
  have hy' : y - 1 ≠ 0 := sub_ne_zero.2 hy
  have e := potts_fk G q (y - 1)
  rw [add_sub_cancel] at e
  rw [e, fk, tutte, mul_sum]
  refine sum_congr rfl fun A _ => ?_
  rw [← zpow_natCast (x - 1), ← zpow_natCast (y - 1)]
  calc (x - 1) ^ (comps G.edgeFinset : ℤ) * (y - 1) ^ (n : ℤ) *
        ((x - 1) ^ ((comps A : ℤ) - comps G.edgeFinset) * (y - 1) ^ ((A.card : ℤ) + comps A - n))
      = ((x - 1) ^ (comps G.edgeFinset : ℤ) * (x - 1) ^ ((comps A : ℤ) - comps G.edgeFinset)) *
        ((y - 1) ^ (n : ℤ) * (y - 1) ^ ((A.card : ℤ) + comps A - n)) := by ring
    _ = (x - 1) ^ ((comps A : ℕ) : ℤ) * (y - 1) ^ (((comps A + A.card : ℕ)) : ℤ) := by
        rw [← zpow_add₀ hx', ← zpow_add₀ hy']; congr 2 <;> push_cast <;> ring
    _ = ((x - 1) * (y - 1)) ^ comps A * (y - 1) ^ A.card := by
        rw [zpow_natCast, zpow_natCast, pow_add, mul_pow]; ring
    _ = (q : K) ^ comps A * (y - 1) ^ A.card := by rw [hq]

end EthCor.Potts
