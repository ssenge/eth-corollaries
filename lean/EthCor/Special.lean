import EthCor.HomTM
import EthCor.PottsTM

/-! # Special cases of N5 and N3

* **Independent sets** (`numHom_hInd`, `indep_subexp`): the homomorphisms to the relation hInd on
  {0, 1}, an edge 01 with a loop at 0, are the indicator maps of the independent sets of G (Mathlib's
  `IsIndepSet`). So the machine of N5 counts them within 2^{εn} steps, for graphs of any density.
* **Max-Cut and the Ising model** (`pottsSpec_two`, `maxcut_spectrum`, `ising_spectrum`): with q = 2
  colors, the colorings with j monochromatic edges are the vertex sets S whose cut has m − j edges,
  and the spin configurations with Σ_{uv ∈ E} s_u·s_v = 2j − m. So the machine of N3 outputs the
  Max-Cut spectrum and the density of states of the ±1 Ising model on graphs with O(n) edges.
* **Chromatic polynomial** (`pottsSpec_zero`, `chromatic_tutte`): N₀ is the number of proper
  q-colorings in Mathlib's sense, and N₀ = (−q)^{k(E)}·(−1)^n·T(G; 1−q, 0).
* **The point (0, 1 − q)** (`flow_tutte`): (−1)^{k(E)}·(−q)^n·T(G; 0, 1−q) = Σ_j N_j·(1−q)^j. By
  Tutte's classical theorem, (−1)^{m−n+k(E)}·T(G; 0, 1−q) is the number of nowhere-zero ℤ_q-flows of
  G (the flow polynomial at q); that identity is not formalized here. -/

namespace EthCor.Special

open Finset SimpleGraph EthCor.Potts GraphProblems Turing

variable {n : ℕ}

/-! ### Independent sets -/

/-- The relation on {0, 1} that is false only at (1, 1): an edge 01 with a loop at 0. -/
def hInd : Fin 2 → Fin 2 → Bool := fun a c => !(decide (a = 1) && decide (c = 1))

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

open Classical in
/-- **Independent sets as homomorphisms.** The maps V(G) → {0, 1} that send every edge into hInd are
the indicator maps of the independent sets of G. -/
theorem numHom_hInd (G : SimpleGraph (Fin n)) :
    Hom.numHom G hInd = (univ.filter fun S : Finset (Fin n) => G.IsIndepSet (S : Set (Fin n))).card := by
  rw [Hom.numHom, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun f => ⟨univ.filter fun v => f.1 v = 1, ?_⟩
      invFun := fun S => ⟨fun v => if v ∈ S.1 then 1 else 0, ?_⟩
      left_inv := fun f => ?_
      right_inv := fun S => ?_ }
  · intro u hu v hv _ huv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
    have := f.2 u v huv
    simp [hInd, hu, hv] at this
  · intro u v huv
    have hS := (isIndepSet_iff G).1 S.2
    by_cases hu : u ∈ S.1 <;> by_cases hv : v ∈ S.1
    · exact absurd huv (hS (by simpa using hu) (by simpa using hv) (G.ne_of_adj huv))
    all_goals simp [hInd, hu, hv]
  · apply Subtype.ext; funext v
    simp only [mem_filter, mem_univ, true_and]
    rcases fin2_cases (f.1 v) with h | h <;> simp [h]
  · apply Subtype.ext; ext v
    simp only [mem_filter, mem_univ, true_and]
    by_cases hv : v ∈ S.1 <;> simp [hv]

open Classical in
/-- **Counting independent sets in 2^{εn}.** The machine of N5, run on h = 2, the matrix of hInd and
a graph G on n vertices of any density, outputs the number of independent sets of G (Mathlib's
`IsIndepSet`) within ⌊2^{εn}⌋ steps, for every ε > 0 and n ≥ n₀(ε). -/
theorem indep_subexp : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      Wrap.Outputs M (unary 2 ++ (Hom.hmat hInd ++ code G))
        (Nat.bits (univ.filter fun S : Finset (Fin n) => G.IsIndepSet (S : Set (Fin n))).card)
        ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, hfin, hM⟩ := Hom.hom_subexp
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hM (1 / 12) ε (by norm_num) (by norm_num) hε
  refine ⟨n₀ + 2, fun n G hn => ?_⟩
  have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by norm_cast; omega), Real.rpow_one]
    exact_mod_cast (show 2 ≤ n by omega)
  have hlog : Real.logb 2 (2 : ℕ) ≤ Real.logb 2 n ^ (1 / 6 - 1 / 12 : ℝ) := by
    rw [Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two]
    exact Real.one_le_rpow h1 (by norm_num)
  have := hn₀ n 2 G hInd (by omega) le_rfl hlog
  rwa [numHom_hInd] at this

/-! ### Max-Cut and the Ising model -/

open Classical in
/-- The number of edges of G with exactly one end in S. -/
noncomputable def cutSize (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (G.edgeFinset.filter fun e => ∃ u ∈ S, ∃ v ∉ S, e = s(u, v)).card

/-- The coloring with color 1 on S and 0 elsewhere. -/
def ind (S : Finset (Fin n)) : Fin n → Fin 2 := fun v => if v ∈ S then 1 else 0

theorem ind_eq_iff {S : Finset (Fin n)} {u v : Fin n} : ind S u = ind S v ↔ (u ∈ S ↔ v ∈ S) := by
  unfold ind; by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

theorem diag_iff_not_cut (S : Finset (Fin n)) (e : Sym2 (Fin n)) :
    (e.map (ind S)).IsDiag ↔ ¬ ∃ u ∈ S, ∃ v ∉ S, e = s(u, v) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff, ind_eq_iff]
    constructor
    · rintro h ⟨u, hu, v, hv, he⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hv (h.1 hu)
      · exact hv (h.2 hu)
    · intro h
      by_contra hab
      apply h
      by_cases ha : a ∈ S
      · exact ⟨a, ha, b, fun hb => hab ⟨fun _ => hb, fun _ => ha⟩, rfl⟩
      · have hb : b ∈ S := by by_contra hb; exact hab ⟨fun h => absurd h ha, fun h => absurd h hb⟩
        exact ⟨b, hb, a, ha, Sym2.eq_swap⟩

open Classical in
theorem cut_add_mono (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    cutSize G S + mono G (ind S) = G.edgeFinset.card := by
  rw [cutSize, mono, filter_congr (fun e _ => diag_iff_not_cut S e)]
  exact card_filter_add_card_filter_not _

open Classical in
/-- **q = 2: cuts.** The colorings with two colors and j monochromatic edges correspond to the vertex
sets whose cut has m − j edges. -/
theorem pottsSpec_two (G : SimpleGraph (Fin n)) (j : ℕ) :
    pottsSpec G 2 j = (univ.filter fun S : Finset (Fin n) => cutSize G S + j = G.edgeFinset.card).card := by
  rw [pottsSpec]
  refine card_nbij' (fun σ => univ.filter fun v => σ v = 1) ind ?_ ?_ ?_ ?_
  · intro σ hσ
    have hσ' : ind (univ.filter fun v => σ v = 1) = σ := by
      funext v; unfold ind; rcases fin2_cases (σ v) with h | h <;> simp [h]
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    have := cut_add_mono G (univ.filter fun v => σ v = 1)
    rw [hσ', hσ] at this
    exact this
  · intro S hS
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    have := cut_add_mono G S
    omega
  · intro σ _
    funext v; unfold ind; simp only [mem_filter, mem_univ, true_and]
    rcases fin2_cases (σ v) with h | h <;> simp [h]
  · intro S _
    ext v; unfold ind; by_cases hv : v ∈ S <;> simp [hv]

open Classical in
/-- **The Max-Cut spectrum on sparse graphs.** For every density D and δ > 0, one machine, given a
graph G on n vertices with m ≤ D·n edges and j ≤ m in unary, outputs the number of vertex sets S
with a cut of m − j edges, within C·2^{δn} steps. -/
theorem maxcut_spectrum (D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n j : ℕ) (G : SimpleGraph (Fin n)), G.edgeFinset.card ≤ D * n → j ≤ G.edgeFinset.card →
      Wrap.Outputs M (code G ++ unary j)
        (Nat.bits (univ.filter fun S : Finset (Fin n) => cutSize G S + j = G.edgeFinset.card).card)
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M, C, hfin, hM⟩ := PottsTM.potts_spectrum 2 D (by norm_num) hδ
  refine ⟨M, C, hfin, fun n j G hm hj => ?_⟩
  have := hM n j G hm hj
  rwa [pottsSpec_two] at this

/-- The spin of a vertex: +1 for color 0, −1 for color 1. -/
def spin (σ : Fin n → Fin 2) (v : Fin n) : ℤ := if σ v = 0 then 1 else -1

/-- The product of the spins at the two ends of an edge. -/
def spinProd (σ : Fin n → Fin 2) (e : Sym2 (Fin n)) : ℤ :=
  Sym2.lift ⟨fun u v => spin σ u * spin σ v, fun _ _ => mul_comm _ _⟩ e

open Classical in
/-- The Ising sum Σ_{uv ∈ E} s_u·s_v. -/
noncomputable def isingSum (G : SimpleGraph (Fin n)) (σ : Fin n → Fin 2) : ℤ :=
  ∑ e ∈ G.edgeFinset, spinProd σ e

theorem spinProd_eq (σ : Fin n → Fin 2) (e : Sym2 (Fin n)) :
    spinProd σ e = if (e.map σ).IsDiag then 1 else -1 := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [spinProd, Sym2.lift_mk, Sym2.map_mk, Sym2.mk_isDiag_iff, spin]
    rcases fin2_cases (σ a) with ha | ha <;> rcases fin2_cases (σ b) with hb | hb <;> simp [ha, hb]

open Classical in
theorem isingSum_eq (G : SimpleGraph (Fin n)) (σ : Fin n → Fin 2) :
    isingSum G σ = 2 * (mono G σ : ℤ) - G.edgeFinset.card := by
  have h := card_filter_add_card_filter_not (s := G.edgeFinset) (fun e => (e.map σ).IsDiag)
  have h1 : ∑ e ∈ G.edgeFinset.filter (fun e => (e.map σ).IsDiag), spinProd σ e =
      ∑ e ∈ G.edgeFinset.filter (fun e => (e.map σ).IsDiag), (1 : ℤ) :=
    sum_congr rfl fun e he => by rw [spinProd_eq, if_pos (mem_filter.1 he).2]
  have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬ (e.map σ).IsDiag), spinProd σ e =
      ∑ e ∈ G.edgeFinset.filter (fun e => ¬ (e.map σ).IsDiag), (-1 : ℤ) :=
    sum_congr rfl fun e he => by rw [spinProd_eq, if_neg (mem_filter.1 he).2]
  rw [isingSum, ← sum_filter_add_sum_filter_not G.edgeFinset (fun e => (e.map σ).IsDiag), h1, h2, mono]
  simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  linarith

open Classical in
/-- **The density of states of the ±1 Ising model.** The spin configurations with Ising sum
2j − m are N_j for q = 2. -/
theorem ising_spectrum (G : SimpleGraph (Fin n)) (j : ℕ) :
    (univ.filter fun σ : Fin n → Fin 2 => isingSum G σ = 2 * (j : ℤ) - G.edgeFinset.card).card =
      pottsSpec G 2 j := by
  rw [pottsSpec]
  congr 1; ext σ
  simp only [mem_filter, mem_univ, true_and, isingSum_eq]
  omega

/-! ### The chromatic polynomial and the point (0, 1 − q) -/

open Classical in
/-- **N₀ is the number of proper colorings** (Mathlib's `G.Coloring (Fin q)`). -/
theorem pottsSpec_zero (G : SimpleGraph (Fin n)) (q : ℕ) : pottsSpec G q 0 = numColorings G q := by
  rw [pottsSpec, numColorings, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr
    { toFun := fun φ => ⟨φ, ?_⟩
      invFun := fun σ => ⟨σ.1, fun {u v} huv => ?_⟩
      left_inv := fun φ => rfl
      right_inv := fun σ => rfl }
  · rw [mono, card_eq_zero, filter_eq_empty_iff]
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      exact (top_adj _ _).1 (φ.map_rel he)
  · have h := σ.2
    rw [mono, card_eq_zero, filter_eq_empty_iff] at h
    have := h (mem_edgeFinset.2 (G.mem_edgeSet.2 huv))
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff] at this
    exact (top_adj _ _).2 this

theorem sum_zero_pow {K : Type} [Field K] (m : ℕ) (N : ℕ → ℕ) :
    ∑ j ∈ range (m + 1), (N j : K) * (0 : K) ^ j = N 0 := by
  rw [sum_range_succ']
  simp

open Classical in
/-- **The chromatic polynomial on the hyperbola.** For q ≥ 1, the number of proper q-colorings is
(−q)^{k(E)}·(−1)^n·T(G; 1−q, 0), the classical form of the chromatic polynomial. -/
theorem chromatic_tutte (G : SimpleGraph (Fin n)) (q : ℕ) (hq : 1 ≤ q) :
    (numColorings G q : ℚ) = (-(q : ℚ)) ^ comps G.edgeFinset * (-1) ^ n * Potts.tutte G (1 - (q : ℚ)) 0 := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h := tutte_hyperbola (K := ℚ) G q (x := 1 - q) (y := 0) (by intro h; apply hq'; linarith)
    zero_ne_one (by ring)
  rw [sum_zero_pow, pottsSpec_zero] at h
  rw [← h]; ring_nf

open Classical in
/-- **The point (0, 1 − q).** For q ≥ 1, (−1)^{k(E)}·(−q)^n·T(G; 0, 1−q) = Σ_j N_j·(1−q)^j, so the
spectrum of N3 gives T(G; 0, 1−q), which is ± the flow polynomial at q by Tutte's theorem. -/
theorem flow_tutte (G : SimpleGraph (Fin n)) (q : ℕ) (hq : 1 ≤ q) :
    (-1 : ℚ) ^ comps G.edgeFinset * (-(q : ℚ)) ^ n * Potts.tutte G (0 : ℚ) (1 - q) =
      ∑ j ∈ range (G.edgeFinset.card + 1), (pottsSpec G q j : ℚ) * (1 - q) ^ j := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [← tutte_hyperbola (K := ℚ) G q (x := 0) (y := 1 - q) zero_ne_one.symm.symm
    (by intro h; apply hq'; linarith) (by ring)]
  ring_nf

end EthCor.Special
