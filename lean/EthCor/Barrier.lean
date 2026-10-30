import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination

/-!
# A barrier for Cut & Count with few colors

A coloring `s : X → {1, …, q}` that is constant on the edges of `G[X]` is one color per component
of `G[X]`. With color weights `x₁, …, x_q` shared by all vertices, the set `X` contributes
`∏_C p_{|C|}(x)` to the count, where `p_k = x₁^k + ⋯ + x_q^k` is the power sum. If a root `r ∈ X`
has its color fixed to `a`, it contributes `x_a^{|C_r|} ∏_{C ≠ C_r} p_{|C|}(x)`. A connected set of
size `ℓ` contributes `p_ℓ`, resp. `x_a^ℓ`.

For `ℓ > q` both are rational combinations of the contributions of disconnected sets of size `ℓ`
(`psum_mem`, `pow_mem`), by Newton's identities and Vieta's formulas. So a rational linear map that
is zero on every disconnected pattern is zero on the connected one (`barrier`, `barrier_rooted`):
separating the connected sets of size `ℓ` needs `q ≥ ℓ` colors, i.e. `⌈lg ℓ⌉` bits per vertex.
Counting modulo 2 is not rational, which is how Cut & Count gets parities with `q = 2`.
-/

namespace EthCor.Barrier

open MvPolynomial Finset

variable {q ℓ : ℕ}

/-- Products `p_{μ₁} ⋯ p_{μ_r}` of power sums in `q` variables with positive degrees summing to `k`
and at least `m` factors: the contribution of a set with components of sizes `μ`. -/
def Prods (q k m : ℕ) : Set (MvPolynomial (Fin q) ℚ) :=
  {f | ∃ μ : Multiset ℕ, (∀ i ∈ μ, 0 < i) ∧ μ.sum = k ∧ m ≤ Multiset.card μ ∧
    f = (μ.map (psum (Fin q) ℚ)).prod}

/-- `x_a^c p_{μ₁} ⋯ p_{μ_r}` with `c ≥ 1`, `r ≥ 1` and degree `k`: a disconnected set whose root
component has `c` vertices and color `a`. -/
def RProds (q : ℕ) (a : Fin q) (k : ℕ) : Set (MvPolynomial (Fin q) ℚ) :=
  {f | ∃ c : ℕ, ∃ μ : Multiset ℕ, 1 ≤ c ∧ (∀ i ∈ μ, 0 < i) ∧ c + μ.sum = k ∧
    1 ≤ Multiset.card μ ∧ f = X a ^ c * (μ.map (psum (Fin q) ℚ)).prod}

lemma prods_mono {k m m' : ℕ} (h : m' ≤ m) : Prods q k m ⊆ Prods q k m' := by
  rintro _ ⟨μ, hpos, hsum, hcard, rfl⟩
  exact ⟨μ, hpos, hsum, h.trans hcard, rfl⟩

/-- Positive degree means at least one factor. -/
lemma prods_one {k : ℕ} (hk : 0 < k) : Prods q k 0 ⊆ Prods q k 1 := by
  rintro _ ⟨μ, hpos, hsum, -, rfl⟩
  refine ⟨μ, hpos, hsum, Multiset.card_pos.2 ?_, rfl⟩
  rintro rfl
  simp at hsum
  omega

lemma neg_one_pow_mul_mem {M : Submodule ℚ (MvPolynomial (Fin q) ℚ)} {f : MvPolynomial (Fin q) ℚ}
    (n : ℕ) (hf : f ∈ M) : (-1) ^ n * f ∈ M := by
  rcases neg_one_pow_eq_or (MvPolynomial (Fin q) ℚ) n with h | h <;> rw [h]
  · simpa using hf
  · simpa using M.neg_mem hf

lemma mul_psum_mem {i m j : ℕ} {f : MvPolynomial (Fin q) ℚ}
    (hf : f ∈ Submodule.span ℚ (Prods q i m)) (hj : 0 < j) :
    f * psum (Fin q) ℚ j ∈ Submodule.span ℚ (Prods q (i + j) (m + 1)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨μ, hpos, hsum, hcard, rfl⟩ := hg
    refine Submodule.subset_span ⟨j ::ₘ μ, fun x hx => ?_, ?_, ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hx with rfl | hx
      exacts [hj, hpos x hx]
    · rw [Multiset.sum_cons, hsum, add_comm]
    · rw [Multiset.card_cons]
      omega
    · rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

lemma xpow_mul_mem {a : Fin q} {c i : ℕ} {f : MvPolynomial (Fin q) ℚ}
    (hf : f ∈ Submodule.span ℚ (Prods q i 1)) (hc : 1 ≤ c) :
    X a ^ c * f ∈ Submodule.span ℚ (RProds q a (c + i)) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨μ, hpos, hsum, hcard, rfl⟩ := hg
    exact Submodule.subset_span ⟨c, μ, hc, hpos, by rw [hsum], hcard, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

/-- `e_k` is a rational combination of products of power sums of total degree `k` (Newton). -/
theorem esymm_mem (k : ℕ) : esymm (Fin q) ℚ k ∈ Submodule.span ℚ (Prods q k 0) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · rw [esymm_zero]
    exact Submodule.subset_span ⟨0, by simp, by simp, le_rfl, by simp⟩
  · have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
    have he : esymm (Fin q) ℚ (k + 1) = ((k + 1 : ℕ) : ℚ)⁻¹ •
        (((k + 1 : ℕ) : MvPolynomial (Fin q) ℚ) * esymm (Fin q) ℚ (k + 1)) := by
      rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [he, mul_esymm_eq_sum]
    refine Submodule.smul_mem _ _ (neg_one_pow_mul_mem _ (Submodule.sum_mem _ fun a ha => ?_))
    obtain ⟨ha, hlt⟩ := Finset.mem_filter.1 ha
    rw [Finset.mem_antidiagonal] at ha
    rw [mul_assoc]
    refine neg_one_pow_mul_mem _ ?_
    have h := mul_psum_mem (ih a.1 hlt) (j := a.2) (by omega)
    rw [ha] at h
    exact Submodule.span_mono (prods_mono (Nat.zero_le _)) h

/-- Each variable is a root of `∏_b (T − x_b)`, so for `ℓ > q`:
`x_a^ℓ = −∑_{j=1}^{q} (−1)^j e_j x_a^{ℓ−j}`. -/
theorem pow_eq (hq : q < ℓ) (a : Fin q) :
    (X a : MvPolynomial (Fin q) ℚ) ^ ℓ =
      -∑ j ∈ range q, (-1) ^ (j + 1) * (esymm (Fin q) ℚ (j + 1) * X a ^ (ℓ - (j + 1))) := by
  have h0 := congrArg (Polynomial.eval (X a : MvPolynomial (Fin q) ℚ))
    (Multiset.prod_X_sub_X_eq_sum_esymm (univ.val.map (X : Fin q → MvPolynomial (Fin q) ℚ)))
  rw [Polynomial.eval_multiset_prod, Multiset.map_map,
    Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨X a, Multiset.mem_map.2 ⟨a, mem_univ_val a, rfl⟩,
      by simp⟩), Polynomial.eval_finsetSum] at h0
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, Multiset.card_map, card_val, card_univ,
    Fintype.card_fin, ← esymm_eq_multiset_esymm] at h0
  rw [sum_range_succ'] at h0
  simp only [pow_zero, esymm_zero, one_mul, Nat.sub_zero] at h0
  have hsum : ∑ j ∈ range q, (-1) ^ (j + 1) * (esymm (Fin q) ℚ (j + 1) * X a ^ (ℓ - (j + 1))) =
      X a ^ (ℓ - q) *
        ∑ j ∈ range q, (-1) ^ (j + 1) * (esymm (Fin q) ℚ (j + 1) * X a ^ (q - (j + 1))) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have := mem_range.1 hj
    rw [show ℓ - (j + 1) = ℓ - q + (q - (j + 1)) by omega, pow_add]
    ring
  rw [hsum, show ℓ = ℓ - q + q by omega, pow_add, Nat.add_sub_cancel]
  linear_combination (-X a ^ (ℓ - q) : MvPolynomial (Fin q) ℚ) * h0

/-- Newton's identity for `ℓ > q`: `p_ℓ = −∑_{j=1}^{q} (−1)^j e_j p_{ℓ−j}`. -/
theorem psum_eq (hq : q < ℓ) :
    psum (Fin q) ℚ ℓ =
      -∑ j ∈ range q, (-1) ^ (j + 1) * (esymm (Fin q) ℚ (j + 1) * psum (Fin q) ℚ (ℓ - (j + 1))) := by
  rw [psum, sum_congr rfl fun a _ => pow_eq hq a, sum_neg_distrib, sum_comm]
  simp only [psum, mul_sum]

/-- **Unrooted.** For `ℓ > q`, `p_ℓ` is a rational combination of products `p_μ` over partitions
`μ` of `ℓ` with at least two parts. -/
theorem psum_mem (hq : q < ℓ) : psum (Fin q) ℚ ℓ ∈ Submodule.span ℚ (Prods q ℓ 2) := by
  rw [psum_eq hq]
  refine neg_mem (Submodule.sum_mem _ fun j hj => neg_one_pow_mul_mem _ ?_)
  have := mem_range.1 hj
  have h := mul_psum_mem (q := q) (Submodule.span_mono (prods_one (Nat.succ_pos j)) (esymm_mem (j + 1)))
    (j := ℓ - (j + 1)) (by omega)
  rwa [show j + 1 + (ℓ - (j + 1)) = ℓ by omega] at h

/-- **Rooted.** For `ℓ > q`, `x_a^ℓ` is a rational combination of products `x_a^c p_μ` with
`c ≥ 1` and `μ` a nonempty partition of `ℓ − c`. -/
theorem pow_mem (hq : q < ℓ) (a : Fin q) :
    (X a : MvPolynomial (Fin q) ℚ) ^ ℓ ∈ Submodule.span ℚ (RProds q a ℓ) := by
  rw [pow_eq hq a]
  refine neg_mem (Submodule.sum_mem _ fun j hj => neg_one_pow_mul_mem _ ?_)
  have := mem_range.1 hj
  have h := xpow_mul_mem (q := q) (a := a) (c := ℓ - (j + 1))
    (Submodule.span_mono (prods_one (Nat.succ_pos j)) (esymm_mem (j + 1))) (by omega)
  rw [show ℓ - (j + 1) + (j + 1) = ℓ by omega] at h
  rwa [mul_comm] at h

/-- **Barrier, unrooted.** If `q < ℓ`, a rational linear map that vanishes on the contribution of
every disconnected set of size `ℓ` vanishes on the contribution of a connected one. -/
theorem barrier {M : Type*} [AddCommGroup M] [Module ℚ M] (hq : q < ℓ)
    (L : MvPolynomial (Fin q) ℚ →ₗ[ℚ] M)
    (h : ∀ μ : Multiset ℕ, (∀ i ∈ μ, 0 < i) → μ.sum = ℓ → 2 ≤ Multiset.card μ →
      L (μ.map (psum (Fin q) ℚ)).prod = 0) :
    L (psum (Fin q) ℚ ℓ) = 0 := by
  have : Submodule.span ℚ (Prods q ℓ 2) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, hpos, hsum, hcard, rfl⟩
    exact h μ hpos hsum hcard
  exact this (psum_mem hq)

/-- **Barrier, rooted.** The same with the root's color fixed to `a`. -/
theorem barrier_rooted {M : Type*} [AddCommGroup M] [Module ℚ M] (hq : q < ℓ) (a : Fin q)
    (L : MvPolynomial (Fin q) ℚ →ₗ[ℚ] M)
    (h : ∀ c : ℕ, ∀ μ : Multiset ℕ, 1 ≤ c → (∀ i ∈ μ, 0 < i) → c + μ.sum = ℓ →
      1 ≤ Multiset.card μ → L (X a ^ c * (μ.map (psum (Fin q) ℚ)).prod) = 0) :
    L (X a ^ ℓ) = 0 := by
  have : Submodule.span ℚ (RProds q a ℓ) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨c, μ, hc, hpos, hsum, hcard, rfl⟩
    exact h c μ hc hpos hsum hcard
  exact this (pow_mem hq a)

end EthCor.Barrier
