import EthCor.ColorTM

/-! # Counting k-colorings in time 2^{o(n)}, for k up to 2^{(lg n)^{1/7}}

The bound of `colorings_uniform` is c·2^{c·(2b)²·(n·b)·r(n·b)} with b = ⌈log₂ k⌉ and
r(N) = lg lg(N+4)/√lg(N+4). Since lg y ≤ 28·y^{1/28}/ln 2, r(N) ≤ (28/ln 2)·(lg n)^{−13/28}; with
b ≤ 2·(lg n)^{1/7} the exponent is at most (896c/ln 2)·n·(lg n)^{−1/28} = o(n) (`boundNK_le`). -/

namespace EthCor

open GraphProblems Turing

/-- r(N) ≤ (28/ln 2)·lg(N+4)^{−13/28}. -/
theorem rate_le_pow (N : ℕ) :
    SatK.rN 1 (1 / 2) N ≤ 28 / Real.log 2 * Real.logb 2 ((N : ℝ) + 4) ^ (-(13 / 28 : ℝ)) := by
  unfold SatK.rN
  rw [pow_one]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hy2 : 2 ≤ Real.logb 2 ((N : ℝ) + 4) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    norm_num
  generalize Real.logb 2 ((N : ℝ) + 4) = y at hy2 ⊢
  have hy0 : 0 < y := by linarith
  have h1 : Real.logb 2 y ≤ 28 / Real.log 2 * y ^ (1 / 28 : ℝ) := by
    have := Real.log_le_rpow_div hy0.le (show (0 : ℝ) < 1 / 28 by norm_num)
    rw [Real.logb, div_le_iff₀ hl2]
    have e : 28 / Real.log 2 * y ^ (1 / 28 : ℝ) * Real.log 2 = y ^ (1 / 28 : ℝ) / (1 / 28) := by field_simp
    rw [e]; exact this
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hy0 _)]
  calc Real.logb 2 y ≤ 28 / Real.log 2 * y ^ (1 / 28 : ℝ) := h1
    _ = 28 / Real.log 2 * y ^ (-(13 / 28 : ℝ)) * y ^ (1 / 2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hy0]; norm_num

/-- For b ≤ 2·(lg n)^{1/7} and n large, the bound of `colorings_uniform` is below 2^{εn}. -/
theorem boundNK_le (c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n b : ℕ, n₀ ≤ n → 1 ≤ b → (b : ℝ) ≤ 2 * Real.logb 2 n ^ (1 / 7 : ℝ) →
      (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((2 * b : ℕ) : ℝ) ^ 2 * ((n * b : ℕ) : ℝ) * SatK.rN 1 (1 / 2) (n * b))
        ≤ (2 : ℝ) ^ (ε * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 896 * ((c : ℝ) + 1) / Real.log 2 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((2 : ℝ) ^ ((2 * A / ε) ^ (28 : ℝ)))
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (2 * Real.logb 2 ((c : ℝ) + 1) / ε)
  refine ⟨n₁ + n₂ + 2, fun n b hn hb hbL => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  generalize hL : Real.logb 2 n = L at hL1 hbL
  have hL0 : 0 < L := by linarith
  -- n is large: A·L^{−1/28} ≤ ε/2
  have hLs : A * L ^ (-(1 / 28 : ℝ)) ≤ ε / 2 := by
    have hLbig : (2 * A / ε) ^ (28 : ℝ) ≤ L := by
      rw [← hL, Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
      exact hn₁.trans (by exact_mod_cast (by omega : n₁ ≤ n))
    have h1 : 2 * A / ε ≤ L ^ (1 / 28 : ℝ) := by
      calc 2 * A / ε = ((2 * A / ε) ^ (28 : ℝ)) ^ (1 / 28 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ L ^ (1 / 28 : ℝ) := Real.rpow_le_rpow (by positivity) hLbig (by norm_num)
    have hpos : 0 < L ^ (1 / 28 : ℝ) := Real.rpow_pos_of_pos hL0 _
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  -- the rate
  have hy : L ≤ Real.logb 2 (((n * b : ℕ) : ℝ) + 4) := by
    rw [← hL]
    refine (Real.logb_le_logb one_lt_two (by linarith) (by positivity)).2 ?_
    have : n ≤ n * b := Nat.le_mul_of_pos_right n hb
    have : (n : ℝ) ≤ ((n * b : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hr : SatK.rN 1 (1 / 2) (n * b) ≤ 28 / Real.log 2 * L ^ (-(13 / 28 : ℝ)) :=
    (rate_le_pow _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL0 hy (by norm_num)) (by positivity))
  have hr0 : 0 ≤ SatK.rN 1 (1 / 2) (n * b) := Wrap.Arith.rate_nonneg _
  -- the bits per vertex
  have hb3 : (b : ℝ) ^ 3 ≤ 8 * L ^ (3 / 7 : ℝ) := by
    calc (b : ℝ) ^ 3 ≤ (2 * L ^ (1 / 7 : ℝ)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg b) hbL 3
      _ = 8 * (L ^ (1 / 7 : ℝ)) ^ (3 : ℕ) := by ring
      _ = 8 * L ^ (3 / 7 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  -- the exponent is at most εn/2
  have hE : (c : ℝ) * ((2 * b : ℕ) : ℝ) ^ 2 * ((n * b : ℕ) : ℝ) * SatK.rN 1 (1 / 2) (n * b) ≤ ε / 2 * n := by
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbr : (b : ℝ) ^ 3 * SatK.rN 1 (1 / 2) (n * b) ≤ 8 * L ^ (3 / 7 : ℝ) * (28 / Real.log 2 * L ^ (-(13 / 28 : ℝ))) :=
      mul_le_mul hb3 hr hr0 (by positivity)
    have hcA : 896 * (c : ℝ) / Real.log 2 ≤ A := by
      rw [hA]; exact div_le_div_of_nonneg_right (by linarith) hl2.le
    calc (c : ℝ) * ((2 * b : ℕ) : ℝ) ^ 2 * ((n * b : ℕ) : ℝ) * SatK.rN 1 (1 / 2) (n * b)
        = 4 * c * n * ((b : ℝ) ^ 3 * SatK.rN 1 (1 / 2) (n * b)) := by push_cast; ring
      _ ≤ 4 * c * n * (8 * L ^ (3 / 7 : ℝ) * (28 / Real.log 2 * L ^ (-(13 / 28 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ = 896 * c / Real.log 2 * (L ^ (3 / 7 : ℝ) * L ^ (-(13 / 28 : ℝ))) * n := by ring
      _ = 896 * c / Real.log 2 * L ^ (-(1 / 28 : ℝ)) * n := by rw [← Real.rpow_add hL0]; norm_num
      _ ≤ A * L ^ (-(1 / 28 : ℝ)) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcA (by positivity)) hn0
      _ ≤ ε / 2 * n := mul_le_mul_of_nonneg_right hLs hn0
  -- the constant factor is at most 2^{εn/2}
  have hc : (c : ℝ) ≤ (2 : ℝ) ^ (ε / 2 * n) := by
    have h3 : Real.logb 2 ((c : ℝ) + 1) ≤ ε / 2 * n := by
      have : (n₂ : ℝ) ≤ n := by exact_mod_cast (by omega : n₂ ≤ n)
      rw [div_le_iff₀ hε] at hn₂
      nlinarith [mul_le_mul_of_nonneg_left this hε.le]
    calc (c : ℝ) ≤ c + 1 := by linarith
      _ = (2 : ℝ) ^ Real.logb 2 ((c : ℝ) + 1) := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (ε / 2 * n) := Real.rpow_le_rpow_of_exponent_le one_le_two h3
  calc (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((2 * b : ℕ) : ℝ) ^ 2 * ((n * b : ℕ) : ℝ) * SatK.rN 1 (1 / 2) (n * b))
      ≤ (2 : ℝ) ^ (ε / 2 * n) * (2 : ℝ) ^ (ε / 2 * n) :=
        mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le one_le_two hE) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (ε * n) := by rw [← Real.rpow_add two_pos]; congr 1; ring

/-- **Counting k-colorings in 2^{o(n)}, uniformly for k ≤ 2^{(lg n)^{1/7}}.** One Turing machine: for
every ε > 0 there is n₀ such that for all n ≥ n₀, all k ≥ 2 with lg k ≤ (lg n)^{1/7} and every graph
G on n vertices, given k in unary and G, it outputs the number of proper k-colorings of G within
2^{εn} steps. -/
theorem colorings_subexp : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → 2 ≤ k →
      Real.logb 2 k ≤ Real.logb 2 n ^ (1 / 7 : ℝ) →
        Wrap.Outputs M (unary k ++ code G) (Nat.bits (numColorings G k)) ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, c, hfin, hM⟩ := colorings_uniform
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := boundNK_le c hε
  refine ⟨n₀ + 2, fun n k G hn hk hkL => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkn : k ≤ n := by
    have h1 : Real.logb 2 n ^ (1 / 7 : ℝ) ≤ Real.logb 2 n := by
      calc Real.logb 2 n ^ (1 / 7 : ℝ) ≤ Real.logb 2 n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = Real.logb 2 n := Real.rpow_one _
    have h2 := (Real.logb_le_logb one_lt_two hk0 (by linarith)).1 (hkL.trans h1)
    exact_mod_cast h2
  have hb : (nb k : ℝ) ≤ 2 * Real.logb 2 n ^ (1 / 7 : ℝ) := by
    have h2 : (2 : ℝ) ^ (nb k : ℝ) ≤ 2 * k := by
      rw [Real.rpow_natCast]; exact_mod_cast two_pow_nb_le hk
    have h3 := (Real.le_logb_iff_rpow_le one_lt_two (by positivity : (0 : ℝ) < 2 * k)).2 h2
    rw [Real.logb_mul (by norm_num) hk0.ne', Real.logb_self_eq_one one_lt_two] at h3
    have h4 : 1 ≤ Real.logb 2 n ^ (1 / 7 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    linarith
  refine Wrap.Outputs.mono (hM n k G hk hkn) (Nat.floor_le_floor ?_)
  exact hn₀ n (nb k) (by omega) (one_le_nb hk) hb

end EthCor
