import EthCor.GrowTree
import MainTheoremFormsStatement
import Mathlib

/-! # The numbers for the growing width

With w = `wN (2n)` and y = lg n: w² ≤ 4·lg(2n)^{1/3}, y/64 ≤ w⁶, w ≤ 4y (`wN_real`). Hence the
exponent C·k²·N·lg lg N/√lg N of the Main Theorem for k = w and N = 2n is at most
328·C·n·lg(2n)^{−11/84} = o(n) (`expN_small`), and (2/w)·lg(e·w·(D+2)) ≤ 96·y^{1/7}/w → 0 for
D ≤ 2^{y^{1/7}} + 1 (`width_small`). `poly_le`: c·(n+2)^c ≤ 2^{ηn} for large n. -/

namespace EthCor.GrowArith

open EthCor.GrowTree Filter Asymptotics

/-- lg y ≤ 41·y^{1/28}. -/
theorem lg_le {y : ℝ} (hy : 0 ≤ y) : Real.logb 2 y ≤ 41 * y ^ (1 / 28 : ℝ) := by
  have hl2 := Real.log_two_gt_d9
  have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 28 by norm_num)
  have hp : 0 ≤ y ^ (1 / 28 : ℝ) := Real.rpow_nonneg hy _
  rw [Real.logb, div_le_iff₀ (by linarith)]
  have e : y ^ (1 / 28 : ℝ) / (1 / 28) = 28 * y ^ (1 / 28 : ℝ) := by ring
  rw [e] at h
  nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 41 * Real.log 2 - 28 by linarith)]

/-- n ≥ ⌈2^T⌉ gives lg n ≥ T. -/
theorem lg_ge (T : ℝ) {n : ℕ} (hn : ⌈(2 : ℝ) ^ T⌉₊ ≤ n) : T ≤ Real.logb 2 n := by
  have h1 : (2 : ℝ) ^ T ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos T) h1
  exact (Real.le_logb_iff_rpow_le one_lt_two h0).2 h1

theorem one_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact this

theorem lg_two_mul {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 ((2 * n : ℕ) : ℝ) = 1 + Real.logb 2 n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  rw [Real.logb_mul (by norm_num) this.ne', Real.logb_self_eq_one one_lt_two]

/-- The width in real numbers. -/
theorem wN_real {n : ℕ} (hn : 2 ≤ n) :
    ((wN (2 * n) : ℕ) : ℝ) ^ 2 ≤ 4 * Real.logb 2 ((2 * n : ℕ) : ℝ) ^ (1 / 3 : ℝ) ∧
    Real.logb 2 n / 64 ≤ ((wN (2 * n) : ℕ) : ℝ) ^ 6 ∧ ((wN (2 * n) : ℕ) : ℝ) ≤ 4 * Real.logb 2 n := by
  obtain ⟨b1, b2⟩ := wN_bounds (show 2 ≤ 2 * n by omega)
  have hv := one_le_wN_sub (2 * n)
  obtain ⟨v, hvd⟩ : ∃ v, v = wN (2 * n) - 1 := ⟨_, rfl⟩
  rw [← hvd] at b1 b2 hv
  have hw : wN (2 * n) = v + 1 := by have := one_le_wN_sub (2 * n); omega
  rw [hw]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Nat.log2 (2 * n) := ⟨_, rfl⟩
  rw [← hℓ] at b1 b2
  have hN0 : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * n by omega)
  -- ℓ ≤ lg(2n) and lg n < ℓ
  have hℓY : (ℓ : ℝ) ≤ Real.logb 2 ((2 * n : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hN0, Real.rpow_natCast]
    have := Nat.log2_self_le (show 2 * n ≠ 0 by omega)
    rw [← hℓ] at this; exact_mod_cast this
  have hyℓ : Real.logb 2 n < ℓ := by
    rw [Real.logb_lt_iff_lt_rpow one_lt_two (by exact_mod_cast (show 0 < n by omega)), Real.rpow_natCast]
    have h := Nat.lt_log2_self (n := 2 * n)
    rw [← hℓ, pow_succ] at h
    exact_mod_cast (show n < 2 ^ ℓ by omega)
  have hY := lg_two_mul (show 1 ≤ n by omega)
  have hy1 := one_le_lg hn
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have b1' : (v : ℝ) ^ 6 ≤ ℓ := by exact_mod_cast b1
  have b2' : (ℓ : ℝ) < 64 * (v : ℝ) ^ 6 := by exact_mod_cast b2
  refine ⟨?_, ?_, ?_⟩
  · have h2 : ((v + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (v : ℝ) ^ 2 := by push_cast; nlinarith
    have h3 : (v : ℝ) ^ 2 = ((v : ℝ) ^ 6) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have h4 : ((v : ℝ) ^ 6) ^ (1 / 3 : ℝ) ≤ Real.logb 2 ((2 * n : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (b1'.trans hℓY) (by norm_num)
    linarith
  · have h5 : (v : ℝ) ^ 6 ≤ ((v + 1 : ℕ) : ℝ) ^ 6 := by push_cast; exact pow_le_pow_left₀ (by positivity) (by linarith) 6
    linarith
  · have h6 : (v : ℝ) ≤ (v : ℝ) ^ 6 := by
      calc (v : ℝ) = (v : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (v : ℝ) ^ 6 := pow_le_pow_right₀ hv1 (by norm_num)
    push_cast
    linarith

/-- The exponent of the Main Theorem at the width `wN (2n)` on 2n variables. -/
theorem expN_le {n : ℕ} (hn : 2 ≤ n) :
    MainTheoremForms.expN (wN (2 * n)) (2 * n) ≤ 164 * ((2 * n : ℕ) : ℝ) * Real.logb 2 ((2 * n : ℕ) : ℝ) ^ (-(11 / 84) : ℝ) := by
  obtain ⟨h1, -, -⟩ := wN_real hn
  unfold MainTheoremForms.expN MainTheoremForms.lg
  generalize hYd : Real.logb 2 ((2 * n : ℕ) : ℝ) = Y at h1
  have hY2 : 2 ≤ Y := by
    rw [← hYd, lg_two_mul (show 1 ≤ n by omega)]; linarith [one_le_lg hn]
  have hY : 0 < Y := by linarith
  have hN : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 := lg_le hY.le
  have hlY : 0 ≤ Real.logb 2 Y := Real.logb_nonneg one_lt_two (by linarith)
  rw [Real.sqrt_eq_rpow, div_le_iff₀ (Real.rpow_pos_of_pos hY _)]
  have e : Y ^ (1 / 3 : ℝ) * Y ^ (1 / 28 : ℝ) = Y ^ (-(11 / 84) : ℝ) * Y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hY, ← Real.rpow_add hY]; norm_num
  calc ((wN (2 * n) : ℕ) : ℝ) ^ 2 * ((2 * n : ℕ) : ℝ) * Real.logb 2 Y
      ≤ (4 * Y ^ (1 / 3 : ℝ)) * ((2 * n : ℕ) : ℝ) * (41 * Y ^ (1 / 28 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 hN) h2 hlY (by positivity)
    _ = 164 * ((2 * n : ℕ) : ℝ) * (Y ^ (1 / 3 : ℝ) * Y ^ (1 / 28 : ℝ)) := by ring
    _ = 164 * ((2 * n : ℕ) : ℝ) * Y ^ (-(11 / 84) : ℝ) * Y ^ (1 / 2 : ℝ) := by rw [e]; ring

/-- C·(the exponent) ≤ η·n for large n. -/
theorem expN_small (C : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n) ≤ η * n := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 328 * ((C : ℝ) + 1) / η := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨⌈(2 : ℝ) ^ (B ^ (84 / 11 : ℝ))⌉₊ + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hy := lg_ge (B ^ (84 / 11 : ℝ)) (show ⌈(2 : ℝ) ^ (B ^ (84 / 11 : ℝ))⌉₊ ≤ n by omega)
  have hYe := lg_two_mul (show 1 ≤ n by omega)
  have hy1 := one_le_lg hn2
  generalize hYd : Real.logb 2 ((2 * n : ℕ) : ℝ) = Y at hYe
  have hYB : B ^ (84 / 11 : ℝ) ≤ Y := by linarith
  have hY : 0 < Y := by linarith
  have hYp : B ≤ Y ^ (11 / 84 : ℝ) := by
    calc B = (B ^ (84 / 11 : ℝ)) ^ (11 / 84 : ℝ) := by rw [← Real.rpow_mul hB0.le]; norm_num
      _ ≤ Y ^ (11 / 84 : ℝ) := Real.rpow_le_rpow (by positivity) hYB (by norm_num)
  have hneg : Y ^ (-(11 / 84) : ℝ) ≤ η / (328 * ((C : ℝ) + 1)) := by
    rw [Real.rpow_neg hY.le, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hB, div_le_iff₀ hη] at hYp
    linarith
  have h := expN_le hn2
  rw [hYd] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  calc (C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n)
      ≤ C * (164 * ((2 * n : ℕ) : ℝ) * (η / (328 * ((C : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hneg (by positivity))) hc0
    _ = η * n * (C / ((C : ℝ) + 1)) := by push_cast; field_simp; ring
    _ ≤ η * n * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
    _ = η * n := mul_one _

/-- The width condition of `EthCor.CnfTree.shortens_of` holds for large n, for every D ≤ 2^{y^{1/7}} + 1. -/
theorem width_small {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ D : ℕ, (D : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) + 1 →
      ((2 : ℕ) : ℝ) / ((wN (2 * n) : ℕ) : ℝ) *
        Real.logb 2 (Real.exp 1 * ((wN (2 * n) : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ)) ≤ η := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 64 * (96 / η) ^ 6 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨⌈(2 : ℝ) ^ (T ^ (7 : ℝ))⌉₊ + 2, fun n hn D hD => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hy := lg_ge (T ^ (7 : ℝ)) (show ⌈(2 : ℝ) ^ (T ^ (7 : ℝ))⌉₊ ≤ n by omega)
  obtain ⟨-, w1, w2⟩ := wN_real hn2
  have hy1 := one_le_lg hn2
  generalize hyd : Real.logb 2 n = y at hy hy1 hD w1 w2
  generalize hwd : ((wN (2 * n) : ℕ) : ℝ) = w at w1 w2 ⊢
  have hy0 : 0 < y := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = y ^ (1 / 7 : ℝ) := ⟨_, rfl⟩
  rw [← hs] at hD
  have hs7 : s ^ 7 = y := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow hy1 (by norm_num)
  have hsT : T ≤ s := by
    calc T = (T ^ (7 : ℝ)) ^ (1 / 7 : ℝ) := by rw [← Real.rpow_mul hT0.le]; norm_num
      _ ≤ s := by rw [hs]; exact Real.rpow_le_rpow (by positivity) hy (by norm_num)
  have hw1 : 1 ≤ w := by
    rw [← hwd]; have := one_le_wN_sub (2 * n); exact_mod_cast (show 1 ≤ wN (2 * n) by omega)
  have hw0 : 0 < w := by linarith
  -- the logarithm is at most 48·s
  have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow one_le_two (by linarith)
  have hD2 : ((D + 2 : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ s := by push_cast; linarith
  have harg : Real.exp 1 * w * ((D + 2 : ℕ) : ℝ) ≤ 48 * y * (2 : ℝ) ^ s := by
    have he := Real.exp_one_lt_d9
    calc Real.exp 1 * w * ((D + 2 : ℕ) : ℝ) ≤ 3 * (4 * y) * (4 * (2 : ℝ) ^ s) := by
          gcongr
          · linarith
      _ = 48 * y * (2 : ℝ) ^ s := by ring
  have hlog : Real.logb 2 (Real.exp 1 * w * ((D + 2 : ℕ) : ℝ)) ≤ 48 * s := by
    have hpos : 0 < Real.exp 1 * w * ((D + 2 : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < D + 2 by omega)
      positivity
    refine (Real.logb_le_logb_of_le one_lt_two hpos harg).trans ?_
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) hy0.ne',
      Real.logb_rpow two_pos (by norm_num)]
    have h48 : Real.logb 2 48 ≤ 6 := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by norm_num)]; norm_num
    have hly := lg_le hy0.le
    have h28 : y ^ (1 / 28 : ℝ) ≤ s := by rw [hs]; exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    linarith
  -- 96·s ≤ η·w
  have hsw : 96 * s ≤ η * w := by
    have k1 : η ^ 6 * s ≥ 64 * 96 ^ 6 := by
      have : 64 * 96 ^ 6 = η ^ 6 * T := by rw [hT]; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left hsT (by positivity)
    have k2 : (96 * s) ^ 6 ≤ (η * w) ^ 6 := by
      have e1 : (96 * s) ^ 6 = 96 ^ 6 * s ^ 6 := by ring
      have e2 : (η * w) ^ 6 = η ^ 6 * w ^ 6 := by ring
      rw [e1, e2]
      have k3 : η ^ 6 * (y / 64) ≤ η ^ 6 * w ^ 6 := mul_le_mul_of_nonneg_left w1 (by positivity)
      have k4 : 96 ^ 6 * s ^ 6 ≤ η ^ 6 * (y / 64) := by
        rw [← hs7]
        have : 0 ≤ s ^ 6 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left k1 this]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 k2
  calc ((2 : ℕ) : ℝ) / w * Real.logb 2 (Real.exp 1 * w * ((D + 2 : ℕ) : ℝ)) ≤ 2 / w * (48 * s) := by
        rw [Nat.cast_ofNat]; exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 96 * s / w := by ring
    _ ≤ η := by rw [div_le_iff₀ hw0]; linarith

/-- c·(n+2)^c ≤ 2^{ηn} for large n. -/
theorem poly_le (c : ℕ) {η : ℝ} (hη : 0 < η) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (c : ℝ) * ((n : ℝ) + 2) ^ c ≤ (2 : ℝ) ^ (η * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = η * Real.log 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop c hb0).bound
    (show 0 < Real.exp (-(2 * b)) / ((c : ℝ) + 1) by positivity)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈a⌉₊, fun n hn => ?_⟩
  have hx : a ≤ (n : ℝ) + 2 := by
    have := (Nat.le_ceil a).trans (show ((⌈a⌉₊ : ℕ) : ℝ) ≤ n by exact_mod_cast hn); linarith
  have h1 := ha _ hx
  have hx0 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0 c), abs_of_pos (Real.exp_pos _)] at h1
  have e : Real.exp (-(2 * b)) * Real.exp (b * ((n : ℝ) + 2)) = (2 : ℝ) ^ (η * n) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos two_pos, hb]; congr 1; ring
  have h2 : ((n : ℝ) + 2) ^ c ≤ (2 : ℝ) ^ (η * n) / ((c : ℝ) + 1) := by
    rw [← e]; calc _ ≤ _ := h1
      _ = _ := by ring
  have h3 : 0 ≤ (2 : ℝ) ^ (η * n) := by positivity
  calc (c : ℝ) * ((n : ℝ) + 2) ^ c ≤ c * ((2 : ℝ) ^ (η * n) / ((c : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
    _ = (2 : ℝ) ^ (η * n) * (c / ((c : ℝ) + 1)) := by ring
    _ ≤ (2 : ℝ) ^ (η * n) * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith)) h3
    _ = (2 : ℝ) ^ (η * n) := mul_one _

/-- D = ⌈2^{y^{1/7}}⌉ is at most n, for n ≥ 2. -/
theorem ceil_le_n {n : ℕ} (hn : 2 ≤ n) : ⌈(2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ))⌉₊ ≤ n := by
  have hy1 := one_le_lg hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine Nat.ceil_le.2 ?_
  calc (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) ≤ (2 : ℝ) ^ (Real.logb 2 n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        calc Real.logb 2 n ^ (1 / 7 : ℝ) ≤ Real.logb 2 n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
          _ = Real.logb 2 n := Real.rpow_one _
    _ = n := Real.rpow_logb two_pos (by norm_num) h0

end EthCor.GrowArith
