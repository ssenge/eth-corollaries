import Wrap.ArithRate
import UniformInKStatement

/-! # Arithmetic of the time bound, uniform in the width

`Wrap.Arith.wrapped_time_le_rate` bounds a wrapped call of the counting machine at width 3. Here the
width K is arbitrary: the polynomial overhead of a wrapper around one call at width K, on a formula
in which n' ≤ N + 4 variables occur, is at most c·2^{c·K²·N·r(N)} with one c for all K
(`wrapped_time_le_rateK`), where r(N) = lg lg(N+4)/√lg(N+4). -/

namespace EthCor

open MainTheoremForms Wrap.Arith

theorem timeMin_le (C K m n : ℕ) : (timeMin C K m n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expN K n) := by
  unfold timeMin
  refine (Nat.floor_le (by positivity)).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C))

/-- n'·lg lg n'/√lg n' ≤ 5·N·r(N) for 4 ≤ n' ≤ N + 4 and N ≥ 1. -/
theorem exponent_le_five {N n' : ℕ} (hN : 1 ≤ N) (hn' : 4 ≤ n') (hnn : n' ≤ N + 4) :
    (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ 5 * ((N : ℝ) * SatK.rN 1 (1 / 2) N) := by
  have h := exponent_le hn' hnn
  have hr := rate_nonneg N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- One wrapped call at width K costs at most c·2^{c·K²·N·r(N)}, with c independent of K. -/
theorem wrapped_time_le_rateK (q C₁ C₂ a d : ℕ) :
    ∃ c : ℕ, ∀ (K N m' n' L X : ℕ), 1 ≤ K → 1 ≤ N → 4 ≤ n' → n' ≤ N + 4 → L ≤ a * (N + 2) ^ d → X ≤ a * (N + 2) ^ d →
      q * ((timeMin C₁ K m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ SatM.boundNK (SatK.rN 1 (1 / 2)) c K N := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d * C₂ + d := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, κ = 5 * C₁ + 64 * D := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((q : ℝ) * B ^ q)
  refine ⟨c₀ + κ * q, fun K N m' n' L X hK hN hn' hnn hL hX => Nat.le_floor ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (N : ℝ) * SatK.rN 1 (1 / 2) N := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (Nat.cast_nonneg N) (rate_nonneg N)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hK)
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (K : ℝ) ^ 2 * E := ⟨_, rfl⟩
  have hEF : E ≤ F := by rw [hF]; nlinarith
  have hF0 : 0 ≤ F := hE0.trans hEF
  have h2F : (1 : ℝ) ≤ (2 : ℝ) ^ ((κ : ℝ) * F) := Real.one_le_rpow one_le_two (by positivity)
  have hT : (timeMin C₁ K m' n' : ℝ) ≤ (2 : ℝ) ^ ((κ : ℝ) * F) := by
    have h1 := exponent_le_five hN hn' hnn
    have e : expN K n' = (K : ℝ) ^ 2 * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n')) := by unfold expN; ring
    refine (timeMin_le C₁ K m' n').trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    rw [e, hF, ← hE] at *
    have hk0 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
    have : (C₁ : ℝ) * ((K : ℝ) ^ 2 * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n'))) ≤ (C₁ : ℝ) * ((K : ℝ) ^ 2 * (5 * E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hk0) (Nat.cast_nonneg _)
    have hκ' : (5 * C₁ : ℝ) ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) D]
    nlinarith [mul_nonneg hk0 hE0]
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * F) := by
    have hDκ : (D : ℝ) * 64 ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) C₁]
    calc ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ ((A * (N + 2) ^ D : ℕ) : ℝ) := by
          rw [hA, hD]; exact_mod_cast poly_part_le C₂ a d hL hX
      _ = (A : ℝ) * ((N : ℝ) + 2) ^ D := by push_cast; ring
      _ ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (64 * E + 256)) := by
          rw [hE]; exact mul_le_mul_of_nonneg_left (pow_le_rate D N) (Nat.cast_nonneg A)
      _ = (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((D : ℝ) * 64 * E)) := by
          rw [← Real.rpow_add two_pos]; congr 2; ring
      _ ≤ (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * F)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
            (Real.rpow_nonneg zero_le_two _)) (Nat.cast_nonneg A)
          nlinarith [Nat.cast_nonneg (α := ℝ) D]
      _ = (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * F) := by ring
  have hb : (((timeMin C₁ K m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ≤ B * (2 : ℝ) ^ ((κ : ℝ) * F) := by
    have e1 : (((timeMin C₁ K m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) = (timeMin C₁ K m' n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [e1, hB]
    nlinarith
  have hpow : ((2 : ℝ) ^ ((κ : ℝ) * F)) ^ q ≤ (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * (K : ℝ) ^ 2 * N * SatK.rN 1 (1 / 2) N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have e3 : ((c₀ + κ * q : ℕ) : ℝ) * (K : ℝ) ^ 2 * N * SatK.rN 1 (1 / 2) N = ((c₀ : ℝ) + (κ : ℝ) * q) * F := by
      rw [hF, hE]; push_cast; ring
    rw [e3]
    nlinarith [Nat.cast_nonneg (α := ℝ) c₀]
  calc ((q * ((timeMin C₁ K m' n' + C₂ * L ^ C₂) + X + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * (((timeMin C₁ K m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (B * (2 : ℝ) ^ ((κ : ℝ) * F)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * B ^ q * ((2 : ℝ) ^ ((κ : ℝ) * F)) ^ q := by rw [mul_pow]; ring
    _ ≤ ((c₀ + κ * q : ℕ) : ℝ) * (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * (K : ℝ) ^ 2 * N * SatK.rN 1 (1 / 2) N) := by
        have hc' : (q : ℝ) * B ^ q ≤ ((c₀ + κ * q : ℕ) : ℝ) := by
          push_cast; have : (0 : ℝ) ≤ (κ : ℝ) * q := by positivity
          linarith
        exact mul_le_mul hc' hpow (by positivity) (Nat.cast_nonneg _)

end EthCor
