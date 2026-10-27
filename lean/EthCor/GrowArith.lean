import EthCor.GrowTree
import MainTheoremFormsStatement
import Mathlib

/-! # The numbers for the growing width

N = 2n variables, ℓ = ⌊lg N⌋, L = ⌊lg ℓ⌋, q = ⌊lg L⌋ and w = `wN N`, so (w − 1)⁴·2^{4q} ≤ ℓ <
16·(w − 1)⁴·2^{4q} and 2^q ≤ L < 2^{q+1} (`GrowTree.wN_bounds`). Hence w²·L² ≤ 16·√ℓ and
ℓ < 16·(w − 1)⁴·L⁴ (`wN_facts`). The exponent C·w²·N·lg lg N/√lg N of the Main Theorem is at most
32C·N/L = o(n) (`expN_le`, `expN_small`). For D ≤ 2^{s} + 1 with s = (lg n)^{1/4}/(lg lg n)²
(`sN`), (2/w)·lg(e·w·(D+2)) ≤ 14/√w + 8/(L − 1) → 0 (`width_small`). `poly_le`: c·(n+2)^c ≤ 2^{ηn}
for large n. -/

namespace EthCor.GrowArith

open EthCor.GrowTree Filter Asymptotics

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

theorem lg_two_mul {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 ((2 * n : ℕ) : ℝ) = 1 + Real.logb 2 n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  rw [Real.logb_mul (by norm_num) this.ne', Real.logb_self_eq_one one_lt_two]

/-- lg x ≤ 3·√x. -/
theorem lg_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.logb 2 x ≤ 3 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have hl2 := Real.log_two_gt_d9
  have hs := Real.sqrt_nonneg x
  rw [Real.logb, div_le_iff₀ (by linarith)]
  have e : Real.sqrt x / (1 / 2) = 2 * Real.sqrt x := by ring
  rw [e] at h
  nlinarith

/-- ⌊lg N⌋ ≤ lg N < ⌊lg N⌋ + 1. -/
theorem log2_le_logb {N : ℕ} (hN : N ≠ 0) :
    ((Nat.log2 N : ℕ) : ℝ) ≤ Real.logb 2 N ∧ Real.logb 2 N < ((Nat.log2 N : ℕ) : ℝ) + 1 := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  constructor
  · rw [Real.le_logb_iff_rpow_le one_lt_two h0, Real.rpow_natCast]
    exact_mod_cast Nat.log2_self_le hN
  · rw [Real.logb_lt_iff_lt_rpow one_lt_two h0, ← Nat.cast_succ, Real.rpow_natCast]
    exact_mod_cast Nat.lt_log2_self

/-- N ≥ 2^{2^T} gives ⌊lg N⌋ ≥ 2^T and ⌊lg ⌊lg N⌋⌋ ≥ T. -/
theorem big_N {T N : ℕ} (hN : 2 ^ 2 ^ T ≤ N) : 2 ^ T ≤ Nat.log2 N ∧ T ≤ Nat.log2 (Nat.log2 N) := by
  have hN0 : N ≠ 0 := by have := Nat.two_pow_pos (2 ^ T); omega
  have h1 : 2 ^ T ≤ Nat.log2 N := (Nat.le_log2 hN0).2 hN
  have hℓ0 : Nat.log2 N ≠ 0 := by have := Nat.two_pow_pos T; omega
  exact ⟨h1, (Nat.le_log2 hℓ0).2 h1⟩

/-- The facts on the width: with ℓ = ⌊lg N⌋, L = ⌊lg ℓ⌋ ≥ 16 and v = w − 1: w²·L² ≤ 16·√ℓ,
ℓ < 16·v⁴·L⁴ and 2^L ≤ ℓ < 2^{L+1}. -/
theorem wN_facts {N : ℕ} (hL : 16 ≤ Nat.log2 (Nat.log2 N)) :
    ((wN N : ℕ) : ℝ) ^ 2 * ((Nat.log2 (Nat.log2 N) : ℕ) : ℝ) ^ 2 ≤ 16 * Real.sqrt (Nat.log2 N) ∧
    Nat.log2 N < 16 * (wN N - 1) ^ 4 * Nat.log2 (Nat.log2 N) ^ 4 ∧
    2 ^ Nat.log2 (Nat.log2 N) ≤ Nat.log2 N ∧ Nat.log2 N < 2 ^ (Nat.log2 (Nat.log2 N) + 1) := by
  obtain ⟨b1, b2⟩ := wN_bounds hL
  have hv := one_le_wN_sub N
  generalize hvd : wN N - 1 = v at b1 b2 hv ⊢
  have hw : wN N = v + 1 := by omega
  rw [hw]
  generalize hℓ : Nat.log2 N = ℓ at b1 b2 hL ⊢
  generalize hLd : Nat.log2 ℓ = L at b1 b2 hL ⊢
  generalize hq : Nat.log2 L = q at b1 b2
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hLd; omega
  have hL0 : L ≠ 0 := by omega
  have q1 : 2 ^ q ≤ L := hq ▸ Nat.log2_self_le hL0
  have q2 : L < 2 ^ (q + 1) := hq ▸ Nat.lt_log2_self
  refine ⟨?_, ?_, hLd ▸ Nat.log2_self_le hℓ0, hLd ▸ Nat.lt_log2_self⟩
  · have k1 : (v + 1) ^ 2 * L ^ 2 ≤ 16 * (v ^ 2 * 2 ^ (2 * q)) := by
      have hL2 : L ^ 2 ≤ 4 * 2 ^ (2 * q) := by
        have : L ≤ 2 * 2 ^ q := by rw [pow_succ] at q2; omega
        calc L ^ 2 ≤ (2 * 2 ^ q) ^ 2 := Nat.pow_le_pow_left this 2
          _ = 4 * 2 ^ (2 * q) := by ring
      have hv2 : (v + 1) ^ 2 ≤ 4 * v ^ 2 := by nlinarith
      calc (v + 1) ^ 2 * L ^ 2 ≤ (4 * v ^ 2) * (4 * 2 ^ (2 * q)) := Nat.mul_le_mul hv2 hL2
        _ = 16 * (v ^ 2 * 2 ^ (2 * q)) := by ring
    have k2 : (v ^ 2 * 2 ^ (2 * q)) ^ 2 ≤ ℓ := by
      calc (v ^ 2 * 2 ^ (2 * q)) ^ 2 = v ^ 4 * 2 ^ (4 * q) := by ring
        _ ≤ ℓ := b1
    have k2' : ((v ^ 2 * 2 ^ (2 * q) : ℕ) : ℝ) ^ 2 ≤ ℓ := by exact_mod_cast k2
    have k3 : ((v ^ 2 * 2 ^ (2 * q) : ℕ) : ℝ) ≤ Real.sqrt ℓ := by
      calc ((v ^ 2 * 2 ^ (2 * q) : ℕ) : ℝ) = Real.sqrt (((v ^ 2 * 2 ^ (2 * q) : ℕ) : ℝ) ^ 2) :=
            (Real.sqrt_sq (Nat.cast_nonneg _)).symm
        _ ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt k2'
    have k1' : (((v + 1 : ℕ) : ℝ)) ^ 2 * (L : ℝ) ^ 2 ≤ 16 * ((v ^ 2 * 2 ^ (2 * q) : ℕ) : ℝ) := by
      exact_mod_cast k1
    linarith
  · have h4 : 2 ^ (4 * q) ≤ L ^ 4 := by
      calc 2 ^ (4 * q) = (2 ^ q) ^ 4 := by ring
        _ ≤ L ^ 4 := Nat.pow_le_pow_left q1 4
    calc ℓ < 16 * (v ^ 4 * 2 ^ (4 * q)) := b2
      _ ≤ 16 * (v ^ 4 * L ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
      _ = 16 * v ^ 4 * L ^ 4 := by ring

/-- The exponent of the Main Theorem at the width `wN N`: at most 32·N/L, L = ⌊lg ⌊lg N⌋⌋ ≥ 16. -/
theorem expN_le {N : ℕ} (hL : 16 ≤ Nat.log2 (Nat.log2 N)) :
    MainTheoremForms.expN (wN N) N ≤ 32 * N / ((Nat.log2 (Nat.log2 N) : ℕ) : ℝ) := by
  obtain ⟨f1, -, f3, f4⟩ := wN_facts hL
  have hN0 : N ≠ 0 := by rintro rfl; simp at hL
  obtain ⟨y1, y2⟩ := log2_le_logb hN0
  unfold MainTheoremForms.expN MainTheoremForms.lg
  generalize Real.logb 2 (N : ℝ) = Y at y1 y2 ⊢
  generalize hℓ : Nat.log2 N = ℓ at f1 f3 f4 hL y1 y2 ⊢
  generalize hLd : Nat.log2 ℓ = L at f1 f3 f4 hL ⊢
  have hL16 : (16 : ℝ) ≤ L := by exact_mod_cast hL
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ from le_trans Nat.one_le_two_pow f3)
  have hY1 : 1 ≤ Y := by linarith
  have hlY : Real.logb 2 Y ≤ L + 1 := by
    have h5 : ((ℓ + 1 : ℕ) : ℝ) ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt f4
    push_cast at h5
    rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith),
      show ((L : ℝ) + 1) = ((L + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    linarith
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.2 (by linarith)
  have hw : ((wN N : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ 16 * Real.sqrt Y :=
    f1.trans (by linarith [Real.sqrt_le_sqrt y1])
  rw [div_le_div_iff₀ hsY (by linarith)]
  calc ((wN N : ℕ) : ℝ) ^ 2 * N * Real.logb 2 Y * L ≤ ((wN N : ℕ) : ℝ) ^ 2 * N * (2 * L) * L := by
        gcongr; linarith
    _ = 2 * N * (((wN N : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2) := by ring
    _ ≤ 2 * N * (16 * Real.sqrt Y) := by gcongr
    _ = 32 * N * Real.sqrt Y := by ring

/-- C·(the exponent) ≤ η·n for large n. -/
theorem expN_small (C : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n) ≤ η * n := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 16 + ⌈64 * ((C : ℝ) + 1) / η⌉₊ := ⟨_, rfl⟩
  refine ⟨2 ^ 2 ^ T, fun n hn => ?_⟩
  obtain ⟨-, hL⟩ := big_N (show 2 ^ 2 ^ T ≤ 2 * n by omega)
  have hL16 : 16 ≤ Nat.log2 (Nat.log2 (2 * n)) := by omega
  have h := expN_le hL16
  generalize hLd : Nat.log2 (Nat.log2 (2 * n)) = L at h hL hL16
  have hLr : 64 * ((C : ℝ) + 1) / η ≤ L := by
    have h1 := Nat.le_ceil (64 * ((C : ℝ) + 1) / η)
    have h2 : ((⌈64 * ((C : ℝ) + 1) / η⌉₊ : ℕ) : ℝ) ≤ L := by
      exact_mod_cast (show ⌈64 * ((C : ℝ) + 1) / η⌉₊ ≤ L by omega)
    linarith
  have hL0 : (0 : ℝ) < L := by
    have : (16 : ℝ) ≤ L := by exact_mod_cast hL16
    linarith
  rw [div_le_iff₀ hη] at hLr
  have hc0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n) ≤ C * (32 * ((2 * n : ℕ) : ℝ) / L) :=
        mul_le_mul_of_nonneg_left h hc0
    _ = 64 * C * n / L := by push_cast; ring
    _ ≤ η * n := by
        rw [div_le_iff₀ hL0]
        nlinarith [mul_le_mul_of_nonneg_left hLr hn0]

/-- The exponent in the density: (lg n)^{1/4}/(lg lg n)². -/
noncomputable def sN (n : ℕ) : ℝ := Real.logb 2 n ^ (1 / 4 : ℝ) / Real.logb 2 (Real.logb 2 n) ^ 2

theorem sN_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ sN n := by
  have : (0 : ℝ) ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  exact div_nonneg (Real.rpow_nonneg this _) (sq_nonneg _)

/-- With ℓ = ⌊lg 2n⌋, L = ⌊lg ℓ⌋ ≥ 16 and ℓ < 16·v⁴·L⁴: s ≤ 4v/(L − 1). -/
theorem sN_le {n ℓ L v : ℕ} (hn : 1 ≤ n) (hℓ : Nat.log2 (2 * n) = ℓ) (hL : Nat.log2 ℓ = L)
    (hL16 : 16 ≤ L) (hv : ℓ < 16 * v ^ 4 * L ^ 4) : sN n ≤ 4 * v / ((L : ℝ) - 1) := by
  have hN0 : 2 * n ≠ 0 := by omega
  obtain ⟨y1, y2⟩ := log2_le_logb hN0
  rw [lg_two_mul hn, hℓ] at y1 y2
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hL; omega
  have f3 : 2 ^ L ≤ ℓ := hL ▸ Nat.log2_self_le hℓ0
  have hL16r : (16 : ℝ) ≤ L := by exact_mod_cast hL16
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
  have f2r : (ℓ : ℝ) < 16 * (v : ℝ) ^ 4 * (L : ℝ) ^ 4 := by exact_mod_cast hv
  have f3r : (2 : ℝ) ^ L ≤ ℓ := by exact_mod_cast f3
  have hℓ2 : (2 : ℝ) ≤ ℓ := by
    have : (2 : ℝ) ≤ 2 ^ L :=
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := pow_le_pow_right₀ one_le_two (by omega)
    linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.logb 2 n := ⟨_, rfl⟩
  rw [← hy] at y1 y2
  have hy0 : 0 < y := by linarith
  have hlgy : (L : ℝ) - 1 ≤ Real.logb 2 y := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hy0, Real.rpow_sub two_pos, Real.rpow_one, Real.rpow_natCast]
    linarith
  have hs : sN n = y ^ (1 / 4 : ℝ) / Real.logb 2 y ^ 2 := by rw [sN, hy]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (ℓ : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have ht4 : t ^ 4 = ℓ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hyt : y ^ (1 / 4 : ℝ) ≤ t := by
    rw [ht]; exact Real.rpow_le_rpow hy0.le (by linarith) (by norm_num)
  have htv : t ≤ 4 * v * ((L : ℝ) - 1) := by
    have k1 : (L : ℝ) ^ 4 ≤ (2 * ((L : ℝ) - 1)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have k2 : t ^ 4 ≤ (4 * v * ((L : ℝ) - 1)) ^ 4 := by
      rw [ht4]
      have : 16 * (v : ℝ) ^ 4 * (L : ℝ) ^ 4 ≤ 16 * (v : ℝ) ^ 4 * (2 * ((L : ℝ) - 1)) ^ 4 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e : (4 * (v : ℝ) * ((L : ℝ) - 1)) ^ 4 = 16 * (v : ℝ) ^ 4 * (2 * ((L : ℝ) - 1)) ^ 4 := by
        ring
      rw [e]; linarith
    exact (pow_le_pow_iff_left₀ ht0 (mul_nonneg (by positivity) hL1.le) (by norm_num)).1 k2
  rw [hs]
  calc y ^ (1 / 4 : ℝ) / Real.logb 2 y ^ 2 ≤ t / Real.logb 2 y ^ 2 :=
        div_le_div_of_nonneg_right hyt (sq_nonneg _)
    _ ≤ t / ((L : ℝ) - 1) ^ 2 :=
        div_le_div_of_nonneg_left ht0 (pow_pos hL1 2) (pow_le_pow_left₀ hL1.le hlgy 2)
    _ ≤ 4 * v * ((L : ℝ) - 1) / ((L : ℝ) - 1) ^ 2 := div_le_div_of_nonneg_right htv (sq_nonneg _)
    _ = 4 * v / ((L : ℝ) - 1) := by field_simp

/-- 2^L ≤ ℓ < 16·v⁴·L⁴ forces v > W once L is large. -/
theorem v_big (W : ℕ) :
    ∃ T : ℕ, ∀ ℓ L v : ℕ, T ≤ L → 2 ^ L ≤ ℓ → ℓ < 16 * v ^ 4 * L ^ 4 → W < v := by
  obtain ⟨T, hT⟩ := poly_le (16 * W ^ 4 + 4) one_pos
  refine ⟨T, fun ℓ L v hL h1 h2 => ?_⟩
  have h3 := hT L hL
  rw [one_mul, Real.rpow_natCast] at h3
  have h4 : 16 * W ^ 4 * L ^ 4 ≤ 2 ^ L := by
    have k1 : L ^ 4 ≤ (L + 2) ^ (16 * W ^ 4 + 4) :=
      calc L ^ 4 ≤ (L + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        _ ≤ (L + 2) ^ (16 * W ^ 4 + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have k2 : 16 * W ^ 4 * L ^ 4 ≤ (16 * W ^ 4 + 4) * (L + 2) ^ (16 * W ^ 4 + 4) :=
      Nat.mul_le_mul (by omega) k1
    have k3 : (((16 * W ^ 4 + 4) * (L + 2) ^ (16 * W ^ 4 + 4) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
      push_cast at h3 ⊢; exact h3
    exact k2.trans (by exact_mod_cast k3)
  by_contra hv
  have h5 : 16 * v ^ 4 * L ^ 4 ≤ 16 * W ^ 4 * L ^ 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  exact absurd (lt_of_lt_of_le h2 (h5.trans (h4.trans h1))) (lt_irrefl ℓ)

/-- lg(e·w·(D+2)) ≤ 4 + 3√w + s for D ≤ 2^s + 1. -/
theorem log_part (v D : ℕ) {s : ℝ} (hs : 0 ≤ s) (hD : (D : ℝ) ≤ (2 : ℝ) ^ s + 1) :
    Real.logb 2 (Real.exp 1 * ((v + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ)) ≤
      4 + 3 * Real.sqrt ((v + 1 : ℕ) : ℝ) + s := by
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := Real.one_le_rpow one_le_two hs
  have hD2 : ((D + 2 : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ s := by push_cast; linarith
  have hpos : 0 < Real.exp 1 * ((v + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((D + 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < D + 2 by omega)
    positivity
  have he := Real.exp_one_lt_d9
  refine (Real.logb_le_logb_of_le one_lt_two hpos
    (mul_le_mul_of_nonneg_left hD2 (by positivity))).trans ?_
  have e : Real.exp 1 * ((v + 1 : ℕ) : ℝ) * (4 * (2 : ℝ) ^ s) =
      (4 * Real.exp 1) * ((v + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s := by ring
  rw [e, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow two_pos (by norm_num)]
  have h4e : Real.logb 2 (4 * Real.exp 1) ≤ 4 := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]; norm_num; linarith
  have := lg_le_sqrt (show (0 : ℝ) ≤ ((v + 1 : ℕ) : ℝ) by positivity)
  linarith

/-- The width condition of `EthCor.CnfTree.shortens_of` holds for large n, for every
D ≤ 2^{(lg n)^{1/4}/(lg lg n)²} + 1. -/
theorem width_small {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ D : ℕ, (D : ℝ) ≤ (2 : ℝ) ^ sN n + 1 →
      ((2 : ℕ) : ℝ) / ((wN (2 * n) : ℕ) : ℝ) *
        Real.logb 2 (Real.exp 1 * ((wN (2 * n) : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ)) ≤ η := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = ⌈(28 / η) ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ := v_big W
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 18 + T₁ + ⌈16 / η⌉₊ := ⟨_, rfl⟩
  refine ⟨2 ^ 2 ^ T, fun n hn D hD => ?_⟩
  obtain ⟨-, hLT⟩ := big_N (show 2 ^ 2 ^ T ≤ 2 * n by omega)
  have hL16 : 16 ≤ Nat.log2 (Nat.log2 (2 * n)) := by omega
  obtain ⟨-, f2, f3, -⟩ := wN_facts hL16
  have hn1 : 1 ≤ n := by have := Nat.two_pow_pos (2 ^ T); omega
  have hv1 := one_le_wN_sub (2 * n)
  generalize hvd : wN (2 * n) - 1 = v at f2 hv1
  have hwv : wN (2 * n) = v + 1 := by omega
  rw [hwv]
  generalize hℓ : Nat.log2 (2 * n) = ℓ at f2 f3 hLT hL16
  generalize hLd : Nat.log2 ℓ = L at f2 f3 hLT hL16
  have hs4 := sN_le hn1 hℓ hLd hL16 f2
  have hs0 := sN_nonneg hn1
  have hWv : W < v := hT₁ ℓ L v (by omega) f3 f2
  have hL16r : (16 : ℝ) ≤ L := by exact_mod_cast hL16
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
  have hlog := log_part v D hs0 hD
  have hw1 : (1 : ℝ) ≤ ((v + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ v + 1 by omega)
  generalize hwr : ((v + 1 : ℕ) : ℝ) = w at hlog hw1 ⊢
  have hvw : (v : ℝ) + 1 = w := by rw [← hwr]; push_cast; ring
  have hVW : (28 / η) ^ 2 ≤ (v : ℝ) := by
    have h7 : (28 / η) ^ 2 ≤ (W : ℝ) := by rw [hW]; exact Nat.le_ceil _
    have h8 : (W : ℝ) ≤ v := by exact_mod_cast hWv.le
    linarith
  have hr0 : 0 ≤ Real.sqrt w := Real.sqrt_nonneg w
  have hss : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt (by linarith)
  have hsq : 28 / η ≤ Real.sqrt w := by
    rw [show 28 / η = Real.sqrt ((28 / η) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsw1 : 1 ≤ Real.sqrt w := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hw1
  have hLη : 16 ≤ η * ((L : ℝ) - 1) := by
    have h1 : 16 / η ≤ (⌈16 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈16 / η⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) - 1 := by
      have : ⌈16 / η⌉₊ + 1 ≤ L := by omega
      have : ((⌈16 / η⌉₊ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast this
      push_cast at this; linarith
    rw [div_le_iff₀ hη] at h1
    have := mul_le_mul_of_nonneg_left h2 hη.le
    linarith
  have hA : 2 * (4 + 3 * Real.sqrt w) ≤ η / 2 * w := by
    have h1 : 28 ≤ Real.sqrt w * η := (div_le_iff₀ hη).1 hsq
    have h2 := mul_le_mul_of_nonneg_right h1 hr0
    have h3 : η * w = η * (Real.sqrt w * Real.sqrt w) := by rw [hss]
    linarith
  have hB : 2 * sN n ≤ η / 2 * w := by
    have k : 4 * (v : ℝ) / ((L : ℝ) - 1) ≤ η / 4 * v := by
      rw [div_le_iff₀ hL1]
      have := mul_le_mul_of_nonneg_left hLη (Nat.cast_nonneg v : (0 : ℝ) ≤ v)
      linarith
    have : η / 4 * (v : ℝ) ≤ η / 4 * w := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), e2]
  linarith

/-- D = ⌈2^{(lg n)^{1/4}/(lg lg n)²}⌉ is at most n, for n ≥ 4. -/
theorem ceil_le_n {n : ℕ} (hn : 4 ≤ n) : ⌈(2 : ℝ) ^ sN n⌉₊ ≤ n := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hy2 : 2 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two h0, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
    exact_mod_cast hn
  have hly : 1 ≤ Real.logb 2 (Real.logb 2 n) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hy2
  have hs : sN n ≤ Real.logb 2 n := by
    unfold sN
    calc Real.logb 2 n ^ (1 / 4 : ℝ) / Real.logb 2 (Real.logb 2 n) ^ 2 ≤ Real.logb 2 n ^ (1 / 4 : ℝ) :=
          div_le_self (Real.rpow_nonneg (by linarith) _) (one_le_pow₀ hly)
      _ ≤ Real.logb 2 n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = Real.logb 2 n := Real.rpow_one _
  refine Nat.ceil_le.2 ?_
  calc (2 : ℝ) ^ sN n ≤ (2 : ℝ) ^ (Real.logb 2 n) := Real.rpow_le_rpow_of_exponent_le one_le_two hs
    _ = n := Real.rpow_logb two_pos (by norm_num) h0

end EthCor.GrowArith
