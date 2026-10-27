import EthCor.Isolation

/-! # The isolation lemma with success rate 2^{−δM}

`iso_real` evaluates the counting bound `iso_count` for r = ⌊M/a⌋ + 1, k = a·b and mm = 3M + 3:
a fraction 1/F of the seeds isolates a point of S, where
F = 8(3M+4)·e^{(3M+3)/(1+b)}·a^{⌊M/a⌋}·e^{M/a}·(2t)^{2r}·e^{M/(2t−1)}.
`isolation` chooses t, b and a, in this order, so that F ≤ 2^{δM} for all large M. -/

open Finset Real

namespace EthCor.Iso

variable {M : ℕ}

/-- (u+1)^M ≤ u^M·e^{M/u}. -/
theorem succ_pow_le (u M : ℕ) (hu : 1 ≤ u) : ((u + 1 : ℕ) : ℝ) ^ M ≤ (u : ℝ) ^ M * exp (M / u) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 (by omega)
  have h : ((u + 1 : ℕ) : ℝ) = u * (1 / u + 1) := by push_cast; field_simp; ring
  calc ((u + 1 : ℕ) : ℝ) ^ M = (u : ℝ) ^ M * (1 / u + 1) ^ M := by rw [h, mul_pow]
    _ ≤ (u : ℝ) ^ M * exp (1 / u) ^ M := by
        gcongr
        exact add_one_le_exp _
    _ = (u : ℝ) ^ M * exp (M / u) := by rw [← exp_nat_mul, mul_one_div]

/-- (M − r)^{ab} ≤ M^{ab}/(1+b) when M/a < r. -/
theorem sub_pow_le (M a b q : ℕ) (ha : 1 ≤ a) (hq : (M : ℝ) / a < q + 1) :
    ((M - (q + 1) : ℕ) : ℝ) ^ (a * b) ≤ (M : ℝ) ^ (a * b) * (1 / (1 + b)) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.2 (by omega)
  have h1a : 1 / (a : ℝ) ≤ 1 := by rw [div_le_one ha']; exact_mod_cast ha
  have h0 : (0 : ℝ) ≤ 1 - 1 / a := by linarith
  have h1 : ((M - (q + 1) : ℕ) : ℝ) ≤ M * (1 - 1 / a) := by
    rcases le_or_gt (q + 1) M with h | h
    · rw [Nat.cast_sub h]
      push_cast
      have : (M : ℝ) * (1 - 1 / a) = M - M / a := by ring
      rw [this]; linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) h0
  have h2 : (1 - 1 / (a : ℝ)) ^ (a * b) ≤ 1 / (1 + b) := by
    calc (1 - 1 / (a : ℝ)) ^ (a * b) ≤ exp (-(1 / a)) ^ (a * b) :=
          pow_le_pow_left₀ h0 (by linarith [add_one_le_exp (-(1 / (a : ℝ)))]) _
      _ = exp (-b) := by
          rw [← exp_nat_mul]
          congr 1
          push_cast
          field_simp
      _ ≤ 1 / (1 + b) := by
          rw [exp_neg, one_div]
          exact inv_anti₀ (by positivity) (by linarith [add_one_le_exp (b : ℝ)])
  calc ((M - (q + 1) : ℕ) : ℝ) ^ (a * b) ≤ ((M : ℝ) * (1 - 1 / a)) ^ (a * b) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
    _ = (M : ℝ) ^ (a * b) * (1 - 1 / a) ^ (a * b) := mul_pow _ _ _
    _ ≤ (M : ℝ) ^ (a * b) * (1 / (1 + b)) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem A_le (M a b q : ℕ) (ha : 1 ≤ a) (hq : (M : ℝ) / a < q + 1) :
    ((2 ^ (a * b) * M ^ (a * b) + 2 ^ (a * b) * (M - (q + 1)) ^ (a * b) : ℕ) : ℝ) ≤
      ((M ^ (a * b) * 2 ^ (a * b) : ℕ) : ℝ) * (1 + 1 / (1 + b)) := by
  have h := sub_pow_le M a b q ha hq
  have h2 : (0 : ℝ) ≤ 2 ^ (a * b) := by positivity
  push_cast
  linarith [mul_le_mul_of_nonneg_left h h2]

theorem two_A_le (M a b q : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hq : (M : ℝ) / a < q + 1) :
    2 * (2 ^ (a * b) * M ^ (a * b) + 2 ^ (a * b) * (M - (q + 1)) ^ (a * b)) ≤ 3 * (M ^ (a * b) * 2 ^ (a * b)) := by
  have h := A_le M a b q ha hq
  have hb' : (1 : ℝ) / (1 + b) ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hN : (0 : ℝ) ≤ ((M ^ (a * b) * 2 ^ (a * b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have : ((2 * (2 ^ (a * b) * M ^ (a * b) + 2 ^ (a * b) * (M - (q + 1)) ^ (a * b)) : ℕ) : ℝ) ≤
      ((3 * (M ^ (a * b) * 2 ^ (a * b)) : ℕ) : ℝ) := by
    rw [Nat.cast_mul 2, Nat.cast_mul 3]
    push_cast only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hb' hN]
  exact_mod_cast this

theorem card_le_two_pow (S : Finset (Fin M → Bool)) : S.card ≤ 2 ^ M := by
  have := Finset.card_le_univ S
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this

theorem hmm_of (s A N M : ℕ) (hs : s ≤ 2 ^ M) (h : 2 * A ≤ 3 * N) :
    2 * s * A ^ (3 * M + 3) ≤ (2 * N) ^ (3 * M + 3) := by
  have h1 : (2 * A) ^ (3 * M + 3) ≤ (3 * N) ^ (3 * M + 3) := Nat.pow_le_pow_left h _
  have h2 : 2 * 2 ^ M * 3 ^ (3 * M + 3) ≤ 4 ^ (3 * M + 3) := by
    rw [show 3 * M + 3 = 3 * (M + 1) by ring, pow_mul, pow_mul, ← pow_succ', ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine Nat.le_of_mul_le_mul_right (?_ : _ * 2 ^ (3 * M + 3) ≤ _ * 2 ^ (3 * M + 3)) (Nat.two_pow_pos _)
  calc 2 * s * A ^ (3 * M + 3) * 2 ^ (3 * M + 3) = 2 * s * (2 * A) ^ (3 * M + 3) := by rw [mul_pow]; ring
    _ ≤ 2 * 2 ^ M * (3 * N) ^ (3 * M + 3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) h1
    _ = 2 * 2 ^ M * 3 ^ (3 * M + 3) * N ^ (3 * M + 3) := by rw [mul_pow]; ring
    _ ≤ 4 ^ (3 * M + 3) * N ^ (3 * M + 3) := Nat.mul_le_mul_right _ h2
    _ = (2 * N) ^ (3 * M + 3) * 2 ^ (3 * M + 3) := by
        rw [mul_pow, show (4 : ℕ) = 2 * 2 by rfl, mul_pow]; ring

theorem chain_le {Ω C A V p c U n e1 v p' w e2 : ℝ} (hc : Ω * (w * n) ≤ C * A * V * p * c * U)
    (hA : A ≤ n * e1) (hV : V ≤ v) (hp : p ≤ p') (hcc : c ≤ w * e2)
    (hC : 0 ≤ C) (hV0 : 0 ≤ V) (hp0 : 0 ≤ p) (hc0 : 0 ≤ c) (hU : 0 ≤ U) (he1 : 0 ≤ e1) (hv : 0 ≤ v)
    (hn : 0 ≤ n) (hwn : 0 < w * n) :
    Ω ≤ C * e1 * v * p' * e2 * U := by
  have s0 : 0 ≤ C * (n * e1) := mul_nonneg hC (mul_nonneg hn he1)
  have s1 : C * A ≤ C * (n * e1) := mul_le_mul_of_nonneg_left hA hC
  have s2 : C * A * V ≤ C * (n * e1) * v := mul_le_mul s1 hV hV0 s0
  have s3 : C * A * V * p ≤ C * (n * e1) * v * p' := mul_le_mul s2 hp hp0 (mul_nonneg s0 hv)
  have s4 : C * A * V * p * c ≤ C * (n * e1) * v * p' * (w * e2) :=
    mul_le_mul s3 hcc hc0 (mul_nonneg (mul_nonneg s0 hv) (hp0.trans hp))
  have h2 : Ω * (w * n) ≤ (C * e1 * v * p' * e2 * U) * (w * n) := by
    calc Ω * (w * n) ≤ C * A * V * p * c * U := hc
      _ ≤ C * (n * e1) * v * p' * (w * e2) * U := mul_le_mul_of_nonneg_right s4 hU
      _ = _ := by ring
  exact le_of_mul_le_mul_right h2 hwn

/-- The ball of radius ⌊M/a⌋: V ≤ a^{⌊M/a⌋}·e^{M/a}. -/
theorem V_le (a q : ℕ) (ha : 1 ≤ a) (hqle : q ≤ M) :
    ((univ.filter fun z : Fin M → Bool => wt z < q + 1).card : ℝ) ≤ (a : ℝ) ^ q * exp (M / a) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.2 (by omega)
  have h1 := card_ball_le (M := M) a (q + 1) ha
  rw [show M + 1 - (q + 1) = M - q by omega] at h1
  have h2 : ((univ.filter fun z : Fin M → Bool => wt z < q + 1).card : ℝ) * (a : ℝ) ^ (M - q) ≤
      ((a + 1 : ℕ) : ℝ) ^ M := by exact_mod_cast h1
  have h3 := succ_pow_le a M ha
  have h4 : (a : ℝ) ^ M = (a : ℝ) ^ q * (a : ℝ) ^ (M - q) := by rw [← pow_add, Nat.add_sub_cancel' hqle]
  rw [h4] at h3
  have h5 : ((univ.filter fun z : Fin M → Bool => wt z < q + 1).card : ℝ) * (a : ℝ) ^ (M - q) ≤
      ((a : ℝ) ^ q * exp (M / a)) * (a : ℝ) ^ (M - q) := by
    calc _ ≤ _ := h2
      _ ≤ _ := h3
      _ = _ := by ring
  exact le_of_mul_le_mul_right h5 (pow_pos ha' _)

/-- **Explicit isolation bound.** -/
theorem iso_real (M a b t : ℕ) (S : Finset (Fin M → Bool)) (hS : S.Nonempty) (ht : 1 ≤ t) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hM : 1 ≤ M) :
    (Fintype.card (Seed M (a * b) t (3 * M + 3)) : ℝ) ≤
      8 * (3 * M + 4) * exp ((3 * M + 3) * (1 / (1 + b))) * ((a : ℝ) ^ (M / a) * exp (M / a)) *
        ((2 * t : ℕ) : ℝ) ^ (2 * (M / a + 1)) * exp (M / (2 * t - 1 : ℕ)) *
          (univ.filter fun ω : Seed M (a * b) t (3 * M + 3) => (S.filter (H ω)).card = 1).card := by
  have hqlt : (M : ℝ) / a < (M / a : ℕ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.lt_floor_add_one _
  have hc := iso_count (k := a * b) S hS (M / a + 1) (3 * M + 3) t ht
    (hmm_of S.card _ _ M (card_le_two_pow S) (two_A_le M a b (M / a) ha hb hqlt))
  have hA := A_le M a b (M / a) ha hqlt
  have hV := V_le (M := M) a (M / a) ha (Nat.div_le_self M a)
  generalize (univ.filter fun z : Fin M → Bool => wt z < M / a + 1).card = V at hc hV
  generalize (univ.filter fun ω : Seed M (a * b) t (3 * M + 3) => (S.filter (H ω)).card = 1).card = U at hc ⊢
  generalize Fintype.card (Seed M (a * b) t (3 * M + 3)) = Ω at hc ⊢
  generalize 2 ^ (a * b) * M ^ (a * b) + 2 ^ (a * b) * (M - (M / a + 1)) ^ (a * b) = A at hc hA
  have hN0 : 0 < M ^ (a * b) * 2 ^ (a * b) := Nat.mul_pos (pow_pos hM _) (pow_pos two_pos _)
  generalize M ^ (a * b) * 2 ^ (a * b) = N at hc hA hN0
  generalize M / a = q at hc hV ⊢
  obtain ⟨u, hu⟩ : ∃ u, u = 2 * t - 1 := ⟨_, rfl⟩
  have h2t : 2 * t = u + 1 := by omega
  have hu1 : 1 ≤ u := by omega
  rw [← hu, h2t, show 3 * M + 3 + 1 = 3 * M + 4 by ring] at hc
  rw [← hu, h2t]
  have hcR : (Ω : ℝ) * ((u : ℝ) ^ M * (N : ℝ) ^ (3 * M + 3)) ≤
      (8 * (3 * M + 4) : ℝ) * (A : ℝ) ^ (3 * M + 3) * V * (u : ℝ) ^ (2 * (q + 1)) * ((u + 1 : ℕ) : ℝ) ^ M * U := by
    exact_mod_cast hc
  have hAm : (A : ℝ) ^ (3 * M + 3) ≤ (N : ℝ) ^ (3 * M + 3) * exp ((3 * M + 3) * (1 / (1 + b))) := by
    have h1 : (A : ℝ) ≤ N * exp (1 / (1 + b)) :=
      hA.trans (mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp (1 / (1 + (b : ℝ)))]) (Nat.cast_nonneg _))
    calc (A : ℝ) ^ (3 * M + 3) ≤ (N * exp (1 / (1 + b))) ^ (3 * M + 3) := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
      _ = _ := by rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  have hp : (u : ℝ) ^ (2 * (q + 1)) ≤ ((u + 1 : ℕ) : ℝ) ^ (2 * (q + 1)) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) _
  have hwn : (0 : ℝ) < (u : ℝ) ^ M * (N : ℝ) ^ (3 * M + 3) := by
    have hu' : (0 : ℝ) < u := Nat.cast_pos.2 (by omega)
    have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    positivity
  exact chain_le hcR hAm hV hp (succ_pow_le u M hu1) (by positivity) (Nat.cast_nonneg _) (by positivity)
    (by positivity) (Nat.cast_nonneg _) (exp_pos _).le (by positivity) (by positivity) hwn

/-- F ≤ 2^{δM} under the conditions on the parameters. -/
theorem F_le (M a b t : ℕ) (η δ : ℝ) (hη : η = δ * log 2 / 5) (ht : 1 ≤ t) (ha : 1 ≤ a) (hM : 1 ≤ M)
    (htη : 1 / ((2 * t - 1 : ℕ) : ℝ) ≤ η) (hbη : 6 * (1 / (1 + (b : ℝ))) ≤ η)
    (haη : log a + 1 + 2 * log ((2 * t : ℕ) : ℝ) ≤ η * a)
    (hlog : log (8 * (3 * M + 4)) + 2 * log ((2 * t : ℕ) : ℝ) ≤ 2 * η * M) :
    8 * (3 * (M : ℝ) + 4) * exp ((3 * M + 3) * (1 / (1 + b))) * ((a : ℝ) ^ (M / a) * exp (M / a)) *
        ((2 * t : ℕ) : ℝ) ^ (2 * (M / a + 1)) * exp (M / (2 * t - 1 : ℕ)) ≤ 2 ^ (δ * M) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.2 (by omega)
  have ht' : (1 : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * t by omega)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h8 : 8 * (3 * (M : ℝ) + 4) = exp (log (8 * (3 * M + 4))) := (exp_log (by positivity)).symm
  have hpa : (a : ℝ) ^ (M / a) = exp (((M / a : ℕ) : ℝ) * log a) := by rw [exp_nat_mul, exp_log ha']
  have hpt : ((2 * t : ℕ) : ℝ) ^ (2 * (M / a + 1)) =
      exp (((2 * (M / a + 1) : ℕ) : ℝ) * log ((2 * t : ℕ) : ℝ)) := by
    rw [exp_nat_mul, exp_log (by linarith)]
  rw [h8, hpa, hpt, rpow_def_of_pos two_pos]
  simp only [← exp_add]
  rw [exp_le_exp]
  have hq : ((M / a : ℕ) : ℝ) ≤ M / a := Nat.cast_div_le
  have hla : 0 ≤ log (a : ℝ) := log_nonneg (by exact_mod_cast ha)
  have hlt : 0 ≤ log ((2 * t : ℕ) : ℝ) := log_nonneg ht'
  have f1 : ((M / a : ℕ) : ℝ) * log a ≤ (M / a) * log a := mul_le_mul_of_nonneg_right hq hla
  have f2 : ((M / a : ℕ) : ℝ) * (2 * log ((2 * t : ℕ) : ℝ)) ≤ (M / a) * (2 * log ((2 * t : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  have f3 : ((M : ℝ) / a) * (log a + 1 + 2 * log ((2 * t : ℕ) : ℝ)) ≤ (M / a) * (η * a) :=
    mul_le_mul_of_nonneg_left haη (by positivity)
  have f4 : ((M : ℝ) / a) * (η * a) = η * M := by field_simp
  have hρ : 0 ≤ 1 / (1 + (b : ℝ)) := by positivity
  have f5 := mul_le_mul_of_nonneg_right (show 3 * (M : ℝ) + 3 ≤ 6 * M by linarith) hρ
  have f6 := mul_le_mul_of_nonneg_left hbη (show (0 : ℝ) ≤ M by positivity)
  have f7 : (M : ℝ) / ((2 * t - 1 : ℕ) : ℝ) ≤ M * η := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left htη (by positivity)
  have e : ((2 * (M / a + 1) : ℕ) : ℝ) = 2 * ((M / a : ℕ) : ℝ) + 2 := by push_cast; ring
  rw [e]
  subst hη
  linarith

/-- **Isolation lemma for arbitrary sets.** For every δ > 0 there are k and t such that, for all large M
and every nonempty S ⊆ {0,1}^M, at least a fraction 2^{−δM} of the seeds ω (3M+3 parity checks on k
coordinates each, a number of checks to use, and fixings with rate 1/t) leave exactly one point of S. -/
theorem isolation (δ : ℝ) (hδ : 0 < δ) : ∃ k t : ℕ, 1 ≤ t ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ S : Finset (Fin M → Bool), S.Nonempty →
      (Fintype.card (Seed M k t (3 * M + 3)) : ℝ) ≤
        2 ^ (δ * M) * (univ.filter fun ω : Seed M k t (3 * M + 3) => (S.filter (H ω)).card = 1).card := by
  obtain ⟨η, hη⟩ : ∃ η, η = δ * log 2 / 5 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; have := log_pos one_lt_two; positivity
  -- the fixing rate
  obtain ⟨t, ht1, htη⟩ : ∃ t : ℕ, 1 ≤ t ∧ 1 / ((2 * t - 1 : ℕ) : ℝ) ≤ η := by
    refine ⟨⌈1 / η⌉₊ + 1, by omega, ?_⟩
    have h1 : (1 / η : ℝ) ≤ ⌈1 / η⌉₊ := Nat.le_ceil _
    have h2 : ((⌈1 / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((2 * (⌈1 / η⌉₊ + 1) - 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
    have h3 : (0 : ℝ) < ((2 * (⌈1 / η⌉₊ + 1) - 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    rw [div_le_iff₀ h3]
    push_cast at h2
    calc (1 : ℝ) = η * (1 / η) := (mul_one_div_cancel hη0.ne').symm
      _ ≤ η * ((2 * (⌈1 / η⌉₊ + 1) - 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hη0.le
  -- the check width is a·b
  obtain ⟨b, hb1, hbη⟩ : ∃ b : ℕ, 1 ≤ b ∧ 6 * (1 / (1 + (b : ℝ))) ≤ η := by
    refine ⟨⌈6 / η⌉₊ + 1, by omega, ?_⟩
    have h1 : (6 / η : ℝ) ≤ ⌈6 / η⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hη0] at h1
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atTop.1 (isLittleO_log_id_atTop.bound (half_pos hη0))
  obtain ⟨a, ha1, haη⟩ : ∃ a : ℕ, 1 ≤ a ∧ log a + 1 + 2 * log ((2 * t : ℕ) : ℝ) ≤ η * a := by
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈max A₀ (2 * (1 + 2 * log ((2 * t : ℕ) : ℝ)) / η)⌉₊ := ⟨_, rfl⟩
    have hcle : max A₀ (2 * (1 + 2 * log ((2 * t : ℕ) : ℝ)) / η) ≤ (c : ℝ) := hc ▸ Nat.le_ceil _
    refine ⟨c + 1, by omega, ?_⟩
    have h1 : max A₀ (2 * (1 + 2 * log ((2 * t : ℕ) : ℝ)) / η) ≤ ((c + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]; linarith
    have ha0 : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]; linarith [Nat.cast_nonneg (α := ℝ) c]
    have h2 := hA₀ ((c + 1 : ℕ) : ℝ) (le_trans (le_max_left _ _) h1)
    simp only [Real.norm_eq_abs, id] at h2
    rw [abs_of_nonneg (log_nonneg ha0), abs_of_nonneg (by linarith)] at h2
    have h3 : 2 * (1 + 2 * log ((2 * t : ℕ) : ℝ)) / η ≤ ((c + 1 : ℕ) : ℝ) := le_trans (le_max_right _ _) h1
    rw [div_le_iff₀ hη0] at h3
    linarith
  -- large M
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.1 (isLittleO_log_id_atTop.bound hη0)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈max B₀ ((log 56 + 2 * log ((2 * t : ℕ) : ℝ)) / η)⌉₊ := ⟨_, rfl⟩
  have hcle : max B₀ ((log 56 + 2 * log ((2 * t : ℕ) : ℝ)) / η) ≤ (c : ℝ) := hc ▸ Nat.le_ceil _
  refine ⟨a * b, t, ht1, c + 1, fun M hM S hS => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMr : (c : ℝ) + 1 ≤ M := by exact_mod_cast hM
  have hlog : log (8 * (3 * M + 4)) + 2 * log ((2 * t : ℕ) : ℝ) ≤ 2 * η * M := by
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have h1 : log (8 * (3 * (M : ℝ) + 4)) ≤ log 56 + log M := by
      rw [← log_mul (by norm_num) (by linarith : (0 : ℝ) < M).ne']
      exact log_le_log (by positivity) (by linarith)
    have h2 := hB₀ (M : ℝ) (by linarith [le_max_left B₀ ((log 56 + 2 * log ((2 * t : ℕ) : ℝ)) / η)])
    simp only [Real.norm_eq_abs, id] at h2
    rw [abs_of_nonneg (log_nonneg hM'), abs_of_nonneg (by linarith)] at h2
    have h3 : (log 56 + 2 * log ((2 * t : ℕ) : ℝ)) / η ≤ M := by
      linarith [le_max_right B₀ ((log 56 + 2 * log ((2 * t : ℕ) : ℝ)) / η)]
    rw [div_le_iff₀ hη0] at h3
    linarith
  have h := iso_real M a b t S hS ht1 ha1 hb1 hM1
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact F_le M a b t η δ hη ht1 ha1 hM1 htη hbη haη hlog

end EthCor.Iso
