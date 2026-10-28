import EthCor.HamSparseTM

/-! # ⊕Hamiltonian cycle for m = o(n·√lg n / lg lg n) edges

`hc_parity_little_o`: the machine of A5a′ (`HamSTM.hcS_tm`) decides the parity of the number of
Hamiltonian cycles within 2^{εn} steps for every graph with at most n·g(n) edges, for every g with
g(n)·r(n) → 0, where r(n) = lg lg(n+4)/√lg(n+4) is the rate of Anthropic's bound (`SatK.rN 1 (1/2)`).
That is, for m = o(n·√lg n/lg lg n) edges. It contains `hc_parity_sparse` (g(n) = (lg n)^{1/2−θ}).

The formula has N = 5m' + n + 2 variables, m' ≤ m the length of the edge list, and the bound of
`hcS_tm` is c·2^{9c·N·r(N)}. Since m ≤ n², N + 4 ≤ (n + 4)³, and then r(N) ≤ 3·r(n) (`rate_three`):
lg(N+4) ≤ 3·lg(n+4) and lg lg(N+4) ≤ lg 3 + lg lg(n+4) ≤ 3·lg lg(n+4). So
N·r(N) ≤ 3·(5n·g(n) + n + 2)·r(n), and g(n)·r(n) → 0 and r(n) → 0 (`rate_tendsto`) make the exponent
at most εn/2 for large n (`boundO_le`). -/

namespace EthCor.HamO

open Groundwork Groundwork.Prog CountKSat GraphProblems Turing EthCor.Ham EthCor.HamS EthCor.HamTM
  EthCor.HamSTM Filter Topology

/-- r(N) ≤ 3·r(n) for n ≤ N with N + 4 ≤ (n + 4)³. -/
theorem rate_three {n N : ℕ} (hnN : n ≤ N) (hN : (N : ℝ) + 4 ≤ ((n : ℝ) + 4) ^ 3) :
    SatK.rN 1 (1 / 2) N ≤ 3 * SatK.rN 1 (1 / 2) n := by
  unfold SatK.rN
  simp only [pow_one]
  have hn4 : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnN' : (n : ℝ) + 4 ≤ (N : ℝ) + 4 := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = Real.logb 2 ((n : ℝ) + 4) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.logb 2 ((N : ℝ) + 4) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha2 : 2 ≤ a := by
    rw [ha, Real.le_logb_iff_rpow_le one_lt_two (by linarith)]; norm_num
  have hab : a ≤ b := by
    rw [ha, hb]; exact (Real.logb_le_logb one_lt_two (by linarith) (by linarith)).2 hnN'
  have hb3 : b ≤ 3 * a := by
    have h := (Real.logb_le_logb one_lt_two (by linarith) (by positivity)).2 hN
    rw [Real.logb_pow] at h
    rw [hb, ha]; push_cast at h; linarith
  have hla : 1 ≤ Real.logb 2 a := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact ha2
  have hlb : Real.logb 2 b ≤ 3 * Real.logb 2 a := by
    have h1 : Real.logb 2 b ≤ Real.logb 2 (3 * a) :=
      (Real.logb_le_logb one_lt_two (by linarith) (by linarith)).2 hb3
    rw [Real.logb_mul (by norm_num) (by linarith)] at h1
    have h3 : Real.logb 2 3 ≤ 2 := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by norm_num)]; norm_num
    linarith
  have hlb0 : 0 ≤ Real.logb 2 b := Real.logb_nonneg one_lt_two (by linarith)
  have hsa : 0 < a ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hsab : a ^ (1 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) hab (by norm_num)
  calc Real.logb 2 b / b ^ (1 / 2 : ℝ) ≤ Real.logb 2 b / a ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hlb0 hsa hsab
    _ ≤ 3 * Real.logb 2 a / a ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_right hlb hsa.le
    _ = 3 * (Real.logb 2 a / a ^ (1 / 2 : ℝ)) := by ring

/-- The rate r(n) tends to 0. -/
theorem rate_tendsto : Tendsto (fun n : ℕ => SatK.rN 1 (1 / 2) n) atTop (𝓝 0) := by
  have h4 : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ => Real.logb 2 ((n : ℝ) + 4)) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp h4
  have hU : Tendsto (fun n : ℕ => 1 / ((1 / 4 : ℝ) * Real.log 2) *
      Real.logb 2 ((n : ℝ) + 4) ^ ((1 / 4 : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hL).const_mul
      (1 / ((1 / 4 : ℝ) * Real.log 2))
    rw [mul_zero] at h
    convert h using 2 with n
    simp only [Function.comp]
    norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun n => Wrap.Arith.rate_nonneg n) (fun n => rate_le_rpow (by norm_num) n)

/-- For n ≤ N ≤ 5n·g(n) + n + 2 with N + 4 ≤ (n+4)³ and n large, c·2^{9c·N·r(N)} ≤ 2^{εn}. -/
theorem boundO_le (c : ℕ) {ε : ℝ} (hε : 0 < ε) (g : ℕ → ℝ)
    (hg : Tendsto (fun n : ℕ => g n * SatK.rN 1 (1 / 2) n) atTop (𝓝 0)) :
    ∃ n₀ : ℕ, ∀ n N : ℕ, n₀ ≤ n → n ≤ N → (N : ℝ) + 4 ≤ ((n : ℝ) + 4) ^ 3 →
      (N : ℝ) ≤ 5 * n * g n + n + 2 →
      (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N) ≤ (2 : ℝ) ^ (ε * n) := by
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (4 * (162 * c + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hcη : 162 * (c : ℝ) * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hg.eventually (gt_mem_nhds hη0))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (rate_tendsto.eventually (gt_mem_nhds hη0))
  obtain ⟨n₃, hn₃⟩ := exists_nat_ge (2 * Real.logb 2 ((c : ℝ) + 1) / ε)
  refine ⟨n₁ + n₂ + n₃ + 1, fun n N hn hnN hN3 hNg => ?_⟩
  have hgr := hn₁ n (by omega)
  have hr := hn₂ n (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hrN0 : 0 ≤ SatK.rN 1 (1 / 2) N := Wrap.Arith.rate_nonneg _
  have hr0 : 0 ≤ SatK.rN 1 (1 / 2) n := Wrap.Arith.rate_nonneg _
  have h3 := rate_three hnN hN3
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- N·r(N) ≤ 3·(5n·g(n) + n + 2)·r(n) ≤ 18ηn + 6η
  have hNr : (N : ℝ) * SatK.rN 1 (1 / 2) N ≤ 18 * η * n + 6 * η := by
    calc (N : ℝ) * SatK.rN 1 (1 / 2) N ≤ (5 * n * g n + n + 2) * SatK.rN 1 (1 / 2) N :=
          mul_le_mul_of_nonneg_right hNg hrN0
      _ ≤ (5 * n * g n + n + 2) * (3 * SatK.rN 1 (1 / 2) n) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 15 * n * (g n * SatK.rN 1 (1 / 2) n) + 3 * n * SatK.rN 1 (1 / 2) n + 6 * SatK.rN 1 (1 / 2) n := by
          ring
      _ ≤ 15 * n * η + 3 * n * η + 6 * η := by gcongr
      _ = 18 * η * n + 6 * η := by ring
  have hE : (c : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N ≤ ε / 2 * n := by
    have e : (c : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N =
        9 * c * ((N : ℝ) * SatK.rN 1 (1 / 2) N) := by push_cast; ring
    rw [e]
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc 9 * (c : ℝ) * ((N : ℝ) * SatK.rN 1 (1 / 2) N) ≤ 9 * c * (18 * η * n + 6 * η) :=
          mul_le_mul_of_nonneg_left hNr (by positivity)
      _ = 162 * c * η * n + 54 * c * η := by ring
      _ ≤ ε / 4 * n + ε / 4 * n := by
          have h54 : 54 * (c : ℝ) * η ≤ ε / 4 * n := by nlinarith
          nlinarith
      _ = ε / 2 * n := by ring
  have hc : (c : ℝ) ≤ (2 : ℝ) ^ (ε / 2 * n) := by
    have h3' : Real.logb 2 ((c : ℝ) + 1) ≤ ε / 2 * n := by
      have : (n₃ : ℝ) ≤ n := by exact_mod_cast (by omega : n₃ ≤ n)
      rw [div_le_iff₀ hε] at hn₃
      nlinarith [mul_le_mul_of_nonneg_left this hε.le]
    calc (c : ℝ) ≤ c + 1 := by linarith
      _ = (2 : ℝ) ^ Real.logb 2 ((c : ℝ) + 1) := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (ε / 2 * n) := Real.rpow_le_rpow_of_exponent_le one_le_two h3'
  calc (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N)
      ≤ (2 : ℝ) ^ (ε / 2 * n) * (2 : ℝ) ^ (ε / 2 * n) :=
        mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le one_le_two hE) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (ε * n) := by rw [← Real.rpow_add two_pos]; congr 1; ring

open Classical in
/-- **⊕Hamiltonian Cycle in 2^{o(n)} for m = o(n·√lg n/lg lg n) edges.** One Turing machine: for
every g : ℕ → ℝ with g(n)·lg lg(n+4)/√lg(n+4) → 0 and every ε > 0 there is n₀ such that for every
graph G on n ≥ n₀ vertices with at most n·g(n) edges, given G, it outputs whether the number of
Hamiltonian cycles of G is odd within 2^{εn} steps. -/
theorem hc_parity_little_o : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n * (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) /
        Real.logb 2 ((n : ℝ) + 4) ^ (1 / 2 : ℝ))) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      (G.edgeFinset.card : ℝ) ≤ n * g n →
        Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)] ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, c, hfin, hM⟩ := hcS_tm
  refine ⟨M, hfin, fun g hg ε hε => ?_⟩
  have hrn : ∀ n : ℕ, Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) / Real.logb 2 ((n : ℝ) + 4) ^ (1 / 2 : ℝ) =
      SatK.rN 1 (1 / 2) n := fun n => by simp [SatK.rN]
  simp only [hrn] at hg
  obtain ⟨n₀, hn₀⟩ := boundO_le c hε g hg
  refine ⟨n₀ + 4, fun n G hn hm => ?_⟩
  refine Wrap.Outputs.mono (hM n G (by omega)) (Nat.floor_le_floor ?_)
  have h1 : (edges n (matrix G)).length ≤ G.edgeFinset.card := length_edges_le_card G
  have h2 : G.edgeFinset.card ≤ n * n := by
    have := G.card_edgeFinset_le_card_choose_two
    rw [Fintype.card_fin, Nat.choose_two_right] at this
    exact this.trans ((Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
  have h1' : ((edges n (matrix G)).length : ℝ) ≤ G.edgeFinset.card := by exact_mod_cast h1
  refine hn₀ n _ (by omega) (by omega) ?_ ?_
  · have hnn : ((edges n (matrix G)).length : ℝ) ≤ n * n := by exact_mod_cast h1.trans h2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith
  · push_cast
    linarith

end EthCor.HamO
