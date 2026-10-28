import EthCor.HamIsoTM
import EthCor.ConnIsoTM

/-! # Amplification by independent repetition

A5b and N2′ give a machine and a bit out(ω) per seed: 0 for every seed on a no-instance, and 1 for at
least a fraction p = 2^{−δn} of the seeds on a yes-instance. Run the machine on R independent seeds
ω₁, …, ω_R and answer yes if some run outputs 1. On a no-instance the answer is always no. On a
yes-instance it is wrong exactly on the tuples with out(ω_i) = 0 for all i, and these are at most a
fraction e^{−pR} of all tuples (`amplify`): there are #{out = 0}^R of them and #{out = 0} ≤ (1 − p)·|Ω|
≤ e^{−p}·|Ω|. For R ≥ 2^{2δn} the fraction is at most e^{−2^{δn}} (`amplify_sq`).

`ham_amplified` and `conn_amplified` state this for the machines of A5b and N2′. The R runs are R
runs of the same machine, each within the time bound of the single run. -/

namespace EthCor.Amplify

open Finset GraphProblems Turing EthCor.Iso EthCor.Ham

/-- **Repetition.** If at least a fraction p of the elements of Ω have out = 1, then at most a
fraction e^{−pR} of the R-tuples have out = 0 everywhere. -/
theorem amplify {Ω : Type} [Fintype Ω] (out : Ω → Bool) {p : ℝ}
    (h : (Fintype.card Ω : ℝ) * p ≤ (univ.filter fun ω => out ω = true).card) (R : ℕ) :
    ((univ.filter fun w : Fin R → Ω => ∀ i, out (w i) = false).card : ℝ) ≤
      (Fintype.card Ω : ℝ) ^ R * Real.exp (-(p * R)) := by
  have hpi : (univ.filter fun w : Fin R → Ω => ∀ i, out (w i) = false) =
      Fintype.piFinset fun _ => univ.filter fun ω => out ω = false := by
    ext w; simp [Fintype.mem_piFinset]
  have hcard : (univ.filter fun ω => out ω = false).card + (univ.filter fun ω => out ω = true).card =
      Fintype.card Ω := by
    have := card_filter_add_card_filter_not (s := (univ : Finset Ω)) (fun ω => out ω = false)
    simp only [Bool.not_eq_false] at this
    rw [this, card_univ]
  have hf : ((univ.filter fun ω => out ω = false).card : ℝ) ≤ Fintype.card Ω * Real.exp (-p) := by
    have h1 : ((univ.filter fun ω => out ω = false).card : ℝ) ≤ Fintype.card Ω * (1 - p) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hcard
      push_cast at this
      nlinarith
    have h2 : (1 - p) ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  rw [hpi, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  push_cast
  calc ((univ.filter fun ω => out ω = false).card : ℝ) ^ R ≤ (Fintype.card Ω * Real.exp (-p)) ^ R :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hf R
    _ = (Fintype.card Ω : ℝ) ^ R * Real.exp (-(p * R)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf

/-- **2^{2δn} repetitions.** If at least a fraction 2^{−δn} of Ω has out = 1, then for R ≥ 2^{2δn} at
most a fraction e^{−2^{δn}} of the R-tuples has out = 0 everywhere. -/
theorem amplify_sq {Ω : Type} [Fintype Ω] (out : Ω → Bool) (δ x : ℝ)
    (h : (Fintype.card Ω : ℝ) ≤ 2 ^ (δ * x) * (univ.filter fun ω => out ω = true).card) (R : ℕ)
    (hR : (2 : ℝ) ^ (2 * δ * x) ≤ R) :
    ((univ.filter fun w : Fin R → Ω => ∀ i, out (w i) = false).card : ℝ) ≤
      (Fintype.card Ω : ℝ) ^ R * Real.exp (-(2 : ℝ) ^ (δ * x)) := by
  have hpos : (0 : ℝ) < 2 ^ (δ * x) := by positivity
  have hp : (Fintype.card Ω : ℝ) * (2 : ℝ) ^ (-(δ * x)) ≤ (univ.filter fun ω => out ω = true).card := by
    rw [Real.rpow_neg zero_le_two]
    calc (Fintype.card Ω : ℝ) * ((2 : ℝ) ^ (δ * x))⁻¹ ≤
          2 ^ (δ * x) * (univ.filter fun ω => out ω = true).card * ((2 : ℝ) ^ (δ * x))⁻¹ :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by field_simp
  refine (amplify out hp R).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Real.exp_le_exp.2
  have : (2 : ℝ) ^ (δ * x) ≤ (2 : ℝ) ^ (-(δ * x)) * R := by
    have e : (2 : ℝ) ^ (2 * δ * x) = (2 : ℝ) ^ (δ * x) * (2 : ℝ) ^ (δ * x) := by
      rw [← Real.rpow_add two_pos]; ring_nf
    rw [Real.rpow_neg zero_le_two]
    rw [e] at hR
    rw [le_inv_mul_iff₀ hpos]
    exact hR
  linarith

open Classical in
/-- **Hamiltonian cycle, amplified.** The machine of A5b, run on R independent seeds: on a graph
without a Hamiltonian cycle every run outputs 0; on a graph with one, the R-tuples of seeds on which
all R runs output 0 are at most a fraction e^{−R·2^{−δn}} of all R-tuples, and at most e^{−2^{δn}}
for R ≥ 2^{2δn}. -/
theorem ham_amplified : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (D : ℕ) (δ ε : ℝ), 0 < δ → 0 < ε → ∃ k t n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      G.edgeFinset.card ≤ D * n →
      ∃ out : Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3) → Bool,
        (∀ ω, Wrap.Outputs M (code G ++ HamITM.seedCode ω) [out ω] ⌊(2 : ℝ) ^ (ε * n)⌋₊) ∧
        (EthCor.Ham.numHamCycles G = 0 → ∀ ω, out ω = false) ∧
        (0 < EthCor.Ham.numHamCycles G → ∀ R : ℕ,
          ((univ.filter fun w : Fin R → Seed (edges n (matrix G)).length k t
              (3 * (edges n (matrix G)).length + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
            (Fintype.card (Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3)) : ℝ) ^ R *
              Real.exp (-((2 : ℝ) ^ (-(δ * n)) * R)) ∧
          ((2 : ℝ) ^ (2 * δ * n) ≤ R →
            ((univ.filter fun w : Fin R → Seed (edges n (matrix G)).length k t
                (3 * (edges n (matrix G)).length + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
              (Fintype.card (Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3)) : ℝ) ^ R *
                Real.exp (-(2 : ℝ) ^ (δ * n)))) := by
  obtain ⟨M, hfin, hM⟩ := HamITM.ham_randomized
  refine ⟨M, hfin, fun D δ ε hδ hε => ?_⟩
  obtain ⟨k, t, n₀, h⟩ := hM D δ ε hδ hε
  refine ⟨k, t, n₀, fun n G hn hm => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := h n G hn hm
  refine ⟨out, hrun, hno, fun hpos R => ⟨?_, amplify_sq out δ n (hyes hpos) R⟩⟩
  have hp : (Fintype.card (Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3)) : ℝ) *
      (2 : ℝ) ^ (-(δ * n)) ≤ (univ.filter fun ω => out ω = true).card := by
    have := hyes hpos
    rw [Real.rpow_neg zero_le_two]
    calc _ ≤ 2 ^ (δ * n) * ((univ.filter fun ω => out ω = true).card : ℝ) * ((2 : ℝ) ^ (δ * n))⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by field_simp
  exact amplify out hp R

open Classical in
/-- **Connected solutions (Steiner tree, connected vertex cover), amplified.** The machine of N2′,
run on R independent seeds, with the same guarantees as `ham_amplified`. -/
theorem conn_amplified (r D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ r) → φ.length ≤ (n + 2) ^ D →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (ConnITM.codeCI G ℓ ω φ) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (ConnTM.numConn G φ ℓ = 0 → ∀ ω, out ω = false) ∧
        (0 < ConnTM.numConn G φ ℓ → ∀ R : ℕ,
          ((univ.filter fun w : Fin R → Seed n k t (3 * n + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
            (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ^ R * Real.exp (-((2 : ℝ) ^ (-(δ * n)) * R)) ∧
          ((2 : ℝ) ^ (2 * δ * n) ≤ R →
            ((univ.filter fun w : Fin R → Seed n k t (3 * n + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
              (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ^ R * Real.exp (-(2 : ℝ) ^ (δ * n)))) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := ConnITM.conn_randomized r D hδ hε
  refine ⟨k, t, n₀, M, C, hfin, fun n ℓ G φ hn h1 h2 hr hD => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n ℓ G φ hn h1 h2 hr hD
  refine ⟨out, hrun, hno, fun hpos R => ⟨?_, amplify_sq out δ n (hyes hpos) R⟩⟩
  have hp : (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) * (2 : ℝ) ^ (-(δ * n)) ≤
      (univ.filter fun ω => out ω = true).card := by
    have := hyes hpos
    rw [Real.rpow_neg zero_le_two]
    calc _ ≤ 2 ^ (δ * n) * ((univ.filter fun ω => out ω = true).card : ℝ) * ((2 : ℝ) ^ (δ * n))⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by field_simp
  exact amplify out hp R

end EthCor.Amplify
