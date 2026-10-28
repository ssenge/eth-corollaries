import EthCor.Perm
import EthCor.VcTM

/-! # The permanent of a 0/1 matrix in time C·(n+2)^C·2^{εm}

The input is n in unary followed by the n² entries of A, row by row. The front end `leafP` lists the
m ones of A and writes the 2-CNF `permF` on m variables with s = n; Anthropic's counter
`FromPrinted.Consequences.SIZED` counts its solutions with exactly n true variables in c·2^{εm}
steps, and `Nat.bits` writes the count. If m < n the permanent is 0 and the front end writes a formula
with no solution. The FPT host `tm_fpt` makes one Turing machine of it (`perm_fpt`). Under #ETH the
permanent of 0/1 matrices with m nonzero entries cannot be computed in time exp(o(m/log n))
[Dell, Husfeldt, Marx, Taslaman, Wahlén, TALG 2014, Thm 1.3]. -/

namespace EthCor.PermTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Perm

/-! ### The front end -/

def nP (x : List Bool) : ℕ := GraphProblems.ones x
def EP (x : List Bool) : List (ℕ × ℕ) := ents (nP x) (rest x)

/-- The counter's input: the formula on the ones of A and the size n, or a formula without solution. -/
def leafP (x : List Bool) : List Unit × ℕ × Fml :=
  if nP x ≤ (EP x).length then (List.replicate (EP x).length (), nP x, permF (EP x)) else ([], 0, [[]])

def permM (ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn leafP (FromPrinted.Consequences.SIZED 2 ℓ τ)) Nat.bits

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

theorem ents_polyT {n : α → ℕ} {m : α → List Bool} (hn : Unary n) (hm : PolyT m) :
    PolyT fun a => ents (n a) (m a) := by
  have hn' := hn.poly
  have hd : PolyT fun q : α × (ℕ × ℕ) => adjB (n q.1) (m q.1) q.2.1 q.2.2 := by fun_prop
  unfold ents
  exact PolyT.filter hd (pairs_polyT hn)

theorem permF_polyT {E : α → List (ℕ × ℕ)} (hE : PolyT E) : PolyT fun a => permF (E a) := by
  have hL : Unary fun a => (E a).length := Unary.of_length hE
  have hd : PolyT fun q : α × (ℕ × ℕ) =>
      decide (q.2.1 < q.2.2) && clash ((E q.1).getD q.2.1 (0, 0)) ((E q.1).getD q.2.2 (0, 0)) := by
    unfold clash; fun_prop
  have hf : PolyT fun q : α × (ℕ × ℕ) => [(q.2.1, false), (q.2.2, false)] := by fun_prop
  unfold permF
  exact PolyT.map hf (PolyT.filter hd (pairs_polyT hL))

theorem decle_polyT {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT fun a => decide (f a ≤ g a) := by
  fun_prop

end Poly

theorem leafP_polyT : PolyT leafP := by
  have hn : Unary nP := ones_unary PolyT.id'
  have hn' := hn.poly
  have hE : PolyT EP := by unfold EP; exact ents_polyT hn (by fun_prop)
  have hL : Unary fun x => (EP x).length := Unary.of_length hE
  have hL' := hL.poly
  have h1 : PolyT fun x => (List.replicate (EP x).length (), nP x, permF (EP x)) :=
    PolyT.prodMk hL (PolyT.prodMk hn' (permF_polyT hE))
  exact PolyT.ite' (c := fun x => nP x ≤ (EP x).length) (g := fun _ => (([] : List Unit), 0, [[]]))
    (decle_polyT hn' hL') h1 (PolyT.const _)

@[instance_reducible] def isPolyT_permM (ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED 2 ℓ τ)] :
    IsPolyT (permM ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED 2 ℓ τ) leafP_polyT
  IsPolyT.mapOut (M := Stepped.mapIn leafP (FromPrinted.Consequences.SIZED 2 ℓ τ)) GraphProblems.bits_polyT

/-! ### Small facts -/

theorem cntS_dead : cntS 0 0 [[]] = 0 := by simp [cntS]

theorem shaped_dead : Shaped 2 0 [[]] := by
  intro C hC
  rw [List.mem_singleton] at hC
  subst hC
  simp

theorem cntS_zero_of_lt {m s : ℕ} (ψ : Fml) (h : m < s) : cntS m s ψ = 0 := by
  unfold cntS
  rw [card_eq_zero, filter_eq_empty_iff]
  intro a _ ⟨_, hc⟩
  have := card_le_univ (univ.filter fun i : Fin m => a i = true)
  rw [Fintype.card_fin] at this
  omega

/-! ### The theorem -/

/-- **The 0/1 permanent in 2^{εm}·poly(n).** For every ε > 0 there are C and one Turing machine with
finite alphabets: given n in unary and the n² entries of A : Fin n → Fin n → Bool, it outputs in binary
the permanent of the 0/1 matrix of A (Mathlib's `Matrix.permanent`, which for a bipartite graph is its
number of perfect matchings) within ⌊C·(n+2)^C·2^{εm}⌋ steps, m the number of ones of A. -/
theorem perm_fpt {ε : ℝ} (hε : 0 < ε) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (A : Fin n → Fin n → Bool),
      Wrap.Outputs M (unary n ++ Hom.hmat A)
        (Nat.bits (Matrix.of fun i j => if A i j then 1 else 0 : Matrix (Fin n) (Fin n) ℕ).permanent)
        ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C *
          (2 : ℝ) ^ (ε * (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card)⌋₊ := by
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 2 hε
  have := isPolyT_permM ℓ τ
  let ι := Σ n : ℕ, (Fin n → Fin n → Bool)
  suffices hrun : ∀ x : ι, ∃ T S : ℕ, (permM ℓ τ).Runs (unary x.1 ++ Hom.hmat x.2) T S
      (Nat.bits (Matrix.of fun i j => if x.2 i j then 1 else 0 : Matrix (Fin x.1) (Fin x.1) ℕ).permanent) ∧
      (unary x.1 ++ Hom.hmat x.2).length + S + 1 ≤ (c + 2) * (x.1 + 2) ^ (4 * c + 2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (ε * (univ.filter fun p : Fin x.1 × Fin x.1 => x.2 p.1 p.2 = true).card) by
    obtain ⟨N, C, hfin, hN⟩ := EthCor.VcTM.tm_fpt (permM ℓ τ) (ι := ι) (fun x => unary x.1 ++ Hom.hmat x.2)
      (fun x => Nat.bits (Matrix.of fun i j => if x.2 i j then 1 else 0 : Matrix (Fin x.1) (Fin x.1) ℕ).permanent)
      (fun x => x.1) (fun x => (univ.filter fun p : Fin x.1 × Fin x.1 => x.2 p.1 p.2 = true).card)
      hε.le c (c + 2) (4 * c + 2) hrun
    exact ⟨N, C, hfin, fun n A => hN ⟨n, A⟩⟩
  rintro ⟨n, A⟩
  dsimp only
  have hn : nP (unary n ++ Hom.hmat A) = n := Read.ones_unary_append n _
  have hr : rest (unary n ++ Hom.hmat A) = Hom.hmat A := Read.rest_unary_append n _
  have hE : EP (unary n ++ Hom.hmat A) = ents n (Hom.hmat A) := by rw [EP, hn, hr]
  have hval := (permanent_eq A).trans (cntS_permF A).symm
  have hm := length_ents A
  obtain ⟨m, hmdef⟩ : ∃ m, m = (ents n (Hom.hmat A)).length := ⟨_, rfl⟩
  rw [← hmdef] at hval hm
  -- sizes
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  have hmn : m ≤ n * n := by
    rw [hm]
    have := card_le_univ (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true)
    simpa using this
  have hlen : (unary n ++ Hom.hmat A).length = n + 1 + n * n := by simp [unary, Hom.length_hmat]; omega
  have hX2 : X ^ 2 = n * n + 4 * n + 4 := by rw [hX]; ring
  have hX4 : n * n * (n * n) + n * n + 2 ≤ X ^ 4 := by
    have : X ^ 4 = n * n * (n * n) + 8 * (n * n * n) + 24 * (n * n) + 32 * n + 16 := by rw [hX]; ring
    omega
  have hq1 : X ^ 2 ≤ X ^ (4 * c + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hq2 : c * X ^ (4 * c) ≤ c * X ^ (4 * c + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have he : (c + 2) * X ^ (4 * c + 2) = c * X ^ (4 * c + 2) + 2 * X ^ (4 * c + 2) := by ring
  have hpow : ∀ y, y ≤ X ^ 4 → c * y ^ c ≤ c * X ^ (4 * c) := fun y hy => by
    rw [pow_mul]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card) :=
    Real.one_le_rpow one_le_two (by positivity)
  by_cases hnm : n ≤ m
  · have hleaf : leafP (unary n ++ Hom.hmat A) = (List.replicate m (), n, permF (ents n (Hom.hmat A))) := by
      rw [leafP, hn, hE, ← hmdef, if_pos hnm]
    obtain ⟨T, hrunT, hT⟩ := hc m n (permF (ents n (Hom.hmat A))) hnm (hmdef ▸ shaped_permF _)
    rw [← hleaf] at hrunT
    have wo := Stepped.mapOut_runs (f := Nat.bits) (Stepped.mapIn_runs (f := leafP) hrunT)
    rw [← hval] at wo
    refine ⟨T, _, wo, ?_, ?_⟩
    · have hψ : (permF (ents n (Hom.hmat A))).length ≤ m * m := hmdef ▸ length_permF_le _
      have hmm : m * m ≤ n * n * (n * n) := Nat.mul_le_mul hmn hmn
      have := hpow (m + (permF (ents n (Hom.hmat A))).length + 2) (by omega)
      rw [hlen, ← hX, he]
      omega
    · rw [hm] at hT; exact hT
  · have hleaf : leafP (unary n ++ Hom.hmat A) = ([], 0, [[]]) := by
      rw [leafP, hn, hE, ← hmdef, if_neg hnm]
    obtain ⟨T, hrunT, hT⟩ := hc 0 0 [[]] le_rfl shaped_dead
    have e0 : (List.replicate 0 () : List Unit) = [] := rfl
    rw [e0, ← hleaf] at hrunT
    have wo := Stepped.mapOut_runs (f := Nat.bits) (Stepped.mapIn_runs (f := leafP) hrunT)
    have hout : Nat.bits (cntS 0 0 [[]]) =
        Nat.bits (Matrix.of fun i j => if A i j then 1 else 0 : Matrix (Fin n) (Fin n) ℕ).permanent := by
      rw [cntS_dead, hval, cntS_zero_of_lt (permF (ents n (Hom.hmat A))) (show m < n by omega)]
    rw [hout] at wo
    refine ⟨T, _, wo, ?_, ?_⟩
    · have h16 : 2 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have := hpow (0 + ([[]] : Fml).length + 2) (by simp only [List.length_singleton]; omega)
      rw [hlen, ← hX, he]
      omega
    · refine hT.trans ?_
      simp only [CharP.cast_eq_zero, mul_zero, Real.rpow_zero, mul_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) c]

end EthCor.PermTM
