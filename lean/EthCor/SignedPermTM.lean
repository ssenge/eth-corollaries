import EthCor.SignedPerm
import EthCor.PermTM

/-! # The permanent of a {−1, 0, 1} matrix in time C·(n+2)^C·2^{εm}

The input is a bit b, then n in unary, then the n² entries of A (nonzero) and of Sg (−1), row by row.
The front end `leafS` writes `sF` on m + 1 + 2r ≤ 3m + 1 variables with s = n + r; Anthropic's counter
`SIZED` (width 3) counts its solutions, which are the permutations along nonzero entries with an
even (b = 0) or odd (b = 1) number of −1 entries (`cnt_sperm`). The permanent is the first count
minus the second (`permanent_signed`), so two runs of one machine give it (`sperm_fpt`). Under #ETH,
the permanent of {−1, 0, 1} matrices with m nonzero entries cannot be computed in time exp(o(m))
[Dell, Husfeldt, Marx, Taslaman, Wahlén, TALG 2014, Thm 1.3]. -/

namespace EthCor.SPermTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Perm
  EthCor.SPerm EthCor.PermTM

/-! ### The front end -/

def bS (x : List Bool) : Bool := x.headD false
def nS (x : List Bool) : ℕ := GraphProblems.ones x.tail
def ES (x : List Bool) : List (ℕ × ℕ) := ents (nS x) ((rest x.tail).take (nS x * nS x))
def gS (x : List Bool) : List ℕ := negs (nS x) ((rest x.tail).drop (nS x * nS x)) (ES x)

/-- The counter's input: `sF` with the size n + r, or a formula without solution if m < n. -/
def leafS (x : List Bool) : List Unit × ℕ × Fml :=
  if nS x ≤ (ES x).length then
    (List.replicate ((ES x).length + 1 + (gS x).length + (gS x).length) (), nS x + (gS x).length, sF (ES x) (gS x) (bS x))
  else ([], 0, [[]])

def spermM (ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn leafS (FromPrinted.Consequences.SIZED 3 ℓ τ)) Nat.bits

/-! ### Polynomial time -/

section Poly

variable {α : Type} [Enc α]

theorem xorC_polyT {c a x : α → ℕ} (hc : PolyT c) (ha : PolyT a) (hx : PolyT x) :
    PolyT fun p => xorC (c p) (a p) (x p) := by unfold xorC; fun_prop

theorem compC_polyT {p q : α → ℕ} (hp : PolyT p) (hq : PolyT q) : PolyT fun z => compC (p z) (q z) := by
  unfold compC; fun_prop

theorem chainF_polyT {m : α → ℕ} {g : α → List ℕ} {b : α → Bool} (hm : PolyT m) (hg : PolyT g) (hb : PolyT b) :
    PolyT fun a => chainF (m a) (g a) (b a) := by
  have hL : Unary fun a => (g a).length := Unary.of_length hg
  have hL' := hL.poly
  have h1 : PolyT fun a => (List.range (g a).length).flatMap fun k => xorC (m a + 1 + k) (m a + k) ((g a).getD k 0) :=
    PolyT.flatMap (xorC_polyT (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.range hL)
  have h2 : PolyT fun a => (List.range (g a).length).flatMap fun k => compC (m a + 1 + k) (m a + 1 + (g a).length + k) :=
    PolyT.flatMap (compC_polyT (by fun_prop) (by fun_prop)) (PolyT.range hL)
  unfold chainF
  exact PolyT.append (PolyT.append (PolyT.append (by fun_prop) h1) h2) (by fun_prop)

theorem negs_polyT {n : α → ℕ} {mS : α → List Bool} {E : α → List (ℕ × ℕ)} (hn : PolyT n) (hmS : PolyT mS)
    (hE : PolyT E) : PolyT fun a => negs (n a) (mS a) (E a) := by
  have hL : Unary fun a => (E a).length := Unary.of_length hE
  have hd : PolyT fun q : α × ℕ => adjB (n q.1) (mS q.1) ((E q.1).getD q.2 (0, 0)).1 ((E q.1).getD q.2 (0, 0)).2 := by
    fun_prop
  unfold negs
  exact PolyT.filter hd (PolyT.range hL)

end Poly

theorem bS_polyT : PolyT bS := by unfold bS; fun_prop

theorem nS_unary : Unary nS := by unfold nS; exact ones_unary (by fun_prop)

theorem ES_polyT : PolyT ES := by
  have hn' := nS_unary.poly
  unfold ES; exact ents_polyT nS_unary (by fun_prop)

theorem gS_polyT : PolyT gS := by
  have hn' := nS_unary.poly
  unfold gS; exact negs_polyT hn' (by fun_prop) ES_polyT

theorem sFS_polyT : PolyT fun x => sF (ES x) (gS x) (bS x) := by
  have hL' := (Unary.of_length ES_polyT).poly
  unfold sF
  exact PolyT.append (permF_polyT ES_polyT) (chainF_polyT hL' gS_polyT bS_polyT)

theorem leafS_then_polyT : PolyT fun x => (List.replicate ((ES x).length + 1 + (gS x).length + (gS x).length) (),
    nS x + (gS x).length, sF (ES x) (gS x) (bS x)) := by
  have hL : Unary fun x => (ES x).length := Unary.of_length ES_polyT
  have hr : Unary fun x => (gS x).length := Unary.of_length gS_polyT
  have hN : Unary fun x => (ES x).length + 1 + (gS x).length + (gS x).length :=
    ((hL.add (Unary.const 1)).add hr).add hr
  exact PolyT.prodMk hN (PolyT.prodMk (PolyT.add nS_unary.poly hr.poly) sFS_polyT)

theorem leafS_polyT : PolyT leafS := by
  have hc := decle_polyT nS_unary.poly (Unary.of_length ES_polyT).poly
  unfold leafS
  exact PolyT.ite' (c := fun x => nS x ≤ (ES x).length) (g := fun _ => (([] : List Unit), 0, [[]]))
    hc leafS_then_polyT (PolyT.const _)

@[instance_reducible] def isPolyT_spermM (ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED 3 ℓ τ)] :
    IsPolyT (spermM ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED 3 ℓ τ) leafS_polyT
  IsPolyT.mapOut (M := Stepped.mapIn leafS (FromPrinted.Consequences.SIZED 3 ℓ τ)) GraphProblems.bits_polyT

/-! ### Facts on the formula -/

theorem negs_lt' (n : ℕ) (mS : List Bool) (E : List (ℕ × ℕ)) :
    ∀ k < (negs n mS E).length, (negs n mS E).getD k 0 < E.length := by
  intro k hk
  rw [List.getD_eq_getElem _ _ hk]
  exact List.mem_range.1 (List.mem_of_mem_filter (List.getElem_mem hk))

theorem length_negs_le (n : ℕ) (mS : List Bool) (E : List (ℕ × ℕ)) : (negs n mS E).length ≤ E.length :=
  (List.length_filter_le _ _).trans (by simp)

theorem length_chainF (m : ℕ) (g : List ℕ) (b : Bool) : (chainF m g b).length = 6 * g.length + 2 := by
  simp only [chainF, xorC, compC, List.length_append, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem shaped_chainF (m : ℕ) (g : List ℕ) (b : Bool) (hg : ∀ k < g.length, g.getD k 0 < m) :
    Shaped 3 (m + 1 + g.length + g.length) (chainF m g b) := by
  intro C hC
  simp only [chainF, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at hC
  rcases hC with ((rfl | ⟨k, hk, hC⟩) | ⟨k, hk, hC⟩) | rfl
  · refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega
  · have := hg k hk
    simp only [xorC, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, fun l hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rcases hl with rfl | rfl | rfl <;> simp only <;> omega⟩
  · simp only [compC, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;>
      exact ⟨by simp, fun l hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rcases hl with rfl | rfl <;> simp only <;> omega⟩
  · refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega

theorem shaped_sF (E : List (ℕ × ℕ)) (g : List ℕ) (b : Bool) (hg : ∀ k < g.length, g.getD k 0 < E.length) :
    Shaped 3 (E.length + 1 + g.length + g.length) (sF E g b) := by
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨h1, h2⟩ := shaped_permF E C hC
    exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · exact shaped_chainF _ g b hg C hC

/-! ### The theorem -/

/-- **The {−1, 0, 1} permanent in 2^{εm}·poly(n).** For every ε > 0 there are C and one Turing
machine with finite alphabets: given a bit b, n in unary and the entries of A (nonzero) and Sg (−1),
it outputs the number of permutations along nonzero entries with an even (b = 0) or odd (b = 1)
number of −1 entries, within ⌊C·(n+2)^C·2^{εm}⌋ steps, m the number of nonzero entries. The
permanent of the matrix (Mathlib's `Matrix.permanent`, over ℤ) is the count for b = 0 minus the count
for b = 1. -/
theorem sperm_fpt {ε : ℝ} (hε : 0 < ε) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (A Sg : Fin n → Fin n → Bool),
      (Matrix.of fun i j => if A i j then (if Sg i j then -1 else 1) else 0 : Matrix (Fin n) (Fin n) ℤ).permanent =
        (numPar A Sg false : ℤ) - numPar A Sg true ∧
      ∀ b : Bool, Wrap.Outputs M (b :: (unary n ++ (Hom.hmat A ++ Hom.hmat Sg))) (Nat.bits (numPar A Sg b))
        ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C *
          (2 : ℝ) ^ (ε * (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card)⌋₊ := by
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 3 (show 0 < ε / 3 by positivity)
  have := isPolyT_spermM ℓ τ
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, (c : ℝ) * (2 : ℝ) ^ (ε / 3) ≤ c₀ := exists_nat_ge _
  let ι := Σ n : ℕ, (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) × Bool
  suffices hrun : ∀ x : ι, ∃ T S : ℕ,
      (spermM ℓ τ).Runs (x.2.2.2 :: (unary x.1 ++ (Hom.hmat x.2.1 ++ Hom.hmat x.2.2.1))) T S
        (Nat.bits (numPar x.2.1 x.2.2.1 x.2.2.2)) ∧
      (x.2.2.2 :: (unary x.1 ++ (Hom.hmat x.2.1 ++ Hom.hmat x.2.2.1))).length + S + 1 ≤ (c + 3) * (x.1 + 2) ^ (4 * c + 2) ∧
      (T : ℝ) ≤ c₀ * (2 : ℝ) ^ (ε * (univ.filter fun p : Fin x.1 × Fin x.1 => x.2.1 p.1 p.2 = true).card) by
    obtain ⟨N, C, hfin, hN⟩ := EthCor.VcTM.tm_fpt (spermM ℓ τ) (ι := ι)
      (fun x => x.2.2.2 :: (unary x.1 ++ (Hom.hmat x.2.1 ++ Hom.hmat x.2.2.1)))
      (fun x => Nat.bits (numPar x.2.1 x.2.2.1 x.2.2.2))
      (fun x => x.1) (fun x => (univ.filter fun p : Fin x.1 × Fin x.1 => x.2.1 p.1 p.2 = true).card)
      hε.le c₀ (c + 3) (4 * c + 2) hrun
    exact ⟨N, C, hfin, fun n A Sg => ⟨permanent_signed A Sg, fun b => hN ⟨n, A, Sg, b⟩⟩⟩
  rintro ⟨n, A, Sg, b⟩
  dsimp only
  -- what the front end reads
  obtain ⟨w, hw⟩ : ∃ w, w = unary n ++ (Hom.hmat A ++ Hom.hmat Sg) := ⟨_, rfl⟩
  rw [← hw]
  have hb : bS (b :: w) = b := rfl
  have hn : nS (b :: w) = n := by rw [nS, List.tail_cons, hw]; exact Read.ones_unary_append n _
  have hr : rest (b :: w).tail = Hom.hmat A ++ Hom.hmat Sg := by rw [List.tail_cons, hw]; exact Read.rest_unary_append n _
  have hE : ES (b :: w) = ents n (Hom.hmat A) := by
    rw [ES, hn, hr, List.take_left' (Hom.length_hmat A)]
  have hg : gS (b :: w) = negs n (Hom.hmat Sg) (ents n (Hom.hmat A)) := by
    rw [gS, hn, hr, List.drop_left' (Hom.length_hmat A), hE]
  have hcnt := cnt_sperm A Sg b
  have hm := length_ents A
  obtain ⟨m, hmdef⟩ : ∃ m, m = (ents n (Hom.hmat A)).length := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length := ⟨_, rfl⟩
  rw [← hmdef] at hm
  have hrm : r ≤ m := hrdef ▸ hmdef ▸ length_negs_le _ _ _
  -- sizes
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  have hmn : m ≤ n * n := by
    rw [hm]
    have := card_le_univ (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true)
    simpa using this
  have hlen : (b :: w).length = n + 2 + 2 * (n * n) := by
    rw [hw]; simp [unary, Hom.length_hmat]; omega
  have hX4 : n * n * (n * n) + 9 * (n * n) + 5 ≤ X ^ 4 := by
    have : X ^ 4 = n * n * (n * n) + 8 * (n * n * n) + 24 * (n * n) + 32 * n + 16 := by rw [hX]; ring
    omega
  have hX2 : X ^ 2 = n * n + 4 * n + 4 := by rw [hX]; ring
  have hq1 : X ^ 2 ≤ X ^ (4 * c + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hq2 : c * X ^ (4 * c) ≤ c * X ^ (4 * c + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have he : (c + 3) * X ^ (4 * c + 2) = c * X ^ (4 * c + 2) + 3 * X ^ (4 * c + 2) := by ring
  have hpow : ∀ y, y ≤ X ^ 4 → c * y ^ c ≤ c * X ^ (4 * c) := fun y hy => by
    rw [pow_mul]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card) :=
    Real.one_le_rpow one_le_two (by positivity)
  have hc0 : (c : ℝ) ≤ c₀ := le_trans (le_mul_of_one_le_right (Nat.cast_nonneg c)
    (Real.one_le_rpow one_le_two (by positivity))) hc₀
  by_cases hnm : n ≤ m
  · have hleaf : leafS (b :: w) = (List.replicate (m + 1 + r + r) (), n + r,
        sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b) := by
      rw [leafS, hn, hE, hg, hb, ← hmdef, ← hrdef, if_pos hnm]
    obtain ⟨T, hrunT, hT⟩ := hc (m + 1 + r + r) (n + r) (sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b)
      (by omega) (by rw [hmdef, hrdef]; exact shaped_sF _ _ b (negs_lt' _ _ _))
    rw [← hleaf] at hrunT
    have wo := Stepped.mapOut_runs (f := Nat.bits) (Stepped.mapIn_runs (f := leafS) hrunT)
    have hout : cntS (m + 1 + r + r) (n + r)
        (sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b) = numPar A Sg b := by
      rw [hmdef, hrdef]; exact hcnt
    rw [hout] at wo
    refine ⟨T, _, wo, ?_, ?_⟩
    · have hψ : (sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b).length ≤ m * m + 6 * r + 2 := by
        rw [sF, List.length_append, length_chainF, ← hrdef]
        have := length_permF_le (ents n (Hom.hmat A))
        rw [← hmdef] at this
        omega
      have hmm : m * m ≤ n * n * (n * n) := Nat.mul_le_mul hmn hmn
      have := hpow (m + 1 + r + r + (sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b).length + 2)
        (by omega)
      rw [hlen, ← hX, he]
      omega
    · refine hT.trans ?_
      have hN : (((m + 1 + r + r : ℕ) : ℝ)) ≤ 3 * m + 1 := by
        have : m + 1 + r + r ≤ 3 * m + 1 := by omega
        exact_mod_cast this
      have hE' : ε / 3 * ((m + 1 + r + r : ℕ) : ℝ) ≤ ε / 3 + ε * m := by nlinarith
      calc (c : ℝ) * (2 : ℝ) ^ (ε / 3 * ((m + 1 + r + r : ℕ) : ℝ)) ≤ c * (2 : ℝ) ^ (ε / 3 + ε * m) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hE') (Nat.cast_nonneg c)
        _ = c * (2 : ℝ) ^ (ε / 3) * (2 : ℝ) ^ (ε * m) := by rw [Real.rpow_add two_pos]; ring
        _ ≤ c₀ * (2 : ℝ) ^ (ε * m) := mul_le_mul_of_nonneg_right hc₀ (by positivity)
        _ = _ := by rw [hm]
  · have hleaf : leafS (b :: w) = ([], 0, [[]]) := by
      rw [leafS, hn, hE, ← hmdef, if_neg hnm]
    obtain ⟨T, hrunT, hT⟩ := hc 0 0 [[]] le_rfl (by
      intro C hC; rw [List.mem_singleton] at hC; subst hC; simp)
    have e0 : (List.replicate 0 () : List Unit) = [] := rfl
    rw [e0, ← hleaf] at hrunT
    have wo := Stepped.mapOut_runs (f := Nat.bits) (Stepped.mapIn_runs (f := leafS) hrunT)
    have h0 : numPar A Sg b = 0 := by
      have h1 := cntS_permF A
      rw [← hmdef, cntS_zero_of_lt _ (show m < n by omega)] at h1
      refine Nat.eq_zero_of_le_zero ?_
      calc numPar A Sg b ≤ (univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, A (σ i) i = true).card := by
            unfold numPar
            exact card_le_card fun σ hσ => by
              simp only [mem_filter, mem_univ, true_and] at hσ ⊢; exact hσ.1
        _ = 0 := h1.symm
    have hout : Nat.bits (cntS 0 0 [[]]) = Nat.bits (numPar A Sg b) := by rw [cntS_dead, h0]
    rw [hout] at wo
    refine ⟨T, _, wo, ?_, ?_⟩
    · have h16 : 2 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have := hpow (0 + ([[]] : Fml).length + 2) (by simp only [List.length_singleton]; omega)
      rw [hlen, ← hX, he]
      omega
    · refine hT.trans ?_
      simp only [CharP.cast_eq_zero, mul_zero, Real.rpow_zero, mul_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) c]

end EthCor.SPermTM
