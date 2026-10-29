import EthCor.ForestFormula
import EthCor.ConnIsoTM

/-! # The parity of the number of induced forests in time C·2^{δn}, for O(n) edges

The input is the code of G, then s in unary. The front end `preF` writes the formula
`fvsF n E []` of `EthCor.Forest` on 3n + 2m variables (m the number of edges) with the target
n + s + m. Anthropic's machine `FromPrinted.Consequences.SIZED` counts its satisfying assignments
with that many true variables, and the last step, which reads s again from the input, keeps bit s of
the count. By `Forest.fvs_parity` this bit is the parity of the number of vertex sets X of size s
with G[X] a forest, i.e. of the feedback vertex sets of size n − s (`for_parity_tm`). With at most
D·n edges the formula has at most (2D + 3)·n variables. -/

namespace EthCor.ForestTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Ham EthCor.HamTM
  EthCor.HamITM EthCor.Conn EthCor.ConnTM EthCor.ConnI EthCor.ConnITM EthCor.Forest

open Classical in
/-- The vertex sets of size s that induce a forest. -/
noncomputable def numFor {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (univ.filter fun v => x v = true).card = s ∧
    (G.induce {v | x v = true}).IsAcyclic).card

theorem numFor_eq {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) : numFor G s = numForF G [] s := by
  unfold numFor numForF
  congr 1
  ext x
  simp

/-! ### The front end and the last step -/

def preF (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x + nH x + nH x + (EH x).length + (EH x).length) (), nH x + lC x + (EH x).length,
    fvsF (nH x) (EH x) [])

/-- Bit s of the count, s read from the input. -/
def postF (p : List Bool × ℕ) : List Bool := [decide (p.2 / 2 ^ lC p.1 % 2 = 1)]

section Poly

variable {α : Type} [Enc α]

theorem ebF_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : PolyT n) (hE : PolyT E) :
    PolyT fun a => ebF (n a) (E a) := by
  have hm : Unary fun a => (E a).length := Unary.of_length hE
  have h : PolyT fun p : α × ℕ => [[(n p.1 + n p.1 + n p.1 + p.2, false), (((E p.1).getD p.2 (0, 0)).1, true)],
      [(n p.1 + n p.1 + n p.1 + p.2, false), (((E p.1).getD p.2 (0, 0)).2, true)]] := by fun_prop
  unfold ebF
  exact PolyT.flatMap h (PolyT.range hm)

theorem fvsF_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} {ψ : α → Fml} (hn : Unary n) (hE : PolyT E)
    (hψ : PolyT ψ) : PolyT fun a => fvsF (n a) (E a) (ψ a) := by
  have hm : Unary fun a => (E a).length := Unary.of_length hE
  have hn' := hn.poly
  unfold fvsF
  exact PolyT.append (PolyT.append (connF_polyT hn hE hψ) (ebF_polyT hn' hE))
    (compF_polyT (by fun_prop) hm)

end Poly

theorem preF_polyT : PolyT preF := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have hm : Unary fun x => (EH x).length := Unary.of_length hE
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x + (EH x).length + (EH x).length) () :=
    (((hn.add hn).add hn).add hm).add hm
  have h2 : PolyT fun x => nH x + lC x + (EH x).length := PolyT.add (PolyT.add hn.poly hl) hm.poly
  have h3 : PolyT fun x => fvsF (nH x) (EH x) [] := fvsF_polyT hn hE (by fun_prop)
  exact PolyT.prodMk h1 (PolyT.prodMk h2 h3)

theorem lC_unary : Unary lC := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have h : PolyT fun x => (sI x).takeWhile id := by fun_prop
  exact Unary.of_length h

theorem postF_polyT : PolyT postF := by
  have hl : Unary fun p : List Bool × ℕ => lC p.1 := lC_unary.comp (PolyT.fst PolyT.id')
  have h2 : PolyT fun p : List Bool × ℕ => p.2 := PolyT.snd PolyT.id'
  have hp : PolyT fun p : List Bool × ℕ => p.2 / 2 ^ lC p.1 % 2 :=
    PolyT.mod (PolyT.div h2 (PolyT.pow_unary (PolyT.const _) hl)) (PolyT.const _)
  have hd : PolyT fun p : List Bool × ℕ => decide (p.2 / 2 ^ lC p.1 % 2 = 1) := PolyT.decide_eq hp (PolyT.const _)
  unfold postF
  exact PolyT.cons' hd (PolyT.const _)

/-- Prepare, count with `SIZED`, keep bit s. -/
def forM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (Stepped.mapIn preF (FromPrinted.Consequences.SIZED w ℓ τ)) (Stepped.ofFun postF)

@[instance_reducible] def isPolyT_forM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (forM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preF_polyT
  haveI := IsPolyT.ofFun postF_polyT
  IsPolyT.bind (M := Stepped.mapIn preF (FromPrinted.Consequences.SIZED w ℓ τ)) (N := Stepped.ofFun postF)

theorem read_for {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) :
    preF (code G ++ unary s) = (List.replicate (n + n + n + (edges n (matrix G)).length +
      (edges n (matrix G)).length) (), n + s + (edges n (matrix G)).length, fvsF n (edges n (matrix G)) []) ∧
    lC (code G ++ unary s) = s := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary s)
  have h1 : ones (unary s) = s := by simpa using Read.ones_unary_append s []
  refine ⟨?_, by rw [lC, hs, h1]⟩
  rw [preF, lC, hn, hE, hs, h1]

/-! ### Sizes -/

theorem shaped_fvs {n : ℕ} (G : SimpleGraph (Fin n)) :
    Shaped 4 (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
      (fvsF n (edges n (matrix G)) []) := by
  have hE := edges_bound n (matrix G)
  intro C hC
  simp only [fvsF, List.mem_append] at hC
  rcases hC with (hC | hC) | hC
  · have h := shaped_connF (r := 0) G ([] : Sat3.CNF n) (by simp) C hC
    exact ⟨h.1, fun l hl => by have := h.2 l hl; omega⟩
  · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    refine ⟨?_, fun l hl => by have := ebF_vars hE C (List.mem_flatMap.2 ⟨i, hi, hC⟩) l hl; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> simp
  · rw [compF] at hC
    obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> dsimp only <;> omega

theorem length_fvsF {n : ℕ} (E : List (ℕ × ℕ)) :
    (fvsF n E []).length = 3 * n + 6 * E.length := by
  simp only [fvsF, List.length_append, length_connF_le, ebF, compF, List.length_flatMap, List.length_cons,
    List.length_nil]
  simp; ring

/-! ### The theorem -/

open Classical in
/-- **The parity of the number of induced forests in time C·2^{δn}, for O(n) edges.** For every D
and δ > 0, one Turing machine with finite alphabets: given a graph G on n vertices with at most D·n
edges and s ≤ n in unary, it outputs whether the number of vertex sets X of size s with G[X] a forest
(the complements of the feedback vertex sets of size n − s) is odd, within ⌊C·2^{δn}⌋ steps. -/
theorem for_parity_tm (D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n s : ℕ) (G : SimpleGraph (Fin n)), s ≤ n → G.edgeFinset.card ≤ D * n →
      Wrap.Outputs M (code G ++ unary s) [decide (numFor G s % 2 = 1)] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 4
    (show 0 < δ / (2 * (2 * D + 3)) by positivity)
  have := isPolyT_forM 4 ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * 8 ^ c + 2 * c + 20 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // p.1 ≤ n ∧ p.2.edgeFinset.card ≤ D * n}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (forM 4 ℓ₀ τ).Runs (code x.2.1.2 ++ unary x.2.1.1)
      T (K * (x.1 + 2) ^ K) [decide (numFor x.2.1.2 x.2.1.1 % 2 = 1)] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (forM 4 ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (numFor x.2.1.2 x.2.1.1 % 2 = 1)]) (fun x => x.1) hδ K 6 2 (fun x => by
        have := x.2.2.1
        rw [List.length_append, length_code_eq]
        simp only [unary, List.length_append, List.length_replicate, List.length_singleton]
        nlinarith) hrun
    exact ⟨N, C', hfin, fun n s G h1 h2 => hN ⟨n, (s, G), h1, h2⟩⟩
  rintro ⟨n, ⟨s, G⟩, h1, h2⟩
  dsimp only at h1 h2 ⊢
  have hmD : (edges n (matrix G)).length ≤ D * n := (EthCor.HamSTM.length_edges_le_card G).trans h2
  have hmn := length_edges_sq (n := n) (matrix G)
  obtain ⟨hpre, hl⟩ := read_for G s
  obtain ⟨T, hT, hTle⟩ := hc (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
    (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) []) (by omega) (shaped_fvs G)
  rw [← hpre] at hT
  have hpost := ofFun_runs postF (code G ++ unary s,
    cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
      (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) []))
  have hout := bind_runs (Stepped.mapIn_runs hT) hpost
  have hval : postF (code G ++ unary s,
      cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) [])) =
      [decide (numFor G s % 2 = 1)] := by
    rw [postF, hl, fvs_parity G (by simp) s, ← numFor_eq]
  rw [hval] at hout
  refine ⟨T + 1 + 1, hout.mono le_rfl ?_, ?_⟩
  · -- the states: the input, the states of SIZED, the count
    have hcnt : size (cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) [])) ≤
        n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 2 := by
      have hle : cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
          (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) []) <
          2 ^ (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1) := by
        unfold cntS
        refine lt_of_le_of_lt (card_le_univ _) ?_
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ]
        have := Nat.one_le_two_pow (n := n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        omega
      have := Nat.size_le.2 hle
      change Nat.size _ + 1 ≤ _
      omega
    have hin : size (code G ++ unary s) = 2 * (n + 1 + n * n + (s + 1)) + 1 := by
      rw [size_bools, List.length_append, length_code_eq]
      simp [unary]
    have hF := length_fvsF (n := n) (edges n (matrix G))
    have hX : n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length +
        (fvsF n (edges n (matrix G)) []).length + 2 ≤ 8 * (n + 2) ^ 2 := by
      have : n * n + 4 * n + 4 = (n + 2) ^ 2 := by ring
      omega
    have hS : c * (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length +
        (fvsF n (edges n (matrix G)) []).length + 2) ^ c ≤ c * 8 ^ c * (n + 2) ^ (2 * c) := by
      calc _ ≤ c * (8 * (n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
        _ = c * 8 ^ c * (n + 2) ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    have hsq : (n + 2) ^ 2 ≤ (n + 2) ^ (2 * c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hsq' : (n + 2) ^ (2 * c) ≤ (n + 2) ^ (2 * c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hKK : (n + 2) ^ (2 * c + 2) ≤ (n + 2) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    have hsz : size [decide (numFor G s % 2 = 1)] = 3 := by rw [size_bools]; rfl
    have hpair : size (code G ++ unary s, cntS (n + n + n + (edges n (matrix G)).length +
        (edges n (matrix G)).length) (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) [])) =
        size (code G ++ unary s) + size (cntS (n + n + n + (edges n (matrix G)).length +
          (edges n (matrix G)).length) (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) [])) := rfl
    rw [hpair, hsz, hin]
    have e : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
    have h8 : c * 8 ^ c * (n + 2) ^ (2 * c) ≤ c * 8 ^ c * (n + 2) ^ (2 * c + 2) := Nat.mul_le_mul_left _ hsq'
    have hK2 : (c * 8 ^ c + 17) * (n + 2) ^ (2 * c + 2) ≤ K * (n + 2) ^ K :=
      Nat.mul_le_mul (by omega) hKK
    have e2 : (c * 8 ^ c + 17) * (n + 2) ^ (2 * c + 2) = c * 8 ^ c * (n + 2) ^ (2 * c + 2) +
        17 * (n + 2) ^ (2 * c + 2) := by ring
    omega
  · have hN : ((n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length : ℕ) : ℝ) ≤
        (2 * D + 3) * n := by
      have : ((edges n (matrix G)).length : ℝ) ≤ D * n := by exact_mod_cast hmD
      push_cast; nlinarith
    have hD : (0 : ℝ) < 2 * D + 3 := by positivity
    have hexp : δ / (2 * (2 * D + 3)) *
        ((n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length : ℕ) : ℝ) ≤ δ / 2 * n := by
      calc δ / (2 * (2 * D + 3)) * ((n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length : ℕ) : ℝ)
          ≤ δ / (2 * (2 * D + 3)) * ((2 * D + 3) * n) := mul_le_mul_of_nonneg_left hN (by positivity)
        _ = δ / 2 * n := by field_simp
    have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow (by norm_num) (by positivity)
    have hcK : (c : ℝ) + 2 ≤ K := by exact_mod_cast (show c + 2 ≤ K by omega)
    push_cast
    calc (T : ℝ) + 1 + 1 ≤ c * (2 : ℝ) ^ (δ / 2 * n) + 2 :=
          by linarith [hTle.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
            (Nat.cast_nonneg c))]
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) := by nlinarith

/-! ### Feedback vertex sets -/

open Classical in
/-- The feedback vertex sets of G with k vertices: removing them leaves a forest. -/
noncomputable def numFVS {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  (univ.filter fun X : Finset (Fin n) => X.card = k ∧ (G.induce {v | v ∉ X}).IsAcyclic).card

/-- The feedback vertex sets of size k are the complements of the induced forests of size n − k. -/
theorem numFVS_eq {n : ℕ} (G : SimpleGraph (Fin n)) {k : ℕ} (hk : k ≤ n) : numFVS G k = numFor G (n - k) := by
  unfold numFVS numFor
  refine Finset.card_nbij' (fun X v => decide (v ∉ X)) (fun x => univ.filter fun v => x v = false) ?_ ?_ ?_ ?_
  · intro X hX
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hX ⊢
    have e : (univ.filter fun v => decide (v ∉ X) = true) = Xᶜ := by ext v; simp
    have e2 : ({v | decide (v ∉ X) = true} : Set (Fin n)) = {v | v ∉ X} := by ext v; simp
    refine ⟨by rw [e, card_compl, Fintype.card_fin, hX.1], by rw [e2]; exact hX.2⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have e : (univ.filter fun v => x v = false) = (univ.filter fun v => x v = true)ᶜ := by ext v; simp
    have e2 : ({v | v ∉ univ.filter fun v => x v = false} : Set (Fin n)) = {v | x v = true} := by ext v; simp
    refine ⟨by rw [e, card_compl, Fintype.card_fin, hx.1]; omega, by rw [e2]; exact hx.2⟩
  · intro X _
    ext v; simp
  · intro x _
    funext v; cases h : x v <;> simp [h]

open Classical in
/-- Induced forests are closed under removing vertices: there is a feedback vertex set with at most
k ≤ n vertices iff there is an induced forest with exactly n − k vertices. -/
theorem fvs_iff {n : ℕ} (G : SimpleGraph (Fin n)) {k : ℕ} (hk : k ≤ n) :
    (∃ X : Finset (Fin n), X.card ≤ k ∧ (G.induce {v | v ∉ X}).IsAcyclic) ↔ 0 < numFor G (n - k) := by
  unfold numFor
  rw [card_pos]
  constructor
  · rintro ⟨X, hX, hA⟩
    obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq (s := Xᶜ) (n := n - k)
      (by rw [card_compl, Fintype.card_fin]; omega)
    refine ⟨fun v => decide (v ∈ Z), mem_filter.2 ⟨mem_univ _, ?_, ?_⟩⟩
    · convert hZc using 2; ext v; simp
    · have hle : ({v | decide (v ∈ Z) = true} : Set (Fin n)) ≤ {v | v ∉ X} := fun v hv => by
        simpa using hZ (by simpa using hv)
      exact hA.embedding (G.induceHomOfLE hle)
  · rintro ⟨x, hx⟩
    obtain ⟨hc, hA⟩ := (mem_filter.1 hx).2
    refine ⟨univ.filter fun v => x v = false, ?_, ?_⟩
    · have e : (univ.filter fun v => x v = false) = (univ.filter fun v => x v = true)ᶜ := by ext v; simp
      rw [e, card_compl, Fintype.card_fin, hc]; omega
    · have e2 : ({v | v ∉ univ.filter fun v => x v = false} : Set (Fin n)) = {v | x v = true} := by ext v; simp
      rw [e2]; exact hA

open Classical in
/-- **The parity of the number of feedback vertex sets in time C·2^{δn}, for O(n) edges.** For every
D and δ > 0, one Turing machine with finite alphabets: given a graph G on n vertices with at most D·n
edges and n − k in unary (k ≤ n), it outputs whether G has an odd number of feedback vertex sets with
k vertices, within ⌊C·2^{δn}⌋ steps. -/
theorem fvs_parity_tm (D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), k ≤ n → G.edgeFinset.card ≤ D * n →
      Wrap.Outputs M (code G ++ unary (n - k)) [decide (numFVS G k % 2 = 1)] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M, C, hfin, hM⟩ := for_parity_tm D hδ
  exact ⟨M, C, hfin, fun n k G hk hm => by rw [numFVS_eq G hk]; exact hM n (n - k) G (by omega) hm⟩

end EthCor.ForestTM
