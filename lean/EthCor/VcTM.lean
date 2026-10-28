import EthCor.VcTree
import EthCor.HamIsoTM
import EthCor.HamSparseTM
import EthCor.ConnTM
import EthCor.CnfTree
import FromPrinted.Sets
import GraphProblems.Host
import GraphProblems.SetTM
import CountKSat.Host
import CountKSat.Walk

/-! # Vertex cover in time C·(n+2)^C·2^{εk}

The input is the code of G followed by k in unary. The machine `vcM` walks the tree of
`EthCor.Vc.stepV` from the node (k, edge list of G), runs Anthropic's counter
`FromPrinted.Consequences.SIZED` on the formula `leafV` of every leaf, adds the counts, and outputs
whether the sum is positive. By `good_leaves` and `cnt_leafV_pos` the sum is positive exactly if G has
a vertex cover with at most k vertices. For every ε > 0 the degree d is chosen with
(1/d)·lg(e·d) ≤ ε/4, so the tree has at most 2^{ε(k+d)/4} leaves, and the counter takes
2^{(ε/(4d))·kd} = 2^{εk/4} steps at a leaf, because a leaf has at most k·d vertices. The FPT host
`tm_fpt` turns this into one Turing machine with running time C·(n+2)^C·2^{εk} (`vc_fpt`). No
kernel is used. -/

namespace EthCor.VcTM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Turing Finset
  EthCor.Ham EthCor.HamTM EthCor.HamITM EthCor.Vc

/-! ### The host for a parameter -/

/-- **From a stepped machine to a Turing machine, with a parameter.** If M returns `out x` on
`code x` within c·2^{δ·par x} steps and the input and the states have size at most a·(sz x + 2)^e,
one Turing machine with finite alphabets does so within ⌊C·(sz x + 2)^C·2^{δ·par x}⌋ steps. -/
theorem tm_fpt (M : Stepped (List Bool) (List Bool)) [IsPolyT M] {ι : Type} (code out : ι → List Bool)
    (sz par : ι → ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (c a e : ℕ)
    (h : ∀ x, ∃ T S : ℕ, M.Runs (code x) T S (out x) ∧ (code x).length + S + 1 ≤ a * (sz x + 2) ^ e ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * par x)) :
    ∃ (N : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ ∀ x,
      Wrap.Outputs N (code x) (out x) ⌊(C : ℝ) * ((sz x : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * par x)⌋₊ := by
  obtain ⟨N', q, hfin, hP⟩ := stHostW M
  refine ⟨N', q * (c + 1) * a ^ q + e * q, hfin, fun x => ?_⟩
  obtain ⟨T, S, hr, hS, hT⟩ := h x
  obtain ⟨ev⟩ := hP (code x) T S (out x) hr
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.le_floor ?_)⟩⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (sz x : ℝ) + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hX]; linarith [Nat.cast_nonneg (α := ℝ) (sz x)]
  have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * par x) := Real.one_le_rpow one_le_two (by positivity)
  have h1 : (T : ℝ) + 1 ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ (δ * par x) := by nlinarith
  have hS' : (((code x).length + S + 1 : ℕ) : ℝ) ≤ (a : ℝ) * X ^ e := by
    rw [hX]; exact_mod_cast hS
  have h2 : (((code x).length + S + 1 : ℕ) : ℝ) ^ q ≤ (a : ℝ) ^ q * X ^ (e * q) := by
    calc (((code x).length + S + 1 : ℕ) : ℝ) ^ q ≤ ((a : ℝ) * X ^ e) ^ q := by gcongr
      _ = (a : ℝ) ^ q * X ^ (e * q) := by rw [mul_pow, ← pow_mul]
  have h3 : X ^ (e * q) ≤ X ^ (q * (c + 1) * a ^ q + e * q) := pow_le_pow_right₀ hX1 (by omega)
  rw [← hX]
  calc ((q * (T + 1) * ((code x).length + S + 1) ^ q : ℕ) : ℝ)
      = (q : ℝ) * ((T : ℝ) + 1) * ((((code x).length + S + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (((c : ℝ) + 1) * (2 : ℝ) ^ (δ * par x)) * ((a : ℝ) ^ q * X ^ (e * q)) := by gcongr
    _ = ((q * (c + 1) * a ^ q : ℕ) : ℝ) * X ^ (e * q) * (2 : ℝ) ^ (δ * par x) := by push_cast; ring
    _ ≤ ((q * (c + 1) * a ^ q + e * q : ℕ) : ℝ) * X ^ (q * (c + 1) * a ^ q + e * q) * (2 : ℝ) ^ (δ * par x) := by
        gcongr
        · exact_mod_cast Nat.le_add_right _ _

/-! ### The steps are polynomial-time -/

section Poly

variable {α : Type} [Enc α]

theorem nbs_polyT {E : α → List (ℕ × ℕ)} {v : α → ℕ} (hE : PolyT E) (hv : PolyT v) :
    PolyT fun a => nbs (E a) (v a) := by
  unfold nbs; fun_prop

theorem cand_polyT {E : α → List (ℕ × ℕ)} (hE : PolyT E) : PolyT fun a => cand (E a) := by
  unfold cand; fun_prop

theorem verts_polyT {E : α → List (ℕ × ℕ)} (hE : PolyT E) : PolyT fun a => verts (E a) := by
  have := cand_polyT hE
  unfold verts; fun_prop

theorem delV_polyT {E : α → List (ℕ × ℕ)} {v : α → ℕ} (hE : PolyT E) (hv : PolyT v) :
    PolyT fun a => delV (E a) (v a) := by
  unfold delV; fun_prop

theorem delN_polyT {E : α → List (ℕ × ℕ)} {v k : α → ℕ} (hE : PolyT E) (hv : PolyT v) (hk : PolyT k) :
    PolyT fun a => delN (E a) (v a) (k a) := by
  have hN := nbs_polyT hE hv
  have hE' : PolyT fun p : α × (ℕ × ℕ) => E p.1 := by fun_prop
  have hv' : PolyT fun p : α × (ℕ × ℕ) => v p.1 := by fun_prop
  have hN' : PolyT fun p : α × (ℕ × ℕ) => nbs (E p.1) (v p.1) := nbs_polyT hE' hv'
  unfold delN; fun_prop

theorem vcClauses_polyT {E : α → List (ℕ × ℕ)} (hE : PolyT E) : PolyT fun a => vcClauses (E a) := by
  have hE' : PolyT fun p : α × (ℕ × ℕ) => E p.1 := by fun_prop
  have hV : PolyT fun p : α × (ℕ × ℕ) => verts (E p.1) := verts_polyT hE'
  unfold vcClauses; fun_prop

end Poly

theorem pick_polyT (d : ℕ) : PolyT (pick d) := by
  have hN : PolyT fun p : VNode × ℕ => nbs p.1.2 p.2 := nbs_polyT (by fun_prop) (by fun_prop)
  have hc : PolyT fun x : VNode => cand x.2 := cand_polyT (by fun_prop)
  unfold pick; fun_prop

theorem stepV_polyT (d : ℕ) : PolyT (stepV d) := by
  have hp := pick_polyT d
  have h1 : PolyT fun p : VNode × ℕ => delV p.1.2 p.2 := delV_polyT (by fun_prop) (by fun_prop)
  have h2 : PolyT fun p : VNode × ℕ => delN p.1.2 p.2 p.1.1 := delN_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun p : VNode × ℕ => nbs p.1.2 p.2 := nbs_polyT (by fun_prop) (by fun_prop)
  unfold stepV; fun_prop

theorem leafV_polyT (d : ℕ) : PolyT (leafV d) := by
  have hV : PolyT fun x : VNode => verts x.2 := verts_polyT (by fun_prop)
  have hU : PolyT fun x : VNode => List.replicate (verts x.2).length () := Unary.of_length hV
  have hC : PolyT fun x : VNode => vcClauses x.2 := vcClauses_polyT (by fun_prop)
  unfold leafV; fun_prop

/-- The root: (k, the edge list of G). -/
def rootV (x : List Bool) : VNode := (GraphProblems.ones (sI x), EH x)

theorem rootV_polyT : PolyT rootV := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT fun x => GraphProblems.ones (sI x) := by unfold GraphProblems.ones; fun_prop
  unfold rootV; fun_prop

theorem read_vc {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : rootV (code G ++ unary k) = (k, edges n (matrix G)) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary k)
  have h1 : GraphProblems.ones (unary k) = k := by simpa using Read.ones_unary_append k []
  rw [rootV, hE, hs, h1]

/-- The last step: is the sum positive? -/
def postV (N : ℕ) : List Bool := [decide (0 < N)]

theorem postV_polyT : PolyT postV := by unfold postV; fun_prop

/-- Walk the tree, count at the leaves, say whether the sum is positive. -/
def vcM (d w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepV d) rootV (Stepped.mapIn (leafV d) (FromPrinted.Consequences.SIZED w ℓ τ))) postV

@[instance_reducible] def isPolyT_vcM (d w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] : IsPolyT (vcM d w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) (leafV_polyT d)
  haveI := isPolyT_walkSum (T := Stepped.mapIn (leafV d) (FromPrinted.Consequences.SIZED w ℓ τ)) (stepV_polyT d) rootV_polyT
  IsPolyT.mapOut (M := walkSum (stepV d) rootV (Stepped.mapIn (leafV d) (FromPrinted.Consequences.SIZED w ℓ τ))) postV_polyT

/-! ### The graph and the root -/

/-- The root is good exactly if G has a vertex cover with at most k vertices. -/
theorem good_root {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Good (k, edges n (matrix G)) ↔ ∃ X : Finset (Fin n), X.card ≤ k ∧ ∀ u v, G.Adj u v → u ∈ X ∨ v ∈ X := by
  have hb := edges_bound n (matrix G)
  constructor
  · rintro ⟨X, hX, hc⟩
    refine ⟨univ.filter fun u : Fin n => u.val ∈ X, ?_, fun u v huv => ?_⟩
    · refine (card_le_card_of_injOn Fin.val (fun u hu => (mem_filter.1 hu).2) ?_).trans hX
      intro u _ v _ h; exact Fin.ext h
    · rcases lt_trichotomy u v with h | rfl | h
      · rcases hc _ ((mem_edges stAdj G u v).2 ⟨h, huv⟩) with h1 | h1
        · exact Or.inl (mem_filter.2 ⟨mem_univ _, h1⟩)
        · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1⟩)
      · exact absurd huv (G.loopless.irrefl _)
      · rcases hc _ ((mem_edges stAdj G v u).2 ⟨h, huv.symm⟩) with h1 | h1
        · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1⟩)
        · exact Or.inl (mem_filter.2 ⟨mem_univ _, h1⟩)
  · rintro ⟨Y, hY, hc⟩
    refine ⟨Y.map ⟨Fin.val, Fin.val_injective⟩, by rw [card_map]; exact hY, fun e he => ?_⟩
    obtain ⟨h1, h2⟩ := hb e he
    have hm := (mem_edges stAdj G ⟨e.1, by omega⟩ ⟨e.2, h2⟩).1 he
    rcases hc _ _ hm.2 with h | h
    · exact Or.inl (mem_map.2 ⟨_, h, rfl⟩)
    · exact Or.inr (mem_map.2 ⟨_, h, rfl⟩)

/-! ### Sizes -/

theorem size_sublist {β : Type} [HasSize β] {l₁ l₂ : List β} (h : l₁.Sublist l₂) : size l₁ ≤ size l₂ := by
  show (l₁.map fun x => size x + 1).sum + 1 ≤ (l₂.map fun x => size x + 1).sum + 1
  exact Nat.add_le_add_right ((h.map _).sum_le_sum fun _ _ => Nat.zero_le _) 1

theorem size_edges_le {n : ℕ} (G : SimpleGraph (Fin n)) : size (edges n (matrix G)) ≤ 4 * (n + 2) ^ 3 := by
  have hb := edges_bound n (matrix G)
  have hl := EthCor.ConnTM.length_edges_sq (n := n) (matrix G)
  have h := SplitCount.size_list_le (s := 2 * n + 2) hl fun e he => by
    obtain ⟨h1, h2⟩ := hb e he
    have s1 : size e.1 ≤ n + 1 := SplitCount.size_nat_le ((show e.1 < n by omega).trans Nat.lt_two_pow_self)
    have s2 : size e.2 ≤ n + 1 := SplitCount.size_nat_le (h2.trans Nat.lt_two_pow_self)
    show size e.1 + size e.2 ≤ 2 * n + 2
    omega
  calc size (edges n (matrix G)) ≤ n * n * (2 * n + 2 + 1) + 1 := h
    _ ≤ 4 * (n + 2) ^ 3 := by nlinarith

theorem ar1 {n k d : ℕ} (hk : k ≤ n) : k + d + 1 ≤ (d + 2) * (n + 2) := by nlinarith

theorem ar2 {n k d : ℕ} (hk : k ≤ n) : k + d + k * d + 1 ≤ (2 * d + 2) * (n + 2) := by nlinarith

theorem ar3 {n k d m : ℕ} (hk : k ≤ n) (hm : m ≤ n * n) : k * d + m + 3 ≤ (d + 4) * (n + 2) ^ 2 := by nlinarith

theorem ar4 {n k : ℕ} (hk : k ≤ n) : n + 1 + n * n + (k + 1) + 6 ≤ 9 * (n + 2) ^ 2 := by nlinarith

/-! ### The theorem -/

open Classical in
/-- **Vertex cover in time C·(n+2)^C·2^{εk}.** For every ε > 0, one Turing machine with finite
alphabets: given a graph G on n vertices and k ≤ n in unary, it outputs whether G has a vertex cover
with at most k vertices, within ⌊C·(n+2)^C·2^{εk}⌋ steps. -/
theorem vc_fpt {ε : ℝ} (hε : 0 < ε) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), k ≤ n →
      Wrap.Outputs M (code G ++ unary k)
        [decide (∃ X : Finset (Fin n), X.card ≤ k ∧ ∀ u v, G.Adj u v → u ∈ X ∨ v ∈ X)]
        ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (ε * k)⌋₊ := by
  -- the degree d
  obtain ⟨d, hd2, hw⟩ := EthCor.CnfTree.exists_width 1 le_rfl (show 0 < ε / 4 by positivity)
  have hd : 1 ≤ d := by omega
  have hd' : ((1 : ℕ) : ℝ) / (d : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ) * ((1 : ℕ) : ℝ)) ≤ ε / 4 := by
    have hlog : 0 ≤ Real.logb 2 (Real.exp 1 * (d : ℝ) * ((1 : ℕ) : ℝ)) := by
      apply Real.logb_nonneg one_lt_two
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      push_cast; nlinarith
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    refine le_trans ?_ hw
    gcongr
    norm_num
  -- the counter
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 2 (show 0 < ε / (4 * d) by positivity)
  have := isPolyT_vcM d 2 ℓ τ
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, ((c : ℝ) + 2) * (2 : ℝ) ^ (ε / 4 * d) ≤ c₀ := exists_nat_ge _
  obtain ⟨A, hA⟩ : ∃ A, A = 8 * d + 24 + c * (d + 4) ^ c := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // p.1 ≤ n}
  suffices hrun : ∀ x : ι, ∃ T S : ℕ, (vcM d 2 ℓ τ).Runs (code x.2.1.2 ++ unary x.2.1.1) T S
      [decide (∃ X : Finset (Fin x.1), X.card ≤ x.2.1.1 ∧ ∀ u v, x.2.1.2.Adj u v → u ∈ X ∨ v ∈ X)] ∧
      (code x.2.1.2 ++ unary x.2.1.1).length + S + 1 ≤ A * (x.1 + 2) ^ (2 * c + 4) ∧
      (T : ℝ) ≤ c₀ * (2 : ℝ) ^ (ε * x.2.1.1) by
    obtain ⟨N, C, hfin, hN⟩ := tm_fpt (vcM d 2 ℓ τ) (ι := ι) (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (∃ X : Finset (Fin x.1), X.card ≤ x.2.1.1 ∧ ∀ u v, x.2.1.2.Adj u v → u ∈ X ∨ v ∈ X)])
      (fun x => x.1) (fun x => x.2.1.1) hε.le c₀ A (2 * c + 4) hrun
    exact ⟨N, C, hfin, fun n k G hk => hN ⟨n, (k, G), hk⟩⟩
  rintro ⟨n, ⟨k, G⟩, hk⟩
  dsimp only at hk ⊢
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = edges n (matrix G) := ⟨_, rfl⟩
  have hroot : rootV (code G ++ unary k) = (k, E₀) := by rw [hE₀]; exact read_vc G k
  have hE₀l : E₀.length ≤ n * n := hE₀ ▸ EthCor.ConnTM.length_edges_sq (matrix G)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  -- the leaves
  obtain ⟨hLn, hLr⟩ := leaves_le hd hd' k E₀
  have hfinal := leaves_final hd k E₀
  obtain ⟨t, ht⟩ : ∃ t, t = ⌊(c : ℝ) * (2 : ℝ) ^ (ε / (4 * d) * ((k * d : ℕ) : ℝ))⌋₊ := ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ Sm, Sm = c * (k * d + E₀.length + 3) ^ c := ⟨_, rfl⟩
  have hleaf : ∀ y ∈ leaves (stepV d) (k + d) (rootV (code G ++ unary k)),
      (Stepped.mapIn (leafV d) (FromPrinted.Consequences.SIZED 2 ℓ τ)).Runs y t Sm
        (cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2) := by
    intro y hy
    rw [hroot] at hy
    obtain ⟨-, p, t', hG⟩ := hfinal y hy
    obtain ⟨hyk, hysub⟩ := inv_le hG
    obtain ⟨s1, s2, s3, s4⟩ := leafV_shape d y
    obtain ⟨T, hr, hTle⟩ := hc _ _ _ s2 (shaped_leafV d y)
    have e : leafV d y = (List.replicate (leafV d y).1.length (), (leafV d y).2.1, (leafV d y).2.2) := by
      rw [← s1]
    rw [← e] at hr
    have hNk : (leafV d y).1.length ≤ k * d := s3.trans (Nat.mul_le_mul_right d hyk)
    have hψ : (leafV d y).2.2.length ≤ E₀.length + 1 := s4.trans (by have := hysub.length_le; omega)
    have hTt : T ≤ t := by
      rw [ht]
      refine Nat.le_floor (hTle.trans ?_)
      have : ((leafV d y).1.length : ℝ) ≤ ((k * d : ℕ) : ℝ) := by exact_mod_cast hNk
      gcongr
      · exact one_le_two
    refine (Stepped.mapIn_runs hr).mono hTt ?_
    rw [hSm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  -- the stack
  obtain ⟨Sx, hSx⟩ : ∃ Sx, Sx = (k + d + 1) * (k + 1 + size E₀ + 1) + 1 := ⟨_, rfl⟩
  have hstack : ∀ i, size ((round (stepV d))^[i] ([rootV (code G ++ unary k)], [])).1 ≤ Sx := by
    intro i
    rw [hroot]
    obtain ⟨s1, s2⟩ := stack_inv hd k E₀ i
    rw [hSx]
    refine SplitCount.size_list_le s1 fun y hy => ?_
    obtain ⟨p, t', hG⟩ := s2 y hy
    obtain ⟨hyk, hysub⟩ := inv_le hG
    have e1 : size y.1 ≤ k + 1 := SplitCount.size_nat_le (lt_of_le_of_lt hyk Nat.lt_two_pow_self)
    have e2 := size_sublist hysub
    show size y.1 + size y.2 ≤ k + 1 + size E₀
    omega
  -- the sum
  obtain ⟨B, hB⟩ : ∃ B, B = k + d + k * d + 1 := ⟨_, rfl⟩
  have hsum : ((leaves (stepV d) (k + d) (rootV (code G ++ unary k))).map
      fun y => cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2).sum < 2 ^ B := by
    rw [hroot]
    have hcnt : ∀ y ∈ leaves (stepV d) (k + d) (k, E₀), cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2 ≤ 2 ^ (k * d) := by
      intro y hy
      obtain ⟨-, p, t', hG⟩ := hfinal y hy
      obtain ⟨hyk, -⟩ := inv_le hG
      have hNk : (leafV d y).1.length ≤ k * d := (leafV_shape d y).2.2.1.trans (Nat.mul_le_mul_right d hyk)
      calc cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2 ≤ 2 ^ (leafV d y).1.length := by
            unfold cntS
            refine (card_filter_le _ _).trans ?_
            simp
        _ ≤ 2 ^ (k * d) := Nat.pow_le_pow_right (by norm_num) hNk
    have hL2 : (leaves (stepV d) (k + d) (k, E₀)).length ≤ 2 ^ (k + d) := by
      refine hLn.trans ?_
      rw [← Nat.sum_range_choose]
      exact sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right (Nat.div_le_self _ _) 1))
    have h1 := List.sum_le_card_nsmul _ (2 ^ (k * d)) (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hcnt y hy)
    rw [List.length_map, smul_eq_mul] at h1
    calc _ ≤ (leaves (stepV d) (k + d) (k, E₀)).length * 2 ^ (k * d) := h1
      _ ≤ 2 ^ (k + d) * 2 ^ (k * d) := Nat.mul_le_mul_right _ hL2
      _ < 2 ^ B := by rw [← pow_add, hB]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have wr := walkSum_runs (stepV d) (root := rootV) (T := Stepped.mapIn (leafV d) (FromPrinted.Consequences.SIZED 2 ℓ τ))
    (k + d) (code G ++ unary k) (fun y hy => (hfinal y (hroot ▸ hy)).1)
    (fun y => cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2) t Sm Sx B hleaf hstack hsum
  have wo := Stepped.mapOut_runs (f := postV) wr
  -- the answer
  have hans : postV ((leaves (stepV d) (k + d) (rootV (code G ++ unary k))).map
      fun y => cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2).sum =
      [decide (∃ X : Finset (Fin n), X.card ≤ k ∧ ∀ u v, G.Adj u v → u ∈ X ∨ v ∈ X)] := by
    have hg : Good (k, E₀) ↔ ∃ X : Finset (Fin n), X.card ≤ k ∧ ∀ u v, G.Adj u v → u ∈ X ∨ v ∈ X := by
      rw [hE₀]; exact good_root G k
    rw [postV, hroot]
    congr 1
    refine decide_eq_decide.2 (Iff.trans ?_ hg)
    rw [good_leaves d (k + d) (k, E₀)]
    constructor
    · intro hpos
      obtain ⟨z, hz, hz0⟩ : ∃ z ∈ (leaves (stepV d) (k + d) (k, E₀)).map
          (fun y => cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2), z ≠ 0 := by
        by_contra hne
        have hall : ∀ z ∈ (leaves (stepV d) (k + d) (k, E₀)).map
            (fun y => cntS (leafV d y).1.length (leafV d y).2.1 (leafV d y).2.2), z = 0 :=
          fun z hz => by by_contra h; exact hne ⟨z, hz, h⟩
        have := List.sum_eq_zero hall
        omega
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact ⟨y, hy, (cnt_leafV_pos hd (hfinal y hy).1).1 (Nat.pos_of_ne_zero hz0)⟩
    · rintro ⟨y, hy, g⟩
      have h1 := (cnt_leafV_pos hd (hfinal y hy).1).2 g
      exact lt_of_lt_of_le h1 (List.le_sum_of_mem (List.mem_map.2 ⟨y, hy, rfl⟩))
  rw [hans] at wo
  refine ⟨_, _, wo, ?_, ?_⟩
  · -- the space
    have hsz := size_edges_le G
    rw [← hE₀] at hsz
    have hcode : (code G ++ unary k).length = n + 1 + n * n + (k + 1) := by
      rw [List.length_append, length_code_eq]; simp [unary]
    rw [hcode]
    have hkX : k ≤ X := by omega
    have hnX : n ≤ X := by omega
    have p1 : Sx ≤ (6 * d + 13) * X ^ 4 := by
      rw [hSx]
      have a1 : k + d + 1 ≤ (d + 2) * X := by rw [hX]; exact ar1 hk
      have a2 : k + 1 + size E₀ + 1 ≤ 6 * X ^ 3 := by
        have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
        rw [← hX] at hsz; omega
      calc (k + d + 1) * (k + 1 + size E₀ + 1) + 1 ≤ (d + 2) * X * (6 * X ^ 3) + X ^ 4 := by
            have : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX1
            have := Nat.mul_le_mul a1 a2
            omega
        _ = (6 * d + 12) * X ^ 4 + X ^ 4 := by ring
        _ = (6 * d + 13) * X ^ 4 := by ring
    have p2 : B ≤ (2 * d + 2) * X := by rw [hB, hX]; exact ar2 hk
    have p3 : Sm ≤ c * (d + 4) ^ c * X ^ (2 * c) := by
      rw [hSm]
      have : k * d + E₀.length + 3 ≤ (d + 4) * X ^ 2 := by rw [hX]; exact ar3 hk hE₀l
      calc c * (k * d + E₀.length + 3) ^ c ≤ c * ((d + 4) * X ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this _)
        _ = c * (d + 4) ^ c * X ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    have p4 : n + 1 + n * n + (k + 1) + 6 ≤ 9 * X ^ 2 := by rw [hX]; exact ar4 hk
    have q1 : X ^ 4 ≤ X ^ (2 * c + 4) := Nat.pow_le_pow_right hX1 (by omega)
    have q2 : X ^ (2 * c) ≤ X ^ (2 * c + 4) := Nat.pow_le_pow_right hX1 (by omega)
    have q3 : X ^ 2 ≤ X ^ (2 * c + 4) := Nat.pow_le_pow_right hX1 (by omega)
    have q4 : X ≤ X ^ (2 * c + 4) := Nat.le_self_pow (by omega) X
    have r1 := Nat.mul_le_mul_left (6 * d + 13) q1
    have r2 := Nat.mul_le_mul_left (c * (d + 4) ^ c) q2
    have r3 := Nat.mul_le_mul_left 9 q3
    have r4 := Nat.mul_le_mul_left (2 * d + 2) q4
    have eA : A * X ^ (2 * c + 4) = (6 * d + 13) * X ^ (2 * c + 4) + c * (d + 4) ^ c * X ^ (2 * c + 4) +
        9 * X ^ (2 * c + 4) + (2 * d + 2) * X ^ (2 * c + 4) := by
      rw [hA]; ring
    rw [← hX]
    omega
  · -- the time
    have hfl : ((t : ℕ) : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (ε / 4 * k) := by
      rw [ht]
      refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
      congr 2
      have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   exact this.ne'
      push_cast; field_simp
    have hL : ((leaves (stepV d) (k + d) (rootV (code G ++ unary k))).length : ℝ) ≤
        (2 : ℝ) ^ (ε / 4 * d) * (2 : ℝ) ^ (ε / 4 * k) := by
      rw [hroot, ← Real.rpow_add two_pos]
      refine hLr.trans (le_of_eq ?_)
      congr 1; push_cast; ring
    have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 4 * k) := Real.one_le_rpow one_le_two (by positivity)
    have hEE : (2 : ℝ) ^ (ε / 4 * k) * (2 : ℝ) ^ (ε / 4 * k) ≤ (2 : ℝ) ^ (ε * k) := by
      rw [← Real.rpow_add two_pos]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    calc (((leaves (stepV d) (k + d) (rootV (code G ++ unary k))).length * (t + 2) : ℕ) : ℝ)
        = ((leaves (stepV d) (k + d) (rootV (code G ++ unary k))).length : ℝ) * ((t : ℝ) + 2) := by push_cast; ring
      _ ≤ ((2 : ℝ) ^ (ε / 4 * d) * (2 : ℝ) ^ (ε / 4 * k)) * ((c : ℝ) * (2 : ℝ) ^ (ε / 4 * k) + 2 * (2 : ℝ) ^ (ε / 4 * k)) := by
          gcongr
          linarith
      _ = (((c : ℝ) + 2) * (2 : ℝ) ^ (ε / 4 * d)) * ((2 : ℝ) ^ (ε / 4 * k) * (2 : ℝ) ^ (ε / 4 * k)) := by ring
      _ ≤ (c₀ : ℝ) * (2 : ℝ) ^ (ε * k) := by gcongr

end EthCor.VcTM
