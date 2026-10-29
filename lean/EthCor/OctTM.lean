import EthCor.ConnTM

/-! # Odd cycle transversal in time C·2^{δn}, deterministic, any density

The formula `octF n E` on 3n variables has a vertex bit x_v (v is kept), a color bit c_v and its
complement c̄_v for each vertex. Its clauses say c̄_v = ¬c_v, c_v = 0 if v is not kept (`sideF` of
`EthCor.Conn`), and c_u ≠ c_v on the edges between kept vertices (`edgeOC`). Each pair of
complementary bits holds one true bit, so the formula has a satisfying assignment with n + s true
variables iff some s vertices induce a bipartite subgraph (`oct_pos`). Induced bipartite subgraphs
are closed under removing vertices, so G has an odd cycle transversal with at most k ≤ n vertices
iff that holds for s = n − k (`oct_iff`). The front end `preO` writes the formula, Anthropic's
`SIZED` counts, and the last step tests whether the count is positive (`oct_tm`). The formula has
3n variables and clauses of width 4 for every density, and nothing is random. -/

namespace EthCor.OctTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset SimpleGraph EthCor.Ham
  EthCor.HamTM EthCor.HamITM EthCor.Conn EthCor.ConnTM

/-! ### The formula -/

/-- c_u ≠ c_v on the edges between kept vertices. -/
def edgeOC (n : ℕ) (E : List (ℕ × ℕ)) : Fml := E.flatMap fun p =>
  [[(p.1, false), (p.2, false), (n + p.1, true), (n + p.2, true)],
   [(p.1, false), (p.2, false), (n + p.1, false), (n + p.2, false)]]

def octF (n : ℕ) (E : List (ℕ × ℕ)) : Fml := sideF n ++ edgeOC n E

theorem sat_edgeOC (f : ℕ → Bool) (n : ℕ) (E : List (ℕ × ℕ)) : (∀ C ∈ edgeOC n E, ∃ l ∈ C, f l.1 = l.2) ↔
    ∀ p ∈ E, f p.1 = true → f p.2 = true → f (n + p.1) ≠ f (n + p.2) := by
  have h : (∀ C ∈ edgeOC n E, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ p ∈ E, ∀ C ∈ [[(p.1, false), (p.2, false), (n + p.1, true),
      (n + p.2, true)], [(p.1, false), (p.2, false), (n + p.1, false), (n + p.2, false)]], ∃ l ∈ C, f l.1 = l.2 := by
    simp only [edgeOC, List.mem_flatMap]
    exact ⟨fun h p hp C hC => h C ⟨p, hp, hC⟩, fun h C ⟨p, hp, hC⟩ => h p hp C hC⟩
  rw [h]
  refine forall₂_congr fun p _ => ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat4]
  generalize f p.1 = a, f p.2 = b, f (n + p.1) = c, f (n + p.2) = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- **The formula has a solution with n + s true variables iff some s vertices induce a bipartite
subgraph.** -/
theorem oct_pos {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) :
    0 < cntS (n + n + n) (n + s) (octF n (edges n (matrix G))) ↔
      ∃ x : Fin n → Bool, (univ.filter fun v => x v = true).card = s ∧ (G.induce {v | x v = true}).IsBipartite := by
  have hE := edges_bound n (matrix G)
  unfold cntS
  rw [card_pos]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hsat, hcnt⟩ := (mem_filter.1 hw).2
    obtain ⟨y, g, rfl⟩ : ∃ (y : Fin (n + n) → Bool) (g : Fin n → Bool), w = Fin.append y g :=
      ⟨_, _, (Fin.append_castAdd_natAdd (f := w)).symm⟩
    rw [octF, List.forall_mem_append, sat_sideF, sat_edgeOC] at hsat
    obtain ⟨hS, hC⟩ := hsat
    obtain ⟨x, hxd⟩ : ∃ x : Fin n → Bool, x = fun v => y (Fin.castAdd n v) := ⟨_, rfl⟩
    obtain ⟨c, hcd⟩ : ∃ c : Fin n → Bool, c = fun v => y (Fin.natAdd n v) := ⟨_, rfl⟩
    have hx : ∀ v : Fin n, ext (Fin.append y g) v.val = x v := fun v => by
      rw [ext_append_lt y g (by omega), hxd]
      simp only [CountKSat.ext, dif_pos (show v.val < n + n by omega)]
      rfl
    have hc : ∀ v : Fin n, ext (Fin.append y g) (n + v.val) = c v := fun v => by
      rw [ext_append_lt y g (by omega), ext_natAdd y v.2, hcd]
    have hg : g = fun v => !c v := by
      funext v
      have := (hS v.val v.2).1
      rwa [ext_append_ge, ext_fin, hc] at this
    have hcy : (univ.filter fun i => y i = true).card = (univ.filter fun v => x v = true).card +
        (univ.filter fun v => c v = true).card := by
      rw [hxd, hcd]
      conv_lhs => rw [← Fin.append_castAdd_natAdd (f := y)]
      exact card_true_append _ _
    have hgc : (univ.filter fun i => g i = true).card = (univ.filter fun i => (!c i) = true).card := by rw [hg]
    have hnot := card_true_not c
    rw [card_true_append, hcy] at hcnt
    refine ⟨x, by omega, ⟨Coloring.mk (fun v => if c v.1 then (1 : Fin 2) else 0) fun {a b} hab => ?_⟩⟩
    have hab' : G.Adj a.1 b.1 := hab
    have ha : x a.1 = true := a.2
    have hb : x b.1 = true := b.2
    have key : ∀ u v : Fin n, u < v → G.Adj u v → x u = true → x v = true → c u ≠ c v := by
      intro u v huv hadj hu hv
      have := hC _ ((mem_edges stAdj G u v).2 ⟨huv, hadj⟩) (by rw [hx]; exact hu) (by rw [hx]; exact hv)
      rwa [hc, hc] at this
    have hne : c a.1 ≠ c b.1 := by
      rcases lt_trichotomy a.1 b.1 with h | h | h
      · exact key _ _ h hab' ha hb
      · rw [h] at hab'
        exact absurd hab' (G.loopless.irrefl _)
      · exact fun e => key _ _ h hab'.symm hb ha e.symm
    revert hne
    generalize c a.1 = p
    generalize c b.1 = q
    revert p q
    decide
  · rintro ⟨x, hx, hB⟩
    obtain ⟨col⟩ := hB
    obtain ⟨c, hc0, hc1⟩ : ∃ c : Fin n → Bool, (∀ v, x v = false → c v = false) ∧
        ∀ u v (hu : x u = true) (hv : x v = true), G.Adj u v → c u ≠ c v := by
      refine ⟨fun v => if h : x v = true then decide (col ⟨v, h⟩ = 0) else false, fun v hv => by simp [hv],
        fun u v hu hv huv => ?_⟩
      simp only [dif_pos hu, dif_pos hv]
      have hne : col ⟨u, hu⟩ ≠ col ⟨v, hv⟩ := col.valid (show (G.induce {v | x v = true}).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
      revert hne
      generalize col ⟨u, hu⟩ = a
      generalize col ⟨v, hv⟩ = b
      revert a b
      decide
    obtain ⟨w, hw⟩ : ∃ w : Fin (n + n + n) → Bool, w = Fin.append (Fin.append x c) (fun v => !c v) := ⟨_, rfl⟩
    have h0 : ∀ v (hv : v < n), ext w v = x ⟨v, hv⟩ := fun v hv => by
      rw [hw, ext_append_lt _ _ (by omega), ext_append_lt _ _ hv]
      simp only [CountKSat.ext, dif_pos hv]
    have h1 : ∀ v (hv : v < n), ext w (n + v) = c ⟨v, hv⟩ := fun v hv => by
      rw [hw, ext_append_lt _ _ (by omega), ext_append_ge]
      simp only [CountKSat.ext, dif_pos hv]
    have h2 : ∀ v (hv : v < n), ext w (n + n + v) = !c ⟨v, hv⟩ := fun v hv => by
      rw [hw, ext_append_ge]
      simp only [CountKSat.ext, dif_pos hv]
    refine ⟨w, mem_filter.2 ⟨mem_univ _, ?_, ?_⟩⟩
    · rw [octF, List.forall_mem_append, sat_sideF, sat_edgeOC]
      refine ⟨fun v hv => ?_, fun p hp => ?_⟩
      · rw [h2 v hv, h1 v hv, h0 v hv]
        exact ⟨rfl, hc0 _⟩
      · obtain ⟨hp1, hp2⟩ := hE p hp
        rw [h0 p.1 (by omega), h0 p.2 hp2, h1 p.1 (by omega), h1 p.2 hp2]
        intro hu hv
        exact hc1 _ _ hu hv ((mem_edges stAdj G ⟨p.1, by omega⟩ ⟨p.2, hp2⟩).1 hp).2
    · rw [hw, card_true_append, card_true_append]
      have := card_true_not c
      omega

open Classical in
/-- Induced bipartite subgraphs are closed under removing vertices: G has an odd cycle transversal
with at most k ≤ n vertices iff the formula has a solution with n + (n − k) true variables. -/
theorem oct_iff {n : ℕ} (G : SimpleGraph (Fin n)) {k : ℕ} (hk : k ≤ n) :
    (∃ X : Finset (Fin n), X.card ≤ k ∧ (G.induce {v | v ∉ X}).IsBipartite) ↔
      0 < cntS (n + n + n) (n + (n - k)) (octF n (edges n (matrix G))) := by
  rw [oct_pos]
  constructor
  · rintro ⟨X, hX, hB⟩
    obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq (s := Xᶜ) (n := n - k)
      (by rw [card_compl, Fintype.card_fin]; omega)
    refine ⟨fun v => decide (v ∈ Z), by convert hZc using 2; ext v; simp, ?_⟩
    have hle : ({v | decide (v ∈ Z) = true} : Set (Fin n)) ≤ {v | v ∉ X} := fun v hv => by
      simpa using hZ (by simpa using hv)
    exact Colorable.of_hom (G.induceHomOfLE hle).toHom hB
  · rintro ⟨x, hc, hB⟩
    refine ⟨univ.filter fun v => x v = false, ?_, ?_⟩
    · have e : (univ.filter fun v => x v = false) = (univ.filter fun v => x v = true)ᶜ := by ext v; simp
      rw [e, card_compl, Fintype.card_fin, hc]; omega
    · have e2 : ({v | v ∉ univ.filter fun v => x v = false} : Set (Fin n)) = {v | x v = true} := by ext v; simp
      rw [e2]; exact hB

/-! ### The front end and the last step -/

def preO (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x + nH x + nH x) (), nH x + lC x, octF (nH x) (EH x))

/-- Whether the count is positive. -/
def postO (N : ℕ) : List Bool := [decide (0 < N)]

theorem edgeOC_polyT {α : Type} [Enc α] {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : PolyT n) (hE : PolyT E) :
    PolyT fun a => edgeOC (n a) (E a) := by
  unfold edgeOC; fun_prop

theorem preO_polyT : PolyT preO := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x) () := (hn.add hn).add hn
  have h2 : PolyT fun x => nH x + lC x := PolyT.add hn.poly hl
  have h3 : PolyT fun x => octF (nH x) (EH x) := by
    unfold octF
    exact PolyT.append (sideF_polyT hn) (edgeOC_polyT hn.poly hE)
  exact PolyT.prodMk h1 (PolyT.prodMk h2 h3)

theorem postO_polyT : PolyT postO := by unfold postO; fun_prop

/-- Prepare, count with `SIZED`, test whether the count is positive. -/
def octM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preO (FromPrinted.Consequences.SIZED w ℓ τ)) postO

@[instance_reducible] def isPolyT_octM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (octM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preO_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preO (FromPrinted.Consequences.SIZED w ℓ τ)) postO_polyT

theorem read_oct {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) :
    preO (code G ++ unary s) = (List.replicate (n + n + n) (), n + s, octF n (edges n (matrix G))) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary s)
  have h1 : ones (unary s) = s := by simpa using Read.ones_unary_append s []
  rw [preO, lC, hn, hE, hs, h1]

/-! ### Sizes -/

theorem shaped_oct {n : ℕ} (G : SimpleGraph (Fin n)) : Shaped 4 (n + n + n) (octF n (edges n (matrix G))) := by
  have hE := edges_bound n (matrix G)
  intro D hD
  simp only [octF, List.mem_append] at hD
  rcases hD with hD | hD
  · rw [sideF] at hD
    obtain ⟨v, hv, hD⟩ := List.mem_flatMap.1 hD
    rw [List.mem_range] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> simp <;> omega
  · rw [edgeOC] at hD
    obtain ⟨p, hp, hD⟩ := List.mem_flatMap.1 hD
    have := hE p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl | rfl <;>
      simp <;> omega

theorem length_octF {n : ℕ} (E : List (ℕ × ℕ)) : (octF n E).length = 3 * n + 2 * E.length := by
  simp only [octF, sideF, edgeOC, List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  simp; ring

/-! ### The theorems -/

/-- The machine: on `code G ++ unary s` it says whether the formula has a solution with n + s true
variables, within ⌊C·2^{δn}⌋ steps. -/
theorem pos_tm {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n s : ℕ) (G : SimpleGraph (Fin n)), s ≤ n →
      Wrap.Outputs M (code G ++ unary s) [decide (0 < cntS (n + n + n) (n + s) (octF n (edges n (matrix G))))]
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 4 (show 0 < δ / 6 by positivity)
  have := isPolyT_octM 4 ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * 10 ^ c + 2 * c + c + 1 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // p.1 ≤ n}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (octM 4 ℓ₀ τ).Runs (code x.2.1.2 ++ unary x.2.1.1)
      T (K * (x.1 + 2) ^ K)
        [decide (0 < cntS (x.1 + x.1 + x.1) (x.1 + x.2.1.1) (octF x.1 (edges x.1 (matrix x.2.1.2))))] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (octM 4 ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (0 < cntS (x.1 + x.1 + x.1) (x.1 + x.2.1.1) (octF x.1 (edges x.1 (matrix x.2.1.2))))])
      (fun x => x.1) hδ K 6 2 (fun x => by
        have := x.2.2
        rw [List.length_append, length_code_eq]
        simp only [unary, List.length_append, List.length_replicate, List.length_singleton]
        nlinarith) hrun
    exact ⟨N, C', hfin, fun n s G h => hN ⟨n, (s, G), h⟩⟩
  rintro ⟨n, ⟨s, G⟩, h⟩
  dsimp only at h ⊢
  obtain ⟨T, hT, hTle⟩ := hc (n + n + n) (n + s) (octF n (edges n (matrix G))) (by omega) (shaped_oct G)
  rw [← read_oct G s] at hT
  refine ⟨T, ?_, ?_⟩
  · have hout := Stepped.mapOut_runs (f := postO) (Stepped.mapIn_runs hT)
    rw [postO] at hout
    refine hout.mono le_rfl ?_
    have hl := length_octF (n := n) (edges n (matrix G))
    have hE := length_edges_sq (n := n) (matrix G)
    have hX : n + n + n + (octF n (edges n (matrix G))).length + 2 ≤ 10 * (n + 2) ^ 2 := by
      have h5 : 2 * (n * n) + 6 * n + 2 ≤ 3 * (n + 2) ^ 2 := by nlinarith
      omega
    calc c * (n + n + n + (octF n (edges n (matrix G))).length + 2) ^ c
        ≤ c * (10 * (n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
      _ = c * 10 ^ c * (n + 2) ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ K * (n + 2) ^ K := Nat.mul_le_mul (by rw [hK]; omega) (Nat.pow_le_pow_right (by omega) (by rw [hK]; omega))
  · have e : δ / 6 * ((n + n + n : ℕ) : ℝ) = δ / 2 * n := by push_cast; ring
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 6 * ((n + n + n : ℕ) : ℝ)) := hTle
      _ = c * (2 : ℝ) ^ (δ / 2 * n) := by rw [e]
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)

open Classical in
/-- **Odd cycle transversal in time C·2^{δn}, deterministic.** For every δ > 0, one Turing machine
with finite alphabets: given a graph G on n vertices (of any density) and n − k in unary (k ≤ n), it
outputs whether G has an odd cycle transversal with at most k vertices, i.e. a set X of at most k
vertices with G − X bipartite, within ⌊C·2^{δn}⌋ steps. Run for k = 0, 1, … it finds the minimum. -/
theorem oct_tm {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), k ≤ n →
      Wrap.Outputs M (code G ++ unary (n - k))
        [decide (∃ X : Finset (Fin n), X.card ≤ k ∧ (G.induce {v | v ∉ X}).IsBipartite)]
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M, C, hfin, hM⟩ := pos_tm hδ
  refine ⟨M, C, hfin, fun n k G hk => ?_⟩
  rw [decide_eq_decide.2 (oct_iff G hk)]
  exact hM n (n - k) G (by omega)

end EthCor.OctTM
