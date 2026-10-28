import EthCor.CdsTree
import EthCor.ConnTM
import EthCor.CnfTM
import GraphProblems.Sets
import GraphProblems.Cert
import Consequences.Dom
import CountKSat.Walk

/-! # The parity of the number of connected dominating sets in time C·2^{δn}

The input is the code of G, then ℓ in unary. The formula of Cut & Count for connected sets
(`EthCor.Conn.connF`) with ψ the clauses of domination (`GraphProblems.domF`) has n clauses whose
width is not bounded: one per vertex, over its closed neighbourhood. The machine `cdsM w ℓ τ` walks
the tree of `EthCor.CdsTree.shortensN` from the root with these clauses open and the clauses of the
side bits and the edges closed (`rootC`), counts at each leaf with
`FromPrinted.Consequences.SIZED (w + 4) ℓ τ` the satisfying assignments of the leaf formula on 3n
variables with n + ℓ true variables, adds up, and keeps bit 1 of the sum. By `Conn.conn_parity`
this bit is the parity of the number of dominating sets X of size ℓ with G[X] connected
(`cds_parity_tm`). The graph may be dense. -/

namespace EthCor.CdsTM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Turing Finset
  EthCor.Ham EthCor.HamTM EthCor.HamITM EthCor.Conn EthCor.ConnTM EthCor.CdsTree EthCor.CnfTM

/-! ### Connected dominating sets -/

open Classical in
/-- The connected dominating sets of G with ℓ vertices: every vertex is in X or has a neighbour in
X, and G[X] is connected. -/
noncomputable def numCDS {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (∀ v, x v = true ∨ ∃ u, x u = true ∧ G.Adj v u) ∧
    (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected).card

theorem sat_dom {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    (∀ C ∈ domF n (matrix G), ∃ l ∈ C, ext x l.1 = l.2) ↔ ∀ v, x v = true ∨ ∃ u, x u = true ∧ G.Adj v u := by
  rw [Sets.sat_domF G x]
  simp only [IsDominating, Sets.mem_trueSet]

theorem numCDS_eq {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) :
    numCDS G ℓ = numConnF G (domF n (matrix G)) ℓ := by
  unfold numCDS numConnF
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, sat_dom]

theorem domF_lt {n : ℕ} (m : List Bool) : ∀ C ∈ domF n m, ∀ l ∈ C, l.1 < n := by
  intro C hC l hl
  obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hD
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
  rw [List.mem_range] at hv
  rcases List.mem_cons.1 hu with rfl | hu
  · exact hv
  · exact List.mem_range.1 (List.mem_of_mem_filter hu)

/-! ### The root -/

/-- The adjacency matrix: the n·n bits after n in unary. -/
def mH (x : List Bool) : List Bool := (gH x).2.take (nH x * nH x)

/-- The root of the tree: 3n variables, the target n + ℓ, the clauses of domination open, the
clauses of the side bits and of the edges closed. -/
def rootC (x : List Bool) : DNode :=
  rootN (nH x + nH x + nH x) (nH x + lC x) (nH x) (mH x) (sideF (nH x) ++ edgeCC (nH x) (EH x))

theorem rootC_polyT : PolyT rootC := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC GraphProblems.ones; fun_prop
  have hm : PolyT mH := by unfold mH; have := hn.poly; fun_prop
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x) () := (hn.add hn).add hn
  have h2 : PolyT fun x => nH x + lC x := PolyT.add hn.poly hl
  have h3 : PolyT fun x => nbhd (nH x) (mH x) := nbhd_polyT hn hm
  have h4 : PolyT fun x => sideF (nH x) ++ edgeCC (nH x) (EH x) :=
    PolyT.append (sideF_polyT hn) (edgeCC_polyT hn.poly hE)
  unfold rootC rootN
  exact PolyT.prodMk (PolyT.prodMk h1 h2) (PolyT.prodMk h3 h4)

theorem mH_code {n : ℕ} (G : SimpleGraph (Fin n)) (s : List Bool) : mH (code G ++ s) = matrix G := by
  have hg : gH (code G ++ s) = (List.replicate n (), matrix G ++ s) := by
    rw [gH, read1, code, List.append_assoc, Read.ones_unary_append, Read.rest_unary_append]
  rw [mH, hg, (read_code G s).1]
  exact List.take_left' (stMatrixLength n G)

theorem read_cds {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) :
    rootC (code G ++ unary ℓ) = rootN (n + n + n) (n + ℓ) n (matrix G) (sideF n ++ edgeCC n (edges n (matrix G))) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ)
  have h1 : ones (unary ℓ) = ℓ := by simpa using Read.ones_unary_append ℓ []
  rw [rootC, lC, hn, hE, hs, h1, mH_code]

/-! ### The machine -/

/-- Read G and ℓ, walk the tree, count at the leaves, keep bit 1 of the sum. -/
def cdsM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepD w) rootC (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))) postC

@[instance_reducible] def isPolyT_cdsM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)] :
    IsPolyT (cdsM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ) stCertDom.2.2
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (stCertDom.1 w)
    rootC_polyT
  IsPolyT.mapOut (M := walkSum (stepD w) rootC (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)))
    postC_polyT

/-! ### Sizes -/

theorem shaped_mono {W W' N : ℕ} {F : Fml} (h : Shaped W N F) (hW : W ≤ W') : Shaped W' N F :=
  fun C hC => ⟨(h C hC).1.trans hW, (h C hC).2⟩

/-- The clauses of the side bits and of the edges have width at most 4. -/
theorem shaped_cc (n : ℕ) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) :
    Shaped 4 (n + n + n) (sideF n ++ edgeCC n E) := by
  intro D hD
  rcases List.mem_append.1 hD with hD | hD
  · rw [sideF] at hD
    obtain ⟨v, hv, hD⟩ := List.mem_flatMap.1 hD
    rw [List.mem_range] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> simp <;> omega
  · rw [edgeCC] at hD
    obtain ⟨p, hp, hD⟩ := List.mem_flatMap.1 hD
    have := hE p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl | rfl <;>
      simp <;> omega

theorem length_cc (n : ℕ) (E : List (ℕ × ℕ)) : (sideF n ++ edgeCC n E).length = 3 * n + 2 * E.length := by
  simp only [sideF, edgeCC, List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  simp; ring

/-- A node with N + 2 ≤ X, s ≤ X, at most n ≤ X open clauses of at most n variables below N, and at
most P ≤ X² closed clauses of width W on N variables has size at most (2W + 11)·X³. -/
theorem size_nodeN_le {N s n P W X : ℕ} {x : DNode} (h1 : x.1 = (List.replicate N (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < N) (h4 : x.2.2.length ≤ P) (h5 : Shaped W N x.2.2)
    (hN : N + 2 ≤ X) (hs : s ≤ X) (hn : n ≤ X) (hP : P ≤ X ^ 2) : size x ≤ (2 * W + 11) * X ^ 3 := by
  have s1 : size (List.replicate N ()) ≤ N * 2 + 1 := SplitCount.size_unary _
  have s2 : size s ≤ s + 1 := SplitCount.size_nat_le Nat.lt_two_pow_self
  have s3 : size x.2.1 ≤ n * (n * (N + 1 + 1) + 1 + 1) + 1 :=
    SplitCount.size_list_le h2 fun D hD => SplitCount.size_list_le (h3 D hD).1 fun u hu =>
      SplitCount.size_nat_le (((h3 D hD).2 u hu).trans Nat.lt_two_pow_self)
  have s4 : size x.2.2 ≤ P * (W * (N + 2 + 1) + 1 + 1) + 1 := SplitCount.size_fml_le h4 h5
  have sx : size x = size (List.replicate N ()) + size s + (size x.2.1 + size x.2.2) := by
    rw [size_prod, size_prod, h1]
    rfl
  have hX1 : 1 ≤ X := by omega
  have i3 : n * (n * (N + 1 + 1) + 1 + 1) ≤ X * (X * X + 2) :=
    Nat.mul_le_mul hn (by have := Nat.mul_le_mul hn (show N + 1 + 1 ≤ X by omega); omega)
  have i4 : P * (W * (N + 2 + 1) + 1 + 1) ≤ X ^ 2 * ((2 * W + 2) * X) :=
    Nat.mul_le_mul hP (by nlinarith [Nat.mul_le_mul_left W (show N + 2 + 1 ≤ 2 * X by omega)])
  have e3 : X * (X * X + 2) = X ^ 3 + 2 * X := by ring
  have e4 : X ^ 2 * ((2 * W + 2) * X) = (2 * W + 2) * X ^ 3 := by ring
  have h6 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have e5 : (2 * W + 11) * X ^ 3 = (2 * W + 2) * X ^ 3 + 9 * X ^ 3 := by ring
  rw [sx]
  omega

/-! ### The theorem -/

/-- **The parity of the number of connected dominating sets in time C·2^{δn}.** For every δ > 0,
one Turing machine with finite alphabets: given a graph G on n vertices (of any density) and
1 ≤ ℓ ≤ n in unary, it outputs whether G has an odd number of connected dominating sets with ℓ
vertices, within ⌊C·2^{δn}⌋ steps. -/
theorem cds_parity_tm {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ ℓ → ℓ ≤ n →
      Wrap.Outputs M (code G ++ unary ℓ) [decide (numCDS G ℓ % 2 = 1)] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨w, hw2, hw⟩ := shortensN_exists (show 0 < δ / 4 by positivity)
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (w + 4) (show 0 < δ / 12 by positivity)
  have := isPolyT_cdsM w ℓ₀ τ
  -- the constants
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * (w + 4) + 11 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 56 * 27 * A + c * 3 ^ c + 2 * c + 16 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // 1 ≤ p.1 ∧ p.1 ≤ n}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (cdsM w ℓ₀ τ).Runs (code x.2.1.2 ++ unary x.2.1.1)
      T (K * (x.1 + 2) ^ K) [decide (numCDS x.2.1.2 x.2.1.1 % 2 = 1)] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (cdsM w ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (numCDS x.2.1.2 x.2.1.1 % 2 = 1)]) (fun x => x.1) hδ K 6 2 (fun x => by
        have := x.2.2.2
        rw [List.length_append, length_code_eq]
        simp only [unary, List.length_append, List.length_replicate, List.length_singleton]
        nlinarith) hrun
    exact ⟨N, C', hfin, fun n ℓ G h1 h2 => hN ⟨n, (ℓ, G), h1, h2⟩⟩
  rintro ⟨n, ⟨ℓ, G⟩, h1, h2⟩
  dsimp only at h1 h2 ⊢
  -- the tree
  obtain ⟨F, hF⟩ : ∃ F, F = sideF n ++ edgeCC n (edges n (matrix G)) := ⟨_, rfl⟩
  have hEb := edges_bound n (matrix G)
  have hEsq := length_edges_sq (n := n) (matrix G)
  have hFs : Shaped (w + 4) (n + n + n) F := hF ▸ shaped_mono (shaped_cc n hEb) (by omega)
  have hFl : F.length = 3 * n + 2 * (edges n (matrix G)).length := hF ▸ length_cc n _
  obtain ⟨t1, t2, t3, t4⟩ := shortensN w hw2 hw (n + n + n) (n + ℓ) n (matrix G) F (by omega) hFs
  have hR : rootC (code G ++ unary ℓ) = rootN (n + n + n) (n + ℓ) n (matrix G) F := by rw [hF]; exact read_cds G ℓ
  rw [← hR] at t1 t2 t3 t4
  have hcf : (nbhd n (matrix G)).map posC ++ F = connF n (edges n (matrix G)) (domF n (matrix G)) := by
    rw [hF, connF, domF, List.append_assoc]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 4 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  -- the leaves
  have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootC (code G ++ unary ℓ)),
      (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)).Runs x ⌊(c : ℝ) * E⌋₊
        (c * 3 ^ c * X ^ (2 * c)) (cntS (n + n + n) (n + ℓ) (leafD x).2.2) := by
    intro x hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    obtain ⟨T, hr, hTle⟩ := hc (n + n + n) (n + ℓ) (leafD x).2.2 (by omega) h2
    have e : leafD x = (List.replicate (n + n + n) (), n + ℓ, (leafD x).2.2) := by simp [leafD, h1]
    rw [← e] at hr
    refine (Stepped.mapIn_runs hr).mono (Nat.le_floor ?_) ?_
    · have e12 : δ / 12 * ((n + n + n : ℕ) : ℝ) = δ / 4 * n := by push_cast; ring
      rw [e12] at hTle; rw [hE]; exact hTle
    · have hsp : n + n + n + (leafD x).2.2.length + 2 ≤ 3 * X ^ 2 := by rw [hX]; nlinarith
      calc c * (n + n + n + (leafD x).2.2.length + 2) ^ c ≤ c * (3 * X ^ 2) ^ c :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsp c)
        _ = c * 3 ^ c * X ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
  -- the stack
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootC (code G ++ unary ℓ)], [])).1 ≤
      (2 * n + 1) * (27 * A * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitCount.size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      have hP : F.length + 2 * n ≤ (3 * X) ^ 2 := by rw [hFl, hX]; nlinarith
      have := size_nodeN_le h1 h2 h3 h4 h5 (X := 3 * X) (by omega) (by omega) (by omega) hP
      calc size x ≤ (2 * (w + 4) + 11) * (3 * X) ^ 3 := this
        _ = 27 * A * X ^ 3 := by rw [hA]; ring
  have hlt : ((leaves (stepD w) (2 * n) (rootC (code G ++ unary ℓ))).map
      fun x => cntS (n + n + n) (n + ℓ) (leafD x).2.2).sum < 2 ^ (n + n + n + 1) := by
    rw [← t3]
    exact lt_of_le_of_lt (Consequences.cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have wr := walkSum_runs (stepD w) (root := rootC)
    (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)) (2 * n) (code G ++ unary ℓ)
    (fun x hx => (t2 x hx).1) (fun x => cntS (n + n + n) (n + ℓ) (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ _ _ (n + n + n + 1)
    hleaf hstack hlt
  have hout := Stepped.mapOut_runs (f := postC) wr
  rw [← t3, hcf, postC, conn_parity G (domF_lt (matrix G)) h1, ← numCDS_eq] at hout
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) (2 * n) (rootC (code G ++ unary ℓ))).length := ⟨_, rfl⟩
  rw [← hL] at hout t1
  refine ⟨_, hout.mono le_rfl ?_, ?_⟩
  · -- the space
    rw [← hX]
    have p1 : (2 * n + 1) * (27 * A * X ^ 3 + 1) + 1 ≤ (56 * 27 * A + 1) * X ^ (2 * c + 4) := by
      have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
      have h4 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX1
      have hA1 : 1 ≤ A := by omega
      calc (2 * n + 1) * (27 * A * X ^ 3 + 1) + 1 ≤ (2 * X) * (28 * 27 * A * X ^ 3) + X ^ 4 := by
            gcongr
            · omega
            · nlinarith [Nat.mul_le_mul hA1 h3]
        _ = (56 * 27 * A + 1) * X ^ 4 := by ring
        _ ≤ (56 * 27 * A + 1) * X ^ (2 * c + 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    have p2 : c * 3 ^ c * X ^ (2 * c) ≤ c * 3 ^ c * X ^ (2 * c + 4) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    have p3 : n + n + n + 1 + 1 + 1 + 1 ≤ 8 * X ^ (2 * c + 4) := by
      have : X ≤ X ^ (2 * c + 4) := Nat.le_self_pow (by omega) X
      omega
    have p4 : (56 * 27 * A + 1 + c * 3 ^ c + 8) * X ^ (2 * c + 4) ≤ K * X ^ K := absorb hX1 (by omega) (by omega)
    have e5 : (56 * 27 * A + 1 + c * 3 ^ c + 8) * X ^ (2 * c + 4) =
        (56 * 27 * A + 1) * X ^ (2 * c + 4) + c * 3 ^ c * X ^ (2 * c + 4) + 8 * X ^ (2 * c + 4) := by ring
    omega
  · -- the time
    have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
    have hLE : (L : ℝ) ≤ E := hE ▸ t1
    have hEE : E * E = (2 : ℝ) ^ (δ / 2 * n) := by
      rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
    have hE0 : 0 ≤ E := by linarith
    have hcK : (c : ℝ) + 2 ≤ (K : ℝ) := by
      have : c + 2 ≤ K := by omega
      exact_mod_cast this
    calc ((L * (⌊(c : ℝ) * E⌋₊ + 2) : ℕ) : ℝ) = (L : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) := by push_cast; ring
      _ ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
      _ = ((c : ℝ) + 2) * (E * E) := by ring
      _ = ((c : ℝ) + 2) * (2 : ℝ) ^ (δ / 2 * n) := by rw [hEE]
      _ ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * n) := mul_le_mul_of_nonneg_right hcK (by positivity)

end EthCor.CdsTM
