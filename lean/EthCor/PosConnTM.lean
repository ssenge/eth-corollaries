import EthCor.CdsIsoTM

/-! # Connected solutions of a positive CNF of any width, on graphs of any density

The input is G, ℓ and a CNF φ on the vertices whose literals are all positive, with at most D·n
clauses of any width. The clauses of φ are open in the tree of `EthCor.CdsTree.shortensP`, the
clauses of Cut & Count closed, exactly as for connected dominating sets (N7), where φ is the clauses
of domination. So for every D and δ > 0 one machine outputs the parity of the number of vertex sets
X of size ℓ with G[X] connected that meet every clause of φ (`pos_parity_tm`), and with the checks of
a seed ω closed as well one machine decides with one-sided error whether such an X exists
(`pos_randomized`). Special cases: Group Steiner Tree and connected hitting set (φ = the groups or
hyperedges), connected total domination (φ = the open neighbourhoods), connected dominating set. -/

namespace EthCor.PosTM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Turing Finset
  EthCor.Ham EthCor.HamTM EthCor.HamI EthCor.HamITM EthCor.Iso EthCor.Conn EthCor.ConnTM EthCor.ConnITM
  EthCor.CdsTree EthCor.CnfTM EthCor.CdsTM EthCor.CdsITM

/-! ### Positive clauses as open clauses -/

/-- The variables of each clause, without repeats. -/
def opens (ψ : Fml) : List (List ℕ) := ψ.map fun C => (C.map Prod.fst).dedup

theorem length_opens (ψ : Fml) : (opens ψ).length = ψ.length := by simp [opens]

theorem opens_ok {n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : ∀ C ∈ opens ψ, C.Nodup ∧ ∀ u ∈ C, u < n := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
  refine ⟨List.nodup_dedup _, fun u hu => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hu)
  exact hψ D hD l hl

theorem cntS_opens (N s : ℕ) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.2 = true) (F : Fml) :
    cntS N s ((opens ψ).map posC ++ F) = cntS N s (ψ ++ F) := by
  unfold cntS
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, List.forall_mem_append, and_assoc]
  refine and_congr ?_ Iff.rfl
  simp only [opens, List.map_map, List.forall_mem_map, Function.comp_apply]
  refine forall₂_congr fun C hC => ⟨fun ⟨l, hl, h⟩ => ?_, fun ⟨l, hl, h⟩ => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hu)
    exact ⟨l', hl', by simpa [hψ C hC l' hl'] using h⟩
  · exact ⟨(l.1, true), List.mem_map.2 ⟨l.1, List.mem_dedup.2 (List.mem_map.2 ⟨l, hl, rfl⟩), rfl⟩,
      by simpa [hψ C hC l hl] using h⟩

theorem toN_pos {n : ℕ} {φ : Sat3.CNF n} (h : ∀ C ∈ φ, ∀ l ∈ C, l.2 = true) :
    ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.2 = true := by
  intro C hC l hl
  obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  exact h C' hC' l' hl'

theorem opens_polyT {α : Type} [Enc α] {ψ : α → Fml} (h : PolyT ψ) : PolyT fun a => opens (ψ a) := by
  unfold opens; fun_prop

/-! ### The parity -/

/-- The root: as `rootC`, with the clauses of φ open in place of the clauses of domination. -/
def rootP (x : List Bool) : DNode := ((CdsTM.rootC x).1, (opens (fC x), (CdsTM.rootC x).2.2))

theorem rootP_polyT : PolyT rootP := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hrs : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hf : PolyT fC := (FreeCode.readFree_polyT.comp hrs).snd
  unfold rootP
  exact PolyT.prodMk CdsTM.rootC_polyT.fst (PolyT.prodMk (opens_polyT hf) CdsTM.rootC_polyT.snd.snd)

theorem read_pos {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (φ : Sat3.CNF n) :
    rootP (code G ++ unary ℓ ++ SatFree.enc φ) =
      ((List.replicate (n + n + n) (), n + ℓ), (opens (Decode.toN φ), sideF n ++ edgeCC n (edges n (matrix G)))) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ ++ SatFree.enc φ)
  simp only [rootP, CdsTM.rootC, rootN]
  rw [List.append_assoc, lC, fC, hn, hE, hs, Read.ones_unary_append, Read.rest_unary_append,
    FreeCode.reads_readFree n φ]

/-- Read G, ℓ and φ, walk the tree, count at the leaves, keep bit 1 of the sum. -/
def posM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepD w) rootP (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))) postC

@[instance_reducible] def isPolyT_posM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)] :
    IsPolyT (posM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ) stCertDom.2.2
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (stCertDom.1 w)
    rootP_polyT
  IsPolyT.mapOut (M := walkSum (stepD w) rootP (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)))
    postC_polyT

theorem length_enc_pos {n D : ℕ} (φ : Sat3.CNF n) (hr : ∀ C ∈ φ, C.length ≤ n) (hm : φ.length ≤ D * n) :
    (SatFree.enc φ).length ≤ n + 2 + 2 * D * (n + 2) ^ 3 := by
  have h1 := length_enc_le φ hr
  have h3 : n * ((2 * n + 2) * (n + 2)) ≤ 2 * (n + 2) ^ 3 := by nlinarith
  have h2 : φ.length * ((2 * n + 2) * (n + 2)) ≤ 2 * D * (n + 2) ^ 3 :=
    calc φ.length * ((2 * n + 2) * (n + 2)) ≤ D * n * ((2 * n + 2) * (n + 2)) := Nat.mul_le_mul_right _ hm
      _ = D * (n * ((2 * n + 2) * (n + 2))) := by ring
      _ ≤ D * (2 * (n + 2) ^ 3) := Nat.mul_le_mul_left _ h3
      _ = 2 * D * (n + 2) ^ 3 := by ring
  omega

theorem length_input_pos {n D ℓ : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (hr : ∀ C ∈ φ, C.length ≤ n)
    (hm : φ.length ≤ D * n) (hℓ : ℓ ≤ n) :
    (code G ++ unary ℓ ++ SatFree.enc φ).length + 1 ≤ (2 * D + 8) * (n + 2) ^ 3 := by
  have h1 := length_enc_pos φ hr hm
  have h4 : n * n + 6 * n + 6 ≤ 8 * (n + 2) ^ 3 := by nlinarith
  have e : (2 * D + 8) * (n + 2) ^ 3 = 2 * D * (n + 2) ^ 3 + 8 * (n + 2) ^ 3 := by ring
  have eu : (unary ℓ).length = ℓ + 1 := by simp [unary]
  rw [List.length_append, List.length_append, length_code_eq, eu]
  omega

/-- A stack of at most (D+1)·n + 1 nodes of size at most A·X⁶ has size at most ((D+1)(A+1)+1)·X⁷. -/
theorem stack_le {D n A X : ℕ} (hX : X = n + 2) :
    ((D + 1) * n + 1) * (A * X ^ 6 + 1) + 1 ≤ ((D + 1) * (A + 1) + 1) * X ^ 7 := by
  have hX1 : 1 ≤ X := by omega
  calc ((D + 1) * n + 1) * (A * X ^ 6 + 1) + 1 ≤ ((D + 1) * X) * ((A + 1) * X ^ 6) + X ^ 7 := by
        gcongr
        · rw [hX]; nlinarith
        · nlinarith [Nat.one_le_pow 6 X hX1]
        · exact Nat.one_le_pow 7 X hX1
    _ = ((D + 1) * (A + 1) + 1) * X ^ 7 := by ring

open Classical in
/-- **The parity of the number of connected solutions of a positive CNF of any width in time
C·2^{δn}.** For every D and δ > 0, one Turing machine with finite alphabets: given a graph G on n
vertices (of any density), 1 ≤ ℓ ≤ n in unary, and a CNF φ on the n vertices with only positive
literals, clauses of at most n literals and at most D·n clauses, it outputs whether the number of
vertex sets X of size ℓ that meet every clause of φ and induce a connected subgraph is odd, within
⌊C·2^{δn}⌋ steps. -/
theorem pos_parity_tm (D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ n ∧ ∀ l ∈ C, l.2 = true) → φ.length ≤ D * n →
        Wrap.Outputs M (code G ++ unary ℓ ++ SatFree.enc φ) [decide (numConn G φ ℓ % 2 = 1)]
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨w, hw2, hw⟩ := shortensP_exists D (show 0 < δ / 4 by positivity)
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (w + 4) (show 0 < δ / 12 by positivity)
  have := isPolyT_posM w ℓ₀ τ
  -- the constants
  obtain ⟨S, hS⟩ : ∃ S, S = 2 * D + 9 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (2 * (w + 4) + 11) * S ^ 3 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (D + 1) * (A + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = P + S + c * S ^ c + 2 * c + 20 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Sat3.CNF n //
    1 ≤ p.1 ∧ p.1 ≤ n ∧ (∀ C ∈ p.2.2, C.length ≤ n ∧ ∀ l ∈ C, l.2 = true) ∧ p.2.2.length ≤ D * n}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (posM w ℓ₀ τ).Runs (code x.2.1.2.1 ++ unary x.2.1.1 ++ SatFree.enc x.2.1.2.2)
      T (K * (x.1 + 2) ^ K) [decide (numConn x.2.1.2.1 x.2.1.2.2 x.2.1.1 % 2 = 1)] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (posM w ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2.1 ++ unary x.2.1.1 ++ SatFree.enc x.2.1.2.2)
      (fun x => [decide (numConn x.2.1.2.1 x.2.1.2.2 x.2.1.1 % 2 = 1)]) (fun x => x.1) hδ K (2 * D + 8) 3
      (fun x => length_input_pos x.2.1.2.1 x.2.1.2.2 (fun C hC => (x.2.2.2.2.1 C hC).1) x.2.2.2.2.2 x.2.2.2.1)
      hrun
    exact ⟨N, C', hfin, fun n ℓ G φ h1 h2 hr hm => hN ⟨n, (ℓ, G, φ), h1, h2, hr, hm⟩⟩
  rintro ⟨n, ⟨ℓ, G, φ⟩, h1, h2, hr, hm⟩
  dsimp only at h1 h2 hr hm ⊢
  have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
  have hpos := toN_pos fun C hC => (hr C hC).2
  -- the tree
  obtain ⟨F, hF⟩ : ∃ F, F = sideF n ++ edgeCC n (edges n (matrix G)) := ⟨_, rfl⟩
  have hEb := edges_bound n (matrix G)
  have hEsq := length_edges_sq (n := n) (matrix G)
  have hFs : Shaped (w + 4) (n + n + n) F := hF ▸ shaped_mono (shaped_cc n hEb) (by omega)
  have hFl : F.length = 3 * n + 2 * (edges n (matrix G)).length := hF ▸ length_cc n _
  have hOl : (opens (Decode.toN φ)).length ≤ D * n := by rw [length_opens, Decode.toN, List.length_map]; exact hm
  obtain ⟨t1, t2, t3, t4⟩ := shortensP D w hw2 hw (show w ≤ w + 4 by omega) (n + n + n) (n + ℓ) n
    (opens (Decode.toN φ)) F (by omega) (opens_ok hψ) hOl hFs
  have hR : rootP (code G ++ unary ℓ ++ SatFree.enc φ) =
      ((List.replicate (n + n + n) (), n + ℓ), (opens (Decode.toN φ), F)) := by rw [hF]; exact read_pos G ℓ φ
  rw [← hR] at t1 t2 t3 t4
  have hcf : cntS (n + n + n) (n + ℓ) ((opens (Decode.toN φ)).map posC ++ F) =
      cntS (n + n + n) (n + ℓ) (connF n (edges n (matrix G)) (Decode.toN φ)) := by
    rw [cntS_opens _ _ hpos, hF, connF, List.append_assoc]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 4 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  -- every node has at most S·X² variables and clauses
  have hX2 : n + 2 ≤ X ^ 2 := by rw [hX]; nlinarith
  have hnn : n * n ≤ X ^ 2 := by rw [hX]; nlinarith
  have hDn : D * n ≤ D * X ^ 2 := Nat.mul_le_mul_left _ (by omega)
  have eS : S * X ^ 2 = 2 * (D * X ^ 2) + 9 * X ^ 2 := by rw [hS]; ring
  have e2D : (2 * D + 1) * n = 2 * (D * n) + n := by ring
  have eD1 : (D + 1) * n = D * n + n := by ring
  -- the leaves
  have hleaf : ∀ x ∈ leaves (stepD w) ((D + 1) * n) (rootP (code G ++ unary ℓ ++ SatFree.enc φ)),
      (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)).Runs x ⌊(c : ℝ) * E⌋₊
        (c * S ^ c * X ^ (2 * c)) (cntS (n + n + n) (n + ℓ) (leafD x).2.2) := by
    intro x hx
    obtain ⟨-, g1, g2, g3⟩ := t2 x hx
    obtain ⟨T, hr, hTle⟩ := hc (n + n + n) (n + ℓ) (leafD x).2.2 (by omega) g2
    have e : leafD x = (List.replicate (n + n + n) (), n + ℓ, (leafD x).2.2) := by simp [leafD, g1]
    rw [← e] at hr
    refine (Stepped.mapIn_runs hr).mono (Nat.le_floor ?_) ?_
    · have e12 : δ / 12 * ((n + n + n : ℕ) : ℝ) = δ / 4 * n := by push_cast; ring
      rw [e12] at hTle; rw [hE]; exact hTle
    · have hsp : n + n + n + (leafD x).2.2.length + 2 ≤ S * X ^ 2 := by omega
      calc c * (n + n + n + (leafD x).2.2.length + 2) ^ c ≤ c * (S * X ^ 2) ^ c :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsp c)
        _ = c * S ^ c * X ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
  -- the stack
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootP (code G ++ unary ℓ ++ SatFree.enc φ)], [])).1 ≤
      ((D + 1) * n + 1) * (A * X ^ 6 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitCount.size_list_le s1 fun x hx => by
      obtain ⟨g1, g2, g3, g4, g5⟩ := s2 x hx
      have hYY : S * X ^ 2 ≤ (S * X ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
      have := size_nodeN_le g1 (n := D * n + n) (by omega) (fun C hC => ⟨by have := (g3 C hC).1; omega, (g3 C hC).2⟩)
        g4 g5 (X := S * X ^ 2) (by omega) (by omega) (by omega) (by omega)
      calc size x ≤ (2 * (w + 4) + 11) * (S * X ^ 2) ^ 3 := this
        _ = A * X ^ 6 := by rw [hA]; ring
  have hlt : ((leaves (stepD w) ((D + 1) * n) (rootP (code G ++ unary ℓ ++ SatFree.enc φ))).map
      fun x => cntS (n + n + n) (n + ℓ) (leafD x).2.2).sum < 2 ^ (n + n + n + 1) := by
    rw [← t3]
    exact lt_of_le_of_lt (Consequences.cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have wr := walkSum_runs (stepD w) (root := rootP)
    (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)) ((D + 1) * n)
    (code G ++ unary ℓ ++ SatFree.enc φ) (fun x hx => (t2 x hx).1) (fun x => cntS (n + n + n) (n + ℓ) (leafD x).2.2)
    ⌊(c : ℝ) * E⌋₊ _ _ (n + n + n + 1) hleaf hstack hlt
  have hout := Stepped.mapOut_runs (f := postC) wr
  rw [← t3, hcf, postC, conn_parity G hψ h1, ← numConn_eq] at hout
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) ((D + 1) * n) (rootP (code G ++ unary ℓ ++ SatFree.enc φ))).length :=
    ⟨_, rfl⟩
  rw [← hL] at hout t1
  refine ⟨_, hout.mono le_rfl ?_, ?_⟩
  · -- the space
    rw [← hX]
    have hpow : X ^ 7 ≤ X ^ (2 * c + 7) := Nat.pow_le_pow_right hX1 (by omega)
    have p1 := stack_le (D := D) (A := A) hX
    rw [← hP] at p1
    have p1' : P * X ^ 7 ≤ P * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ hpow
    have p2 : n + n + n + 1 + 1 + 1 + 1 ≤ S * X ^ (2 * c + 7) := by
      have : X ^ 2 ≤ X ^ (2 * c + 7) := Nat.pow_le_pow_right hX1 (by omega)
      have : S * X ^ 2 ≤ S * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ this
      omega
    have p3 : c * S ^ c * X ^ (2 * c) ≤ c * S ^ c * X ^ (2 * c + 7) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    have p4 : (P + S + c * S ^ c) * X ^ (2 * c + 7) ≤ K * X ^ K := absorb hX1 (by omega) (by omega)
    have e5 : (P + S + c * S ^ c) * X ^ (2 * c + 7) =
        P * X ^ (2 * c + 7) + S * X ^ (2 * c + 7) + c * S ^ c * X ^ (2 * c + 7) := by ring
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

/-! ### With one-sided error -/

/-- The root: as `rootR`, with the clauses of φ open in place of the clauses of domination. -/
def rootQ (x : List Bool) : DNode := ((rootR x).1, (opens (fR x), (rootR x).2.2))

theorem rootQ_polyT : PolyT rootQ := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hr1 : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hr2 : PolyT r2 := by unfold r2 rest; unfold rest at hr1; fun_prop
  have hL : PolyT fun x => GraphProblems.ones (rest (sI x)) := (ones_unary hr1).poly
  have hfp : PolyT fun x => (r2 x).drop (GraphProblems.ones (rest (sI x))) := by fun_prop
  have hf : PolyT fR := (FreeCode.readFree_polyT.comp hfp).snd
  unfold rootQ
  exact PolyT.prodMk rootR_polyT.fst (PolyT.prodMk (opens_polyT hf) rootR_polyT.snd.snd)

theorem read_q {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (ω : Seed n k t mm) (φ : Sat3.CNF n) :
    rootQ (codeCI G ℓ ω φ) = ((List.replicate (n + n + n + 1 + mm * k + mm * k) (), n + ℓ + mm * k),
      (opens (Decode.toN φ), ConnI.ciF n (edges n (matrix G)) [] ω)) := by
  have e : codeCI G ℓ ω φ = code G ++ (unary ℓ ++ (unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ))) := by
    simp only [codeCI, seedL, List.append_assoc]
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ ++ (unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ)))
  rw [← e] at hn hE hs
  have hl : lC (codeCI G ℓ ω φ) = ℓ := by rw [lC, hs, Read.ones_unary_append]
  have hr1 : rest (sI (codeCI G ℓ ω φ)) = unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ) := by
    rw [hs, Read.rest_unary_append]
  have hL : GraphProblems.ones (rest (sI (codeCI G ℓ ω φ))) = (seedCode ω).length := by
    rw [hr1, Read.ones_unary_append]
  have hr2 : r2 (codeCI G ℓ ω φ) = seedCode ω ++ SatFree.enc φ := by rw [r2, hr1, Read.rest_unary_append]
  have hsd : sdR (codeCI G ℓ ω φ) = seedCode ω := by rw [sdR, hr2, hL, List.take_left' rfl]
  have hf : fR (codeCI G ℓ ω φ) = Decode.toN φ := by
    rw [fR, hr2, hL, List.drop_left' rfl, FreeCode.reads_readFree n φ]
  obtain ⟨ek, em1, emm, -, eR, eF⟩ := decode_seedCode ω
  have hA : aR (codeCI G ℓ ω φ) = mm * k := by rw [aR, hsd, ek, emm]
  simp only [rootQ, rootR, rootN]
  rw [formD, hA, hn, hE, hl, hf, hsd, ek, em1, eR, eF, ConnI.ciF]

/-- Read G, ℓ, ω and φ, walk the tree, count at the leaves, keep bit 1 of the sum. -/
def posrM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepD w) rootQ (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))) postC

@[instance_reducible] def isPolyT_posrM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)] :
    IsPolyT (posrM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ) stCertDom.2.2
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (stCertDom.1 w)
    rootQ_polyT
  IsPolyT.mapOut (M := walkSum (stepD w) rootQ (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)))
    postC_polyT

theorem length_codeCI_pos {n D k t ℓ : ℕ} (G : SimpleGraph (Fin n)) (ω : Seed n k t (3 * n + 3)) (φ : Sat3.CNF n)
    (hr : ∀ C ∈ φ, C.length ≤ n) (hm : φ.length ≤ D * n) (hℓ : ℓ ≤ n) :
    (codeCI G ℓ ω φ).length + 1 ≤ (2 * D + 2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 12) * (n + 2) ^ 3 := by
  obtain ⟨B, hB⟩ : ∃ B, B = (k + 5) + (k + 4) * (6 * k + 5) := ⟨_, rfl⟩
  have hS := length_seedCode_le ω
  rw [← hB] at hS ⊢
  have h1 := length_enc_pos φ hr hm
  have h3 : (n + 2) ^ 2 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n * n + 6 * n + 6 ≤ 6 * (n + 2) ^ 2 := by nlinarith
  have h5 : B * (n + 2) ^ 2 ≤ B * (n + 2) ^ 3 := Nat.mul_le_mul_left _ h3
  have e : (2 * D + 2 * B + 12) * (n + 2) ^ 3 =
      2 * D * (n + 2) ^ 3 + 2 * (B * (n + 2) ^ 3) + 12 * (n + 2) ^ 3 := by ring
  have eu : ∀ m, (unary m).length = m + 1 := fun m => by simp [unary]
  simp only [codeCI, seedL, List.length_append, length_code_eq, eu]
  omega

open Classical in
/-- **Connected solutions of a positive CNF of any width, with one-sided error, in time C·2^{εn}.**
For every D, δ > 0 and ε > 0 there are k, t, n₀ and one Turing machine with finite alphabets such
that for every graph G on n ≥ n₀ vertices (of any density), 1 ≤ ℓ ≤ n and every CNF φ on the
vertices with only positive literals, clauses of at most n literals and at most D·n clauses: run on
`codeCI G ℓ ω φ` for a seed ω of `Seed n k t (3n + 3)`, it halts within ⌊C·2^{εn}⌋ steps with one
bit out(ω); if no vertex set X of size ℓ meets every clause of φ and induces a connected subgraph,
out(ω) = 0 for every seed; if one does, out(ω) = 1 for at least a 2^{−δn} fraction of the seeds. -/
theorem pos_randomized (D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ n ∧ ∀ l ∈ C, l.2 = true) → φ.length ≤ D * n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCI G ℓ ω φ) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numConn G φ ℓ = 0 → ∀ ω, out ω = false) ∧
        (0 < numConn G φ ℓ →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, hk, -, n₀, hdec⟩ := ConnI.ci_decide δ hδ
  obtain ⟨w, hw2, hw⟩ := shortensP_exists D (show 0 < ε / 4 by positivity)
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (w + 4)
    (show 0 < ε / (4 * (12 * k + 4)) by positivity)
  have := isPolyT_posrM w ℓ₀ τ
  -- the constants
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 24 * k + 16 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = Z + 2 * D + 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (2 * (w + 4) + 11) * S ^ 3 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (D + 1) * (A + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = P + S + 4 + c * S ^ c + 2 * c + 20 := ⟨_, rfl⟩
  let out : (n : ℕ) → SimpleGraph (Fin n) → Sat3.CNF n → ℕ → Seed n k t (3 * n + 3) → Bool := fun n G φ ℓ ω =>
    decide (cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
      (ConnI.ciF n (edges n (matrix G)) (Decode.toN φ) ω) / 2 % 2 = 1)
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Sat3.CNF n × Seed n k t (3 * n + 3) //
    1 ≤ p.1 ∧ p.1 ≤ n ∧ (∀ C ∈ p.2.2.1, C.length ≤ n ∧ ∀ l ∈ C, l.2 = true) ∧ p.2.2.1.length ≤ D * n}
  have hrun : ∀ x : ι, ∃ T : ℕ, (posrM w ℓ₀ τ).Runs (codeCI x.2.1.2.1 x.2.1.1 x.2.1.2.2.2 x.2.1.2.2.1)
      T (K * (x.1 + 2) ^ K) [out x.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.1 x.2.1.2.2.2] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (ε / 2 * (x.1 : ℝ)) := by
    rintro ⟨n, ⟨ℓ, G, φ, ω⟩, h1, h2, hr, hm⟩
    dsimp only at h1 h2 hr hm ⊢
    have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
    have hpos := toN_pos fun C hC => (hr C hC).2
    obtain ⟨N, hNdef⟩ : ∃ N, N = n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k := ⟨_, rfl⟩
    obtain ⟨s, hsdef⟩ : ∃ s, s = n + ℓ + (3 * n + 3) * k := ⟨_, rfl⟩
    have hsN : s ≤ N := by omega
    have h3N : 3 * n ≤ N := by omega
    -- the closed clauses
    obtain ⟨F, hF⟩ : ∃ F, F = ConnI.ciF n (edges n (matrix G)) [] ω := ⟨_, rfl⟩
    have h0 : Decode.toN ([] : Sat3.CNF n) = [] := rfl
    have hFs : Shaped (w + 4) N F := by
      have := shaped_ci (r := 0) hk G ([] : Sat3.CNF n) ω (by simp)
      rw [h0] at this
      rw [hF, hNdef]; exact shaped_mono this (by omega)
    have hFl : N + F.length + 2 ≤ Z * (n + 2) ^ 2 := by
      have := length_ci_le (D := 0) G ([] : Sat3.CNF n) ω (by simp)
      rw [h0] at this
      rw [hNdef, hF, hZ]; simpa only [Nat.zero_add] using this
    -- the tree
    have hOl : (opens (Decode.toN φ)).length ≤ D * n := by rw [length_opens, Decode.toN, List.length_map]; exact hm
    obtain ⟨t1, t2, t3, t4⟩ := shortensP D w hw2 hw (show w ≤ w + 4 by omega) N s n (opens (Decode.toN φ)) F
      (by omega) (opens_ok hψ) hOl hFs
    have hR : rootQ (codeCI G ℓ ω φ) = ((List.replicate N (), s), (opens (Decode.toN φ), F)) := by
      rw [hNdef, hsdef, hF]; exact read_q G ℓ ω φ
    rw [← hR] at t1 t2 t3 t4
    have hcf : cntS N s ((opens (Decode.toN φ)).map posC ++ F) =
        cntS N s (ConnI.ciF n (edges n (matrix G)) (Decode.toN φ) ω) := by
      rw [cntS_opens _ _ hpos, hF]; simp only [ConnI.ciF, connF, List.append_assoc, List.nil_append]
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (ε / 4 * n) := ⟨_, rfl⟩
    have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by omega
    -- every node has at most S·X² variables and clauses
    have hY : N + F.length + 2 ≤ Z * X ^ 2 := by rw [hX]; exact hFl
    have hX2 : n + 2 ≤ X ^ 2 := by rw [hX]; nlinarith
    have hDn : D * n ≤ D * X ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have eS : S * X ^ 2 = Z * X ^ 2 + 2 * (D * X ^ 2) + X ^ 2 := by rw [hS]; ring
    have e2D : (2 * D + 1) * n = 2 * (D * n) + n := by ring
    have eD1 : (D + 1) * n = D * n + n := by ring
    -- the leaves
    have hNn : (N : ℝ) ≤ (12 * k + 4) * n := by
      have : N ≤ (12 * k + 4) * n := by rw [hNdef]; nlinarith
      exact_mod_cast this
    have hleaf : ∀ x ∈ leaves (stepD w) ((D + 1) * n) (rootQ (codeCI G ℓ ω φ)),
        (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)).Runs x ⌊(c : ℝ) * E⌋₊
          (c * S ^ c * X ^ (2 * c)) (cntS N s (leafD x).2.2) := by
      intro x hx
      obtain ⟨-, g1, g2, g3⟩ := t2 x hx
      obtain ⟨T, hr, hTle⟩ := hc N s (leafD x).2.2 hsN g2
      have e : leafD x = (List.replicate N (), s, (leafD x).2.2) := by simp [leafD, g1]
      rw [← e] at hr
      refine (Stepped.mapIn_runs hr).mono (Nat.le_floor ?_) ?_
      · have e' : ε / (4 * (12 * k + 4)) * (N : ℝ) ≤ ε / 4 * n := by
          calc ε / (4 * (12 * k + 4)) * (N : ℝ) ≤ ε / (4 * (12 * k + 4)) * ((12 * k + 4) * n) :=
                mul_le_mul_of_nonneg_left hNn (by positivity)
            _ = ε / 4 * n := by field_simp
        rw [hE]
        calc (T : ℝ) ≤ c * (2 : ℝ) ^ (ε / (4 * (12 * k + 4)) * (N : ℝ)) := hTle
          _ ≤ c * (2 : ℝ) ^ (ε / 4 * n) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two e') (Nat.cast_nonneg _)
      · have hsp : N + (leafD x).2.2.length + 2 ≤ S * X ^ 2 := by omega
        calc c * (N + (leafD x).2.2.length + 2) ^ c ≤ c * (S * X ^ 2) ^ c :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsp c)
          _ = c * S ^ c * X ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    -- the stack
    have hstack : ∀ i, size ((round (stepD w))^[i] ([rootQ (codeCI G ℓ ω φ)], [])).1 ≤
        ((D + 1) * n + 1) * (A * X ^ 6 + 1) + 1 := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      exact SplitCount.size_list_le s1 fun x hx => by
        obtain ⟨g1, g2, g3, g4, g5⟩ := s2 x hx
        have hYY : S * X ^ 2 ≤ (S * X ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
        have := size_nodeN_le g1 (n := D * n + n) (by omega)
          (fun C hC => ⟨by have := (g3 C hC).1; omega, (g3 C hC).2⟩) g4 g5 (X := S * X ^ 2)
          (by omega) (by omega) (by omega) (by omega)
        calc size x ≤ (2 * (w + 4) + 11) * (S * X ^ 2) ^ 3 := this
          _ = A * X ^ 6 := by rw [hA]; ring
    have hlt : ((leaves (stepD w) ((D + 1) * n) (rootQ (codeCI G ℓ ω φ))).map
        fun x => cntS N s (leafD x).2.2).sum < 2 ^ (N + 1) := by
      rw [← t3]
      exact lt_of_le_of_lt (Consequences.cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have wr := walkSum_runs (stepD w) (root := rootQ)
      (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)) ((D + 1) * n) (codeCI G ℓ ω φ)
      (fun x hx => (t2 x hx).1) (fun x => cntS N s (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ _ _ (N + 1) hleaf hstack hlt
    have hout := Stepped.mapOut_runs (f := postC) wr
    have hval : postC (cntS N s (ConnI.ciF n (edges n (matrix G)) (Decode.toN φ) ω)) = [out n G φ ℓ ω] := by
      rw [hNdef, hsdef]; rfl
    rw [← t3, hcf, hval] at hout
    obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) ((D + 1) * n) (rootQ (codeCI G ℓ ω φ))).length := ⟨_, rfl⟩
    rw [← hL] at hout t1
    refine ⟨_, hout.mono le_rfl ?_, ?_⟩
    · -- the space
      rw [← hX]
      have hpow : X ^ 7 ≤ X ^ (2 * c + 7) := Nat.pow_le_pow_right hX1 (by omega)
      have p1 := stack_le (D := D) (A := A) hX
      rw [← hP] at p1
      have p1' : P * X ^ 7 ≤ P * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ hpow
      have p2 : N + 1 + 1 + 1 + 1 ≤ (S + 4) * X ^ (2 * c + 7) := by
        have h2X : X ^ 2 ≤ X ^ (2 * c + 7) := Nat.pow_le_pow_right hX1 (by omega)
        have hSX : S * X ^ 2 ≤ S * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ h2X
        have h1X : 1 ≤ X ^ (2 * c + 7) := Nat.one_le_pow _ _ hX1
        have e : (S + 4) * X ^ (2 * c + 7) = S * X ^ (2 * c + 7) + 4 * X ^ (2 * c + 7) := by ring
        omega
      have p3 : c * S ^ c * X ^ (2 * c) ≤ c * S ^ c * X ^ (2 * c + 7) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
      have p4 : (P + (S + 4) + c * S ^ c) * X ^ (2 * c + 7) ≤ K * X ^ K := absorb hX1 (by omega) (by omega)
      have e5 : (P + (S + 4) + c * S ^ c) * X ^ (2 * c + 7) =
          P * X ^ (2 * c + 7) + (S + 4) * X ^ (2 * c + 7) + c * S ^ c * X ^ (2 * c + 7) := by ring
      omega
    · -- the time
      have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
      have hLE : (L : ℝ) ≤ E := hE ▸ t1
      have hEE : E * E = (2 : ℝ) ^ (ε / 2 * n) := by
        rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
      have hE0 : 0 ≤ E := by linarith
      have hcK : (c : ℝ) + 2 ≤ (K : ℝ) := by
        have : c + 2 ≤ K := by omega
        exact_mod_cast this
      calc ((L * (⌊(c : ℝ) * E⌋₊ + 2) : ℕ) : ℝ) = (L : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2) := by push_cast; ring
        _ ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
        _ = ((c : ℝ) + 2) * (E * E) := by ring
        _ = ((c : ℝ) + 2) * (2 : ℝ) ^ (ε / 2 * n) := by rw [hEE]
        _ ≤ (K : ℝ) * (2 : ℝ) ^ (ε / 2 * n) := mul_le_mul_of_nonneg_right hcK (by positivity)
  obtain ⟨M', C', hfin, hN⟩ := tm_of_stepped (posrM w ℓ₀ τ) (ι := ι)
    (fun x => codeCI x.2.1.2.1 x.2.1.1 x.2.1.2.2.2 x.2.1.2.2.1)
    (fun x => [out x.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.1 x.2.1.2.2.2]) (fun x => x.1) hε K
    (2 * D + 2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 12) 3
    (fun x => length_codeCI_pos x.2.1.2.1 x.2.1.2.2.2 x.2.1.2.2.1 (fun C hC => (x.2.2.2.2.1 C hC).1) x.2.2.2.2.2
      x.2.2.2.1) hrun
  refine ⟨k, t, n₀, M', C', hfin, fun n ℓ G φ hn h1 h2 hr hm => ⟨out n G φ ℓ,
    fun ω => hN ⟨n, (ℓ, G, φ, ω), h1, h2, hr, hm⟩, fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · have := (hdec n G (Decode.toN φ) ℓ hn (fun C hC => (Decode.mem_toN hC).2) h1).1
      (by rw [← numConn_eq]; exact h0) ω
    simp [out, this]
  · have h := (hdec n G (Decode.toN φ) ℓ hn (fun C hC => (Decode.mem_toN hC).2) h1).2
      (by rw [← numConn_eq]; exact hpos)
    have e : (univ.filter fun ω : Seed n k t (3 * n + 3) =>
        cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
          (ConnI.ciF n (edges n (matrix G)) (Decode.toN φ) ω) / 2 % 2 = 1) =
          univ.filter fun ω => out n G φ ℓ ω = true :=
      Finset.filter_congr fun ω _ => by simp [out]
    rwa [e] at h

end EthCor.PosTM
