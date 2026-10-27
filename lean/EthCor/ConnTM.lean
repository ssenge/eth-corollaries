import EthCor.ConnFormula
import EthCor.HamIsoTM
import FromPrinted.Sets
import GraphProblems.Host
import GraphProblems.SetTM
import FreeCode.ReaderCert
import FreeCode.Reader

/-! # The parity of the number of connected solutions in time C·2^{δn}

The input is the code of G, then ℓ in unary, then the code `SatFree.enc φ` of a CNF φ on the n
vertices. The front end `preC` writes the formula `connF n E (toN φ)` of `EthCor.Conn` on 3n
variables with the target n + ℓ for the number of true variables. Anthropic's machine
`FromPrinted.Consequences.SIZED` counts its satisfying assignments with n + ℓ true variables, and
the last step keeps bit 1 of the count. By `Conn.conn_parity` this bit is the parity of the number of
vertex sets X of size ℓ with X ⊨ φ and G[X] connected (`conn_parity_tm`). With φ = the terminals
these are the vertex sets of the Steiner trees with ℓ vertices; with φ = the edges they are the
connected vertex covers of size ℓ. The graph may be dense: the formula has 3n variables. -/

namespace EthCor.ConnTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Ham EthCor.HamTM
  EthCor.HamITM EthCor.Conn

open Classical in
/-- The vertex sets of size ℓ that satisfy φ and induce a connected subgraph of G. -/
noncomputable def numConn {n : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (ℓ : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (∀ C ∈ φ, ∃ l ∈ C, x l.1 = l.2) ∧
    (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected).card

theorem sat_toN {n : ℕ} (φ : Sat3.CNF n) (x : Fin n → Bool) :
    (∀ C ∈ Decode.toN φ, ∃ l ∈ C, ext x l.1 = l.2) ↔ ∀ C ∈ φ, ∃ l ∈ C, x l.1 = l.2 := by
  simp [Decode.toN, ext_fin]

theorem numConn_eq {n : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (ℓ : ℕ) :
    numConn G φ ℓ = numConnF G (Decode.toN φ) ℓ := by
  unfold numConn numConnF
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, sat_toN]

/-! ### The front end and the last step -/

/-- ℓ: the unary number after the matrix. -/
def lC (x : List Bool) : ℕ := ones (sI x)

/-- φ: the formula after ℓ. -/
def fC (x : List Bool) : Fml := (FreeCode.readFree (rest (sI x))).2

def preC (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x + nH x + nH x) (), nH x + lC x, connF (nH x) (EH x) (fC x))

/-- Bit 1 of the count. -/
def postC (N : ℕ) : List Bool := [decide (N / 2 % 2 = 1)]

section Poly

variable {α : Type} [Enc α]

theorem sideF_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun a => sideF (n a) := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  have hn' := hn.poly
  unfold sideF; fun_prop

theorem edgeCC_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : PolyT n) (hE : PolyT E) :
    PolyT fun a => edgeCC (n a) (E a) := by
  unfold edgeCC; fun_prop

theorem connF_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} {ψ : α → Fml} (hn : Unary n) (hE : PolyT E)
    (hψ : PolyT ψ) : PolyT fun a => connF (n a) (E a) (ψ a) := by
  unfold connF
  exact PolyT.append (PolyT.append hψ (sideF_polyT hn)) (edgeCC_polyT hn.poly hE)

end Poly

theorem preC_polyT : PolyT preC := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have hrs : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hf : PolyT fC := (FreeCode.readFree_polyT.comp hrs).snd
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x) () := (hn.add hn).add hn
  have h2 : PolyT fun x => nH x + lC x := PolyT.add hn.poly hl
  have h3 : PolyT fun x => connF (nH x) (EH x) (fC x) := connF_polyT hn hE hf
  exact PolyT.prodMk h1 (PolyT.prodMk h2 h3)

theorem postC_polyT : PolyT postC := by unfold postC; fun_prop

/-- Prepare, count with `SIZED`, keep bit 1. -/
def connM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preC (FromPrinted.Consequences.SIZED w ℓ τ)) postC

@[instance_reducible] def isPolyT_connM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (connM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preC_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preC (FromPrinted.Consequences.SIZED w ℓ τ)) postC_polyT

theorem read_conn {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (φ : Sat3.CNF n) :
    preC (code G ++ unary ℓ ++ SatFree.enc φ) =
      (List.replicate (n + n + n) (), n + ℓ, connF n (edges n (matrix G)) (Decode.toN φ)) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ ++ SatFree.enc φ)
  rw [List.append_assoc, preC, lC, fC, hn, hE, hs, Read.ones_unary_append, Read.rest_unary_append,
    FreeCode.reads_readFree n φ]

/-! ### Sizes -/

theorem shaped_connF {n r : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (hr : ∀ C ∈ φ, C.length ≤ r) :
    Shaped (r + 4) (n + n + n) (connF n (edges n (matrix G)) (Decode.toN φ)) := by
  have hE := edges_bound n (matrix G)
  intro D hD
  simp only [connF, List.mem_append] at hD
  rcases hD with (hD | hD) | hD
  · obtain ⟨⟨C, hC, e⟩, hv⟩ := Decode.mem_toN hD
    exact ⟨by rw [e]; have := hr C hC; omega, fun l hl => by have := hv l hl; omega⟩
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

theorem length_edges_sq {n : ℕ} (M : List Bool) : (edges n M).length ≤ n * n := by
  unfold edges
  exact (List.length_filter_le _ _).trans (by rw [GraphProblems.pairs, List.length_product, List.length_range])

theorem length_connF_le {n : ℕ} (E : List (ℕ × ℕ)) (ψ : Fml) :
    (connF n E ψ).length = ψ.length + 3 * n + 2 * E.length := by
  simp only [connF, sideF, edgeCC, List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  simp; ring

theorem length_enc_le {n r : ℕ} (φ : Sat3.CNF n) (hr : ∀ C ∈ φ, C.length ≤ r) :
    (SatFree.enc φ).length ≤ n + 2 + φ.length * ((2 * r + 2) * (n + 2)) := by
  have hC : ∀ C ∈ φ, (SatFree.encClause C).length ≤ (2 * r + 2) * (n + 2) := by
    intro C hC
    have e : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by
      simp [SatFree.encClause, SatFree.encLit, List.length_flatMap]; ring
    have hW : Nat.log2 (2 * n) + 2 ≤ 2 * (n + 2) := by have := Nat.log2_le_self (2 * n); omega
    rw [e]
    have e1 : C.length * (Nat.log2 (2 * n) + 2) ≤ r * (2 * (n + 2)) := Nat.mul_le_mul (hr C hC) hW
    have e2 : (2 * r + 2) * (n + 2) = r * (2 * (n + 2)) + 2 * (n + 2) := by ring
    omega
  have hsum := length_flatMap_le φ SatFree.encClause _ hC
  have e : (SatFree.enc φ).length = n + 1 + ((φ.flatMap SatFree.encClause).length + 1) := by
    simp [SatFree.enc]; ring
  omega

theorem length_input_conn {n r D ℓ : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (hr : ∀ C ∈ φ, C.length ≤ r)
    (hm : φ.length ≤ (n + 2) ^ D) (hℓ : ℓ ≤ n) :
    (code G ++ unary ℓ ++ SatFree.enc φ).length + 1 ≤ (2 * r + 8) * (n + 2) ^ (D + 2) := by
  have h1 := length_enc_le φ hr
  have h2 : φ.length * ((2 * r + 2) * (n + 2)) ≤ (2 * r + 2) * (n + 2) ^ (D + 2) := by
    calc φ.length * ((2 * r + 2) * (n + 2)) ≤ (n + 2) ^ D * ((2 * r + 2) * (n + 2)) := Nat.mul_le_mul_right _ hm
      _ = (2 * r + 2) * (n + 2) ^ (D + 1) := by ring
      _ ≤ (2 * r + 2) * (n + 2) ^ (D + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : (n + 2) ^ 2 ≤ (n + 2) ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n * n + 6 * n + 6 ≤ 6 * (n + 2) ^ 2 := by nlinarith
  have e : (2 * r + 8) * (n + 2) ^ (D + 2) = (2 * r + 2) * (n + 2) ^ (D + 2) + 6 * (n + 2) ^ (D + 2) := by ring
  have eu : (unary ℓ).length = ℓ + 1 := by simp [unary]
  rw [List.length_append, List.length_append, length_code_eq, eu]
  omega

/-! ### The theorem -/

/-- **The parity of the number of connected solutions in time C·2^{δn}.** For every width r,
exponent D and δ > 0, one Turing machine with finite alphabets: given a graph G on n vertices (of
any density), 1 ≤ ℓ ≤ n in unary, and a CNF φ on the n vertices with clauses of at most r literals
and at most (n+2)^D clauses, it outputs whether the number of vertex sets X of size ℓ with X ⊨ φ and
G[X] connected is odd, within ⌊C·2^{δn}⌋ steps. -/
theorem conn_parity_tm (r D : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), 1 ≤ ℓ → ℓ ≤ n → (∀ C ∈ φ, C.length ≤ r) →
      φ.length ≤ (n + 2) ^ D →
        Wrap.Outputs M (code G ++ unary ℓ ++ SatFree.enc φ) [decide (numConn G φ ℓ % 2 = 1)]
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (r + 4) (show 0 < δ / 6 by positivity)
  have := isPolyT_connM (r + 4) ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * 6 ^ c + c * (D + 2) + c + 1 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Sat3.CNF n //
    1 ≤ p.1 ∧ p.1 ≤ n ∧ (∀ C ∈ p.2.2, C.length ≤ r) ∧ p.2.2.length ≤ (n + 2) ^ D}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (connM (r + 4) ℓ₀ τ).Runs (code x.2.1.2.1 ++ unary x.2.1.1 ++ SatFree.enc x.2.1.2.2)
      T (K * (x.1 + 2) ^ K) [decide (numConn x.2.1.2.1 x.2.1.2.2 x.2.1.1 % 2 = 1)] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (connM (r + 4) ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2.1 ++ unary x.2.1.1 ++ SatFree.enc x.2.1.2.2)
      (fun x => [decide (numConn x.2.1.2.1 x.2.1.2.2 x.2.1.1 % 2 = 1)]) (fun x => x.1) hδ K (2 * r + 8) (D + 2)
      (fun x => length_input_conn x.2.1.2.1 x.2.1.2.2 x.2.2.2.2.1 x.2.2.2.2.2 x.2.2.2.1) hrun
    exact ⟨N, C', hfin, fun n ℓ G φ h1 h2 hr hm => hN ⟨n, (ℓ, G, φ), h1, h2, hr, hm⟩⟩
  rintro ⟨n, ⟨ℓ, G, φ⟩, h1, h2, hr, hm⟩
  dsimp only at h1 h2 hr hm ⊢
  have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
  obtain ⟨T, hT, hTle⟩ := hc (n + n + n) (n + ℓ) (connF n (edges n (matrix G)) (Decode.toN φ)) (by omega)
    (shaped_connF G φ hr)
  rw [← read_conn G ℓ φ] at hT
  refine ⟨T, ?_, ?_⟩
  · have hout := Stepped.mapOut_runs (f := postC) (Stepped.mapIn_runs hT)
    rw [postC, conn_parity G hψ h1, ← numConn_eq] at hout
    refine hout.mono le_rfl ?_
    have hl := length_connF_le (n := n) (edges n (matrix G)) (Decode.toN φ)
    have hφl : (Decode.toN φ).length = φ.length := by rw [Decode.toN, List.length_map]
    have hE := length_edges_sq (n := n) (matrix G)
    have hX : n + n + n + (connF n (edges n (matrix G)) (Decode.toN φ)).length + 2 ≤ 6 * (n + 2) ^ (D + 2) := by
      have h3 : (n + 2) ^ 2 ≤ (n + 2) ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : (n + 2) ^ D ≤ (n + 2) ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h5 : 2 * (n * n) + 6 * n + 2 ≤ 2 * (n + 2) ^ 2 := by nlinarith
      omega
    calc c * (n + n + n + (connF n (edges n (matrix G)) (Decode.toN φ)).length + 2) ^ c
        ≤ c * (6 * (n + 2) ^ (D + 2)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
      _ = c * 6 ^ c * (n + 2) ^ ((D + 2) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ K * (n + 2) ^ K := Nat.mul_le_mul (by rw [hK]; omega) (Nat.pow_le_pow_right (by omega)
          (by rw [hK]; have : (D + 2) * c = c * (D + 2) := by ring
              omega))
  · have e : δ / 6 * ((n + n + n : ℕ) : ℝ) = δ / 2 * n := by push_cast; ring
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 6 * ((n + n + n : ℕ) : ℝ)) := hTle
      _ = c * (2 : ℝ) ^ (δ / 2 * n) := by rw [e]
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)

/-! ### Connected vertex covers -/

/-- Every edge has an end in the set. -/
def vcF (E : List (ℕ × ℕ)) : Fml := E.map fun p => [(p.1, true), (p.2, true)]

open Classical in
/-- The connected vertex covers of G with ℓ vertices. -/
noncomputable def numCVC {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (∀ u v, G.Adj u v → x u = true ∨ x v = true) ∧
    (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected).card

theorem sat_vcF {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    (∀ C ∈ vcF (edges n (matrix G)), ∃ l ∈ C, ext x l.1 = l.2) ↔ ∀ u v, G.Adj u v → x u = true ∨ x v = true := by
  have hE := edges_bound n (matrix G)
  simp only [vcF, List.forall_mem_map, EthCor.HamS.sat2]
  constructor
  · intro h u v huv
    rcases lt_trichotomy u v with h' | rfl | h'
    · have := h _ ((mem_edges stAdj G u v).2 ⟨h', huv⟩)
      simpa only [ext_fin] using this
    · exact absurd huv (G.loopless.irrefl _)
    · have := h _ ((mem_edges stAdj G v u).2 ⟨h', huv.symm⟩)
      simp only [ext_fin] at this
      exact this.symm
  · intro h p hp
    obtain ⟨h1, h2⟩ := hE p hp
    have hm := (mem_edges stAdj G ⟨p.1, by omega⟩ ⟨p.2, h2⟩).1 hp
    have := h _ _ hm.2
    rw [← ext_fin x ⟨p.1, by omega⟩, ← ext_fin x ⟨p.2, h2⟩] at this
    exact this

theorem numCVC_eq {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) :
    numCVC G ℓ = numConnF G (vcF (edges n (matrix G))) ℓ := by
  unfold numCVC numConnF
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, sat_vcF]

def preV (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x + nH x + nH x) (), nH x + lC x, connF (nH x) (EH x) (vcF (EH x)))

theorem preV_polyT : PolyT preV := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have hv : PolyT fun x => vcF (EH x) := by unfold vcF; fun_prop
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x) () := (hn.add hn).add hn
  have h2 : PolyT fun x => nH x + lC x := PolyT.add hn.poly hl
  have h3 : PolyT fun x => connF (nH x) (EH x) (vcF (EH x)) := connF_polyT hn hE hv
  exact PolyT.prodMk h1 (PolyT.prodMk h2 h3)

def cvcM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preV (FromPrinted.Consequences.SIZED w ℓ τ)) postC

@[instance_reducible] def isPolyT_cvcM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (cvcM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preV_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preV (FromPrinted.Consequences.SIZED w ℓ τ)) postC_polyT

theorem read_cvc {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) :
    preV (code G ++ unary ℓ) =
      (List.replicate (n + n + n) (), n + ℓ, connF n (edges n (matrix G)) (vcF (edges n (matrix G)))) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ)
  have h1 : ones (unary ℓ) = ℓ := by simpa using Read.ones_unary_append ℓ []
  rw [preV, lC, hn, hE, hs, h1]

theorem shaped_cvc {n : ℕ} (G : SimpleGraph (Fin n)) :
    Shaped 4 (n + n + n) (connF n (edges n (matrix G)) (vcF (edges n (matrix G)))) := by
  have hE := edges_bound n (matrix G)
  intro D hD
  simp only [connF, List.mem_append] at hD
  rcases hD with (hD | hD) | hD
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hD
    have := hE p hp
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp <;> omega
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

/-- **The parity of the number of connected vertex covers in time C·2^{δn}.** For every δ > 0, one
Turing machine with finite alphabets: given a graph G on n vertices (of any density) and 1 ≤ ℓ ≤ n in
unary, it outputs whether G has an odd number of connected vertex covers with ℓ vertices, within
⌊C·2^{δn}⌋ steps. -/
theorem cvc_parity_tm {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ ℓ → ℓ ≤ n →
      Wrap.Outputs M (code G ++ unary ℓ) [decide (numCVC G ℓ % 2 = 1)] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 4 (show 0 < δ / 6 by positivity)
  have := isPolyT_cvcM 4 ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * 10 ^ c + 2 * c + c + 1 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // 1 ≤ p.1 ∧ p.1 ≤ n}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (cvcM 4 ℓ₀ τ).Runs (code x.2.1.2 ++ unary x.2.1.1)
      T (K * (x.1 + 2) ^ K) [decide (numCVC x.2.1.2 x.2.1.1 % 2 = 1)] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (cvcM 4 ℓ₀ τ) (ι := ι)
      (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => [decide (numCVC x.2.1.2 x.2.1.1 % 2 = 1)]) (fun x => x.1) hδ K 6 2 (fun x => by
        have := x.2.2.2
        rw [List.length_append, length_code_eq]
        simp only [unary, List.length_append, List.length_replicate, List.length_singleton]
        nlinarith) hrun
    exact ⟨N, C', hfin, fun n ℓ G h1 h2 => hN ⟨n, (ℓ, G), h1, h2⟩⟩
  rintro ⟨n, ⟨ℓ, G⟩, h1, h2⟩
  dsimp only at h1 h2 ⊢
  have hψ : ∀ C ∈ vcF (edges n (matrix G)), ∀ l ∈ C, l.1 < n := by
    intro C hC l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hC
    have := edges_bound n (matrix G) p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp <;> omega
  obtain ⟨T, hT, hTle⟩ := hc (n + n + n) (n + ℓ) (connF n (edges n (matrix G)) (vcF (edges n (matrix G))))
    (by omega) (shaped_cvc G)
  rw [← read_cvc G ℓ] at hT
  refine ⟨T, ?_, ?_⟩
  · have hout := Stepped.mapOut_runs (f := postC) (Stepped.mapIn_runs hT)
    rw [postC, conn_parity G hψ h1, ← numCVC_eq] at hout
    refine hout.mono le_rfl ?_
    have hl := length_connF_le (n := n) (edges n (matrix G)) (vcF (edges n (matrix G)))
    have hv : (vcF (edges n (matrix G))).length = (edges n (matrix G)).length := by rw [vcF, List.length_map]
    have hE := length_edges_sq (n := n) (matrix G)
    have hX : n + n + n + (connF n (edges n (matrix G)) (vcF (edges n (matrix G)))).length + 2 ≤
        10 * (n + 2) ^ 2 := by
      have h5 : 3 * (n * n) + 6 * n + 2 ≤ 3 * (n + 2) ^ 2 := by nlinarith
      omega
    calc c * (n + n + n + (connF n (edges n (matrix G)) (vcF (edges n (matrix G)))).length + 2) ^ c
        ≤ c * (10 * (n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
      _ = c * 10 ^ c * (n + 2) ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ K * (n + 2) ^ K := Nat.mul_le_mul (by rw [hK]; omega) (Nat.pow_le_pow_right (by omega) (by rw [hK]; omega))
  · have e : δ / 6 * ((n + n + n : ℕ) : ℝ) = δ / 2 * n := by push_cast; ring
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 6 * ((n + n + n : ℕ) : ℝ)) := hTle
      _ = c * (2 : ℝ) ^ (δ / 2 * n) := by rw [e]
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)

end EthCor.ConnTM
