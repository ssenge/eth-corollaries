import EthCor.ConnIso
import EthCor.ConnTM

/-! # Connected solutions with one-sided error in time 2^{εn}

The input is the code of G, ℓ in unary, the code of a seed ω with its length in front (`seedL`),
and the code of a CNF φ on the n vertices (`codeCI`). The front end `preR` reads them and writes
the formula `ciF` of `EthCor.ConnI` on 3n + 1 + 2·(3n+3)·k variables with the target n + ℓ + (3n+3)·k.
Anthropic's machine `FromPrinted.Consequences.SIZED` counts it and the last step keeps bit 1. With
`ConnI.ci_decide`: for every width r, exponent D, δ > 0 and ε > 0, one machine runs within C·2^{εn}
steps and outputs, for a random seed, 0 always if no vertex set of size ℓ satisfies φ and induces a
connected subgraph, and 1 with probability at least 2^{−δn} if one does (`conn_randomized`). With φ
the terminals this decides Steiner tree (on ℓ vertices), with φ the edges connected vertex cover. -/

namespace EthCor.ConnITM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Ham EthCor.HamTM
  EthCor.HamI EthCor.HamITM EthCor.Iso EthCor.Conn EthCor.ConnTM EthCor.ConnI

/-! ### The input -/

/-- The code of a seed with its length in unary in front. -/
def seedL {M k t mm : ℕ} (ω : Seed M k t mm) : List Bool := unary (seedCode ω).length ++ seedCode ω

/-- The input: G, ℓ, the seed, φ. -/
noncomputable def codeCI {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (ω : Seed n k t mm) (φ : Sat3.CNF n) : List Bool :=
  code G ++ unary ℓ ++ seedL ω ++ SatFree.enc φ

/-! ### The front end -/

/-- What follows ℓ. -/
def r2 (x : List Bool) : List Bool := rest (rest (sI x))

/-- The seed part. -/
def sdR (x : List Bool) : List Bool := (r2 x).take (ones (rest (sI x)))

/-- The formula φ. -/
def fR (x : List Bool) : Fml := (FreeCode.readFree ((r2 x).drop (ones (rest (sI x))))).2

/-- The number of chain bits. -/
def aR (x : List Bool) : ℕ := dmm (sdR x) * dk (sdR x)

def formR (x : List Bool) : Fml :=
  connF (nH x) (EH x) (fR x) ++ [[(nH x + nH x + nH x, false)]] ++
    isoF (nH x + nH x + nH x) (nH x + nH x + nH x + 1) (dk (sdR x)) (dm1 (sdR x)) (dRows (sdR x)) (dFixes (sdR x)) ++
    compF (nH x + nH x + nH x + 1) (aR x)

def preR (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x + nH x + nH x + 1 + aR x + aR x) (), nH x + lC x + aR x, formR x)

section Poly

variable {α : Type} [Enc α]

theorem compF_polyT {B A : α → ℕ} (hB : PolyT B) (hA : Unary A) : PolyT fun a => compF (B a) (A a) := by
  have hr : PolyT fun a => List.range (A a) := PolyT.range hA
  have hA' := hA.poly
  unfold compF; fun_prop

end Poly

theorem preR_polyT : PolyT preR := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have hr1 : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hr2 : PolyT r2 := by unfold r2 rest; unfold rest at hr1; fun_prop
  have hL : PolyT fun x => ones (rest (sI x)) := (ones_unary hr1).poly
  have hsd : PolyT sdR := by unfold sdR; fun_prop
  have hfp : PolyT fun x => (r2 x).drop (ones (rest (sI x))) := by fun_prop
  have hf : PolyT fR := (FreeCode.readFree_polyT.comp hfp).snd
  have hk : Unary fun x => dk (sdR x) := dn_unary hsd (PolyT.const 0)
  have hmm : Unary fun x => dmm (sdR x) := dn_unary hsd (PolyT.const 2)
  have hA : Unary aR := hmm.mul hk
  have h3 : Unary fun x => nH x + nH x + nH x := (hn.add hn).add hn
  have h3' : PolyT fun x => nH x + nH x + nH x := h3.poly
  have h31 : PolyT fun x => nH x + nH x + nH x + 1 := PolyT.add h3' (PolyT.const 1)
  have hI : PolyT fun x => isoF (nH x + nH x + nH x) (nH x + nH x + nH x + 1) (dk (sdR x)) (dm1 (sdR x))
      (dRows (sdR x)) (dFixes (sdR x)) :=
    isoF_polyT hk h3' h31 (dn_polyT hsd (PolyT.const 1)) (dRows_polyT hsd) (dFixes_polyT hsd)
  have hz : PolyT fun x => [[(nH x + nH x + nH x, false)]] := by fun_prop
  have hF : PolyT formR := by
    unfold formR
    exact PolyT.append (PolyT.append (PolyT.append (connF_polyT hn hE hf) hz) hI) (compF_polyT h31 hA)
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x + 1 + aR x + aR x) () :=
    (((h3.add (Unary.const 1)).add hA).add hA)
  have h2 : PolyT fun x => nH x + lC x + aR x := PolyT.add (PolyT.add hn.poly hl) hA.poly
  exact PolyT.prodMk h1 (PolyT.prodMk h2 hF)

/-- Prepare, count with `SIZED`, keep bit 1. -/
def ciM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn preR (FromPrinted.Consequences.SIZED w ℓ τ)) postC

@[instance_reducible] def isPolyT_ciM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (ciM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preR_polyT
  IsPolyT.mapOut (M := Stepped.mapIn preR (FromPrinted.Consequences.SIZED w ℓ τ)) postC_polyT

/-- **The front end reads G, ℓ, ω and φ.** -/
theorem read_ci {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (ω : Seed n k t mm) (φ : Sat3.CNF n) :
    preR (codeCI G ℓ ω φ) = (List.replicate (n + n + n + 1 + mm * k + mm * k) (), n + ℓ + mm * k,
      ciF n (edges n (matrix G)) (Decode.toN φ) ω) := by
  have e : codeCI G ℓ ω φ = code G ++ (unary ℓ ++ (unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ))) := by
    simp only [codeCI, seedL, List.append_assoc]
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ ++ (unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ)))
  rw [← e] at hn hE hs
  have hl : lC (codeCI G ℓ ω φ) = ℓ := by rw [lC, hs, Read.ones_unary_append]
  have hr1 : rest (sI (codeCI G ℓ ω φ)) = unary (seedCode ω).length ++ (seedCode ω ++ SatFree.enc φ) := by
    rw [hs, Read.rest_unary_append]
  have hL : ones (rest (sI (codeCI G ℓ ω φ))) = (seedCode ω).length := by rw [hr1, Read.ones_unary_append]
  have hr2 : r2 (codeCI G ℓ ω φ) = seedCode ω ++ SatFree.enc φ := by rw [r2, hr1, Read.rest_unary_append]
  have hsd : sdR (codeCI G ℓ ω φ) = seedCode ω := by rw [sdR, hr2, hL, List.take_left' rfl]
  have hf : fR (codeCI G ℓ ω φ) = Decode.toN φ := by
    rw [fR, hr2, hL, List.drop_left' rfl, FreeCode.reads_readFree n φ]
  obtain ⟨ek, em1, emm, -, eR, eF⟩ := decode_seedCode ω
  have hA : aR (codeCI G ℓ ω φ) = mm * k := by rw [aR, hsd, ek, emm]
  rw [preR, formR, hA, hn, hE, hl, hf, hsd, ek, em1, eR, eF, ciF]

/-! ### Sizes -/

theorem length_compF (B A : ℕ) : (compF B A).length = 2 * A := by
  simp [compF, List.length_flatMap, mul_comm]

theorem shaped_ci {n r k t mm : ℕ} (hk : 1 ≤ k) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (ω : Seed n k t mm)
    (hr : ∀ C ∈ φ, C.length ≤ r) :
    Shaped (r + 4) (n + n + n + 1 + mm * k + mm * k) (ciF n (edges n (matrix G)) (Decode.toN φ) ω) := by
  intro D hD
  simp only [ciF, List.mem_append] at hD
  rcases hD with ((hD | hD) | hD) | hD
  · obtain ⟨h1, h2⟩ := shaped_connF G φ hr D (by simp only [connF, List.mem_append] at hD ⊢; exact hD)
    exact ⟨h1, fun l hl => by have := h2 l hl; omega⟩
  · rw [List.mem_singleton] at hD; subst hD
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega
  · obtain ⟨h1, h2⟩ := isoF_clause (by omega) (by omega) hk ω hD
    exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · rw [compF] at hD
    obtain ⟨i, hi, hD⟩ := List.mem_flatMap.1 hD
    rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> simp <;> omega

theorem length_ci_le {n D k t : ℕ} (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n) (ω : Seed n k t (3 * n + 3))
    (hm : φ.length ≤ (n + 2) ^ D) :
    n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k + (ciF n (edges n (matrix G)) (Decode.toN φ) ω).length + 2 ≤
      (24 * k + 16) * (n + 2) ^ (D + 2) := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hc := length_connF_le (n := n) (edges n (matrix G)) (Decode.toN φ)
  have hφl : (Decode.toN φ).length = φ.length := by rw [Decode.toN, List.length_map]
  have hE := length_edges_sq (n := n) (matrix G)
  have hI := length_isoF_le (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω)
  rw [length_rowsOf] at hI
  have hfx := length_fixesOf_le ω
  have hcomp := length_compF (n + n + n + 1) ((3 * n + 3) * k)
  have hlen : (ciF n (edges n (matrix G)) (Decode.toN φ) ω).length =
      (connF n (edges n (matrix G)) (Decode.toN φ)).length + 1 +
      (isoF (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω)).length +
      (compF (n + n + n + 1) ((3 * n + 3) * k)).length := by
    simp only [ciF, List.length_append, List.length_singleton]
  have q1 : (3 * n + 3) * k ≤ 3 * k * X := by rw [hX]; nlinarith
  have q2 : (3 * n + 3) * (k * 4) ≤ 12 * k * X := by rw [hX]; nlinarith
  have q3 : n * n ≤ X ^ 2 := by rw [hX]; nlinarith
  have q4 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have q5 : X ^ 2 ≤ X ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : X ^ D ≤ X ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have q7 : k * X ≤ k * X ^ (D + 2) := Nat.mul_le_mul_left _ (q4.trans q5)
  have e : (24 * k + 16) * X ^ (D + 2) = 24 * (k * X ^ (D + 2)) + 16 * X ^ (D + 2) := by ring
  rw [← hX] at hm ⊢
  have : 3 * k * X = 3 * (k * X) := by ring
  have : 12 * k * X = 12 * (k * X) := by ring
  omega

theorem length_seedCode_le {n k t : ℕ} (ω : Seed n k t (3 * n + 3)) :
    (seedCode ω).length ≤ ((k + 5) + (k + 4) * (6 * k + 5)) * (n + 2) ^ 2 := by
  rw [length_seedCode]
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hW : n + k + (3 * n + 3) + 1 ≤ (k + 4) * X := by rw [hX]; nlinarith
  have hC : 4 + (3 * n + 3) * (2 * k + 1) + n * 2 ≤ (6 * k + 5) * X := by rw [hX]; nlinarith
  have hWC := Nat.mul_le_mul hC hW
  have e1 : (6 * k + 5) * X * ((k + 4) * X) = (k + 4) * (6 * k + 5) * X ^ 2 := by ring
  have q : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have e2 : ((k + 5) + (k + 4) * (6 * k + 5)) * X ^ 2 = (k + 5) * X ^ 2 + (k + 4) * (6 * k + 5) * X ^ 2 := by ring
  have q2 : (k + 4) * X + 1 ≤ (k + 5) * X ^ 2 := by
    have : (k + 4) * X ≤ (k + 4) * X ^ 2 := Nat.mul_le_mul_left _ q
    have : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  rw [← hX]
  omega

theorem length_codeCI_le {n r D k t ℓ : ℕ} (G : SimpleGraph (Fin n)) (ω : Seed n k t (3 * n + 3)) (φ : Sat3.CNF n)
    (hr : ∀ C ∈ φ, C.length ≤ r) (hm : φ.length ≤ (n + 2) ^ D) (hℓ : ℓ ≤ n) :
    (codeCI G ℓ ω φ).length + 1 ≤ (2 * r + 2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 12) * (n + 2) ^ (D + 2) := by
  obtain ⟨B, hB⟩ : ∃ B, B = (k + 5) + (k + 4) * (6 * k + 5) := ⟨_, rfl⟩
  have hS := length_seedCode_le ω
  rw [← hB] at hS ⊢
  have h1 := length_enc_le φ hr
  have h2 : φ.length * ((2 * r + 2) * (n + 2)) ≤ (2 * r + 2) * (n + 2) ^ (D + 2) := by
    calc φ.length * ((2 * r + 2) * (n + 2)) ≤ (n + 2) ^ D * ((2 * r + 2) * (n + 2)) := Nat.mul_le_mul_right _ hm
      _ = (2 * r + 2) * (n + 2) ^ (D + 1) := by ring
      _ ≤ (2 * r + 2) * (n + 2) ^ (D + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : (n + 2) ^ 2 ≤ (n + 2) ^ (D + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n * n + 6 * n + 6 ≤ 6 * (n + 2) ^ 2 := by nlinarith
  have h5 : B * (n + 2) ^ 2 ≤ B * (n + 2) ^ (D + 2) := Nat.mul_le_mul_left _ h3
  have e : (2 * r + 2 * B + 12) * (n + 2) ^ (D + 2) =
      (2 * r + 2) * (n + 2) ^ (D + 2) + 2 * (B * (n + 2) ^ (D + 2)) + 10 * (n + 2) ^ (D + 2) := by ring
  have eu : ∀ m, (unary m).length = m + 1 := fun m => by simp [unary]
  simp only [codeCI, seedL, List.length_append, length_code_eq, eu]
  omega

/-! ### The theorem -/

open Classical in
/-- **Connected solutions with one-sided error in time C·2^{εn}.** For every width r, exponent D,
δ > 0 and ε > 0 there are k, t, n₀ and one Turing machine with finite alphabets such that for every
graph G on n ≥ n₀ vertices (of any density), 1 ≤ ℓ ≤ n and every CNF φ on the vertices with clauses
of at most r literals and at most (n+2)^D clauses: run on `codeCI G ℓ ω φ` for a seed ω of
`Seed n k t (3n + 3)`, it halts within ⌊C·2^{εn}⌋ steps with one bit out(ω); if no vertex set X of
size ℓ satisfies φ and induces a connected subgraph, out(ω) = 0 for every seed; if one does,
out(ω) = 1 for at least a 2^{−δn} fraction of the seeds. -/
theorem conn_randomized (r D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (φ : Sat3.CNF n), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      (∀ C ∈ φ, C.length ≤ r) → φ.length ≤ (n + 2) ^ D →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCI G ℓ ω φ) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numConn G φ ℓ = 0 → ∀ ω, out ω = false) ∧
        (0 < numConn G φ ℓ →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, hk, -, n₀, hdec⟩ := ci_decide δ hδ
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (r + 4)
    (show 0 < ε / (2 * (12 * k + 4)) by positivity)
  have := isPolyT_ciM (r + 4) ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * (24 * k + 16) ^ c + (D + 2) * c + c + 1 := ⟨_, rfl⟩
  let out : (n : ℕ) → SimpleGraph (Fin n) → Sat3.CNF n → ℕ → Seed n k t (3 * n + 3) → Bool := fun n G φ ℓ ω =>
    decide (cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
      (ciF n (edges n (matrix G)) (Decode.toN φ) ω) / 2 % 2 = 1)
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Sat3.CNF n × Seed n k t (3 * n + 3) //
    1 ≤ p.1 ∧ p.1 ≤ n ∧ (∀ C ∈ p.2.2.1, C.length ≤ r) ∧ p.2.2.1.length ≤ (n + 2) ^ D}
  have hrun : ∀ x : ι, ∃ T : ℕ, (ciM (r + 4) ℓ₀ τ).Runs (codeCI x.2.1.2.1 x.2.1.1 x.2.1.2.2.2 x.2.1.2.2.1)
      T (K * (x.1 + 2) ^ K) [out x.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.1 x.2.1.2.2.2] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (ε / 2 * (x.1 : ℝ)) := by
    rintro ⟨n, ⟨ℓ, G, φ, ω⟩, h1, h2, hr, hm⟩
    dsimp only at h1 h2 hr hm ⊢
    obtain ⟨T, hT, hTle⟩ := hc (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
      (ciF n (edges n (matrix G)) (Decode.toN φ) ω) (by omega) (shaped_ci hk G φ ω hr)
    rw [← read_ci G ℓ ω φ] at hT
    refine ⟨T, ?_, ?_⟩
    · have hout := Stepped.mapOut_runs (f := postC) (Stepped.mapIn_runs hT)
      refine hout.mono le_rfl ?_
      have hX := length_ci_le G φ ω hm
      calc c * (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k +
            (ciF n (edges n (matrix G)) (Decode.toN φ) ω).length + 2) ^ c
          ≤ c * ((24 * k + 16) * (n + 2) ^ (D + 2)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
        _ = c * (24 * k + 16) ^ c * (n + 2) ^ ((D + 2) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
        _ ≤ K * (n + 2) ^ K := Nat.mul_le_mul (by rw [hK]; omega) (Nat.pow_le_pow_right (by omega) (by rw [hK]; omega))
    · have hN : ((n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ) ≤ (12 * k + 4) * n := by
        have : n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k ≤ (12 * k + 4) * n := by nlinarith
        exact_mod_cast this
      have hpos : (0 : ℝ) < 12 * k + 4 := by positivity
      have e : ε / (2 * (12 * k + 4)) * ((n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ) ≤ ε / 2 * n := by
        calc ε / (2 * (12 * k + 4)) * ((n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ)
            ≤ ε / (2 * (12 * k + 4)) * ((12 * k + 4) * n) := mul_le_mul_of_nonneg_left hN (by positivity)
          _ = ε / 2 * n := by field_simp
      calc (T : ℝ) ≤ c * (2 : ℝ) ^ (ε / (2 * (12 * k + 4)) *
            ((n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ)) := hTle
        _ ≤ c * (2 : ℝ) ^ (ε / 2 * n) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two e) (Nat.cast_nonneg _)
        _ ≤ K * (2 : ℝ) ^ (ε / 2 * n) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)
  obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (ciM (r + 4) ℓ₀ τ) (ι := ι)
    (fun x => codeCI x.2.1.2.1 x.2.1.1 x.2.1.2.2.2 x.2.1.2.2.1)
    (fun x => [out x.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.1 x.2.1.2.2.2]) (fun x => x.1) hε K
    (2 * r + 2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 12) (D + 2)
    (fun x => length_codeCI_le x.2.1.2.1 x.2.1.2.2.2 x.2.1.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.2.2.2.1) hrun
  refine ⟨k, t, n₀, N, C', hfin, fun n ℓ G φ hn h1 h2 hr hm => ⟨out n G φ ℓ, fun ω => hN ⟨n, (ℓ, G, φ, ω), h1, h2, hr, hm⟩,
    fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
    have := (hdec n G (Decode.toN φ) ℓ hn hψ h1).1 (by rw [← numConn_eq]; exact h0) ω
    simp [out, this]
  · have hψ : ∀ C ∈ Decode.toN φ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
    have h := (hdec n G (Decode.toN φ) ℓ hn hψ h1).2 (by rw [← numConn_eq]; exact hpos)
    have e : (univ.filter fun ω : Seed n k t (3 * n + 3) =>
        cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
          (ciF n (edges n (matrix G)) (Decode.toN φ) ω) / 2 % 2 = 1) = univ.filter fun ω => out n G φ ℓ ω = true :=
      Finset.filter_congr fun ω _ => by simp [out]
    rwa [e] at h

end EthCor.ConnITM
