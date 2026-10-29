import EthCor.ForestTM

/-! # Feedback vertex set with one-sided error in time C·2^{εn}, for O(n) edges

The input is the code of G, s in unary and the code of a seed ω with its length in front
(`codeFI`). The front end `preQ` writes the formula `isoAdd N₀ (fvsF n E []) ω` of `EthCor.Forest`
on N₀ + 1 + 2·(3n+3)·k variables, N₀ = 3n + 2m, with the target n + s + m + (3n+3)·k. Anthropic's
machine `FromPrinted.Consequences.SIZED` counts it, and the last step, which reads s again from the
input, keeps bit s of the count. With `Forest.fi_decide`: for every D, δ > 0 and ε > 0, one machine
runs within C·2^{εn} steps on graphs with at most D·n edges and outputs, for a random seed, 0
always if no induced forest has s vertices, and 1 with probability at least 2^{−δn} if one does
(`for_randomized`). With s = n − k this decides whether G has a feedback vertex set with at most k
vertices (`fvs_randomized`). -/

namespace EthCor.ForestITM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Ham EthCor.HamTM
  EthCor.HamI EthCor.HamITM EthCor.Iso EthCor.Conn EthCor.ConnTM EthCor.ConnI EthCor.ConnITM EthCor.Forest
  EthCor.ForestTM

/-- The input: G, s, the seed. -/
noncomputable def codeFI {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) (ω : Seed n k t mm) : List Bool :=
  code G ++ unary s ++ seedL ω

/-! ### The front end -/

/-- The number of variables of `fvsF`. -/
def nQ (x : List Bool) : ℕ := nH x + nH x + nH x + (EH x).length + (EH x).length

def formQ (x : List Bool) : Fml :=
  fvsF (nH x) (EH x) [] ++ [[(nQ x, false)]] ++
    isoF (nQ x) (nQ x + 1) (dk (sdR x)) (dm1 (sdR x)) (dRows (sdR x)) (dFixes (sdR x)) ++ compF (nQ x + 1) (aR x)

def preQ (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nQ x + 1 + aR x + aR x) (), nH x + lC x + (EH x).length + aR x, formQ x)

theorem preQ_polyT : PolyT preQ := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC ones; fun_prop
  have hr1 : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hr2 : PolyT r2 := by unfold r2 rest; unfold rest at hr1; fun_prop
  have hsd : PolyT sdR := by unfold sdR; fun_prop
  have hk : Unary fun x => dk (sdR x) := dn_unary hsd (PolyT.const 0)
  have hmm : Unary fun x => dmm (sdR x) := dn_unary hsd (PolyT.const 2)
  have hA : Unary aR := hmm.mul hk
  have hm : Unary fun x => (EH x).length := Unary.of_length hE
  have hN : Unary nQ := (((hn.add hn).add hn).add hm).add hm
  have hN' : PolyT nQ := hN.poly
  have hN1 : PolyT fun x => nQ x + 1 := PolyT.add hN' (PolyT.const 1)
  have hI : PolyT fun x => isoF (nQ x) (nQ x + 1) (dk (sdR x)) (dm1 (sdR x)) (dRows (sdR x)) (dFixes (sdR x)) :=
    isoF_polyT hk hN' hN1 (dn_polyT hsd (PolyT.const 1)) (dRows_polyT hsd) (dFixes_polyT hsd)
  have hz : PolyT fun x => [[(nQ x, false)]] := by fun_prop
  have hF : PolyT formQ := by
    unfold formQ
    exact PolyT.append (PolyT.append (PolyT.append (fvsF_polyT hn hE (by fun_prop)) hz) hI) (compF_polyT hN1 hA)
  have h1 : PolyT fun x => List.replicate (nQ x + 1 + aR x + aR x) () :=
    ((hN.add (Unary.const 1)).add hA).add hA
  have h2 : PolyT fun x => nH x + lC x + (EH x).length + aR x :=
    PolyT.add (PolyT.add (PolyT.add hn.poly hl) hm.poly) hA.poly
  exact PolyT.prodMk h1 (PolyT.prodMk h2 hF)

/-- Prepare, count with `SIZED`, keep bit s. -/
def fiM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (Stepped.mapIn preQ (FromPrinted.Consequences.SIZED w ℓ τ)) (Stepped.ofFun postF)

@[instance_reducible] def isPolyT_fiM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (fiM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) preQ_polyT
  haveI := IsPolyT.ofFun postF_polyT
  IsPolyT.bind (M := Stepped.mapIn preQ (FromPrinted.Consequences.SIZED w ℓ τ)) (N := Stepped.ofFun postF)

/-- **The front end reads G, s and ω.** -/
theorem read_fi {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) (ω : Seed n k t mm) :
    preQ (codeFI G s ω) = (List.replicate (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length +
      1 + mm * k + mm * k) (), n + s + (edges n (matrix G)).length + mm * k,
      isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) []) ω) ∧ lC (codeFI G s ω) = s := by
  have e : codeFI G s ω = code G ++ (unary s ++ (unary (seedCode ω).length ++ seedCode ω)) := by
    simp only [codeFI, seedL, List.append_assoc]
  obtain ⟨hn, hE, hs⟩ := read_code G (unary s ++ (unary (seedCode ω).length ++ seedCode ω))
  rw [← e] at hn hE hs
  have hl : lC (codeFI G s ω) = s := by rw [lC, hs, Read.ones_unary_append]
  have hr1 : rest (sI (codeFI G s ω)) = unary (seedCode ω).length ++ seedCode ω := by
    rw [hs, Read.rest_unary_append]
  have hL : ones (rest (sI (codeFI G s ω))) = (seedCode ω).length := by rw [hr1, Read.ones_unary_append]
  have hr2 : r2 (codeFI G s ω) = seedCode ω := by rw [r2, hr1, Read.rest_unary_append]
  have hsd : sdR (codeFI G s ω) = seedCode ω := by rw [sdR, hr2, hL, List.take_length]
  obtain ⟨ek, em1, emm, -, eR, eF⟩ := decode_seedCode ω
  have hA : aR (codeFI G s ω) = mm * k := by rw [aR, hsd, ek, emm]
  refine ⟨?_, hl⟩
  rw [preQ, formQ, nQ, hA, hn, hE, hl, hsd, ek, em1, eR, eF, isoAdd]

/-! ### Sizes -/

theorem shaped_fi {n k t mm : ℕ} (hk : 1 ≤ k) (G : SimpleGraph (Fin n)) (ω : Seed n k t mm) :
    Shaped 4 (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + mm * k + mm * k)
      (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) []) ω) := by
  intro C hC
  simp only [isoAdd, List.mem_append] at hC
  rcases hC with ((hC | hC) | hC) | hC
  · obtain ⟨h1, h2⟩ := shaped_fvs G C hC
    exact ⟨h1, fun l hl => by have := h2 l hl; omega⟩
  · rw [List.mem_singleton] at hC; subst hC
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega
  · obtain ⟨h1, h2⟩ := isoF_clause (by omega) (by omega) hk ω hC
    exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · rw [compF] at hC
    obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> dsimp only <;> omega

theorem length_fi_le {n k t : ℕ} (G : SimpleGraph (Fin n)) (ω : Seed n k t (3 * n + 3)) :
    n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k + (3 * n + 3) * k +
      (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) []) ω).length + 2 ≤ (24 * k + 24) * (n + 2) ^ 2 := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hF := length_fvsF (n := n) (edges n (matrix G))
  have hE := length_edges_sq (n := n) (matrix G)
  have hI := length_isoF_le (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
    (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1) k ω.1.val (rowsOf ω) (fixesOf ω)
  rw [length_rowsOf] at hI
  have hfx := length_fixesOf_le ω
  have hcomp := length_compF (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1)
    ((3 * n + 3) * k)
  have hlen : (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
      (fvsF n (edges n (matrix G)) []) ω).length = (fvsF n (edges n (matrix G)) []).length + 1 +
      (isoF (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1) k ω.1.val (rowsOf ω)
        (fixesOf ω)).length +
      (compF (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1) ((3 * n + 3) * k)).length := by
    simp only [isoAdd, List.length_append, List.length_singleton]
  have q1 : (3 * n + 3) * k ≤ 3 * (k * X) := by rw [hX]; nlinarith
  have q2 : (3 * n + 3) * (k * 4) ≤ 12 * (k * X) := by rw [hX]; nlinarith
  have q3 : n * n + 4 * n + 4 = X ^ 2 := by rw [hX]; ring
  have q4 : k * X ≤ k * X ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) X)
  have e : (24 * k + 24) * X ^ 2 = 24 * (k * X ^ 2) + 24 * X ^ 2 := by ring
  rw [← hX]
  omega

theorem length_codeFI_le {n k t s : ℕ} (G : SimpleGraph (Fin n)) (ω : Seed n k t (3 * n + 3)) (hs : s ≤ n) :
    (codeFI G s ω).length + 1 ≤ (2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 2) * (n + 2) ^ 2 := by
  obtain ⟨B, hB⟩ : ∃ B, B = (k + 5) + (k + 4) * (6 * k + 5) := ⟨_, rfl⟩
  have hS := length_seedCode_le ω
  rw [← hB] at hS ⊢
  have h4 : n * n + 2 * n + 5 ≤ 2 * (n + 2) ^ 2 := by nlinarith
  have e : (2 * B + 2) * (n + 2) ^ 2 = 2 * (B * (n + 2) ^ 2) + 2 * (n + 2) ^ 2 := by ring
  have eu : ∀ m, (unary m).length = m + 1 := fun m => by simp [unary]
  simp only [codeFI, seedL, List.length_append, length_code_eq, eu]
  omega

/-! ### The theorems -/

open Classical in
/-- **Induced forests with one-sided error in time C·2^{εn}, for O(n) edges.** For every D, δ > 0
and ε > 0 there are k, t, n₀ and one Turing machine with finite alphabets such that for every graph
G on n ≥ n₀ vertices with at most D·n edges and s ≤ n: run on `codeFI G s ω` for a seed ω of
`Seed n k t (3n + 3)`, it halts within ⌊C·2^{εn}⌋ steps with one bit out(ω); if no vertex set of
size s induces a forest, out(ω) = 0 for every seed; if one does, out(ω) = 1 for at least a
2^{−δn} fraction of the seeds. -/
theorem for_randomized (D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n s : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → s ≤ n → G.edgeFinset.card ≤ D * n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeFI G s ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numFor G s = 0 → ∀ ω, out ω = false) ∧
        (0 < numFor G s →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, hk, -, n₀, hdec⟩ := fi_decide δ hδ
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts 4
    (show 0 < ε / (2 * (2 * D + 12 * k + 4)) by positivity)
  have := isPolyT_fiM 4 ℓ₀ τ
  obtain ⟨K, hK⟩ : ∃ K, K = c * (24 * k + 24) ^ c + 2 * c + 8 * ((k + 5) + (k + 4) * (6 * k + 5)) + 60 :=
    ⟨_, rfl⟩
  let out : (n : ℕ) → SimpleGraph (Fin n) → ℕ → Seed n k t (3 * n + 3) → Bool := fun n G s ω =>
    decide (cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
      (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
      (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) []) ω) / 2 ^ s % 2 = 1)
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Seed n k t (3 * n + 3) //
    1 ≤ n ∧ p.1 ≤ n ∧ p.2.1.edgeFinset.card ≤ D * n}
  have hrun : ∀ x : ι, ∃ T : ℕ, (fiM 4 ℓ₀ τ).Runs (codeFI x.2.1.2.1 x.2.1.1 x.2.1.2.2)
      T (K * (x.1 + 2) ^ K) [out x.1 x.2.1.2.1 x.2.1.1 x.2.1.2.2] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (ε / 2 * (x.1 : ℝ)) := by
    rintro ⟨n, ⟨s, G, ω⟩, h0, h1, h2⟩
    dsimp only at h0 h1 h2 ⊢
    have hmD : (edges n (matrix G)).length ≤ D * n := (EthCor.HamSTM.length_edges_le_card G).trans h2
    have hmn := length_edges_sq (n := n) (matrix G)
    obtain ⟨hpre, hl⟩ := read_fi G s ω
    obtain ⟨T, hT, hTle⟩ := hc (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 +
      (3 * n + 3) * k + (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
      (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) []) ω) (by omega) (shaped_fi hk G ω)
    rw [← hpre] at hT
    have hpost := ofFun_runs postF (codeFI G s ω,
      cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
        (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
        (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
          (fvsF n (edges n (matrix G)) []) ω))
    have hout := bind_runs (Stepped.mapIn_runs hT) hpost
    have hval : postF (codeFI G s ω,
        cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
          (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
          (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
            (fvsF n (edges n (matrix G)) []) ω)) = [out n G s ω] := by
      rw [postF, hl]
    rw [hval] at hout
    refine ⟨T + 1 + 1, hout.mono le_rfl ?_, ?_⟩
    · obtain ⟨Nv, hNv⟩ : ∃ Nv, Nv = n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 +
          (3 * n + 3) * k + (3 * n + 3) * k := ⟨_, rfl⟩
      have hcnt : size (cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 +
          (3 * n + 3) * k + (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
          (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
            (fvsF n (edges n (matrix G)) []) ω)) ≤ Nv + 2 := by
        rw [hNv]
        have hle : cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 +
            (3 * n + 3) * k + (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
            (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
              (fvsF n (edges n (matrix G)) []) ω) < 2 ^ (n + n + n + (edges n (matrix G)).length +
                (edges n (matrix G)).length + 1 + (3 * n + 3) * k + (3 * n + 3) * k + 1) := by
          unfold cntS
          refine lt_of_le_of_lt (card_le_univ _) ?_
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ]
          have := Nat.one_le_two_pow (n := n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 +
            (3 * n + 3) * k + (3 * n + 3) * k)
          omega
        have := Nat.size_le.2 hle
        change Nat.size _ + 1 ≤ _
        omega
      have hX := length_fi_le G ω
      rw [← hNv] at hX
      have hin : size (codeFI G s ω) + 1 ≤ 2 * ((2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 2) * (n + 2) ^ 2) := by
        rw [size_bools]; have := length_codeFI_le G ω h1; omega
      have hS : c * (Nv + (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
          (fvsF n (edges n (matrix G)) []) ω).length + 2) ^ c ≤ c * (24 * k + 24) ^ c * (n + 2) ^ (2 * c) := by
        calc _ ≤ c * ((24 * k + 24) * (n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
          _ = c * (24 * k + 24) ^ c * (n + 2) ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      have hsq' : (n + 2) ^ (2 * c) ≤ (n + 2) ^ (2 * c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hsq : (n + 2) ^ 2 ≤ (n + 2) ^ (2 * c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hKK : (n + 2) ^ (2 * c + 2) ≤ (n + 2) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
      have hsz : size [out n G s ω] = 3 := by rw [size_bools]; rfl
      have hpair : size (codeFI G s ω, cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length +
          1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
          (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
            (fvsF n (edges n (matrix G)) []) ω)) = size (codeFI G s ω) + size (cntS (n + n + n +
              (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k + (3 * n + 3) * k)
              (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
              (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
                (fvsF n (edges n (matrix G)) []) ω)) := rfl
      rw [hpair, hsz, ← hNv]
      rw [← hNv] at hcnt
      obtain ⟨B, hB⟩ : ∃ B, B = (k + 5) + (k + 4) * (6 * k + 5) := ⟨_, rfl⟩
      rw [← hB] at hin hK
      have hNv2 : Nv + 2 ≤ (24 * k + 24) * (n + 2) ^ 2 := by omega
      have h8 : c * (24 * k + 24) ^ c * (n + 2) ^ (2 * c) ≤ c * (24 * k + 24) ^ c * (n + 2) ^ (2 * c + 2) :=
        Nat.mul_le_mul_left _ hsq'
      have hk2 : (24 * k + 24) * (n + 2) ^ 2 ≤ (24 * k + 24) * (n + 2) ^ (2 * c + 2) := Nat.mul_le_mul_left _ hsq
      have hB2 : (4 * B + 4) * (n + 2) ^ 2 ≤ (4 * B + 4) * (n + 2) ^ (2 * c + 2) := Nat.mul_le_mul_left _ hsq
      have hK2 : (c * (24 * k + 24) ^ c + (24 * k + 24) + (4 * B + 4) + 8) * (n + 2) ^ (2 * c + 2) ≤
          K * (n + 2) ^ K := by
        refine Nat.mul_le_mul ?_ hKK
        have : 24 * k + 24 ≤ 4 * B := by rw [hB]; nlinarith
        omega
      have e2 : (c * (24 * k + 24) ^ c + (24 * k + 24) + (4 * B + 4) + 8) * (n + 2) ^ (2 * c + 2) =
          c * (24 * k + 24) ^ c * (n + 2) ^ (2 * c + 2) + (24 * k + 24) * (n + 2) ^ (2 * c + 2) +
          (4 * B + 4) * (n + 2) ^ (2 * c + 2) + 8 * (n + 2) ^ (2 * c + 2) := by ring
      have e3 : 2 * ((2 * B + 2) * (n + 2) ^ 2) = (4 * B + 4) * (n + 2) ^ 2 := by ring
      have h1p : 1 ≤ (n + 2) ^ (2 * c + 2) := Nat.one_le_pow _ _ (by omega)
      omega
    · have hN : ((n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
          (3 * n + 3) * k : ℕ) : ℝ) ≤ (2 * D + 12 * k + 4) * n := by
        have : n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
            (3 * n + 3) * k ≤ (2 * D + 12 * k + 4) * n := by nlinarith
        exact_mod_cast this
      have hpos : (0 : ℝ) < 2 * D + 12 * k + 4 := by positivity
      have hexp : ε / (2 * (2 * D + 12 * k + 4)) * ((n + n + n + (edges n (matrix G)).length +
          (edges n (matrix G)).length + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ) ≤ ε / 2 * n := by
        calc ε / (2 * (2 * D + 12 * k + 4)) * ((n + n + n + (edges n (matrix G)).length +
              (edges n (matrix G)).length + 1 + (3 * n + 3) * k + (3 * n + 3) * k : ℕ) : ℝ)
            ≤ ε / (2 * (2 * D + 12 * k + 4)) * ((2 * D + 12 * k + 4) * n) :=
              mul_le_mul_of_nonneg_left hN (by positivity)
          _ = ε / 2 * n := by field_simp
      have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 2 * n) := Real.one_le_rpow (by norm_num) (by positivity)
      have hcK : (c : ℝ) + 2 ≤ K := by exact_mod_cast (show c + 2 ≤ K by omega)
      push_cast
      calc (T : ℝ) + 1 + 1 ≤ c * (2 : ℝ) ^ (ε / 2 * n) + 2 :=
            by linarith [hTle.trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (Nat.cast_nonneg c))]
        _ ≤ K * (2 : ℝ) ^ (ε / 2 * n) := by nlinarith
  obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (fiM 4 ℓ₀ τ) (ι := ι)
    (fun x => codeFI x.2.1.2.1 x.2.1.1 x.2.1.2.2)
    (fun x => [out x.1 x.2.1.2.1 x.2.1.1 x.2.1.2.2]) (fun x => x.1) hε K
    (2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 2) 2
    (fun x => length_codeFI_le x.2.1.2.1 x.2.1.2.2 x.2.2.2.1) hrun
  refine ⟨k, t, n₀ + 1, N, C', hfin, fun n s G hn h1 h2 => ⟨out n G s, fun ω => hN ⟨n, (s, G, ω), by omega, h1, h2⟩,
    fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · have := (hdec n G [] s (by omega) (by simp)).1 (by rw [← numFor_eq]; exact h0) ω
    simp [out, this]
  · have h := (hdec n G [] s (by omega) (by simp)).2 (by rw [← numFor_eq]; exact hpos)
    have e : (univ.filter fun ω : Seed n k t (3 * n + 3) =>
        cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
          (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
          (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
            (fvsF n (edges n (matrix G)) []) ω) / 2 ^ s % 2 = 1) = univ.filter fun ω => out n G s ω = true :=
      Finset.filter_congr fun ω _ => by simp [out]
    rwa [e] at h

open Classical in
/-- **Feedback vertex set with one-sided error in time C·2^{εn}, for O(n) edges.** For every D,
δ > 0 and ε > 0 there are k₀, t, n₀ and one Turing machine with finite alphabets such that for every
graph G on n ≥ n₀ vertices with at most D·n edges and k ≤ n: run on `codeFI G (n − k) ω` for a seed
ω of `Seed n k₀ t (3n + 3)`, it halts within ⌊C·2^{εn}⌋ steps with one bit out(ω); if G has no
feedback vertex set with at most k vertices, out(ω) = 0 for every seed; if it has one, out(ω) = 1 for
at least a 2^{−δn} fraction of the seeds. -/
theorem fvs_randomized (D : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k₀ t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → k ≤ n → G.edgeFinset.card ≤ D * n →
      ∃ out : Seed n k₀ t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeFI G (n - k) ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        ((¬∃ X : Finset (Fin n), X.card ≤ k ∧ (G.induce {v | v ∉ X}).IsAcyclic) → ∀ ω, out ω = false) ∧
        ((∃ X : Finset (Fin n), X.card ≤ k ∧ (G.induce {v | v ∉ X}).IsAcyclic) →
          (Fintype.card (Seed n k₀ t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k₀, t, n₀, M, C, hfin, hM⟩ := for_randomized D hδ hε
  refine ⟨k₀, t, n₀, M, C, hfin, fun n k G hn hk hm => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n (n - k) G hn (by omega) hm
  have hiff := fvs_iff G hk
  exact ⟨out, hrun, fun h => hno (by rw [hiff] at h; omega), fun h => hyes (hiff.1 h)⟩

end EthCor.ForestITM
