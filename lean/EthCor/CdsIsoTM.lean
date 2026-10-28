import EthCor.CdsTM
import EthCor.ConnIsoTM
import EthCor.Amplify

/-! # Connected dominating set with one-sided error in time 2^{εn}

The input is the code of G, ℓ in unary and the code of a seed ω with its length in front
(`codeCD`). The root of the tree (`rootR`) has the 3n + 1 + 2·(3n+3)·k variables of
`EthCor.ConnI.ciF`, the clauses of domination open, and the other clauses of `ciF` closed: those of
the side bits, the edges, z = 0, the checks of ω and the complements of the chain bits. The machine
`cdrM w ℓ τ` walks the tree of `EthCor.CdsTree.shortensN`, counts at the leaves with
`FromPrinted.Consequences.SIZED (w + 4) ℓ τ`, adds up and keeps bit 1: the bit of `ConnI.ci_decide`
for ψ the clauses of domination. So for every δ > 0 and ε > 0, one machine runs within C·2^{εn}
steps and outputs, for a random seed, 0 always if G has no connected dominating set of size ℓ, and 1
with probability at least 2^{−δn} if it has one (`cds_randomized`). On R ≥ 2^{2δn} independent seeds
the error is at most e^{−2^{δn}} (`cds_amplified`, with `EthCor.Amplify`). -/

namespace EthCor.CdsITM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Turing Finset
  EthCor.Ham EthCor.HamTM EthCor.HamI EthCor.HamITM EthCor.Iso EthCor.Conn EthCor.ConnTM EthCor.ConnITM
  EthCor.CdsTree EthCor.CnfTM EthCor.CdsTM

/-! ### The input and the root -/

/-- The input: G, ℓ, the seed. -/
noncomputable def codeCD {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (ω : Seed n k t mm) : List Bool :=
  code G ++ unary ℓ ++ seedL ω

/-- The closed clauses: those of `ciF` for ψ = []. -/
def formD (x : List Bool) : Fml :=
  connF (nH x) (EH x) [] ++ [[(nH x + nH x + nH x, false)]] ++
    isoF (nH x + nH x + nH x) (nH x + nH x + nH x + 1) (dk (sdR x)) (dm1 (sdR x)) (dRows (sdR x)) (dFixes (sdR x)) ++
    ConnI.compF (nH x + nH x + nH x + 1) (aR x)

/-- The root of the tree: the variables and the target of `ciF`, the clauses of domination open. -/
def rootR (x : List Bool) : DNode :=
  rootN (nH x + nH x + nH x + 1 + aR x + aR x) (nH x + lC x + aR x) (nH x) (mH x) (formD x)

theorem rootR_polyT : PolyT rootR := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT lC := by unfold lC GraphProblems.ones; fun_prop
  have hm : PolyT mH := by unfold mH; have := hn.poly; fun_prop
  have hr1 : PolyT fun x => rest (sI x) := by unfold rest; fun_prop
  have hr2 : PolyT r2 := by unfold r2 rest; unfold rest at hr1; fun_prop
  have hL : PolyT fun x => GraphProblems.ones (rest (sI x)) := (ones_unary hr1).poly
  have hsd : PolyT sdR := by unfold sdR; fun_prop
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
  have hF : PolyT formD := by
    unfold formD
    exact PolyT.append (PolyT.append (PolyT.append (connF_polyT hn hE (PolyT.const [])) hz) hI) (compF_polyT h31 hA)
  have h1 : PolyT fun x => List.replicate (nH x + nH x + nH x + 1 + aR x + aR x) () :=
    (((h3.add (Unary.const 1)).add hA).add hA)
  have h2 : PolyT fun x => nH x + lC x + aR x := PolyT.add (PolyT.add hn.poly hl) hA.poly
  have h4 : PolyT fun x => nbhd (nH x) (mH x) := nbhd_polyT hn hm
  unfold rootR rootN
  exact PolyT.prodMk (PolyT.prodMk h1 h2) (PolyT.prodMk h4 hF)

/-- **The front end reads G, ℓ and ω.** -/
theorem read_cd {n k t mm : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (ω : Seed n k t mm) :
    rootR (codeCD G ℓ ω) = rootN (n + n + n + 1 + mm * k + mm * k) (n + ℓ + mm * k) n (matrix G)
      (ConnI.ciF n (edges n (matrix G)) [] ω) := by
  have e : codeCD G ℓ ω = code G ++ (unary ℓ ++ (unary (seedCode ω).length ++ seedCode ω)) := by
    simp only [codeCD, seedL, List.append_assoc]
  obtain ⟨hn, hE, hs⟩ := read_code G (unary ℓ ++ (unary (seedCode ω).length ++ seedCode ω))
  have hm := mH_code G (unary ℓ ++ (unary (seedCode ω).length ++ seedCode ω))
  rw [← e] at hn hE hs hm
  have hl : lC (codeCD G ℓ ω) = ℓ := by rw [lC, hs, Read.ones_unary_append]
  have hr1 : rest (sI (codeCD G ℓ ω)) = unary (seedCode ω).length ++ seedCode ω := by
    rw [hs, Read.rest_unary_append]
  have hL : GraphProblems.ones (rest (sI (codeCD G ℓ ω))) = (seedCode ω).length := by
    rw [hr1, Read.ones_unary_append]
  have hr2 : r2 (codeCD G ℓ ω) = seedCode ω := by rw [r2, hr1, Read.rest_unary_append]
  have hsd : sdR (codeCD G ℓ ω) = seedCode ω := by rw [sdR, hr2, hL, List.take_length]
  obtain ⟨ek, em1, emm, -, eR, eF⟩ := decode_seedCode ω
  have hA : aR (codeCD G ℓ ω) = mm * k := by rw [aR, hsd, ek, emm]
  rw [rootR, formD, hA, hn, hE, hl, hm, hsd, ek, em1, eR, eF, ConnI.ciF]

/-! ### The machine -/

/-- Read G, ℓ and ω, walk the tree, count at the leaves, keep bit 1 of the sum. -/
def cdrM (w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum (stepD w) rootR (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ))) postC

@[instance_reducible] def isPolyT_cdrM (w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)] :
    IsPolyT (cdrM w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED (w + 4) ℓ τ) stCertDom.2.2
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)) (stCertDom.1 w)
    rootR_polyT
  IsPolyT.mapOut (M := walkSum (stepD w) rootR (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ τ)))
    postC_polyT

/-! ### Sizes -/

theorem length_codeCD_le {n k t ℓ : ℕ} (G : SimpleGraph (Fin n)) (ω : Seed n k t (3 * n + 3)) (hℓ : ℓ ≤ n) :
    (codeCD G ℓ ω).length + 1 ≤ (2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 6) * (n + 2) ^ 2 := by
  obtain ⟨B, hB⟩ : ∃ B, B = (k + 5) + (k + 4) * (6 * k + 5) := ⟨_, rfl⟩
  have hS := length_seedCode_le ω
  rw [← hB] at hS ⊢
  have h4 : n * n + 6 * n + 6 ≤ 6 * (n + 2) ^ 2 := by nlinarith
  have e : (2 * B + 6) * (n + 2) ^ 2 = 2 * (B * (n + 2) ^ 2) + 6 * (n + 2) ^ 2 := by ring
  have eu : ∀ m, (unary m).length = m + 1 := fun m => by simp [unary]
  simp only [codeCD, seedL, List.length_append, length_code_eq, eu]
  omega

/-! ### The theorem -/

open Classical in
/-- **Connected dominating set with one-sided error in time C·2^{εn}.** For every δ > 0 and ε > 0
there are k, t, n₀ and one Turing machine with finite alphabets such that for every graph G on
n ≥ n₀ vertices (of any density) and 1 ≤ ℓ ≤ n: run on `codeCD G ℓ ω` for a seed ω of
`Seed n k t (3n + 3)`, it halts within ⌊C·2^{εn}⌋ steps with one bit out(ω); if G has no connected
dominating set with ℓ vertices, out(ω) = 0 for every seed; if it has one, out(ω) = 1 for at least a
2^{−δn} fraction of the seeds. -/
theorem cds_randomized {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCD G ℓ ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numCDS G ℓ = 0 → ∀ ω, out ω = false) ∧
        (0 < numCDS G ℓ →
          (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) * (univ.filter fun ω => out ω = true).card) := by
  obtain ⟨k, t, hk, -, n₀, hdec⟩ := ConnI.ci_decide δ hδ
  obtain ⟨w, hw2, hw⟩ := shortensN_exists (show 0 < ε / 4 by positivity)
  obtain ⟨ℓ₀, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (w + 4)
    (show 0 < ε / (4 * (12 * k + 4)) by positivity)
  have := isPolyT_cdrM w ℓ₀ τ
  -- the constants
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 24 * k + 16 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (2 * (w + 4) + 11) * Z ^ 3 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * A + 4 * Z + c * (2 * Z) ^ c + 2 * c + 20 := ⟨_, rfl⟩
  let out : (n : ℕ) → SimpleGraph (Fin n) → ℕ → Seed n k t (3 * n + 3) → Bool := fun n G ℓ ω =>
    decide (cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
      (ConnI.ciF n (edges n (matrix G)) (domF n (matrix G)) ω) / 2 % 2 = 1)
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) × Seed n k t (3 * n + 3) // 1 ≤ p.1 ∧ p.1 ≤ n}
  have hrun : ∀ x : ι, ∃ T : ℕ, (cdrM w ℓ₀ τ).Runs (codeCD x.2.1.2.1 x.2.1.1 x.2.1.2.2)
      T (K * (x.1 + 2) ^ K) [out x.1 x.2.1.2.1 x.2.1.1 x.2.1.2.2] ∧
      (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (ε / 2 * (x.1 : ℝ)) := by
    rintro ⟨n, ⟨ℓ, G, ω⟩, h1, h2⟩
    dsimp only at h1 h2 ⊢
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
    obtain ⟨t1, t2, t3, t4⟩ := shortensN w hw2 hw N s n (matrix G) F (by omega) hFs
    have hR : rootR (codeCD G ℓ ω) = rootN N s n (matrix G) F := by rw [hNdef, hsdef, hF]; exact read_cd G ℓ ω
    rw [← hR] at t1 t2 t3 t4
    have hcf : (nbhd n (matrix G)).map posC ++ F = ConnI.ciF n (edges n (matrix G)) (domF n (matrix G)) ω := by
      rw [hF]; simp only [ConnI.ciF, connF, domF, List.append_assoc, List.nil_append]
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (ε / 4 * n) := ⟨_, rfl⟩
    have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by omega
    have hY : N + F.length + 2 ≤ Z * X ^ 2 := by rw [hX]; exact hFl
    -- the leaves
    have hNn : (N : ℝ) ≤ (12 * k + 4) * n := by
      have : N ≤ (12 * k + 4) * n := by rw [hNdef]; nlinarith
      exact_mod_cast this
    have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootR (codeCD G ℓ ω)),
        (Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)).Runs x ⌊(c : ℝ) * E⌋₊
          (c * (2 * Z) ^ c * X ^ (2 * c)) (cntS N s (leafD x).2.2) := by
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
      · have hsp : N + (leafD x).2.2.length + 2 ≤ 2 * Z * X ^ 2 := by
          have e2 : 2 * Z * X ^ 2 = Z * X ^ 2 + Z * X ^ 2 := by ring
          omega
        calc c * (N + (leafD x).2.2.length + 2) ^ c ≤ c * (2 * Z * X ^ 2) ^ c :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsp c)
          _ = c * (2 * Z) ^ c * X ^ (2 * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    -- the stack
    have hstack : ∀ i, size ((round (stepD w))^[i] ([rootR (codeCD G ℓ ω)], [])).1 ≤
        (2 * n + 1) * (A * X ^ 6 + 1) + 1 := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      exact SplitCount.size_list_le s1 fun x hx => by
        obtain ⟨g1, g2, g3, g4, g5⟩ := s2 x hx
        have hYY : Z * X ^ 2 ≤ (Z * X ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
        have := size_nodeN_le g1 g2 g3 g4 g5 (X := Z * X ^ 2) (by omega) (by omega) (by omega) (by omega)
        calc size x ≤ (2 * (w + 4) + 11) * (Z * X ^ 2) ^ 3 := this
          _ = A * X ^ 6 := by rw [hA]; ring
    have hlt : ((leaves (stepD w) (2 * n) (rootR (codeCD G ℓ ω))).map
        fun x => cntS N s (leafD x).2.2).sum < 2 ^ (N + 1) := by
      rw [← t3]
      exact lt_of_le_of_lt (Consequences.cntS_le _ _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have wr := walkSum_runs (stepD w) (root := rootR)
      (T := Stepped.mapIn leafD (FromPrinted.Consequences.SIZED (w + 4) ℓ₀ τ)) (2 * n) (codeCD G ℓ ω)
      (fun x hx => (t2 x hx).1) (fun x => cntS N s (leafD x).2.2) ⌊(c : ℝ) * E⌋₊ _ _ (N + 1) hleaf hstack hlt
    have hout := Stepped.mapOut_runs (f := postC) wr
    have hval : postC (cntS N s (ConnI.ciF n (edges n (matrix G)) (domF n (matrix G)) ω)) = [out n G ℓ ω] := by
      rw [hNdef, hsdef]; rfl
    rw [← t3, hcf, hval] at hout
    obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (leaves (stepD w) (2 * n) (rootR (codeCD G ℓ ω))).length := ⟨_, rfl⟩
    rw [← hL] at hout t1
    refine ⟨_, hout.mono le_rfl ?_, ?_⟩
    · -- the space
      rw [← hX]
      have hX6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX1
      have hX7 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ hX1
      have hpow : X ^ 7 ≤ X ^ (2 * c + 7) := Nat.pow_le_pow_right hX1 (by omega)
      have p1 : (2 * n + 1) * (A * X ^ 6 + 1) + 1 ≤ (2 * A + 3) * X ^ (2 * c + 7) := by
        calc (2 * n + 1) * (A * X ^ 6 + 1) + 1 ≤ (2 * X) * ((A + 1) * X ^ 6) + X ^ 7 := by
              gcongr
              · omega
              · nlinarith
          _ = (2 * A + 3) * X ^ 7 := by ring
          _ ≤ (2 * A + 3) * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ hpow
      have p2 : N + 1 + 1 + 1 + 1 ≤ (Z + 4) * X ^ (2 * c + 7) := by
        have hZX : Z * X ^ 2 ≤ Z * X ^ (2 * c + 7) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
        have h1X : 1 ≤ X ^ (2 * c + 7) := Nat.one_le_pow _ _ hX1
        have e : (Z + 4) * X ^ (2 * c + 7) = Z * X ^ (2 * c + 7) + 4 * X ^ (2 * c + 7) := by ring
        omega
      have p3 : c * (2 * Z) ^ c * X ^ (2 * c) ≤ c * (2 * Z) ^ c * X ^ (2 * c + 7) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
      have p4 : (2 * A + 3 + (Z + 4) + c * (2 * Z) ^ c) * X ^ (2 * c + 7) ≤ K * X ^ K :=
        absorb hX1 (by omega) (by omega)
      have e5 : (2 * A + 3 + (Z + 4) + c * (2 * Z) ^ c) * X ^ (2 * c + 7) =
          (2 * A + 3) * X ^ (2 * c + 7) + (Z + 4) * X ^ (2 * c + 7) + c * (2 * Z) ^ c * X ^ (2 * c + 7) := by ring
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
  obtain ⟨M', C', hfin, hN⟩ := tm_of_stepped (cdrM w ℓ₀ τ) (ι := ι)
    (fun x => codeCD x.2.1.2.1 x.2.1.1 x.2.1.2.2)
    (fun x => [out x.1 x.2.1.2.1 x.2.1.1 x.2.1.2.2]) (fun x => x.1) hε K
    (2 * ((k + 5) + (k + 4) * (6 * k + 5)) + 6) 2
    (fun x => length_codeCD_le x.2.1.2.1 x.2.1.2.2 x.2.2.2) hrun
  refine ⟨k, t, n₀, M', C', hfin, fun n ℓ G hn h1 h2 => ⟨out n G ℓ, fun ω => hN ⟨n, (ℓ, G, ω), h1, h2⟩,
    fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · have := (hdec n G (domF n (matrix G)) ℓ hn (domF_lt _) h1).1 (by rw [← numCDS_eq]; exact h0) ω
    simp [out, this]
  · have h := (hdec n G (domF n (matrix G)) ℓ hn (domF_lt _) h1).2 (by rw [← numCDS_eq]; exact hpos)
    have e : (univ.filter fun ω : Seed n k t (3 * n + 3) =>
        cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
          (ConnI.ciF n (edges n (matrix G)) (domF n (matrix G)) ω) / 2 % 2 = 1) =
          univ.filter fun ω => out n G ℓ ω = true :=
      Finset.filter_congr fun ω _ => by simp [out]
    rwa [e] at h

open Classical in
/-- **Connected dominating set, amplified.** The machine of `cds_randomized`, run on R independent
seeds, with the same guarantees as `EthCor.Amplify.conn_amplified`. -/
theorem cds_amplified {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) : ∃ k t n₀ : ℕ,
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → 1 ≤ ℓ → ℓ ≤ n →
      ∃ out : Seed n k t (3 * n + 3) → Bool,
        (∀ ω, Wrap.Outputs M (codeCD G ℓ ω) [out ω] ⌊(C : ℝ) * (2 : ℝ) ^ (ε * n)⌋₊) ∧
        (numCDS G ℓ = 0 → ∀ ω, out ω = false) ∧
        (0 < numCDS G ℓ → ∀ R : ℕ,
          ((univ.filter fun w : Fin R → Seed n k t (3 * n + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
            (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ^ R * Real.exp (-((2 : ℝ) ^ (-(δ * n)) * R)) ∧
          ((2 : ℝ) ^ (2 * δ * n) ≤ R →
            ((univ.filter fun w : Fin R → Seed n k t (3 * n + 3) => ∀ i, out (w i) = false).card : ℝ) ≤
              (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ^ R * Real.exp (-(2 : ℝ) ^ (δ * n)))) := by
  obtain ⟨k, t, n₀, M, C, hfin, hM⟩ := cds_randomized hδ hε
  refine ⟨k, t, n₀, M, C, hfin, fun n ℓ G hn h1 h2 => ?_⟩
  obtain ⟨out, hrun, hno, hyes⟩ := hM n ℓ G hn h1 h2
  refine ⟨out, hrun, hno, fun hpos R => ⟨?_, Amplify.amplify_sq out δ n (hyes hpos) R⟩⟩
  have hp : (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) * (2 : ℝ) ^ (-(δ * n)) ≤
      (univ.filter fun ω => out ω = true).card := by
    have := hyes hpos
    rw [Real.rpow_neg zero_le_two]
    calc _ ≤ 2 ^ (δ * n) * ((univ.filter fun ω => out ω = true).card : ℝ) * ((2 : ℝ) ^ (δ * n))⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by field_simp
  exact Amplify.amplify out hp R

end EthCor.CdsITM
