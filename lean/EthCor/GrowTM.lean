import EthCor.GrowArith
import EthCor.ColorTM
import Wrap.Sim
import Wrap.CodingExists
import CountKSat.Host
import Consequences.Main

/-! # CNF with up to n·2^{(lg n)^{1/7}} clauses, of any width: counting in time 2^{o(n)}

The machine `growM K` reads the code `SatFree.enc φ`, walks the tree of `EthCor.GrowTree.stepW`
(width `wN (2n)` ≈ lg(2n)^{1/6}) from `rootX`, and at every leaf runs Anthropic's machine of the
Main Theorem on the compact code (`MainTheoremForms.MainTheoremCompact`), simulated step by step
through a coding of its configurations (`Wrap.sim`). The sum of the leaf counts is written in
binary; `CountKSat.stHostW` turns the whole computation into one Turing machine.

`cnf_grow`: one Turing machine with finite alphabets, and for every δ > 0 an n₀, such that for
every CNF φ on n ≥ n₀ variables with at most n·2^{(lg n)^{1/7}} clauses, none of which repeats a
literal, it outputs the number of satisfying assignments of φ within ⌊2^{δn}⌋ steps. -/

namespace EthCor.GrowTM

open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems EthCor.CnfTree
  EthCor.CnfTM EthCor.GrowTree EthCor.GrowArith Turing

/-! ### The machine -/

/-- The formula at a leaf, without repeated clauses. -/
def leafF (x : DNode) : Fml := (leafD x).2.2.dedup

/-- The compact code of the formula at a leaf, of width `wN N` for N variables. -/
def preL (x : DNode) : List Bool :=
  EthCor.encK (List.replicate (wN x.1.1.length) ()) (List.replicate (Nat.log2 (2 * x.1.1.length) + 1) ()) (leafF x)

theorem preL_polyT : PolyT preL := by
  have hn : Unary fun x : DNode => x.1.1.length := Unary.of_length (by fun_prop)
  have hK : PolyT fun x : DNode => List.replicate (wN x.1.1.length) () := wN_polyT hn
  have hw : PolyT fun x : DNode => List.replicate (Nat.log2 (2 * x.1.1.length) + 1) () :=
    Unary.of_le (((Unary.const 2).mul hn).add (Unary.const 1)) (by have := hn.poly; fun_prop)
      fun x => by have := Nat.log2_le_self (2 * x.1.1.length); omega
  have hF : PolyT leafF := by unfold leafF; exact PolyT.dedup stCertDom.2.2.snd.snd
  exact EthCor.encK_polyT hK hw hF

variable {M₀ : TM2ComputableAux Bool Bool}

/-- At a leaf: the simulated machine on the compact code, its binary output read as a number. -/
def leafM (K : Wrap.Coding M₀) : Stepped DNode ℕ :=
  Stepped.mapIn preL (Stepped.mapOut (Wrap.sim K id id) ofWord)

/-- Read the code, walk the tree, count at the leaves, write the sum in binary. -/
def growM (K : Wrap.Coding M₀) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (walkSum stepW (fun x => rootX (FreeCode.readFree x)) (leafM K)) Nat.bits

@[instance_reducible] def isPolyT_growM (K : Wrap.Coding M₀) : IsPolyT (growM K) :=
  haveI := Wrap.sim_isPolyT K (pre := id) (post := id) PolyT.id' PolyT.id'
  haveI := IsPolyT.mapOut (M := Wrap.sim K id id) (PolyT.ofWord' PolyT.id')
  haveI : IsPolyT (leafM K) := IsPolyT.mapIn (M := Stepped.mapOut (Wrap.sim K id id) ofWord) preL_polyT
  haveI := isPolyT_walkSum (T := leafM K) stepW_polyT (rootX_polyT.comp FreeCode.readFree_polyT)
  IsPolyT.mapOut (M := walkSum stepW (fun x => rootX (FreeCode.readFree x)) (leafM K)) bits_polyT

/-! ### A leaf -/

/-- The length of the compact code at a leaf with at most (2D + 4)·n clauses. -/
def lB (n D : ℕ) : ℕ :=
  wN (2 * n) + (Nat.log2 (2 * (2 * n)) + 1) + 2 + (2 * D + 4) * n * (wN (2 * n) * (Nat.log2 (2 * (2 * n)) + 1))

/-- The steps at a leaf. -/
noncomputable def tB (C n D : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n))⌋₊ + C * lB n D ^ C

/-- The machine of the Main Theorem on the compact code, with its constant. -/
def Compact (M₀ : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k N : ℕ) (φ : Sat3.CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ MainTheoremForms.numOcc φ →
    MainTheoremForms.CountsOccWithinC M₀ k φ
      (MainTheoremForms.timeMin C k φ.length (MainTheoremForms.numOcc φ) + C * (MainTheoremForms.encC k φ).length ^ C)

/-- **A leaf**: on 2n variables with s = n, the pair clauses among the closed clauses, width
`wN (2n)` and at most (2D + 4)·n clauses, the leaf machine returns `cntS (2n) n` of the formula. -/
theorem leaf_runs {C : ℕ} (hM : Compact M₀ C) (K : Wrap.Coding M₀) {n D : ℕ} (hn : 2 ≤ n) {x : DNode}
    (h1 : x.1 = (List.replicate (2 * n) (), n)) (h2 : Shaped (wN (2 * n)) (2 * n) (leafD x).2.2)
    (h3 : (leafD x).2.2.length ≤ (2 * D + 4) * n) (h4 : ∀ C ∈ pairF n, C ∈ x.2.2) :
    (leafM K).Runs x (tB C n D) (K.a * (lB n D + 1) + K.a * tB C n D) (cntS (2 * n) n (leafD x).2.2) := by
  have h4' : ∀ C ∈ pairF n, C ∈ (leafD x).2.2 := fun C hC => by
    simp only [leafD]; exact List.mem_append_right _ (h4 C hC)
  have hvar : ∀ C ∈ leafF x, ∀ l ∈ C, l.1 < 2 * n := fun C hC l hl => (h2 C (List.mem_dedup.1 hC)).2 l hl
  obtain ⟨φ, hφ⟩ := exists_toN (N := 2 * n) hvar
  have hφl : φ.length = (leafF x).length := by rw [← hφ, Decode.toN, List.length_map]
  -- the front end writes the compact code of φ
  have hpre : preL x = MainTheoremForms.encC (wN (2 * n)) φ := by
    unfold preL; rw [h1]; simp only [List.length_replicate]; rw [← hφ, EthCor.encK_toN]
  -- all 2n variables occur
  have hocc : SatM.AllOccur φ := by
    intro i
    have hi := i.2
    have hC : [(2 * (i.val / 2), true), (2 * (i.val / 2) + 1, true)] ∈ leafF x :=
      List.mem_dedup.2 (h4' _ (mem_pairF.2 ⟨i.val / 2, by omega, Or.inl rfl⟩))
    have hl : (i.val, true) ∈ [(2 * (i.val / 2), true), (2 * (i.val / 2) + 1, true)] := by simp; omega
    rw [← hφ, EthCor.mem_toN] at hC
    obtain ⟨D', hD', hD'e⟩ := hC
    rw [← hD'e] at hl
    obtain ⟨l', hl', hl'e⟩ := List.mem_map.1 hl
    exact ⟨D', hD', l', hl', Fin.ext (congrArg Prod.fst hl'e)⟩
  have hk : SatK.IsKCNF (wN (2 * n)) φ := by
    refine ⟨fun D' hD' => ?_, ?_⟩
    · have hm : D'.map (fun l => (l.1.val, l.2)) ∈ Decode.toN φ := EthCor.mem_toN.2 ⟨D', hD', rfl⟩
      rw [hφ] at hm
      simpa using (h2 _ (List.mem_dedup.1 hm)).1
    · have h : (Decode.toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
      exact List.Nodup.of_map _ h
  have hlen2 : 2 ≤ φ.length := by
    rw [hφl]
    have a1 := List.mem_dedup.2 (h4' _ (mem_pairF.2 ⟨0, by omega, Or.inl rfl⟩))
    have a2 := List.mem_dedup.2 (h4' _ (mem_pairF.2 ⟨0, by omega, Or.inr rfl⟩))
    have hne : [(2 * 0, true), (2 * 0 + 1, true)] ≠ [(2 * 0, false), (2 * 0 + 1, false)] := by simp
    have hsub : ({[(2 * 0, true), (2 * 0 + 1, true)], [(2 * 0, false), (2 * 0 + 1, false)]} : Finset (List (ℕ × Bool))) ⊆
        (leafF x).toFinset := by
      intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rw [List.mem_toFinset]; rcases hC with rfl | rfl
      · exact a1
      · exact a2
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne, List.toFinset_card_of_nodup (show (leafF x).Nodup from List.nodup_dedup _)] at this
    exact this
  -- the run of the Main Theorem's machine
  have hocc' := VariableBound.Rename.allOccurStmt _ φ hocc
  have hrun := hM (wN (2 * n)) (2 * n) φ (by have := one_le_wN_sub (2 * n); omega) hk hlen2 (by rw [hocc'.1]; omega)
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc'.1, hocc'.2] at hrun
  have hcnt : SatK.numSat φ = cntS (2 * n) n (leafD x).2.2 := by
    rw [← stCntToN, hφ, cntS_eq_cntN h4']
    unfold cntN leafF; congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]
  have hlenC : (MainTheoremForms.encC (wN (2 * n)) φ).length ≤ lB n D := by
    rw [Wrap.length_encC]
    have hm : φ.length ≤ (2 * D + 4) * n := by rw [hφl]; exact (List.dedup_sublist _).length_le.trans h3
    unfold lB
    gcongr
  have htime : MainTheoremForms.timeMin C (wN (2 * n)) φ.length (2 * n) +
      C * (MainTheoremForms.encC (wN (2 * n)) φ).length ^ C ≤ tB C n D := by
    unfold tB MainTheoremForms.timeMin
    refine Nat.add_le_add (Nat.floor_le_floor ?_) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlenC _))
    exact Real.rpow_le_rpow_of_exponent_le one_le_two
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg _))
  have hout : Wrap.Outputs M₀ (preL x) (SatK.binary (2 * n) (cntS (2 * n) n (leafD x).2.2)) (tB C n D) := by
    rw [hpre, ← hcnt]; exact Wrap.Outputs.mono hrun htime
  have hlt : cntS (2 * n) n (leafD x).2.2 < 2 ^ (2 * n + 1) := by
    rw [← hcnt]
    have h5 : SatK.numSat φ ≤ 2 ^ (2 * n) := (Finset.card_filter_le _ _).trans (by simp)
    have h6 : 2 ^ (2 * n) < 2 ^ (2 * n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hs := Wrap.sim_runs K id id (x := preL x) hout
  have hs2 := Stepped.mapOut_runs (f := ofWord) hs
  dsimp only [id] at hs2
  rw [Consequences.ofWord_binary_lt hlt] at hs2
  have hpl : (preL x).length ≤ lB n D := by rw [hpre]; exact hlenC
  refine (Stepped.mapIn_runs (f := preL) hs2).mono le_rfl ?_
  gcongr

/-! ### The walk -/

/-- **One input**: for a CNF φ on n ≥ 2 variables with at most D·n clauses and a width condition
for ε, the machine returns the binary number of satisfying assignments, after L·(tB + 2) steps
with L ≤ 2^{εn} leaves. -/
theorem grow_runs {C : ℕ} (hM : Compact M₀ C) (K : Wrap.Coding M₀) {n D : ℕ} (hn : 2 ≤ n) (φ : Sat3.CNF n)
    (hm : φ.length ≤ D * n) {ε : ℝ}
    (hw : ((2 : ℕ) : ℝ) / ((wN (2 * n) : ℕ) : ℝ) * Real.logb 2 (Real.exp 1 * ((wN (2 * n) : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ)) ≤ ε) :
    ∃ L S : ℕ, (L : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
      S ≤ ((D + 2) * n + 1) * ((6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7) * (n + 2) ^ 3 + 1) + 1 +
        (n + 1 + 1 + (K.a * (lB n D + 1) + K.a * tB C n D + 1)) + 1 ∧
      (growM K).Runs (SatFree.enc φ) (L * (tB C n D + 2)) S (Nat.bits (SatK.numSat φ)) := by
  have hw2 : 2 ≤ wN (2 * n) := by have := one_le_wN_sub (2 * n); omega
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = Decode.toN φ := ⟨_, rfl⟩
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN (hψdef ▸ hC)).2
  have hψm : ψ.length ≤ D * n := by rw [hψdef, Decode.toN, List.length_map]; exact hm
  obtain ⟨t1, t2, t3, t4⟩ := shortens_of D (wN (2 * n)) hw2 hw n ψ hψ hψm
  have hR : FreeCode.readFree (SatFree.enc φ) = (List.replicate n (), ψ) := by rw [hψdef]; exact FreeCode.reads_readFree n φ
  have hr1 : (rootX (List.replicate n (), ψ)).1.1.length = 2 * n := by simp [rootX]
  have hL := leaves_stepW (rootX (List.replicate n (), ψ)) ((D + 2) * n)
  have hRd := round_stepW (rootX (List.replicate n (), ψ))
  rw [hr1] at hL hRd
  have hpair := pairF_sub_leaves (wN (2 * n)) n ((D + 2) * n) ψ
  have hd : ∀ x ∈ leaves stepW ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ))), stepW x = none := by
    intro x hx
    rw [hR, hL] at hx
    obtain ⟨hn', h1, -⟩ := t2 x hx
    unfold stepW; rw [h1]; simpa using hn'
  have hleaf : ∀ x ∈ leaves stepW ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ))),
      (leafM K).Runs x (tB C n D) (K.a * (lB n D + 1) + K.a * tB C n D) (cntS (2 * n) n (leafD x).2.2) := by
    intro x hx
    rw [hR, hL] at hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    exact leaf_runs hM K hn h1 h2 h3 (hpair x hx)
  have hstack : ∀ i, size ((round stepW)^[i] ([rootX (FreeCode.readFree (SatFree.enc φ))], [])).1 ≤
      ((D + 2) * n + 1) * ((6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7) * (n + 2) ^ 3 + 1) + 1 := by
    intro i
    rw [hR, hRd]
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitCount.size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      exact size_node_le h1 h2 h3 h4 h5
  have hlt : ((leaves stepW ((D + 2) * n) (rootX (FreeCode.readFree (SatFree.enc φ)))).map
      fun x => cntS (2 * n) n (leafD x).2.2).sum < 2 ^ (n + 1) := by
    rw [hR, hL, ← t3]
    exact lt_of_le_of_lt (SplitCount.cntN_le n ψ) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have wr := walkSum_runs stepW (root := fun x => rootX (FreeCode.readFree x)) (T := leafM K) ((D + 2) * n)
    (SatFree.enc φ) hd (fun x => cntS (2 * n) n (leafD x).2.2) _ _ _ (n + 1) hleaf hstack hlt
  rw [hR, hL, ← t3] at wr
  obtain ⟨L, hLd⟩ : ∃ L : ℕ, L = (leaves (stepD (wN (2 * n))) ((D + 2) * n) (rootX (List.replicate n (), ψ))).length :=
    ⟨_, rfl⟩
  rw [← hLd] at wr t1
  rw [hψdef, stCntToN n φ] at wr
  exact ⟨L, _, t1, le_rfl, Stepped.mapOut_runs wr⟩

/-! ### The theorem -/

/-- **CNF with up to n·2^{(lg n)^{1/7}} clauses, of any width, counted in time 2^{o(n)}.** One
Turing machine with finite alphabets: for every δ > 0 there is n₀ such that for every CNF φ on
n ≥ n₀ variables with at most n·2^{(lg n)^{1/7}} clauses, none of which repeats a literal, started on
the code of φ it halts within ⌊2^{δn}⌋ steps with the number of satisfying assignments of φ in
binary. -/
theorem cnf_grow : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), n₀ ≤ n →
      (φ.length : ℝ) ≤ n * (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) → (∀ C ∈ φ, C.Nodup) →
        Wrap.Outputs M (SatFree.enc φ) (Nat.bits (SatK.numSat φ)) ⌊(2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M₀, C, hfin, hM⟩ := EthCor.compact
  obtain ⟨K⟩ := Wrap.coding_exists M₀ hfin
  haveI := isPolyT_growM K
  obtain ⟨M, q, hfinM, hH⟩ := stHostW (growM K)
  refine ⟨M, hfinM, fun δ hδ => ?_⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = δ / (2 * ((q : ℝ) + 2)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = C * 24 ^ C + 4 * C + 25 * K.a + 60 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 5 * q * (2 * K.a + 7) ^ q := ⟨_, rfl⟩
  obtain ⟨n₁, hn₁⟩ := width_small hη0
  obtain ⟨n₂, hn₂⟩ := expN_small C hη0
  obtain ⟨n₃, hn₃⟩ := poly_le P hη0
  obtain ⟨n₄, hn₄⟩ := poly_le Q (show 0 < δ / 2 by positivity)
  refine ⟨n₁ + n₂ + n₃ + n₄ + 2, fun n φ hn hm hnd => ?_⟩
  have hn2 : 2 ≤ n := by omega
  -- the density
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌈(2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ))⌉₊ := ⟨_, rfl⟩
  have hDn : D ≤ n := hD ▸ ceil_le_n hn2
  have hDr : (D : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) + 1 := by
    rw [hD]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hmD : φ.length ≤ D * n := by
    have h1 : (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) ≤ D := hD ▸ Nat.le_ceil _
    have h2 : (φ.length : ℝ) ≤ D * n := by
      calc (φ.length : ℝ) ≤ n * (2 : ℝ) ^ (Real.logb 2 n ^ (1 / 7 : ℝ)) := hm
        _ ≤ n * D := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
        _ = D * n := mul_comm _ _
    exact_mod_cast h2
  obtain ⟨L, S, hL, hS, hrun⟩ := grow_runs hM K hn2 φ hmD (hn₁ n (by omega) D hDr)
  refine Wrap.Outputs.mono (hH _ _ _ _ hrun) (Nat.le_floor ?_)
  -- the numbers
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (η * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  have hPE : ∀ y : ℕ, y ≤ P * X ^ P → (y : ℝ) ≤ E := fun y hy => by
    have h1 : (y : ℝ) ≤ ((P * X ^ P : ℕ) : ℝ) := by exact_mod_cast hy
    have h2 := hn₃ n (by omega)
    rw [hX] at h1; push_cast at h1; rw [hE]; linarith
  -- the width and the logarithm
  have hw : wN (2 * n) + 2 ≤ 2 * X := by have := wN_le (2 * n); omega
  have hlg : Nat.log2 (2 * (2 * n)) + 1 ≤ 4 * X := by have := Nat.log2_le_self (2 * (2 * n)); omega
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
  -- the code at a leaf
  have hlB : lB n D ≤ 24 * X ^ 4 := by
    have e1 : (2 * D + 4) * n * (wN (2 * n) * (Nat.log2 (2 * (2 * n)) + 1)) ≤ 16 * X ^ 4 := by
      calc (2 * D + 4) * n * (wN (2 * n) * (Nat.log2 (2 * (2 * n)) + 1)) ≤ (2 * X) * X * ((2 * X) * (4 * X)) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) hlg)
        _ = 16 * X ^ 4 := by ring
    unfold lB; omega
  -- the steps at a leaf
  have htB : (tB C n D : ℝ) ≤ 2 * E := by
    have h1 : ((⌊(2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN (wN (2 * n)) (2 * n))⌋₊ : ℕ) : ℝ) ≤ E := by
      refine (Nat.floor_le (by positivity)).trans ?_
      rw [hE]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (hn₂ n (by omega))
    have h2 : ((C * lB n D ^ C : ℕ) : ℝ) ≤ E := by
      refine hPE _ ?_
      calc C * lB n D ^ C ≤ C * (24 * X ^ 4) ^ C := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlB _)
        _ = C * 24 ^ C * X ^ (4 * C) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ P * X ^ P := absorb hX1 (by rw [hP]; omega) (by rw [hP]; omega)
    unfold tB; push_cast at h1 h2 ⊢; linarith
  -- the input
  have hx : ((SatFree.enc φ).length : ℝ) ≤ E := by
    refine hPE _ ?_
    have h1 := length_enc_le hmD hnd
    calc (SatFree.enc φ).length ≤ (4 * D + 4) * (n + 2) ^ 3 := by omega
      _ ≤ (4 * X) * X ^ 3 := Nat.mul_le_mul (by omega) (by rw [hX])
      _ = 4 * X ^ 4 := by ring
      _ ≤ P * X ^ P := absorb hX1 (by rw [hP]; omega) (by rw [hP]; omega)
  -- the stack
  have hSx : ((((D + 2) * n + 1) * ((6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7) * (n + 2) ^ 3 + 1) + 1 : ℕ) : ℝ) ≤ E := by
    refine hPE _ ?_
    have hA : 6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7 ≤ 25 * X ^ 2 := by
      have e1 : (D + 4) * (3 * wN (2 * n) + 2) ≤ (2 * X) * (6 * X) := Nat.mul_le_mul (by omega) (by omega)
      have e2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
      have e3 : (2 * X) * (6 * X) = 12 * X ^ 2 := by ring
      omega
    have hB : (D + 2) * n + 1 ≤ 2 * X ^ 2 := by
      have e1 : (D + 2) * n ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
      have e2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
      have e3 : X * X = X ^ 2 := by ring
      omega
    rw [← hX]
    calc ((D + 2) * n + 1) * ((6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7) * X ^ 3 + 1) + 1
        ≤ (2 * X ^ 2) * (25 * X ^ 2 * X ^ 3 + X ^ 5) + X ^ 7 := by
          have e1 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX1
          have e2 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ hX1
          gcongr
      _ = 52 * X ^ 7 + X ^ 7 := by ring
      _ = 53 * X ^ 7 := by ring
      _ ≤ P * X ^ P := absorb hX1 (by rw [hP]; omega) (by rw [hP]; omega)
  have hn1 : ((n + 1 + 1 : ℕ) : ℝ) ≤ E := hPE _ (by
    calc n + 1 + 1 = 1 * X ^ 1 := by rw [hX]; ring
      _ ≤ P * X ^ P := absorb hX1 (by rw [hP]; omega) (by rw [hP]; omega))
  have hKa : ((K.a * (lB n D + 1) : ℕ) : ℝ) ≤ E := hPE _ (by
    calc K.a * (lB n D + 1) ≤ K.a * (25 * X ^ 4) := Nat.mul_le_mul_left _ (by omega)
      _ = 25 * K.a * X ^ 4 := by ring
      _ ≤ P * X ^ P := absorb hX1 (by rw [hP]; omega) (by rw [hP]; omega))
  -- the total
  have hS' : (S : ℝ) ≤ E + (E + (E + K.a * (2 * E) + 1)) + 1 := by
    have h1 : (S : ℝ) ≤ ((((D + 2) * n + 1) * ((6 * D + (D + 4) * (3 * wN (2 * n) + 2) + 7) * (n + 2) ^ 3 + 1) + 1 +
        (n + 1 + 1 + (K.a * (lB n D + 1) + K.a * tB C n D + 1)) + 1 : ℕ) : ℝ) := by exact_mod_cast hS
    have hKt : ((K.a * tB C n D : ℕ) : ℝ) ≤ K.a * (2 * E) := by
      push_cast; exact mul_le_mul_of_nonneg_left htB (Nat.cast_nonneg _)
    push_cast at h1 hSx hn1 hKa hKt
    linarith
  have hKa0 : (0 : ℝ) ≤ K.a := Nat.cast_nonneg _
  have hT1 : ((L * (tB C n D + 2) + 1 : ℕ) : ℝ) ≤ 5 * E ^ 2 := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hLE : (L : ℝ) ≤ E := hE ▸ hL
    push_cast
    nlinarith [mul_le_mul hLE (show (tB C n D : ℝ) + 2 ≤ 2 * E + 2 by linarith) (by positivity) (by linarith)]
  have hW : (((SatFree.enc φ).length + S + 1 : ℕ) : ℝ) ≤ (2 * K.a + 7) * E := by
    push_cast
    nlinarith
  have hQE : (Q : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := by
    have h1 := hn₄ n (by omega)
    have h2 : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ Q := one_le_pow₀ (by linarith)
    have h3 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
    nlinarith
  have hEq : E ^ (q + 2) = (2 : ℝ) ^ (δ / 2 * n) := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hη]
    congr 1; push_cast; field_simp
  have hE0 : 0 ≤ E := by linarith
  calc ((q * (L * (tB C n D + 2) + 1) * ((SatFree.enc φ).length + S + 1) ^ q : ℕ) : ℝ)
      = (q : ℝ) * ((L * (tB C n D + 2) + 1 : ℕ) : ℝ) * ((((SatFree.enc φ).length + S + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (5 * E ^ 2) * ((2 * K.a + 7) * E) ^ q := by gcongr
    _ = (Q : ℝ) * E ^ (q + 2) := by rw [hQ, mul_pow]; push_cast; ring
    _ ≤ (2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n) := by
        rw [hEq]; exact mul_le_mul_of_nonneg_right hQE (by positivity)
    _ = (2 : ℝ) ^ (δ * n) := by rw [← Real.rpow_add two_pos]; congr 1; ring

end EthCor.GrowTM
