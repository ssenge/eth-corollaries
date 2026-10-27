import EthCor.HamFormula
import EthCor.ColorSubexp

/-! # The parity of the number of Hamiltonian cycles in time 2^{o(n)}, for bounded degree

The input is the code of G. The front end `preH Δ` writes the compact code of the Cut & Count
formula `hcF n E` of the edge list E of G (m + n variables, width ≤ Δ + 3 when every degree is
≤ Δ); the machine of `MainTheoremForms.MainTheoremCompact` counts it; the last step keeps the low
bit, which is the parity of the number of Hamiltonian cycles (`hc_parity`). With m ≤ Δ·n the bound
c·2^{c·(Δ+3)²·N·r(N)}, N = m + n ≤ (Δ+1)·n, is 2^{o(n)} (`boundH_le`, `hc_parity_subexp`). -/

namespace EthCor.HamTM

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat GraphProblems Turing EthCor.Ham

/-! ### The front end and the last step -/

def gH (x : List Bool) : List Unit × List Bool := read1 x
def nH (x : List Bool) : ℕ := (gH x).1.length
def EH (x : List Bool) : List (ℕ × ℕ) := edges (nH x) (gH x).2
def formH (x : List Bool) : Fml := (hcF (nH x) (EH x)).dedup

/-- The front end: the compact code of the formula, Δ + 3 slots per clause. -/
def preH (Δ : ℕ) (x : List Bool) : List Bool :=
  encK (List.replicate (Δ + 3) ()) (List.replicate (Nat.log2 (2 * ((EH x).length + nH x)) + 1) ()) (formH x)

/-- The last step: the low bit of the count. -/
def postH (w : List Bool) : List Bool := [w.headD false]

/-! ### Both are polynomial-time -/

section Poly

variable {α : Type} [Enc α]

theorem inc_polyT {E : α → List (ℕ × ℕ)} {v : α → ℕ} (hE : PolyT E) (hv : PolyT v) :
    PolyT fun a => inc (E a) (v a) := by
  have r : PolyT fun a => List.range (E a).length := PolyT.range (Unary.of_length hE)
  unfold inc; fun_prop

theorem atMost2_polyT {I : α → List ℕ} (hI : PolyT I) : PolyT fun a => atMost2 (I a) := by
  unfold atMost2; fun_prop

theorem atLeast2_polyT {I : α → List ℕ} (hI : PolyT I) : PolyT fun a => atLeast2 (I a) := by
  unfold atLeast2; fun_prop

theorem edgeC_polyT {m i a b : α → ℕ} (hm : PolyT m) (hi : PolyT i) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => edgeC (m x) (i x) (a x) (b x) := by
  unfold edgeC; fun_prop

theorem tautC_polyT {N : α → ℕ} (hN : Unary N) : PolyT fun a => tautC (N a) := by
  have r : PolyT fun a => List.range (N a) := PolyT.range hN
  unfold tautC; fun_prop

theorem hcF_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : Unary n) (hE : PolyT E) :
    PolyT fun a => hcF (n a) (E a) := by
  have hm : Unary fun a => (E a).length := Unary.of_length hE
  have h1 := tautC_polyT (hm.add hn)
  have h2 : PolyT fun a => (List.range (n a)).flatMap fun v => atMost2 (inc (E a) v) ++ atLeast2 (inc (E a) v) := by
    have hI : PolyT fun p : α × ℕ => inc (E p.1) p.2 := inc_polyT (by fun_prop) (by fun_prop)
    exact PolyT.flatMap (PolyT.append (atMost2_polyT hI) (atLeast2_polyT hI)) (PolyT.range hn)
  have h3 : PolyT fun a => (List.range (E a).length).flatMap fun i =>
      edgeC (E a).length i ((E a).getD i (0, 0)).1 ((E a).getD i (0, 0)).2 :=
    PolyT.flatMap (edgeC_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.range hm)
  have h4 : PolyT fun a => [[((E a).length, false)]] := by fun_prop
  unfold hcF
  exact PolyT.append (PolyT.append (PolyT.append h1 h2) h3) h4

theorem log2_polyT {g : α → ℕ} (hg : PolyT g) : PolyT fun x => Nat.log2 (2 * g x) + 1 := by fun_prop

theorem edges_polyT {n : α → ℕ} {M : α → List Bool} (hn : Unary n) (hM : PolyT M) :
    PolyT fun a => edges (n a) (M a) := by
  have hp := pairs_polyT hn
  have hn' := hn.poly
  unfold edges; fun_prop

end Poly

theorem preH_polyT (Δ : ℕ) : PolyT (preH Δ) := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hm : Unary fun x => (EH x).length := Unary.of_length hE
  have hK : PolyT fun _ : List Bool => List.replicate (Δ + 3) () := Unary.const (Δ + 3)
  have hw : Unary fun x => Nat.log2 (2 * ((EH x).length + nH x)) + 1 :=
    Unary.of_le (((Unary.const 2).mul (hm.add hn)).add (Unary.const 1))
      (log2_polyT (hm.add hn).poly)
      fun x => by have := Nat.log2_le_self (2 * ((EH x).length + nH x)); omega
  have hF : PolyT formH := PolyT.dedup (hcF_polyT hn hE)
  exact encK_polyT hK hw hF

theorem postH_polyT : PolyT postH := by unfold postH; fun_prop

/-! ### The facts on the formula -/

theorem mem_atMost2 {I : List ℕ} {C : List (ℕ × Bool)} (h : C ∈ atMost2 I) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 ∈ I := by
  obtain ⟨i, hi, h⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  refine ⟨by simp, fun l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact hi
  · exact hj
  · exact (List.mem_filter.1 hk).1

theorem mem_atLeast2 {I : List ℕ} {C : List (ℕ × Bool)} (h : C ∈ atLeast2 I) :
    C.length ≤ I.length ∧ ∀ l ∈ C, l.1 ∈ I := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    refine ⟨by rw [List.length_map]; exact List.length_filter_le _ _, fun l hl => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact (List.mem_filter.1 hj).1
  · rw [List.mem_singleton] at h; subst h
    refine ⟨by simp, fun l hl => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact hj

theorem mem_edgeC {m i a b : ℕ} {C : List (ℕ × Bool)} (h : C ∈ edgeC m i a b) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 = i ∨ l.1 = m + a ∨ l.1 = m + b := by
  simp only [edgeC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl <;> simp

/-- The clauses have width at most Δ + 3 and their variables are below m + n. -/
theorem hcF_clause {n Δ : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    (hI : ∀ v < n, (inc E v).length ≤ Δ) {C : List (ℕ × Bool)} (hC : C ∈ hcF n E) :
    C.length ≤ Δ + 3 ∧ ∀ l ∈ C, l.1 < E.length + n := by
  simp only [hcF, List.mem_append] at hC
  rcases hC with ((hC | hC) | hC) | hC
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
    have hi := List.mem_range.1 hi
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact hi
  · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
    have hv := List.mem_range.1 hv
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨h1, h2⟩ := mem_atMost2 hC
      exact ⟨by omega, fun l hl => by have := lt_of_mem_inc (h2 l hl); omega⟩
    · obtain ⟨h1, h2⟩ := mem_atLeast2 hC
      exact ⟨by have := hI v hv; omega, fun l hl => by have := lt_of_mem_inc (h2 l hl); omega⟩
  · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    have hi := List.mem_range.1 hi
    obtain ⟨h1, h2⟩ := mem_edgeC hC
    rw [List.getD_eq_getElem _ _ hi] at h2
    obtain ⟨a1, a2⟩ := hE _ (List.getElem_mem hi)
    exact ⟨by omega, fun l hl => by rcases h2 l hl with h | h | h <;> omega⟩
  · rw [List.mem_singleton] at hC; subst hC
    exact ⟨by simp, fun l hl => by rw [List.mem_singleton] at hl; subst hl; simp only; omega⟩

theorem mem_hcF_taut {n : ℕ} (E : List (ℕ × ℕ)) {i : ℕ} (hi : i < E.length + n) :
    [(i, true), (i, false)] ∈ hcF n E := by
  simp only [hcF, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

/-- Every variable occurs. -/
theorem allOccur_ofH {n : ℕ} {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n)} (hφ : toN φ = (hcF n E).dedup) :
    SatM.AllOccur φ := by
  intro i
  have hC := mem_hcF_taut (n := n) E i.2
  rw [← List.mem_dedup, ← hφ, mem_toN] at hC
  obtain ⟨D, hD, hDe⟩ := hC
  have hl : (i.val, true) ∈ D.map (fun l => (l.1.val, l.2)) := by rw [hDe]; simp
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hl
  exact ⟨D, hD, l', hl', Fin.ext (congrArg Prod.fst e)⟩

theorem two_le_lengthH {n : ℕ} (hn : 2 ≤ n) {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n)}
    (hφ : toN φ = (hcF n E).dedup) : 2 ≤ φ.length := by
  have hl : φ.length = (hcF n E).dedup.length := by rw [← hφ, toN, List.length_map]
  rw [hl]
  have h0 := mem_hcF_taut (n := n) E (i := 0) (by omega)
  have h1 := mem_hcF_taut (n := n) E (i := 1) (by omega)
  rw [← List.mem_dedup] at h0 h1
  have hne : [((0 : ℕ), true), (0, false)] ≠ [(1, true), (1, false)] := by simp
  have hsub : ({[((0 : ℕ), true), (0, false)], [(1, true), (1, false)]} : Finset (List (ℕ × Bool))) ⊆
      (hcF n E).dedup.toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rw [List.mem_toFinset]; rcases hC with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_dedup _)] at this
  exact this

theorem isKCNF_ofH {n Δ : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    (hI : ∀ v < n, (inc E v).length ≤ Δ) {φ : Sat3.CNF (E.length + n)} (hφ : toN φ = (hcF n E).dedup) :
    SatK.IsKCNF (Δ + 3) φ := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have hm : D.map (fun l => (l.1.val, l.2)) ∈ toN φ := mem_toN.2 ⟨D, hD, rfl⟩
    rw [hφ, List.mem_dedup] at hm
    simpa using (hcF_clause hn hE hI hm).1
  · have h : (toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
    exact List.Nodup.of_map _ h

theorem numSat_ofH {n : ℕ} {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n)} (hφ : toN φ = (hcF n E).dedup) :
    SatK.numSat φ = cntN (E.length + n) (hcF n E) := by
  rw [← stCntToN, hφ]
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]

/-! ### The length bounds -/

theorem length_atMost2_le (I : List ℕ) : (atMost2 I).length ≤ I.length * (I.length * I.length) := by
  refine length_flatMap_le _ _ _ fun i _ => length_flatMap_le _ _ _ fun j _ => ?_
  rw [List.length_map]; exact List.length_filter_le _ _

theorem length_hcF_le (n : ℕ) (E : List (ℕ × ℕ)) : (hcF n E).length ≤ 7 * (E.length + n + 2) ^ 4 := by
  obtain ⟨s, hs⟩ : ∃ s, s = E.length + n + 2 := ⟨_, rfl⟩
  rw [← hs]
  have hI : ∀ v, (inc E v).length ≤ s := fun v => (List.length_filter_le _ _).trans (by simp; omega)
  have h2 : ((List.range n).flatMap fun v => atMost2 (inc E v) ++ atLeast2 (inc E v)).length ≤
      (List.range n).length * (s * (s * s) + (s + 1)) := by
    refine length_flatMap_le _ _ _ fun v _ => ?_
    rw [List.length_append]
    have a1 := length_atMost2_le (inc E v)
    have a2 : (atLeast2 (inc E v)).length = (inc E v).length + 1 := by simp [atLeast2]
    have a3 := hI v
    have a4 : (inc E v).length * ((inc E v).length * (inc E v).length) ≤ s * (s * s) :=
      Nat.mul_le_mul a3 (Nat.mul_le_mul a3 a3)
    omega
  have h3 : ((List.range E.length).flatMap fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2).length ≤
      (List.range E.length).length * 2 :=
    length_flatMap_le _ _ _ fun i _ => by simp [edgeC]
  rw [List.length_range] at h2 h3
  simp only [hcF, List.length_append, tautC, List.length_map, List.length_range, List.length_singleton]
  have p1 : n * (s * (s * s) + (s + 1)) ≤ s * (s * (s * s) + (s + 1)) := Nat.mul_le_mul_right _ (by omega)
  have e : s * (s * (s * s) + (s + 1)) = s ^ 4 + s ^ 2 + s := by ring
  have p2 : s ^ 2 ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : s ≤ s ^ 4 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The theorem -/

theorem length_code_eq {n : ℕ} (G : SimpleGraph (Fin n)) : (code G).length = n + 1 + n * n := by
  simp [unary, code, stMatrixLength n G]; omega

open Classical in
/-- **The parity of the number of Hamiltonian cycles, bounded degree.** For every Δ one Turing
machine and one constant c: for every graph G on n ≥ 4 vertices with all degrees ≤ Δ, given G, it
outputs whether G has an odd number of Hamiltonian cycles within c·2^{c·(Δ+3)²·N·r(N)} steps,
N = |E(G)| + n, r(N) = lg lg(N+4)/√lg(N+4). -/
theorem hc_parity_tm (Δ : ℕ) : ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 4 ≤ n → (∀ v, G.degree v ≤ Δ) →
      Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)]
        (SatM.boundNK (SatK.rN 1 (1 / 2)) c (Δ + 3) ((edges n (matrix G)).length + n)) := by
  obtain ⟨M₀, C, hfin, hM⟩ := compact
  obtain ⟨M, q, hfinM, hW⟩ := Wrap.everyMachineCanBeWrapped M₀ hfin (preH Δ) postH (preH_polyT Δ) postH_polyT
  obtain ⟨c, hc⟩ := wrapped_time_le_rateK q C C (1000 * (Δ + 3)) 6
  refine ⟨M, c, hfinM, fun n G hn hdeg => ?_⟩
  have hE := edges_bound n (matrix G)
  have hI : ∀ v < n, (inc (edges n (matrix G)) v).length ≤ Δ := fun v hv =>
    (length_inc_le stAdj G ⟨v, hv⟩).trans (hdeg _)
  set E := edges n (matrix G) with hEd
  obtain ⟨φ, hφ⟩ := GraphProblems.exists_toN (N := E.length + n) (ψ := (hcF n E).dedup)
    (fun C hC l hl => (hcF_clause (by omega) hE hI (List.mem_dedup.1 hC)).2 l hl)
  have hocc := VariableBound.Rename.allOccurStmt _ φ (allOccur_ofH hφ)
  have hpre : preH Δ (code G) = MainTheoremForms.encC (Δ + 3) φ := by
    rw [preH, formH, EH, nH, gH, stRead1 n G]
    simp only [List.length_replicate]
    rw [← hEd, ← hφ, encK_toN]
  have hrun := hM (Δ + 3) (E.length + n) φ (by omega) (isKCNF_ofH (by omega) hE hI hφ)
    (two_le_lengthH (by omega) hφ) (by rw [hocc.1]; omega)
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc.1, hocc.2] at hrun
  have hout := hW (code G) _ _ (by rw [hpre]; exact hrun)
  have hbit : postH (SatK.binary (E.length + n) (SatK.numSat φ)) = [decide (numHamCycles G % 2 = 1)] := by
    rw [postH, SatK.binary, List.range_succ_eq_map, List.map_cons, List.headD_cons, Nat.testBit_zero,
      numSat_ofH hφ, hEd, hc_parity stAdj (by omega) G]
  rw [hbit] at hout
  refine Wrap.Outputs.mono hout ?_
  -- the polynomial parts
  obtain ⟨s, hs⟩ : ∃ s, s = E.length + n + 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = Δ + 3 := ⟨_, rfl⟩
  have hw : Nat.log2 (2 * (E.length + n)) + 1 ≤ 2 * s := by
    have := Nat.log2_le_self (2 * (E.length + n)); omega
  have hm : φ.length ≤ 7 * s ^ 4 := by
    have h1 : φ.length = (hcF n E).dedup.length := by rw [← hφ, toN, List.length_map]
    have h2 := (List.dedup_sublist (hcF n E)).length_le
    have h3 := length_hcF_le n E
    rw [← hs] at h3
    omega
  have q1 : K ≤ K * s ^ 6 := Nat.le_mul_of_pos_right K (pow_pos (by omega) 6)
  have q2 : s ≤ s ^ 6 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : s ^ 6 ≤ K * s ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have q4 : K * s ^ 5 ≤ K * s ^ 6 := Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by omega) (by omega))
  have q5 : s ^ 2 ≤ s ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : (MainTheoremForms.encC (Δ + 3) φ).length ≤ 1000 * (Δ + 3) * (E.length + n + 2) ^ 6 := by
    rw [Wrap.length_encC, ← hs, ← hK]
    have e : 7 * s ^ 4 * (K * (2 * s)) = 14 * (K * s ^ 5) := by ring
    have e2 : 1000 * K * s ^ 6 = 1000 * (K * s ^ 6) := by ring
    calc K + (Nat.log2 (2 * (E.length + n)) + 1) + 2 + φ.length * (K * (Nat.log2 (2 * (E.length + n)) + 1))
        ≤ K + 2 * s + 2 + 7 * s ^ 4 * (K * (2 * s)) := by gcongr
      _ ≤ 1000 * K * s ^ 6 := by omega
  have hX : (code G).length ≤ 1000 * (Δ + 3) * (E.length + n + 2) ^ 6 := by
    rw [length_code_eq, ← hs, ← hK]
    have e : 1000 * K * s ^ 6 = 1000 * (K * s ^ 6) := by ring
    have hnn : n * n ≤ s ^ 2 := by
      calc n * n ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
        _ = s ^ 2 := by ring
    omega
  exact hc (Δ + 3) (E.length + n) φ.length (E.length + n) _ _ (by omega) (by omega) (by omega) (by omega) hL hX

/-! ### The bound is 2^{o(n)} -/

/-- For n ≤ N ≤ D·n and n large, c·2^{c·K²·N·r(N)} ≤ 2^{εn}. -/
theorem boundH_le (c K D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n N : ℕ, n₀ ≤ n → n ≤ N → N ≤ D * n →
      (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N) ≤ (2 : ℝ) ^ (ε * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 28 * ((c : ℝ) * (K : ℝ) ^ 2 * D) / Real.log 2 + 1 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((2 : ℝ) ^ ((2 * A / ε) ^ (28 / 13 : ℝ)))
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (2 * Real.logb 2 ((c : ℝ) + 1) / ε)
  refine ⟨n₁ + n₂ + 2, fun n N hn hnN hND => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  have hy : Real.logb 2 n ≤ Real.logb 2 ((N : ℝ) + 4) := by
    refine (Real.logb_le_logb one_lt_two (by linarith) (by positivity)).2 ?_
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  generalize hL : Real.logb 2 n = L at hL1 hy
  have hL0 : 0 < L := by linarith
  -- n is large: A·L^{−13/28} ≤ ε/2
  have hLs : A * L ^ (-(13 / 28 : ℝ)) ≤ ε / 2 := by
    have hLbig : (2 * A / ε) ^ (28 / 13 : ℝ) ≤ L := by
      rw [← hL, Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
      exact hn₁.trans (by exact_mod_cast (by omega : n₁ ≤ n))
    have h1 : 2 * A / ε ≤ L ^ (13 / 28 : ℝ) := by
      calc 2 * A / ε = ((2 * A / ε) ^ (28 / 13 : ℝ)) ^ (13 / 28 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ L ^ (13 / 28 : ℝ) := Real.rpow_le_rpow (by positivity) hLbig (by norm_num)
    have hpos : 0 < L ^ (13 / 28 : ℝ) := Real.rpow_pos_of_pos hL0 _
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  have hr : SatK.rN 1 (1 / 2) N ≤ 28 / Real.log 2 * L ^ (-(13 / 28 : ℝ)) :=
    (rate_le_pow _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL0 hy (by norm_num)) (by positivity))
  have hr0 : 0 ≤ SatK.rN 1 (1 / 2) N := Wrap.Arith.rate_nonneg _
  -- the exponent is at most εn/2
  have hE : (c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N ≤ ε / 2 * n := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hND' : (N : ℝ) ≤ D * n := by exact_mod_cast hND
    have hpow : 0 ≤ L ^ (-(13 / 28 : ℝ)) := by positivity
    calc (c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N
        ≤ (c : ℝ) * (K : ℝ) ^ 2 * (D * n) * (28 / Real.log 2 * L ^ (-(13 / 28 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hND' (by positivity)) hr hr0 (by positivity)
      _ = 28 * ((c : ℝ) * (K : ℝ) ^ 2 * D) / Real.log 2 * L ^ (-(13 / 28 : ℝ)) * n := by ring
      _ ≤ A * L ^ (-(13 / 28 : ℝ)) * n := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hpow) hn0
          rw [hA]; linarith
      _ ≤ ε / 2 * n := mul_le_mul_of_nonneg_right hLs hn0
  -- the constant factor is at most 2^{εn/2}
  have hc : (c : ℝ) ≤ (2 : ℝ) ^ (ε / 2 * n) := by
    have h3 : Real.logb 2 ((c : ℝ) + 1) ≤ ε / 2 * n := by
      have : (n₂ : ℝ) ≤ n := by exact_mod_cast (by omega : n₂ ≤ n)
      rw [div_le_iff₀ hε] at hn₂
      nlinarith [mul_le_mul_of_nonneg_left this hε.le]
    calc (c : ℝ) ≤ c + 1 := by linarith
      _ = (2 : ℝ) ^ Real.logb 2 ((c : ℝ) + 1) := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (ε / 2 * n) := Real.rpow_le_rpow_of_exponent_le one_le_two h3
  calc (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N)
      ≤ (2 : ℝ) ^ (ε / 2 * n) * (2 : ℝ) ^ (ε / 2 * n) :=
        mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le one_le_two hE) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (ε * n) := by rw [← Real.rpow_add two_pos]; congr 1; ring

open Classical in
/-- **⊕Hamiltonian Cycle in 2^{o(n)}, bounded degree.** For every Δ one Turing machine: for every
ε > 0 there is n₀ such that for every graph G on n ≥ n₀ vertices with all degrees ≤ Δ, given G, it
outputs whether the number of Hamiltonian cycles of G is odd within 2^{εn} steps. -/
theorem hc_parity_subexp (Δ : ℕ) : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n → (∀ v, G.degree v ≤ Δ) →
      Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)] ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, c, hfin, hM⟩ := hc_parity_tm Δ
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := boundH_le c (Δ + 3) (Δ + 1) hε
  refine ⟨n₀ + 4, fun n G hn hdeg => ?_⟩
  have hm : (edges n (matrix G)).length ≤ Δ * n :=
    length_edges_le _ (edges_bound n (matrix G)) fun v hv => (length_inc_le stAdj G ⟨v, hv⟩).trans (hdeg _)
  refine Wrap.Outputs.mono (hM n G (by omega) hdeg) (Nat.floor_le_floor ?_)
  exact hn₀ n _ (by omega) (by omega) (by rw [Nat.add_mul, one_mul]; omega)

end EthCor.HamTM
