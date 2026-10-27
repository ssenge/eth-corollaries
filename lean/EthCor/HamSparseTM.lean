import EthCor.HamCounter
import EthCor.HamTM

/-! # The parity of the number of Hamiltonian cycles in time 2^{o(n)}, for sparse graphs

The front end `preS` writes the compact code of the Cut & Count formula with sequential counters
`hcS n E` of the edge list E of G. It has N = 5m + n + 2 variables and width 3, whatever the
degrees. The machine of `MainTheoremForms.MainTheoremCompact` counts it, and the last step keeps the
low bit, the parity of the number of Hamiltonian cycles (`hcS_parity`). The bound is
c·2^{9c·N·r(N)} (`hcS_tm`). For m ≤ n·(lg n)^{1/2−θ} edges it is 2^{o(n)} (`boundS_le`,
`hc_parity_sparse`), with one machine for all such graphs. -/

namespace EthCor.HamSTM

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat GraphProblems Turing EthCor.Ham EthCor.HamS
  EthCor.HamTM

/-! ### The front end -/

/-- The number of variables of `hcS` for the input x. -/
def NS (x : List Bool) : ℕ := (EH x).length + nH x + (4 * (EH x).length + 2)

def formS (x : List Bool) : Fml := (hcS (nH x) (EH x)).dedup

/-- The front end: the compact code of the formula, 3 slots per clause. -/
def preS (x : List Bool) : List Bool :=
  encK (List.replicate 3 ()) (List.replicate (Nat.log2 (2 * NS x) + 1) ()) (formS x)

/-! ### It is polynomial-time -/

section Poly

variable {α : Type} [Enc α]

theorem stepC_polyT {p x c : α → ℕ} (hp : PolyT p) (hx : PolyT x) (hc : PolyT c) :
    PolyT fun a => HamS.stepC (p a) (x a) (c a) := by
  unfold HamS.stepC; fun_prop

theorem cntC_polyT {z : α → ℕ} {L : α → List (ℕ × ℕ)} (hz : PolyT z) (hL : PolyT L) :
    PolyT fun a => cntC (z a) (L a) := by
  have hm : Unary fun a => (L a).length := Unary.of_length hL
  have hP : PolyT fun a => z a :: (L a).map Prod.snd := by fun_prop
  have h1 : PolyT fun a => (List.range (L a).length).flatMap fun k =>
      HamS.stepC ((z a :: (L a).map Prod.snd).getD k 0) ((L a).getD k (0, 0)).1 ((L a).getD k (0, 0)).2 :=
    PolyT.flatMap (stepC_polyT (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.range hm)
  have h2 : PolyT fun a => [[((z a :: (L a).map Prod.snd).getD (L a).length 0 + 1, true)]] := by fun_prop
  unfold cntC
  exact PolyT.append h1 h2

/-- Stated generically: `fun_prop` times out on the concrete sum. -/
theorem lin_polyT {f g h k : α → ℕ} (hf : PolyT f) (hg : PolyT g) (hh : PolyT h) (hk : PolyT k) :
    PolyT fun a => f a + g a + (4 * h a + 2 * k a) := by fun_prop

theorem cb_polyT {E : α → List (ℕ × ℕ)} {n v e : α → ℕ} (hE : PolyT E) (hn : PolyT n) (hv : PolyT v)
    (he : PolyT e) : PolyT fun a => cb (E a) (n a) (v a) (e a) := by
  have h1 : PolyT fun a => ((E a).getD (e a) (0, 0)).1 := by fun_prop
  have h2 : PolyT fun a => min (v a - ((E a).getD (e a) (0, 0)).1) 1 := by fun_prop
  unfold cb
  exact lin_polyT (by fun_prop) hn he h2

theorem incC_polyT {E : α → List (ℕ × ℕ)} {n v : α → ℕ} (hE : PolyT E) (hn : PolyT n) (hv : PolyT v) :
    PolyT fun a => incC (E a) (n a) (v a) := by
  have hI : PolyT fun a => inc (E a) (v a) := inc_polyT hE hv
  have hc : PolyT fun p : α × ℕ => cb (E p.1) (n p.1) (v p.1) p.2 :=
    cb_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hf : PolyT fun p : α × ℕ => (p.2, cb (E p.1) (n p.1) (v p.1) p.2) := by fun_prop
  unfold incC
  exact PolyT.map hf hI

theorem hcS_polyT {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : Unary n) (hE : PolyT E) :
    PolyT fun a => hcS (n a) (E a) := by
  have hm : Unary fun a => (E a).length := Unary.of_length hE
  have h1 := tautC_polyT ((hm.add hn).add (((Unary.const 4).mul hm).add (Unary.const 2)))
  have hz : PolyT fun a => zC (E a) (n a) := by unfold zC; have := hn.poly; have := hm.poly; fun_prop
  have h2 : PolyT fun a => (List.range (n a)).flatMap fun v => cntC (zC (E a) (n a)) (incC (E a) (n a) v) := by
    have hI : PolyT fun p : α × ℕ => incC (E p.1) (n p.1) p.2 :=
      incC_polyT (by fun_prop) (by have := hn.poly; fun_prop) (by fun_prop)
    have hz' : PolyT fun p : α × ℕ => zC (E p.1) (n p.1) := by unfold zC; have := hn.poly; fun_prop
    exact PolyT.flatMap (cntC_polyT hz' hI) (PolyT.range hn)
  have h3 : PolyT fun a => (List.range (E a).length).flatMap fun i =>
      edgeC (E a).length i ((E a).getD i (0, 0)).1 ((E a).getD i (0, 0)).2 :=
    PolyT.flatMap (edgeC_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.range hm)
  have h4 : PolyT fun a => [[((E a).length, false)], [(zC (E a) (n a), false)], [(zC (E a) (n a) + 1, false)]] := by
    fun_prop
  unfold hcS
  exact PolyT.append (PolyT.append (PolyT.append h1 h2) h3) h4

end Poly

theorem preS_polyT : PolyT preS := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hm : Unary fun x => (EH x).length := Unary.of_length hE
  have hN : Unary NS := (hm.add hn).add (((Unary.const 4).mul hm).add (Unary.const 2))
  have hK : PolyT fun _ : List Bool => List.replicate 3 () := Unary.const 3
  have hw : Unary fun x => Nat.log2 (2 * NS x) + 1 :=
    Unary.of_le (((Unary.const 2).mul hN).add (Unary.const 1)) (log2_polyT hN.poly)
      fun x => by have := Nat.log2_le_self (2 * NS x); omega
  have hF : PolyT formS := PolyT.dedup (hcS_polyT hn hE)
  exact encK_polyT hK hw hF

/-! ### The facts on the formula -/

theorem getD_prop {β : Type} {P : β → Prop} {l : List β} {d : β} (hd : P d) (h : ∀ b ∈ l, P b) (k : ℕ) :
    P (l.getD k d) := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ hk]; exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hd

theorem mem_stepC {p x c : ℕ} {C : List (ℕ × Bool)} (h : C ∈ HamS.stepC p x c) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 = p ∨ l.1 = p + 1 ∨ l.1 = x ∨ l.1 = c ∨ l.1 = c + 1 := by
  simp only [HamS.stepC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The clauses of a counter have at most three literals, and their variables are below B. -/
theorem cntC_clause {z B : ℕ} {L : List (ℕ × ℕ)} (hB : 1 < B) (hz : z + 1 < B)
    (hL : ∀ q ∈ L, q.1 < B ∧ q.2 + 1 < B) {C : List (ℕ × Bool)} (hC : C ∈ cntC z L) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < B := by
  have hP : ∀ k, (z :: L.map Prod.snd).getD k 0 + 1 < B := fun k =>
    getD_prop (P := fun p => p + 1 < B) (by omega) (fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hz
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact (hL q hq).2) k
  have hQ : ∀ k, (L.getD k (0, 0)).1 < B ∧ (L.getD k (0, 0)).2 + 1 < B := fun k =>
    getD_prop (P := fun q : ℕ × ℕ => q.1 < B ∧ q.2 + 1 < B) ⟨by show 0 < B; omega, by show 0 + 1 < B; omega⟩ hL k
  unfold cntC at hC
  rcases List.mem_append.1 hC with hC | hC
  · obtain ⟨k, -, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨h1, h2⟩ := mem_stepC hC
    refine ⟨h1, fun l hl => ?_⟩
    have := hP k; have := hQ k
    rcases h2 l hl with h | h | h | h | h <;> omega
  · rw [List.mem_singleton] at hC; subst hC
    refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl
    exact hP L.length

/-- The clauses have at most three literals and their variables are below m + n + (4m + 2). -/
theorem hcS_clause {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    {C : List (ℕ × Bool)} (hC : C ∈ hcS n E) :
    C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < E.length + n + (4 * E.length + 2) := by
  simp only [hcS, List.mem_append] at hC
  rcases hC with ((hC | hC) | hC) | hC
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
    have hi := List.mem_range.1 hi
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact hi
  · obtain ⟨v, -, hC⟩ := List.mem_flatMap.1 hC
    refine cntC_clause (by omega) (by unfold zC; omega) (fun q hq => ?_) hC
    unfold incC at hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
    have := lt_of_mem_inc he
    have : min (v - (E.getD e (0, 0)).1) 1 ≤ 1 := min_le_right _ _
    refine ⟨by omega, ?_⟩
    show cb E n v e + 1 < _
    unfold cb
    omega
  · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    have hi := List.mem_range.1 hi
    obtain ⟨h1, h2⟩ := mem_edgeC hC
    rw [List.getD_eq_getElem _ _ hi] at h2
    obtain ⟨a1, a2⟩ := hE _ (List.getElem_mem hi)
    exact ⟨by omega, fun l hl => by rcases h2 l hl with h | h | h <;> omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;> rw [List.mem_singleton] at hl <;>
      subst hl <;> simp only [zC] <;> omega

theorem mem_hcS_taut {n : ℕ} (E : List (ℕ × ℕ)) {i : ℕ} (hi : i < E.length + n + (4 * E.length + 2)) :
    [(i, true), (i, false)] ∈ hcS n E := by
  simp only [hcS, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

/-- Every variable occurs. -/
theorem allOccur_ofS {n : ℕ} {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n + (4 * E.length + 2))}
    (hφ : toN φ = (hcS n E).dedup) : SatM.AllOccur φ := by
  intro i
  have hC := mem_hcS_taut (n := n) E i.2
  rw [← List.mem_dedup, ← hφ, mem_toN] at hC
  obtain ⟨D, hD, hDe⟩ := hC
  have hl : (i.val, true) ∈ D.map (fun l => (l.1.val, l.2)) := by rw [hDe]; simp
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hl
  exact ⟨D, hD, l', hl', Fin.ext (congrArg Prod.fst e)⟩

theorem two_le_lengthS {n : ℕ} {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n + (4 * E.length + 2))}
    (hφ : toN φ = (hcS n E).dedup) : 2 ≤ φ.length := by
  have hl : φ.length = (hcS n E).dedup.length := by rw [← hφ, toN, List.length_map]
  rw [hl]
  have h0 := mem_hcS_taut (n := n) E (i := 0) (by omega)
  have h1 := mem_hcS_taut (n := n) E (i := 1) (by omega)
  rw [← List.mem_dedup] at h0 h1
  have hne : [((0 : ℕ), true), (0, false)] ≠ [(1, true), (1, false)] := by simp
  have hsub : ({[((0 : ℕ), true), (0, false)], [(1, true), (1, false)]} : Finset (List (ℕ × Bool))) ⊆
      (hcS n E).dedup.toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rw [List.mem_toFinset]; rcases hC with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_dedup _)] at this
  exact this

theorem isKCNF_ofS {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    {φ : Sat3.CNF (E.length + n + (4 * E.length + 2))} (hφ : toN φ = (hcS n E).dedup) : SatK.IsKCNF 3 φ := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have hm : D.map (fun l => (l.1.val, l.2)) ∈ toN φ := mem_toN.2 ⟨D, hD, rfl⟩
    rw [hφ, List.mem_dedup] at hm
    simpa using (hcS_clause hn hE hm).1
  · have h : (toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
    exact List.Nodup.of_map _ h

theorem numSat_ofS {n : ℕ} {E : List (ℕ × ℕ)} {φ : Sat3.CNF (E.length + n + (4 * E.length + 2))}
    (hφ : toN φ = (hcS n E).dedup) : SatK.numSat φ = cntN (E.length + n + (4 * E.length + 2)) (hcS n E) := by
  rw [← stCntToN, hφ]
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]

/-! ### The length bound -/

theorem length_cntC_le (z : ℕ) (L : List (ℕ × ℕ)) : (cntC z L).length ≤ L.length * 8 + 1 := by
  unfold cntC
  rw [List.length_append, List.length_singleton]
  have := length_flatMap_le (List.range L.length) (fun k =>
      HamS.stepC ((z :: L.map Prod.snd).getD k 0) (L.getD k (0, 0)).1 (L.getD k (0, 0)).2) 8 (fun k _ => by simp [HamS.stepC])
  rw [List.length_range] at this
  omega

theorem length_hcS_le (n : ℕ) (E : List (ℕ × ℕ)) : (hcS n E).length ≤ 20 * (E.length + n + 2) ^ 2 := by
  obtain ⟨s, hs⟩ : ∃ s, s = E.length + n + 2 := ⟨_, rfl⟩
  rw [← hs]
  have hI : ∀ v, (incC E n v).length ≤ E.length := fun v => by
    rw [incC, List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
  have h2 : ((List.range n).flatMap fun v => cntC (zC E n) (incC E n v)).length ≤ (List.range n).length * (E.length * 8 + 1) :=
    length_flatMap_le _ _ _ fun v _ => (length_cntC_le _ _).trans (by have := hI v; omega)
  have h3 : ((List.range E.length).flatMap fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2).length ≤
      (List.range E.length).length * 2 :=
    length_flatMap_le _ _ _ fun i _ => by simp [edgeC]
  rw [List.length_range] at h2 h3
  simp only [hcS, List.length_append, tautC, List.length_map, List.length_range, List.length_cons, List.length_nil]
  have p1 : n * (E.length * 8 + 1) ≤ s * (s * 8 + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : s * (s * 8 + 1) = 8 * s ^ 2 + s := by ring
  have p2 : s ≤ s ^ 2 := Nat.le_self_pow (by norm_num) s
  have p3 : 2 ≤ s := by omega
  have p4 : 2 * s ≤ s ^ 2 := by nlinarith
  omega

/-! ### The machine -/

open Classical in
/-- **The parity of the number of Hamiltonian cycles, any degree.** One Turing machine and one
constant c: for every graph G on n ≥ 4 vertices with m edges, given G, it outputs whether G has an
odd number of Hamiltonian cycles within c·2^{9c·N·r(N)} steps, N = 5m + n + 2,
r(N) = lg lg(N+4)/√lg(N+4). -/
theorem hcS_tm : ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 4 ≤ n →
      Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)]
        (SatM.boundNK (SatK.rN 1 (1 / 2)) c 3
          ((edges n (matrix G)).length + n + (4 * (edges n (matrix G)).length + 2))) := by
  obtain ⟨M₀, C, hfin, hM⟩ := compact
  obtain ⟨M, q, hfinM, hW⟩ := Wrap.everyMachineCanBeWrapped M₀ hfin preS postH preS_polyT postH_polyT
  obtain ⟨c, hc⟩ := wrapped_time_le_rateK q C C 1000 3
  refine ⟨M, c, hfinM, fun n G hn => ?_⟩
  have hE := edges_bound n (matrix G)
  set E := edges n (matrix G) with hEd
  obtain ⟨φ, hφ⟩ := GraphProblems.exists_toN (N := E.length + n + (4 * E.length + 2)) (ψ := (hcS n E).dedup)
    (fun C hC l hl => (hcS_clause (by omega) hE (List.mem_dedup.1 hC)).2 l hl)
  have hocc := VariableBound.Rename.allOccurStmt _ φ (allOccur_ofS hφ)
  have hpre : preS (code G) = MainTheoremForms.encC 3 φ := by
    rw [preS, formS, NS, EH, nH, gH, stRead1 n G]
    simp only [List.length_replicate]
    rw [← hEd, ← hφ, encK_toN]
  have hrun := hM 3 (E.length + n + (4 * E.length + 2)) φ (by omega) (isKCNF_ofS (by omega) hE hφ)
    (two_le_lengthS hφ) (by rw [hocc.1]; omega)
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc.1, hocc.2] at hrun
  have hout := hW (code G) _ _ (by rw [hpre]; exact hrun)
  have hbit : postH (SatK.binary (E.length + n + (4 * E.length + 2)) (SatK.numSat φ)) =
      [decide (numHamCycles G % 2 = 1)] := by
    rw [postH, SatK.binary, List.range_succ_eq_map, List.map_cons, List.headD_cons, Nat.testBit_zero,
      numSat_ofS hφ, hEd, hcS_parity stAdj (by omega) G]
  rw [hbit] at hout
  refine Wrap.Outputs.mono hout ?_
  -- the polynomial parts, in S = N + 2
  obtain ⟨S, hS⟩ : ∃ S, S = E.length + n + (4 * E.length + 2) + 2 := ⟨_, rfl⟩
  have hw : Nat.log2 (2 * (E.length + n + (4 * E.length + 2))) + 1 ≤ 2 * S := by
    have := Nat.log2_le_self (2 * (E.length + n + (4 * E.length + 2))); omega
  have hm : φ.length ≤ 20 * S ^ 2 := by
    have h1 : φ.length = (hcS n E).dedup.length := by rw [← hφ, toN, List.length_map]
    have h2 := (List.dedup_sublist (hcS n E)).length_le
    have h3 := length_hcS_le n E
    have h4 : (E.length + n + 2) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have q1 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) S
  have q2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : (MainTheoremForms.encC 3 φ).length ≤ 1000 * (E.length + n + (4 * E.length + 2) + 2) ^ 3 := by
    rw [Wrap.length_encC, ← hS]
    have e : 20 * S ^ 2 * (3 * (2 * S)) = 120 * S ^ 3 := by ring
    calc 3 + (Nat.log2 (2 * (E.length + n + (4 * E.length + 2))) + 1) + 2 +
          φ.length * (3 * (Nat.log2 (2 * (E.length + n + (4 * E.length + 2))) + 1))
        ≤ 3 + 2 * S + 2 + 20 * S ^ 2 * (3 * (2 * S)) := by gcongr
      _ ≤ 1000 * S ^ 3 := by omega
  have hX : (code G).length ≤ 1000 * (E.length + n + (4 * E.length + 2) + 2) ^ 3 := by
    rw [length_code_eq, ← hS]
    have hnn : n * n ≤ S ^ 2 := by
      calc n * n ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
        _ = S ^ 2 := by ring
    omega
  exact hc 3 (E.length + n + (4 * E.length + 2)) φ.length (E.length + n + (4 * E.length + 2)) _ _
    (by omega) (by omega) (by omega) (by omega) hL hX

/-! ### The bound is 2^{o(n)} for m ≤ n·(lg n)^{1/2−θ} -/

/-- For n ≤ N ≤ 8n·(lg n)^{1/2−θ} and n large, c·2^{c·K²·N·r(N)} ≤ 2^{εn}. -/
theorem boundS_le (c K : ℕ) {θ ε : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n N : ℕ, n₀ ≤ n → n ≤ N → (N : ℝ) ≤ 8 * n * Real.logb 2 n ^ (1 / 2 - θ) →
      (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N) ≤ (2 : ℝ) ^ (ε * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 16 * ((c : ℝ) * (K : ℝ) ^ 2 + 1) / (θ * Real.log 2) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((2 : ℝ) ^ ((2 * A / ε) ^ (2 / θ)))
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (2 * Real.logb 2 ((c : ℝ) + 1) / ε)
  refine ⟨n₁ + n₂ + 2, fun n N hn hnN hNL => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  have hy : Real.logb 2 n ≤ Real.logb 2 ((N : ℝ) + 4) := by
    refine (Real.logb_le_logb one_lt_two (by linarith) (by positivity)).2 ?_
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  generalize hL : Real.logb 2 n = L at hL1 hy hNL
  have hL0 : 0 < L := by linarith
  -- n is large: A·L^{−θ/2} ≤ ε/2
  have hLs : A * L ^ (-(θ / 2)) ≤ ε / 2 := by
    have hLbig : (2 * A / ε) ^ (2 / θ) ≤ L := by
      rw [← hL, Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
      exact hn₁.trans (by exact_mod_cast (by omega : n₁ ≤ n))
    have h1 : 2 * A / ε ≤ L ^ (θ / 2) := by
      calc 2 * A / ε = ((2 * A / ε) ^ (2 / θ)) ^ (θ / 2) := by
            rw [← Real.rpow_mul (by positivity), show 2 / θ * (θ / 2) = 1 by field_simp, Real.rpow_one]
        _ ≤ L ^ (θ / 2) := Real.rpow_le_rpow (by positivity) hLbig (by positivity)
    have hpos : 0 < L ^ (θ / 2) := Real.rpow_pos_of_pos hL0 _
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  -- the rate
  have e2 : 1 / (θ / 2 * Real.log 2) = 2 / (θ * Real.log 2) := by
    rw [eq_div_iff (mul_pos hθ hl2).ne', div_mul_eq_mul_div, one_mul,
      div_eq_iff (mul_pos (half_pos hθ) hl2).ne']
    ring
  have hr : SatK.rN 1 (1 / 2) N ≤ 2 / (θ * Real.log 2) * L ^ (θ / 2 - 1 / 2) := by
    rw [← e2]
    exact (rate_le_rpow (half_pos hθ) _).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL0 hy (by linarith)) (by positivity))
  have hr0 : 0 ≤ SatK.rN 1 (1 / 2) N := Wrap.Arith.rate_nonneg _
  -- the exponent is at most εn/2
  have hE : (c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N ≤ ε / 2 * n := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcA : 16 * ((c : ℝ) * (K : ℝ) ^ 2) / (θ * Real.log 2) ≤ A := by
      rw [hA]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    calc (c : ℝ) * (K : ℝ) ^ 2 * (N : ℝ) * SatK.rN 1 (1 / 2) N
        ≤ (c : ℝ) * (K : ℝ) ^ 2 * (8 * n * L ^ (1 / 2 - θ)) * (2 / (θ * Real.log 2) * L ^ (θ / 2 - 1 / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hNL (by positivity)) hr hr0 (by positivity)
      _ = 16 * ((c : ℝ) * (K : ℝ) ^ 2) / (θ * Real.log 2) * (L ^ (1 / 2 - θ) * L ^ (θ / 2 - 1 / 2)) * n := by
          ring
      _ = 16 * ((c : ℝ) * (K : ℝ) ^ 2) / (θ * Real.log 2) * L ^ (-(θ / 2)) * n := by
          rw [← Real.rpow_add hL0, show 1 / 2 - θ + (θ / 2 - 1 / 2) = -(θ / 2) by ring]
      _ ≤ A * L ^ (-(θ / 2)) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcA (by positivity)) hn0
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
/-- The edge list of G has at most as many entries as G has edges. -/
theorem length_edges_le_card {n : ℕ} (G : SimpleGraph (Fin n)) :
    (edges n (matrix G)).length ≤ G.edgeFinset.card := by
  have hE := edges_bound n (matrix G)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : edges 0 (matrix G) = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun p hp => by have := hE p hp; omega
    rw [this]; exact Nat.zero_le _
  set E := edges n (matrix G) with hEd
  have key : ∀ i < E.length, (E.getD i (0, 0)).1 < (E.getD i (0, 0)).2 ∧ (E.getD i (0, 0)).2 < n := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hE _ (List.getElem_mem hi)
  let f : ℕ → Sym2 (Fin n) := fun i =>
    s(⟨(E.getD i (0, 0)).1 % n, Nat.mod_lt _ hn⟩, ⟨(E.getD i (0, 0)).2 % n, Nat.mod_lt _ hn⟩)
  calc E.length = (Finset.range E.length).card := (Finset.card_range _).symm
    _ ≤ G.edgeFinset.card := by
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro i hi
        have hi := Finset.mem_range.1 hi
        obtain ⟨k1, k2⟩ := key i hi
        rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        have hm := (mem_edges stAdj G ⟨(E.getD i (0, 0)).1 % n, Nat.mod_lt _ hn⟩
          ⟨(E.getD i (0, 0)).2 % n, Nat.mod_lt _ hn⟩).1
        simp only [Nat.mod_eq_of_lt (show (E.getD i (0, 0)).1 < n by omega), Nat.mod_eq_of_lt k2] at hm ⊢
        refine (hm ?_).2
        rw [← hEd, List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      · intro i hi j hj hij
        have hi := Finset.mem_range.1 hi
        have hj := Finset.mem_range.1 hj
        obtain ⟨a1, a2⟩ := key i hi
        obtain ⟨b1, b2⟩ := key j hj
        simp only [f, Sym2.eq_iff, Fin.mk.injEq, Nat.mod_eq_of_lt (show (E.getD i (0, 0)).1 < n by omega),
          Nat.mod_eq_of_lt a2, Nat.mod_eq_of_lt (show (E.getD j (0, 0)).1 < n by omega), Nat.mod_eq_of_lt b2] at hij
        rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h1 h2
          exact (edges_nodup n (matrix G)).getElem_inj_iff.1 (Prod.ext h1 h2)
        · omega

open Classical in
/-- **⊕Hamiltonian Cycle in 2^{o(n)} for sparse graphs.** One Turing machine: for every θ > 0 and
ε > 0 there is n₀ such that for every graph G on n ≥ n₀ vertices with at most n·(lg n)^{1/2−θ}
edges, given G, it outputs whether the number of Hamiltonian cycles of G is odd within 2^{εn}
steps. -/
theorem hc_parity_sparse : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ θ ε : ℝ, 0 < θ → 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      (G.edgeFinset.card : ℝ) ≤ n * Real.logb 2 n ^ (1 / 2 - θ) →
        Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)] ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, c, hfin, hM⟩ := hcS_tm
  refine ⟨M, hfin, fun θ ε hθ hε => ?_⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ', θ' = min θ (1 / 4) := ⟨_, rfl⟩
  have hθ'0 : 0 < θ' := by rw [hθ']; exact lt_min hθ (by norm_num)
  have hθ'2 : θ' < 1 / 2 := by rw [hθ']; exact (min_le_right _ _).trans_lt (by norm_num)
  have hθθ : θ' ≤ θ := by rw [hθ']; exact min_le_left _ _
  obtain ⟨n₀, hn₀⟩ := boundS_le c 3 hθ'0 hθ'2 hε
  refine ⟨n₀ + 4, fun n G hn hm => ?_⟩
  refine Wrap.Outputs.mono (hM n G (by omega)) (Nat.floor_le_floor ?_)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; linarith
  obtain ⟨X, hX⟩ : ∃ X, X = Real.logb 2 n ^ (1 / 2 - θ') := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hL1 (by linarith)
  have hmX : ((edges n (matrix G)).length : ℝ) ≤ n * X := by
    have h1 : ((edges n (matrix G)).length : ℝ) ≤ G.edgeFinset.card := by exact_mod_cast length_edges_le_card G
    have h2 : Real.logb 2 n ^ (1 / 2 - θ) ≤ X := by
      rw [hX]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h3 : (n : ℝ) * Real.logb 2 n ^ (1 / 2 - θ) ≤ n * X := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hnX : (n : ℝ) ≤ n * X := by nlinarith
  refine hn₀ n _ (by omega) (by omega) ?_
  rw [← hX]
  push_cast
  linarith

open Classical in
/-- **⊕Hamiltonian Cycle in 2^{o(n)} for bounded degree, one machine for every Δ.** One Turing
machine: for every Δ and ε > 0 there is n₀ such that for every graph G on n ≥ n₀ vertices with
all degrees ≤ Δ, given G, it outputs whether the number of Hamiltonian cycles of G is odd within
2^{εn} steps. (`EthCor.HamTM.hc_parity_subexp` has one machine for each Δ.) -/
theorem hc_parity_bounded : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (Δ : ℕ) (ε : ℝ), 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      (∀ v, G.degree v ≤ Δ) →
        Wrap.Outputs M (code G) [decide (numHamCycles G % 2 = 1)] ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, hfin, hM⟩ := hc_parity_sparse
  refine ⟨M, hfin, fun Δ ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hM (1 / 4) ε (by norm_num) hε
  refine ⟨n₀ + 2 ^ (Δ ^ 4) + 2, fun n G hn hdeg => ?_⟩
  have hp := Nat.two_pow_pos (Δ ^ 4)
  refine hn₀ n G (by omega) ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2E : 2 * G.edgeFinset.card ≤ Δ * n := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    calc ∑ v, G.degree v ≤ ∑ _v : Fin n, Δ := Finset.sum_le_sum fun v _ => hdeg v
      _ = Δ * n := by simp [mul_comm]
  have hL : (Δ : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := by
    have h1 : ((Δ ^ 4 : ℕ) : ℝ) ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le one_lt_two hn0, Real.rpow_natCast]
      exact_mod_cast (show 2 ^ (Δ ^ 4) ≤ n by omega)
    calc (Δ : ℝ) = (((Δ ^ 4 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) := by
          push_cast
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
      _ ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hE : (G.edgeFinset.card : ℝ) ≤ Δ * n := by exact_mod_cast (by omega : G.edgeFinset.card ≤ Δ * n)
  have e : (1 / 2 - 1 / 4 : ℝ) = 1 / 4 := by norm_num
  rw [e]
  calc (G.edgeFinset.card : ℝ) ≤ Δ * n := hE
    _ ≤ n * Real.logb 2 n ^ (1 / 4 : ℝ) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hL hn0.le

end EthCor.HamSTM
