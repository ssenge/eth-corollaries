import EthCor.HomFormula
import EthCor.ColorSubexp

/-! # Counting homomorphisms G → H with one call to the machine of the Main Theorem

The input is h in unary, the h × h matrix of the target relation H, then the code of G. The front end
`preHom` writes the compact code of `homB` (width 2⌈log₂ h⌉ on n⌈log₂ h⌉ + 4 variables), the machine of
the Main Theorem counts it, `bitsTrim` reads the count off (`hom_uniform`). The bound has the same form
as for k-colorings, so the count takes 2^{o(n)} steps for lg h ≤ (lg n)^{1/6−θ} (`hom_subexp`); under
ETH no algorithm decides whether G → H exists in time h^{o(n)} [Cygan et al., J. ACM 2017]. -/

namespace EthCor.Hom

open Groundwork Groundwork.Prog Groundwork.Decode CountKSat GraphProblems Turing

/-! ### The front end -/

def hIn (x : List Bool) : ℕ := ones x
def mIn (x : List Bool) : List Bool := (rest x).take (hIn x * hIn x)
def gIn (x : List Bool) : List Unit × List Bool := read1 ((rest x).drop (hIn x * hIn x))
def formHom (x : List Bool) : Fml := (homB (hIn x) (gIn x).1.length (mIn x) (gIn x).2).dedup

/-- The front end. -/
def preHom (x : List Bool) : List Bool :=
  encK (List.replicate (2 * nb (hIn x)) ()) (List.replicate (Nat.log2 (2 * ((gIn x).1.length * nb (hIn x) + 4)) + 1) ())
    (formHom x)

theorem read_input {n h : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool) :
    hIn (unary h ++ (hmat H ++ code G)) = h ∧ mIn (unary h ++ (hmat H ++ code G)) = hmat H ∧
      gIn (unary h ++ (hmat H ++ code G)) = (List.replicate n (), matrix G) := by
  have h1 : hIn (unary h ++ (hmat H ++ code G)) = h := Read.ones_unary_append h _
  have h2 : rest (unary h ++ (hmat H ++ code G)) = hmat H ++ code G := Read.rest_unary_append h _
  refine ⟨h1, ?_, ?_⟩
  · rw [mIn, h1, h2]; exact List.take_left' (length_hmat H)
  · rw [gIn, h1, h2, List.drop_left' (length_hmat H)]; exact stRead1 n G

/-! ### The front end is polynomial-time -/

section Poly

variable {α : Type} [Enc α]

theorem homB_polyT {h n : α → ℕ} {mH m : α → List Bool} (hh : Unary h) (hn : Unary n) (hmH : PolyT mH)
    (hm : PolyT m) : PolyT fun a => homB (h a) (n a) (mH a) (m a) := by
  have hh' := hh.poly
  have hn' := hn.poly
  have hb := nb_unary hh
  have hb' := hb.poly
  have hA : PolyT fun a => (List.range (n a)).flatMap fun v =>
      ((List.range (2 * h a)).filter fun c => decide (h a ≤ c) && decide (Nat.log2 c < nb (h a))).map
        fun c => forbid (nb (h a)) v c := by
    have hf : PolyT fun q : (α × ℕ) × ℕ => forbid (nb (h q.1.1)) q.1.2 q.2 :=
      forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop)
    have hd : PolyT fun q : (α × ℕ) × ℕ => decide (h q.1.1 ≤ q.2) && decide (Nat.log2 q.2 < nb (h q.1.1)) := by
      fun_prop
    have r : PolyT fun p : α × ℕ => List.range (2 * h p.1) := PolyT.range (((Unary.const 2).mul hh).comp (by fun_prop))
    exact PolyT.flatMap (PolyT.map hf (PolyT.filter hd r)) (PolyT.range hn)
  have hB : PolyT fun a => ((GraphProblems.pairs (n a)).filter fun p => adjB (n a) (m a) p.1 p.2).flatMap fun p =>
      ((GraphProblems.pairs (h a)).filter fun q => !adjB (h a) (mH a) q.1 q.2).map
        fun q => forbid (nb (h a)) p.1 q.1 ++ forbid (nb (h a)) p.2 q.2 := by
    have hf : PolyT fun r : (α × (ℕ × ℕ)) × (ℕ × ℕ) =>
        forbid (nb (h r.1.1)) r.1.2.1 r.2.1 ++ forbid (nb (h r.1.1)) r.1.2.2 r.2.2 :=
      PolyT.append (forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop))
        (forbid_polyT (hb.comp (by fun_prop)) (by fun_prop) (by fun_prop))
    have hq : PolyT fun p : α × (ℕ × ℕ) => (GraphProblems.pairs (h p.1)).filter fun q => !adjB (h p.1) (mH p.1) q.1 q.2 := by
      have hd : PolyT fun r : (α × (ℕ × ℕ)) × (ℕ × ℕ) => !adjB (h r.1.1) (mH r.1.1) r.2.1 r.2.2 := by fun_prop
      exact PolyT.filter hd (pairs_polyT (hh.comp (by fun_prop)))
    have hd : PolyT fun q : α × (ℕ × ℕ) => adjB (n q.1) (m q.1) q.2.1 q.2.2 := by fun_prop
    exact PolyT.flatMap (PolyT.map hf hq) (PolyT.filter hd (pairs_polyT hn))
  have hC : PolyT fun a => (List.range (n a * nb (h a))).map fun i => [(i, true), (i, false)] :=
    PolyT.map (by fun_prop) (PolyT.range (hn.mul hb))
  have hD : PolyT fun a => (List.range 4).map fun i => [(n a * nb (h a) + i, true)] :=
    PolyT.map (by fun_prop) (PolyT.range (Unary.const 4))
  unfold homB
  exact PolyT.append (PolyT.append (PolyT.append hA hB) hC) hD

theorem preHom_polyT : PolyT preHom := by
  have hh : Unary hIn := ones_unary PolyT.id'
  have hh' := hh.poly
  have hr : PolyT rest := by fun_prop
  have hmH : PolyT mIn := by unfold mIn; fun_prop
  have hg : PolyT gIn := by unfold gIn; have := stCertRead.1; fun_prop
  have hn : Unary fun x => (gIn x).1.length := Unary.of_length hg.fst
  have hb := nb_unary hh
  have hK : PolyT fun x => List.replicate (2 * nb (hIn x)) () := (Unary.const 2).mul hb
  have hw : Unary fun x => Nat.log2 (2 * ((gIn x).1.length * nb (hIn x) + 4)) + 1 :=
    Unary.of_le (((Unary.const 2).mul ((hn.mul hb).add (Unary.const 4))).add (Unary.const 1))
      (by have := hb.poly; have := hn.poly; fun_prop)
      fun x => by have := Nat.log2_le_self (2 * ((gIn x).1.length * nb (hIn x) + 4)); omega
  have hF : PolyT formHom := PolyT.dedup (homB_polyT hh hn hmH hg.snd)
  exact encK_polyT hK hw hF

end Poly

/-! ### The facts on a formula that the Main Theorem needs -/

theorem allOccur_gen {N : ℕ} {F : Fml} (hF : ∀ i < N, ∃ C ∈ F, ∃ l ∈ C, l.1 = i) {φ : Sat3.CNF N}
    (hφ : toN φ = F.dedup) : SatM.AllOccur φ := by
  intro i
  obtain ⟨C, hC, l, hl, hli⟩ := hF i.val i.2
  rw [← List.mem_dedup, ← hφ, mem_toN] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  exact ⟨D, hD, l', hl', Fin.ext hli⟩

theorem two_le_length_gen {N : ℕ} {F : Fml} {C₀ C₁ : List (ℕ × Bool)} (h0 : C₀ ∈ F) (h1 : C₁ ∈ F) (hne : C₀ ≠ C₁)
    {φ : Sat3.CNF N} (hφ : toN φ = F.dedup) : 2 ≤ φ.length := by
  have hl : φ.length = F.dedup.length := by rw [← hφ, toN, List.length_map]
  rw [hl]
  rw [← List.mem_dedup] at h0 h1
  have hsub : ({C₀, C₁} : Finset (List (ℕ × Bool))) ⊆ F.dedup.toFinset := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rw [List.mem_toFinset]; rcases hC with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_dedup _)] at this
  exact this

theorem isKCNF_gen {N K : ℕ} {F : Fml} (hw : ∀ C ∈ F, C.length ≤ K) {φ : Sat3.CNF N} (hφ : toN φ = F.dedup) :
    SatK.IsKCNF K φ := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have hm : D.map (fun l => (l.1.val, l.2)) ∈ toN φ := mem_toN.2 ⟨D, hD, rfl⟩
    rw [hφ, List.mem_dedup] at hm
    simpa using hw _ hm
  · have h : (toN φ).Nodup := by rw [hφ]; exact List.nodup_dedup _
    exact List.Nodup.of_map _ h

/-! ### The facts on the formula -/

theorem homB_var_lt (h n : ℕ) (mH m : List Bool) : ∀ C ∈ homB h n mH m, ∀ l ∈ C, l.1 < n * nb h + 4 := by
  intro C hC l hl
  simp only [homB, forbid, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hC
  rcases hC with ((⟨v, hv, c, -, rfl⟩ | ⟨p, ⟨hp, -⟩, q, -, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact idx_lt' hv (List.mem_range.1 hj)
  · have hp' := GraphProblems.Color.mem_pairs.1 hp
    rcases List.mem_append.1 hl with hl | hl <;> obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    · exact idx_lt' hp'.1 (List.mem_range.1 hj)
    · exact idx_lt' hp'.2 (List.mem_range.1 hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp only <;> omega
  · rw [List.mem_singleton] at hl; subst hl; simp only; omega

theorem homB_width {h : ℕ} (hh : 2 ≤ h) (n : ℕ) (mH m : List Bool) : ∀ C ∈ homB h n mH m, C.length ≤ 2 * nb h := by
  have hb := one_le_nb hh
  intro C hC
  simp only [homB, forbid, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hC
  rcases hC with ((⟨v, hv, c, -, rfl⟩ | ⟨p, -, q, -, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega

theorem mem_homB_taut (h n : ℕ) (mH m : List Bool) {i : ℕ} (hi : i < n * nb h) :
    [(i, true), (i, false)] ∈ homB h n mH m := by
  simp only [homB, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨i, hi, rfl⟩)

theorem mem_homB_unit (h n : ℕ) (mH m : List Bool) {i : ℕ} (hi : i < 4) : [(n * nb h + i, true)] ∈ homB h n mH m := by
  simp only [homB, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨i, hi, rfl⟩

theorem homB_occ (h n : ℕ) (mH m : List Bool) : ∀ i < n * nb h + 4, ∃ C ∈ homB h n mH m, ∃ l ∈ C, l.1 = i := by
  intro i hi
  by_cases hi' : i < n * nb h
  · exact ⟨_, mem_homB_taut h n mH m hi', (i, true), by simp, rfl⟩
  · exact ⟨_, mem_homB_unit h n mH m (show i - n * nb h < 4 by omega), _, List.mem_singleton.2 rfl,
      by simp only; omega⟩

theorem numSat_homB {h : ℕ} (hh : 2 ≤ h) {n : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool)
    {φ : Sat3.CNF (n * nb h + 4)} (hφ : toN φ = (homB h n (hmat H) (matrix G)).dedup) : SatK.numSat φ = numHom G H := by
  rw [← stCntToN, hφ, ← cntN_homB hh G H]
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]

theorem length_homB_le (h n : ℕ) (mH m : List Bool) :
    (homB h n mH m).length ≤ n * (2 * h) + n * n * (h * h) + n * nb h + 4 := by
  simp only [homB, List.length_append]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_
  · refine (length_flatMap_le _ _ (2 * h) fun v _ => ?_).trans (by simp)
    rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
  · refine (length_flatMap_le _ _ (h * h) fun p _ => ?_).trans ?_
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp [GraphProblems.pairs, List.length_product])
    · exact Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (by simp [GraphProblems.pairs, List.length_product]))
  · simp
  · simp

theorem length_input {n h : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool) :
    (unary h ++ (hmat H ++ code G)).length = h + 1 + (h * h + (n + 1 + n * n)) := by
  simp [unary, code, stMatrixLength n G, length_hmat]; omega

/-! ### The theorems -/

/-- **Counting homomorphisms, uniformly in the target.** One Turing machine and one constant c: for
all 2 ≤ h ≤ n, every graph G on n vertices and every relation H on Fin h (loops allowed), given h in
unary, the matrix of H and G, it outputs the number of homomorphisms from G to H within
c·2^{c·(2b)²·(n·b)·r(n·b)} steps, b = ⌈log₂ h⌉, r(N) = lg lg(N+4)/√lg(N+4). -/
theorem hom_uniform : ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n h : ℕ) (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool), 2 ≤ h → h ≤ n →
      Wrap.Outputs M (unary h ++ (hmat H ++ code G)) (Nat.bits (numHom G H))
        (SatM.boundNK (SatK.rN 1 (1 / 2)) c (2 * nb h) (n * nb h)) := by
  obtain ⟨M₀, C, hfin, hM⟩ := compact
  obtain ⟨M, q, hfinM, hW⟩ := Wrap.everyMachineCanBeWrapped M₀ hfin preHom Groundwork.PolyT.bitsTrim preHom_polyT
    (Groundwork.PolyT.bitsTrim' PolyT.id')
  obtain ⟨c, hc⟩ := wrapped_time_le_rateK q C C 1000 7
  refine ⟨M, c, hfinM, fun n h G H hh hhn => ?_⟩
  have hb := one_le_nb hh
  obtain ⟨hhx, hmx, hgx⟩ := read_input G H
  obtain ⟨φ, hφ⟩ := GraphProblems.exists_toN (N := n * nb h + 4) (ψ := (homB h n (hmat H) (matrix G)).dedup)
    (fun C hC l hl => homB_var_lt h n (hmat H) (matrix G) C (List.mem_dedup.1 hC) l hl)
  have hocc := VariableBound.Rename.allOccurStmt _ φ (allOccur_gen (homB_occ h n (hmat H) (matrix G)) hφ)
  have hpre : preHom (unary h ++ (hmat H ++ code G)) = MainTheoremForms.encC (2 * nb h) φ := by
    rw [preHom, formHom, hhx, hmx, hgx]
    simp only [List.length_replicate]
    rw [← hφ, encK_toN]
  have h2 : 2 ≤ φ.length := two_le_length_gen (mem_homB_unit h n (hmat H) (matrix G) (show 0 < 4 by omega))
    (mem_homB_unit h n (hmat H) (matrix G) (show 1 < 4 by omega)) (by simp) hφ
  have hrun := hM (2 * nb h) (n * nb h + 4) φ (by omega) (isKCNF_gen (homB_width hh n (hmat H) (matrix G)) hφ) h2
    (by rw [hocc.1]; omega)
  have hcnt : SatK.numSat φ = numHom G H := numSat_homB hh G H hφ
  have hlt : numHom G H < 2 ^ (n * nb h + 4 + 1) := by
    have h1 : SatK.numSat φ ≤ 2 ^ (n * nb h + 4) := (Finset.card_filter_le _ _).trans (by simp)
    have h2 : 2 ^ (n * nb h + 4) < 2 ^ (n * nb h + 4 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  unfold MainTheoremForms.CountsOccWithinC at hrun
  rw [hocc.1, hocc.2, hcnt] at hrun
  have hout := hW (unary h ++ (hmat H ++ code G)) _ _ (by rw [hpre]; exact hrun)
  rw [bitsTrim_binary hlt] at hout
  refine Wrap.Outputs.mono hout ?_
  -- the polynomial parts
  obtain ⟨s, hs⟩ : ∃ s, s = n * nb h + 2 := ⟨_, rfl⟩
  have hN1 : 1 ≤ n * nb h := Nat.mul_pos (by omega) hb
  have hns : n ≤ n * nb h := Nat.le_mul_of_pos_right n hb
  have hbs : nb h ≤ n * nb h := Nat.le_mul_of_pos_left (nb h) (by omega)
  have hb' : nb h ≤ s := by omega
  have hw : Nat.log2 (2 * (n * nb h + 4)) + 1 ≤ 7 * s := by
    have := Nat.log2_le_self (2 * (n * nb h + 4)); omega
  have hs2 : 2 ≤ s := by omega
  have hn' : n ≤ s := by omega
  have hh' : h ≤ s := by omega
  have p2' : s ^ 2 ≤ s ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : φ.length ≤ 8 * s ^ 4 := by
    have h1 : φ.length = (homB h n (hmat H) (matrix G)).dedup.length := by rw [← hφ, toN, List.length_map]
    have h2 := (List.dedup_sublist (homB h n (hmat H) (matrix G))).length_le
    have h3 := length_homB_le h n (hmat H) (matrix G)
    have p1 : n * (2 * h) ≤ 2 * s ^ 2 := by
      calc n * (2 * h) ≤ s * (2 * s) := Nat.mul_le_mul hn' (by omega)
        _ = 2 * s ^ 2 := by ring
    have p2 : n * n * (h * h) ≤ s ^ 4 := by
      calc n * n * (h * h) ≤ s * s * (s * s) := Nat.mul_le_mul (Nat.mul_le_mul hn' hn') (Nat.mul_le_mul hh' hh')
        _ = s ^ 4 := by ring
    have p3 : n * nb h ≤ s ^ 2 := by
      calc n * nb h ≤ s * s := Nat.mul_le_mul hn' hb'
        _ = s ^ 2 := by ring
    have p4 : 4 ≤ s ^ 2 := by
      calc 4 = 2 * 2 := rfl
        _ ≤ s * s := Nat.mul_le_mul hs2 hs2
        _ = s ^ 2 := by ring
    omega
  have q0 : 1 ≤ s ^ 7 := Nat.one_le_pow _ _ (by omega)
  have q1 : s ≤ s ^ 7 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q2 : s ^ 2 ≤ s ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have q6 : s ^ 6 ≤ s ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hL : (MainTheoremForms.encC (2 * nb h) φ).length ≤ 1000 * (n * nb h + 2) ^ 7 := by
    rw [Wrap.length_encC, ← hs]
    have hb2 : 2 * nb h ≤ 2 * s := by omega
    have e : 8 * s ^ 4 * (2 * s * (7 * s)) = 112 * s ^ 6 := by ring
    calc 2 * nb h + (Nat.log2 (2 * (n * nb h + 4)) + 1) + 2 + φ.length * (2 * nb h * (Nat.log2 (2 * (n * nb h + 4)) + 1))
        ≤ 2 * s + 7 * s + 2 + 8 * s ^ 4 * (2 * s * (7 * s)) := by gcongr
      _ ≤ 1000 * s ^ 7 := by omega
  have hX : (unary h ++ (hmat H ++ code G)).length ≤ 1000 * (n * nb h + 2) ^ 7 := by
    rw [length_input, ← hs]
    have e : s * s = s ^ 2 := by ring
    calc h + 1 + (h * h + (n + 1 + n * n)) ≤ s + 1 + (s * s + (s + 1 + s * s)) := by gcongr
      _ ≤ 1000 * s ^ 7 := by omega
  exact hc (2 * nb h) (n * nb h) φ.length (n * nb h + 4) _ _ (by omega) hN1 (by omega) le_rfl hL hX

/-- **Counting homomorphisms in 2^{o(n)}, uniformly for |V(H)| ≤ 2^{(lg n)^{1/6−θ}}.** One Turing
machine: for every θ ∈ (0, 1/6) and ε > 0 there is n₀ such that for all n ≥ n₀, all h ≥ 2 with
lg h ≤ (lg n)^{1/6−θ}, every graph G on n vertices and every relation H on Fin h, given h in unary,
the matrix of H and G, it outputs the number of homomorphisms from G to H within 2^{εn} steps. -/
theorem hom_subexp : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ θ ε : ℝ, 0 < θ → θ < 1 / 6 → 0 < ε → ∃ n₀ : ℕ, ∀ (n h : ℕ) (G : SimpleGraph (Fin n))
      (H : Fin h → Fin h → Bool), n₀ ≤ n → 2 ≤ h → Real.logb 2 h ≤ Real.logb 2 n ^ (1 / 6 - θ) →
        Wrap.Outputs M (unary h ++ (hmat H ++ code G)) (Nat.bits (numHom G H)) ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, c, hfin, hM⟩ := hom_uniform
  refine ⟨M, hfin, fun θ ε hθ hθ6 hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := boundNK_le c hθ hθ6 hε
  refine ⟨n₀ + 2, fun n h G H hn hh hhL => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hL1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hn2
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hhn : h ≤ n := by
    have h1 : Real.logb 2 n ^ (1 / 6 - θ) ≤ Real.logb 2 n := by
      calc Real.logb 2 n ^ (1 / 6 - θ) ≤ Real.logb 2 n ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        _ = Real.logb 2 n := Real.rpow_one _
    have h2 := (Real.logb_le_logb one_lt_two hh0 (by linarith)).1 (hhL.trans h1)
    exact_mod_cast h2
  have hb : (nb h : ℝ) ≤ 2 * Real.logb 2 n ^ (1 / 6 - θ) := by
    have h2 : (2 : ℝ) ^ (nb h : ℝ) ≤ 2 * h := by
      rw [Real.rpow_natCast]; exact_mod_cast two_pow_nb_le hh
    have h3 := (Real.le_logb_iff_rpow_le one_lt_two (by positivity : (0 : ℝ) < 2 * h)).2 h2
    rw [Real.logb_mul (by norm_num) hh0.ne', Real.logb_self_eq_one one_lt_two] at h3
    have h4 : 1 ≤ Real.logb 2 n ^ (1 / 6 - θ) := Real.one_le_rpow hL1 (by linarith)
    linarith
  refine Wrap.Outputs.mono (hM n h G H hh hhn) (Nat.floor_le_floor ?_)
  exact hn₀ n (nb h) (by omega) (one_le_nb hh) hb

open Classical in
/-- The same for a simple graph H, counting Mathlib's homomorphisms `G →g H`. -/
theorem hom_subexp_graph : ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ θ ε : ℝ, 0 < θ → θ < 1 / 6 → 0 < ε → ∃ n₀ : ℕ, ∀ (n h : ℕ) (G : SimpleGraph (Fin n))
      (H : SimpleGraph (Fin h)), n₀ ≤ n → 2 ≤ h → Real.logb 2 h ≤ Real.logb 2 n ^ (1 / 6 - θ) →
        Wrap.Outputs M (unary h ++ (hmat (fun a c => decide (H.Adj a c)) ++ code G))
          (Nat.bits (Nat.card (G →g H))) ⌊(2 : ℝ) ^ (ε * n)⌋₊ := by
  obtain ⟨M, hfin, hM⟩ := hom_subexp
  refine ⟨M, hfin, fun θ ε hθ hθ6 hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hM θ ε hθ hθ6 hε
  refine ⟨n₀, fun n h G H hn hh hhL => ?_⟩
  rw [← numHom_simple]
  exact hn₀ n h G _ hn hh hhL

end EthCor.Hom
