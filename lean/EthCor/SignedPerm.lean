import EthCor.Perm

/-! # The permanent of a {−1, 0, 1} matrix by two sized counts

A matrix with entries in {−1, 0, 1} is given by two 0/1 matrices: A (the entry is nonzero) and Sg (the
entry is −1). The variables are those of `permF` on the m nonzero entries, then z = x_m, the parities
p_k = x_{m+1+k} and their complements q_k = x_{m+1+r+k}, r the number of −1 entries (`negs`). The
clauses of `chainF` say z = 0, p_k = p_{k−1} ⊕ x_{g k} (width 3, `xorC`, with p_{−1} = z),
q_k = ¬p_k and p_{r−1} = b. The chain bits are determined by the entry bits (`chain_det`), and every pair
(p_k, q_k) has exactly one true bit. So the solutions of `sF` with n + r true variables are the
permutations along nonzero entries with an even (b = 0) resp. odd (b = 1) number of −1 entries
(`cnt_sperm`), and the permanent is the difference of the two counts (`permanent_signed`). -/

namespace EthCor.SPerm

open Groundwork Groundwork.Prog CountKSat GraphProblems Finset EthCor.Perm

/-- c = a ⊕ x. -/
def xorC (c a x : ℕ) : Fml :=
  [[(c, false), (a, true), (x, true)], [(c, false), (a, false), (x, false)],
    [(c, true), (a, false), (x, true)], [(c, true), (a, true), (x, false)]]

/-- q = ¬p. -/
def compC (p q : ℕ) : Fml := [[(p, true), (q, true)], [(p, false), (q, false)]]

/-- The parity chain over the entries g 0, …, g (r−1), with last parity b. -/
def chainF (m : ℕ) (g : List ℕ) (b : Bool) : Fml :=
  [[(m, false)]] ++ ((List.range g.length).flatMap fun k => xorC (m + 1 + k) (m + k) (g.getD k 0)) ++
    ((List.range g.length).flatMap fun k => compC (m + 1 + k) (m + 1 + g.length + k)) ++
      [[(m + g.length, b)]]

/-- No two chosen entries in a row or column, and the parity of the chosen −1 entries is b. -/
def sF (E : List (ℕ × ℕ)) (g : List ℕ) (b : Bool) : Fml := permF E ++ chainF E.length g b

/-- The indices of the entries of E that are −1 in Sg. -/
def negs (n : ℕ) (mS : List Bool) (E : List (ℕ × ℕ)) : List ℕ :=
  (List.range E.length).filter fun t => adjB n mS (E.getD t (0, 0)).1 (E.getD t (0, 0)).2

/-- The parities along the chain. -/
def chainVal (f : ℕ → Bool) (g : List ℕ) : ℕ → Bool
  | 0 => false
  | k + 1 => xor (chainVal f g k) (f (g.getD k 0))

/-! ### What the clauses say -/

theorem ex2 (f : ℕ → Bool) (p q : ℕ) (b₁ b₂ : Bool) :
    (∃ l ∈ [(p, b₁), (q, b₂)], f l.1 = l.2) ↔ f p = b₁ ∨ f q = b₂ := by
  constructor
  · rintro ⟨l, hl, h⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨(p, b₁), by simp, h⟩
    · exact ⟨(q, b₂), by simp, h⟩

theorem ex3 (f : ℕ → Bool) (p q r : ℕ) (b₁ b₂ b₃ : Bool) :
    (∃ l ∈ [(p, b₁), (q, b₂), (r, b₃)], f l.1 = l.2) ↔ f p = b₁ ∨ f q = b₂ ∨ f r = b₃ := by
  constructor
  · rintro ⟨l, hl, h⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨(p, b₁), by simp, h⟩
    · exact ⟨(q, b₂), by simp, h⟩
    · exact ⟨(r, b₃), by simp, h⟩

theorem sat_xorC (f : ℕ → Bool) (c a x : ℕ) :
    (∀ C ∈ xorC c a x, ∃ l ∈ C, f l.1 = l.2) ↔ f c = xor (f a) (f x) := by
  simp only [xorC, List.forall_mem_cons, ex3]
  cases f c <;> cases f a <;> cases f x <;> simp

theorem sat_compC (f : ℕ → Bool) (p q : ℕ) : (∀ C ∈ compC p q, ∃ l ∈ C, f l.1 = l.2) ↔ f q = !f p := by
  simp only [compC, List.forall_mem_cons, ex2]
  cases f p <;> cases f q <;> simp

theorem sat_chainF (f : ℕ → Bool) (m : ℕ) (g : List ℕ) (b : Bool) :
    (∀ C ∈ chainF m g b, ∃ l ∈ C, f l.1 = l.2) ↔
      f m = false ∧ (∀ k < g.length, f (m + 1 + k) = xor (f (m + k)) (f (g.getD k 0))) ∧
        (∀ k < g.length, f (m + 1 + g.length + k) = !f (m + 1 + k)) ∧ f (m + g.length) = b := by
  simp only [chainF, List.forall_mem_append, List.forall_mem_flatMap, List.mem_range, sat_xorC, sat_compC,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.mem_singleton, exists_eq_left, and_assoc]

theorem sat_congr {F : Fml} {N : ℕ} (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < N) {f f' : ℕ → Bool} (h : ∀ v < N, f v = f' v) :
    (∀ C ∈ F, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ C ∈ F, ∃ l ∈ C, f' l.1 = l.2 := by
  constructor
  · intro hs C hC
    obtain ⟨l, hl, e⟩ := hs C hC
    exact ⟨l, hl, (h _ (hF C hC l hl)) ▸ e⟩
  · intro hs C hC
    obtain ⟨l, hl, e⟩ := hs C hC
    exact ⟨l, hl, (h _ (hF C hC l hl)).symm ▸ e⟩

/-! ### The chain -/

theorem chain_det (f : ℕ → Bool) (m : ℕ) (g : List ℕ) (h0 : f m = false)
    (hs : ∀ k < g.length, f (m + 1 + k) = xor (f (m + k)) (f (g.getD k 0))) :
    ∀ k ≤ g.length, f (m + k) = chainVal f g k
  | 0, _ => by simpa [chainVal] using h0
  | k + 1, hk => by
    rw [chainVal, ← chain_det f m g h0 hs k (by omega), show m + (k + 1) = m + 1 + k by omega]
    exact hs k (by omega)

theorem chainVal_congr {f f' : ℕ → Bool} (g : List ℕ) :
    ∀ k, (∀ i < k, f (g.getD i 0) = f' (g.getD i 0)) → chainVal f g k = chainVal f' g k
  | 0, _ => rfl
  | k + 1, h => by
    rw [chainVal, chainVal, chainVal_congr g k fun i hi => h i (by omega), h k (by omega)]

theorem chainVal_eq (f : ℕ → Bool) (g : List ℕ) :
    ∀ k, chainVal f g k = decide (Odd ((range k).filter fun i => f (g.getD i 0) = true).card)
  | 0 => by simp [chainVal]
  | k + 1 => by
    rw [chainVal, chainVal_eq f g k, range_add_one, filter_insert]
    by_cases h : f (g.getD k 0) = true
    · rw [if_pos h, card_insert_of_notMem (by simp)]
      simp only [h, Bool.xor_true, Nat.odd_add_one, decide_not]
    · rw [if_neg h]
      simp only [Bool.not_eq_true] at h
      rw [h, Bool.xor_false]

/-! ### Counting true variables -/

theorem card_true_eq {N : ℕ} (a : Fin N → Bool) :
    (univ.filter fun i => a i = true).card = ∑ v ∈ range N, if ext a v = true then 1 else 0 := by
  rw [card_filter, ← Fin.sum_univ_eq_sum_range (fun v => if ext a v = true then 1 else 0) N]
  refine sum_congr rfl fun i _ => ?_
  rw [ext_val']

theorem card_true_split {m r : ℕ} (a : Fin (m + 1 + r + r) → Bool) (h0 : ext a m = false)
    (hq : ∀ k < r, ext a (m + 1 + r + k) = !ext a (m + 1 + k)) :
    (univ.filter fun i => a i = true).card = (∑ v ∈ range m, if ext a v = true then 1 else 0) + r := by
  rw [card_true_eq, sum_range_add, sum_range_add, sum_range_succ, h0]
  have : ∑ k ∈ range r, ((if ext a (m + 1 + k) = true then 1 else 0) + if ext a (m + 1 + r + k) = true then 1 else 0) =
      ∑ k ∈ range r, 1 := by
    refine sum_congr rfl fun k hk => ?_
    rw [hq k (mem_range.1 hk)]
    cases ext a (m + 1 + k) <;> rfl
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at this
  simp only [Bool.false_eq_true, if_false, add_zero]
  omega

/-! ### The count of the formula -/

section Gen

variable (E : List (ℕ × ℕ)) (g : List ℕ) (b : Bool)

local notation "N" => E.length + 1 + g.length + g.length

/-- The entry bits of an assignment of all variables. -/
def res (a : Fin (E.length + 1 + g.length + g.length) → Bool) (t : Fin E.length) : Bool := a (Fin.castLE (by omega) t)

theorem ext_res (a : Fin (E.length + 1 + g.length + g.length) → Bool) {v : ℕ} (hv : v < E.length) :
    ext (res E g a) v = ext a v := by
  rw [CountKSat.ext, dif_pos hv, CountKSat.ext, dif_pos (by omega)]
  rfl

/-- The assignment of all variables that an assignment of the entry bits determines. -/
def fullF (f : ℕ → Bool) (v : ℕ) : Bool :=
  if v < E.length then f v else if v ≤ E.length + g.length then chainVal f g (v - E.length)
  else !chainVal f g (v - E.length - g.length)

def full (x : Fin E.length → Bool) (v : Fin (E.length + 1 + g.length + g.length)) : Bool := fullF E g (ext x) v

theorem ext_full (x : Fin E.length → Bool) {v : ℕ} (hv : v < E.length + 1 + g.length + g.length) :
    ext (full E g x) v = fullF E g (ext x) v := by
  rw [CountKSat.ext, dif_pos hv]
  rfl

theorem permF_var_lt : ∀ C ∈ permF E, ∀ l ∈ C, l.1 < E.length := fun C hC => (shaped_permF E C hC).2

theorem cnt_sF (hg : ∀ k < g.length, g.getD k 0 < E.length) (n : ℕ) :
    cntS (E.length + 1 + g.length + g.length) (n + g.length) (sF E g b) =
      (univ.filter fun x : Fin E.length → Bool =>
        ((∀ C ∈ permF E, ∃ l ∈ C, ext x l.1 = l.2) ∧ (univ.filter fun i => x i = true).card = n) ∧
          chainVal (ext x) g g.length = b).card := by
  unfold cntS
  -- agreement below m
  have hagree : ∀ a : Fin (E.length + 1 + g.length + g.length) → Bool, ∀ v < E.length, ext a v = ext (res E g a) v :=
    fun a v hv => (ext_res E g a hv).symm
  have hchain : ∀ a : Fin (E.length + 1 + g.length + g.length) → Bool, ∀ k ≤ g.length,
      chainVal (ext a) g k = chainVal (ext (res E g a)) g k :=
    fun a k hk => chainVal_congr g k fun i hi => hagree a _ (hg i (by omega))
  refine card_bij (fun a _ => res E g a) (fun a ha => ?_) (fun a ha a' ha' h => ?_) (fun x hx => ?_)
  · obtain ⟨hsat, hcard⟩ := (mem_filter.1 ha).2
    rw [sF, List.forall_mem_append, sat_chainF] at hsat
    obtain ⟨hp, h0, hs, hq, hb⟩ := hsat
    refine mem_filter.2 ⟨mem_univ _, ⟨(sat_congr (permF_var_lt E) (hagree a)).1 hp, ?_⟩, ?_⟩
    · rw [card_true_split a h0 hq] at hcard
      have hsum : (∑ v ∈ range E.length, if ext a v = true then 1 else 0) =
          ∑ v ∈ range E.length, if ext (res E g a) v = true then 1 else 0 :=
        sum_congr rfl fun v hv => by rw [hagree a v (mem_range.1 hv)]
      rw [card_true_eq]
      omega
    · rw [← hchain a _ le_rfl, ← chain_det (ext a) E.length g h0 hs _ le_rfl, hb]
  · obtain ⟨hsat, -⟩ := (mem_filter.1 ha).2
    obtain ⟨hsat', -⟩ := (mem_filter.1 ha').2
    rw [sF, List.forall_mem_append, sat_chainF] at hsat hsat'
    obtain ⟨-, h0, hs, hq, -⟩ := hsat
    obtain ⟨-, h0', hs', hq', -⟩ := hsat'
    have hlow : ∀ v < E.length, ext a v = ext a' v := fun v hv => by rw [hagree a v hv, hagree a' v hv, h]
    have hc : ∀ k ≤ g.length, ext a (E.length + k) = ext a' (E.length + k) := fun k hk => by
      rw [chain_det _ _ g h0 hs k hk, chain_det _ _ g h0' hs' k hk, hchain a k hk, hchain a' k hk, h]
    funext v
    rw [← ext_val' a v, ← ext_val' a' v]
    have hv := v.2
    by_cases h1 : v.val < E.length
    · exact hlow _ h1
    · by_cases h2 : v.val ≤ E.length + g.length
      · have := hc (v.val - E.length) (by omega)
        rwa [show E.length + (v.val - E.length) = v.val by omega] at this
      · obtain ⟨k, hk⟩ : ∃ k, v.val = E.length + 1 + g.length + k := ⟨v.val - (E.length + 1 + g.length), by omega⟩
        rw [hk, hq k (by omega), hq' k (by omega)]
        have := hc (k + 1) (by omega)
        rw [show E.length + (k + 1) = E.length + 1 + k by omega] at this
        rw [this]
  · obtain ⟨⟨hp, hcard⟩, hb⟩ := (mem_filter.1 hx).2
    have hfx : ∀ v < E.length, ext (full E g x) v = ext x v := fun v hv => by
      rw [ext_full E g x (by omega), fullF, if_pos hv]
    have hcx : ∀ k ≤ g.length, chainVal (ext (full E g x)) g k = chainVal (ext x) g k :=
      fun k hk => chainVal_congr g k fun i hi => hfx _ (hg i (by omega))
    have hmid : ∀ k ≤ g.length, ext (full E g x) (E.length + k) = chainVal (ext x) g k := fun k hk => by
      rw [ext_full E g x (by omega), fullF, if_neg (by omega), if_pos (by omega), show E.length + k - E.length = k by omega]
    have h0 : ext (full E g x) E.length = false := by simpa [chainVal] using hmid 0 (Nat.zero_le _)
    have hq : ∀ k < g.length, ext (full E g x) (E.length + 1 + g.length + k) = !ext (full E g x) (E.length + 1 + k) := by
      intro k hk
      rw [ext_full E g x (by omega), fullF, if_neg (by omega), if_neg (by omega),
        show E.length + 1 + k = E.length + (k + 1) by omega, hmid (k + 1) (by omega),
        show E.length + 1 + g.length + k - E.length - g.length = k + 1 by omega]
    have hres : res E g (full E g x) = x := by
      funext t
      rw [← ext_val' (res E g (full E g x)) t, ext_res E g _ t.2, hfx _ t.2, ext_val']
    refine ⟨full E g x, mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, hres⟩
    · rw [sF, List.forall_mem_append, sat_chainF]
      refine ⟨(sat_congr (permF_var_lt E) hfx).2 hp, h0, fun k hk => ?_, hq, ?_⟩
      · rw [show E.length + 1 + k = E.length + (k + 1) by omega, hmid (k + 1) (by omega), hmid k (by omega),
          hfx _ (hg k hk), chainVal]
      · rw [hmid _ le_rfl, hb]
    · rw [card_true_split _ h0 hq, ← hcard, card_true_eq x]
      congr 1
      exact sum_congr rfl fun v hv => by rw [hfx v (mem_range.1 hv)]

end Gen

/-! ### Back to permutations -/

section Perm

variable {n : ℕ} (A Sg : Fin n → Fin n → Bool)

/-- The permutations along nonzero entries with an even (b = false) or odd (b = true) number of −1 entries. -/
noncomputable def numPar (b : Bool) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) =>
    (∀ i, A (σ i) i = true) ∧ decide (Odd (univ.filter fun i => Sg (σ i) i = true).card) = b).card

theorem negs_lt : ∀ k < (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length,
    (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).getD k 0 < (ents n (Hom.hmat A)).length := by
  intro k hk
  rw [List.getD_eq_getElem _ _ hk]
  exact List.mem_range.1 (List.mem_of_mem_filter (List.getElem_mem hk))

theorem neg_iff (t : Fin (ents n (Hom.hmat A)).length) :
    adjB n (Hom.hmat Sg) ((ents n (Hom.hmat A)).getD t (0, 0)).1 ((ents n (Hom.hmat A)).getD t (0, 0)).2 =
      Sg (row A t) (col A t) := by
  rw [List.getD_eq_getElem _ _ t.2]
  exact Hom.adjB_hmat Sg (row A t) (col A t)

/-- The chosen −1 entries of a permutation are its columns with Sg (σ i) i. -/
theorem card_negs (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, A (σ i) i = true) :
    ((range (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length).filter fun k =>
      ext (asg A σ) ((negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).getD k 0) = true).card =
      (univ.filter fun i => Sg (σ i) i = true).card := by
  classical
  have hnd : (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).Nodup := List.nodup_range.filter _
  refine card_bij (fun k hk => col A ⟨_, negs_lt A Sg k (mem_range.1 (mem_filter.1 hk).1)⟩)
    (fun k hk => ?_) (fun k hk k' hk' h => ?_) (fun i hi => ?_)
  · obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
    have hk1' := mem_range.1 hk1
    have hm : (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).getD k 0 ∈ negs n (Hom.hmat Sg) (ents n (Hom.hmat A)) := by
      rw [List.getD_eq_getElem _ _ hk1']; exact List.getElem_mem hk1'
    have hneg := (List.mem_filter.1 hm).2
    rw [neg_iff A Sg ⟨_, negs_lt A Sg k hk1'⟩] at hneg
    rw [ext_val' (asg A σ) ⟨_, negs_lt A Sg k hk1'⟩] at hk2
    simp only [asg, decide_eq_true_eq] at hk2
    rw [hk2] at hneg
    exact mem_filter.2 ⟨mem_univ _, hneg⟩
  · obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
    obtain ⟨hk1', hk2'⟩ := mem_filter.1 hk'
    rw [ext_val' (asg A σ) ⟨_, negs_lt A Sg k (mem_range.1 hk1)⟩] at hk2
    rw [ext_val' (asg A σ) ⟨_, negs_lt A Sg k' (mem_range.1 hk1')⟩] at hk2'
    simp only [asg, decide_eq_true_eq] at hk2 hk2'
    have e := idx_eq A (by rw [hk2, hk2', h]) h
    have e' := congrArg Fin.val e
    simp only at e'
    rw [List.getD_eq_getElem _ _ (mem_range.1 hk1), List.getD_eq_getElem _ _ (mem_range.1 hk1')] at e'
    exact (hnd.getElem_inj_iff.1 e')
  · obtain ⟨t, h1, h2⟩ := exists_idx A (hσ i)
    have hneg : t.val ∈ negs n (Hom.hmat Sg) (ents n (Hom.hmat A)) := by
      refine List.mem_filter.2 ⟨List.mem_range.2 t.2, ?_⟩
      rw [neg_iff A Sg t, h1, h2]
      exact (mem_filter.1 hi).2
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 hneg
    have hget : (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).getD k 0 = t.val := by
      rw [List.getD_eq_getElem _ _ hk, he]
    have ht : (⟨_, negs_lt A Sg k hk⟩ : Fin (ents n (Hom.hmat A)).length) = t := Fin.ext hget
    refine ⟨k, mem_filter.2 ⟨mem_range.2 hk, ?_⟩, ?_⟩
    · rw [ext_val' (asg A σ) ⟨_, negs_lt A Sg k hk⟩, ht]
      simp [asg, h1, h2]
    · rw [ht, h2]

/-- **The count of the formula is the number of permutations of parity b.** -/
theorem cnt_sperm (b : Bool) :
    cntS ((ents n (Hom.hmat A)).length + 1 + (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length +
        (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length)
      (n + (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length)
      (sF (ents n (Hom.hmat A)) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))) b) = numPar A Sg b := by
  classical
  rw [cnt_sF _ _ b (negs_lt A Sg) n,
    card_asg A (fun x => chainVal (ext x) (negs n (Hom.hmat Sg) (ents n (Hom.hmat A)))
      (negs n (Hom.hmat Sg) (ents n (Hom.hmat A))).length = b), numPar]
  congr 1
  refine filter_congr fun σ _ => ?_
  constructor
  · rintro ⟨hσ, hb⟩
    refine ⟨hσ, ?_⟩
    rw [chainVal_eq, card_negs A Sg σ hσ] at hb
    convert hb
  · rintro ⟨hσ, hb⟩
    refine ⟨hσ, ?_⟩
    rw [chainVal_eq, card_negs A Sg σ hσ]
    convert hb

/-- **The permanent of the {−1, 0, 1} matrix** is the even count minus the odd count. -/
theorem permanent_signed :
    (Matrix.of fun i j => if A i j then (if Sg i j then -1 else 1) else 0 : Matrix (Fin n) (Fin n) ℤ).permanent =
      (numPar A Sg false : ℤ) - numPar A Sg true := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (Matrix.of fun i j => if A i j then (if Sg i j then -1 else 1) else 0 : Matrix (Fin n) (Fin n) ℤ) (σ i) i) =
        if (∀ i, A (σ i) i = true) then
          (if Odd (univ.filter fun i => Sg (σ i) i = true).card then -1 else 1) else 0 := by
    intro σ
    simp only [Matrix.of_apply]
    by_cases hσ : ∀ i, A (σ i) i = true
    · rw [if_pos hσ]
      rw [prod_congr rfl fun i _ => if_pos (hσ i), prod_ite, prod_const, prod_const, one_pow, mul_one]
      rcases Nat.even_or_odd (univ.filter fun i => Sg (σ i) i = true).card with h | h
      · rw [h.neg_one_pow, if_neg (Nat.not_odd_iff_even.2 h)]
      · rw [h.neg_one_pow, if_pos h]
    · rw [if_neg hσ]
      push Not at hσ
      obtain ⟨i, hi⟩ := hσ
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  rw [Matrix.permanent, sum_congr rfl fun σ _ => hterm σ, sum_ite, sum_const_zero, add_zero, sum_ite,
    sum_const, sum_const, filter_filter, filter_filter, numPar, numPar]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, nsmul_eq_mul, mul_neg, mul_one]
  ring
end Perm

end EthCor.SPerm
