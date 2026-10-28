import EthCor.HomFormula
import Mathlib.LinearAlgebra.Matrix.Permanent

/-! # The permanent of a 0/1 matrix as a count of sized solutions of a 2-CNF

The variables are the m nonzero entries of A (`ents`, row by row). The clauses say that no two chosen
entries lie in the same row or the same column (`permF`, width 2). An assignment with exactly n true
variables then chooses one entry in every column, and the rows of these entries are distinct: it is
a permutation σ with A (σ i) i for all i (`cntS_permF`). Their number is Mathlib's
`Matrix.permanent` of A (`permanent_eq`). So Anthropic's `SIZED` counter computes the permanent
in c·2^{δm} steps, m the number of ones of A. -/

namespace EthCor.Perm

open Groundwork Groundwork.Prog CountKSat GraphProblems Finset

/-- The nonzero entries (row, column), row by row. -/
def ents (n : ℕ) (mA : List Bool) : List (ℕ × ℕ) := (pairs n).filter fun p => adjB n mA p.1 p.2

/-- Two entries in the same row or the same column. -/
def clash (p q : ℕ × ℕ) : Bool := decide (p.1 = q.1) || decide (p.2 = q.2)

/-- No two chosen entries in the same row or column. -/
def permF (E : List (ℕ × ℕ)) : Fml :=
  ((pairs E.length).filter fun ab => decide (ab.1 < ab.2) && clash (E.getD ab.1 (0, 0)) (E.getD ab.2 (0, 0))).map
    fun ab => [(ab.1, false), (ab.2, false)]

theorem clash_comm (p q : ℕ × ℕ) : clash p q = clash q p := by
  simp only [clash, eq_comm]

theorem nodup_ents (n : ℕ) (mA : List Bool) : (ents n mA).Nodup := by
  unfold ents GraphProblems.pairs
  exact (List.nodup_range.product List.nodup_range).filter _

theorem lt_of_mem_ents {n : ℕ} {mA : List Bool} {p : ℕ × ℕ} (h : p ∈ ents n mA) : p.1 < n ∧ p.2 < n :=
  GraphProblems.Color.mem_pairs.1 (List.mem_of_mem_filter h)

theorem mem_ents_fin {n : ℕ} (A : Fin n → Fin n → Bool) (i j : Fin n) :
    ((i : ℕ), (j : ℕ)) ∈ ents n (Hom.hmat A) ↔ A i j = true := by
  rw [ents, List.mem_filter, GraphProblems.Color.mem_pairs]
  simp only [Fin.is_lt, and_self, true_and]
  rw [Hom.adjB_hmat]

theorem length_permF_le (E : List (ℕ × ℕ)) : (permF E).length ≤ E.length * E.length := by
  rw [permF, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [GraphProblems.pairs, List.length_product])

theorem shaped_permF (E : List (ℕ × ℕ)) : Shaped 2 E.length (permF E) := by
  intro C hC
  simp only [permF, List.mem_map, List.mem_filter] at hC
  obtain ⟨ab, ⟨hab, -⟩, rfl⟩ := hC
  have h := GraphProblems.Color.mem_pairs.1 hab
  refine ⟨by simp, fun l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact h.1
  · exact h.2

/-! ### What the formula says -/

theorem sat_permF (E : List (ℕ × ℕ)) (a : Fin E.length → Bool) :
    (∀ C ∈ permF E, ∃ l ∈ C, ext a l.1 = l.2) ↔
      ∀ s t : Fin E.length, s ≠ t → a s = true → a t = true → clash E[s] E[t] = false := by
  simp only [permF, List.forall_mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, and_imp,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  constructor
  · intro h s t hst hs ht
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have key : ∀ s t : Fin E.length, s < t → a s = true → a t = true → clash E[s] E[t] = true → False := by
      intro s t hlt hs ht hc
      have h1 := h (s.val, t.val) (GraphProblems.Color.mem_pairs.2 ⟨s.2, t.2⟩) hlt
        (by rw [List.getD_eq_getElem _ _ s.2, List.getD_eq_getElem _ _ t.2]; exact hc)
      rw [ext_val' a s, ext_val' a t, hs, ht] at h1
      simp at h1
    rcases lt_or_gt_of_ne hst with hlt | hlt
    · exact key s t hlt hs ht hc
    · exact key t s hlt ht hs (by rw [clash_comm]; exact hc)
  · intro h ab hab hlt hc
    have h' := GraphProblems.Color.mem_pairs.1 hab
    rw [List.getD_eq_getElem _ _ h'.1, List.getD_eq_getElem _ _ h'.2] at hc
    have e := h ⟨ab.1, h'.1⟩ ⟨ab.2, h'.2⟩ (fun he => by have := congrArg Fin.val he; simp at this; omega)
    rw [ext_val' a ⟨ab.1, h'.1⟩, ext_val' a ⟨ab.2, h'.2⟩]
    cases h1 : a ⟨ab.1, h'.1⟩
    · exact Or.inl rfl
    · cases h2 : a ⟨ab.2, h'.2⟩
      · exact Or.inr rfl
      · exact absurd (e h1 h2) (by simp only [Fin.getElem_fin]; rw [hc]; simp)

/-! ### Counting -/

section Count

variable {n : ℕ} (A : Fin n → Fin n → Bool)

local notation "E" => ents n (Hom.hmat A)

/-- The row and the column of the entry t. -/
def row (t : Fin (ents n (Hom.hmat A)).length) : Fin n := ⟨E[t].1, (lt_of_mem_ents (List.getElem_mem t.2)).1⟩
def col (t : Fin (ents n (Hom.hmat A)).length) : Fin n := ⟨E[t].2, (lt_of_mem_ents (List.getElem_mem t.2)).2⟩

theorem get_eq (t : Fin (ents n (Hom.hmat A)).length) : E[t] = ((row A t : ℕ), (col A t : ℕ)) := rfl

theorem entry_true (t : Fin (ents n (Hom.hmat A)).length) : A (row A t) (col A t) = true :=
  (mem_ents_fin A _ _).1 (get_eq A t ▸ List.getElem_mem t.2)

theorem idx_eq {s t : Fin (ents n (Hom.hmat A)).length} (h1 : row A s = row A t) (h2 : col A s = col A t) : s = t := by
  have h : E[s] = E[t] := by rw [get_eq, get_eq, h1, h2]
  exact Fin.ext ((nodup_ents n _).getElem_inj_iff.1 h)

theorem exists_idx {i j : Fin n} (h : A i j = true) : ∃ t, row A t = i ∧ col A t = j := by
  obtain ⟨t, ht, he⟩ := List.mem_iff_getElem.1 ((mem_ents_fin A i j).2 h)
  refine ⟨⟨t, ht⟩, Fin.ext ?_, Fin.ext ?_⟩
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem clash_eq (s t : Fin (ents n (Hom.hmat A)).length) :
    clash E[s] E[t] = (decide (row A s = row A t) || decide (col A s = col A t)) := by
  rw [get_eq, get_eq, clash]
  simp only [Fin.val_inj]

/-- The assignment of a permutation: the entry t is chosen if its row is σ of its column. -/
def asg (σ : Equiv.Perm (Fin n)) (t : Fin (ents n (Hom.hmat A)).length) : Bool := decide (row A t = σ (col A t))

theorem asg_mem (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, A (σ i) i = true) :
    (∀ C ∈ permF E, ∃ l ∈ C, ext (asg A σ) l.1 = l.2) ∧
      (univ.filter fun t => asg A σ t = true).card = n := by
  refine ⟨(sat_permF _ _).2 fun s t hst hs ht => ?_, ?_⟩
  · simp only [asg, decide_eq_true_eq] at hs ht
    rw [clash_eq]
    by_contra hc
    simp only [Bool.not_eq_false, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with h | h
    · have hc' : col A s = col A t := σ.injective (hs.symm.trans (h.trans ht))
      exact hst (idx_eq A h hc')
    · exact hst (idx_eq A (by rw [hs, ht, h]) h)
  · have : (univ.filter fun t => asg A σ t = true).card = (univ : Finset (Fin n)).card := by
      refine card_bij (fun t _ => col A t) (fun _ _ => mem_univ _) (fun s hs t ht h => ?_) (fun j _ => ?_)
      · simp only [mem_filter, mem_univ, true_and, asg, decide_eq_true_eq] at hs ht
        exact idx_eq A (by rw [hs, ht, h]) h
      · obtain ⟨t, h1, h2⟩ := exists_idx A (hσ j)
        exact ⟨t, by simp [asg, h1, h2], h2⟩
    rw [this, card_univ, Fintype.card_fin]

/-- **The count is the number of permutations with A (σ i) i for all i.** -/
theorem cntS_permF : cntS (ents n (Hom.hmat A)).length n (permF (ents n (Hom.hmat A))) = (univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, A (σ i) i = true).card := by
  classical
  symm
  unfold cntS
  refine card_bij (fun σ _ => asg A σ) (fun σ hσ => ?_) (fun σ hσ τ hτ h => ?_) (fun a ha => ?_)
  · exact mem_filter.2 ⟨mem_univ _, asg_mem A σ (mem_filter.1 hσ).2⟩
  · ext j
    obtain ⟨t, h1, h2⟩ := exists_idx A ((mem_filter.1 hσ).2 j)
    have e : asg A σ t = asg A τ t := congrFun h t
    have e1 : asg A σ t = true := by simp [asg, h1, h2]
    rw [e1] at e
    have e2 : row A t = τ (col A t) := of_decide_eq_true e.symm
    rw [h1, h2] at e2
    exact congrArg Fin.val e2
  · obtain ⟨hsat, hcard⟩ := (mem_filter.1 ha).2
    have hno := (sat_permF _ _).1 hsat
    -- the chosen entries have distinct columns, so every column has one
    have hinj : ∀ s t, a s = true → a t = true → col A s = col A t → s = t := by
      intro s t hs ht h
      by_contra hst
      have := hno s t hst hs ht
      rw [clash_eq, h] at this
      simp at this
    have hsurj := surj_on_of_inj_on_of_card_le (s := univ.filter fun t => a t = true) (t := (univ : Finset (Fin n)))
      (fun t _ => col A t) (fun _ _ => mem_univ _)
      (fun s t hs ht h => hinj s t (mem_filter.1 hs).2 (mem_filter.1 ht).2 h)
      (by rw [card_univ, Fintype.card_fin, hcard])
    choose tc htc using fun j : Fin n => hsurj j (mem_univ _)
    have hta : ∀ j, a (tc j) = true := fun j => (mem_filter.1 (htc j).1).2
    have hcol : ∀ j, col A (tc j) = j := fun j => (htc j).2.symm
    have hfinj : Function.Injective fun j => row A (tc j) := by
      intro j j' h
      have e : tc j = tc j' := by
        by_contra hne
        have := hno _ _ hne (hta j) (hta j')
        rw [clash_eq] at this
        simp only [h, decide_true, Bool.true_or] at this
        exact absurd this (by decide)
      rw [← hcol j, ← hcol j', e]
    let σ := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hfinj)
    have hσ : ∀ j, σ j = row A (tc j) := fun j => rfl
    refine ⟨σ, mem_filter.2 ⟨mem_univ _, fun j => ?_⟩, ?_⟩
    · rw [hσ, ← entry_true A (tc j), hcol]
    · funext t
      simp only [asg, hσ]
      by_cases ht : a t = true
      · rw [ht, decide_eq_true_iff, hinj _ _ (hta (col A t)) ht (hcol _)]
      · rw [Bool.not_eq_true] at ht
        rw [ht, decide_eq_false_iff_not]
        intro h
        have e := idx_eq A h.symm (hcol (col A t))
        rw [← e, hta] at ht
        exact absurd ht (by decide)

end Count

/-- The permanent of the 0/1 matrix of A counts the permutations along ones. -/
theorem permanent_eq {n : ℕ} (A : Fin n → Fin n → Bool) :
    (Matrix.of fun i j => if A i j then 1 else 0 : Matrix (Fin n) (Fin n) ℕ).permanent =
      (univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, A (σ i) i = true).card := by
  rw [Matrix.permanent, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [prod_boole]
  simp

/-- The number of ones of A is the number of variables. -/
theorem length_ents {n : ℕ} (A : Fin n → Fin n → Bool) :
    (ents n (Hom.hmat A)).length = (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card := by
  rw [← List.toFinset_card_of_nodup (nodup_ents n _)]
  have h : (ents n (Hom.hmat A)).toFinset =
      (univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).image fun p => ((p.1 : ℕ), (p.2 : ℕ)) := by
    ext p
    simp only [List.mem_toFinset, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · intro hp
      obtain ⟨h1, h2⟩ := lt_of_mem_ents hp
      exact ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), (mem_ents_fin A ⟨p.1, h1⟩ ⟨p.2, h2⟩).1 hp, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact (mem_ents_fin A q.1 q.2).2 hq
  rw [h, card_image_of_injective]
  intro p q hpq
  simp only [Prod.mk.injEq] at hpq
  exact Prod.ext (Fin.ext hpq.1) (Fin.ext hpq.2)

end EthCor.Perm
