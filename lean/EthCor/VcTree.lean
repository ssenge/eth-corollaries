import GraphProblems.Defs
import GraphProblems.Interfaces
import StepMachines.Math.SparsifyTree
import SparsifyWidthK.Thresholds
import Mathlib.Tactic

/-! # Vertex cover: the branching tree

A node is a budget k and a list E of edges (pairs of numbers). It is *good* if some set of at most k
vertices meets every edge of E (`Good`). While k ≥ 1 and some vertex v has at least d distinct
neighbours (`nbs`), the node branches (`stepV`): either v is in the cover (budget k − 1, the edges at
v removed), or v is not, and then all its neighbours N are (budget k − |N|, the edges at v and N
removed; if |N| > k this child is (0, E), which is not good). A node is good exactly if one of its
children is (`good_step`), so the root is good exactly if some leaf is (`good_leaves`).

Along a path every step lowers the budget by 1 or by at least d. With p steps and t = d·(number of
second children), p ≤ k + d and t ≤ k + d (`inv_step`, `inv_bound`), so the tree has at most
Σ_{j ≤ (k+d)/d} C(k+d, j) leaves, which is at most 2^{ε(k+d)} once (1/d)·lg(e·d) ≤ ε (`leaves_le`).

At a leaf every vertex has fewer than d neighbours or the budget is 0. A good leaf then has at most
k·d vertices on its edges (`card_V_le`): each is in the cover or a neighbour of a cover vertex. The
leaf formula (`leafV`) renames these vertices to 0, …, |V| − 1 and has the clause x_u ∨ x_v for every
edge; it has a satisfying assignment with min(k, |V|) true variables exactly if the leaf is good
(`cnt_leafV_pos`). A leaf with more than k·d vertices gets the formula with one empty clause on no
variables. -/

namespace EthCor.Vc

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems

/-- A node: the budget and the edges still to be met. -/
abbrev VNode := ℕ × List (ℕ × ℕ)

/-- X meets every edge of E. -/
def Covers (X : Finset ℕ) (E : List (ℕ × ℕ)) : Prop := ∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ X

/-- Some set of at most k vertices meets every edge. -/
def Good (x : VNode) : Prop := ∃ X : Finset ℕ, X.card ≤ x.1 ∧ Covers X x.2

/-- The distinct neighbours of v. -/
def nbs (E : List (ℕ × ℕ)) (v : ℕ) : List ℕ :=
  (E.filterMap fun e => if e.1 = v then some e.2 else if e.2 = v then some e.1 else none).dedup

/-- The ends of the edges. -/
def cand (E : List (ℕ × ℕ)) : List ℕ := E.flatMap fun e => [e.1, e.2]

/-- A vertex with at least d neighbours, if the budget is positive. -/
def pick (d : ℕ) (x : VNode) : Option ℕ := (cand x.2).find? fun v => decide (0 < x.1) && decide (d ≤ (nbs x.2 v).length)

/-- The edges not at v. -/
def delV (E : List (ℕ × ℕ)) (v : ℕ) : List (ℕ × ℕ) := E.filter fun e => !(decide (e.1 = v) || decide (e.2 = v))

/-- The edges at none of v and its neighbours; all edges if there are more than k neighbours. -/
def delN (E : List (ℕ × ℕ)) (v k : ℕ) : List (ℕ × ℕ) :=
  E.filter fun e => decide (k < (nbs E v).length) ||
    !(decide (e.1 = v) || decide (e.2 = v) || decide (e.1 ∈ nbs E v) || decide (e.2 ∈ nbs E v))

/-- The branching step. -/
def stepV (d : ℕ) (x : VNode) : Option (VNode × VNode) :=
  (pick d x).map fun v => ((x.1 - 1, delV x.2 v), (x.1 - (nbs x.2 v).length, delN x.2 v x.1))

/-! ### Neighbours -/

theorem mem_nbs {E : List (ℕ × ℕ)} {v u : ℕ} :
    u ∈ nbs E v ↔ ∃ e ∈ E, (e.1 = v ∧ e.2 = u) ∨ (e.1 ≠ v ∧ e.2 = v ∧ e.1 = u) := by
  simp only [nbs, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    split_ifs at h with h1 h2
    · exact Or.inl ⟨h1, Option.some_inj.1 h⟩
    · exact Or.inr ⟨h1, h2, Option.some_inj.1 h⟩
  · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2, h3⟩⟩
    · exact ⟨e, he, by rw [if_pos h1, h2]⟩
    · exact ⟨e, he, by rw [if_neg h1, if_pos h2, h3]⟩

theorem snd_mem_nbs {E : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ E) {v : ℕ} (h : e.1 = v) : e.2 ∈ nbs E v :=
  mem_nbs.2 ⟨e, he, Or.inl ⟨h, rfl⟩⟩

theorem fst_mem_nbs {E : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ E) {v : ℕ} (h : e.2 = v) : e.1 ∈ nbs E v := by
  by_cases h1 : e.1 = v
  · rw [h1, ← h]; exact snd_mem_nbs he (h1.trans h.symm)
  · exact mem_nbs.2 ⟨e, he, Or.inr ⟨h1, h, rfl⟩⟩

theorem card_nbs (E : List (ℕ × ℕ)) (v : ℕ) : (nbs E v).toFinset.card = (nbs E v).length :=
  List.toFinset_card_of_nodup (List.nodup_dedup _)

theorem mem_cand {E : List (ℕ × ℕ)} {u : ℕ} : u ∈ cand E ↔ ∃ e ∈ E, e.1 = u ∨ e.2 = u := by
  simp only [cand, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by tauto⟩
  · rintro ⟨e, he, h | h⟩ <;> exact ⟨e, he, by tauto⟩

/-! ### The step -/

theorem stepV_some {d : ℕ} {x l h : VNode} (e : stepV d x = some (l, h)) : ∃ v, 0 < x.1 ∧ d ≤ (nbs x.2 v).length ∧
    v ∈ cand x.2 ∧ l = (x.1 - 1, delV x.2 v) ∧ h = (x.1 - (nbs x.2 v).length, delN x.2 v x.1) := by
  unfold stepV at e
  obtain ⟨v, hv, e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨h1, h2⟩ := List.find?_eq_some_iff_append.1 hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨as, bs, hab, -⟩ := h2
  refine ⟨v, h1.1, h1.2, by rw [hab]; simp, (Prod.ext_iff.1 e).1.symm, (Prod.ext_iff.1 e).2.symm⟩

theorem stepV_none {d : ℕ} {x : VNode} (e : stepV d x = none) : x.1 = 0 ∨ ∀ v ∈ cand x.2, (nbs x.2 v).length < d := by
  unfold stepV pick at e
  have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 e)
  by_cases h0 : x.1 = 0
  · exact Or.inl h0
  · refine Or.inr fun v hv => ?_
    have h := this v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_le] at h
    exact h (Nat.pos_of_ne_zero h0)

/-- **A node is good exactly if one of its children is.** -/
theorem good_step {d : ℕ} {x l h : VNode} (e : stepV d x = some (l, h)) : Good x ↔ Good l ∨ Good h := by
  obtain ⟨v, hk, -, -, rfl, rfl⟩ := stepV_some e
  obtain ⟨k, E⟩ := x
  simp only at hk ⊢
  have hL0 := card_nbs E v
  constructor
  · rintro ⟨X, hX, hc⟩
    by_cases hv : v ∈ X
    · left
      refine ⟨X.erase v, by rw [card_erase_of_mem hv]; omega, fun e he => ?_⟩
      obtain ⟨he, hne⟩ := List.mem_filter.1 he
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hne
      rcases hc e he with h | h
      · exact Or.inl (mem_erase.2 ⟨hne.1, h⟩)
      · exact Or.inr (mem_erase.2 ⟨hne.2, h⟩)
    · right
      have hNX : (nbs E v).toFinset ⊆ X := by
        intro u hu
        obtain ⟨e, he, ⟨h1, h2⟩ | ⟨-, h1, h2⟩⟩ := mem_nbs.1 (List.mem_toFinset.1 hu)
        · rcases hc e he with h | h
          · exact absurd (h1 ▸ h) hv
          · exact h2 ▸ h
        · rcases hc e he with h | h
          · exact h2 ▸ h
          · exact absurd (h1 ▸ h) hv
      have hc1 := card_le_card hNX
      refine ⟨X \ (nbs E v).toFinset, ?_, fun e he => ?_⟩
      · rw [card_sdiff_of_subset hNX]; simp only; omega
      · obtain ⟨he, hne⟩ := List.mem_filter.1 he
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
          decide_eq_false_iff_not] at hne
        rcases hne with hne | hne
        · omega
        · obtain ⟨⟨⟨-, -⟩, h3⟩, h4⟩ := hne
          rcases hc e he with h | h
          · exact Or.inl (mem_sdiff.2 ⟨h, fun h' => h3 (List.mem_toFinset.1 h')⟩)
          · exact Or.inr (mem_sdiff.2 ⟨h, fun h' => h4 (List.mem_toFinset.1 h')⟩)
  · rintro (⟨X, hX, hc⟩ | ⟨X, hX, hc⟩)
    · simp only at hX hc
      refine ⟨insert v X, (card_insert_le _ _).trans (by omega), fun e he => ?_⟩
      by_cases hat : e.1 = v ∨ e.2 = v
      · rcases hat with h | h
        · exact Or.inl (h ▸ mem_insert_self _ _)
        · exact Or.inr (h ▸ mem_insert_self _ _)
      · have hne : ¬e.1 = v ∧ ¬e.2 = v := not_or.1 hat
        have he' : e ∈ delV E v := List.mem_filter.2 ⟨he, (by
          simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact hne)⟩
        rcases hc e he' with h | h
        · exact Or.inl (mem_insert_of_mem h)
        · exact Or.inr (mem_insert_of_mem h)
    · simp only at hX hc
      by_cases hL : k < (nbs E v).length
      · refine ⟨X, by omega, fun e he => hc e (List.mem_filter.2 ⟨he, by simp [hL]⟩)⟩
      · refine ⟨X ∪ (nbs E v).toFinset, (card_union_le _ _).trans (by omega), fun e he => ?_⟩
        by_cases hat : e.1 = v ∨ e.2 = v ∨ e.1 ∈ nbs E v ∨ e.2 ∈ nbs E v
        · rcases hat with h | h | h | h
          · exact Or.inr (mem_union_right _ (List.mem_toFinset.2 (snd_mem_nbs he h)))
          · exact Or.inl (mem_union_right _ (List.mem_toFinset.2 (fst_mem_nbs he h)))
          · exact Or.inl (mem_union_right _ (List.mem_toFinset.2 h))
          · exact Or.inr (mem_union_right _ (List.mem_toFinset.2 h))
        · have hne : ¬(e.1 = v ∨ e.2 = v ∨ e.1 ∈ nbs E v ∨ e.2 ∈ nbs E v) := hat
          have he' : e ∈ delN E v k := List.mem_filter.2 ⟨he, (by
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
              decide_eq_false_iff_not]
            right; tauto)⟩
          rcases hc e he' with h | h
          · exact Or.inl (mem_union_left _ h)
          · exact Or.inr (mem_union_left _ h)

/-- The root is good exactly if some leaf is. -/
theorem good_leaves (d : ℕ) : ∀ (m : ℕ) (x : VNode), Good x ↔ ∃ y ∈ leaves (stepV d) m x, Good y := by
  intro m
  induction m with
  | zero => intro x; simp [leaves]
  | succ m ih =>
    intro x
    cases h0 : stepV d x with
    | none => simp [leaves, h0]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      simp only [leaves, h0, List.mem_append]
      rw [good_step h0, ih l, ih h]
      constructor
      · rintro (⟨y, hy, g⟩ | ⟨y, hy, g⟩)
        · exact ⟨y, Or.inl hy, g⟩
        · exact ⟨y, Or.inr hy, g⟩
      · rintro ⟨y, hy | hy, g⟩
        · exact Or.inl ⟨y, hy, g⟩
        · exact Or.inr ⟨y, hy, g⟩

/-! ### The size of the tree -/

/-- p steps, t = d·(number of second children), and the edges a sublist of the root's. -/
def Inv (k d : ℕ) (E₀ : List (ℕ × ℕ)) (x : VNode) (p t : ℕ) : Prop :=
  ∃ a b : ℕ, p = a + b ∧ t = d * b ∧ a + t ≤ k + d ∧ (x.1 ≠ 0 → x.1 + a + t ≤ k) ∧ x.2.Sublist E₀

theorem inv_root (k d : ℕ) (E₀ : List (ℕ × ℕ)) : Inv k d E₀ (k, E₀) 0 0 :=
  ⟨0, 0, rfl, by simp, by omega, fun _ => by simp, List.Sublist.refl _⟩

theorem inv_bound {k d : ℕ} (hd : 1 ≤ d) {E₀ : List (ℕ × ℕ)} (x : VNode) (p t : ℕ) (h : Inv k d E₀ x p t) :
    p ≤ k + d ∧ t ≤ k + d := by
  obtain ⟨a, b, rfl, rfl, h1, -⟩ := h
  have : b ≤ d * b := Nat.le_mul_of_pos_left b hd
  omega

theorem inv_step {k d : ℕ} {E₀ : List (ℕ × ℕ)} (x : VNode) (p t : ℕ) (l h : VNode) (hG : Inv k d E₀ x p t)
    (e : stepV d x = some (l, h)) : Inv k d E₀ l (p + 1) t ∧ Inv k d E₀ h (p + 1) (t + d) := by
  obtain ⟨v, hk, hdN, -, rfl, rfl⟩ := stepV_some e
  obtain ⟨a, b, rfl, rfl, h1, h2, h3⟩ := hG
  have h2' := h2 (by omega)
  refine ⟨⟨a + 1, b, by ring, rfl, by omega, fun _ => by simp only; omega,
    List.filter_sublist.trans h3⟩, ⟨a, b + 1, by ring, by ring, by omega, fun hne => ?_,
    List.filter_sublist.trans h3⟩⟩
  simp only at hne ⊢
  have : d * (b + 1) = d * b + d := by ring
  omega

open Classical in
/-- **The tree has at most 2^{ε(k+d)} leaves** if (1/d)·lg(e·d) ≤ ε. -/
theorem leaves_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ((1 : ℕ) : ℝ) / (d : ℝ) * Real.logb 2 (Real.exp 1 * (d : ℝ) * ((1 : ℕ) : ℝ)) ≤ ε) (k : ℕ) (E₀ : List (ℕ × ℕ)) :
    (leaves (stepV d) (k + d) (k, E₀)).length ≤ ∑ j ∈ range ((k + d) / d + 1), (k + d).choose j ∧
    ((leaves (stepV d) (k + d) (k, E₀)).length : ℝ) ≤ (2 : ℝ) ^ (ε * ((k + d : ℕ) : ℝ)) := by
  have h1 := length_leaves_le (G := Inv k d E₀) (inv_bound hd) (fun x p t l h hG e => inv_step x p t l h hG e)
    (k + d) (k + d) ((k + d) / d) (k, E₀) 0 0 (inv_root k d E₀) (by omega)
    (by have := Nat.lt_mul_div_succ (k + d) (show 0 < d by omega); rw [Nat.mul_comm] at this; omega)
  refine ⟨h1, ?_⟩
  have h2 := WidthK.Thresholds.sum_choose_le_two_rpow (k := 1) (L := 1) hd le_rfl hε (k + d)
  simp only [one_mul] at h2
  calc ((leaves (stepV d) (k + d) (k, E₀)).length : ℝ) ≤ ((∑ j ∈ range ((k + d) / d + 1), (k + d).choose j : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ _ := h2

/-- Every leaf is final; the leaves and the nodes on the stack satisfy the invariant. -/
theorem leaves_final {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (E₀ : List (ℕ × ℕ)) :
    ∀ y ∈ leaves (stepV d) (k + d) (k, E₀), stepV d y = none ∧ ∃ p t, Inv k d E₀ y p t := fun y hy =>
  ⟨step_eq_none_of_mem_leaves (inv_bound hd) (fun x p t l h hG e => inv_step x p t l h hG e) (k + d) (k, E₀) 0 0
    (inv_root k d E₀) (by omega) y hy,
   exists_of_mem_leaves (fun x p t l h hG e => inv_step x p t l h hG e) (k + d) (k, E₀) 0 0 (inv_root k d E₀) y hy⟩

theorem stack_inv {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (E₀ : List (ℕ × ℕ)) (i : ℕ) :
    ((round (stepV d))^[i] ([(k, E₀)], [])).1.length ≤ k + d + 1 ∧
      ∀ x ∈ ((round (stepV d))^[i] ([(k, E₀)], [])).1, ∃ p t, Inv k d E₀ x p t :=
  stack_bound (inv_bound hd) (fun x p t l h hG e => inv_step x p t l h hG e) (k, E₀) 0 0 (inv_root k d E₀) i

theorem inv_le {k d : ℕ} {E₀ : List (ℕ × ℕ)} {x : VNode} {p t : ℕ} (h : Inv k d E₀ x p t) : x.1 ≤ k ∧ x.2.Sublist E₀ := by
  obtain ⟨a, b, -, -, -, h2, h3⟩ := h
  refine ⟨?_, h3⟩
  by_cases h0 : x.1 = 0
  · omega
  · have := h2 h0; omega

/-! ### The leaves -/

/-- The vertices on the edges. -/
def verts (E : List (ℕ × ℕ)) : List ℕ := (cand E).dedup

/-- The clauses x_u ∨ x_v, with the vertices renamed by their place in `verts`. -/
def vcClauses (E : List (ℕ × ℕ)) : Fml := E.map fun e => [((verts E).idxOf e.1, true), ((verts E).idxOf e.2, true)]

/-- The input of the counter at a leaf: |V| variables, min(k, |V|) true, the clauses; or nothing to
satisfy if |V| > k·d. -/
def leafV (d : ℕ) (x : VNode) : List Unit × ℕ × Fml :=
  if x.1 * d < (verts x.2).length then ([], 0, [[]])
  else (List.replicate (verts x.2).length (), min x.1 (verts x.2).length, vcClauses x.2)

theorem mem_verts {E : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ E) : e.1 ∈ verts E ∧ e.2 ∈ verts E :=
  ⟨List.mem_dedup.2 (mem_cand.2 ⟨e, he, Or.inl rfl⟩), List.mem_dedup.2 (mem_cand.2 ⟨e, he, Or.inr rfl⟩)⟩

theorem nodup_verts (E : List (ℕ × ℕ)) : (verts E).Nodup := List.nodup_dedup _

/-- **A good leaf has at most k·d vertices.** -/
theorem card_V_le {d : ℕ} (hd : 1 ≤ d) {x : VNode} (hs : stepV d x = none) (hg : Good x) : (verts x.2).length ≤ x.1 * d := by
  obtain ⟨X, hX, hc⟩ := hg
  set Y := X.filter fun w => w ∈ cand x.2 with hY
  have hsub : (verts x.2).toFinset ⊆ Y ∪ Y.biUnion fun w => (nbs x.2 w).toFinset := by
    intro u hu
    obtain ⟨e, he, h⟩ := mem_cand.1 (List.mem_dedup.1 (List.mem_toFinset.1 hu))
    have hw : ∀ w, (w = e.1 ∨ w = e.2) → w ∈ X → w ∈ Y := fun w hw hwX =>
      mem_filter.2 ⟨hwX, mem_cand.2 ⟨e, he, by tauto⟩⟩
    rcases hc e he with h1 | h1
    · rcases h with rfl | rfl
      · exact mem_union_left _ (hw _ (Or.inl rfl) h1)
      · exact mem_union_right _ (mem_biUnion.2 ⟨e.1, hw _ (Or.inl rfl) h1, List.mem_toFinset.2 (snd_mem_nbs he rfl)⟩)
    · rcases h with rfl | rfl
      · exact mem_union_right _ (mem_biUnion.2 ⟨e.2, hw _ (Or.inr rfl) h1, List.mem_toFinset.2 (fst_mem_nbs he rfl)⟩)
      · exact mem_union_left _ (hw _ (Or.inr rfl) h1)
  have hV : (verts x.2).toFinset.card = (verts x.2).length := List.toFinset_card_of_nodup (nodup_verts _)
  have hYX : Y.card ≤ x.1 := (card_filter_le _ _).trans hX
  have hc1 := (card_le_card hsub).trans (card_union_le _ _)
  have hc2 : (Y.biUnion fun w => (nbs x.2 w).toFinset).card ≤ Y.card * (d - 1) := by
    refine card_biUnion_le.trans ?_
    rcases stepV_none hs with h0 | hall
    · have : Y = ∅ := card_eq_zero.1 (by omega)
      simp [this]
    · rw [← smul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun w hw => ?_
      rw [card_nbs]
      have := hall w (mem_filter.1 hw).2
      omega
  rw [hV] at hc1
  have e : Y.card + Y.card * (d - 1) = Y.card * d := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have := Nat.mul_le_mul_right d hYX
  omega

/-- Covers by vertices on the edges, of exactly s = min(k, |V|) vertices. -/
theorem good_iff_exact (x : VNode) : Good x ↔ ∃ Z : Finset ℕ, Z ⊆ (verts x.2).toFinset ∧
    Z.card = min x.1 (verts x.2).length ∧ Covers Z x.2 := by
  have hV : (verts x.2).toFinset.card = (verts x.2).length := List.toFinset_card_of_nodup (nodup_verts _)
  constructor
  · rintro ⟨X, hX, hc⟩
    set Y := X ∩ (verts x.2).toFinset
    have hY : Y.card ≤ min x.1 (verts x.2).length :=
      le_min ((card_le_card inter_subset_left).trans hX) (hV ▸ card_le_card inter_subset_right)
    obtain ⟨Z, h1, h2, h3⟩ := exists_subsuperset_card_eq (inter_subset_right (s₁ := X)) hY
      (by rw [hV]; exact min_le_right _ _)
    refine ⟨Z, h2, h3, fun e he => ?_⟩
    obtain ⟨m1, m2⟩ := mem_verts he
    rcases hc e he with h | h
    · exact Or.inl (h1 (mem_inter.2 ⟨h, List.mem_toFinset.2 m1⟩))
    · exact Or.inr (h1 (mem_inter.2 ⟨h, List.mem_toFinset.2 m2⟩))
  · rintro ⟨Z, -, hZ, hc⟩
    exact ⟨Z, hZ ▸ min_le_left _ _, hc⟩

theorem sat2' (f : ℕ → Bool) (a b : ℕ × Bool) : (∃ l ∈ [a, b], f l.1 = l.2) ↔ f a.1 = a.2 ∨ f b.1 = b.2 := by
  simp

theorem ext_eq {N : ℕ} (a : Fin N → Bool) {i : ℕ} (hi : i < N) : ext a i = a ⟨i, hi⟩ := by
  simp [CountKSat.ext, hi]

/-- **The counter finds a solution exactly at a good leaf.** -/
theorem cnt_leafV_pos {d : ℕ} (hd : 1 ≤ d) {x : VNode} (hs : stepV d x = none) :
    0 < cntS (leafV d x).1.length (leafV d x).2.1 (leafV d x).2.2 ↔ Good x := by
  unfold leafV
  split_ifs with hdead
  · simp only [List.length_nil]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := card_pos.1 h
      obtain ⟨l, hl, -⟩ := (mem_filter.1 ha).2.1 [] (by simp)
      simp at hl
    · intro hg; have := card_V_le hd hs hg; omega
  · simp only [List.length_replicate]
    set V := verts x.2 with hVdef
    have hnd := nodup_verts x.2
    have hidx : ∀ {u}, u ∈ V → V.idxOf u < V.length := fun hu => List.idxOf_lt_length_of_mem hu
    have hget : ∀ {u} (hu : u ∈ V), V[V.idxOf u]'(hidx hu) = u := fun hu => List.getElem_idxOf (hidx hu)
    rw [good_iff_exact, cntS, card_pos]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨-, hsat, hcnt⟩ := mem_filter.1 ha
      refine ⟨(univ.filter fun i => a i = true).image fun i => V[i.val], ?_, ?_, ?_⟩
      · intro u hu
        obtain ⟨i, -, rfl⟩ := mem_image.1 hu
        exact List.mem_toFinset.2 (List.getElem_mem _)
      · rw [card_image_of_injective _ fun i j h => Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h), hcnt]
      · intro e he
        obtain ⟨m1, m2⟩ := mem_verts (E := x.2) he
        have := hsat _ (List.mem_map.2 ⟨e, he, rfl⟩)
        rw [sat2'] at this
        simp only at this
        rcases this with h | h
        · rw [ext_eq a (hidx m1)] at h
          exact Or.inl (mem_image.2 ⟨_, mem_filter.2 ⟨mem_univ _, h⟩, hget m1⟩)
        · rw [ext_eq a (hidx m2)] at h
          exact Or.inr (mem_image.2 ⟨_, mem_filter.2 ⟨mem_univ _, h⟩, hget m2⟩)
    · rintro ⟨Z, hZV, hZ, hc⟩
      refine ⟨fun i => decide (V[i.val] ∈ Z), mem_filter.2 ⟨mem_univ _, fun C hC => ?_, ?_⟩⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hC
        obtain ⟨m1, m2⟩ := mem_verts (E := x.2) he
        rw [sat2']
        simp only
        rw [ext_eq _ (hidx m1), ext_eq _ (hidx m2)]
        simp only [hget m1, hget m2, decide_eq_true_eq]
        exact hc e he
      · rw [← hZ]
        refine card_bij (fun i _ => V[i.val]) (fun i hi => by simpa using hi)
          (fun i _ j _ h => Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h)) (fun u hu => ?_)
        have hu' := List.mem_toFinset.1 (hZV hu)
        exact ⟨⟨V.idxOf u, hidx hu'⟩, by simpa [hget hu'] using hu, hget hu'⟩

theorem shaped_leafV (d : ℕ) (x : VNode) : Shaped 2 (leafV d x).1.length (leafV d x).2.2 := by
  unfold leafV
  split_ifs
  · intro C hC; simp at hC; subst hC; simp
  · intro C hC
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hC
    obtain ⟨m1, m2⟩ := mem_verts (E := x.2) he
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [List.length_replicate]
    rcases hl with rfl | rfl
    · exact List.idxOf_lt_length_of_mem m1
    · exact List.idxOf_lt_length_of_mem m2

theorem leafV_shape (d : ℕ) (x : VNode) : (leafV d x).1 = List.replicate (leafV d x).1.length () ∧
    (leafV d x).2.1 ≤ (leafV d x).1.length ∧ (leafV d x).1.length ≤ x.1 * d ∧ (leafV d x).2.2.length ≤ x.2.length + 1 := by
  unfold leafV
  split_ifs with h
  · simp
  · simp only [List.length_replicate, vcClauses, List.length_map]
    refine ⟨by simp, min_le_right _ _, by omega, by omega⟩

end EthCor.Vc
