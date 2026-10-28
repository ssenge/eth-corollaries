module

public import GraphProblems.Interfaces
public import SplitCount.Sizes
public import EthCor.CnfTree
import all GraphProblems.DomTree
import SparsifyWidthK.Thresholds
import Mathlib.Tactic

/-! # The tree that shortens the clauses of domination, under any closed clauses

The root `rootN N s n m F` has N variables and the target s; its open clauses are the n clauses of
domination of the matrix m (`GraphProblems.nbhd`), and its closed clauses are any formula F of width
at most w + 4 on the N variables. The tree of Anthropic's Corollary 7 (`GraphProblems.stepD w`)
shortens the open clauses; the closed ones are carried along. Their invariant bounds the variables
that may still occur in the open clauses by the number of variables; here the bound is n, however
large N is (`InvC`), so a path has at most n light and n/w heavy steps, and the tree has at most
2^{εn} leaves for a suitable w (`shortensN`). With F the clauses of Cut & Count this counts the
connected dominating sets. -/

@[expose] public section

namespace EthCor.CdsTree

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems GraphProblems.DomTree Finset

/-- The root: N variables, target s; the n clauses of domination of m open, F closed. -/
def rootN (N s n : ℕ) (m : List Bool) (F : Fml) : DNode := ((List.replicate N (), s), (nbhd n m, F))

/-! ### The invariant -/

/-- As `GraphProblems.DomTree.Inv`, with N variables for the shape and R in place of n where it
bounds the open clauses and the variables that may occur in them, P closed clauses at the root and
width W ≥ w for the closed clauses. -/
def InvC (N s W R P : ℕ) (x : DNode) (p t : ℕ) : Prop :=
  x.1 = (List.replicate N (), s) ∧ ∃ (a : ℕ) (V : Finset ℕ), a + x.2.1.length ≤ R ∧ p ≤ a + t ∧ t + #V ≤ R ∧
    (∀ u ∈ V, u < N) ∧ (∀ D ∈ x.2.1, D.Nodup ∧ ∀ u ∈ D, u ∈ V) ∧ x.2.2.length ≤ P + a + t ∧ Shaped W N x.2.2

theorem invC_bound {N s W R P : ℕ} (x : DNode) (p t : ℕ) (h : InvC N s W R P x p t) : p ≤ 2 * R ∧ t ≤ R := by
  obtain ⟨-, a, V, h1, h2, h3, -⟩ := h
  omega

theorem invC_root {N s W n : ℕ} (m : List Bool) {F : Fml} (hn : n ≤ N) (hF : Shaped W N F) :
    InvC N s W n F.length (rootN N s n m F) 0 0 := by
  refine ⟨rfl, 0, range n, by simp [rootN, nbhd], le_rfl, by simp, fun u hu => (mem_range.1 hu).trans_le hn, ?_,
    by simp [rootN], hF⟩
  intro D hD
  simp only [rootN, nbhd, List.mem_map, List.mem_range] at hD
  obtain ⟨v, hv, rfl⟩ := hD
  refine ⟨List.nodup_cons.2 ⟨by simp, List.nodup_range.filter _⟩, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact mem_range.2 hv
  · exact mem_range.2 (List.mem_range.1 (List.mem_of_mem_filter hu))

theorem invC_step {N s w W R P : ℕ} (hw : 1 ≤ w) (hwW : w ≤ W) (x : DNode) (p t : ℕ) (l h : DNode)
    (hG : InvC N s W R P x p t) (e : stepD w x = some (l, h)) :
    InvC N s W R P l (p + 1) t ∧ InvC N s W R P h (p + 1) (t + w) := by
  obtain ⟨C, hC, hwC, rfl, rfl⟩ := stepD_some e
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := hG
  have hlen : (C.take w).length = w := by rw [List.length_take]; omega
  have hHV : ∀ u ∈ C.take w, u ∈ V := fun u hu => (h5 C hC).2 u (List.mem_of_mem_take hu)
  constructor
  · refine ⟨hx, a + 1, V, ?_, by omega, h3, h4, fun D hD => h5 D (List.mem_of_mem_filter hD),
      by simp only [List.length_cons]; omega, ?_⟩
    · have : (x.2.1.filter fun D => D != C).length < x.2.1.length :=
        List.length_filter_lt_length_iff_exists.2 ⟨C, hC, by simp⟩
      simp only
      omega
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · refine ⟨by simp only [posC, List.length_map, hlen]; exact hwW, fun q hq => ?_⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
        exact h4 u (hHV u hu)
      · exact h7 B hB
  · refine ⟨hx, a, V \ (C.take w).toFinset, by simpa using h1, by omega, ?_, fun u hu => h4 u (mem_sdiff.1 hu).1, ?_, ?_, ?_⟩
    · have hsub : (C.take w).toFinset ⊆ V := fun u hu => hHV u (List.mem_toFinset.1 hu)
      have hc := card_sdiff_add_card_eq_card hsub
      have hn : #(C.take w).toFinset = w := by
        rw [List.toFinset_card_of_nodup ((h5 C hC).1.sublist (List.take_sublist w C)), hlen]
      omega
    · intro D' hD'
      obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hD'
      refine ⟨(h5 D hD).1.filter _, fun u hu => ?_⟩
      obtain ⟨hu1, hu2⟩ := List.mem_filter.1 hu
      exact mem_sdiff.2 ⟨(h5 D hD).2 u hu1, by simpa using hu2⟩
    · simp only [List.length_append, List.length_map, hlen]
      omega
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hB
        exact ⟨by simp; omega, fun q hq => by
          obtain rfl : q = (u, false) := by simpa using hq
          exact h4 u (hHV u hu)⟩
      · exact h7 B hB

theorem invC_size {N s W R P : ℕ} {x : DNode} {p t : ℕ} (h : InvC N s W R P x p t) :
    x.1 = (List.replicate N (), s) ∧ x.2.1.length ≤ R ∧ (∀ D ∈ x.2.1, D.length ≤ R ∧ ∀ u ∈ D, u < N) ∧
      x.2.2.length ≤ P + 2 * R ∧ Shaped W N x.2.2 := by
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hx, by omega, fun D hD => ⟨?_, fun u hu => h4 u ((h5 D hD).2 u hu)⟩, by omega, h7⟩
  have hc : #D.toFinset ≤ #V := card_le_card fun u hu => (h5 D hD).2 u (List.mem_toFinset.1 hu)
  rw [List.toFinset_card_of_nodup (h5 D hD).1] at hc
  omega

/-! ### The tree -/

/-- **The tree for domination under closed clauses F**, for a width w ≥ 2 with
(2/w)·lg(2e·w) ≤ ε: for all N ≥ n, every target s, every matrix m and every formula F of width at
most w + 4 on N variables, the tree of depth 2n from `rootN N s n m F` has at most 2^{εn} leaves;
every leaf is final, on N variables with target s, of width at most w + 4, with at most |F| + 3n
clauses; the numbers `cntS N s` of the leaves add up to that of the clauses of domination with F;
and the stack of the walk holds at most 2n + 1 nodes, each with at most n open clauses of at most n
variables below N and at most |F| + 2n closed clauses of width at most w + 4. -/
theorem shortensN (w : ℕ) (hw2 : 2 ≤ w) {ε : ℝ}
    (hw : ((2 : ℕ) : ℝ) / (w : ℝ) * Real.logb 2 (Real.exp 1 * (w : ℝ) * ((2 : ℕ) : ℝ)) ≤ ε)
    (N s n : ℕ) (m : List Bool) (F : Fml) (hn : n ≤ N) (hF : Shaped (w + 4) N F) :
    ((leaves (stepD w) (2 * n) (rootN N s n m F)).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepD w) (2 * n) (rootN N s n m F), stepD w x = none ∧
      x.1 = (List.replicate N (), s) ∧ Shaped (w + 4) N (leafD x).2.2 ∧ (leafD x).2.2.length ≤ F.length + 3 * n) ∧
    cntS N s ((nbhd n m).map posC ++ F) =
      ((leaves (stepD w) (2 * n) (rootN N s n m F)).map fun x => cntS N s (leafD x).2.2).sum ∧
    ∀ i, ((round (stepD w))^[i] ([rootN N s n m F], [])).1.length ≤ 2 * n + 1 ∧
      ∀ x ∈ ((round (stepD w))^[i] ([rootN N s n m F], [])).1, x.1 = (List.replicate N (), s) ∧
        x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < N) ∧
        x.2.2.length ≤ F.length + 2 * n ∧ Shaped (w + 4) N x.2.2 := by
  have hw1 : 1 ≤ w := by omega
  set G := InvC N s (w + 4) n F.length with hGdef
  have hb : ∀ x p t, G x p t → p ≤ 2 * n ∧ t ≤ n := invC_bound
  have hs : ∀ x p t l h, G x p t → stepD w x = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + w) :=
    fun x p t l h => invC_step hw1 (by omega) x p t l h
  have h0 : G (rootN N s n m F) 0 0 := invC_root m hn hF
  refine ⟨?_, fun x hx => ?_, ?_, fun i => ?_⟩
  · have h1 := length_leaves_le hb hs (2 * n) (2 * n) (2 * n / w) _ 0 0 h0 (by omega)
      (by have := Nat.lt_mul_div_succ (2 * n) (show 0 < w by omega); rw [Nat.mul_comm w] at this
          simpa only [zero_add] using lt_of_le_of_lt (show n ≤ 2 * n by omega) this)
    have h2 := WidthK.Thresholds.sum_choose_le_two_rpow hw1 (le_refl 2) hw n
    exact le_trans (by exact_mod_cast h1) h2
  · have hn' := step_eq_none_of_mem_leaves hb hs (2 * n) _ 0 0 h0 (by omega) x hx
    obtain ⟨p', t', hG⟩ := exists_of_mem_leaves hs (2 * n) _ 0 0 h0 x hx
    obtain ⟨g1, g2, g3, g4, g5⟩ := invC_size hG
    have hshort : ∀ D ∈ x.2.1, D.length ≤ w := by
      unfold stepD at hn'
      have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 hn')
      intro D hD
      simpa using this D hD
    refine ⟨hn', g1, ?_, ?_⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
        refine ⟨by simp only [posC, List.length_map]; have := hshort D hD; omega, fun q hq => ?_⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
        exact (g3 D hD).2 u hu
      · exact g5 B hB
    · simp only [leafD, List.length_append, List.length_map]
      omega
  · have h1 := sum_leaves (stepD w) (fun x => cntS N s (leafD x).2.2) (fun x l h e => cntS_step e N s)
      (2 * n) (rootN N s n m F)
    rw [← h1]
    rfl
  · obtain ⟨h1, h2⟩ := stack_bound hb hs _ 0 0 h0 i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hG⟩ := h2 x hx
    exact invC_size hG

/-- For every ε > 0 some width w ≥ 2 makes `shortensN` apply. -/
theorem shortensN_exists {ε : ℝ} (hε : 0 < ε) : ∃ w : ℕ, 2 ≤ w ∧
    ((2 : ℕ) : ℝ) / (w : ℝ) * Real.logb 2 (Real.exp 1 * (w : ℝ) * ((2 : ℕ) : ℝ)) ≤ ε :=
  EthCor.CnfTree.exists_width 2 (by norm_num) hε

end EthCor.CdsTree
