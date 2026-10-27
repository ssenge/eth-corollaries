module

public import GraphProblems.Interfaces
public import SplitCount.Sizes
import all GraphProblems.DomTree
import SparsifyWidthK.Thresholds
import Mathlib.Tactic

/-! # The tree that shortens the clauses of an arbitrary CNF

A formula ψ on n variables, of any width, becomes a formula on 2n variables in which every clause of
ψ is positive: the literal (u, b) is the variable 2u if b and 2u+1 if not (`lv`), and the clauses
x_{2u} ∨ x_{2u+1}, ¬x_{2u} ∨ ¬x_{2u+1} (`pairF`) make x_{2u+1} the negation of x_{2u}. Its
satisfying assignments have exactly n true variables, and there are as many as ψ has
(`cntS_rootX`). The tree of Anthropic's Corollary 7 (`GraphProblems.stepD`) then shortens these
positive clauses. Their invariant bounds the number of open clauses by the number of variables; here
it is any M (`Inv2`), so ψ may have more clauses than variables. With M = D·n there is, for every
ε > 0, a width w for which the tree has at most 2^{εn} leaves (`shortens`). -/

@[expose] public section

namespace EthCor.CnfTree

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems GraphProblems.DomTree Finset

/-! ### Literals as variables -/

/-- The literal (u, b) as the variable 2u if b, 2u + 1 if not. -/
def lv (l : ℕ × Bool) : ℕ := 2 * l.1 + bif l.2 then 0 else 1

/-- x_{2u} and x_{2u+1} differ, for u < n. -/
def pairF (n : ℕ) : Fml :=
  (List.range n).flatMap fun u => [[(2 * u, true), (2 * u + 1, true)], [(2 * u, false), (2 * u + 1, false)]]

/-- The root for ψ on n variables: 2n variables and s = n; the clauses of ψ open, each as the list of
the variables of its literals; the pair clauses closed. -/
def rootX (a : List Unit × Fml) : DNode :=
  ((List.replicate (2 * a.1.length) (), a.1.length), (a.2.map fun C => (C.map lv).dedup, pairF a.1.length))

/-- The assignment on 2n variables of an assignment a on n variables. -/
def dbl {n : ℕ} (a : Fin n → Bool) (j : Fin (2 * n)) : Bool :=
  if j.val % 2 = 0 then a ⟨j.val / 2, by omega⟩ else !a ⟨j.val / 2, by omega⟩

theorem ext_dbl_even {n : ℕ} (a : Fin n → Bool) {u : ℕ} (hu : u < n) : ext (dbl a) (2 * u) = a ⟨u, hu⟩ := by
  have h2 : 2 * u < 2 * n := by omega
  simp [CountKSat.ext, h2, dbl]

theorem ext_dbl_odd {n : ℕ} (a : Fin n → Bool) {u : ℕ} (hu : u < n) : ext (dbl a) (2 * u + 1) = !a ⟨u, hu⟩ := by
  have h2 : 2 * u + 1 < 2 * n := by omega
  have e1 : (2 * u + 1) % 2 = 1 := by omega
  have e2 : (2 * u + 1) / 2 = u := by omega
  simp [CountKSat.ext, h2, dbl, e1, e2]

theorem ext_dbl_lv {n : ℕ} (a : Fin n → Bool) {l : ℕ × Bool} (hl : l.1 < n) :
    ext (dbl a) (lv l) = true ↔ ext a l.1 = l.2 := by
  obtain ⟨u, b⟩ := l
  simp only at hl ⊢
  have e : ext a u = a ⟨u, hl⟩ := by simp [CountKSat.ext, hl]
  cases b
  · rw [show lv (u, false) = 2 * u + 1 by simp [lv], ext_dbl_odd a hl, e]; simp
  · rw [show lv (u, true) = 2 * u by simp [lv], ext_dbl_even a hl, e]

theorem lv_lt {n : ℕ} {l : ℕ × Bool} (hl : l.1 < n) : lv l < 2 * n := by
  unfold lv; cases l.2 <;> simp <;> omega

theorem lv_injective : Function.Injective lv := by
  rintro ⟨u, b⟩ ⟨u', b'⟩ h
  cases b <;> cases b' <;> simp [lv] at h ⊢ <;> omega

theorem mem_pairF {n : ℕ} {C : List (ℕ × Bool)} :
    C ∈ pairF n ↔ ∃ u < n, C = [(2 * u, true), (2 * u + 1, true)] ∨ C = [(2 * u, false), (2 * u + 1, false)] := by
  simp only [pairF, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]

theorem length_pairF (n : ℕ) : (pairF n).length = 2 * n := by
  simp [pairF, List.length_flatMap]; ring

theorem shaped_pairF {w : ℕ} (hw : 2 ≤ w) (n : ℕ) : Shaped w (2 * n) (pairF n) := by
  intro C hC
  obtain ⟨u, hu, rfl | rfl⟩ := mem_pairF.1 hC <;>
    exact ⟨by simpa using hw, fun l hl => by simp at hl; rcases hl with rfl | rfl <;> simp <;> omega⟩

/-! ### The count at the root -/

/-- The assignments of 2n variables that satisfy the pair clauses are the doubled assignments. -/
theorem sat_pairF {n : ℕ} (b : Fin (2 * n) → Bool) :
    (∀ C ∈ pairF n, ∃ l ∈ C, ext b l.1 = l.2) ↔ ∀ u, u < n → ext b (2 * u + 1) = !ext b (2 * u) := by
  constructor
  · intro h u hu
    obtain ⟨l1, hl1, e1⟩ := h _ (mem_pairF.2 ⟨u, hu, Or.inl rfl⟩)
    obtain ⟨l2, hl2, e2⟩ := h _ (mem_pairF.2 ⟨u, hu, Or.inr rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;> simp_all
  · intro h C hC
    obtain ⟨u, hu, rfl | rfl⟩ := mem_pairF.1 hC
    · cases hb : ext b (2 * u)
      · exact ⟨(2 * u + 1, true), by simp, show ext b (2 * u + 1) = true by rw [h u hu, hb]; rfl⟩
      · exact ⟨(2 * u, true), by simp, hb⟩
    · cases hb : ext b (2 * u)
      · exact ⟨(2 * u, false), by simp, hb⟩
      · exact ⟨(2 * u + 1, false), by simp, show ext b (2 * u + 1) = false by rw [h u hu, hb]; rfl⟩

theorem sat_dbl_pairF {n : ℕ} (a : Fin n → Bool) : ∀ C ∈ pairF n, ∃ l ∈ C, ext (dbl a) l.1 = l.2 :=
  (sat_pairF _).2 fun u hu => by rw [ext_dbl_odd a hu, ext_dbl_even a hu]

/-- The doubled assignment satisfies the translated clauses exactly if a satisfies ψ. -/
theorem sat_open {n : ℕ} (a : Fin n → Bool) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    (∀ C ∈ (ψ.map fun C => (C.map lv).dedup).map posC, ∃ l ∈ C, ext (dbl a) l.1 = l.2) ↔
      ∀ C ∈ ψ, ∃ l ∈ C, ext a l.1 = l.2 := by
  constructor
  · intro h C hC
    have hm : posC (C.map lv).dedup ∈ (ψ.map fun C => (C.map lv).dedup).map posC :=
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨C, hC, rfl⟩, rfl⟩
    obtain ⟨q, hq, e⟩ := h _ hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hv)
    exact ⟨l, hl, (ext_dbl_lv a (hψ C hC l hl)).1 e⟩
  · intro h C' hC'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    obtain ⟨l, hl, e⟩ := h C hC
    exact ⟨(lv l, true), List.mem_map.2 ⟨lv l, List.mem_dedup.2 (List.mem_map.2 ⟨l, hl, rfl⟩), rfl⟩,
      (ext_dbl_lv a (hψ C hC l hl)).2 e⟩

theorem card_dbl {n : ℕ} (a : Fin n → Bool) : (univ.filter fun j : Fin (2 * n) => dbl a j = true).card = n := by
  suffices h : (univ : Finset (Fin n)).card = (univ.filter fun j : Fin (2 * n) => dbl a j = true).card by
    rw [← h, Finset.card_univ, Fintype.card_fin]
  refine Finset.card_bij (fun u _ => (⟨2 * u.val + bif a u then 0 else 1, by cases a u <;> simp <;> omega⟩ : Fin (2 * n)))
    (fun u _ => ?_) (fun u _ u' _ h => ?_) (fun j hj => ?_)
  · have key : ∀ k (hk : k < n), k = u.val → a ⟨k, hk⟩ = a u := fun k hk e => congrArg a (Fin.ext e)
    simp only [dbl]
    cases h : a u <;> simp [h, Nat.add_mod] <;> rw [key _ _ (by omega), h]
  · have := congrArg (fun j : Fin (2 * n) => j.val / 2) h
    simp only at this
    have e1 : (2 * u.val + bif a u then 0 else 1) / 2 = u.val := by cases a u <;> simp <;> omega
    have e2 : (2 * u'.val + bif a u' then 0 else 1) / 2 = u'.val := by cases a u' <;> simp <;> omega
    exact Fin.ext (by rw [← e1, ← e2]; exact this)
  · have hj' := (Finset.mem_filter.1 hj).2
    simp only [dbl] at hj'
    refine ⟨⟨j.val / 2, by omega⟩, mem_univ _, Fin.ext ?_⟩
    simp only
    split_ifs at hj' with hp
    · rw [hj']; simp; omega
    · rw [Bool.not_eq_true'] at hj'; rw [hj']; simp; omega

/-- **The count at the root**: the formula on 2n variables has as many satisfying assignments with
n true variables as ψ has satisfying assignments. -/
theorem cntS_rootX (n : ℕ) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    cntS (2 * n) n (leafD (rootX (List.replicate n (), ψ))).2.2 = cntN n ψ := by
  simp only [leafD, rootX, List.length_replicate]
  unfold cntS cntN
  symm
  refine Finset.card_bij (fun a _ => dbl a) (fun a ha => ?_) (fun a _ a' _ h => ?_) (fun b hb => ?_)
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢
    refine ⟨List.forall_mem_append.2 ⟨(sat_open a hψ).2 ha, sat_dbl_pairF a⟩, card_dbl a⟩
  · funext u
    have := congrFun h ⟨2 * u.val, by omega⟩
    simpa [dbl] using this
  · simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨hs, -⟩ := hb
    obtain ⟨h1, h2⟩ := List.forall_mem_append.1 hs
    have hp := (sat_pairF b).1 h2
    have hb : dbl (fun u : Fin n => b ⟨2 * u.val, by omega⟩) = b := by
      funext j
      have hj := j.2
      unfold dbl
      split_ifs with hpar
      · exact congrArg b (Fin.ext (show 2 * (j.val / 2) = j.val by omega))
      · have := hp (j.val / 2) (by omega)
        rw [show 2 * (j.val / 2) + 1 = j.val by omega] at this
        simp only [CountKSat.ext, dif_pos hj, dif_pos (show 2 * (j.val / 2) < 2 * n by omega)] at this
        rw [this]
    refine ⟨_, ?_, hb⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← sat_open _ hψ, hb]
    exact h1

/-! ### The invariant, with at most M open clauses -/

/-- As `GraphProblems.DomTree.Inv`, with the number M of clauses in place of n where it bounds the
open clauses, and P closed clauses at the root. -/
def Inv2 (N s w M P : ℕ) (x : DNode) (p t : ℕ) : Prop :=
  x.1 = (List.replicate N (), s) ∧ ∃ (a : ℕ) (V : Finset ℕ), a + x.2.1.length ≤ M ∧ p ≤ a + t ∧ t + #V ≤ N ∧
    (∀ u ∈ V, u < N) ∧ (∀ D ∈ x.2.1, D.Nodup ∧ ∀ u ∈ D, u ∈ V) ∧ x.2.2.length ≤ P + a + t ∧ Shaped w N x.2.2

theorem inv2_bound {N s w M P : ℕ} (x : DNode) (p t : ℕ) (h : Inv2 N s w M P x p t) : p ≤ M + N ∧ t ≤ N := by
  obtain ⟨-, a, V, h1, h2, h3, -⟩ := h
  omega

theorem inv2_root {w : ℕ} (hw : 2 ≤ w) (n : ℕ) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    Inv2 (2 * n) n w ψ.length (2 * n) (rootX (List.replicate n (), ψ)) 0 0 := by
  refine ⟨by simp [rootX], 0, range (2 * n), by simp [rootX], le_rfl, by simp, fun u hu => mem_range.1 hu, ?_,
    by simp [rootX, length_pairF], by simpa [rootX] using shaped_pairF hw n⟩
  intro D hD
  simp only [rootX, List.mem_map] at hD
  obtain ⟨C, hC, rfl⟩ := hD
  refine ⟨List.nodup_dedup _, fun u hu => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hu)
  exact mem_range.2 (lv_lt (hψ C hC l hl))

theorem inv2_step {N s w M P : ℕ} (hw : 1 ≤ w) (x : DNode) (p t : ℕ) (l h : DNode) (hG : Inv2 N s w M P x p t)
    (e : stepD w x = some (l, h)) : Inv2 N s w M P l (p + 1) t ∧ Inv2 N s w M P h (p + 1) (t + w) := by
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
      · refine ⟨by simp [posC], fun q hq => ?_⟩
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
        exact ⟨by simpa using hw, fun q hq => by
          obtain rfl : q = (u, false) := by simpa using hq
          exact h4 u (hHV u hu)⟩
      · exact h7 B hB

theorem inv2_size {N s w M P : ℕ} {x : DNode} {p t : ℕ} (h : Inv2 N s w M P x p t) :
    x.1 = (List.replicate N (), s) ∧ x.2.1.length ≤ M ∧ (∀ D ∈ x.2.1, D.length ≤ N ∧ ∀ u ∈ D, u < N) ∧
      x.2.2.length ≤ P + M + N ∧ Shaped w N x.2.2 := by
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hx, by omega, fun D hD => ⟨?_, fun u hu => h4 u ((h5 D hD).2 u hu)⟩, by omega, h7⟩
  have hc : #D.toFinset ≤ #V := card_le_card fun u hu => (h5 D hD).2 u (List.mem_toFinset.1 hu)
  rw [List.toFinset_card_of_nodup (h5 D hD).1] at hc
  omega

/-! ### The choice of the width -/

/-- For every L ≥ 1 and ε > 0 some w ≥ 2 has (2/w)·lg(e·w·L) ≤ ε. -/
theorem exists_width (L : ℕ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℕ, 2 ≤ w ∧ ((2 : ℕ) : ℝ) / (w : ℝ) * Real.logb 2 (Real.exp 1 * (w : ℝ) * (L : ℝ)) ≤ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.sqrt (Real.exp 1 * L) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.sqrt_nonneg _
  obtain ⟨w₀, hw₀⟩ := exists_nat_ge ((4 * A / (ε * Real.log 2)) ^ 2)
  refine ⟨w₀ + 2, by omega, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((w₀ + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hw]
  have hw2 : (2 : ℝ) ≤ w := by rw [hw]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) w₀]
  have hw0 : 0 < w := by linarith
  have hS : 4 * A / (ε * Real.log 2) ≤ Real.sqrt w := by
    apply Real.le_sqrt_of_sq_le
    refine hw₀.trans ?_
    rw [hw]; push_cast; linarith
  have hS0 : 0 < Real.sqrt w := Real.sqrt_pos.2 hw0
  have hy : 0 < Real.exp 1 * w * L := by positivity
  have hlog : Real.log (Real.exp 1 * w * L) ≤ 2 * (A * Real.sqrt w) := by
    have h1 := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : Real.sqrt (Real.exp 1 * w * L) = A * Real.sqrt w := by
      rw [hA, show Real.exp 1 * w * L = Real.exp 1 * L * w by ring, Real.sqrt_mul (by positivity)]
    rw [h2] at h1
    linarith
  have hww : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw0.le
  rw [Real.logb, Nat.cast_ofNat]
  have hS' : 4 * A ≤ ε * Real.log 2 * Real.sqrt w := by
    rw [div_le_iff₀ (by positivity)] at hS; linarith
  have step1 : (2 : ℝ) / w * (Real.log (Real.exp 1 * w * L) / Real.log 2) ≤ 2 / w * (2 * (A * Real.sqrt w) / Real.log 2) := by
    gcongr
  refine step1.trans ?_
  generalize Real.sqrt w = S at hS' hS0 hww ⊢
  rw [← hww, div_mul_div_comm, div_le_iff₀ (mul_pos (mul_pos hS0 hS0) hl2)]
  nlinarith [mul_le_mul_of_nonneg_left hS' hS0.le]

/-! ### The tree -/

/-- **The tree for a CNF with at most D·n clauses**, for a width w ≥ 2 with (2/w)·lg(e·w·(D+2)) ≤ ε:
for every formula ψ with variables below n and at most D·n clauses, the tree of depth
(D+2)·n from `rootX` has at most 2^{εn} leaves; every leaf is final, on 2n variables with s = n, of
width at most w, with at most (2D+4)·n clauses; the numbers `cntS (2n) n` of the leaves add up to
the number of satisfying assignments of ψ; and the stack of the walk holds at most (D+2)·n + 1 nodes,
each with at most D·n open clauses of at most 2n variables below 2n and at most (D+4)·n closed
clauses of width at most w. -/
theorem shortens_of (D w : ℕ) (hw2 : 2 ≤ w) {ε : ℝ}
    (hw : ((2 : ℕ) : ℝ) / (w : ℝ) * Real.logb 2 (Real.exp 1 * (w : ℝ) * ((D + 2 : ℕ) : ℝ)) ≤ ε) : ∀ (n : ℕ) (ψ : Fml),
    (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → ψ.length ≤ D * n →
    ((leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ)), stepD w x = none ∧
      x.1 = (List.replicate (2 * n) (), n) ∧ Shaped w (2 * n) (leafD x).2.2 ∧ (leafD x).2.2.length ≤ (2 * D + 4) * n) ∧
    cntN n ψ = ((leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ))).map fun x => cntS (2 * n) n (leafD x).2.2).sum ∧
    ∀ i, ((round (stepD w))^[i] ([rootX (List.replicate n (), ψ)], [])).1.length ≤ (D + 2) * n + 1 ∧
      ∀ x ∈ ((round (stepD w))^[i] ([rootX (List.replicate n (), ψ)], [])).1, x.1 = (List.replicate (2 * n) (), n) ∧
        x.2.1.length ≤ D * n ∧ (∀ D' ∈ x.2.1, D'.length ≤ 2 * n ∧ ∀ u ∈ D', u < 2 * n) ∧
        x.2.2.length ≤ (D + 4) * n ∧ Shaped w (2 * n) x.2.2 := by
  have hw1 : 1 ≤ w := by omega
  intro n ψ hψ hm
  set G := Inv2 (2 * n) n w (D * n) (2 * n) with hGdef
  have hb : ∀ x p t, G x p t → p ≤ D * n + 2 * n ∧ t ≤ 2 * n := inv2_bound
  have hs : ∀ x p t l h, G x p t → stepD w x = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + w) :=
    fun x p t l h => inv2_step hw1 x p t l h
  have h0 : G (rootX (List.replicate n (), ψ)) 0 0 := by
    obtain ⟨hx, a, V, h1, h2⟩ := inv2_root hw2 n hψ
    exact ⟨hx, a, V, h1.trans hm, h2⟩
  have hdep : D * n + 2 * n ≤ 0 + (D + 2) * n := by ring_nf; omega
  refine ⟨?_, fun x hx => ?_, ?_, fun i => ?_⟩
  · have h1 := length_leaves_le hb hs ((D + 2) * n) ((D + 2) * n) (2 * n / w) _ 0 0 h0 hdep
      (by have := Nat.lt_mul_div_succ (2 * n) (show 0 < w by omega); rw [Nat.mul_comm w] at this; simpa only [zero_add] using this)
    have h2 := WidthK.Thresholds.sum_choose_le_two_rpow hw1 (show 2 ≤ D + 2 by omega) hw n
    exact le_trans (by exact_mod_cast h1) h2
  · have hn := step_eq_none_of_mem_leaves hb hs ((D + 2) * n) _ 0 0 h0 hdep x hx
    obtain ⟨p', t', hG⟩ := exists_of_mem_leaves hs ((D + 2) * n) _ 0 0 h0 x hx
    obtain ⟨g1, g2, g3, g4, g5⟩ := inv2_size hG
    have hshort : ∀ D ∈ x.2.1, D.length ≤ w := by
      unfold stepD at hn
      have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 hn)
      intro D hD
      simpa using this D hD
    refine ⟨hn, g1, ?_, ?_⟩
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
        refine ⟨by simpa [posC] using hshort D hD, fun q hq => ?_⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
        exact (g3 D hD).2 u hu
      · exact g5 B hB
    · simp only [leafD, List.length_append, List.length_map]
      have : (2 * D + 4) * n = D * n + (2 * n + D * n + 2 * n) := by ring
      omega
  · have h1 := sum_leaves (stepD w) (fun x => cntS (2 * n) n (leafD x).2.2) (fun x l h e => cntS_step e (2 * n) n)
      ((D + 2) * n) (rootX (List.replicate n (), ψ))
    rw [← h1, cntS_rootX n hψ]
  · obtain ⟨h1, h2⟩ := stack_bound hb hs _ 0 0 h0 i
    have e1 : D * n + 2 * n = (D + 2) * n := by ring
    have e2 : (D + 4) * n = 2 * n + D * n + 2 * n := by ring
    refine ⟨by omega, fun x hx => ?_⟩
    obtain ⟨p', t', hG⟩ := h2 x hx
    obtain ⟨g1, g2, g3, g4, g5⟩ := inv2_size hG
    exact ⟨g1, g2, g3, by omega, g5⟩

/-- For every D and ε > 0 some width w ≥ 2 makes `shortens_of` apply. -/
theorem shortens (D : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ w : ℕ, 2 ≤ w ∧ ∀ (n : ℕ) (ψ : Fml),
    (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → ψ.length ≤ D * n →
    ((leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ)), stepD w x = none ∧
      x.1 = (List.replicate (2 * n) (), n) ∧ Shaped w (2 * n) (leafD x).2.2 ∧ (leafD x).2.2.length ≤ (2 * D + 4) * n) ∧
    cntN n ψ = ((leaves (stepD w) ((D + 2) * n) (rootX (List.replicate n (), ψ))).map fun x => cntS (2 * n) n (leafD x).2.2).sum ∧
    ∀ i, ((round (stepD w))^[i] ([rootX (List.replicate n (), ψ)], [])).1.length ≤ (D + 2) * n + 1 ∧
      ∀ x ∈ ((round (stepD w))^[i] ([rootX (List.replicate n (), ψ)], [])).1, x.1 = (List.replicate (2 * n) (), n) ∧
        x.2.1.length ≤ D * n ∧ (∀ D' ∈ x.2.1, D'.length ≤ 2 * n ∧ ∀ u ∈ D', u < 2 * n) ∧
        x.2.2.length ≤ (D + 4) * n ∧ Shaped w (2 * n) x.2.2 := by
  obtain ⟨w, hw2, hw⟩ := exists_width (D + 2) (by omega) hε
  exact ⟨w, hw2, shortens_of D w hw2 hw⟩

end EthCor.CnfTree
