import Mathlib

/-! # An isolation lemma for arbitrary sets, with sparse parity checks

After Calabro, Impagliazzo, Kabanets and Paturi (Lemma 3 of "The complexity of Unique k-SAT"), whose
proof only uses that S is a nonempty set of vectors. A seed ω consists of a number m, mm parity checks
on k coordinates each (indices with repetition, coefficients, right-hand sides), and for every
coordinate a value in `Fin t` and a bit: the coordinate is fixed to the bit when the value is 0.
`H ω x` says that x passes the first m checks and the fixings.

Step I (`card_not_semi`, `card_fiber_le`): x ∈ S is semi-isolated when no y ∈ S at distance ≥ r passes
the same checks. A check separates two vectors at distance ≥ r unless all k indices miss their
difference (`two_mul_card_rv`), so few check arrays leave x not semi-isolated. The semi-isolated
points with the same check values lie in one ball of radius r − 1. Step II (`stepII`): if the points
of S that pass the checks lie within distance < 2r of each other, fixing the coordinates where the
two furthest of them differ, to the values of one of them, leaves exactly that one. `card_unique_ge`
puts the two steps together. -/

open Finset

namespace EthCor.Iso

variable {M k : ℕ}

/-- The Hamming weight. -/
def wt (z : Fin M → Bool) : ℕ := (univ.filter fun j => z j = true).card

/-- The Hamming distance. -/
def hd (x y : Fin M → Bool) : ℕ := wt fun j => xor (x j) (y j)

/-- A parity check on k coordinates: the indices (with repetition) and the coefficients. -/
abbrev Row (M k : ℕ) := (Fin k → Fin M) × (Fin k → Bool)

/-- The value of a parity check on x. -/
def rv (ρ : Row M k) (x : Fin M → Bool) : ZMod 2 := ∑ l, if (ρ.2 l && x (ρ.1 l)) = true then 1 else 0

/-- A bit as an element of ZMod 2. -/
def bz (b : Bool) : ZMod 2 := if b = true then 1 else 0

/-! ### One parity check -/

theorem add_aux : ∀ a b c : Bool, ((if (a && b) = true then (1 : ZMod 2) else 0) +
    if (a && c) = true then 1 else 0) = if (a && xor b c) = true then 1 else 0 := by decide

theorem rv_add (ρ : Row M k) (x y : Fin M → Bool) :
    rv ρ x + rv ρ y = rv ρ (fun j => xor (x j) (y j)) := by
  unfold rv
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => add_aux _ _ _

theorem zmod2_eq_iff (a b : ZMod 2) : a = b ↔ a + b = 0 := by revert a b; decide

theorem rv_eq_iff (ρ : Row M k) (x y : Fin M → Bool) :
    rv ρ x = rv ρ y ↔ rv ρ (fun j => xor (x j) (y j)) = 0 := by
  rw [zmod2_eq_iff, rv_add]

theorem flip_aux : ∀ (a : Bool) (s : ZMod 2),
    (if ((!a) && true) = true then (1 : ZMod 2) else 0) + s = (if (a && true) = true then 1 else 0) + s + 1 := by
  decide

/-- Flipping the coefficient of an index that hits z flips the value. -/
theorem rv_flip (J : Fin k → Fin M) (C : Fin k → Bool) (z : Fin M → Bool) (l₀ : Fin k)
    (h : z (J l₀) = true) : rv (J, Function.update C l₀ (!C l₀)) z = rv (J, C) z + 1 := by
  unfold rv
  rw [← Finset.add_sum_erase _ _ (mem_univ l₀), ← Finset.add_sum_erase _ _ (mem_univ l₀)]
  have hs : ∑ l ∈ univ.erase l₀, (if ((Function.update C l₀ (!C l₀)) l && z (J l)) = true then (1 : ZMod 2) else 0) =
      ∑ l ∈ univ.erase l₀, (if (C l && z (J l)) = true then (1 : ZMod 2) else 0) :=
    Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  simp only at hs ⊢
  rw [hs]
  simp only [Function.update_self, h]
  exact flip_aux _ _

theorem update_update (C : Fin k → Bool) (l₀ : Fin k) :
    Function.update (Function.update C l₀ (!C l₀)) l₀ (!(Function.update C l₀ (!C l₀)) l₀) = C := by
  funext l
  by_cases hl : l = l₀
  · subst hl; simp
  · simp [Function.update_of_ne hl]

/-- If an index hits z, half of the coefficient vectors give the value 0. -/
theorem two_mul_card_half (J : Fin k → Fin M) (z : Fin M → Bool) (h : ∃ l, z (J l) = true) :
    2 * (univ.filter fun C : Fin k → Bool => rv (J, C) z = 0).card = 2 ^ k := by
  obtain ⟨l₀, hl₀⟩ := h
  have heq : (univ.filter fun C : Fin k → Bool => rv (J, C) z = 0).card =
      (univ.filter fun C : Fin k → Bool => ¬ rv (J, C) z = 0).card := by
    refine Finset.card_nbij' (fun C => Function.update C l₀ (!C l₀)) (fun C => Function.update C l₀ (!C l₀))
      ?_ ?_ ?_ ?_
    · intro C hC
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hC ⊢
      rw [rv_flip J C z l₀ hl₀, hC]; decide
    · intro C hC
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hC ⊢
      rw [rv_flip J C z l₀ hl₀]
      revert hC; generalize rv (J, C) z = a; revert a; decide
    · intro C _; exact update_update C l₀
    · intro C _; exact update_update C l₀
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k → Bool)))
    (fun C => rv (J, C) z = 0)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  omega

theorem card_false (z : Fin M → Bool) : (univ.filter fun j => z j = false).card = M - wt z := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (fun j => z j = true)
  rw [card_univ, Fintype.card_fin] at h
  have e : (univ.filter fun j : Fin M => ¬ z j = true) = univ.filter fun j => z j = false := by
    ext j; simp
  rw [e] at h
  unfold wt
  omega

/-- **One check**: 2·#{ρ : ρ(z) = 0} = 2^k·M^k + 2^k·(M − |z|)^k. -/
theorem two_mul_card_rv (z : Fin M → Bool) :
    2 * (univ.filter fun ρ : Row M k => rv ρ z = 0).card = 2 ^ k * M ^ k + 2 ^ k * (M - wt z) ^ k := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum]
  have h1 : ∀ J : Fin k → Fin M, 2 * ∑ C : Fin k → Bool, (if rv (J, C) z = 0 then 1 else 0) =
      2 ^ k + (if ∀ l, z (J l) = false then 2 ^ k else 0) := by
    intro J
    rw [← Finset.card_filter]
    by_cases hJ : ∀ l, z (J l) = false
    · rw [if_pos hJ]
      have : (univ.filter fun C : Fin k → Bool => rv (J, C) z = 0) = univ := by
        ext C
        simp only [mem_filter, mem_univ, true_and, iff_true]
        unfold rv
        exact Finset.sum_eq_zero fun l _ => by simp [hJ l]
      rw [this, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; ring
    · rw [if_neg hJ, add_zero]
      push_neg at hJ
      obtain ⟨l, hl⟩ := hJ
      exact two_mul_card_half J z ⟨l, by simpa using hl⟩
  rw [Finset.sum_congr rfl fun J _ => h1 J, Finset.sum_add_distrib, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, smul_eq_mul, ← Finset.sum_filter, sum_const, smul_eq_mul]
  have hc : (univ.filter fun J : Fin k → Fin M => ∀ l, z (J l) = false).card = (M - wt z) ^ k := by
    have : (univ.filter fun J : Fin k → Fin M => ∀ l, z (J l) = false) =
        Fintype.piFinset fun _ => univ.filter fun j => z j = false := by
      ext J; simp [Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_false]
  rw [hc]; simp only [Fintype.card_fin]; ring

/-! ### Many checks -/

theorem prod_ite_lt (mm m a b : ℕ) (hm : m ≤ mm) :
    ∏ i : Fin mm, (if i.val < m then a else b) = a ^ m * b ^ (mm - m) := by
  calc ∏ i : Fin mm, (if i.val < m then a else b) = ∏ i ∈ range mm, (if i < m then a else b) :=
        Fin.prod_univ_eq_prod_range (fun i => if i < m then a else b) mm
    _ = a ^ m * b ^ (mm - m) := by
        rw [Finset.prod_ite, prod_const, prod_const]
        have e1 : (range mm).filter (· < m) = range m := by ext i; simp; omega
        have e2 : (range mm).filter (fun i => ¬ i < m) = Finset.Ico m mm := by ext i; simp; omega
        rw [e1, e2, card_range, Nat.card_Ico]

theorem card_row : Fintype.card (Row M k) = M ^ k * 2 ^ k := by
  simp [Fintype.card_prod, Fintype.card_fun]

/-- The arrays of checks whose first m checks agree on x and y. -/
theorem card_agree (x y : Fin M → Bool) (m mm : ℕ) (hm : m ≤ mm) :
    (univ.filter fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y).card =
      (univ.filter fun ρ : Row M k => rv ρ x = rv ρ y).card ^ m * (M ^ k * 2 ^ k) ^ (mm - m) := by
  have : (univ.filter fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) =
      Fintype.piFinset fun i : Fin mm =>
        if i.val < m then univ.filter (fun ρ : Row M k => rv ρ x = rv ρ y) else univ := by
    ext R
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    split_ifs with h <;> simp [h]
  rw [this, Fintype.card_piFinset]
  have e : ∀ i : Fin mm, (if i.val < m then univ.filter (fun ρ : Row M k => rv ρ x = rv ρ y) else univ).card =
      if i.val < m then (univ.filter (fun ρ : Row M k => rv ρ x = rv ρ y)).card else M ^ k * 2 ^ k := by
    intro i; split_ifs
    · rfl
    · rw [card_univ, card_row]
  rw [Finset.prod_congr rfl fun i _ => e i, prod_ite_lt mm m _ _ hm]

/-- The right-hand sides that match given values on the first m checks. -/
theorem card_rhs (m mm : ℕ) (hm : m ≤ mm) (v : Fin mm → ZMod 2) :
    (univ.filter fun B : Fin mm → Bool => ∀ i : Fin mm, i.val < m → v i = bz (B i)).card = 2 ^ (mm - m) := by
  have h1 : ∀ a : ZMod 2, (univ.filter fun b : Bool => a = bz b).card = 1 := by decide
  have : (univ.filter fun B : Fin mm → Bool => ∀ i : Fin mm, i.val < m → v i = bz (B i)) =
      Fintype.piFinset fun i : Fin mm => if i.val < m then univ.filter (fun b : Bool => v i = bz b) else univ := by
    ext B
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    split_ifs with h <;> simp [h]
  rw [this, Fintype.card_piFinset]
  have e : ∀ i : Fin mm, (if i.val < m then univ.filter (fun b : Bool => v i = bz b) else univ).card =
      if i.val < m then 1 else 2 := by
    intro i; split_ifs
    · exact h1 _
    · rw [card_univ, Fintype.card_bool]
  rw [Finset.prod_congr rfl fun i _ => e i, prod_ite_lt mm m _ _ hm, one_pow, one_mul]

/-! ### Step I: semi-isolated points -/

/-- No y ∈ S at distance ≥ r passes the first m checks of R with the same values as x. -/
abbrev semi (S : Finset (Fin M → Bool)) (r m : ℕ) {mm : ℕ} (R : Fin mm → Row M k) (x : Fin M → Bool) : Prop :=
  ∀ y ∈ S, r ≤ hd x y → ∃ i : Fin mm, i.val < m ∧ rv (R i) x ≠ rv (R i) y

/-- x passes the first m checks of (R, B). -/
abbrev rowsOK {mm : ℕ} (m : ℕ) (R : Fin mm → Row M k) (B : Fin mm → Bool) (x : Fin M → Bool) : Prop :=
  ∀ i : Fin mm, i.val < m → rv (R i) x = bz (B i)

/-- x agrees with the fixed coordinates of F. -/
abbrev fixOK {t : ℕ} (F : Fin M → Fin t × Bool) (x : Fin M → Bool) : Prop :=
  ∀ j, (F j).1.val = 0 → x j = (F j).2

/-- **Union bound**: few arrays of checks leave x not semi-isolated. -/
theorem card_not_semi (S : Finset (Fin M → Bool)) (r m mm : ℕ) (hm : m ≤ mm) (x : Fin M → Bool) :
    (univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x).card * 2 ^ m ≤
      S.card * ((2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m * (M ^ k * 2 ^ k) ^ (mm - m)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m * (M ^ k * 2 ^ k) ^ (mm - m) := ⟨_, rfl⟩
  rw [← hQ]
  have hsub : (univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x) ⊆
      S.biUnion fun y => if r ≤ hd x y then
        univ.filter (fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) else ∅ := by
    intro R hR
    simp only [mem_filter, mem_univ, true_and, semi, not_forall, not_exists, not_and, not_not] at hR
    obtain ⟨y, hy, hr, h⟩ := hR
    exact mem_biUnion.2 ⟨y, hy, by rw [if_pos hr]; exact mem_filter.2 ⟨mem_univ _, h⟩⟩
  have hb : ∀ y ∈ S, (if r ≤ hd x y then
      univ.filter (fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) else ∅).card *
        2 ^ m ≤ Q := by
    intro y _
    split_ifs with hr
    · rw [card_agree x y m mm hm, hQ]
      have h2 := two_mul_card_rv (k := k) (fun j => xor (x j) (y j))
      have hA : (univ.filter fun ρ : Row M k => rv ρ x = rv ρ y) =
          univ.filter fun ρ : Row M k => rv ρ (fun j => xor (x j) (y j)) = 0 := by
        ext ρ; simp only [mem_filter, mem_univ, true_and]; exact rv_eq_iff ρ x y
      rw [hA]
      have hw : (M - wt (fun j => xor (x j) (y j))) ^ k ≤ (M - r) ^ k :=
        Nat.pow_le_pow_left (by unfold hd at hr; omega) k
      have h3 : 2 * (univ.filter fun ρ : Row M k => rv ρ (fun j => xor (x j) (y j)) = 0).card ≤
          2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k := by
        rw [h2]; have := Nat.mul_le_mul_left (2 ^ k) hw; omega
      calc (univ.filter fun ρ : Row M k => rv ρ (fun j => xor (x j) (y j)) = 0).card ^ m *
            (M ^ k * 2 ^ k) ^ (mm - m) * 2 ^ m =
          (2 * (univ.filter fun ρ : Row M k => rv ρ (fun j => xor (x j) (y j)) = 0).card) ^ m *
            (M ^ k * 2 ^ k) ^ (mm - m) := by rw [mul_pow]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h3 m)
    · simp
  calc (univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x).card * 2 ^ m
      ≤ (S.biUnion fun y => if r ≤ hd x y then
          univ.filter (fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) else ∅).card *
            2 ^ m := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ y ∈ S, (if r ≤ hd x y then
          univ.filter (fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) else ∅).card) *
            2 ^ m := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ y ∈ S, (if r ≤ hd x y then
          univ.filter (fun R : Fin mm → Row M k => ∀ i : Fin mm, i.val < m → rv (R i) x = rv (R i) y) else ∅).card *
            2 ^ m := by rw [Finset.sum_mul]
    _ ≤ ∑ _y ∈ S, Q := sum_le_sum hb
    _ = S.card * Q := by rw [sum_const, smul_eq_mul]

/-- The semi-isolated points with the same check values lie in one ball of radius r − 1. -/
theorem card_fiber_le (S : Finset (Fin M → Bool)) (r m : ℕ) {mm : ℕ} (R : Fin mm → Row M k)
    (B : Fin mm → Bool) :
    (S.filter fun x => semi S r m R x ∧ rowsOK m R B x).card ≤ (univ.filter fun z : Fin M → Bool => wt z < r).card := by
  by_cases hne : (S.filter fun x => semi S r m R x ∧ rowsOK m R B x).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    rw [mem_filter] at hx₀
    refine card_le_card_of_injOn (fun x j => xor (x₀ j) (x j)) ?_ ?_
    · intro x hx
      have hx := mem_filter.1 (Finset.mem_coe.1 hx)
      refine Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, ?_⟩)
      by_contra hlt
      push_neg at hlt
      obtain ⟨i, hi, hne⟩ := hx₀.2.1 x hx.1 hlt
      exact hne (by rw [hx₀.2.2 i hi, hx.2.2 i hi])
    · intro x _ y _ hxy
      funext j
      have := congrFun hxy j
      simp only at this
      revert this; cases x₀ j <;> cases x j <;> cases y j <;> simp
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp

/-- Double counting. -/
theorem sum_card_le {α β : Type*} [Fintype β] (S : Finset α) (P : α → β → Prop) [∀ a b, Decidable (P a b)]
    (V : ℕ) (hV : ∀ b, (S.filter fun a => P a b).card ≤ V) :
    ∑ a ∈ S, (univ.filter fun b => P a b).card ≤ (univ.filter fun b => ∃ a ∈ S, P a b).card * V := by
  calc ∑ a ∈ S, (univ.filter fun b => P a b).card = ∑ b, (S.filter fun a => P a b).card := by
        simp only [card_filter]; exact Finset.sum_comm
    _ = ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, P a b), (S.filter fun a => P a b).card := by
        rw [Finset.sum_filter]
        refine sum_congr rfl fun b _ => ?_
        split_ifs with h
        · rfl
        · push_neg at h
          rw [card_eq_zero, filter_eq_empty_iff]
          exact fun a ha => h a ha
    _ ≤ ∑ _b ∈ univ.filter (fun b => ∃ a ∈ S, P a b), V := sum_le_sum fun b _ => hV b
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- The pairs (R, B) for which x is semi-isolated and passes the checks. -/
theorem card_pairs (S : Finset (Fin M → Bool)) (r m mm : ℕ) (hm : m ≤ mm) (x : Fin M → Bool) :
    (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) => semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card =
      (univ.filter fun R : Fin mm → Row M k => semi S r m R x).card * 2 ^ (mm - m) := by
  rw [card_filter, Fintype.sum_prod_type, card_filter, sum_mul]
  refine sum_congr rfl fun R _ => ?_
  by_cases hs : semi S r m R x
  · rw [if_pos hs, one_mul, ← card_rhs m mm hm (fun i => rv (R i) x), card_filter]
    refine sum_congr rfl fun B _ => ?_
    by_cases hB : rowsOK m R B x
    · rw [if_pos ⟨hs, hB⟩, if_pos hB]
    · rw [if_neg fun h => hB h.2, if_neg hB]
  · rw [if_neg hs, zero_mul]
    refine sum_eq_zero fun B _ => ?_
    simp only [hs, false_and, if_false]

/-! ### Step II: fixing coordinates -/

theorem hd_comm (x y : Fin M → Bool) : hd x y = hd y x := by
  unfold hd wt; congr 1; ext j; simp [Bool.xor_comm]

theorem hd_triangle (x y z : Fin M → Bool) : hd x z ≤ hd x y + hd y z := by
  unfold hd wt
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro j hj
  simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
  revert hj; cases x j <;> cases y j <;> cases z j <;> simp

theorem hd_eq_zero {x y : Fin M → Bool} (h : hd x y = 0) : x = y := by
  unfold hd wt at h
  rw [card_eq_zero, filter_eq_empty_iff] at h
  funext j
  have := h (mem_univ j)
  simp only at this
  revert this; generalize x j = a; generalize y j = b; revert a b; decide

theorem card_cond (t : ℕ) (ht : 1 ≤ t) (b : Bool) :
    (univ.filter fun p : Fin t × Bool => p.1.val = 0 → p.2 = b).card = 2 * t - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin t × Bool)))
    (fun p => p.1.val = 0 → p.2 = b)
  have h1 : (univ.filter fun p : Fin t × Bool => ¬ (p.1.val = 0 → p.2 = b)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨(⟨0, ht⟩, !b), ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton, _root_.not_imp]
    obtain ⟨⟨a, ha⟩, c⟩ := p
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    cases b <;> cases c <;> simp
  rw [h1, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
  omega

/-- **Step II**: if some point of S passing the checks is semi-isolated, then a fraction
(2t−1)^M / ((2t−1)^{2r}·(2t)^M) of the fixings leaves exactly one point. -/
theorem stepII (S : Finset (Fin M → Bool)) (r m t : ℕ) (ht : 1 ≤ t) {mm : ℕ} (R : Fin mm → Row M k)
    (B : Fin mm → Bool) (hG : ∃ x ∈ S, semi S r m R x ∧ rowsOK m R B x) :
    (2 * t - 1) ^ M ≤ (2 * t - 1) ^ (2 * r) *
      (univ.filter fun F : Fin M → Fin t × Bool => (S.filter fun x => rowsOK m R B x ∧ fixOK F x).card = 1).card := by
  obtain ⟨x₀, hx₀S, hx₀s, hx₀B⟩ := hG
  obtain ⟨T, hT⟩ : ∃ T, T = S.filter fun x => rowsOK m R B x := ⟨_, rfl⟩
  have hx₀T : x₀ ∈ T := by rw [hT, mem_filter]; exact ⟨hx₀S, hx₀B⟩
  have hnear : ∀ x ∈ T, hd x₀ x < r := by
    intro x hx
    rw [hT, mem_filter] at hx
    by_contra hlt
    push_neg at hlt
    obtain ⟨i, hi, hne⟩ := hx₀s x hx.1 hlt
    exact hne (by rw [hx₀B i hi, hx.2 i hi])
  obtain ⟨⟨u, u'⟩, hp, hmax⟩ := Finset.exists_max_image (T ×ˢ T) (fun p => hd p.1 p.2)
    ⟨(x₀, x₀), mem_product.2 ⟨hx₀T, hx₀T⟩⟩
  obtain ⟨huT, hu'T⟩ := mem_product.1 hp
  have hmax' : ∀ w ∈ T, hd w u' ≤ hd u u' := fun w hw => hmax (w, u') (mem_product.2 ⟨hw, hu'T⟩)
  have hC : hd u u' < 2 * r := by
    have h1 := hnear u huT
    have h2 := hnear u' hu'T
    have := hd_triangle u x₀ u'
    rw [hd_comm u x₀] at this
    omega
  -- the good fixings
  obtain ⟨P, hP⟩ : ∃ P : Finset (Fin M → Fin t × Bool), P = Fintype.piFinset fun j =>
      if u j ≠ u' j then {((⟨0, ht⟩ : Fin t), u j)} else univ.filter fun p : Fin t × Bool => p.1.val = 0 → p.2 = u j :=
    ⟨_, rfl⟩
  have hPsub : P ⊆ univ.filter fun F : Fin M → Fin t × Bool => (S.filter fun x => rowsOK m R B x ∧ fixOK F x).card = 1 := by
    intro F hF
    rw [hP, Fintype.mem_piFinset] at hF
    rw [mem_filter, Finset.card_eq_one]
    refine ⟨mem_univ _, u, ?_⟩
    have hFu : ∀ j, (F j).1.val = 0 → u j = (F j).2 := by
      intro j hj
      have := hF j
      split_ifs at this with h
      · rw [mem_singleton] at this; rw [this]
      · exact ((mem_filter.1 this).2 hj).symm
    have hFC : ∀ j, u j ≠ u' j → F j = ((⟨0, ht⟩ : Fin t), u j) := by
      intro j hj
      have := hF j
      rw [if_pos hj, mem_singleton] at this
      exact this
    ext w
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hwS, hwB, hwF⟩
      have hwT : w ∈ T := by rw [hT, mem_filter]; exact ⟨hwS, hwB⟩
      -- w agrees with u where u and u' differ
      have hagree : ∀ j, u j ≠ u' j → w j = u j := by
        intro j hj
        have := hwF j (by rw [hFC j hj])
        rw [this, hFC j hj]
      have hsum : hd u u' + hd w u ≤ hd w u' := by
        unfold hd wt
        rw [← card_union_of_disjoint]
        · refine card_le_card fun j hj => ?_
          simp only [mem_union, mem_filter, mem_univ, true_and] at hj ⊢
          rcases hj with hj | hj
          · have hne : u j ≠ u' j := by revert hj; cases u j <;> cases u' j <;> simp
            have := hagree j hne
            revert hne; rw [this]; cases u j <;> cases u' j <;> simp
          · by_cases hne : u j = u' j
            · rw [← hne]; exact hj
            · have := hagree j hne
              revert hj; rw [this]; simp
        · rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [mem_filter, mem_univ, true_and] at h1 h2
          have hne : u j ≠ u' j := by revert h1; cases u j <;> cases u' j <;> simp
          have := hagree j hne
          revert h2; rw [this]; simp
      have := hmax' w hwT
      exact hd_eq_zero (by omega)
    · rintro rfl
      rw [hT, mem_filter] at huT
      exact ⟨huT.1, huT.2, fun j hj => hFu j hj⟩
  -- the number of good fixings
  have hcard : P.card * (2 * t - 1) ^ hd u u' = (2 * t - 1) ^ M := by
    rw [hP, Fintype.card_piFinset]
    have e : ∀ j, (if u j ≠ u' j then {((⟨0, ht⟩ : Fin t), u j)} else
        univ.filter fun p : Fin t × Bool => p.1.val = 0 → p.2 = u j).card = if u j ≠ u' j then 1 else 2 * t - 1 := by
      intro j; split_ifs
      · exact card_singleton _
      · exact card_cond t ht (u j)
    rw [Finset.prod_congr rfl fun j _ => e j, Finset.prod_ite, prod_const_one, prod_const, one_mul, ← pow_add]
    congr 1
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (fun j => u j ≠ u' j)
    rw [card_univ, Fintype.card_fin] at h
    have e2 : (univ.filter fun j : Fin M => u j ≠ u' j).card = hd u u' := by
      unfold hd wt; congr 1; ext j; simp only [mem_filter, mem_univ, true_and]
      cases u j <;> cases u' j <;> simp
    omega
  have h2t : 1 ≤ 2 * t - 1 := by omega
  calc (2 * t - 1) ^ M = P.card * (2 * t - 1) ^ hd u u' := hcard.symm
    _ ≤ (2 * t - 1) ^ (2 * r) * P.card := by
        rw [mul_comm]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h2t hC.le)
    _ ≤ _ := Nat.mul_le_mul_left _ (card_le_card hPsub)

/-! ### Both steps -/

theorem card_filter_prod {A B : Type*} [Fintype A] [Fintype B] (P : A → B → Prop) [∀ a b, Decidable (P a b)] :
    (univ.filter fun q : A × B => P q.1 q.2).card = ∑ a, (univ.filter fun b => P a b).card := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

theorem sum_mul_card_le {A B : Type*} [Fintype A] [Fintype B] (G : Finset A) (Q : A → B → Prop)
    [∀ a b, Decidable (Q a b)] (c d : ℕ) (h : ∀ a ∈ G, d ≤ c * (univ.filter fun b => Q a b).card) :
    G.card * d ≤ c * (univ.filter fun q : A × B => Q q.1 q.2).card := by
  calc G.card * d = ∑ _a ∈ G, d := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ G, c * (univ.filter fun b => Q a b).card := sum_le_sum h
    _ ≤ ∑ a, c * (univ.filter fun b => Q a b).card := sum_le_sum_of_subset (subset_univ _)
    _ = c * ∑ a, (univ.filter fun b => Q a b).card := (Finset.mul_sum univ _ _).symm
    _ = c * (univ.filter fun q : A × B => Q q.1 q.2).card := by rw [card_filter_prod Q]

/-- The seeds: the number m of checks used, the checks with their right-hand sides, and the fixings. -/
abbrev Seed (M k t mm : ℕ) := Fin (mm + 1) × ((Fin mm → Row M k) × (Fin mm → Bool)) × (Fin M → Fin t × Bool)

/-- x passes the checks and the fixings of ω. -/
abbrev H {t mm : ℕ} (ω : Seed M k t mm) (x : Fin M → Bool) : Prop :=
  rowsOK ω.1.val ω.2.1.1 ω.2.1.2 x ∧ fixOK ω.2.2 x

theorem card_unique_ge (S : Finset (Fin M → Bool)) (r m mm t : ℕ) (hm : m ≤ mm) (ht : 1 ≤ t) :
    (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) => ∃ x ∈ S, semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card *
        (2 * t - 1) ^ M ≤
      (2 * t - 1) ^ (2 * r) * (univ.filter fun ω : Seed M k t mm => (S.filter (H ω)).card = 1).card := by
  have h1 : (univ.filter fun q : ((Fin mm → Row M k) × (Fin mm → Bool)) × (Fin M → Fin t × Bool) =>
      (S.filter fun x => rowsOK m q.1.1 q.1.2 x ∧ fixOK q.2 x).card = 1).card ≤
        (univ.filter fun ω : Seed M k t mm => (S.filter (H ω)).card = 1).card := by
    refine card_le_card_of_injOn (fun q => ((⟨m, by omega⟩ : Fin (mm + 1)), q)) ?_ ?_
    · intro q hq
      exact Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, (mem_filter.1 (Finset.mem_coe.1 hq)).2⟩)
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      exact h.2
  have h2 := sum_mul_card_le (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
      ∃ x ∈ S, semi S r m p.1 x ∧ rowsOK m p.1 p.2 x)
    (fun (p : (Fin mm → Row M k) × (Fin mm → Bool)) (F : Fin M → Fin t × Bool) =>
      (S.filter fun x => rowsOK m p.1 p.2 x ∧ fixOK F x).card = 1)
    ((2 * t - 1) ^ (2 * r)) ((2 * t - 1) ^ M) (fun p hp => stepII S r m t ht p.1 p.2 (mem_filter.1 hp).2)
  exact h2.trans (Nat.mul_le_mul_left _ h1)

/-! ### Counting the isolating seeds -/

/-- When 2|S|·A^m ≤ (2N)^m, at least half of the check arrays make x semi-isolated. -/
theorem two_mul_card_semi (S : Finset (Fin M → Bool)) (r m mm : ℕ) (hm : m ≤ mm) (x : Fin M → Bool)
    (hgood : 2 * S.card * (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m ≤ (2 * (M ^ k * 2 ^ k)) ^ m) :
    (M ^ k * 2 ^ k) ^ mm ≤ 2 * (univ.filter fun R : Fin mm → Row M k => semi S r m R x).card := by
  have h1 := card_not_semi (k := k) S r m mm hm x
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin mm → Row M k)))
    (fun R => semi S r m R x)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, card_row] at htot
  have h2 : 2 ^ m * (2 * (univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x).card) ≤
      2 ^ m * (M ^ k * 2 ^ k) ^ mm := by
    calc 2 ^ m * (2 * (univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x).card)
        = 2 * ((univ.filter fun R : Fin mm → Row M k => ¬ semi S r m R x).card * 2 ^ m) := by ring
      _ ≤ 2 * (S.card * ((2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m * (M ^ k * 2 ^ k) ^ (mm - m))) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 * S.card * (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m * (M ^ k * 2 ^ k) ^ (mm - m) := by ring
      _ ≤ (2 * (M ^ k * 2 ^ k)) ^ m * (M ^ k * 2 ^ k) ^ (mm - m) := Nat.mul_le_mul_right _ hgood
      _ = 2 ^ m * (M ^ k * 2 ^ k) ^ mm := by rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  have h3 := Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos m)
  omega

/-- Steps I and II for a fixed number m of checks. -/
theorem iso_main (S : Finset (Fin M → Bool)) (r m mm t : ℕ) (hm : m ≤ mm) (ht : 1 ≤ t)
    (hgood : 2 * S.card * (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ m ≤ (2 * (M ^ k * 2 ^ k)) ^ m) :
    S.card * ((M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m)) * (2 * t - 1) ^ M ≤
      2 * (univ.filter fun z : Fin M → Bool => wt z < r).card * (2 * t - 1) ^ (2 * r) *
        (univ.filter fun ω : Seed M k t mm => (S.filter (H ω)).card = 1).card := by
  have hsum := sum_card_le S (fun x (p : (Fin mm → Row M k) × (Fin mm → Bool)) => semi S r m p.1 x ∧ rowsOK m p.1 p.2 x)
    (univ.filter fun z : Fin M → Bool => wt z < r).card (fun p => card_fiber_le S r m p.1 p.2)
  have hx : ∀ x ∈ S, (M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m) ≤
      2 * (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) => semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card := by
    intro x _
    rw [card_pairs S r m mm hm x, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (two_mul_card_semi S r m mm hm x hgood)
  have hS : S.card * ((M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m)) ≤
      2 * ((univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
        ∃ x ∈ S, semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card * (univ.filter fun z : Fin M → Bool => wt z < r).card) := by
    calc S.card * ((M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m)) = ∑ _x ∈ S, (M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ S, 2 * (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
            semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card := sum_le_sum hx
      _ = 2 * ∑ x ∈ S, (univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
            semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card := (Finset.mul_sum S _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hsum
  have hU := card_unique_ge (k := k) S r m mm t hm ht
  calc S.card * ((M ^ k * 2 ^ k) ^ mm * 2 ^ (mm - m)) * (2 * t - 1) ^ M
      ≤ 2 * ((univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
        ∃ x ∈ S, semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card * (univ.filter fun z : Fin M → Bool => wt z < r).card) *
          (2 * t - 1) ^ M := Nat.mul_le_mul_right _ hS
    _ = 2 * (univ.filter fun z : Fin M → Bool => wt z < r).card * ((univ.filter fun p : (Fin mm → Row M k) × (Fin mm → Bool) =>
        ∃ x ∈ S, semi S r m p.1 x ∧ rowsOK m p.1 p.2 x).card * (2 * t - 1) ^ M) := by ring
    _ ≤ 2 * (univ.filter fun z : Fin M → Bool => wt z < r).card *
        ((2 * t - 1) ^ (2 * r) * (univ.filter fun ω : Seed M k t mm => (S.filter (H ω)).card = 1).card) :=
          Nat.mul_le_mul_left _ hU
    _ = _ := by ring

/-- The least good m: 2^m·N^mm ≤ 4|S|·A^mm. -/
theorem exists_m (s A N mm : ℕ) (hs : 1 ≤ s) (hNA : N ≤ A) (hmm : 2 * s * A ^ mm ≤ (2 * N) ^ mm) :
    ∃ m ≤ mm, 2 * s * A ^ m ≤ (2 * N) ^ m ∧ 2 ^ m * N ^ mm ≤ 4 * s * A ^ mm := by
  classical
  have hex : ∃ m, 2 * s * A ^ m ≤ (2 * N) ^ m := ⟨mm, hmm⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.find hex := ⟨_, rfl⟩
  have hmle : m ≤ mm := hm ▸ Nat.find_min' hex hmm
  have hspec : 2 * s * A ^ m ≤ (2 * N) ^ m := hm ▸ Nat.find_spec hex
  refine ⟨m, hmle, hspec, ?_⟩
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp at hspec; omega
  have hlt : ¬ 2 * s * A ^ (m - 1) ≤ (2 * N) ^ (m - 1) := hm ▸ Nat.find_min hex (by omega)
  have h1 : 2 ^ m * N ^ (m - 1) ≤ 4 * s * A ^ (m - 1) := by
    have e : 2 ^ m * N ^ (m - 1) = 2 * (2 * N) ^ (m - 1) := by
      rw [mul_pow, show m = m - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel]; ring
    rw [e]
    have : (2 * N) ^ (m - 1) < 2 * s * A ^ (m - 1) := by omega
    linarith
  have e1 : N ^ mm = N ^ (m - 1) * N ^ (mm - m + 1) := by rw [← pow_add]; congr 1; omega
  have e2 : A ^ mm = A ^ (m - 1) * A ^ (mm - m + 1) := by rw [← pow_add]; congr 1; omega
  have h3 : N ^ (mm - m + 1) ≤ A ^ (mm - m + 1) := Nat.pow_le_pow_left hNA _
  rw [e1, e2]
  calc 2 ^ m * (N ^ (m - 1) * N ^ (mm - m + 1)) = (2 ^ m * N ^ (m - 1)) * N ^ (mm - m + 1) := by ring
    _ ≤ (4 * s * A ^ (m - 1)) * A ^ (mm - m + 1) := Nat.mul_le_mul h1 h3
    _ = _ := by ring

theorem iso_arith (s A N V U m mm a b c Ω : ℕ) (hm : m ≤ mm)
    (h1 : 2 ^ m * N ^ mm ≤ 4 * s * A ^ mm)
    (h2 : s * (N ^ mm * 2 ^ (mm - m)) * a ≤ 2 * V * b * U)
    (hΩ : Ω = (mm + 1) * (N ^ mm * 2 ^ mm) * c) :
    Ω * (a * N ^ mm) ≤ 8 * (mm + 1) * A ^ mm * V * b * c * U := by
  subst hΩ
  have e : 2 ^ mm = 2 ^ (mm - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  calc (mm + 1) * (N ^ mm * (2 ^ (mm - m) * 2 ^ m)) * c * (a * N ^ mm)
      = (mm + 1) * c * (N ^ mm * 2 ^ (mm - m) * a) * (2 ^ m * N ^ mm) := by ring
    _ ≤ (mm + 1) * c * (N ^ mm * 2 ^ (mm - m) * a) * (4 * s * A ^ mm) := Nat.mul_le_mul_left _ h1
    _ = 4 * (mm + 1) * c * A ^ mm * (s * (N ^ mm * 2 ^ (mm - m)) * a) := by ring
    _ ≤ 4 * (mm + 1) * c * A ^ mm * (2 * V * b * U) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem card_seed (t mm : ℕ) :
    Fintype.card (Seed M k t mm) = (mm + 1) * ((M ^ k * 2 ^ k) ^ mm * 2 ^ mm) * (2 * t) ^ M := by
  simp only [Seed, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, card_row]
  ring

/-- **Counting form of the isolation lemma.** For every nonempty S, with
A = 2^k M^k + 2^k (M−r)^k, N = 2^k M^k and V the volume of the ball of radius r − 1:
|Ω|·(2t−1)^M·N^mm ≤ 8(mm+1)·A^mm·V·(2t−1)^{2r}·(2t)^M·#{ω : |S ∩ H(ω)| = 1}. -/
theorem iso_count (S : Finset (Fin M → Bool)) (hS : S.Nonempty) (r mm t : ℕ) (ht : 1 ≤ t)
    (hmm : 2 * S.card * (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ mm ≤ (2 * (M ^ k * 2 ^ k)) ^ mm) :
    Fintype.card (Seed M k t mm) * ((2 * t - 1) ^ M * (M ^ k * 2 ^ k) ^ mm) ≤
      8 * (mm + 1) * (2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k) ^ mm * (univ.filter fun z : Fin M → Bool => wt z < r).card *
        (2 * t - 1) ^ (2 * r) * (2 * t) ^ M * (univ.filter fun ω : Seed M k t mm => (S.filter (H ω)).card = 1).card := by
  have hNA : M ^ k * 2 ^ k ≤ 2 ^ k * M ^ k + 2 ^ k * (M - r) ^ k := by rw [mul_comm]; exact Nat.le_add_right _ _
  obtain ⟨m, hm, hgood, h1⟩ := exists_m S.card _ _ mm (card_pos.2 hS) hNA hmm
  exact iso_arith _ _ _ _ _ m mm _ _ _ _ hm h1 (iso_main S r m mm t hm ht hgood) (card_seed t mm)

/-! ### The volume of a ball -/

theorem sum_pow_false (a : ℕ) :
    ∑ z : Fin M → Bool, a ^ (univ.filter fun j => z j = false).card = (a + 1) ^ M := by
  have e : ∀ z : Fin M → Bool, a ^ (univ.filter fun j => z j = false).card = ∏ j, (if z j = false then a else 1) := by
    intro z; rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  rw [Finset.sum_congr rfl fun z _ => e z, ← Fintype.prod_sum (fun (_ : Fin M) (b : Bool) => if b = false then a else 1)]
  simp [Fintype.sum_bool, add_comm]

/-- V·a^{M+1−r} ≤ (a+1)^M. -/
theorem card_ball_le (a r : ℕ) (ha : 1 ≤ a) :
    (univ.filter fun z : Fin M → Bool => wt z < r).card * a ^ (M + 1 - r) ≤ (a + 1) ^ M := by
  rw [← sum_pow_false a, card_eq_sum_ones, sum_mul, sum_filter]
  refine sum_le_sum fun z _ => ?_
  split_ifs with h
  · rw [one_mul]
    apply Nat.pow_le_pow_right ha
    have := card_false z
    omega
  · exact Nat.zero_le _

end EthCor.Iso
