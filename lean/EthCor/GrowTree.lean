module

public import EthCor.CnfTM
import Mathlib.Tactic

/-! # The shortening tree with a width that grows with the number of variables

`stepW` is the step of `GraphProblems.stepD` with the width `wN N` = 2^{⌊L/4⌋ − ⌊lg L⌋} + 1,
L = ⌊lg ⌊lg N⌋⌋, about (lg N)^{1/4}/lg lg N, read off
the node (N = its number of variables). A step of `stepD` keeps the first component of a node, so
from a root on N variables `stepW` is `stepD (wN N)` on the whole tree (`leaves_stepW`,
`round_stepW`). The step keeps the closed clauses, so the pair clauses of `rootX` are in every leaf
(`pairF_sub_leaves`), and then the satisfying assignments of a leaf have exactly n true variables
(`cntS_eq_cntN`). -/

@[expose] public section

namespace EthCor.GrowTree

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems EthCor.CnfTree Finset

/-! ### The width -/

/-- The width for N variables: 2^{⌊L/4⌋ − ⌊lg L⌋} + 1 with L = ⌊lg ⌊lg N⌋⌋, about
(lg N)^{1/4}/lg lg N. -/
def wN (N : ℕ) : ℕ := 2 ^ (Nat.log2 (Nat.log2 N) / 4 - Nat.log2 (Nat.log2 (Nat.log2 N))) + 1

theorem four_mul_le_two_pow {q : ℕ} (hq : 4 ≤ q) : 4 * q ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih => rw [pow_succ]; omega

/-- With ℓ = ⌊lg N⌋, L = ⌊lg ℓ⌋ ≥ 16 and q = ⌊lg L⌋: (w − 1)⁴·2^{4q} ≤ ℓ < 16·(w − 1)⁴·2^{4q}. -/
theorem wN_bounds {N : ℕ} (hL : 16 ≤ Nat.log2 (Nat.log2 N)) :
    (wN N - 1) ^ 4 * 2 ^ (4 * Nat.log2 (Nat.log2 (Nat.log2 N))) ≤ Nat.log2 N ∧
      Nat.log2 N < 16 * ((wN N - 1) ^ 4 * 2 ^ (4 * Nat.log2 (Nat.log2 (Nat.log2 N)))) := by
  have e : wN N - 1 = 2 ^ (Nat.log2 (Nat.log2 N) / 4 - Nat.log2 (Nat.log2 (Nat.log2 N))) := by simp [wN]
  rw [e]
  generalize hℓ : Nat.log2 N = ℓ at hL ⊢
  generalize hLd : Nat.log2 ℓ = L at hL ⊢
  generalize hq : Nat.log2 L = q
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hLd; omega
  have h1 : 2 ^ L ≤ ℓ := hLd ▸ Nat.log2_self_le hℓ0
  have h2 : ℓ < 2 ^ (L + 1) := hLd ▸ Nat.lt_log2_self
  have hqL : q ≤ L / 4 := by
    have h3 : L < 2 ^ (L / 4 + 1) := lt_of_lt_of_le (by omega) (four_mul_le_two_pow (by omega))
    have := (Nat.log2_lt (by omega)).2 h3
    omega
  rw [← pow_mul, ← pow_add]
  constructor
  · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h1
  · calc ℓ < 2 ^ (L + 1) := h2
      _ ≤ 2 ^ (4 + ((L / 4 - q) * 4 + 4 * q)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 * 2 ^ ((L / 4 - q) * 4 + 4 * q) := by rw [pow_add]; norm_num

theorem one_le_wN_sub (N : ℕ) : 1 ≤ wN N - 1 := by simp [wN]; exact Nat.one_le_two_pow

theorem wN_le (N : ℕ) : wN N ≤ N + 2 := by
  have h1 : 2 ^ (Nat.log2 (Nat.log2 N) / 4 - Nat.log2 (Nat.log2 (Nat.log2 N))) ≤ 2 ^ Nat.log2 (Nat.log2 N) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.log2 (Nat.log2 N) ≤ Nat.log2 N ∨ Nat.log2 N = 0 := by
    by_cases h : Nat.log2 N = 0
    · exact Or.inr h
    · exact Or.inl (Nat.log2_self_le h)
  have h3 := Nat.log2_le_self N
  unfold wN
  rcases h2 with h2 | h2
  · omega
  · rw [h2] at h1 ⊢; simp

section Poly

variable {α : Type} [Enc α]

theorem wN_polyT {f : α → ℕ} (hf : Unary f) : Unary fun a => wN (f a) := by
  have he : Unary fun a => Nat.log2 (Nat.log2 (f a)) / 4 - Nat.log2 (Nat.log2 (Nat.log2 (f a))) :=
    Unary.of_le hf (by have := hf.poly; fun_prop) fun a => by
      have := Nat.log2_le_self (Nat.log2 (f a)); have := Nat.log2_le_self (f a)
      omega
  have hp : PolyT fun a => 2 ^ (Nat.log2 (Nat.log2 (f a)) / 4 - Nat.log2 (Nat.log2 (Nat.log2 (f a)))) :=
    PolyT.pow_unary (PolyT.const 2) he
  exact Unary.of_le (hf.add (Unary.const 2)) (by unfold wN; fun_prop) fun a => wN_le (f a)

end Poly

/-! ### The step -/

/-- The step of `stepD` with the width for the number of variables of the node. -/
def stepW (x : DNode) : Option (DNode × DNode) := stepD (wN x.1.1.length) x

theorem stepW_polyT : PolyT stepW := by
  have hw : PolyT fun x : DNode => wN x.1.1.length := (wN_polyT (Unary.of_length (by fun_prop))).poly
  have hD : PolyT fun p : ℕ × DNode => stepD p.1 p.2 := by unfold stepD; fun_prop
  exact PolyT.comp₂ hD hw PolyT.id'

theorem stepD_kids {w : ℕ} {x l h : DNode} (e : stepD w x = some (l, h)) :
    l.1 = x.1 ∧ h.1 = x.1 ∧ (∀ C ∈ x.2.2, C ∈ l.2.2) ∧ ∀ C ∈ x.2.2, C ∈ h.2.2 := by
  unfold stepD at e
  obtain ⟨C, -, e'⟩ := Option.map_eq_some_iff.1 e
  simp only [Prod.mk.injEq] at e'
  obtain ⟨rfl, rfl⟩ := e'
  refine ⟨rfl, rfl, fun D hD => ?_, fun D hD => ?_⟩ <;> simp [hD]

/-! ### Two steps that agree on a closed set of nodes -/

section Congr

variable {σ : Type} {s₁ s₂ : σ → Option (σ × σ)} {P : σ → Prop}

theorem leaves_congr (hag : ∀ x, P x → s₁ x = s₂ x) (hcl : ∀ x l h, P x → s₁ x = some (l, h) → P l ∧ P h) :
    ∀ d x, P x → leaves s₁ d x = leaves s₂ d x
  | 0, _, _ => rfl
  | d + 1, x, hx => by
    simp only [leaves]
    rw [← hag x hx]
    cases e : s₁ x with
    | none => rfl
    | some p =>
      obtain ⟨l, h⟩ := p
      obtain ⟨hl, hh⟩ := hcl x l h hx e
      simp only
      rw [leaves_congr hag hcl d l hl, leaves_congr hag hcl d h hh]

theorem round_congr (hag : ∀ x, P x → s₁ x = s₂ x) (hcl : ∀ x l h, P x → s₁ x = some (l, h) → P l ∧ P h) :
    ∀ i (st out : List σ), (∀ x ∈ st, P x) → (round s₁)^[i] (st, out) = (round s₂)^[i] (st, out)
  | 0, _, _, _ => rfl
  | i + 1, [], out, _ => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact round_congr hag hcl i [] out (by simp)
  | i + 1, x :: r, out, hst => by
    have hx := hst x (by simp)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simp only [Groundwork.Sparsify.round]
    rw [← hag x hx]
    cases e : s₁ x with
    | none => exact round_congr hag hcl i r (x :: out) fun y hy => hst y (by simp [hy])
    | some p =>
      obtain ⟨l, h⟩ := p
      obtain ⟨hl, hh⟩ := hcl x l h hx e
      exact round_congr hag hcl i (l :: h :: r) out fun y hy => by
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | hy
        · exact hl
        · exact hh
        · exact hst y (by simp [hy])

/-- A property of the root that both children keep holds at every leaf. -/
theorem forall_mem_leaves (hcl : ∀ x l h, P x → s₁ x = some (l, h) → P l ∧ P h) :
    ∀ d x, P x → ∀ y ∈ leaves s₁ d x, P y
  | 0, x, hx, y, hy => by simp only [leaves, List.mem_singleton] at hy; exact hy ▸ hx
  | d + 1, x, hx, y, hy => by
    simp only [leaves] at hy
    cases e : s₁ x with
    | none => rw [e] at hy; simp only [List.mem_singleton] at hy; exact hy ▸ hx
    | some p =>
      obtain ⟨l, h⟩ := p
      rw [e] at hy
      obtain ⟨hl, hh⟩ := hcl x l h hx e
      rcases List.mem_append.1 hy with hy | hy
      · exact forall_mem_leaves hcl d l hl y hy
      · exact forall_mem_leaves hcl d h hh y hy

end Congr

theorem leaves_stepW (r : DNode) (d : ℕ) : leaves stepW d r = leaves (stepD (wN r.1.1.length)) d r :=
  leaves_congr (P := fun x => x.1 = r.1) (fun x hx => by unfold stepW; rw [hx])
    (fun x l h hx e => by
      unfold stepW at e; rw [hx] at e
      obtain ⟨h1, h2, -⟩ := stepD_kids e
      exact ⟨h1.trans hx, h2.trans hx⟩) d r rfl

theorem round_stepW (r : DNode) (i : ℕ) :
    (round stepW)^[i] ([r], []) = (round (stepD (wN r.1.1.length)))^[i] ([r], []) :=
  round_congr (P := fun x => x.1 = r.1) (fun x hx => by unfold stepW; rw [hx])
    (fun x l h hx e => by
      unfold stepW at e; rw [hx] at e
      obtain ⟨h1, h2, -⟩ := stepD_kids e
      exact ⟨h1.trans hx, h2.trans hx⟩) i [r] [] (by simp)

/-! ### The pair clauses stay -/

theorem pairF_sub_leaves (w n d : ℕ) (ψ : Fml) :
    ∀ x ∈ leaves (stepD w) d (rootX (List.replicate n (), ψ)), ∀ C ∈ pairF n, C ∈ x.2.2 :=
  forall_mem_leaves (P := fun x : DNode => ∀ C ∈ pairF n, C ∈ x.2.2)
    (fun x l h hx e => by
      obtain ⟨-, -, h3, h4⟩ := stepD_kids e
      exact ⟨fun C hC => h3 C (hx C hC), fun C hC => h4 C (hx C hC)⟩) d _
    (fun C hC => by simpa [rootX] using hC)

/-- An assignment of 2n variables with x_{2u+1} = ¬x_{2u} for all u < n is a doubled assignment. -/
theorem eq_dbl {n : ℕ} (b : Fin (2 * n) → Bool) (hp : ∀ u, u < n → ext b (2 * u + 1) = !ext b (2 * u)) :
    dbl (fun u : Fin n => b ⟨2 * u.val, by omega⟩) = b := by
  funext j
  have hj := j.2
  unfold dbl
  split_ifs with hpar
  · exact congrArg b (Fin.ext (show 2 * (j.val / 2) = j.val by omega))
  · have := hp (j.val / 2) (by omega)
    rw [show 2 * (j.val / 2) + 1 = j.val by omega] at this
    simp only [CountKSat.ext, dif_pos hj, dif_pos (show 2 * (j.val / 2) < 2 * n by omega)] at this
    rw [this]

/-- With the pair clauses, every satisfying assignment has exactly n true variables. -/
theorem cntS_eq_cntN {n : ℕ} {F : Fml} (hF : ∀ C ∈ pairF n, C ∈ F) : cntS (2 * n) n F = cntN (2 * n) F := by
  unfold cntS cntN
  congr 1
  refine Finset.filter_congr fun a _ => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hp := (sat_pairF a).1 fun C hC => h C (hF C hC)
  rw [← eq_dbl a hp]
  exact card_dbl _

end EthCor.GrowTree
