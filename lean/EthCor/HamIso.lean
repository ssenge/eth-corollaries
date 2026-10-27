import EthCor.HamSparseTM
import EthCor.IsoBound

/-! # Cut & Count with the checks of a seed

A seed ω of `EthCor.Iso` (checks on k coordinates, the number m₁ of checks to use, fixings) becomes
clauses on the edge variables of `hcS`. A check with terms c_l ∧ x_{j_l} is a chain of auxiliary
variables a_l = a_{l−1} ⊕ (c_l ∧ x_{j_l}), with a_{−1} = z, the variable that `hcS` sets to false
(`rowF`, width ≤ 3). For the first m₁ checks a unit clause says a_{k−1} = b. A fixing is a unit
clause (`isoF`). The auxiliary variables are determined by the edge variables (`sat_isoF_iff`).
So the formula `hcS n E ++ isoF …` on 5m + n + 2 + mm·k variables has, mod 2, as many satisfying
assignments as there are Hamiltonian cycles that pass the checks and fixings of ω (`iso_parity`).
With the isolation lemma this decides Hamiltonicity with one-sided error (`iso_decide`). -/

namespace EthCor.HamI

open Groundwork.Prog CountKSat GraphProblems Finset EthCor.Ham EthCor.HamS EthCor.HamSTM EthCor.Iso

/-! ### The formula -/

/-- a = p ⊕ (c ∧ x). -/
def xstep (p x a : ℕ) : Bool → Fml
  | true => [[(a, false), (p, true), (x, true)], [(a, false), (p, false), (x, false)],
      [(a, true), (p, false), (x, true)], [(a, true), (p, true), (x, false)]]
  | false => [[(a, false), (p, true)], [(a, true), (p, false)]]

/-- The chain of check i on the list L of (index, coefficient): variable B + i·k + l is the sum of
the first l + 1 terms; z stands for 0. -/
def rowF (z B k i : ℕ) (L : List (ℕ × Bool)) : Fml :=
  (List.range k).flatMap fun l =>
    xstep (if l = 0 then z else B + i * k + (l - 1)) (L.getD l (0, false)).1 (B + i * k + l) (L.getD l (0, false)).2

/-- The checks with their right-hand sides (the first m₁ are used), and the fixings. -/
def isoF (z B k m₁ : ℕ) (rows : List (List (ℕ × Bool) × Bool)) (fixes : List (ℕ × Bool)) : Fml :=
  ((List.range rows.length).flatMap fun i => rowF z B k i (rows.getD i ([], false)).1) ++
    ((List.range (min m₁ rows.length)).map fun i => [(B + i * k + (k - 1), (rows.getD i ([], false)).2)]) ++
    fixes.map fun q => [q]

section Seed

variable {M k t mm : ℕ}

def rowL (ρ : Row M k) : List (ℕ × Bool) := List.ofFn fun l => ((ρ.1 l).val, ρ.2 l)

def rowsOf (ω : Seed M k t mm) : List (List (ℕ × Bool) × Bool) :=
  List.ofFn fun i : Fin mm => (rowL (ω.2.1.1 i), ω.2.1.2 i)

def fixesOf (ω : Seed M k t mm) : List (ℕ × Bool) :=
  (List.finRange M).filterMap fun j => if (ω.2.2 j).1.val = 0 then some (j.val, (ω.2.2 j).2) else none

theorem length_rowsOf (ω : Seed M k t mm) : (rowsOf ω).length = mm := by simp [rowsOf]

theorem getD_rowsOf (ω : Seed M k t mm) {i : ℕ} (hi : i < mm) :
    (rowsOf ω).getD i ([], false) = (rowL (ω.2.1.1 ⟨i, hi⟩), ω.2.1.2 ⟨i, hi⟩) := by
  rw [List.getD_eq_getElem _ _ (by simp [rowsOf]; exact hi)]
  simp [rowsOf]

theorem getD_rowL (ρ : Row M k) {l : ℕ} (hl : l < k) :
    (rowL ρ).getD l (0, false) = ((ρ.1 ⟨l, hl⟩).val, ρ.2 ⟨l, hl⟩) := by
  rw [List.getD_eq_getElem _ _ (by simp [rowL]; exact hl)]
  simp [rowL]

theorem mem_fixesOf (ω : Seed M k t mm) (q : ℕ × Bool) :
    q ∈ fixesOf ω ↔ ∃ j : Fin M, (ω.2.2 j).1.val = 0 ∧ q = (j.val, (ω.2.2 j).2) := by
  simp only [fixesOf, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, h⟩
    by_cases hj : (ω.2.2 j).1.val = 0
    · rw [if_pos hj] at h
      exact ⟨j, hj, (Option.some_inj.1 h).symm⟩
    · rw [if_neg hj] at h
      exact absurd h (by simp)
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by rw [if_pos hj]⟩

end Seed

/-! ### What the formula says -/

theorem sat_xstep (f : ℕ → Bool) (p x a : ℕ) (c : Bool) :
    (∀ C ∈ xstep p x a c, ∃ l ∈ C, f l.1 = l.2) ↔ f a = xor (f p) (c && f x) := by
  cases c
  · simp only [xstep, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat2]
    generalize f a = u, f p = v, f x = w
    cases u <;> cases v <;> cases w <;> decide
  · simp only [xstep, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat3]
    generalize f a = u, f p = v, f x = w
    cases u <;> cases v <;> cases w <;> decide

theorem sat_rowF (f : ℕ → Bool) (z B k i : ℕ) (L : List (ℕ × Bool)) :
    (∀ C ∈ rowF z B k i L, ∃ l ∈ C, f l.1 = l.2) ↔
      ∀ l < k, f (B + i * k + l) = xor (f (if l = 0 then z else B + i * k + (l - 1)))
        ((L.getD l (0, false)).2 && f (L.getD l (0, false)).1) := by
  rw [rowF, forall_flatMap_range]
  exact forall₂_congr fun l _ => sat_xstep f _ _ _ _

theorem sat_isoF (f : ℕ → Bool) (z B k m₁ : ℕ) (rows : List (List (ℕ × Bool) × Bool)) (fixes : List (ℕ × Bool)) :
    (∀ C ∈ isoF z B k m₁ rows fixes, ∃ l ∈ C, f l.1 = l.2) ↔
      (∀ i < rows.length, ∀ l < k, f (B + i * k + l) = xor (f (if l = 0 then z else B + i * k + (l - 1)))
        (((rows.getD i ([], false)).1.getD l (0, false)).2 && f ((rows.getD i ([], false)).1.getD l (0, false)).1)) ∧
      (∀ i < min m₁ rows.length, f (B + i * k + (k - 1)) = (rows.getD i ([], false)).2) ∧
      ∀ q ∈ fixes, f q.1 = q.2 := by
  rw [isoF, List.forall_mem_append, List.forall_mem_append, forall_flatMap_range, List.forall_mem_map,
    List.forall_mem_map]
  have h2 : (∀ i ∈ List.range (min m₁ rows.length),
      ∃ l ∈ [(B + i * k + (k - 1), (rows.getD i ([], false)).2)], f l.1 = l.2) ↔
      ∀ i < min m₁ rows.length, f (B + i * k + (k - 1)) = (rows.getD i ([], false)).2 := by simp
  have h3 : (∀ q ∈ fixes, ∃ l ∈ [q], f l.1 = l.2) ↔ ∀ q ∈ fixes, f q.1 = q.2 := by simp
  rw [h2, h3, and_assoc]
  exact and_congr (forall₂_congr fun i _ => sat_rowF f _ _ _ _ _) Iff.rfl

/-- The sum of the first l + 1 terms c ∧ x_j of L. -/
def px (f : ℕ → Bool) (L : List (ℕ × Bool)) : ℕ → Bool
  | 0 => (L.getD 0 (0, false)).2 && f (L.getD 0 (0, false)).1
  | l + 1 => xor (px f L l) ((L.getD (l + 1) (0, false)).2 && f (L.getD (l + 1) (0, false)).1)

theorem px_congr {f f' : ℕ → Bool} {L : List (ℕ × Bool)}
    (h : ∀ l, f (L.getD l (0, false)).1 = f' (L.getD l (0, false)).1) : ∀ l, px f L l = px f' L l
  | 0 => by simp only [px, h 0]
  | l + 1 => by simp only [px, h (l + 1), px_congr h l]

/-- The chain computes the partial sums. -/
theorem chain_iff (f : ℕ → Bool) (z B k i : ℕ) (L : List (ℕ × Bool)) (hz : f z = false) :
    (∀ l < k, f (B + i * k + l) = xor (f (if l = 0 then z else B + i * k + (l - 1)))
        ((L.getD l (0, false)).2 && f (L.getD l (0, false)).1)) ↔
      ∀ l < k, f (B + i * k + l) = px f L l := by
  constructor
  · intro h l hl
    induction l with
    | zero =>
      have := h 0 hl
      rw [if_pos rfl, hz, Bool.false_xor] at this
      exact this
    | succ l ih =>
      have := h (l + 1) hl
      rw [if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, ih (by omega)] at this
      exact this
  · intro h l hl
    cases l with
    | zero =>
      rw [h 0 hl, if_pos rfl, hz, Bool.false_xor]
      rfl
    | succ l =>
      rw [h (l + 1) hl, if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, h l (by omega)]
      rfl

theorem sat_isoF' (f : ℕ → Bool) (z B k m₁ : ℕ) (rows : List (List (ℕ × Bool) × Bool)) (fixes : List (ℕ × Bool))
    (hz : f z = false) (hk : 1 ≤ k) :
    (∀ C ∈ isoF z B k m₁ rows fixes, ∃ l ∈ C, f l.1 = l.2) ↔
      (∀ i < rows.length, ∀ l < k, f (B + i * k + l) = px f (rows.getD i ([], false)).1 l) ∧
      (∀ i < min m₁ rows.length, px f (rows.getD i ([], false)).1 (k - 1) = (rows.getD i ([], false)).2) ∧
      ∀ q ∈ fixes, f q.1 = q.2 := by
  rw [sat_isoF]
  have hc : (∀ i < rows.length, ∀ l < k, f (B + i * k + l) = xor (f (if l = 0 then z else B + i * k + (l - 1)))
        (((rows.getD i ([], false)).1.getD l (0, false)).2 && f ((rows.getD i ([], false)).1.getD l (0, false)).1)) ↔
      ∀ i < rows.length, ∀ l < k, f (B + i * k + l) = px f (rows.getD i ([], false)).1 l :=
    forall₂_congr fun i _ => chain_iff f z B k i _ hz
  rw [hc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => (h1 i (lt_of_lt_of_le hi (min_le_right _ _)) (k - 1) (by omega)).symm.trans (h2 i hi), h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => (h1 i (lt_of_lt_of_le hi (min_le_right _ _)) (k - 1) (by omega)).trans (h2 i hi), h3⟩

/-! ### The partial sums and the checks -/

theorem bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by revert h; cases a <;> cases b <;> decide

theorem bz_px (f : ℕ → Bool) (L : List (ℕ × Bool)) : ∀ l, bz (px f L l) =
    ∑ l' ∈ range (l + 1), (if ((L.getD l' (0, false)).2 && f (L.getD l' (0, false)).1) = true then (1 : ZMod 2) else 0)
  | 0 => by rw [Finset.sum_range_one]; rfl
  | l + 1 => by
    rw [Finset.sum_range_succ, ← bz_px f L l]
    show bz (xor (px f L l) _) = _
    rw [bz_xor]
    rfl

theorem rv_eq {M k : ℕ} (ρ : Row M k) (f : ℕ → Bool) (hk : 1 ≤ k) :
    rv ρ (fun j => f j.val) = bz (px f (rowL ρ) (k - 1)) := by
  rw [bz_px, Nat.sub_add_cancel hk, ← Fin.sum_univ_eq_sum_range (fun l =>
    if (((rowL ρ).getD l (0, false)).2 && f ((rowL ρ).getD l (0, false)).1) = true then (1 : ZMod 2) else 0) k]
  unfold rv
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [getD_rowL ρ l.2]

/-! ### The auxiliary variables are determined -/

/-- The values of the chains for the assignment y. -/
def auxT {M k t mm N₀ : ℕ} (ω : Seed M k t mm) (y : Fin N₀ → Bool) (t' : Fin (mm * k)) : Bool :=
  px (ext y) ((rowsOf ω).getD (t'.val / k) ([], false)).1 (t'.val % k)

section Det

variable {N₀ M k t mm : ℕ}

theorem auxT_iff (hk : 1 ≤ k) (ω : Seed M k t mm) (y : Fin N₀ → Bool) (g : Fin (mm * k) → Bool)
    (hpx : ∀ i < mm, ∀ l, px (ext (Fin.append y g)) ((rowsOf ω).getD i ([], false)).1 l =
      px (ext y) ((rowsOf ω).getD i ([], false)).1 l) :
    (∀ i < (rowsOf ω).length, ∀ l < k, ext (Fin.append y g) (N₀ + i * k + l) =
        px (ext (Fin.append y g)) ((rowsOf ω).getD i ([], false)).1 l) ↔ g = auxT ω y := by
  have hk0 : 0 < k := hk
  have hge : ∀ i l, ext (Fin.append y g) (N₀ + i * k + l) = ext g (i * k + l) := fun i l => by
    rw [add_assoc]; exact ext_append_ge y g _
  rw [length_rowsOf]
  constructor
  · intro h
    funext t'
    have htk : t'.val / k < mm := (Nat.div_lt_iff_lt_mul hk0).2 t'.2
    have hmod : t'.val % k < k := Nat.mod_lt _ hk0
    have e : t'.val / k * k + t'.val % k = t'.val := by rw [mul_comm]; exact Nat.div_add_mod _ _
    have h1 := h _ htk _ hmod
    rw [hge, hpx _ htk, e, ext_fin] at h1
    exact h1
  · rintro rfl i hi l hl
    have h1 : i * k + l < mm * k := by
      calc i * k + l < i * k + k := by omega
        _ = (i + 1) * k := by ring
        _ ≤ mm * k := Nat.mul_le_mul_right k hi
    rw [hge, hpx i hi]
    have e1 : ext (auxT ω y) (i * k + l) = auxT ω y ⟨i * k + l, h1⟩ := by simp only [CountKSat.ext, dif_pos h1]
    rw [e1]
    show px (ext y) ((rowsOf ω).getD ((i * k + l) / k) ([], false)).1 ((i * k + l) % k) = _
    rw [show (i * k + l) / k = i by rw [add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt hl, zero_add],
      show (i * k + l) % k = l by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]]

theorem rows_iff (hk : 1 ≤ k) (ω : Seed M k t mm) (y : Fin N₀ → Bool) (g : Fin (mm * k) → Bool)
    (hpx : ∀ i < mm, ∀ l, px (ext (Fin.append y g)) ((rowsOf ω).getD i ([], false)).1 l =
      px (ext y) ((rowsOf ω).getD i ([], false)).1 l) :
    (∀ i < min ω.1.val (rowsOf ω).length, px (ext (Fin.append y g)) ((rowsOf ω).getD i ([], false)).1 (k - 1) =
        ((rowsOf ω).getD i ([], false)).2) ↔ rowsOK ω.1.val ω.2.1.1 ω.2.1.2 (fun j => ext y j.val) := by
  have hm₁ : ω.1.val ≤ mm := Nat.lt_succ_iff.1 ω.1.2
  rw [length_rowsOf, min_eq_left hm₁]
  constructor
  · intro h i hi
    have := h i.val hi
    rw [hpx i.val i.2, getD_rowsOf ω i.2] at this
    simp only [Fin.eta] at this
    rw [rv_eq _ _ hk, this]
  · intro h i hi
    have hi' : i < mm := lt_of_lt_of_le hi hm₁
    rw [hpx i hi', getD_rowsOf ω hi']
    have := h ⟨i, hi'⟩ hi
    rw [rv_eq _ _ hk] at this
    exact bz_inj this

theorem fixes_iff (hM : M ≤ N₀) (ω : Seed M k t mm) (y : Fin N₀ → Bool) (g : Fin (mm * k) → Bool)
    (hlt : ∀ a < N₀, ext (Fin.append y g) a = ext y a) :
    (∀ q ∈ fixesOf ω, ext (Fin.append y g) q.1 = q.2) ↔ fixOK ω.2.2 (fun j => ext y j.val) := by
  constructor
  · intro h j hj
    have := h (j.val, (ω.2.2 j).2) ((mem_fixesOf ω _).2 ⟨j, hj, rfl⟩)
    rwa [hlt _ (by omega)] at this
  · intro h q hq
    obtain ⟨j, hj, rfl⟩ := (mem_fixesOf ω q).1 hq
    rw [hlt _ (by omega)]
    exact h j hj

/-- **What the formula of a seed says**, for the edge assignment y with z false: y passes the checks
and the fixings, and the auxiliary variables are the partial sums. -/
theorem sat_isoF_iff (hM : M ≤ N₀) (hk : 1 ≤ k) (ω : Seed M k t mm) {z : ℕ} (hz : z < N₀)
    (y : Fin N₀ → Bool) (g : Fin (mm * k) → Bool) (hyz : ext y z = false) :
    (∀ C ∈ isoF z N₀ k ω.1.val (rowsOf ω) (fixesOf ω), ∃ l ∈ C, ext (Fin.append y g) l.1 = l.2) ↔
      H ω (fun j => ext y j.val) ∧ g = auxT ω y := by
  have hlt : ∀ a < N₀, ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt y g ha
  have hz' : ext (Fin.append y g) z = false := by rw [hlt z hz]; exact hyz
  have hidx : ∀ i < mm, ∀ l, (((rowsOf ω).getD i ([], false)).1.getD l (0, false)).1 < N₀ := by
    intro i hi l
    refine getD_prop (P := fun q : ℕ × Bool => q.1 < N₀) (by show 0 < N₀; omega) (fun q hq => ?_) l
    rw [getD_rowsOf ω hi] at hq
    dsimp only at hq
    rw [rowL, List.mem_ofFn] at hq
    obtain ⟨l', rfl⟩ := hq
    exact lt_of_lt_of_le ((ω.2.1.1 ⟨i, hi⟩).1 l').2 hM
  have hpx : ∀ i < mm, ∀ l, px (ext (Fin.append y g)) ((rowsOf ω).getD i ([], false)).1 l =
      px (ext y) ((rowsOf ω).getD i ([], false)).1 l := fun i hi =>
    px_congr fun l => hlt _ (hidx i hi l)
  rw [sat_isoF' _ _ _ _ _ _ _ hz' hk, auxT_iff hk ω y g hpx, rows_iff hk ω y g hpx, fixes_iff hM ω y g hlt]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨b, c⟩, a⟩, fun ⟨⟨b, c⟩, a⟩ => ⟨a, b, c⟩⟩

end Det

/-! ### The count -/

theorem card_append {N A : ℕ} (Φ : (Fin (N + A) → Bool) → Prop) (Ψ : (Fin N → Bool) → Prop)
    [DecidablePred Φ] [DecidablePred Ψ] (aux : (Fin N → Bool) → Fin A → Bool)
    (h : ∀ y g, Φ (Fin.append y g) ↔ Ψ y ∧ g = aux y) :
    (univ.filter Φ).card = (univ.filter Ψ).card := by
  rw [Finset.card_equiv (Fin.appendEquiv N A).symm
    (t := univ.filter fun p : (Fin N → Bool) × (Fin A → Bool) => Ψ p.1 ∧ p.2 = aux p.1)]
  · refine Finset.card_nbij' (fun p => p.1) (fun y => (y, aux y)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact hp.1
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      exact ⟨hy, trivial⟩
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
      exact Prod.ext rfl hp.2.symm
    · intro y _
      rfl
  · intro b
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨p, rfl⟩ : ∃ p, b = Fin.appendEquiv N A p := ⟨_, ((Fin.appendEquiv _ _).apply_symm_apply b).symm⟩
    rw [Equiv.symm_apply_apply]
    have hb : (Fin.appendEquiv N A) p = Fin.append p.1 p.2 := funext fun a => Fin.appendEquiv_apply _ _ _ _
    rw [hb, h]

theorem sat_congr {f f' : ℕ → Bool} {φ : Fml} (h : ∀ C ∈ φ, ∀ l ∈ C, f l.1 = f' l.1) :
    (∀ C ∈ φ, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ C ∈ φ, ∃ l ∈ C, f' l.1 = l.2 :=
  forall₂_congr fun C hC => exists_congr fun l => and_congr_right fun hl => by rw [h C hC l hl]

theorem cnt_stepA {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {k t mm : ℕ}
    (hk : 1 ≤ k) (ω : Seed E.length k t mm) :
    cntN (E.length + n + (4 * E.length + 2) + mm * k)
        (hcS n E ++ isoF (zC E n) (E.length + n + (4 * E.length + 2)) k ω.1.val (rowsOf ω) (fixesOf ω)) =
      (univ.filter fun y : Fin (E.length + n + (4 * E.length + 2)) → Bool =>
        (∀ C ∈ hcS n E, ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val)).card := by
  unfold cntN
  refine card_append _ _ (auxT ω) fun y g => ?_
  rw [List.forall_mem_append,
    sat_congr (f' := ext y) (fun C hC l hl => ext_append_lt y g ((hcS_clause hn hE hC).2 l hl))]
  have hzf : (∀ C ∈ hcS n E, ∃ l ∈ C, ext y l.1 = l.2) → ext y (zC E n) = false := fun h =>
    ((sat_hcS _ n E).1 h).2.2.1
  have hz : zC E n < E.length + n + (4 * E.length + 2) := by unfold zC; omega
  constructor
  · rintro ⟨h1, h2⟩
    have := (sat_isoF_iff (by omega) hk ω hz y g (hzf h1)).1 h2
    exact ⟨⟨h1, this.1⟩, this.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (sat_isoF_iff (by omega) hk ω hz y g (hzf h1)).2 ⟨h2, h3⟩⟩

theorem cnt_stepB {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {k t mm : ℕ}
    (ω : Seed E.length k t mm) :
    (univ.filter fun y : Fin (E.length + n + (4 * E.length + 2)) → Bool =>
        (∀ C ∈ hcS n E, ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val)).card =
      (univ.filter fun y : Fin (E.length + n) → Bool =>
        (∀ C ∈ hcF n E, ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val)).card := by
  refine card_append _ _ (fun y t => auxOf E (ext y) t.val) fun y g => ?_
  have hx : (fun j : Fin E.length => ext (Fin.append y g) j.val) = fun j => ext y j.val :=
    funext fun j => ext_append_lt y g (by omega)
  rw [sat_append_iff hn hE, hx, funext_iff]
  tauto

/-- The choices of edges with every vertex on two of them and property P, counted with their side
maps. -/
theorem card_hcF_P (n : ℕ) (E : List (ℕ × ℕ)) (P : (Fin E.length → Bool) → Prop) [DecidablePred P] :
    (univ.filter fun y : Fin (E.length + n) → Bool =>
        (∀ C ∈ hcF n E, ∃ l ∈ C, ext y l.1 = l.2) ∧ P (fun j => ext y j.val)).card =
      ∑ x : Fin E.length → Bool, if (∀ v < n, (inc E v).countP (ext x) = 2) ∧ P x then sides n E x else 0 := by
  rw [Finset.card_equiv (Fin.appendEquiv E.length n).symm (t := univ.filter fun p : (Fin E.length → Bool) × (Fin n → Bool) =>
      ((∀ v < n, (inc E v).countP (ext p.1) = 2) ∧ P p.1) ∧
      ((∀ i < E.length, ext p.1 i = true → ext p.2 (E.getD i (0, 0)).1 = ext p.2 (E.getD i (0, 0)).2) ∧ ext p.2 0 = false))]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [sides, Finset.card_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : (∀ i < E.length, ext x i = true → ext s (E.getD i (0, 0)).1 = ext s (E.getD i (0, 0)).2) ∧
          ext s 0 = false
      · rw [if_pos ⟨hx, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2), if_neg h]
    · simp [hx]
  · intro b
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨p, rfl⟩ : ∃ p, b = Fin.appendEquiv E.length n p :=
      ⟨_, ((Fin.appendEquiv E.length n).apply_symm_apply b).symm⟩
    rw [Equiv.symm_apply_apply]
    have hb : (Fin.appendEquiv E.length n) p = Fin.append p.1 p.2 := funext fun a => Fin.appendEquiv_apply _ _ _ _
    rw [hb, sat_hcF]
    have h1 : ∀ v, (inc E v).countP (ext (Fin.append p.1 p.2)) = (inc E v).countP (ext p.1) := fun v =>
      List.countP_congr fun i hi => by rw [ext_append_lt _ _ (lt_of_mem_inc hi)]
    have h2 : ∀ i < E.length, ext (Fin.append p.1 p.2) i = ext p.1 i := fun i hi => ext_append_lt _ _ hi
    have h3 : ext (Fin.append p.1 p.2) E.length = ext p.2 0 := by
      have := ext_append_ge p.1 p.2 0; rwa [Nat.add_zero] at this
    have h4 : (fun j : Fin E.length => ext (Fin.append p.1 p.2) j.val) = p.1 :=
      funext fun j => by rw [h2 j.val j.2, ext_fin]
    rw [h4]
    simp only [h1, ext_append_ge, h3]
    constructor
    · rintro ⟨⟨hd, he, hs⟩, hP⟩
      exact ⟨⟨hd, hP⟩, fun i hi e => he i hi (by rw [h2 i hi]; exact e), hs⟩
    · rintro ⟨⟨hd, hP⟩, he, hs⟩
      exact ⟨⟨hd, fun i hi e => he i hi (by rw [← h2 i hi]; exact e), hs⟩, hP⟩

open Classical in
/-- The Hamiltonian cycles of G as choices of edges of its edge list. -/
noncomputable def hcSet {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin (edges n (matrix G)).length → Bool) :=
  univ.filter fun x => (∀ v < n, (inc (edges n (matrix G)) v).countP (ext x) = 2) ∧
    (subG n (edges n (matrix G)) x).Connected

theorem card_hcSet {n : ℕ} (G : SimpleGraph (Fin n)) : (hcSet G).card = numHamCycles G := card_hc stAdj G

open Classical in
theorem parity_P {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (P : (Fin (edges n (matrix G)).length → Bool) → Prop) [DecidablePred P] :
    (∑ x : Fin (edges n (matrix G)).length → Bool,
        if (∀ v < n, (inc (edges n (matrix G)) v).countP (ext x) = 2) ∧ P x then sides n (edges n (matrix G)) x else 0) % 2 =
      ((hcSet G).filter P).card % 2 := by
  have hE := edges_bound n (matrix G)
  unfold hcSet
  rw [Finset.filter_filter, Finset.card_filter, Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have hs : sides n (edges n (matrix G)) x = (univ.filter fun s : Fin n → Bool =>
      s ⟨0, hn⟩ = false ∧ ∀ u v, (subG n (edges n (matrix G)) x).Adj u v → s u = s v).card := by
    rw [sides]; congr 1; refine Finset.filter_congr fun s _ => ?_
    have h0 : ext s 0 = s ⟨0, hn⟩ := ext_fin s ⟨0, hn⟩
    rw [cons_iff hE, h0, and_comm]
  by_cases h1 : ∀ v < n, (inc (edges n (matrix G)) v).countP (ext x) = 2
  · by_cases hP : P x
    · rw [if_pos ⟨h1, hP⟩, hs, parity_sides hn]
      by_cases h2 : (subG n (edges n (matrix G)) x).Connected
      · rw [if_pos h2, if_pos ⟨⟨h1, h2⟩, hP⟩]
      · rw [if_neg h2, if_neg fun h => h2 h.1.2]
    · rw [if_neg fun h => hP h.2, if_neg fun h => hP h.2]
  · rw [if_neg fun h => h1 h.1, if_neg fun h => h1 h.1.1]

/-- The number of variables of the formula of a seed. -/
def NI (n m mm k : ℕ) : ℕ := m + n + (4 * m + 2) + mm * k

/-- The formula of the graph with edge list E and the seed ω. -/
def hcI {M k t mm : ℕ} (n : ℕ) (E : List (ℕ × ℕ)) (ω : Seed M k t mm) : Fml :=
  hcS n E ++ isoF (zC E n) (E.length + n + (4 * E.length + 2)) k ω.1.val (rowsOf ω) (fixesOf ω)

/-- **Cut & Count with the checks of a seed**: the number of satisfying assignments has the parity
of the number of Hamiltonian cycles that pass the checks and the fixings of ω. -/
theorem iso_parity {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) {k t mm : ℕ} (hk : 1 ≤ k)
    (ω : Seed (edges n (matrix G)).length k t mm) :
    cntN (NI n (edges n (matrix G)).length mm k) (hcI n (edges n (matrix G)) ω) % 2 =
      ((hcSet G).filter (H ω)).card % 2 := by
  have hE := edges_bound n (matrix G)
  rw [NI, hcI, cnt_stepA hn hE hk ω, cnt_stepB hn hE ω, card_hcF_P, parity_P hn G]

/-! ### Deciding Hamiltonicity with one-sided error -/

open Classical in
/-- A Hamiltonian cycle has n edges. -/
theorem le_length_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) {x : Fin (edges n (matrix G)).length → Bool}
    (hx : x ∈ hcSet G) : n ≤ (edges n (matrix G)).length := by
  have hE := edges_bound n (matrix G)
  have hnd := edges_nodup n (matrix G)
  have hd : ∀ v, (subG n (edges n (matrix G)) x).degree v = 2 := fun v => by
    rw [degree_subG hE hnd]; exact (mem_filter.1 hx).2.1 v v.2
  have h2 : 2 * n = 2 * (subG n (edges n (matrix G)) x).edgeFinset.card := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]; simp [hd, mul_comm]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · omega
  let f : Fin (edges n (matrix G)).length → Sym2 (Fin n) := fun i =>
    s(⟨(edges n (matrix G))[i].1 % n, Nat.mod_lt _ hn⟩, ⟨(edges n (matrix G))[i].2 % n, Nat.mod_lt _ hn⟩)
  have hsub : (subG n (edges n (matrix G)) x).edgeFinset ⊆ univ.image f := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨-, ⟨i, -, e⟩ | ⟨i, -, e⟩⟩ := subG_adj.1 he
      · refine mem_image.2 ⟨i, mem_univ _, ?_⟩
        simp only [f, e, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt v.2]
      · refine mem_image.2 ⟨i, mem_univ _, ?_⟩
        simp only [f, e, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt v.2]
        exact Sym2.eq_swap
  have h3 := (card_le_card hsub).trans card_image_le
  rw [card_univ, Fintype.card_fin] at h3
  omega

open Classical in
/-- **Hamiltonian cycle with one-sided error.** For every δ > 0 there are k and t such that, for all
graphs G on n ≥ n₀ vertices with m edges and the seeds ω of `Seed m k t (3m + 3)`: if G has no
Hamiltonian cycle, the formula `hcI` has an even number of satisfying assignments for every ω; if
G has one, it has an odd number for at least a 2^{−δm} fraction of the seeds. -/
theorem iso_decide (δ : ℝ) (hδ : 0 < δ) : ∃ k t : ℕ, 1 ≤ k ∧ 1 ≤ t ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n₀ ≤ n →
      (numHamCycles G = 0 → ∀ ω : Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3),
        cntN (NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k)
          (hcI n (edges n (matrix G)) ω) % 2 = 0) ∧
      (0 < numHamCycles G →
        (Fintype.card (Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3)) : ℝ) ≤
          2 ^ (δ * (edges n (matrix G)).length) *
            (univ.filter fun ω : Seed (edges n (matrix G)).length k t (3 * (edges n (matrix G)).length + 3) =>
              cntN (NI n (edges n (matrix G)).length (3 * (edges n (matrix G)).length + 3) k)
                (hcI n (edges n (matrix G)) ω) % 2 = 1).card) := by
  obtain ⟨k, t, hk, ht, M₀, hM₀⟩ := isolation δ hδ
  refine ⟨k, t, hk, ht, M₀ + 1, fun n G hn => ⟨fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · rw [iso_parity (by omega) G hk ω]
    have : hcSet G = ∅ := card_eq_zero.1 (by rw [card_hcSet]; exact h0)
    rw [this]; simp
  · have hS : (hcSet G).Nonempty := card_pos.1 (by rw [card_hcSet]; exact hpos)
    obtain ⟨x, hx⟩ := hS
    have hnm := le_length_of_mem G hx
    have h := hM₀ (edges n (matrix G)).length (by omega) (hcSet G) ⟨x, hx⟩
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast card_le_card fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      rw [iso_parity (by omega) G hk ω, hω]

end EthCor.HamI
