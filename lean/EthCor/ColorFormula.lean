import GraphProblems.Color
import GraphProblems.Read

/-! # k-colorings as a CNF with colors written in binary

Vertex v gets b = ⌈log₂ k⌉ variables x_{v·b+j}, the bits of its color. Clauses: no vertex spells a
number in [k, 2^b); the two ends of an edge do not spell the same color c < k; every variable occurs
(tautologies x ∨ ¬x); four padding variables x_{n·b}, …, x_{n·b+3} are forced true. So the formula has
n·b + 4 variables, width 2b, and exactly as many satisfying assignments as G has proper k-colorings
(`cntN_colB`). With b = O(log k) instead of k variables per vertex, the uniform bound of the Main
Theorem stays subexponential for k up to 2^{(log n)^{1/6-ε}}. -/

namespace EthCor

open Groundwork Groundwork.Prog CountKSat GraphProblems Finset

/-- Bits per vertex: ⌊log₂(2(k−1))⌋, which is ⌈log₂ k⌉ for k ≥ 2. -/
def nb (k : ℕ) : ℕ := Nat.log2 (2 * (k - 1))

/-- The clause «the b bits of vertex v do not spell the number c». -/
def forbid (b v c : ℕ) : List (ℕ × Bool) := (List.range b).map fun j => (v * b + j, !c.testBit j)

/-- The formula of the proper k-colorings, colors in binary. -/
def colB (k n : ℕ) (m : List Bool) : Fml :=
  ((List.range n).flatMap fun v =>
      ((List.range (2 * k)).filter fun c => decide (k ≤ c) && decide (Nat.log2 c < nb k)).map fun c => forbid (nb k) v c) ++
  (((pairs n).filter fun p => adjB n m p.1 p.2).flatMap fun p =>
      (List.range k).map fun c => forbid (nb k) p.1 c ++ forbid (nb k) p.2 c) ++
  ((List.range (n * nb k)).map fun i => [(i, true), (i, false)]) ++
  ((List.range 4).map fun i => [(n * nb k + i, true)])

/-! ### Numbers from bits -/

/-- The number spelled by the bits g 0, …, g (b−1), lowest first. -/
def val (b : ℕ) (g : ℕ → Bool) : ℕ := ∑ j ∈ range b, if g j then 2 ^ j else 0

theorem val_succ (b : ℕ) (g : ℕ → Bool) : val (b + 1) g = val b g + if g b then 2 ^ b else 0 :=
  sum_range_succ _ _

theorem val_lt (b : ℕ) (g : ℕ → Bool) : val b g < 2 ^ b := by
  induction b with
  | zero => simp [val]
  | succ b ih =>
    rw [val_succ, pow_succ]
    split <;> omega

theorem testBit_val (b : ℕ) (g : ℕ → Bool) (j : ℕ) : (val b g).testBit j = (decide (j < b) && g j) := by
  induction b with
  | zero => simp [val]
  | succ b ih =>
    have hlt := val_lt b g
    rw [val_succ]
    by_cases hg : g b
    · rw [if_pos hg, add_comm]
      rcases Nat.lt_trichotomy j b with h | rfl | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        simp [h, Nat.lt_succ_of_lt h]
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hlt]
        simp [hg]
      · have h2 : 2 ^ b + val b g < 2 ^ j :=
          lt_of_lt_of_le (by rw [pow_succ]; omega : 2 ^ b + val b g < 2 ^ (b + 1)) (Nat.pow_le_pow_right (by omega) h)
        rw [Nat.testBit_eq_false_of_lt h2]
        simp [show ¬ j < b + 1 by omega]
    · rw [if_neg hg, add_zero, ih]
      by_cases h : j < b
      · simp [h, Nat.lt_succ_of_lt h]
      · by_cases h' : j = b
        · subst h'; simp [hg]
        · simp [h, show ¬ j < b + 1 by omega]

/-- The bits spell c exactly if they agree with the bits of c. -/
theorem val_eq_iff {b c : ℕ} (hc : c < 2 ^ b) (g : ℕ → Bool) : val b g = c ↔ ∀ j < b, g j = c.testBit j := by
  constructor
  · rintro rfl j hj
    rw [testBit_val]; simp [hj]
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [testBit_val]
    by_cases hj : j < b
    · simp [hj, h j hj]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [hj]

/-! ### What the formula says -/

/-- The color that an assignment f spells at vertex v. -/
def colOf (b : ℕ) (f : ℕ → Bool) (v : ℕ) : ℕ := val b fun j => f (v * b + j)

theorem sat_forbid {b c : ℕ} (hc : c < 2 ^ b) (f : ℕ → Bool) (v : ℕ) :
    (∃ l ∈ forbid b v c, f l.1 = l.2) ↔ colOf b f v ≠ c := by
  rw [colOf, Ne, val_eq_iff hc]
  simp only [forbid, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, h⟩ hall
    rw [hall j hj] at h
    cases hb : c.testBit j <;> simp [hb] at h
  · intro h
    push Not at h
    obtain ⟨j, hj, hne⟩ := h
    refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
    cases hb : c.testBit j <;> cases hf : f (v * b + j) <;> simp_all

theorem two_pow_nb_le {k : ℕ} (hk : 2 ≤ k) : 2 ^ nb k ≤ 2 * k := by
  have := Nat.log2_self_le (show 2 * (k - 1) ≠ 0 by omega)
  unfold nb; omega

theorem le_two_pow_nb {k : ℕ} (hk : 2 ≤ k) : k ≤ 2 ^ nb k := by
  have := Nat.lt_log2_self (n := 2 * (k - 1))
  unfold nb; omega

theorem one_le_nb {k : ℕ} (hk : 2 ≤ k) : 1 ≤ nb k := by
  have h := le_two_pow_nb hk
  by_contra h0
  rw [show nb k = 0 by omega, pow_zero] at h
  omega

/-- What the formula says, for k ≥ 2. -/
theorem sat_colB {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (m : List Bool) (f : ℕ → Bool) :
    (∀ C ∈ colB k n m, ∃ l ∈ C, f l.1 = l.2) ↔
      (∀ v < n, colOf (nb k) f v < k) ∧
      (∀ u < n, ∀ v < n, adjB n m u v = true → colOf (nb k) f u ≠ colOf (nb k) f v) ∧
      ∀ i < 4, f (n * nb k + i) = true := by
  have h2 := two_pow_nb_le hk
  have hlt : ∀ v, colOf (nb k) f v < 2 ^ nb k := fun v => val_lt _ _
  simp only [colB, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, and_imp]
  constructor
  · rintro ⟨⟨⟨hA, hB⟩, -⟩, hD⟩
    refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun i hi => ?_⟩
    · by_contra hge
      push Not at hge
      have hc := hlt v
      have hlog : Nat.log2 (colOf (nb k) f v) < nb k := (Nat.log2_lt (by omega)).2 hc
      exact (sat_forbid hc f v).1 (hA v hv _ (by omega) hge hlog) rfl
    · intro heq
      have hc : colOf (nb k) f u < k := by
        by_contra hge
        push Not at hge
        have hc := hlt u
        exact (sat_forbid hc f u).1 (hA u hu _ (by omega) hge ((Nat.log2_lt (by omega)).2 hc)) rfl
      have hck : colOf (nb k) f u < 2 ^ nb k := hlt u
      obtain ⟨l, hl, hfl⟩ := hB (u, v) (GraphProblems.Color.mem_pairs.2 ⟨hu, hv⟩) huv _ hc
      rcases List.mem_append.1 hl with hl | hl
      · exact (sat_forbid hck f u).1 ⟨l, hl, hfl⟩ rfl
      · exact (sat_forbid hck f v).1 ⟨l, hl, hfl⟩ heq.symm
    · obtain ⟨l, hl, hfl⟩ := hD i hi
      rw [List.mem_singleton] at hl
      subst hl; exact hfl
  · rintro ⟨hA, hB, hD⟩
    refine ⟨⟨⟨fun v hv c _ hkc hlog => ?_, fun p hp hadj c hc => ?_⟩, fun i _ => ⟨(i, f i), ?_, rfl⟩⟩,
      fun i hi => ⟨_, List.mem_singleton.2 rfl, hD i hi⟩⟩
    · have hc2 : c < 2 ^ nb k := (Nat.log2_lt (by omega)).1 hlog
      exact (sat_forbid hc2 f v).2 (by have := hA v hv; omega)
    · have hp' := GraphProblems.Color.mem_pairs.1 hp
      have hc2 : c < 2 ^ nb k := lt_of_lt_of_le hc (le_two_pow_nb hk)
      by_cases hu : colOf (nb k) f p.1 = c
      · obtain ⟨l, hl, hfl⟩ := (sat_forbid hc2 f p.2).2 (fun h => hB p.1 hp'.1 p.2 hp'.2 hadj (hu.trans h.symm))
        exact ⟨l, List.mem_append_right _ hl, hfl⟩
      · obtain ⟨l, hl, hfl⟩ := (sat_forbid hc2 f p.1).2 hu
        exact ⟨l, List.mem_append_left _ hl, hfl⟩
    · cases f i <;> simp

/-! ### Counting -/

theorem ext_val' {n : ℕ} (a : Fin n → Bool) (i : Fin n) : ext a i.val = a i := by simp [CountKSat.ext]

theorem idx_lt' {n b v j : ℕ} (hv : v < n) (hj : j < b) : v * b + j < n * b + 4 := by
  have := GraphProblems.Color.idx_lt hv hj; omega

/-- The assignment of a map from the vertices to the colors. -/
def asgB {n k : ℕ} (col : Fin n → Fin k) (x : Fin (n * nb k + 4)) : Bool :=
  if h : x.val < n * nb k then
    (col ⟨x.val / nb k, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h (mul_comm n (nb k)))⟩).val.testBit (x.val % nb k)
  else true

theorem ext_asgB {n k : ℕ} (col : Fin n → Fin k) (v : Fin n) {j : ℕ} (hj : j < nb k) :
    ext (asgB col) (v * nb k + j) = (col v).val.testBit j := by
  have h1 : (v.val * nb k + j) / nb k = v.val := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, add_zero]
  have h2 : (v.val * nb k + j) % nb k = j := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [CountKSat.ext, dif_pos (idx_lt' v.2 hj), asgB, dif_pos (GraphProblems.Color.idx_lt v.2 hj)]
  simp only [h1, h2]

theorem colOf_asgB {n k : ℕ} (hk : 2 ≤ k) (col : Fin n → Fin k) (v : Fin n) :
    colOf (nb k) (ext (asgB col)) v = (col v).val := by
  rw [colOf, val_eq_iff (lt_of_lt_of_le (col v).2 (le_two_pow_nb hk))]
  exact fun j hj => ext_asgB col v hj

theorem ext_asgB_pad {n k : ℕ} (col : Fin n → Fin k) {i : ℕ} (hi : i < 4) : ext (asgB col) (n * nb k + i) = true := by
  rw [CountKSat.ext, dif_pos (by omega), asgB, dif_neg (by simp)]

theorem sat_asgB {k : ℕ} (hk : 2 ≤ k) (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) (col : G.Coloring (Fin k)) :
    ∀ C ∈ colB k n (matrix G), ∃ l ∈ C, ext (asgB col) l.1 = l.2 := by
  rw [sat_colB hk]
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun i hi => ext_asgB_pad col hi⟩
  · rw [show v = (⟨v, hv⟩ : Fin n).val from rfl, colOf_asgB hk]; exact (col _).2
  · rw [show u = (⟨u, hu⟩ : Fin n).val from rfl, show v = (⟨v, hv⟩ : Fin n).val from rfl, colOf_asgB hk, colOf_asgB hk]
    intro h
    exact col.valid ((hAdj n G ⟨u, hu⟩ ⟨v, hv⟩).1 huv) (Fin.ext h)

theorem asgB_injective {k : ℕ} (hk : 2 ≤ k) {n : ℕ} :
    Function.Injective (asgB : (Fin n → Fin k) → Fin (n * nb k + 4) → Bool) := by
  intro col col' h
  funext v
  have h1 := colOf_asgB hk col v
  rw [h, colOf_asgB hk col' v] at h1
  exact Fin.ext h1.symm

theorem exists_coloringB {k : ℕ} (hk : 2 ≤ k) (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin (n * nb k + 4) → Bool)
    (ha : ∀ C ∈ colB k n (matrix G), ∃ l ∈ C, ext a l.1 = l.2) : ∃ col : G.Coloring (Fin k), asgB col = a := by
  obtain ⟨hA, hB, hD⟩ := (sat_colB hk n (matrix G) (ext a)).1 ha
  have hb := one_le_nb hk
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨colOf (nb k) (ext a) v, hA v v.2⟩) fun {u v} huv heq =>
    hB u u.2 v v.2 ((hAdj n G u v).2 huv) (congrArg Fin.val heq), ?_⟩
  funext x
  by_cases hx : x.val < n * nb k
  · have hv : x.val / nb k < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hx (mul_comm n (nb k)))
    have hj : x.val % nb k < nb k := Nat.mod_lt _ (by omega)
    have hxe : x.val = x.val / nb k * nb k + x.val % nb k := (Nat.div_add_mod' x.val (nb k)).symm
    change asgB _ x = a x
    rw [asgB, dif_pos hx]
    change (colOf (nb k) (ext a) (x.val / nb k)).testBit (x.val % nb k) = a x
    rw [colOf, testBit_val, decide_eq_true hj, Bool.true_and, ← hxe, ext_val' a]
  · have hi : x.val - n * nb k < 4 := by have := x.2; omega
    have := hD _ hi
    rw [show n * nb k + (x.val - n * nb k) = x.val by omega, ext_val' a] at this
    change asgB _ x = a x
    rw [asgB, dif_neg hx, this]

/-- The formula has as many satisfying assignments as G has proper k-colorings. -/
theorem cntN_colB {k : ℕ} (hk : 2 ≤ k) (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) :
    cntN (n * nb k + 4) (colB k n (matrix G)) = numColorings G k := by
  rw [numColorings, cntN, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hmem : ∀ col : G.Coloring (Fin k), asgB col ∈ univ.filter fun a : Fin (n * nb k + 4) → Bool =>
      ∀ C ∈ colB k n (matrix G), ∃ l ∈ C, ext a l.1 = l.2 :=
    fun col => mem_filter.2 ⟨mem_univ _, sat_asgB hk hAdj G col⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun col : G.Coloring (Fin k) => (⟨asgB col, hmem col⟩ :
    {a // a ∈ univ.filter fun a : Fin (n * nb k + 4) → Bool => ∀ C ∈ colB k n (matrix G), ∃ l ∈ C, ext a l.1 = l.2}))
      ⟨?_, ?_⟩)).symm
  · intro col col' h
    exact DFunLike.coe_injective (asgB_injective hk (congrArg Subtype.val h))
  · rintro ⟨a, ha⟩
    obtain ⟨col, hcol⟩ := exists_coloringB hk hAdj G a (mem_filter.1 ha).2
    exact ⟨col, Subtype.ext hcol⟩

end EthCor
