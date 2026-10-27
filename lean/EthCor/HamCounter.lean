import EthCor.HamFormula

/-! # Cut & Count for the Hamiltonian cycles with sequential counters

`hcF` says "every vertex is on exactly two chosen edges" with all triples of edges at a vertex, so
its width and its size grow with the degree. `hcS` says it with a sequential counter. For the
edges e₁ < … < e_d at v there are two counter bits per edge: c_k means "one of e₁ … e_k is chosen"
and c_k + 1 means "two of them are". The clauses say c_k = c_{k−1} ∨ x_k and
c_k + 1 = (c_{k−1} + 1) ∨ (x_k ∧ c_{k−1}), that x_k is never chosen when c_{k−1} + 1 is true, and
that c_d + 1 is true (`cntC`, `sat_cntC`). The counter of the edge i at its end b ∈ {0, 1} is at
m + n + 4i + 2b. The counter before the first edge is the pair z = 5m + n, z + 1, both false.

The edge bits determine the counter bits (`auxOK_iff`, `sat_append_iff`). So `hcS` on
5m + n + 2 variables has as many satisfying assignments as `hcF` (`cntN_hcS`), and hence the
parity of the number of Hamiltonian cycles (`hcS_parity`). Every clause of `hcS` has at most three
literals, whatever the degrees. -/

namespace EthCor.HamS

open Groundwork.Prog CountKSat GraphProblems Finset EthCor.Ham

/-! ### The formula -/

/-- One step of the counter at the edge variable x, from the counter p to the counter c. -/
def stepC (p x c : ℕ) : Fml :=
  [[(p, false), (c, true)], [(x, false), (c, true)], [(c, false), (p, true), (x, true)],
    [(p + 1, false), (c + 1, true)], [(x, false), (p, false), (c + 1, true)],
    [(c + 1, false), (p + 1, true), (x, true)], [(c + 1, false), (p + 1, true), (p, true)],
    [(p + 1, false), (x, false)]]

/-- The counter along L = [(x₁, c₁), …], starting from the counter z: exactly two of the x are
true. -/
def cntC (z : ℕ) (L : List (ℕ × ℕ)) : Fml :=
  (List.range L.length).flatMap (fun k =>
      stepC ((z :: L.map Prod.snd).getD k 0) (L.getD k (0, 0)).1 (L.getD k (0, 0)).2) ++
    [[((z :: L.map Prod.snd).getD L.length 0 + 1, true)]]

/-- The counter of the edge e at its end v (2·0 at the first end, 2·1 at the second). -/
def cb (E : List (ℕ × ℕ)) (n v e : ℕ) : ℕ := E.length + n + (4 * e + 2 * min (v - (E.getD e (0, 0)).1) 1)

/-- The edges at v with their counters. -/
def incC (E : List (ℕ × ℕ)) (n v : ℕ) : List (ℕ × ℕ) := (inc E v).map fun e => (e, cb E n v e)

/-- The start of every counter: the pair z, z + 1, both false. -/
def zC (E : List (ℕ × ℕ)) (n : ℕ) : ℕ := E.length + n + 4 * E.length

/-- The formula of Cut & Count with sequential counters, on m + n + (4m + 2) variables. -/
def hcS (n : ℕ) (E : List (ℕ × ℕ)) : Fml :=
  tautC (E.length + n + (4 * E.length + 2)) ++ (List.range n).flatMap (fun v => cntC (zC E n) (incC E n v)) ++
    (List.range E.length).flatMap (fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2) ++
    [[(E.length, false)], [(zC E n, false)], [(zC E n + 1, false)]]

/-! ### The counter -/

theorem sat2 (f : ℕ → Bool) (a b : ℕ × Bool) :
    (∃ l ∈ [a, b], f l.1 = l.2) ↔ f a.1 = a.2 ∨ f b.1 = b.2 := by
  constructor
  · rintro ⟨l, hl, e⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact Or.inl e
    · exact Or.inr e
  · rintro (e | e)
    · exact ⟨a, by simp, e⟩
    · exact ⟨b, by simp, e⟩

theorem sat_stepC (f : ℕ → Bool) (p x c : ℕ) :
    (∀ C ∈ stepC p x c, ∃ l ∈ C, f l.1 = l.2) ↔
      f c = (f p || f x) ∧ f (c + 1) = (f (p + 1) || (f x && f p)) ∧ (f (p + 1) && f x) = false := by
  simp only [stepC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat2, sat3]
  generalize f p = a, f x = b, f c = d, f (p + 1) = e, f (c + 1) = h
  cases a <;> cases b <;> cases d <;> cases e <;> cases h <;> decide

theorem cntC_nil (z : ℕ) : cntC z [] = [[(z + 1, true)]] := by simp [cntC]

theorem cntC_cons (z x c : ℕ) (L : List (ℕ × ℕ)) : cntC z ((x, c) :: L) = stepC z x c ++ cntC c L := by
  simp only [cntC, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    List.map_cons, List.getD_cons_zero, List.getD_cons_succ, List.append_assoc]

/-- The counter bits along L, given k true x before L: each one holds the number of true x up to
it, capped at 2. -/
def auxOK (f : ℕ → Bool) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | k, (x, c) :: L => f c = decide (1 ≤ k + (if f x then 1 else 0)) ∧
      f (c + 1) = decide (2 ≤ k + (if f x then 1 else 0)) ∧ auxOK f (k + (if f x then 1 else 0)) L

/-- **What the counter says**: from a counter z that holds k ≤ 2, the clauses hold exactly if the
counter bits along L are right and k plus the number of true x in L is 2. -/
theorem sat_cntC (f : ℕ → Bool) (L : List (ℕ × ℕ)) :
    ∀ z k : ℕ, f z = decide (1 ≤ k) → f (z + 1) = decide (2 ≤ k) → k ≤ 2 →
      ((∀ C ∈ cntC z L, ∃ l ∈ C, f l.1 = l.2) ↔ auxOK f k L ∧ k + L.countP (fun q => f q.1) = 2) := by
  induction L with
  | nil =>
    intro z k _ h2 hk
    rw [cntC_nil]
    have e : (∀ C ∈ [[(z + 1, true)]], ∃ l ∈ C, f l.1 = l.2) ↔ f (z + 1) = true := by simp
    rw [e, h2]
    simp only [auxOK, List.countP_nil, add_zero, true_and, decide_eq_true_eq]
    omega
  | cons q L ih =>
    obtain ⟨x, c⟩ := q
    intro z k h1 h2 hk
    rw [cntC_cons, List.forall_mem_append, sat_stepC, h1, h2]
    simp only [auxOK, List.countP_cons]
    cases hx : f x
    · simp only [Bool.false_eq_true, if_false, add_zero, Bool.or_false, Bool.and_false, Bool.false_and,
        and_true]
      constructor
      · rintro ⟨⟨hc1, hc2⟩, h⟩
        exact (fun h' => ⟨⟨hc1, hc2, h'.1⟩, h'.2⟩) ((ih c k hc1 hc2 hk).1 h)
      · rintro ⟨⟨hc1, hc2, h⟩, hs⟩
        exact ⟨⟨hc1, hc2⟩, (ih c k hc1 hc2 hk).2 ⟨h, hs⟩⟩
    · by_cases hk2 : 2 ≤ k
      · have : decide (2 ≤ k) = true := decide_eq_true hk2
        simp only [this, Bool.true_and, Bool.true_or, if_true]
        constructor
        · rintro ⟨⟨-, -, h⟩, -⟩; exact absurd h (by decide)
        · rintro ⟨-, h⟩; omega
      · have e2 : decide (2 ≤ k) = false := decide_eq_false hk2
        have e3 : decide (1 ≤ k + 1) = true := decide_eq_true (by omega)
        have e4 : decide (2 ≤ k + 1) = decide (1 ≤ k) := by
          by_cases h : 1 ≤ k
          · rw [decide_eq_true h, decide_eq_true (by omega)]
          · rw [decide_eq_false h, decide_eq_false (by omega)]
        simp only [e2, e3, e4, Bool.or_true, Bool.false_or, Bool.true_and, Bool.and_true, if_true, and_true]
        constructor
        · rintro ⟨⟨hc1, hc2⟩, h⟩
          have := (ih c (k + 1) (by rw [hc1]; exact e3.symm) (by rw [hc2, e4]) (by omega)).1 h
          exact ⟨⟨hc1, hc2, this.1⟩, by omega⟩
        · rintro ⟨⟨hc1, hc2, h⟩, hs⟩
          exact ⟨⟨hc1, hc2⟩, (ih c (k + 1) (by rw [hc1]; exact e3.symm) (by rw [hc2, e4]) (by omega)).2
            ⟨h, by omega⟩⟩

/-- The counter bits along a sorted list I with counters at g e: each one holds the number of true
x in I up to e. -/
theorem auxOK_iff (f : ℕ → Bool) (g : ℕ → ℕ) {I : List ℕ} (hI : I.Pairwise (· < ·)) (k : ℕ) :
    auxOK f k (I.map fun e => (e, g e)) ↔ ∀ e ∈ I,
      f (g e) = decide (1 ≤ k + (I.filter (· ≤ e)).countP f) ∧
        f (g e + 1) = decide (2 ≤ k + (I.filter (· ≤ e)).countP f) := by
  induction I generalizing k with
  | nil => simp [auxOK]
  | cons e₀ I ih =>
    rw [List.pairwise_cons] at hI
    simp only [List.map_cons, auxOK, List.forall_mem_cons]
    rw [ih hI.2]
    have h0 : (e₀ :: I).filter (· ≤ e₀) = [e₀] := by
      rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 fun a ha => by
        simpa using hI.1 a ha]
    have h1 : ∀ e ∈ I, k + ((e₀ :: I).filter (· ≤ e)).countP f =
        (k + if f e₀ then 1 else 0) + (I.filter (· ≤ e)).countP f := by
      intro e he
      rw [List.filter_cons_of_pos (by simpa using (hI.1 e he).le), List.countP_cons]
      omega
    have h2 : k + ([e₀] : List ℕ).countP f = k + if f e₀ then 1 else 0 := by
      simp [List.countP_cons]
    rw [h0, h2, and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun e he => ?_))
    rw [h1 e he]

/-! ### What the formula says -/

theorem forall_flatMap_range {n : ℕ} (F : ℕ → Fml) (P : List (ℕ × Bool) → Prop) :
    (∀ C ∈ (List.range n).flatMap F, P C) ↔ ∀ v < n, ∀ C ∈ F v, P C := by
  simp only [List.mem_flatMap, List.mem_range]
  exact ⟨fun h v hv C hC => h C ⟨v, hv, hC⟩, fun h C ⟨v, hv, hC⟩ => h v hv C hC⟩

/-- **What the formula says**: the counter bits are right and every vertex is on exactly two
chosen edges, chosen edges are inside a side, s₀ is false, and z, z + 1 are false. -/
theorem sat_hcS (f : ℕ → Bool) (n : ℕ) (E : List (ℕ × ℕ)) :
    (∀ C ∈ hcS n E, ∃ l ∈ C, f l.1 = l.2) ↔
      ((∀ v < n, (inc E v).countP f = 2) ∧
        (∀ i < E.length, f i = true → f (E.length + (E.getD i (0, 0)).1) = f (E.length + (E.getD i (0, 0)).2)) ∧
        f E.length = false) ∧
      ((∀ v < n, auxOK f 0 (incC E n v)) ∧ f (zC E n) = false ∧ f (zC E n + 1) = false) := by
  have ht : ∀ C ∈ tautC (E.length + n + (4 * E.length + 2)), ∃ l ∈ C, f l.1 = l.2 := by
    intro C hC
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
    cases h : f i
    · exact ⟨(i, false), by simp, h⟩
    · exact ⟨(i, true), by simp, h⟩
  have he : (∀ C ∈ (List.range E.length).flatMap (fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2),
      ∃ l ∈ C, f l.1 = l.2) ↔
      ∀ i < E.length, f i = true → f (E.length + (E.getD i (0, 0)).1) = f (E.length + (E.getD i (0, 0)).2) := by
    rw [forall_flatMap_range]
    exact forall₂_congr fun i _ => sat_edgeC f _ _ _ _
  have hr : (∀ C ∈ [[(E.length, false)], [(zC E n, false)], [(zC E n + 1, false)]], ∃ l ∈ C, f l.1 = l.2) ↔
      f E.length = false ∧ f (zC E n) = false ∧ f (zC E n + 1) = false := by simp
  have hv : f (zC E n) = false → f (zC E n + 1) = false →
      ((∀ C ∈ (List.range n).flatMap (fun v => cntC (zC E n) (incC E n v)), ∃ l ∈ C, f l.1 = l.2) ↔
        ∀ v < n, auxOK f 0 (incC E n v) ∧ (inc E v).countP f = 2) := by
    intro hz hz1
    rw [forall_flatMap_range]
    refine forall₂_congr fun v _ => ?_
    rw [sat_cntC f _ (zC E n) 0 (by rw [hz]; rfl) (by rw [hz1]; rfl) (by omega), incC, List.countP_map, zero_add]
    rfl
  rw [hcS, List.forall_mem_append, List.forall_mem_append, List.forall_mem_append, he, hr]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3, hz, hz1⟩
    have h1 := (hv hz hz1).1 h1
    exact ⟨⟨fun v hv => (h1 v hv).2, h2, h3⟩, fun v hv => (h1 v hv).1, hz, hz1⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, hz, hz1⟩
    exact ⟨⟨⟨ht, (hv hz hz1).2 fun v hv => ⟨h4 v hv, h1 v hv⟩⟩, h2⟩, h3, hz, hz1⟩

/-! ### The counter bits are determined by the edge bits -/

/-- The end b ∈ {0, 1} of the edge e. -/
def endV (E : List (ℕ × ℕ)) (e b : ℕ) : ℕ := if b = 0 then (E.getD e (0, 0)).1 else (E.getD e (0, 0)).2

/-- The counter bits that the edge bits y determine: bit 4e + 2b + j holds "at least j + 1 of the
edges at the end b of e, up to e, are chosen". -/
def auxOf (E : List (ℕ × ℕ)) (y : ℕ → Bool) (t : ℕ) : Bool :=
  decide (t < 4 * E.length) &&
    decide (t % 2 + 1 ≤ ((inc E (endV E (t / 4) (t % 4 / 2))).filter (· ≤ t / 4)).countP y)

theorem pairwise_inc (E : List (ℕ × ℕ)) (v : ℕ) : (inc E v).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem mem_inc_iff {E : List (ℕ × ℕ)} {v e : ℕ} :
    e ∈ inc E v ↔ e < E.length ∧ ((E.getD e (0, 0)).1 = v ∨ (E.getD e (0, 0)).2 = v) := by
  simp [inc, List.mem_filter, List.mem_range]

/-- The bits of the counters and of z, z + 1 are right exactly if they are the bits `auxOf`. -/
theorem aux_iff {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    (y : Fin (E.length + n) → Bool) (g : Fin (4 * E.length + 2) → Bool) :
    ((∀ v < n, auxOK (ext (Fin.append y g)) 0 (incC E n v)) ∧ ext (Fin.append y g) (zC E n) = false ∧
        ext (Fin.append y g) (zC E n + 1) = false) ↔
      ∀ t : Fin (4 * E.length + 2), g t = auxOf E (ext y) t.val := by
  obtain ⟨m, hm⟩ : ∃ m, m = E.length := ⟨_, rfl⟩
  have hge : ∀ a, ext (Fin.append y g) (E.length + n + a) = ext g a := ext_append_ge y g
  -- the prefix counts only see the edge bits
  have hpre : ∀ v e, ((inc E v).filter (· ≤ e)).countP (ext (Fin.append y g)) =
      ((inc E v).filter (· ≤ e)).countP (ext y) := fun v e =>
    List.countP_congr fun i hi => by
      have := lt_of_mem_inc (List.mem_filter.1 hi).1
      rw [ext_append_lt _ _ (show i < E.length + n by omega)]
  have hg : ∀ t : Fin (4 * E.length + 2), g t = ext (Fin.append y g) (E.length + n + t.val) := by
    intro t; rw [hge]; exact (ext_fin g t).symm
  -- the end of e that is v
  have hcb : ∀ v e, e ∈ inc E v →
      min (v - (E.getD e (0, 0)).1) 1 ≤ 1 ∧ endV E e (min (v - (E.getD e (0, 0)).1) 1) = v := by
    intro v e he
    obtain ⟨he, hv⟩ := mem_inc_iff.1 he
    refine ⟨min_le_right _ _, ?_⟩
    have h := hE _ (List.getElem_mem he)
    unfold endV
    rw [List.getD_eq_getElem _ _ he] at hv ⊢
    rcases hv with hv | hv
    · rw [if_pos (by omega)]; exact hv
    · rw [if_neg (by omega)]; exact hv
  constructor
  · rintro ⟨hv, hz, hz1⟩ t
    rw [hg t]
    by_cases ht : t.val < 4 * E.length
    · obtain ⟨e, b, j, hb, hj, htv⟩ : ∃ e b j, b ≤ 1 ∧ j ≤ 1 ∧ 4 * e + 2 * b + j = t.val :=
        ⟨t.val / 4, t.val % 4 / 2, t.val % 2, by omega, by omega, by omega⟩
      rw [← htv] at ht ⊢
      have he : e < E.length := by omega
      have e1 : (4 * e + 2 * b + j) / 4 = e := by omega
      have e2 : (4 * e + 2 * b + j) % 4 / 2 = b := by omega
      have e3 : (4 * e + 2 * b + j) % 2 = j := by omega
      unfold auxOf
      rw [e1, e2, e3, decide_eq_true ht, Bool.true_and]
      have h := hE _ (List.getElem_mem he)
      obtain ⟨v, hvd⟩ : ∃ v, v = endV E e b := ⟨_, rfl⟩
      rw [← hvd]
      have hvn : v < n := by
        rw [hvd, endV, List.getD_eq_getElem _ _ he]; split_ifs <;> omega
      have hev : e ∈ inc E v := by
        rw [mem_inc_iff]
        refine ⟨he, ?_⟩
        rw [hvd, endV, List.getD_eq_getElem _ _ he]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hbb : min (v - (E.getD e (0, 0)).1) 1 = b := by
        rw [hvd]; unfold endV; rw [List.getD_eq_getElem _ _ he]
        rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
        · simp
        · rw [if_neg (by omega)]; omega
      have hok := ((auxOK_iff _ (cb E n v) (pairwise_inc E v) 0).1 (by rw [← incC]; exact hv v hvn)) e hev
      simp only [cb, hbb, hpre, zero_add] at hok
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [add_zero, hok.1]
      · rw [show E.length + n + (4 * e + 2 * b + 1) = E.length + n + (4 * e + 2 * b) + 1 by ring, hok.2]
    · unfold auxOf
      rw [decide_eq_false ht, Bool.false_and]
      rcases (by omega : t.val = 4 * E.length ∨ t.val = 4 * E.length + 1) with h | h
      · rw [h]; exact hz
      · rw [h]; exact hz1
  · intro h
    have hz : ext (Fin.append y g) (zC E n) = false := by
      have k := h ⟨4 * E.length, by omega⟩
      rw [hg] at k
      dsimp only at k
      unfold auxOf at k
      rw [decide_eq_false (lt_irrefl _), Bool.false_and] at k
      exact k
    have hz1 : ext (Fin.append y g) (zC E n + 1) = false := by
      have k := h ⟨4 * E.length + 1, by omega⟩
      rw [hg] at k
      dsimp only at k
      unfold auxOf at k
      rw [decide_eq_false (show ¬ (4 * E.length + 1 < 4 * E.length) by omega), Bool.false_and] at k
      exact k
    refine ⟨fun v _ => ?_, hz, hz1⟩
    rw [incC, auxOK_iff _ _ (pairwise_inc E v)]
    intro e hev
    obtain ⟨hb1, hend⟩ := hcb v e hev
    have he := lt_of_mem_inc hev
    simp only [cb]
    generalize min (v - (E.getD e (0, 0)).1) 1 = b at hb1 hend ⊢
    rw [hpre, zero_add]
    have k0 := h ⟨4 * e + 2 * b, by omega⟩
    have k1 := h ⟨4 * e + 2 * b + 1, by omega⟩
    rw [hg] at k0 k1
    dsimp only at k0 k1
    unfold auxOf at k0 k1
    rw [show (4 * e + 2 * b) / 4 = e by omega, show (4 * e + 2 * b) % 4 / 2 = b by omega,
      show (4 * e + 2 * b) % 2 = 0 by omega, decide_eq_true (show 4 * e + 2 * b < 4 * E.length by omega),
      Bool.true_and, hend] at k0
    rw [show (4 * e + 2 * b + 1) / 4 = e by omega, show (4 * e + 2 * b + 1) % 4 / 2 = b by omega,
      show (4 * e + 2 * b + 1) % 2 = 1 by omega, decide_eq_true (show 4 * e + 2 * b + 1 < 4 * E.length by omega),
      Bool.true_and, hend] at k1
    exact ⟨k0, k1⟩

/-! ### The count -/

/-- For x = (y, g): the formula `hcS` holds exactly if `hcF` holds for y and g is `auxOf`. -/
theorem sat_append_iff {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    (y : Fin (E.length + n) → Bool) (g : Fin (4 * E.length + 2) → Bool) :
    (∀ C ∈ hcS n E, ∃ l ∈ C, ext (Fin.append y g) l.1 = l.2) ↔
      (∀ C ∈ hcF n E, ∃ l ∈ C, ext y l.1 = l.2) ∧ ∀ t : Fin (4 * E.length + 2), g t = auxOf E (ext y) t.val := by
  rw [sat_hcS, sat_hcF, aux_iff hE]
  have h1 : ∀ v, (inc E v).countP (ext (Fin.append y g)) = (inc E v).countP (ext y) := fun v =>
    List.countP_congr fun i hi => by
      have := lt_of_mem_inc hi
      rw [ext_append_lt _ _ (show i < E.length + n by omega)]
  have h2 : ∀ a < E.length + n, ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt _ _ ha
  have hb : ∀ i < E.length, (E.getD i (0, 0)).1 < n ∧ (E.getD i (0, 0)).2 < n := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    have := hE _ (List.getElem_mem hi); omega
  refine and_congr (and_congr (by simp only [h1]) (and_congr ?_ (by rw [h2 _ (by omega)]))) Iff.rfl
  refine forall₂_congr fun i hi => ?_
  rw [h2 i (by omega), h2 _ (by have := (hb i hi).1; omega), h2 _ (by have := (hb i hi).2; omega)]

/-- **The count**: `hcS` has as many satisfying assignments as `hcF`. -/
theorem cntN_hcS {n : ℕ} (hn : 0 < n) {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) :
    cntN (E.length + n + (4 * E.length + 2)) (hcS n E) = cntN (E.length + n) (hcF n E) := by
  unfold cntN
  rw [Finset.card_equiv (Fin.appendEquiv (E.length + n) (4 * E.length + 2)).symm
    (t := univ.filter fun p : (Fin (E.length + n) → Bool) × (Fin (4 * E.length + 2) → Bool) =>
      (∀ C ∈ hcF n E, ∃ l ∈ C, ext p.1 l.1 = l.2) ∧ ∀ t : Fin (4 * E.length + 2), p.2 t = auxOf E (ext p.1) t.val)]
  · refine Finset.card_nbij' (fun p => p.1) (fun y => (y, fun t => auxOf E (ext y) t.val)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
      exact hp.1
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
      exact ⟨hy, by simp⟩
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      exact Prod.ext rfl (funext fun t => (hp.2 t).symm)
    · intro y _
      rfl
  · intro b
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨p, rfl⟩ : ∃ p, b = Fin.appendEquiv (E.length + n) (4 * E.length + 2) p :=
      ⟨_, ((Fin.appendEquiv _ _).apply_symm_apply b).symm⟩
    rw [Equiv.symm_apply_apply]
    have hb : (Fin.appendEquiv (E.length + n) (4 * E.length + 2)) p = Fin.append p.1 p.2 :=
      funext fun a => Fin.appendEquiv_apply _ _ _ _
    rw [hb, sat_append_iff hn hE]

/-- **Cut & Count with counters**: the number of satisfying assignments of `hcS` for the edge list
of G has the parity of the number of Hamiltonian cycles of G. -/
theorem hcS_parity (hAdj : StAdj) {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    cntN ((edges n (matrix G)).length + n + (4 * (edges n (matrix G)).length + 2)) (hcS n (edges n (matrix G))) % 2 =
      numHamCycles G % 2 := by
  rw [cntN_hcS hn (edges_bound n (matrix G)), hc_parity hAdj hn G]

end EthCor.HamS
