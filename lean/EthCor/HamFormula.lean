import GraphProblems.Interfaces
import SplitCount.Sizes
import Mathlib

/-! # The parity of the Hamiltonian cycles as a number of satisfying assignments (Cut & Count)

For a list E of edges (a, b), a < b < n, the formula `hcF n E` has one variable for every edge
(x_i = variable i) and one for every vertex (s_v = variable m + v, m = |E|): every vertex is on
exactly two chosen edges, the two ends of a chosen edge are on the same side, and s₀ is false. Its
satisfying assignments are the pairs (x, s) of a spanning subgraph `subG n E x` in which every
vertex has degree 2 and a side map s constant along its edges with s₀ = false (`cntN_hcF`). The
number of such s is odd exactly if the subgraph is connected (`parity_sides`: for a disconnected
subgraph, flipping s on the vertices reachable from a vertex w that 0 does not reach pairs off
the side maps). For the edge list of G the subgraphs of degree 2 everywhere are the subgraphs
H ≤ G with H.degree = 2 (`card_hc`), so the number of satisfying assignments has the parity of
the number of Hamiltonian cycles (`hc_parity`). -/

namespace EthCor.Ham

open Groundwork.Prog CountKSat GraphProblems Finset

/-! ### The formula -/

/-- The indices of the edges of E at v. -/
def inc (E : List (ℕ × ℕ)) (v : ℕ) : List ℕ :=
  (List.range E.length).filter fun i => (E.getD i (0, 0)).1 == v || (E.getD i (0, 0)).2 == v

/-- No three distinct ones of the variables in I are all true. -/
def atMost2 (I : List ℕ) : Fml :=
  I.flatMap fun i => I.flatMap fun j =>
    (I.filter fun k => i != j && j != k && i != k).map fun k => [(i, false), (j, false), (k, false)]

/-- Besides any one of the variables in I another one is true, and one is true. -/
def atLeast2 (I : List ℕ) : Fml :=
  I.map (fun i => (I.filter (· != i)).map fun j => (j, true)) ++ [I.map fun j => (j, true)]

/-- If edge i is chosen, its ends a and b are on the same side. -/
def edgeC (m i a b : ℕ) : Fml :=
  [[(i, false), (m + a, false), (m + b, true)], [(i, false), (m + a, true), (m + b, false)]]

/-- x_i ∨ ¬x_i for every variable, so that every variable occurs. -/
def tautC (N : ℕ) : Fml := (List.range N).map fun i => [(i, true), (i, false)]

/-- The formula of Cut & Count for the Hamiltonian cycles. -/
def hcF (n : ℕ) (E : List (ℕ × ℕ)) : Fml :=
  tautC (E.length + n) ++ (List.range n).flatMap (fun v => atMost2 (inc E v) ++ atLeast2 (inc E v)) ++
    (List.range E.length).flatMap (fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2) ++
    [[(E.length, false)]]

/-! ### What the formula says -/

theorem sat_atMost2 (f : ℕ → Bool) (I : List ℕ) :
    (∀ C ∈ atMost2 I, ∃ l ∈ C, f l.1 = l.2) ↔
      ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I, i ≠ j → j ≠ k → i ≠ k → f i = false ∨ f j = false ∨ f k = false := by
  constructor
  · intro h i hi j hj k hk e1 e2 e3
    have hm : [(i, false), (j, false), (k, false)] ∈ atMost2 I :=
      List.mem_flatMap.2 ⟨i, hi, List.mem_flatMap.2 ⟨j, hj, List.mem_map.2 ⟨k, List.mem_filter.2 ⟨hk, by simp [e1, e2, e3]⟩, rfl⟩⟩⟩
    obtain ⟨l, hl, e⟩ := h _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · intro h C hC
    obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨j, hj, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hC
    obtain ⟨hk, hd⟩ := List.mem_filter.1 hk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    obtain ⟨⟨e1, e2⟩, e3⟩ := hd
    rcases h i hi j hj k hk e1 e2 e3 with h | h | h
    · exact ⟨(i, false), by simp, h⟩
    · exact ⟨(j, false), by simp, h⟩
    · exact ⟨(k, false), by simp, h⟩

theorem atMost2_iff (f : ℕ → Bool) {I : List ℕ} (hI : I.Nodup) :
    (∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I, i ≠ j → j ≠ k → i ≠ k → f i = false ∨ f j = false ∨ f k = false) ↔
      I.countP f ≤ 2 := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hI.filter _), ← not_lt, Finset.two_lt_card_iff]
  simp only [List.mem_toFinset, List.mem_filter]
  constructor
  · rintro h ⟨a, b, c, ⟨ha, fa⟩, ⟨hb, fb⟩, ⟨hc, fc⟩, e1, e2, e3⟩
    rcases h a ha b hb c hc e1 e3 e2 with h | h | h <;> simp_all
  · intro h i hi j hj k hk e1 e2 e3
    by_contra hne
    simp only [not_or, Bool.not_eq_false] at hne
    exact h ⟨i, j, k, ⟨hi, hne.1⟩, ⟨hj, hne.2.1⟩, ⟨hk, hne.2.2⟩, e1, e3, e2⟩

theorem sat_atLeast2 (f : ℕ → Bool) (I : List ℕ) :
    (∀ C ∈ atLeast2 I, ∃ l ∈ C, f l.1 = l.2) ↔ (∀ i ∈ I, ∃ j ∈ I, j ≠ i ∧ f j = true) ∧ ∃ j ∈ I, f j = true := by
  rw [atLeast2, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
  refine and_congr ⟨fun h i hi => ?_, fun h i hi => ?_⟩ ⟨fun ⟨l, hl, e⟩ => ?_, fun ⟨j, hj, e⟩ => ?_⟩
  · obtain ⟨l, hl, e⟩ := h i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hj, hne⟩ := List.mem_filter.1 hj
    exact ⟨j, hj, by simpa using hne, e⟩
  · obtain ⟨j, hj, hne, e⟩ := h i hi
    exact ⟨(j, true), List.mem_map.2 ⟨j, List.mem_filter.2 ⟨hj, by simpa using hne⟩, rfl⟩, e⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
    exact ⟨j, hj, e⟩
  · exact ⟨(j, true), List.mem_map.2 ⟨j, hj, rfl⟩, e⟩

theorem atLeast2_iff (f : ℕ → Bool) {I : List ℕ} (hI : I.Nodup) :
    ((∀ i ∈ I, ∃ j ∈ I, j ≠ i ∧ f j = true) ∧ ∃ j ∈ I, f j = true) ↔ 2 ≤ I.countP f := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hI.filter _), Nat.succ_le_iff, Finset.one_lt_card_iff]
  simp only [List.mem_toFinset, List.mem_filter]
  constructor
  · rintro ⟨h, j, hj, e⟩
    obtain ⟨j', hj', hne, e'⟩ := h j hj
    exact ⟨j, j', ⟨hj, e⟩, ⟨hj', e'⟩, Ne.symm hne⟩
  · rintro ⟨a, b, ⟨ha, fa⟩, ⟨hb, fb⟩, hab⟩
    refine ⟨fun i hi => ?_, a, ha, fa⟩
    by_cases hia : i = a
    · exact ⟨b, hb, by rw [hia]; exact Ne.symm hab, fb⟩
    · exact ⟨a, ha, Ne.symm hia, fa⟩

theorem nodup_inc (E : List (ℕ × ℕ)) (v : ℕ) : (inc E v).Nodup := (List.nodup_range).filter _

theorem lt_of_mem_inc {E : List (ℕ × ℕ)} {v i : ℕ} (h : i ∈ inc E v) : i < E.length :=
  List.mem_range.1 (List.mem_filter.1 h).1

theorem sat3 (f : ℕ → Bool) (a b c : ℕ × Bool) :
    (∃ l ∈ [a, b, c], f l.1 = l.2) ↔ f a.1 = a.2 ∨ f b.1 = b.2 ∨ f c.1 = c.2 := by
  constructor
  · rintro ⟨l, hl, e⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · rintro (e | e | e)
    · exact ⟨a, by simp, e⟩
    · exact ⟨b, by simp, e⟩
    · exact ⟨c, by simp, e⟩

theorem sat_edgeC (f : ℕ → Bool) (m i a b : ℕ) :
    (∀ C ∈ edgeC m i a b, ∃ l ∈ C, f l.1 = l.2) ↔ (f i = true → f (m + a) = f (m + b)) := by
  rw [edgeC, List.forall_mem_cons, List.forall_mem_singleton, sat3, sat3]
  dsimp only
  cases f i <;> cases f (m + a) <;> cases f (m + b) <;> simp

/-- **What the formula says**: every vertex on exactly two chosen edges, chosen edges inside a side,
s₀ false. -/
theorem sat_hcF (f : ℕ → Bool) (n : ℕ) (E : List (ℕ × ℕ)) :
    (∀ C ∈ hcF n E, ∃ l ∈ C, f l.1 = l.2) ↔
      (∀ v < n, (inc E v).countP f = 2) ∧
      (∀ i < E.length, f i = true → f (E.length + (E.getD i (0, 0)).1) = f (E.length + (E.getD i (0, 0)).2)) ∧
      f E.length = false := by
  have ht : ∀ C ∈ tautC (E.length + n), ∃ l ∈ C, f l.1 = l.2 := by
    intro C hC
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
    cases h : f i
    · exact ⟨(i, false), by simp, h⟩
    · exact ⟨(i, true), by simp, h⟩
  have hd : (∀ C ∈ (List.range n).flatMap (fun v => atMost2 (inc E v) ++ atLeast2 (inc E v)), ∃ l ∈ C, f l.1 = l.2) ↔
      ∀ v < n, (inc E v).countP f = 2 := by
    constructor
    · intro h v hv
      have h' : ∀ C ∈ atMost2 (inc E v) ++ atLeast2 (inc E v), ∃ l ∈ C, f l.1 = l.2 :=
        fun C hC => h C (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, hC⟩)
      rw [List.forall_mem_append, sat_atMost2, sat_atLeast2, atMost2_iff f (nodup_inc E v),
        atLeast2_iff f (nodup_inc E v)] at h'
      omega
    · intro h C hC
      obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
      have h' : ∀ C ∈ atMost2 (inc E v) ++ atLeast2 (inc E v), ∃ l ∈ C, f l.1 = l.2 := by
        rw [List.forall_mem_append, sat_atMost2, sat_atLeast2, atMost2_iff f (nodup_inc E v),
          atLeast2_iff f (nodup_inc E v)]
        have := h v (List.mem_range.1 hv)
        omega
      exact h' C hC
  have he : (∀ C ∈ (List.range E.length).flatMap (fun i => edgeC E.length i (E.getD i (0, 0)).1 (E.getD i (0, 0)).2),
      ∃ l ∈ C, f l.1 = l.2) ↔
      ∀ i < E.length, f i = true → f (E.length + (E.getD i (0, 0)).1) = f (E.length + (E.getD i (0, 0)).2) := by
    constructor
    · intro h i hi
      exact (sat_edgeC f _ _ _ _).1 fun C hC => h C (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hC⟩)
    · intro h C hC
      obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
      exact (sat_edgeC f _ _ _ _).2 (h i (List.mem_range.1 hi)) C hC
  rw [hcF, List.forall_mem_append, List.forall_mem_append, List.forall_mem_append, hd, he, List.forall_mem_singleton]
  have hr : (∃ l ∈ [(E.length, false)], f l.1 = l.2) ↔ f E.length = false := by simp
  rw [hr]
  exact ⟨fun h => ⟨h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨ht, h.1⟩, h.2.1⟩, h.2.2⟩⟩

/-! ### The count: subgraphs of degree 2 and side maps -/

theorem ext_append_lt {m n : ℕ} (x : Fin m → Bool) (s : Fin n → Bool) {i : ℕ} (hi : i < m) :
    ext (Fin.append x s) i = ext x i := by
  have h1 : i < m + n := by omega
  simp only [CountKSat.ext, dif_pos h1, dif_pos hi]
  exact Fin.append_left x s ⟨i, hi⟩

theorem ext_append_ge {m n : ℕ} (x : Fin m → Bool) (s : Fin n → Bool) (a : ℕ) :
    ext (Fin.append x s) (m + a) = ext s a := by
  by_cases ha : a < n
  · have h1 : m + a < m + n := by omega
    simp only [CountKSat.ext, dif_pos h1, dif_pos ha]
    exact Fin.append_right x s ⟨a, ha⟩
  · have h1 : ¬ m + a < m + n := by omega
    simp only [CountKSat.ext, dif_neg h1, dif_neg ha]

/-- The side maps that agree along the chosen edges, with s₀ false. -/
def sides (n : ℕ) (E : List (ℕ × ℕ)) (x : Fin E.length → Bool) : ℕ :=
  (univ.filter fun s : Fin n → Bool =>
    (∀ i < E.length, ext x i = true → ext s (E.getD i (0, 0)).1 = ext s (E.getD i (0, 0)).2) ∧ ext s 0 = false).card

/-- **The count**: the satisfying assignments are, for every choice x of edges with every vertex on two
of them, the side maps of x. -/
theorem cntN_hcF (n : ℕ) (E : List (ℕ × ℕ)) :
    cntN (E.length + n) (hcF n E) =
      ∑ x : Fin E.length → Bool, if (∀ v < n, (inc E v).countP (ext x) = 2) then sides n E x else 0 := by
  unfold cntN
  rw [Finset.card_equiv (Fin.appendEquiv E.length n).symm (t := univ.filter fun p : (Fin E.length → Bool) × (Fin n → Bool) =>
      (∀ v < n, (inc E v).countP (ext p.1) = 2) ∧
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
    rw [hb]
    rw [sat_hcF]
    have h1 : ∀ v, (inc E v).countP (ext (Fin.append p.1 p.2)) = (inc E v).countP (ext p.1) := fun v =>
      List.countP_congr fun i hi => by rw [ext_append_lt _ _ (lt_of_mem_inc hi)]
    have h2 : ∀ i < E.length, ext (Fin.append p.1 p.2) i = ext p.1 i := fun i hi => ext_append_lt _ _ hi
    have h3 : ext (Fin.append p.1 p.2) E.length = ext p.2 0 := by
      have := ext_append_ge p.1 p.2 0; rwa [Nat.add_zero] at this
    simp only [h1, ext_append_ge, h3]
    refine and_congr Iff.rfl (and_congr ⟨fun h i hi e => h i hi (by rw [h2 i hi]; exact e),
      fun h i hi e => h i hi (by rw [← h2 i hi]; exact e)⟩ Iff.rfl)

/-! ### The parity of the number of side maps -/

/-- The subgraph of the chosen edges. -/
def subG (n : ℕ) (E : List (ℕ × ℕ)) (x : Fin E.length → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i : Fin E.length, x i = true ∧ E[i] = (u.val, v.val)

theorem ext_fin {n : ℕ} (s : Fin n → Bool) (u : Fin n) : ext s u.val = s u := by simp [CountKSat.ext]

theorem cons_iff {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) (x : Fin E.length → Bool)
    (s : Fin n → Bool) :
    (∀ i < E.length, ext x i = true → ext s (E.getD i (0, 0)).1 = ext s (E.getD i (0, 0)).2) ↔
      ∀ u v, (subG n E x).Adj u v → s u = s v := by
  constructor
  · intro h u v huv
    obtain ⟨-, e⟩ := (SimpleGraph.fromRel_adj _ _ _).1 huv
    obtain ⟨i, hi, e⟩ | ⟨i, hi, e⟩ := e
    · have h1 := h i.val i.2 (by rw [ext_fin]; exact hi)
      rw [List.getD_eq_getElem _ _ i.2] at h1
      have e' : E[i.val] = E[i] := rfl
      rw [e', e] at h1
      simpa only [ext_fin] using h1
    · have h1 := h i.val i.2 (by rw [ext_fin]; exact hi)
      rw [List.getD_eq_getElem _ _ i.2] at h1
      have e' : E[i.val] = E[i] := rfl
      rw [e', e] at h1
      simpa only [ext_fin] using h1.symm
  · intro h i hi e
    rw [List.getD_eq_getElem _ _ hi]
    obtain ⟨h1, h2⟩ := hE _ (List.getElem_mem hi)
    have hx : x ⟨i, hi⟩ = true := by rw [← ext_fin x ⟨i, hi⟩]; exact e
    have := h ⟨E[i].1, by omega⟩ ⟨E[i].2, h2⟩ ((SimpleGraph.fromRel_adj _ _ _).2
      ⟨fun e => by simp [Fin.ext_iff] at e; omega, Or.inl ⟨⟨i, hi⟩, hx, rfl⟩⟩)
    rw [← ext_fin s ⟨E[i].1, by omega⟩, ← ext_fin s ⟨E[i].2, h2⟩] at this
    exact this

open Classical in
/-- **The parity**: the side maps constant along the edges of H with s₀ false are odd in number
exactly if H is connected. -/
theorem parity_sides {n : ℕ} (hn : 0 < n) (H : SimpleGraph (Fin n)) :
    (univ.filter fun s : Fin n → Bool => s ⟨0, hn⟩ = false ∧ ∀ u v, H.Adj u v → s u = s v).card % 2 =
      if H.Connected then 1 else 0 := by
  set S := univ.filter fun s : Fin n → Bool => s ⟨0, hn⟩ = false ∧ ∀ u v, H.Adj u v → s u = s v with hSdef
  have hreach : ∀ s ∈ S, ∀ u v, H.Reachable u v → s u = s v := by
    intro s hs u v ⟨p⟩
    induction p with
    | nil => rfl
    | cons h p ih => exact ((mem_filter.1 hs).2.2 _ _ h).trans ih
  split_ifs with hc
  · have hS : S = {fun _ => false} := by
      ext s
      simp only [mem_singleton]
      constructor
      · intro hs
        funext v
        rw [← (mem_filter.1 hs).2.1]
        exact hreach s hs _ _ (hc.preconnected v ⟨0, hn⟩)
      · rintro rfl
        simp [hSdef]
    rw [hS, card_singleton]
  · obtain ⟨w, hw⟩ : ∃ w, ¬ H.Reachable ⟨0, hn⟩ w := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hc ((SimpleGraph.connected_iff H).2 ⟨fun u v => (h u).symm.trans (h v), ⟨⟨0, hn⟩⟩⟩)
    let fl : (Fin n → Bool) → (Fin n → Bool) := fun s v => if H.Reachable w v then !s v else s v
    have hfl2 : ∀ s, fl (fl s) = s := fun s => by
      funext v; by_cases h : H.Reachable w v <;> simp [fl, h]
    have hflw : ∀ s, fl s w = !s w := fun s => by simp [fl]
    have hflS : ∀ s ∈ S, fl s ∈ S := by
      intro s hs
      obtain ⟨h0, hadj⟩ := (mem_filter.1 hs).2
      have hw0 : ¬ H.Reachable w ⟨0, hn⟩ := fun h => hw h.symm
      refine mem_filter.2 ⟨mem_univ _, by simp [fl, hw0, h0], fun u v huv => ?_⟩
      have huv' : H.Reachable w u ↔ H.Reachable w v :=
        ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.reachable.symm⟩
      by_cases h : H.Reachable w u
      · simp [fl, h, huv'.1 h, hadj u v huv]
      · simp [fl, h, mt huv'.2 h, hadj u v huv]
    have hsplit := card_filter_add_card_filter_not (s := S) (fun s => s w = false)
    have hbij : (S.filter fun s => s w = false).card = (S.filter fun s => ¬ s w = false).card := by
      refine Finset.card_bij (fun s _ => fl s) (fun s hs => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
      · obtain ⟨hs, e⟩ := mem_filter.1 hs
        exact mem_filter.2 ⟨hflS s hs, by rw [hflw, e]; simp⟩
      · rw [← hfl2 s, h, hfl2]
      · obtain ⟨ht, e⟩ := mem_filter.1 ht
        refine ⟨fl t, mem_filter.2 ⟨hflS t ht, ?_⟩, hfl2 t⟩
        rw [hflw]; simpa using e
    omega

/-! ### Degrees, and the subgraphs of G -/

theorem subG_adj {n : ℕ} {E : List (ℕ × ℕ)} {x : Fin E.length → Bool} {u v : Fin n} :
    (subG n E x).Adj u v ↔ u ≠ v ∧ ((∃ i : Fin E.length, x i = true ∧ E[i] = (u.val, v.val)) ∨
      ∃ i : Fin E.length, x i = true ∧ E[i] = (v.val, u.val)) := SimpleGraph.fromRel_adj _ _ _

theorem countP_inc (E : List (ℕ × ℕ)) (v : ℕ) (f : ℕ → Bool) :
    (inc E v).countP f = ((range E.length).filter fun i =>
      ((E.getD i (0, 0)).1 = v ∨ (E.getD i (0, 0)).2 = v) ∧ f i = true).card := by
  rw [inc, List.countP_filter, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1; ext i; simp [and_comm]

open Classical in
/-- The degree of v in the subgraph of the chosen edges is the number of chosen edges at v. -/
theorem degree_subG {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) (hnd : E.Nodup)
    (x : Fin E.length → Bool) (v : Fin n) : (subG n E x).degree v = (inc E v.val).countP (ext x) := by
  rw [countP_inc, ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    ← Finset.card_map Fin.valEmbedding]
  symm
  -- edge i at v ↦ its other end a + b − v
  refine Finset.card_nbij (fun i => (E.getD i (0, 0)).1 + (E.getD i (0, 0)).2 - v.val) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi, hP, hx⟩ := by simpa only [coe_filter, mem_range, Set.mem_ofPred_eq] using hi
    dsimp only
    rw [List.getD_eq_getElem _ _ hi] at hP ⊢
    obtain ⟨h1, h2⟩ := hE _ (List.getElem_mem hi)
    have hx' : x ⟨i, hi⟩ = true := by rw [← ext_fin x ⟨i, hi⟩]; exact hx
    refine Finset.mem_coe.2 (Finset.mem_map.2 ⟨⟨E[i].1 + E[i].2 - v.val, by omega⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩)
    refine subG_adj.2 ⟨fun e => by simp [Fin.ext_iff] at e; omega, ?_⟩
    rcases hP with hP | hP
    · exact Or.inl ⟨⟨i, hi⟩, hx', Prod.ext (by simp; omega) (by simp; omega)⟩
    · exact Or.inr ⟨⟨i, hi⟩, hx', Prod.ext (by simp; omega) (by simp; omega)⟩
  · intro i hi j hj e
    obtain ⟨hi, hPi, -⟩ := by simpa only [coe_filter, mem_range, Set.mem_ofPred_eq] using hi
    obtain ⟨hj, hPj, -⟩ := by simpa only [coe_filter, mem_range, Set.mem_ofPred_eq] using hj
    simp only at e
    rw [List.getD_eq_getElem _ _ hi] at hPi e
    rw [List.getD_eq_getElem _ _ hj] at hPj e
    obtain ⟨a1, a2⟩ := hE _ (List.getElem_mem hi)
    obtain ⟨b1, b2⟩ := hE _ (List.getElem_mem hj)
    have hij : E[i] = E[j] := Prod.ext (by omega) (by omega)
    exact (hnd.getElem_inj_iff).1 hij
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hu)
    obtain ⟨-, ⟨j, hj, e⟩ | ⟨j, hj, e⟩⟩ := subG_adj.1 (mem_filter.1 hw).2
    · refine ⟨j.val, ?_, ?_⟩
      · refine Finset.mem_coe.2 (mem_filter.2 ⟨mem_range.2 j.2, ?_, by rw [ext_fin]; exact hj⟩)
        rw [List.getD_eq_getElem _ _ j.2]; exact Or.inl (by rw [show E[j.val] = E[j] from rfl, e])
      · simp only [List.getD_eq_getElem _ _ j.2, show E[j.val] = E[j] from rfl, e, Fin.valEmbedding_apply]; omega
    · refine ⟨j.val, ?_, ?_⟩
      · refine Finset.mem_coe.2 (mem_filter.2 ⟨mem_range.2 j.2, ?_, by rw [ext_fin]; exact hj⟩)
        rw [List.getD_eq_getElem _ _ j.2]; exact Or.inr (by rw [show E[j.val] = E[j] from rfl, e])
      · simp only [List.getD_eq_getElem _ _ j.2, show E[j.val] = E[j] from rfl, e, Fin.valEmbedding_apply]; omega

/-- Edge i is chosen iff it is an edge of the subgraph. -/
theorem x_iff {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) (hnd : E.Nodup)
    (x : Fin E.length → Bool) (i : Fin E.length) :
    x i = true ↔ ∃ u v : Fin n, (subG n E x).Adj u v ∧ E[i] = (u.val, v.val) := by
  obtain ⟨h1, h2⟩ := hE E[i] (List.getElem_mem i.2)
  constructor
  · intro hx
    exact ⟨⟨E[i].1, by omega⟩, ⟨E[i].2, h2⟩,
      subG_adj.2 ⟨fun e => by have := congrArg Fin.val e; dsimp only at this; omega, Or.inl ⟨i, hx, rfl⟩⟩, rfl⟩
  · rintro ⟨u, v, ha, e⟩
    obtain ⟨-, ⟨j, hj, ej⟩ | ⟨j, hj, ej⟩⟩ := subG_adj.1 ha
    · have : j = i := Fin.ext ((hnd.getElem_inj_iff).1 (show E[j.val] = E[i.val] from ej.trans e.symm))
      subst this; exact hj
    · obtain ⟨k1, -⟩ := hE _ (List.getElem_mem j.2)
      rw [show E[j.val] = E[j] from rfl, ej] at k1
      rw [e] at h1
      simp only at k1 h1; omega

/-- The edges (u, v), u < v, of the graph with adjacency matrix M. -/
def edges (n : ℕ) (M : List Bool) : List (ℕ × ℕ) :=
  (pairs n).filter fun p => decide (p.1 < p.2) && adjB n M p.1 p.2

theorem edges_nodup (n : ℕ) (M : List Bool) : (edges n M).Nodup :=
  (List.nodup_range.product List.nodup_range).filter _

theorem edges_bound (n : ℕ) (M : List Bool) : ∀ p ∈ edges n M, p.1 < p.2 ∧ p.2 < n := by
  intro p hp
  obtain ⟨hp, hq⟩ := List.mem_filter.1 hp
  obtain ⟨-, h2⟩ := List.mem_product.1 hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨hq.1, List.mem_range.1 h2⟩

theorem mem_edges (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (u.val, v.val) ∈ edges n (matrix G) ↔ u < v ∧ G.Adj u v := by
  simp only [edges, pairs, List.mem_filter, List.mem_product, List.mem_range, u.2, v.2, and_self, true_and,
    Bool.and_eq_true, decide_eq_true_eq, hAdj n G u v]
  exact Iff.rfl

theorem subG_le (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin (edges n (matrix G)).length → Bool) :
    subG n (edges n (matrix G)) x ≤ G := by
  intro u v h
  obtain ⟨-, ⟨i, -, e⟩ | ⟨i, -, e⟩⟩ := subG_adj.1 h
  · have : (edges n (matrix G))[i] ∈ edges n (matrix G) := List.getElem_mem i.2
    rw [e, mem_edges hAdj] at this; exact this.2
  · have : (edges n (matrix G))[i] ∈ edges n (matrix G) := List.getElem_mem i.2
    rw [e, mem_edges hAdj] at this; exact this.2.symm

open Classical in
/-- At most deg(v) edges of the edge list are at v. -/
theorem length_inc_le (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (inc (edges n (matrix G)) v.val).length ≤ G.degree v := by
  have h := degree_subG (edges_bound n (matrix G)) (edges_nodup n (matrix G)) (fun _ => true) v
  rw [List.countP_eq_length.2 fun i hi => by simp [CountKSat.ext, lt_of_mem_inc hi]] at h
  rw [← h]; exact SimpleGraph.degree_le_of_le (subG_le hAdj G _)

/-- Every edge is at its first end, so there are at most Δ·n edges. -/
theorem length_edges_le {n Δ : ℕ} (E : List (ℕ × ℕ)) (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n)
    (hI : ∀ v < n, (inc E v).length ≤ Δ) : E.length ≤ Δ * n := by
  classical
  have hsub : range E.length ⊆ (range n).biUnion fun v => (inc E v).toFinset := by
    intro i hi
    have hi' := mem_range.1 hi
    have h1 := hE _ (List.getElem_mem hi')
    refine mem_biUnion.2 ⟨E[i].1, mem_range.2 (by omega), List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 hi', ?_⟩)⟩
    rw [List.getD_eq_getElem _ _ hi']; simp
  calc E.length = (range E.length).card := (card_range _).symm
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ v ∈ range n, (inc E v).toFinset.card := card_biUnion_le
    _ ≤ (range n).card • Δ := sum_le_card_nsmul _ _ _ fun v hv =>
        (List.toFinset_card_le _).trans (hI v (mem_range.1 hv))
    _ = Δ * n := by rw [card_range, smul_eq_mul, mul_comm]

open Classical in
/-- The Hamiltonian cycles of G, as edge sets: the connected spanning subgraphs H ≤ G with every
degree 2. -/
noncomputable def numHamCycles {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (univ.filter fun H : SimpleGraph (Fin n) => H ≤ G ∧ (∀ v, H.degree v = 2) ∧ H.Connected).card

open Classical in
/-- The choices of edges of G with every vertex on two of them and a connected subgraph are the
Hamiltonian cycles. -/
theorem card_hc (hAdj : StAdj) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter fun x : Fin (edges n (matrix G)).length → Bool =>
      (∀ v < n, (inc (edges n (matrix G)) v).countP (ext x) = 2) ∧ (subG n (edges n (matrix G)) x).Connected).card =
      numHamCycles G := by
  have hE := edges_bound n (matrix G)
  have hnd := edges_nodup n (matrix G)
  set E := edges n (matrix G) with hEd
  refine Finset.card_nbij (subG n E) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hd, hc⟩ := (mem_filter.1 (Finset.mem_coe.1 hx)).2
    refine Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, subG_le hAdj G x, fun v => ?_, hc⟩)
    rw [degree_subG hE hnd]; exact hd v v.2
  · intro x _ y _ h
    funext i
    exact Bool.eq_iff_iff.2 (by rw [x_iff hE hnd, x_iff hE hnd, h])
  · intro H hH
    obtain ⟨hle, hdeg, hc⟩ := (mem_filter.1 (Finset.mem_coe.1 hH)).2
    let x : Fin E.length → Bool := fun i => decide (∃ u v : Fin n, H.Adj u v ∧ E[i] = (u.val, v.val))
    have hx : subG n E x = H := by
      ext u v
      rw [subG_adj]
      constructor
      · rintro ⟨-, ⟨i, hi, e⟩ | ⟨i, hi, e⟩⟩
        · obtain ⟨u', v', ha, e'⟩ := of_decide_eq_true hi
          rw [e] at e'
          obtain ⟨h1, h2⟩ := Prod.mk.inj e'
          rwa [Fin.ext h1, Fin.ext h2]
        · obtain ⟨u', v', ha, e'⟩ := of_decide_eq_true hi
          rw [e] at e'
          obtain ⟨h1, h2⟩ := Prod.mk.inj e'
          rw [Fin.ext h1, Fin.ext h2]; exact ha.symm
      · intro ha
        refine ⟨H.ne_of_adj ha, ?_⟩
        rcases lt_or_gt_of_ne (H.ne_of_adj ha) with h | h
        · obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ((mem_edges hAdj G u v).2 ⟨h, hle ha⟩)
          exact Or.inl ⟨⟨i, hi⟩, decide_eq_true ⟨u, v, ha, e⟩, e⟩
        · obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ((mem_edges hAdj G v u).2 ⟨h, (hle ha).symm⟩)
          exact Or.inr ⟨⟨i, hi⟩, decide_eq_true ⟨v, u, ha.symm, e⟩, e⟩
    refine ⟨x, Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, fun v hv => ?_, hx ▸ hc⟩), hx⟩
    rw [← degree_subG hE hnd x ⟨v, hv⟩, hx, hdeg]

open Classical in
/-- **The parity**: the formula has as many satisfying assignments, mod 2, as G has Hamiltonian
cycles. -/
theorem hc_parity (hAdj : StAdj) {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    cntN ((edges n (matrix G)).length + n) (hcF n (edges n (matrix G))) % 2 = numHamCycles G % 2 := by
  have hE := edges_bound n (matrix G)
  rw [cntN_hcF, Finset.sum_nat_mod, ← card_hc hAdj G, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have hs : sides n (edges n (matrix G)) x = (univ.filter fun s : Fin n → Bool =>
      s ⟨0, hn⟩ = false ∧ ∀ u v, (subG n (edges n (matrix G)) x).Adj u v → s u = s v).card := by
    rw [sides]; congr 1; refine Finset.filter_congr fun s _ => ?_
    have h0 : ext s 0 = s ⟨0, hn⟩ := ext_fin s ⟨0, hn⟩
    rw [cons_iff hE, h0, and_comm]
  by_cases h1 : ∀ v < n, (inc (edges n (matrix G)) v).countP (ext x) = 2
  · rw [if_pos h1, hs, parity_sides hn]
    by_cases h2 : (subG n (edges n (matrix G)) x).Connected
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg fun h => h2 h.2]
  · rw [if_neg h1, if_neg fun h => h1 h.1]

end EthCor.Ham
