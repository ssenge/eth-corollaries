import EthCor.ColorFormula

/-! # Homomorphisms G → H as a CNF with the images written in binary

The target H is a relation on {0, …, h−1}, given by its h × h matrix (loops allowed, not necessarily
symmetric). Vertex v of G gets b = ⌈log₂ h⌉ variables, the bits of its image. Clauses: no vertex spells a
number in [h, 2^b); for every edge uv of G and every pair (a, c) with H(a, c) false, not both «u ↦ a» and
«v ↦ c»; every variable occurs (tautologies); four padding variables are forced true. So the formula
has n·b + 4 variables, width 2b, and exactly as many satisfying assignments as there are
homomorphisms from G to H (`cntN_homB`). For H = K_h these are the proper h-colorings
(`numColorings_eq`), for a simple graph H they are Mathlib's `G →g H` (`numHom_simple`). -/

namespace EthCor.Hom

open Groundwork Groundwork.Prog CountKSat GraphProblems Finset

/-- The h² entries of a relation on Fin h, row by row. -/
def hmat {h : ℕ} (H : Fin h → Fin h → Bool) : List Bool :=
  (List.finRange h).flatMap fun a => (List.finRange h).map fun c => H a c

/-- The number of maps from the vertices of G to Fin h that send every edge into H. -/
noncomputable def numHom {n h : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool) : ℕ :=
  Nat.card {f : Fin n → Fin h // ∀ u v, G.Adj u v → H (f u) (f v) = true}

/-- The formula of the homomorphisms to the relation with matrix mH, images in binary. -/
def homB (h n : ℕ) (mH m : List Bool) : Fml :=
  ((List.range n).flatMap fun v =>
      ((List.range (2 * h)).filter fun c => decide (h ≤ c) && decide (Nat.log2 c < nb h)).map fun c => forbid (nb h) v c) ++
  (((pairs n).filter fun p => adjB n m p.1 p.2).flatMap fun p =>
      ((pairs h).filter fun q => !adjB h mH q.1 q.2).map fun q => forbid (nb h) p.1 q.1 ++ forbid (nb h) p.2 q.2) ++
  ((List.range (n * nb h)).map fun i => [(i, true), (i, false)]) ++
  ((List.range 4).map fun i => [(n * nb h + i, true)])

theorem length_hmat {h : ℕ} (H : Fin h → Fin h → Bool) : (hmat H).length = h * h := by
  simp [hmat, List.length_flatMap]

theorem adjB_hmat {h : ℕ} (H : Fin h → Fin h → Bool) (a c : Fin h) : adjB h (hmat H) a c = H a c := by
  rw [adjB, hmat, GraphProblems.Read.getD_flatMap _ h false c.2 _ (by simp)]
  simp

/-! ### What the formula says -/

theorem sat_homB {h : ℕ} (hh : 2 ≤ h) (n : ℕ) (mH m : List Bool) (f : ℕ → Bool) :
    (∀ C ∈ homB h n mH m, ∃ l ∈ C, f l.1 = l.2) ↔
      (∀ v < n, colOf (nb h) f v < h) ∧
      (∀ u < n, ∀ v < n, adjB n m u v = true → adjB h mH (colOf (nb h) f u) (colOf (nb h) f v) = true) ∧
      ∀ i < 4, f (n * nb h + i) = true := by
  have h2 := two_pow_nb_le hh
  have hlt : ∀ v, colOf (nb h) f v < 2 ^ nb h := fun v => val_lt _ _
  simp only [homB, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_imp]
  constructor
  · rintro ⟨⟨⟨hA, hB⟩, -⟩, hD⟩
    have hA' : ∀ v < n, colOf (nb h) f v < h := fun v hv => by
      by_contra hge
      push Not at hge
      have hc := hlt v
      exact (sat_forbid hc f v).1 (hA v hv _ (by omega) hge ((Nat.log2_lt (by omega)).2 hc)) rfl
    refine ⟨hA', fun u hu v hv huv => ?_, fun i hi => ?_⟩
    · by_contra hne
      have hne' : adjB h mH (colOf (nb h) f u) (colOf (nb h) f v) = false := by simpa using hne
      obtain ⟨l, hl, hfl⟩ := hB (u, v) (GraphProblems.Color.mem_pairs.2 ⟨hu, hv⟩) huv
        (colOf (nb h) f u, colOf (nb h) f v) (GraphProblems.Color.mem_pairs.2 ⟨hA' u hu, hA' v hv⟩) hne'
      rcases List.mem_append.1 hl with hl | hl
      · exact (sat_forbid (hlt u) f u).1 ⟨l, hl, hfl⟩ rfl
      · exact (sat_forbid (hlt v) f v).1 ⟨l, hl, hfl⟩ rfl
    · obtain ⟨l, hl, hfl⟩ := hD i hi
      rw [List.mem_singleton] at hl
      subst hl; exact hfl
  · rintro ⟨hA, hB, hD⟩
    refine ⟨⟨⟨fun v hv c _ hkc hlog => ?_, fun p hp hadj q hq hnq => ?_⟩, fun i _ => ⟨(i, f i), ?_, rfl⟩⟩,
      fun i hi => ⟨_, List.mem_singleton.2 rfl, hD i hi⟩⟩
    · have hc2 : c < 2 ^ nb h := (Nat.log2_lt (by omega)).1 hlog
      exact (sat_forbid hc2 f v).2 (by have := hA v hv; omega)
    · have hp' := GraphProblems.Color.mem_pairs.1 hp
      have hq' := GraphProblems.Color.mem_pairs.1 hq
      have hc1 : q.1 < 2 ^ nb h := lt_of_lt_of_le hq'.1 (le_two_pow_nb hh)
      have hc2 : q.2 < 2 ^ nb h := lt_of_lt_of_le hq'.2 (le_two_pow_nb hh)
      by_cases hu : colOf (nb h) f p.1 = q.1
      · have hv : colOf (nb h) f p.2 ≠ q.2 := fun hv => by
          have := hB p.1 hp'.1 p.2 hp'.2 hadj
          rw [hu, hv, hnq] at this
          exact Bool.false_ne_true this
        obtain ⟨l, hl, hfl⟩ := (sat_forbid hc2 f p.2).2 hv
        exact ⟨l, List.mem_append_right _ hl, hfl⟩
      · obtain ⟨l, hl, hfl⟩ := (sat_forbid hc1 f p.1).2 hu
        exact ⟨l, List.mem_append_left _ hl, hfl⟩
    · cases f i <;> simp

/-! ### Counting -/

theorem sat_asgH {h : ℕ} (hh : 2 ≤ h) {n : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool)
    (f : Fin n → Fin h) (hf : ∀ u v, G.Adj u v → H (f u) (f v) = true) :
    ∀ C ∈ homB h n (hmat H) (matrix G), ∃ l ∈ C, ext (asgB f) l.1 = l.2 := by
  rw [sat_homB hh]
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun i hi => ext_asgB_pad f hi⟩
  · rw [show v = (⟨v, hv⟩ : Fin n).val from rfl, colOf_asgB hh]; exact (f _).2
  · rw [show u = (⟨u, hu⟩ : Fin n).val from rfl, show v = (⟨v, hv⟩ : Fin n).val from rfl, colOf_asgB hh,
      colOf_asgB hh, adjB_hmat]
    exact hf _ _ ((stAdj n G ⟨u, hu⟩ ⟨v, hv⟩).1 huv)

theorem exists_homB {h : ℕ} (hh : 2 ≤ h) {n : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool)
    (a : Fin (n * nb h + 4) → Bool) (ha : ∀ C ∈ homB h n (hmat H) (matrix G), ∃ l ∈ C, ext a l.1 = l.2) :
    ∃ f : Fin n → Fin h, (∀ u v, G.Adj u v → H (f u) (f v) = true) ∧ asgB f = a := by
  obtain ⟨hA, hB, hD⟩ := (sat_homB hh n (hmat H) (matrix G) (ext a)).1 ha
  have hb := one_le_nb hh
  refine ⟨fun v => ⟨colOf (nb h) (ext a) v, hA v v.2⟩, fun u v huv => ?_, ?_⟩
  · rw [← adjB_hmat H]
    exact hB u u.2 v v.2 ((stAdj n G u v).2 huv)
  funext x
  by_cases hx : x.val < n * nb h
  · have hv : x.val / nb h < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hx (mul_comm n (nb h)))
    have hj : x.val % nb h < nb h := Nat.mod_lt _ (by omega)
    have hxe : x.val = x.val / nb h * nb h + x.val % nb h := (Nat.div_add_mod' x.val (nb h)).symm
    change asgB _ x = a x
    rw [asgB, dif_pos hx]
    change (colOf (nb h) (ext a) (x.val / nb h)).testBit (x.val % nb h) = a x
    rw [colOf, testBit_val, decide_eq_true hj, Bool.true_and, ← hxe, ext_val' a]
  · have hi : x.val - n * nb h < 4 := by have := x.2; omega
    have := hD _ hi
    rw [show n * nb h + (x.val - n * nb h) = x.val by omega, ext_val' a] at this
    change asgB _ x = a x
    rw [asgB, dif_neg hx, this]

/-- The formula has as many satisfying assignments as there are homomorphisms from G to H. -/
theorem cntN_homB {h : ℕ} (hh : 2 ≤ h) {n : ℕ} (G : SimpleGraph (Fin n)) (H : Fin h → Fin h → Bool) :
    cntN (n * nb h + 4) (homB h n (hmat H) (matrix G)) = numHom G H := by
  rw [numHom, cntN, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hmem : ∀ f : {f : Fin n → Fin h // ∀ u v, G.Adj u v → H (f u) (f v) = true},
      asgB f.1 ∈ univ.filter fun a : Fin (n * nb h + 4) → Bool =>
        ∀ C ∈ homB h n (hmat H) (matrix G), ∃ l ∈ C, ext a l.1 = l.2 :=
    fun f => mem_filter.2 ⟨mem_univ _, sat_asgH hh G H f.1 f.2⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun f => (⟨asgB f.1, hmem f⟩ : {a // a ∈ univ.filter
    fun a : Fin (n * nb h + 4) → Bool => ∀ C ∈ homB h n (hmat H) (matrix G), ∃ l ∈ C, ext a l.1 = l.2}))
      ⟨?_, ?_⟩)).symm
  · intro f f' e
    exact Subtype.ext (asgB_injective hh (congrArg Subtype.val e))
  · rintro ⟨a, ha⟩
    obtain ⟨f, hf, hfa⟩ := exists_homB hh G H a (mem_filter.1 ha).2
    exact ⟨⟨f, hf⟩, Subtype.ext hfa⟩

/-! ### Mathlib's homomorphisms and colorings -/

/-- For a simple graph H, the homomorphisms counted are Mathlib's `G →g H`. -/
theorem numHom_simple {n h : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin h)) [DecidableRel H.Adj] :
    numHom G (fun a c => decide (H.Adj a c)) = Nat.card (G →g H) := by
  rw [numHom]
  exact Nat.card_congr
    { toFun := fun f => ⟨f.1, fun {u v} huv => of_decide_eq_true (f.2 u v huv)⟩
      invFun := fun φ => ⟨φ, fun u v huv => decide_eq_true (φ.map_rel huv)⟩
      left_inv := fun f => rfl
      right_inv := fun φ => rfl }

/-- The proper k-colorings are the homomorphisms to the relation «≠» on Fin k. -/
theorem numColorings_eq {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    numColorings G k = numHom G (fun a c : Fin k => decide (a ≠ c)) := by
  rw [numColorings, numHom]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ, fun u v huv => decide_eq_true ((SimpleGraph.top_adj _ _).1 (φ.map_rel huv))⟩
      invFun := fun f => ⟨f.1, fun {u v} huv => (SimpleGraph.top_adj _ _).2 (of_decide_eq_true (f.2 u v huv))⟩
      left_inv := fun φ => rfl
      right_inv := fun f => rfl }

end EthCor.Hom
