import EthCor.ConnIso

/-! # Cut & Count for induced forests

For a graph H with S side maps (maps to Bool constant along the edges, 2^{cc(H)} of them) and e
edges, S·2^e = 2^{|V|+j} where j = 0 exactly if H is acyclic (`sides_edges`, by induction on the
edges: an edge between two components halves S, an edge inside a component leaves S unchanged and
closes a cycle). -/

namespace EthCor.Forest

open Finset SimpleGraph Groundwork.Prog CountKSat GraphProblems EthCor.Ham EthCor.HamS EthCor.HamI EthCor.HamITM
  EthCor.Iso EthCor.Conn EthCor.ConnI

section Graph

variable {W : Type} [Fintype W] [LinearOrder W]

omit [Fintype W] [LinearOrder W] in
/-- Side maps are constant on the reachability classes. -/
theorem sides_reach (H : SimpleGraph W) (s : W → Bool) (h : ∀ a b, H.Adj a b → s a = s b) {a b : W}
    (hab : H.Reachable a b) : s a = s b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons h' _ ih => exact (h _ _ h').trans ih

open Classical in
/-- The flip of the side of everything reachable from v: if u and v are not joined in H, half the
side maps of H have s u = s v. -/
theorem card_sides_eq (H : SimpleGraph W) {u v : W} (hr : ¬ H.Reachable u v) :
    (univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b).card =
      2 * (univ.filter fun s : W → Bool => (∀ a b, H.Adj a b → s a = s b) ∧ s u = s v).card := by
  set S := univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b with hSdef
  have hsplit := card_filter_add_card_filter_not (s := S) (fun s => s u = s v)
  have h1 : S.filter (fun s => s u = s v) =
      univ.filter fun s : W → Bool => (∀ a b, H.Adj a b → s a = s b) ∧ s u = s v := by
    ext s; simp only [hSdef, mem_filter, mem_univ, true_and]
  let fl : (W → Bool) → (W → Bool) := fun s w => if H.Reachable v w then !s w else s w
  have hfl2 : ∀ s, fl (fl s) = s := fun s => by
    funext w; by_cases h : H.Reachable v w <;> simp [fl, h]
  have hvu : ¬ H.Reachable v u := fun h => hr h.symm
  have hflu : ∀ s, fl s u = s u := fun s => by simp [fl, hvu]
  have hflv : ∀ s, fl s v = !s v := fun s => by simp [fl]
  have hflS : ∀ s ∈ S, fl s ∈ S := by
    intro s hs
    have hs' := (mem_filter.1 hs).2
    refine mem_filter.2 ⟨mem_univ _, fun a b hab => ?_⟩
    have hab' : H.Reachable v a ↔ H.Reachable v b :=
      ⟨fun h => h.trans hab.reachable, fun h => h.trans hab.reachable.symm⟩
    by_cases h : H.Reachable v a
    · simp [fl, h, hab'.1 h, hs' a b hab]
    · simp [fl, h, mt hab'.2 h, hs' a b hab]
  have hne : ∀ s, (s u = s v ↔ ¬ fl s u = fl s v) := fun s => by
    rw [hflu, hflv]; cases s u <;> cases s v <;> simp
  have hbij : (S.filter fun s => s u = s v).card = (S.filter fun s => ¬ s u = s v).card := by
    refine Finset.card_bij (fun s _ => fl s) (fun s hs => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
    · obtain ⟨hs, e⟩ := mem_filter.1 hs
      exact mem_filter.2 ⟨hflS s hs, (hne s).1 e⟩
    · rw [← hfl2 s, h, hfl2]
    · obtain ⟨ht, e⟩ := mem_filter.1 ht
      refine ⟨fl t, mem_filter.2 ⟨hflS t ht, ?_⟩, hfl2 t⟩
      rw [hne, hfl2]; exact e
  rw [← h1]
  omega

open Classical in
/-- **Side maps and edges.** A graph H on W with S side maps and e edges has S·2^e = 2^{|W|+j}, and
j = 0 exactly if H is acyclic. -/
theorem sides_edges (H : SimpleGraph W) : ∃ j,
    (univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b).card *
      2 ^ (univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2).card = 2 ^ (Fintype.card W + j) ∧
    (j = 0 ↔ H.IsAcyclic) := by
  obtain ⟨k, hk⟩ : ∃ k, (univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2).card = k := ⟨_, rfl⟩
  induction k generalizing H with
  | zero =>
    have hno : ∀ a b, ¬ H.Adj a b := by
      intro a b h
      have hE := card_eq_zero.1 hk
      rcases lt_trichotomy a b with hab | rfl | hab
      · have : (a, b) ∈ univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2 := by simp [hab, h]
        rw [hE] at this; simp at this
      · exact H.loopless.irrefl _ h
      · have : (b, a) ∈ univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2 := by simp [hab, h.symm]
        rw [hE] at this; simp at this
    refine ⟨0, ?_, by simpa using isAcyclic_iff_forall_adj_isBridge.2 fun a b h => absurd h (hno a b)⟩
    have : (univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b) = univ :=
      filter_true_of_mem fun s _ a b h => absurd h (hno a b)
    rw [hk, this, card_univ, Fintype.card_fun, Fintype.card_bool]; simp
  | succ k ih =>
    obtain ⟨⟨u, v⟩, huv⟩ := card_pos.1 (show 0 < (univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2).card
      by omega)
    simp only [mem_filter, mem_univ, true_and] at huv
    obtain ⟨hlt, hadj⟩ := huv
    obtain ⟨H', hH'⟩ : ∃ H', H' = H.deleteEdges {s(u, v)} := ⟨_, rfl⟩
    have hH'adj : ∀ a b, H'.Adj a b ↔ H.Adj a b ∧ ¬ s(a, b) = s(u, v) := fun a b => by
      rw [hH', deleteEdges_adj, Set.mem_singleton_iff]
    have hH : H = H' ⊔ edge u v := by
      ext a b
      rw [sup_adj, hH'adj, edge_adj]
      constructor
      · intro h
        by_cases e : s(a, b) = s(u, v)
        · refine Or.inr ⟨?_, H.ne_of_adj h⟩
          rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨h, e⟩
      · rintro (⟨h, -⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩)
        · exact h
        · exact hadj
        · exact hadj.symm
    have hk' : (univ.filter fun p : W × W => p.1 < p.2 ∧ H'.Adj p.1 p.2).card = k := by
      have e : (univ.filter fun p : W × W => p.1 < p.2 ∧ H.Adj p.1 p.2) =
          insert (u, v) (univ.filter fun p : W × W => p.1 < p.2 ∧ H'.Adj p.1 p.2) := by
        ext ⟨a, b⟩
        simp only [mem_filter, mem_univ, true_and, mem_insert, Prod.mk.injEq, hH'adj]
        constructor
        · rintro ⟨hab, h⟩
          by_cases e : s(a, b) = s(u, v)
          · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact absurd hab (not_lt.2 hlt.le)
          · exact Or.inr ⟨hab, h, e⟩
        · rintro (⟨rfl, rfl⟩ | ⟨hab, h, -⟩)
          · exact ⟨hlt, hadj⟩
          · exact ⟨hab, h⟩
      rw [e, card_insert_of_notMem (by simp [hH'adj])] at hk
      omega
    obtain ⟨j, hj, hjA⟩ := ih H' hk'
    rw [hk'] at hj
    have hcons : ∀ s : W → Bool, (∀ a b, H.Adj a b → s a = s b) ↔
        (∀ a b, H'.Adj a b → s a = s b) ∧ s u = s v := by
      intro s
      constructor
      · intro h
        exact ⟨fun a b hab => h a b ((hH'adj a b).1 hab).1, h u v hadj⟩
      · rintro ⟨h, huv⟩ a b hab
        by_cases e : s(a, b) = s(u, v)
        · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact huv
          · exact huv.symm
        · exact h a b ((hH'adj a b).2 ⟨hab, e⟩)
    have hS : (univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b) =
        univ.filter fun s : W → Bool => (∀ a b, H'.Adj a b → s a = s b) ∧ s u = s v :=
      filter_congr fun s _ => hcons s
    by_cases hr : H'.Reachable u v
    · have hS' : (univ.filter fun s : W → Bool => ∀ a b, H.Adj a b → s a = s b) =
          univ.filter fun s : W → Bool => ∀ a b, H'.Adj a b → s a = s b := by
        rw [hS]
        exact filter_congr fun s _ => ⟨fun h => h.1, fun h => ⟨h, sides_reach H' s h hr⟩⟩
      refine ⟨j + 1, ?_, ?_⟩
      · rw [hk, hS', pow_succ, ← mul_assoc, hj, ← pow_succ]; rfl
      · simp only [Nat.add_one_ne_zero, false_iff]
        rw [hH, isAcyclic_sup_fromEdgeSet_iff]
        rintro ⟨-, h⟩
        rcases h hr with h | h
        · exact hlt.ne h
        · exact ((hH'adj u v).1 h).2 rfl
    · refine ⟨j, ?_, by rw [hjA, hH, isAcyclic_add_edge_iff_of_not_reachable u v hr]⟩
      rw [hk, pow_succ, mul_comm (2 ^ k), ← mul_assoc, hS, mul_comm _ 2, ← card_sides_eq H' hr, hj]

end Graph

/-! ### The formula -/

/-- b_i → x_u ∧ x_v for the bit b_i = 3n + i of the edge i = (u, v). -/
def ebF (n : ℕ) (E : List (ℕ × ℕ)) : Fml := (List.range E.length).flatMap fun i =>
  [[(n + n + n + i, false), ((E.getD i (0, 0)).1, true)], [(n + n + n + i, false), ((E.getD i (0, 0)).2, true)]]

/-- The formula of induced forests on 3n + 2m variables: `connF`, an edge bit for every edge of the
set, and the complements of the edge bits. -/
def fvsF (n : ℕ) (E : List (ℕ × ℕ)) (ψ : Fml) : Fml := connF n E ψ ++ ebF n E ++ compF (n + n + n) E.length

theorem sat_ebF (f : ℕ → Bool) (n : ℕ) (E : List (ℕ × ℕ)) : (∀ C ∈ ebF n E, ∃ l ∈ C, f l.1 = l.2) ↔
    ∀ i < E.length, f (n + n + n + i) = true → f (E.getD i (0, 0)).1 = true ∧ f (E.getD i (0, 0)).2 = true := by
  rw [ebF, forall_flatMap_range]
  refine forall₂_congr fun i _ => ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat2]
  generalize f (n + n + n + i) = a, f (E.getD i (0, 0)).1 = b, f (E.getD i (0, 0)).2 = c
  cases a <;> cases b <;> cases c <;> decide

theorem getD_bound {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {i : ℕ} (hi : i < E.length) :
    (E.getD i (0, 0)).1 < n ∧ (E.getD i (0, 0)).2 < n := by
  have := hE _ (List.getElem_mem hi)
  rw [List.getD_eq_getElem _ _ hi]
  omega

theorem ebF_vars {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) :
    ∀ C ∈ ebF n E, ∀ l ∈ C, l.1 < n + n + n + E.length := by
  intro C hC l hl
  obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
  rw [List.mem_range] at hi
  have := getD_bound hE hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl <;> dsimp only <;> omega

theorem ext_sub {N n : ℕ} (y : Fin N → Bool) {e : ℕ} (he : e < n) : ext (fun j : Fin n => ext y j.val) e = ext y e := by
  conv_lhs => rw [CountKSat.ext, dif_pos he]

/-! ### The count -/

/-- The edge bits b mark only edges inside x. -/
def EdgeIn {n : ℕ} (E : List (ℕ × ℕ)) (b : Fin E.length → Bool) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin E.length, b i = true → ext x (E.getD i (0, 0)).1 = true ∧ ext x (E.getD i (0, 0)).2 = true

open Classical in
/-- 2^e edge bits mark only edges inside x, e the number of edges inside x. -/
theorem card_edgeIn {n : ℕ} (E : List (ℕ × ℕ)) (x : Fin n → Bool) :
    (univ.filter fun b => EdgeIn E b x).card = 2 ^ (univ.filter fun i : Fin E.length =>
      ext x (E.getD i (0, 0)).1 = true ∧ ext x (E.getD i (0, 0)).2 = true).card := by
  have e : (univ.filter fun b => EdgeIn E b x) = Fintype.piFinset fun i : Fin E.length =>
      if ext x (E.getD i (0, 0)).1 = true ∧ ext x (E.getD i (0, 0)).2 = true then univ else {false} := by
    ext b
    rw [mem_filter, Fintype.mem_piFinset]
    simp only [EdgeIn, mem_univ, true_and]
    refine forall_congr' fun i => ?_
    split_ifs with h
    · exact ⟨fun _ => mem_univ _, fun _ _ => h⟩
    · rw [mem_singleton]
      constructor
      · intro hb
        by_contra hne
        exact h (hb (by simpa using hne))
      · intro hb hbt
        rw [hb] at hbt
        exact absurd hbt (by decide)
  rw [e, Fintype.card_piFinset, prod_congr rfl fun i _ => apply_ite Finset.card _ _ _, prod_ite]
  simp

section Count

variable {n : ℕ} {E : List (ℕ × ℕ)}

/-- Step F: the complements of the edge bits are determined. -/
theorem stepF (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] (s : ℕ) :
    (univ.filter fun w : Fin (n + n + n + E.length + E.length) → Bool =>
      ((∀ C ∈ fvsF n E ψ, ∃ l ∈ C, ext w l.1 = l.2) ∧ P (fun j => ext w j.val)) ∧
        (univ.filter fun i => w i = true).card = s).card =
    (univ.filter fun w : Fin (n + n + n + E.length) → Bool =>
      ((∀ C ∈ connF n E ψ ++ ebF n E, ∃ l ∈ C, ext w l.1 = l.2) ∧ P (fun j => ext w j.val)) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (n + n + n) i)) i = true).card = s).card := by
  refine card_append _ _ (fun w i => !w (Fin.natAdd (n + n + n) i)) fun w h => ?_
  have hlt : ∀ a < n + n + n + E.length, ext (Fin.append w h) a = ext w a := fun a ha => ext_append_lt w h ha
  have hvars : ∀ C ∈ connF n E ψ ++ ebF n E, ∀ l ∈ C, l.1 < n + n + n + E.length := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · have := (connF_vars hE hψ C hC).2 l hl; omega
    · exact ebF_vars hE C hC l hl
  have hP : (fun j : Fin n => ext (Fin.append w h) j.val) = fun j => ext w j.val :=
    funext fun j => hlt _ (by omega)
  rw [fvsF, List.forall_mem_append, sat_congr (f' := ext w) (fun C hC l hl => hlt _ (hvars C hC l hl)), sat_compF, hP]
  have hc : (∀ i < E.length, ext (Fin.append w h) (n + n + n + E.length + i) =
      !ext (Fin.append w h) (n + n + n + i)) ↔ h = fun i => !w (Fin.natAdd (n + n + n) i) := by
    rw [← comp_iff w h]
    exact forall₂_congr fun i hi => by rw [ext_append_ge, hlt _ (by omega)]
  rw [hc]
  constructor
  · rintro ⟨⟨⟨h1, rfl⟩, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩; exact ⟨⟨⟨h1, rfl⟩, h2⟩, h3⟩

open Classical in
/-- Step G: the edge bits, summed over. -/
theorem stepG (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (P : (Fin n → Bool) → Prop) (s : ℕ) :
    (univ.filter fun w : Fin (n + n + n + E.length) → Bool =>
      ((∀ C ∈ connF n E ψ ++ ebF n E, ∃ l ∈ C, ext w l.1 = l.2) ∧ P (fun j => ext w j.val)) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (n + n + n) i)) i = true).card =
          n + s + E.length).card =
    ∑ b : Fin E.length → Bool, (univ.filter fun y : Fin (n + n + n) → Bool =>
      ((∀ C ∈ connF n E ψ, ∃ l ∈ C, ext y l.1 = l.2) ∧ (fun x => EdgeIn E b x ∧ P x) (fun j => ext y j.val)) ∧
        (univ.filter fun i => y i = true).card = n + s).card := by
  rw [Finset.card_equiv (Fin.appendEquiv (n + n + n) E.length).symm
    (t := univ.filter fun p : (Fin (n + n + n) → Bool) × (Fin E.length → Bool) =>
      ((∀ C ∈ connF n E ψ, ∃ l ∈ C, ext p.1 l.1 = l.2) ∧ (fun x => EdgeIn E p.2 x ∧ P x) (fun j => ext p.1 j.val)) ∧
        (univ.filter fun i => p.1 i = true).card = n + s)]
  · rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.card_filter]
  · intro w
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨p, rfl⟩ : ∃ p, w = Fin.appendEquiv (n + n + n) E.length p :=
      ⟨_, ((Fin.appendEquiv _ _).apply_symm_apply w).symm⟩
    rw [Equiv.symm_apply_apply]
    have hw : (Fin.appendEquiv (n + n + n) E.length) p = Fin.append p.1 p.2 :=
      funext fun a => Fin.appendEquiv_apply _ _ _ _
    rw [hw]
    obtain ⟨y, b⟩ := p
    dsimp only
    have hlt : ∀ a < n + n + n, ext (Fin.append y b) a = ext y a := fun a ha => ext_append_lt y b ha
    have hx : (fun j : Fin n => ext (Fin.append y b) j.val) = fun j => ext y j.val :=
      funext fun j => hlt _ (by omega)
    rw [List.forall_mem_append, sat_congr (f' := ext y) (fun C hC l hl => hlt _ ((connF_vars hE hψ C hC).2 l hl)),
      sat_ebF, hx, count_comp]
    have hQ : (∀ i < E.length, ext (Fin.append y b) (n + n + n + i) = true →
        ext (Fin.append y b) (E.getD i (0, 0)).1 = true ∧ ext (Fin.append y b) (E.getD i (0, 0)).2 = true) ↔
        EdgeIn E b (fun j : Fin n => ext y j.val) := by
      unfold EdgeIn
      constructor
      · intro h i hi
        have hb := getD_bound hE i.2
        have := h i.val i.2 (by rw [ext_append_ge, ext_fin]; exact hi)
        rw [hlt _ (by omega), hlt _ (by omega)] at this
        rw [ext_sub y hb.1, ext_sub y hb.2]
        exact this
      · intro h i hi hbi
        have hb := getD_bound hE hi
        rw [ext_append_ge] at hbi
        have := h ⟨i, hi⟩ (by rw [← ext_fin b ⟨i, hi⟩]; exact hbi)
        rw [ext_sub y hb.1, ext_sub y hb.2] at this
        rw [hlt _ (by omega), hlt _ (by omega)]
        exact this
    rw [hQ]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h2, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, by omega⟩

open Classical in
/-- **The count of `fvsF`**: the vertex sets x of size s that satisfy ψ and P, each with weight
sig(x)·2^{e(x)}, e(x) the number of edges inside x. -/
theorem fvs_count (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (P : (Fin n → Bool) → Prop) (s : ℕ) :
    (univ.filter fun w : Fin (n + n + n + E.length + E.length) → Bool =>
      ((∀ C ∈ fvsF n E ψ, ∃ l ∈ C, ext w l.1 = l.2) ∧ P (fun j => ext w j.val)) ∧
        (univ.filter fun i => w i = true).card = n + s + E.length).card =
    ∑ x : Fin n → Bool, if ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
      then sig n E x * 2 ^ (univ.filter fun i : Fin E.length =>
        ext x (E.getD i (0, 0)).1 = true ∧ ext x (E.getD i (0, 0)).2 = true).card else 0 := by
  rw [stepF hE hψ P, stepG hE hψ P,
    Finset.sum_congr rfl fun b _ => (cnt_stepA hE hψ (fun x => EdgeIn E b x ∧ P x)).trans
      (cnt_stepB hE hψ (fun x => EdgeIn E b x ∧ P x)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
  · rw [if_pos hx, ← card_edgeIn, mul_comm, ← smul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : EdgeIn E b x
    · rw [if_pos ⟨⟨hx.1.1, hb, hx.1.2⟩, hx.2⟩, if_pos hb]
    · rw [if_neg fun h => hb h.1.2.1, if_neg hb]
  · rw [if_neg hx]
    exact Finset.sum_eq_zero fun b _ => if_neg fun h => hx ⟨⟨h.1.1, h.1.2.2⟩, h.2⟩

end Count

/-! ### The parity -/

open Classical in
/-- The edges of the edge list inside x are the edges of G[x]. -/
theorem card_inE {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    (univ.filter fun i : Fin (edges n (matrix G)).length =>
      ext x ((edges n (matrix G)).getD i (0, 0)).1 = true ∧ ext x ((edges n (matrix G)).getD i (0, 0)).2 = true).card =
    (univ.filter fun p : ({v | x v = true} : Set (Fin n)) × ({v | x v = true} : Set (Fin n)) =>
      p.1 < p.2 ∧ (G.induce {v | x v = true}).Adj p.1 p.2).card := by
  have hE := edges_bound n (matrix G)
  have hext : ∀ {k : ℕ} (hk : k < n), ext x k = x ⟨k, hk⟩ := fun hk => by simp [CountKSat.ext, hk]
  refine Finset.card_bij (fun i hi =>
      ((⟨⟨((edges n (matrix G)).getD i (0, 0)).1, (getD_bound hE i.2).1⟩,
          by have h := (mem_filter.1 hi).2.1; rwa [hext] at h⟩ : ({v | x v = true} : Set (Fin n))),
        (⟨⟨((edges n (matrix G)).getD i (0, 0)).2, (getD_bound hE i.2).2⟩,
          by have h := (mem_filter.1 hi).2.2; rwa [hext] at h⟩ : ({v | x v = true} : Set (Fin n)))))
    (fun i hi => ?_) (fun i hi j hj h => ?_) (fun p hp => ?_)
  · have hm : ((edges n (matrix G)).getD i (0, 0)) ∈ edges n (matrix G) := by
      rw [List.getD_eq_getElem _ _ i.2]; exact List.getElem_mem i.2
    have h := (mem_edges stAdj G ⟨_, (getD_bound hE i.2).1⟩ ⟨_, (getD_bound hE i.2).2⟩).1 hm
    exact mem_filter.2 ⟨mem_univ _, h.1, by rw [induce_adj]; exact h.2⟩
  · simp only [Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h
    have e : (edges n (matrix G))[i.val] = (edges n (matrix G))[j.val] := by
      rw [← List.getD_eq_getElem _ (0, 0) i.2, ← List.getD_eq_getElem _ (0, 0) j.2]
      exact Prod.ext h.1 h.2
    exact Fin.ext ((edges_nodup n (matrix G)).getElem_inj_iff.1 e)
  · obtain ⟨⟨⟨a, ha⟩, hxa⟩, ⟨⟨b, hb⟩, hxb⟩⟩ := p
    obtain ⟨hab, hadj⟩ := (mem_filter.1 hp).2
    rw [induce_adj] at hadj
    have hm := (mem_edges stAdj G ⟨a, ha⟩ ⟨b, hb⟩).2 ⟨hab, hadj⟩
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
    have e' : (edges n (matrix G)).getD i (0, 0) = (a, b) := by rw [List.getD_eq_getElem _ _ hi]; exact e
    refine ⟨⟨i, hi⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [e', hext ha, hext hb]; exact ⟨hxa, hxb⟩
    · simp only [e']

open Classical in
/-- The weight of x: sig(x)·2^{e(x)} = 2^{|x|+j}, and j = 0 exactly if G[x] is a forest. -/
theorem weight_eq {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : ∃ j,
    sig n (edges n (matrix G)) x * 2 ^ (univ.filter fun i : Fin (edges n (matrix G)).length =>
      ext x ((edges n (matrix G)).getD i (0, 0)).1 = true ∧
        ext x ((edges n (matrix G)).getD i (0, 0)).2 = true).card =
      2 ^ ((univ.filter fun v => x v = true).card + j) ∧ (j = 0 ↔ (G.induce {v | x v = true}).IsAcyclic) := by
  obtain ⟨j, hj, hjA⟩ := sides_edges (G.induce {v | x v = true})
  refine ⟨j, ?_, hjA⟩
  have hc : Fintype.card ({v | x v = true} : Set (Fin n)) = (univ.filter fun v => x v = true).card := by
    simp only [Set.mem_ofPred_eq, Fintype.card_subtype]
  rw [sig_eq, card_inE, ← hc]
  convert hj using 3 <;> first | (ext; simp) | simp

open Classical in
/-- **Cut & Count for induced forests, with a property P of the vertex set**: the number of
satisfying assignments of `fvsF` with n + s + m true variables and P on the vertex bits, divided by
2^s, has the parity of the number of sets X of size s with X ⊨ ψ, P X and G[X] a forest. -/
theorem fvs_parity_P {n : ℕ} (G : SimpleGraph (Fin n)) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (P : (Fin n → Bool) → Prop) (s : ℕ) :
    (univ.filter fun w : Fin (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length) → Bool =>
      ((∀ C ∈ fvsF n (edges n (matrix G)) ψ, ∃ l ∈ C, ext w l.1 = l.2) ∧ P (fun j => ext w j.val)) ∧
        (univ.filter fun i => w i = true).card = n + s + (edges n (matrix G)).length).card / 2 ^ s % 2 =
    (univ.filter fun x : Fin n → Bool => ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧
      (univ.filter fun v => x v = true).card = s ∧ (G.induce {v | x v = true}).IsAcyclic).card % 2 := by
  rw [fvs_count (edges_bound n (matrix G)) hψ P s]
  have key : ∀ x : Fin n → Bool,
      (if ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
        then sig n (edges n (matrix G)) x * 2 ^ (univ.filter fun i : Fin (edges n (matrix G)).length =>
          ext x ((edges n (matrix G)).getD i (0, 0)).1 = true ∧
            ext x ((edges n (matrix G)).getD i (0, 0)).2 = true).card else 0) =
        2 ^ s * (if ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
          then sig n (edges n (matrix G)) x * 2 ^ (univ.filter fun i : Fin (edges n (matrix G)).length =>
            ext x ((edges n (matrix G)).getD i (0, 0)).1 = true ∧
              ext x ((edges n (matrix G)).getD i (0, 0)).2 = true).card / 2 ^ s else 0) ∧
      (if ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
          then sig n (edges n (matrix G)) x * 2 ^ (univ.filter fun i : Fin (edges n (matrix G)).length =>
            ext x ((edges n (matrix G)).getD i (0, 0)).1 = true ∧
              ext x ((edges n (matrix G)).getD i (0, 0)).2 = true).card / 2 ^ s else 0) % 2 =
        if ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s ∧
          (G.induce {v | x v = true}).IsAcyclic then 1 else 0 := by
    intro x
    by_cases hQ : ((∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧ P x) ∧ (univ.filter fun v => x v = true).card = s
    · obtain ⟨j, hj, hjA⟩ := weight_eq G x
      rw [hQ.2] at hj
      rw [if_pos hQ, if_pos hQ, hj, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
      refine ⟨rfl, ?_⟩
      by_cases ha : (G.induce {v | x v = true}).IsAcyclic
      · rw [if_pos ⟨hQ.1, hQ.2, ha⟩, hjA.2 ha, pow_zero]; rfl
      · rw [if_neg fun h => ha h.2.2]
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero fun h => ha (hjA.1 h)
        rw [pow_succ, Nat.mul_mod_left]
    · rw [if_neg hQ, if_neg hQ, if_neg fun h => hQ ⟨h.1, h.2.1⟩]
      simp
  rw [Finset.sum_congr rfl fun x _ => (key x).1, ← Finset.mul_sum, Nat.mul_div_cancel_left _ (by positivity),
    Finset.sum_nat_mod, Finset.sum_congr rfl fun x _ => (key x).2, ← Finset.card_filter]

open Classical in
/-- The vertex sets of size s that satisfy ψ and induce a forest. -/
noncomputable def numForF {n : ℕ} (G : SimpleGraph (Fin n)) (ψ : Fml) (s : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
    (univ.filter fun v => x v = true).card = s ∧ (G.induce {v | x v = true}).IsAcyclic).card

open Classical in
/-- **Cut & Count for induced forests**: the number of satisfying assignments of `fvsF` with
n + s + m true variables, divided by 2^s, has the parity of the number of sets X of size s with
X ⊨ ψ and G[X] a forest. -/
theorem fvs_parity {n : ℕ} (G : SimpleGraph (Fin n)) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (s : ℕ) :
    cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
      (n + s + (edges n (matrix G)).length) (fvsF n (edges n (matrix G)) ψ) / 2 ^ s % 2 = numForF G ψ s % 2 := by
  have h := fvs_parity_P G hψ (fun _ => True) s
  simp only [and_true] at h
  unfold cntS numForF
  exact h

theorem fvsF_vars {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : ∀ C ∈ fvsF n E ψ, ∀ l ∈ C, l.1 < n + n + n + E.length + E.length := by
  intro C hC l hl
  simp only [fvsF, List.mem_append] at hC
  rcases hC with (hC | hC) | hC
  · have := (connF_vars hE hψ C hC).2 l hl; omega
  · have := ebF_vars hE C hC l hl; omega
  · rw [compF] at hC
    obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl <;> dsimp only <;> omega

/-! ### The checks of a seed, on any formula -/

section Iso

variable {n k t mm N₀ : ℕ} {F : Fml}

/-- A formula F on N₀ variables, a variable z = N₀ set to false, the checks of ω on the first n
variables as the chains of `isoF` (variables N₀ + 1 + i), and the complements of the chain bits. -/
def isoAdd (N₀ : ℕ) (F : Fml) (ω : Seed n k t mm) : Fml :=
  F ++ [[(N₀, false)]] ++ isoF N₀ (N₀ + 1) k ω.1.val (rowsOf ω) (fixesOf ω) ++ compF (N₀ + 1) (mm * k)

theorem isoC (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < N₀) (hn : n ≤ N₀) (hk : 1 ≤ k) (ω : Seed n k t mm) (s : ℕ) :
    cntS (N₀ + 1 + mm * k + mm * k) s (isoAdd N₀ F ω) =
      (univ.filter fun w : Fin (N₀ + 1 + mm * k) → Bool =>
        (∀ C ∈ F ++ [[(N₀, false)]] ++ isoF N₀ (N₀ + 1) k ω.1.val (rowsOf ω) (fixesOf ω), ∃ l ∈ C, ext w l.1 = l.2) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (N₀ + 1) i)) i = true).card = s).card := by
  unfold cntS
  refine card_append _ _ (fun w i => !w (Fin.natAdd (N₀ + 1) i)) fun w h => ?_
  have hlt : ∀ a < N₀ + 1 + mm * k, ext (Fin.append w h) a = ext w a := fun a ha => ext_append_lt w h ha
  have hvars : ∀ C ∈ F ++ [[(N₀, false)]] ++ isoF N₀ (N₀ + 1) k ω.1.val (rowsOf ω) (fixesOf ω),
      ∀ l ∈ C, l.1 < N₀ + 1 + mm * k := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · rcases List.mem_append.1 hC with hC | hC
      · have := hF C hC l hl; omega
      · rw [List.mem_singleton] at hC; subst hC; rw [List.mem_singleton] at hl; subst hl; simp only; omega
    · exact (isoF_clause (by omega) (by omega) hk ω hC).2 l hl
  rw [isoAdd, List.forall_mem_append, sat_congr (f' := ext w) (fun C hC l hl => hlt _ (hvars C hC l hl)), sat_compF]
  have hc : (∀ i < mm * k, ext (Fin.append w h) (N₀ + 1 + mm * k + i) =
      !ext (Fin.append w h) (N₀ + 1 + i)) ↔ h = fun i => !w (Fin.natAdd (N₀ + 1) i) := by
    rw [← comp_iff w h]
    exact forall₂_congr fun i hi => by rw [ext_append_ge, hlt _ (by omega)]
  rw [hc]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩; exact ⟨⟨h1, h3⟩, rfl⟩
  · rintro ⟨⟨h1, h3⟩, rfl⟩; exact ⟨⟨h1, rfl⟩, h3⟩

theorem isoD (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < N₀) (hn : n ≤ N₀) (hk : 1 ≤ k) (ω : Seed n k t mm) (s : ℕ) :
    (univ.filter fun w : Fin (N₀ + 1 + mm * k) → Bool =>
        (∀ C ∈ F ++ [[(N₀, false)]] ++ isoF N₀ (N₀ + 1) k ω.1.val (rowsOf ω) (fixesOf ω), ∃ l ∈ C, ext w l.1 = l.2) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (N₀ + 1) i)) i = true).card = s + mm * k).card =
      (univ.filter fun y : Fin (N₀ + 1) → Bool =>
        (∀ C ∈ F ++ [[(N₀, false)]], ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val) ∧
        (univ.filter fun i => y i = true).card = s).card := by
  refine card_append _ _ (auxT ω) fun y g => ?_
  have hlt : ∀ a < N₀ + 1, ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt y g ha
  have hvars : ∀ C ∈ F ++ [[(N₀, false)]], ∀ l ∈ C, l.1 < N₀ + 1 := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · have := hF C hC l hl; omega
    · rw [List.mem_singleton] at hC; subst hC; rw [List.mem_singleton] at hl; subst hl; simp only; omega
  rw [List.forall_mem_append, sat_congr (f' := ext y) (fun C hC l hl => hlt _ (hvars C hC l hl)), count_comp]
  have hzf : (∀ C ∈ F ++ [[(N₀, false)]], ∃ l ∈ C, ext y l.1 = l.2) → ext y N₀ = false := fun h => by
    have := h _ (List.mem_append_right _ (List.mem_singleton_self _))
    simpa using this
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have := (sat_isoF_iff (by omega) hk ω (by omega) y g (hzf h1)).1 h2
    exact ⟨⟨h1, this.1, by omega⟩, this.2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨h1, (sat_isoF_iff (by omega) hk ω (by omega) y g (hzf h1)).2 ⟨h2, h4⟩⟩, by omega⟩

theorem isoE (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < N₀) (hn : n ≤ N₀) (ω : Seed n k t mm) (s : ℕ) :
    (univ.filter fun y : Fin (N₀ + 1) → Bool =>
        (∀ C ∈ F ++ [[(N₀, false)]], ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val) ∧
        (univ.filter fun i => y i = true).card = s).card =
      (univ.filter fun w : Fin N₀ → Bool => ((∀ C ∈ F, ∃ l ∈ C, ext w l.1 = l.2) ∧
        H ω (fun j => ext w j.val)) ∧ (univ.filter fun i => w i = true).card = s).card := by
  refine card_append _ _ (fun _ _ => false) fun w b => ?_
  have hlt : ∀ a < N₀, ext (Fin.append w b) a = ext w a := fun a ha => ext_append_lt w b ha
  have hH : (fun j : Fin n => ext (Fin.append w b) j.val) = fun j => ext w j.val := funext fun j => hlt _ (by omega)
  have hz : ext (Fin.append w b) N₀ = b 0 := by
    have h1 := ext_append_ge w b 0
    simp only [Nat.add_zero] at h1
    rw [h1]
    simp only [CountKSat.ext, dif_pos Nat.zero_lt_one]
    rfl
  have hb : b 0 = false ↔ b = fun _ => false := ⟨fun h => funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h,
    fun h => by rw [h]⟩
  rw [List.forall_mem_append, sat_congr (f' := ext w) (fun C hC l hl => hlt _ (hF C hC l hl)), hH, card_true_append]
  simp only [List.mem_singleton, forall_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, hz]
  rw [hb]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, by simpa using h3⟩, rfl⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨h1, rfl⟩, h2, by simpa using h3⟩

/-- **The checks of a seed on any formula**: the satisfying assignments of `isoAdd N₀ F ω` with
s + mm·k true variables are those of F with s true variables whose first n bits pass the checks. -/
theorem iso_count (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < N₀) (hn : n ≤ N₀) (hk : 1 ≤ k) (ω : Seed n k t mm) (s : ℕ) :
    cntS (N₀ + 1 + mm * k + mm * k) (s + mm * k) (isoAdd N₀ F ω) =
      (univ.filter fun w : Fin N₀ → Bool => ((∀ C ∈ F, ∃ l ∈ C, ext w l.1 = l.2) ∧
        H ω (fun j => ext w j.val)) ∧ (univ.filter fun i => w i = true).card = s).card := by
  rw [isoC hF hn hk ω, isoD hF hn hk ω, isoE hF hn ω]

end Iso

open Classical in
/-- **Induced forests with the checks of a seed**: the count of `isoAdd N₀ (fvsF …) ω`, N₀ = 3n + 2m,
with n + s + m + mm·k true variables, divided by 2^s, has the parity of the number of sets X of
size s with X ⊨ ψ and G[X] a forest that pass the checks of ω. -/
theorem fi_parity {n : ℕ} (G : SimpleGraph (Fin n)) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {s k t mm : ℕ}
    (hk : 1 ≤ k) (ω : Seed n k t mm) :
    cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + mm * k + mm * k)
      (n + s + (edges n (matrix G)).length + mm * k)
      (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
        (fvsF n (edges n (matrix G)) ψ) ω) / 2 ^ s % 2 =
      ((univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
        (univ.filter fun v => x v = true).card = s ∧ (G.induce {v | x v = true}).IsAcyclic).filter (H ω)).card % 2 := by
  rw [iso_count (fvsF_vars (edges_bound n (matrix G)) hψ) (by omega) hk ω, filter_filter]
  refine Eq.trans ?_ ((fvs_parity_P G hψ (H ω) s).trans ?_)
  · congr 3; ext w; simp only [mem_filter]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  tauto

open Classical in
/-- **Induced forests with one-sided error.** For every δ > 0 there are k and t such that for all
graphs G on n ≥ n₀ vertices, ψ on the vertex bits, s and the seeds ω of `Seed n k t (3n+3)`: if no
X of size s with X ⊨ ψ induces a forest, the bit is 0 for every seed; if one does, it is 1 for at
least a 2^{−δn} fraction of the seeds. -/
theorem fi_decide (δ : ℝ) (hδ : 0 < δ) : ∃ k t : ℕ, 1 ≤ k ∧ 1 ≤ t ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ψ : Fml) (s : ℕ), n₀ ≤ n → (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) →
      (numForF G ψ s = 0 → ∀ ω : Seed n k t (3 * n + 3),
        cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
          (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
          (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
            (fvsF n (edges n (matrix G)) ψ) ω) / 2 ^ s % 2 = 0) ∧
      (0 < numForF G ψ s →
        (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) *
          (univ.filter fun ω : Seed n k t (3 * n + 3) =>
            cntS (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length + 1 + (3 * n + 3) * k +
              (3 * n + 3) * k) (n + s + (edges n (matrix G)).length + (3 * n + 3) * k)
              (isoAdd (n + n + n + (edges n (matrix G)).length + (edges n (matrix G)).length)
                (fvsF n (edges n (matrix G)) ψ) ω) / 2 ^ s % 2 = 1).card) := by
  obtain ⟨k, t, hk, ht, M₀, hM₀⟩ := isolation δ hδ
  refine ⟨k, t, hk, ht, M₀, fun n G ψ s hn hψ => ⟨fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · rw [fi_parity G hψ hk ω]
    have : (univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
        (univ.filter fun v => x v = true).card = s ∧ (G.induce {v | x v = true}).IsAcyclic) = ∅ :=
      card_eq_zero.1 h0
    rw [this]; simp
  · have h := hM₀ n hn _ (card_pos.1 hpos)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast card_le_card fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      rw [fi_parity G hψ hk ω, hω]

end EthCor.Forest
